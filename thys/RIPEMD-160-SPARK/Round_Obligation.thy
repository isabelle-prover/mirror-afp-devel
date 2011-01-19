theory Round_Obligation
imports Round_User

begin



lemma goal61'1: 
  assumes R1: " (0 :: int) <= Round_Declaration.integer__size'' "
  assumes R2: 
  " Round_Declaration.integer__first'' <= Round_Declaration.integer__last''
  "
  assumes R3: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__base__last''
  "
  assumes R4: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__first''
  "
  assumes R5: 
  " Round_Declaration.integer__last''
    <= Round_Declaration.integer__base__last''
  "
  assumes R6: 
  " (0 :: int) <= Round_Declaration.interfaces__unsigned_32__size''
  "
  assumes R7: 
  " Round_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R8: 
  " Round_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R9: 
  " Round_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R10: 
  " Round_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R11: 
  " Round_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R12: 
  " (0 :: int) <= Round_Declaration.wordops__word__size''
  "
  assumes R13: 
  " Round_Declaration.wordops__word__first'' = (0 :: int)
  "
  assumes R14: 
  " Round_Declaration.wordops__word__last'' = (4294967295 :: int)
  "
  assumes R15: 
  " Round_Declaration.wordops__word__base__first'' = (0 :: int)
  "
  assumes R16: 
  " Round_Declaration.wordops__word__base__last''
    = (4294967295 :: int)
  "
  assumes R17: 
  " Round_Declaration.wordops__word__modulus'' = (4294967296 :: int)
  "
  assumes R18: 
  " (0 :: int) <= Round_Declaration.wordops__rotate_amount__size''
  "
  assumes R19: 
  " Round_Declaration.wordops__rotate_amount__first'' = (0 :: int)
  "
  assumes R20: 
  " Round_Declaration.wordops__rotate_amount__last'' = (15 :: int)
  "
  assumes R21: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes R22: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__first''
  "
  assumes R23: 
  " Round_Declaration.wordops__rotate_amount__last''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes R24: " (0 :: int) <= Round_Declaration.word__size'' "
  assumes R25: " Round_Declaration.word__first'' = (0 :: int) "
  assumes R26: 
  " Round_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R27: 
  " Round_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R28: 
  " Round_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R29: 
  " Round_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R30: " (0 :: int) <= Round_Declaration.chain__size'' "
  assumes R31: 
  " ALL ( A'' :: chain' ) ( B'' :: chain' )
    .   h0'chain A'' = h0'chain B''
        & h1'chain A'' = h1'chain B''
        & h2'chain A'' = h2'chain B''
        & h3'chain A'' = h3'chain B''
        & h4'chain A'' = h4'chain B''
        --> A'' = B''
  "
  assumes R32: 
  " (0 :: int) <= Round_Declaration.block_index__size''
  "
  assumes R33: 
  " Round_Declaration.block_index__first'' = (0 :: int)
  "
  assumes R34: 
  " Round_Declaration.block_index__last'' = (15 :: int)
  "
  assumes R35: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__base__last''
  "
  assumes R36: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__first''
  "
  assumes R37: 
  " Round_Declaration.block_index__last''
    <= Round_Declaration.block_index__base__last''
  "
  assumes R38: 
  " (0 :: int) <= Round_Declaration.round_index__size''
  "
  assumes R39: 
  " Round_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R40: 
  " Round_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R41: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__base__last''
  "
  assumes R42: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__first''
  "
  assumes R43: 
  " Round_Declaration.round_index__last''
    <= Round_Declaration.round_index__base__last''
  "
  assumes R44: 
  " (0 :: int) <= Round_Declaration.chain_pair__size''
  "
  assumes R45: 
  " ALL ( A'' :: chain_pair' ) ( B'' :: chain_pair' )
    .   left'chain_pair A'' = left'chain_pair B''
        & right'chain_pair A'' = right'chain_pair B''
        --> A'' = B''
  "
  assumes R46: 
  " (0 :: int) <= Round_Declaration.rotate_amount__size''
  "
  assumes R47: 
  " Round_Declaration.rotate_amount__first'' = (0 :: int)
  "
  assumes R48: 
  " Round_Declaration.rotate_amount__last'' = (15 :: int)
  "
  assumes R49: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes R50: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__first''
  "
  assumes R51: 
  " Round_Declaration.rotate_amount__last''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes R52: 
  " ALL ( i1'' :: int ) ( v'' :: int )
    .   ( Round_Declaration.block___mk_const_arr' v'' ) i1'' = v''
  "
  assumes H1: " (0 :: int) <= Round_Declaration.ca'' "
  assumes H2: " Round_Declaration.ca'' <= (4294967295 :: int) "
  assumes H3: " (0 :: int) <= Round_Declaration.cb'' "
  assumes H4: " Round_Declaration.cb'' <= (4294967295 :: int) "
  assumes H5: " (0 :: int) <= Round_Declaration.cc'' "
  assumes H6: " Round_Declaration.cc'' <= (4294967295 :: int) "
  assumes H7: " (0 :: int) <= Round_Declaration.cd'' "
  assumes H8: " Round_Declaration.cd'' <= (4294967295 :: int) "
  assumes H9: " (0 :: int) <= Round_Declaration.ce'' "
  assumes H10: " Round_Declaration.ce'' <= (4294967295 :: int) "
  assumes H11: 
  " ALL ( i___1'' :: int )
    .   (0 :: int) <= i___1'' & i___1'' <= (15 :: int)
        --> (0 :: int) <= Round_Declaration.x'' i___1''
            & Round_Declaration.x'' i___1'' <= (4294967295 :: int)
  "
  assumes H12: 
  " (0 :: int) <= Round_Declaration.s_l_spark' (0 :: int)
  "
  assumes H13: 
  " Round_Declaration.s_l_spark' (0 :: int) <= (15 :: int)
  "
  assumes H14: 
  " Round_Declaration.s_l_spark' (0 :: int)
    = Round_Specification.s_l' (0 :: int)
  "
  assumes H15: 
  " (0 :: int)
    <= Round_Declaration.f_spark'
         (0 :: int)
         Round_Declaration.cb''
         Round_Declaration.cc''
         Round_Declaration.cd''
  "
  assumes H16: 
  " Round_Declaration.f_spark'
      (0 :: int)
      Round_Declaration.cb''
      Round_Declaration.cc''
      Round_Declaration.cd''
    <= (4294967295 :: int)
  "
  assumes H17: 
  " Round_Declaration.f_spark'
      (0 :: int)
      Round_Declaration.cb''
      Round_Declaration.cc''
      Round_Declaration.cd''
    = Round_Specification.f'
        (0 :: int)
        Round_Declaration.cb''
        Round_Declaration.cc''
        Round_Declaration.cd''
  "
  assumes H18: 
  " (0 :: int) <= Round_Declaration.r_l_spark' (0 :: int)
  "
  assumes H19: 
  " Round_Declaration.r_l_spark' (0 :: int) <= (15 :: int)
  "
  assumes H20: 
  " Round_Declaration.r_l_spark' (0 :: int)
    = Round_Specification.r_l' (0 :: int)
  "
  assumes H21: 
  " (0 :: int) <= Round_Declaration.k_l_spark' (0 :: int)
  "
  assumes H22: 
  " Round_Declaration.k_l_spark' (0 :: int) <= (4294967295 :: int)
  "
  assumes H23: 
  " Round_Declaration.k_l_spark' (0 :: int)
    = Round_Specification.k_l' (0 :: int)
  "
  assumes H24: 
  " (0 :: int)
    <= ( ( ( Round_Declaration.ca''
             + Round_Declaration.f_spark'
                 (0 :: int)
                 Round_Declaration.cb''
                 Round_Declaration.cc''
                 Round_Declaration.cd''
           )
           mod (4294967296 :: int)
           + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
         )
         mod (4294967296 :: int)
         + Round_Declaration.k_l_spark' (0 :: int)
       )
       mod (4294967296 :: int)
  "
  assumes H25: 
  " ( ( ( Round_Declaration.ca''
          + Round_Declaration.f_spark'
              (0 :: int)
              Round_Declaration.cb''
              Round_Declaration.cc''
              Round_Declaration.cd''
        )
        mod (4294967296 :: int)
        + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
      )
      mod (4294967296 :: int)
      + Round_Declaration.k_l_spark' (0 :: int)
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H26: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate'
         ( Round_Declaration.s_l_spark' (0 :: int) )
         ( ( ( ( Round_Declaration.ca''
                 + Round_Declaration.f_spark'
                     (0 :: int)
                     Round_Declaration.cb''
                     Round_Declaration.cc''
                     Round_Declaration.cd''
               )
               mod (4294967296 :: int)
               + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
             )
             mod (4294967296 :: int)
             + Round_Declaration.k_l_spark' (0 :: int)
           )
           mod (4294967296 :: int)
         )
  "
  assumes H27: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_l_spark' (0 :: int) )
      ( ( ( ( Round_Declaration.ca''
              + Round_Declaration.f_spark'
                  (0 :: int)
                  Round_Declaration.cb''
                  Round_Declaration.cc''
                  Round_Declaration.cd''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_l_spark' (0 :: int)
        )
        mod (4294967296 :: int)
      )
    <= (4294967295 :: int)
  "
  assumes H28: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_l_spark' (0 :: int) )
      ( ( ( ( Round_Declaration.ca''
              + Round_Declaration.f_spark'
                  (0 :: int)
                  Round_Declaration.cb''
                  Round_Declaration.cc''
                  Round_Declaration.cd''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_l_spark' (0 :: int)
        )
        mod (4294967296 :: int)
      )
    = Round_Specification.wordops__rotate_left'
        ( Round_Declaration.s_l_spark' (0 :: int) )
        ( ( ( ( Round_Declaration.ca''
                + Round_Declaration.f_spark'
                    (0 :: int)
                    Round_Declaration.cb''
                    Round_Declaration.cc''
                    Round_Declaration.cd''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_l_spark' (0 :: int)
          )
          mod (4294967296 :: int)
        )
  "
  assumes H29: 
  " (0 :: int)
    <= ( Round_Declaration.wordops__rotate'
           ( Round_Declaration.s_l_spark' (0 :: int) )
           ( ( ( ( Round_Declaration.ca''
                   + Round_Declaration.f_spark'
                       (0 :: int)
                       Round_Declaration.cb''
                       Round_Declaration.cc''
                       Round_Declaration.cd''
                 )
                 mod (4294967296 :: int)
                 + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
               )
               mod (4294967296 :: int)
               + Round_Declaration.k_l_spark' (0 :: int)
             )
             mod (4294967296 :: int)
           )
         + Round_Declaration.ce''
       )
       mod (4294967296 :: int)
  "
  assumes H30: 
  " ( Round_Declaration.wordops__rotate'
        ( Round_Declaration.s_l_spark' (0 :: int) )
        ( ( ( ( Round_Declaration.ca''
                + Round_Declaration.f_spark'
                    (0 :: int)
                    Round_Declaration.cb''
                    Round_Declaration.cc''
                    Round_Declaration.cd''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_l_spark' (0 :: int)
          )
          mod (4294967296 :: int)
        )
      + Round_Declaration.ce''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H31: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.cc''
  "
  assumes H32: 
  " Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.cc''
    <= (4294967295 :: int)
  "
  assumes H33: 
  " Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.cc''
    = Round_Specification.wordops__rotate_left'
        (10 :: int)
        Round_Declaration.cc''
  "
  assumes H34: 
  " (0 :: int) <= Round_Declaration.s_r_spark' (0 :: int)
  "
  assumes H35: 
  " Round_Declaration.s_r_spark' (0 :: int) <= (15 :: int)
  "
  assumes H36: 
  " Round_Declaration.s_r_spark' (0 :: int)
    = Round_Specification.s_r' (0 :: int)
  "
  assumes H37: 
  " Round_Declaration.round_index__base__first'' <= (79 :: int)
  "
  assumes H38: 
  " (79 :: int) <= Round_Declaration.round_index__base__last''
  "
  assumes H39: 
  " (0 :: int)
    <= Round_Declaration.f_spark'
         (79 :: int)
         Round_Declaration.cb''
         Round_Declaration.cc''
         Round_Declaration.cd''
  "
  assumes H40: 
  " Round_Declaration.f_spark'
      (79 :: int)
      Round_Declaration.cb''
      Round_Declaration.cc''
      Round_Declaration.cd''
    <= (4294967295 :: int)
  "
  assumes H41: 
  " Round_Declaration.f_spark'
      (79 :: int)
      Round_Declaration.cb''
      Round_Declaration.cc''
      Round_Declaration.cd''
    = Round_Specification.f'
        (79 :: int)
        Round_Declaration.cb''
        Round_Declaration.cc''
        Round_Declaration.cd''
  "
  assumes H42: 
  " (0 :: int) <= Round_Declaration.r_r_spark' (0 :: int)
  "
  assumes H43: 
  " Round_Declaration.r_r_spark' (0 :: int) <= (15 :: int)
  "
  assumes H44: 
  " Round_Declaration.r_r_spark' (0 :: int)
    = Round_Specification.r_r' (0 :: int)
  "
  assumes H45: 
  " (0 :: int) <= Round_Declaration.k_r_spark' (0 :: int)
  "
  assumes H46: 
  " Round_Declaration.k_r_spark' (0 :: int) <= (4294967295 :: int)
  "
  assumes H47: 
  " Round_Declaration.k_r_spark' (0 :: int)
    = Round_Specification.k_r' (0 :: int)
  "
  assumes H48: 
  " (0 :: int)
    <= ( ( ( Round_Declaration.ca''
             + Round_Declaration.f_spark'
                 (79 :: int)
                 Round_Declaration.cb''
                 Round_Declaration.cc''
                 Round_Declaration.cd''
           )
           mod (4294967296 :: int)
           + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
         )
         mod (4294967296 :: int)
         + Round_Declaration.k_r_spark' (0 :: int)
       )
       mod (4294967296 :: int)
  "
  assumes H49: 
  " ( ( ( Round_Declaration.ca''
          + Round_Declaration.f_spark'
              (79 :: int)
              Round_Declaration.cb''
              Round_Declaration.cc''
              Round_Declaration.cd''
        )
        mod (4294967296 :: int)
        + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
      )
      mod (4294967296 :: int)
      + Round_Declaration.k_r_spark' (0 :: int)
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H50: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate'
         ( Round_Declaration.s_r_spark' (0 :: int) )
         ( ( ( ( Round_Declaration.ca''
                 + Round_Declaration.f_spark'
                     (79 :: int)
                     Round_Declaration.cb''
                     Round_Declaration.cc''
                     Round_Declaration.cd''
               )
               mod (4294967296 :: int)
               + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
             )
             mod (4294967296 :: int)
             + Round_Declaration.k_r_spark' (0 :: int)
           )
           mod (4294967296 :: int)
         )
  "
  assumes H51: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_r_spark' (0 :: int) )
      ( ( ( ( Round_Declaration.ca''
              + Round_Declaration.f_spark'
                  (79 :: int)
                  Round_Declaration.cb''
                  Round_Declaration.cc''
                  Round_Declaration.cd''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_r_spark' (0 :: int)
        )
        mod (4294967296 :: int)
      )
    <= (4294967295 :: int)
  "
  assumes H52: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_r_spark' (0 :: int) )
      ( ( ( ( Round_Declaration.ca''
              + Round_Declaration.f_spark'
                  (79 :: int)
                  Round_Declaration.cb''
                  Round_Declaration.cc''
                  Round_Declaration.cd''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_r_spark' (0 :: int)
        )
        mod (4294967296 :: int)
      )
    = Round_Specification.wordops__rotate_left'
        ( Round_Declaration.s_r_spark' (0 :: int) )
        ( ( ( ( Round_Declaration.ca''
                + Round_Declaration.f_spark'
                    (79 :: int)
                    Round_Declaration.cb''
                    Round_Declaration.cc''
                    Round_Declaration.cd''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_r_spark' (0 :: int)
          )
          mod (4294967296 :: int)
        )
  "
  assumes H53: 
  " (0 :: int)
    <= ( Round_Declaration.wordops__rotate'
           ( Round_Declaration.s_r_spark' (0 :: int) )
           ( ( ( ( Round_Declaration.ca''
                   + Round_Declaration.f_spark'
                       (79 :: int)
                       Round_Declaration.cb''
                       Round_Declaration.cc''
                       Round_Declaration.cd''
                 )
                 mod (4294967296 :: int)
                 + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
               )
               mod (4294967296 :: int)
               + Round_Declaration.k_r_spark' (0 :: int)
             )
             mod (4294967296 :: int)
           )
         + Round_Declaration.ce''
       )
       mod (4294967296 :: int)
  "
  assumes H54: 
  " ( Round_Declaration.wordops__rotate'
        ( Round_Declaration.s_r_spark' (0 :: int) )
        ( ( ( ( Round_Declaration.ca''
                + Round_Declaration.f_spark'
                    (79 :: int)
                    Round_Declaration.cb''
                    Round_Declaration.cc''
                    Round_Declaration.cd''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_r_spark' (0 :: int)
          )
          mod (4294967296 :: int)
        )
      + Round_Declaration.ce''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H55: " (0 :: int) <= Round_Declaration.integer__size'' "
  assumes H56: 
  " Round_Declaration.integer__first'' <= Round_Declaration.integer__last''
  "
  assumes H57: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__base__last''
  "
  assumes H58: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__first''
  "
  assumes H59: 
  " Round_Declaration.integer__last''
    <= Round_Declaration.integer__base__last''
  "
  assumes H60: 
  " (0 :: int) <= Round_Declaration.interfaces__unsigned_32__size''
  "
  assumes H61: 
  " (0 :: int) <= Round_Declaration.wordops__word__size''
  "
  assumes H62: 
  " (0 :: int) <= Round_Declaration.wordops__rotate_amount__size''
  "
  assumes H63: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes H64: " (0 :: int) <= Round_Declaration.word__size'' "
  assumes H65: " (0 :: int) <= Round_Declaration.chain__size'' "
  assumes H66: 
  " (0 :: int) <= Round_Declaration.block_index__size''
  "
  assumes H67: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__base__last''
  "
  assumes H68: 
  " (0 :: int) <= Round_Declaration.round_index__size''
  "
  assumes H69: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__base__last''
  "
  assumes H70: 
  " (0 :: int) <= Round_Declaration.chain_pair__size''
  "
  assumes H71: 
  " (0 :: int) <= Round_Declaration.rotate_amount__size''
  "
  assumes H72: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes H73: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= (0 :: int)
  "
  assumes H74: 
  " (15 :: int)
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes H75: 
  " Round_Declaration.block_index__base__first'' <= (0 :: int)
  "
  assumes H76: 
  " (15 :: int) <= Round_Declaration.block_index__base__last''
  "
  assumes H77: 
  " Round_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H78: 
  " (79 :: int) <= Round_Declaration.round_index__base__last''
  "
  assumes H79: 
  " Round_Declaration.rotate_amount__base__first'' <= (0 :: int)
  "
  assumes H80: 
  " (15 :: int) <= Round_Declaration.rotate_amount__base__last''
  "
  shows " Round_Declaration.chain_pair___default_rcd''
          (| left'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ce''
                |)
                (| h1'chain
                   := ( Round_Declaration.wordops__rotate'
                          ( Round_Declaration.s_l_spark' (0 :: int) )
                          ( ( ( ( Round_Declaration.ca''
                                  + Round_Declaration.f_spark'
                                      (0 :: int)
                                      Round_Declaration.cb''
                                      Round_Declaration.cc''
                                      Round_Declaration.cd''
                                )
                                mod (4294967296 :: int)
                                + Round_Declaration.x'' ( Round_Declaration.r_l_spark' (0 :: int) )
                              )
                              mod (4294967296 :: int)
                              + Round_Declaration.k_l_spark' (0 :: int)
                            )
                            mod (4294967296 :: int)
                          )
                        + Round_Declaration.ce''
                      )
                      mod (4294967296 :: int)
                |)
                (| h2'chain
                   := Round_Declaration.cb''
                |)
                (| h3'chain
                   := Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.cc''
                |)
                (| h4'chain
                   := Round_Declaration.cd''
                |)
          |)
          (| right'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ce''
                |)
                (| h1'chain
                   := ( Round_Declaration.wordops__rotate'
                          ( Round_Declaration.s_r_spark' (0 :: int) )
                          ( ( ( ( Round_Declaration.ca''
                                  + Round_Declaration.f_spark'
                                      (79 :: int)
                                      Round_Declaration.cb''
                                      Round_Declaration.cc''
                                      Round_Declaration.cd''
                                )
                                mod (4294967296 :: int)
                                + Round_Declaration.x'' ( Round_Declaration.r_r_spark' (0 :: int) )
                              )
                              mod (4294967296 :: int)
                              + Round_Declaration.k_r_spark' (0 :: int)
                            )
                            mod (4294967296 :: int)
                          )
                        + Round_Declaration.ce''
                      )
                      mod (4294967296 :: int)
                |)
                (| h2'chain
                   := Round_Declaration.cb''
                |)
                (| h3'chain
                   := Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.cc''
                |)
                (| h4'chain
                   := Round_Declaration.cd''
                |)
          |)
          = Round_Specification.steps'
              ( Round_Declaration.chain_pair___default_rcd''
                (| left'chain_pair
                   := Round_Declaration.chain___default_rcd''
                      (| h0'chain
                         := Round_Declaration.ca''
                      |)
                      (| h1'chain
                         := Round_Declaration.cb''
                      |)
                      (| h2'chain
                         := Round_Declaration.cc''
                      |)
                      (| h3'chain
                         := Round_Declaration.cd''
                      |)
                      (| h4'chain
                         := Round_Declaration.ce''
                      |)
                |)
                (| right'chain_pair
                   := Round_Declaration.chain___default_rcd''
                      (| h0'chain
                         := Round_Declaration.ca''
                      |)
                      (| h1'chain
                         := Round_Declaration.cb''
                      |)
                      (| h2'chain
                         := Round_Declaration.cc''
                      |)
                      (| h3'chain
                         := Round_Declaration.cd''
                      |)
                      (| h4'chain
                         := Round_Declaration.ce''
                      |)
                |)
              )
              (1 :: int)
              Round_Declaration.x''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal62'1: 
  assumes R1: " (0 :: int) <= Round_Declaration.integer__size'' "
  assumes R2: 
  " Round_Declaration.integer__first'' <= Round_Declaration.integer__last''
  "
  assumes R3: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__base__last''
  "
  assumes R4: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__first''
  "
  assumes R5: 
  " Round_Declaration.integer__last''
    <= Round_Declaration.integer__base__last''
  "
  assumes R6: 
  " (0 :: int) <= Round_Declaration.interfaces__unsigned_32__size''
  "
  assumes R7: 
  " Round_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R8: 
  " Round_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R9: 
  " Round_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R10: 
  " Round_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R11: 
  " Round_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R12: 
  " (0 :: int) <= Round_Declaration.wordops__word__size''
  "
  assumes R13: 
  " Round_Declaration.wordops__word__first'' = (0 :: int)
  "
  assumes R14: 
  " Round_Declaration.wordops__word__last'' = (4294967295 :: int)
  "
  assumes R15: 
  " Round_Declaration.wordops__word__base__first'' = (0 :: int)
  "
  assumes R16: 
  " Round_Declaration.wordops__word__base__last''
    = (4294967295 :: int)
  "
  assumes R17: 
  " Round_Declaration.wordops__word__modulus'' = (4294967296 :: int)
  "
  assumes R18: 
  " (0 :: int) <= Round_Declaration.wordops__rotate_amount__size''
  "
  assumes R19: 
  " Round_Declaration.wordops__rotate_amount__first'' = (0 :: int)
  "
  assumes R20: 
  " Round_Declaration.wordops__rotate_amount__last'' = (15 :: int)
  "
  assumes R21: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes R22: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__first''
  "
  assumes R23: 
  " Round_Declaration.wordops__rotate_amount__last''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes R24: " (0 :: int) <= Round_Declaration.word__size'' "
  assumes R25: " Round_Declaration.word__first'' = (0 :: int) "
  assumes R26: 
  " Round_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R27: 
  " Round_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R28: 
  " Round_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R29: 
  " Round_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R30: " (0 :: int) <= Round_Declaration.chain__size'' "
  assumes R31: 
  " ALL ( A'' :: chain' ) ( B'' :: chain' )
    .   h0'chain A'' = h0'chain B''
        & h1'chain A'' = h1'chain B''
        & h2'chain A'' = h2'chain B''
        & h3'chain A'' = h3'chain B''
        & h4'chain A'' = h4'chain B''
        --> A'' = B''
  "
  assumes R32: 
  " (0 :: int) <= Round_Declaration.block_index__size''
  "
  assumes R33: 
  " Round_Declaration.block_index__first'' = (0 :: int)
  "
  assumes R34: 
  " Round_Declaration.block_index__last'' = (15 :: int)
  "
  assumes R35: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__base__last''
  "
  assumes R36: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__first''
  "
  assumes R37: 
  " Round_Declaration.block_index__last''
    <= Round_Declaration.block_index__base__last''
  "
  assumes R38: 
  " (0 :: int) <= Round_Declaration.round_index__size''
  "
  assumes R39: 
  " Round_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R40: 
  " Round_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R41: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__base__last''
  "
  assumes R42: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__first''
  "
  assumes R43: 
  " Round_Declaration.round_index__last''
    <= Round_Declaration.round_index__base__last''
  "
  assumes R44: 
  " (0 :: int) <= Round_Declaration.chain_pair__size''
  "
  assumes R45: 
  " ALL ( A'' :: chain_pair' ) ( B'' :: chain_pair' )
    .   left'chain_pair A'' = left'chain_pair B''
        & right'chain_pair A'' = right'chain_pair B''
        --> A'' = B''
  "
  assumes R46: 
  " (0 :: int) <= Round_Declaration.rotate_amount__size''
  "
  assumes R47: 
  " Round_Declaration.rotate_amount__first'' = (0 :: int)
  "
  assumes R48: 
  " Round_Declaration.rotate_amount__last'' = (15 :: int)
  "
  assumes R49: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes R50: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__first''
  "
  assumes R51: 
  " Round_Declaration.rotate_amount__last''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes R52: 
  " ALL ( i1'' :: int ) ( v'' :: int )
    .   ( Round_Declaration.block___mk_const_arr' v'' ) i1'' = v''
  "
  assumes H1: 
  " Round_Declaration.chain_pair___default_rcd''
    (| left'chain_pair
       := Round_Declaration.chain___default_rcd''
          (| h0'chain
             := Round_Declaration.cla''
          |)
          (| h1'chain
             := Round_Declaration.clb''
          |)
          (| h2'chain
             := Round_Declaration.clc''
          |)
          (| h3'chain
             := Round_Declaration.cld''
          |)
          (| h4'chain
             := Round_Declaration.cle''
          |)
    |)
    (| right'chain_pair
       := Round_Declaration.chain___default_rcd''
          (| h0'chain
             := Round_Declaration.cra''
          |)
          (| h1'chain
             := Round_Declaration.crb''
          |)
          (| h2'chain
             := Round_Declaration.crc''
          |)
          (| h3'chain
             := Round_Declaration.crd''
          |)
          (| h4'chain
             := Round_Declaration.cre''
          |)
    |)
    = Round_Specification.steps'
        ( Round_Declaration.chain_pair___default_rcd''
          (| left'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ca___init''
                |)
                (| h1'chain
                   := Round_Declaration.cb___init''
                |)
                (| h2'chain
                   := Round_Declaration.cc___init''
                |)
                (| h3'chain
                   := Round_Declaration.cd___init''
                |)
                (| h4'chain
                   := Round_Declaration.ce___init''
                |)
          |)
          (| right'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ca___init''
                |)
                (| h1'chain
                   := Round_Declaration.cb___init''
                |)
                (| h2'chain
                   := Round_Declaration.cc___init''
                |)
                (| h3'chain
                   := Round_Declaration.cd___init''
                |)
                (| h4'chain
                   := Round_Declaration.ce___init''
                |)
          |)
        )
        ( Round_Declaration.loop__1__j'' + (1 :: int) )
        Round_Declaration.x''
  "
  assumes H2: " (0 :: int) <= Round_Declaration.ca___init'' "
  assumes H3: 
  " Round_Declaration.ca___init'' <= (4294967295 :: int)
  "
  assumes H4: " (0 :: int) <= Round_Declaration.cb___init'' "
  assumes H5: 
  " Round_Declaration.cb___init'' <= (4294967295 :: int)
  "
  assumes H6: " (0 :: int) <= Round_Declaration.cc___init'' "
  assumes H7: 
  " Round_Declaration.cc___init'' <= (4294967295 :: int)
  "
  assumes H8: " (0 :: int) <= Round_Declaration.cd___init'' "
  assumes H9: 
  " Round_Declaration.cd___init'' <= (4294967295 :: int)
  "
  assumes H10: " (0 :: int) <= Round_Declaration.ce___init'' "
  assumes H11: 
  " Round_Declaration.ce___init'' <= (4294967295 :: int)
  "
  assumes H12: 
  " ALL ( i___1'' :: int )
    .   (0 :: int) <= i___1'' & i___1'' <= (15 :: int)
        --> (0 :: int) <= Round_Declaration.x'' i___1''
            & Round_Declaration.x'' i___1'' <= (4294967295 :: int)
  "
  assumes H13: " (0 :: int) <= Round_Declaration.loop__1__j'' "
  assumes H14: " Round_Declaration.loop__1__j'' <= (78 :: int) "
  assumes H15: 
  " (0 :: int)
    <= Round_Declaration.s_l_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H16: 
  " Round_Declaration.s_l_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= (15 :: int)
  "
  assumes H17: 
  " Round_Declaration.s_l_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    = Round_Specification.s_l' ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H18: " (0 :: int) <= Round_Declaration.cla'' "
  assumes H19: " Round_Declaration.cla'' <= (4294967295 :: int) "
  assumes H20: " (0 :: int) <= Round_Declaration.clb'' "
  assumes H21: " Round_Declaration.clb'' <= (4294967295 :: int) "
  assumes H22: " (0 :: int) <= Round_Declaration.clc'' "
  assumes H23: " Round_Declaration.clc'' <= (4294967295 :: int) "
  assumes H24: " (0 :: int) <= Round_Declaration.cld'' "
  assumes H25: " Round_Declaration.cld'' <= (4294967295 :: int) "
  assumes H26: 
  " (0 :: int)
    <= Round_Declaration.f_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
         Round_Declaration.clb''
         Round_Declaration.clc''
         Round_Declaration.cld''
  "
  assumes H27: 
  " Round_Declaration.f_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
      Round_Declaration.clb''
      Round_Declaration.clc''
      Round_Declaration.cld''
    <= (4294967295 :: int)
  "
  assumes H28: 
  " Round_Declaration.f_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
      Round_Declaration.clb''
      Round_Declaration.clc''
      Round_Declaration.cld''
    = Round_Specification.f'
        ( Round_Declaration.loop__1__j'' + (1 :: int) )
        Round_Declaration.clb''
        Round_Declaration.clc''
        Round_Declaration.cld''
  "
  assumes H29: 
  " (0 :: int)
    <= Round_Declaration.r_l_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H30: 
  " Round_Declaration.r_l_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= (15 :: int)
  "
  assumes H31: 
  " Round_Declaration.r_l_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    = Round_Specification.r_l' ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H32: 
  " (0 :: int)
    <= Round_Declaration.k_l_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H33: 
  " Round_Declaration.k_l_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= (4294967295 :: int)
  "
  assumes H34: 
  " Round_Declaration.k_l_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    = Round_Specification.k_l' ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H35: 
  " (0 :: int)
    <= ( ( ( Round_Declaration.cla''
             + Round_Declaration.f_spark'
                 ( Round_Declaration.loop__1__j'' + (1 :: int) )
                 Round_Declaration.clb''
                 Round_Declaration.clc''
                 Round_Declaration.cld''
           )
           mod (4294967296 :: int)
           + Round_Declaration.x''
               ( Round_Declaration.r_l_spark'
                   ( Round_Declaration.loop__1__j'' + (1 :: int) )
               )
         )
         mod (4294967296 :: int)
         + Round_Declaration.k_l_spark'
             ( Round_Declaration.loop__1__j'' + (1 :: int) )
       )
       mod (4294967296 :: int)
  "
  assumes H36: 
  " ( ( ( Round_Declaration.cla''
          + Round_Declaration.f_spark'
              ( Round_Declaration.loop__1__j'' + (1 :: int) )
              Round_Declaration.clb''
              Round_Declaration.clc''
              Round_Declaration.cld''
        )
        mod (4294967296 :: int)
        + Round_Declaration.x''
            ( Round_Declaration.r_l_spark'
                ( Round_Declaration.loop__1__j'' + (1 :: int) )
            )
      )
      mod (4294967296 :: int)
      + Round_Declaration.k_l_spark'
          ( Round_Declaration.loop__1__j'' + (1 :: int) )
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H37: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate'
         ( Round_Declaration.s_l_spark'
             ( Round_Declaration.loop__1__j'' + (1 :: int) )
         )
         ( ( ( ( Round_Declaration.cla''
                 + Round_Declaration.f_spark'
                     ( Round_Declaration.loop__1__j'' + (1 :: int) )
                     Round_Declaration.clb''
                     Round_Declaration.clc''
                     Round_Declaration.cld''
               )
               mod (4294967296 :: int)
               + Round_Declaration.x''
                   ( Round_Declaration.r_l_spark'
                       ( Round_Declaration.loop__1__j'' + (1 :: int) )
                   )
             )
             mod (4294967296 :: int)
             + Round_Declaration.k_l_spark'
                 ( Round_Declaration.loop__1__j'' + (1 :: int) )
           )
           mod (4294967296 :: int)
         )
  "
  assumes H38: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_l_spark'
          ( Round_Declaration.loop__1__j'' + (1 :: int) )
      )
      ( ( ( ( Round_Declaration.cla''
              + Round_Declaration.f_spark'
                  ( Round_Declaration.loop__1__j'' + (1 :: int) )
                  Round_Declaration.clb''
                  Round_Declaration.clc''
                  Round_Declaration.cld''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x''
                ( Round_Declaration.r_l_spark'
                    ( Round_Declaration.loop__1__j'' + (1 :: int) )
                )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_l_spark'
              ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        mod (4294967296 :: int)
      )
    <= (4294967295 :: int)
  "
  assumes H39: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_l_spark'
          ( Round_Declaration.loop__1__j'' + (1 :: int) )
      )
      ( ( ( ( Round_Declaration.cla''
              + Round_Declaration.f_spark'
                  ( Round_Declaration.loop__1__j'' + (1 :: int) )
                  Round_Declaration.clb''
                  Round_Declaration.clc''
                  Round_Declaration.cld''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x''
                ( Round_Declaration.r_l_spark'
                    ( Round_Declaration.loop__1__j'' + (1 :: int) )
                )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_l_spark'
              ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        mod (4294967296 :: int)
      )
    = Round_Specification.wordops__rotate_left'
        ( Round_Declaration.s_l_spark'
            ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        ( ( ( ( Round_Declaration.cla''
                + Round_Declaration.f_spark'
                    ( Round_Declaration.loop__1__j'' + (1 :: int) )
                    Round_Declaration.clb''
                    Round_Declaration.clc''
                    Round_Declaration.cld''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x''
                  ( Round_Declaration.r_l_spark'
                      ( Round_Declaration.loop__1__j'' + (1 :: int) )
                  )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_l_spark'
                ( Round_Declaration.loop__1__j'' + (1 :: int) )
          )
          mod (4294967296 :: int)
        )
  "
  assumes H40: " (0 :: int) <= Round_Declaration.cle'' "
  assumes H41: " Round_Declaration.cle'' <= (4294967295 :: int) "
  assumes H42: 
  " (0 :: int)
    <= ( Round_Declaration.wordops__rotate'
           ( Round_Declaration.s_l_spark'
               ( Round_Declaration.loop__1__j'' + (1 :: int) )
           )
           ( ( ( ( Round_Declaration.cla''
                   + Round_Declaration.f_spark'
                       ( Round_Declaration.loop__1__j'' + (1 :: int) )
                       Round_Declaration.clb''
                       Round_Declaration.clc''
                       Round_Declaration.cld''
                 )
                 mod (4294967296 :: int)
                 + Round_Declaration.x''
                     ( Round_Declaration.r_l_spark'
                         ( Round_Declaration.loop__1__j'' + (1 :: int) )
                     )
               )
               mod (4294967296 :: int)
               + Round_Declaration.k_l_spark'
                   ( Round_Declaration.loop__1__j'' + (1 :: int) )
             )
             mod (4294967296 :: int)
           )
         + Round_Declaration.cle''
       )
       mod (4294967296 :: int)
  "
  assumes H43: 
  " ( Round_Declaration.wordops__rotate'
        ( Round_Declaration.s_l_spark'
            ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        ( ( ( ( Round_Declaration.cla''
                + Round_Declaration.f_spark'
                    ( Round_Declaration.loop__1__j'' + (1 :: int) )
                    Round_Declaration.clb''
                    Round_Declaration.clc''
                    Round_Declaration.cld''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x''
                  ( Round_Declaration.r_l_spark'
                      ( Round_Declaration.loop__1__j'' + (1 :: int) )
                  )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_l_spark'
                ( Round_Declaration.loop__1__j'' + (1 :: int) )
          )
          mod (4294967296 :: int)
        )
      + Round_Declaration.cle''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H44: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.clc''
  "
  assumes H45: 
  " Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.clc''
    <= (4294967295 :: int)
  "
  assumes H46: 
  " Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.clc''
    = Round_Specification.wordops__rotate_left'
        (10 :: int)
        Round_Declaration.clc''
  "
  assumes H47: 
  " (0 :: int)
    <= Round_Declaration.s_r_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H48: 
  " Round_Declaration.s_r_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= (15 :: int)
  "
  assumes H49: 
  " Round_Declaration.s_r_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    = Round_Specification.s_r' ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H50: " (0 :: int) <= Round_Declaration.cra'' "
  assumes H51: " Round_Declaration.cra'' <= (4294967295 :: int) "
  assumes H52: " (0 :: int) <= Round_Declaration.crb'' "
  assumes H53: " Round_Declaration.crb'' <= (4294967295 :: int) "
  assumes H54: " (0 :: int) <= Round_Declaration.crc'' "
  assumes H55: " Round_Declaration.crc'' <= (4294967295 :: int) "
  assumes H56: " (0 :: int) <= Round_Declaration.crd'' "
  assumes H57: " Round_Declaration.crd'' <= (4294967295 :: int) "
  assumes H58: 
  " Round_Declaration.round_index__base__first''
    <= (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H59: 
  " (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= Round_Declaration.round_index__base__last''
  "
  assumes H60: 
  " (0 :: int)
    <= Round_Declaration.f_spark'
         ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
         Round_Declaration.crb''
         Round_Declaration.crc''
         Round_Declaration.crd''
  "
  assumes H61: 
  " Round_Declaration.f_spark'
      ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
      Round_Declaration.crb''
      Round_Declaration.crc''
      Round_Declaration.crd''
    <= (4294967295 :: int)
  "
  assumes H62: 
  " Round_Declaration.f_spark'
      ( (78 :: int) - Round_Declaration.loop__1__j'' )
      Round_Declaration.crb''
      Round_Declaration.crc''
      Round_Declaration.crd''
    = Round_Specification.f'
        ( (78 :: int) - Round_Declaration.loop__1__j'' )
        Round_Declaration.crb''
        Round_Declaration.crc''
        Round_Declaration.crd''
  "
  assumes H63: 
  " (0 :: int)
    <= Round_Declaration.r_r_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H64: 
  " Round_Declaration.r_r_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= (15 :: int)
  "
  assumes H65: 
  " Round_Declaration.r_r_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    = Round_Specification.r_r' ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H66: 
  " (0 :: int)
    <= Round_Declaration.k_r_spark'
         ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H67: 
  " Round_Declaration.k_r_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    <= (4294967295 :: int)
  "
  assumes H68: 
  " Round_Declaration.k_r_spark'
      ( Round_Declaration.loop__1__j'' + (1 :: int) )
    = Round_Specification.k_r' ( Round_Declaration.loop__1__j'' + (1 :: int) )
  "
  assumes H69: 
  " (0 :: int)
    <= ( ( ( Round_Declaration.cra''
             + Round_Declaration.f_spark'
                 ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                 Round_Declaration.crb''
                 Round_Declaration.crc''
                 Round_Declaration.crd''
           )
           mod (4294967296 :: int)
           + Round_Declaration.x''
               ( Round_Declaration.r_r_spark'
                   ( Round_Declaration.loop__1__j'' + (1 :: int) )
               )
         )
         mod (4294967296 :: int)
         + Round_Declaration.k_r_spark'
             ( Round_Declaration.loop__1__j'' + (1 :: int) )
       )
       mod (4294967296 :: int)
  "
  assumes H70: 
  " ( ( ( Round_Declaration.cra''
          + Round_Declaration.f_spark'
              ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
              Round_Declaration.crb''
              Round_Declaration.crc''
              Round_Declaration.crd''
        )
        mod (4294967296 :: int)
        + Round_Declaration.x''
            ( Round_Declaration.r_r_spark'
                ( Round_Declaration.loop__1__j'' + (1 :: int) )
            )
      )
      mod (4294967296 :: int)
      + Round_Declaration.k_r_spark'
          ( Round_Declaration.loop__1__j'' + (1 :: int) )
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H71: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate'
         ( Round_Declaration.s_r_spark'
             ( Round_Declaration.loop__1__j'' + (1 :: int) )
         )
         ( ( ( ( Round_Declaration.cra''
                 + Round_Declaration.f_spark'
                     ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                     Round_Declaration.crb''
                     Round_Declaration.crc''
                     Round_Declaration.crd''
               )
               mod (4294967296 :: int)
               + Round_Declaration.x''
                   ( Round_Declaration.r_r_spark'
                       ( Round_Declaration.loop__1__j'' + (1 :: int) )
                   )
             )
             mod (4294967296 :: int)
             + Round_Declaration.k_r_spark'
                 ( Round_Declaration.loop__1__j'' + (1 :: int) )
           )
           mod (4294967296 :: int)
         )
  "
  assumes H72: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_r_spark'
          ( Round_Declaration.loop__1__j'' + (1 :: int) )
      )
      ( ( ( ( Round_Declaration.cra''
              + Round_Declaration.f_spark'
                  ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                  Round_Declaration.crb''
                  Round_Declaration.crc''
                  Round_Declaration.crd''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x''
                ( Round_Declaration.r_r_spark'
                    ( Round_Declaration.loop__1__j'' + (1 :: int) )
                )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_r_spark'
              ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        mod (4294967296 :: int)
      )
    <= (4294967295 :: int)
  "
  assumes H73: 
  " Round_Declaration.wordops__rotate'
      ( Round_Declaration.s_r_spark'
          ( Round_Declaration.loop__1__j'' + (1 :: int) )
      )
      ( ( ( ( Round_Declaration.cra''
              + Round_Declaration.f_spark'
                  ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                  Round_Declaration.crb''
                  Round_Declaration.crc''
                  Round_Declaration.crd''
            )
            mod (4294967296 :: int)
            + Round_Declaration.x''
                ( Round_Declaration.r_r_spark'
                    ( Round_Declaration.loop__1__j'' + (1 :: int) )
                )
          )
          mod (4294967296 :: int)
          + Round_Declaration.k_r_spark'
              ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        mod (4294967296 :: int)
      )
    = Round_Specification.wordops__rotate_left'
        ( Round_Declaration.s_r_spark'
            ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        ( ( ( ( Round_Declaration.cra''
                + Round_Declaration.f_spark'
                    ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                    Round_Declaration.crb''
                    Round_Declaration.crc''
                    Round_Declaration.crd''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x''
                  ( Round_Declaration.r_r_spark'
                      ( Round_Declaration.loop__1__j'' + (1 :: int) )
                  )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_r_spark'
                ( Round_Declaration.loop__1__j'' + (1 :: int) )
          )
          mod (4294967296 :: int)
        )
  "
  assumes H74: " (0 :: int) <= Round_Declaration.cre'' "
  assumes H75: " Round_Declaration.cre'' <= (4294967295 :: int) "
  assumes H76: 
  " (0 :: int)
    <= ( Round_Declaration.wordops__rotate'
           ( Round_Declaration.s_r_spark'
               ( Round_Declaration.loop__1__j'' + (1 :: int) )
           )
           ( ( ( ( Round_Declaration.cra''
                   + Round_Declaration.f_spark'
                       ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                       Round_Declaration.crb''
                       Round_Declaration.crc''
                       Round_Declaration.crd''
                 )
                 mod (4294967296 :: int)
                 + Round_Declaration.x''
                     ( Round_Declaration.r_r_spark'
                         ( Round_Declaration.loop__1__j'' + (1 :: int) )
                     )
               )
               mod (4294967296 :: int)
               + Round_Declaration.k_r_spark'
                   ( Round_Declaration.loop__1__j'' + (1 :: int) )
             )
             mod (4294967296 :: int)
           )
         + Round_Declaration.cre''
       )
       mod (4294967296 :: int)
  "
  assumes H77: 
  " ( Round_Declaration.wordops__rotate'
        ( Round_Declaration.s_r_spark'
            ( Round_Declaration.loop__1__j'' + (1 :: int) )
        )
        ( ( ( ( Round_Declaration.cra''
                + Round_Declaration.f_spark'
                    ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                    Round_Declaration.crb''
                    Round_Declaration.crc''
                    Round_Declaration.crd''
              )
              mod (4294967296 :: int)
              + Round_Declaration.x''
                  ( Round_Declaration.r_r_spark'
                      ( Round_Declaration.loop__1__j'' + (1 :: int) )
                  )
            )
            mod (4294967296 :: int)
            + Round_Declaration.k_r_spark'
                ( Round_Declaration.loop__1__j'' + (1 :: int) )
          )
          mod (4294967296 :: int)
        )
      + Round_Declaration.cre''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H78: 
  " (0 :: int)
    <= Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.crc''
  "
  assumes H79: 
  " Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.crc''
    <= (4294967295 :: int)
  "
  assumes H80: 
  " Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.crc''
    = Round_Specification.wordops__rotate_left'
        (10 :: int)
        Round_Declaration.crc''
  "
  assumes H81: " (0 :: int) <= Round_Declaration.integer__size'' "
  assumes H82: 
  " Round_Declaration.integer__first'' <= Round_Declaration.integer__last''
  "
  assumes H83: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__base__last''
  "
  assumes H84: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__first''
  "
  assumes H85: 
  " Round_Declaration.integer__last''
    <= Round_Declaration.integer__base__last''
  "
  assumes H86: 
  " (0 :: int) <= Round_Declaration.interfaces__unsigned_32__size''
  "
  assumes H87: 
  " (0 :: int) <= Round_Declaration.wordops__word__size''
  "
  assumes H88: 
  " (0 :: int) <= Round_Declaration.wordops__rotate_amount__size''
  "
  assumes H89: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes H90: " (0 :: int) <= Round_Declaration.word__size'' "
  assumes H91: " (0 :: int) <= Round_Declaration.chain__size'' "
  assumes H92: 
  " (0 :: int) <= Round_Declaration.block_index__size''
  "
  assumes H93: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__base__last''
  "
  assumes H94: 
  " (0 :: int) <= Round_Declaration.round_index__size''
  "
  assumes H95: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__base__last''
  "
  assumes H96: 
  " (0 :: int) <= Round_Declaration.chain_pair__size''
  "
  assumes H97: 
  " (0 :: int) <= Round_Declaration.rotate_amount__size''
  "
  assumes H98: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes H99: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= (0 :: int)
  "
  assumes H100: 
  " (15 :: int)
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes H101: 
  " Round_Declaration.block_index__base__first'' <= (0 :: int)
  "
  assumes H102: 
  " (15 :: int) <= Round_Declaration.block_index__base__last''
  "
  assumes H103: 
  " Round_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H104: 
  " (79 :: int) <= Round_Declaration.round_index__base__last''
  "
  assumes H105: 
  " Round_Declaration.rotate_amount__base__first'' <= (0 :: int)
  "
  assumes H106: 
  " (15 :: int) <= Round_Declaration.rotate_amount__base__last''
  "
  shows " Round_Declaration.chain_pair___default_rcd''
          (| left'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.cle''
                |)
                (| h1'chain
                   := ( Round_Declaration.wordops__rotate'
                          ( Round_Declaration.s_l_spark'
                              ( Round_Declaration.loop__1__j'' + (1 :: int) )
                          )
                          ( ( ( ( Round_Declaration.cla''
                                  + Round_Declaration.f_spark'
                                      ( Round_Declaration.loop__1__j'' + (1 :: int) )
                                      Round_Declaration.clb''
                                      Round_Declaration.clc''
                                      Round_Declaration.cld''
                                )
                                mod (4294967296 :: int)
                                + Round_Declaration.x''
                                    ( Round_Declaration.r_l_spark'
                                        ( Round_Declaration.loop__1__j'' + (1 :: int) )
                                    )
                              )
                              mod (4294967296 :: int)
                              + Round_Declaration.k_l_spark'
                                  ( Round_Declaration.loop__1__j'' + (1 :: int) )
                            )
                            mod (4294967296 :: int)
                          )
                        + Round_Declaration.cle''
                      )
                      mod (4294967296 :: int)
                |)
                (| h2'chain
                   := Round_Declaration.clb''
                |)
                (| h3'chain
                   := Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.clc''
                |)
                (| h4'chain
                   := Round_Declaration.cld''
                |)
          |)
          (| right'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.cre''
                |)
                (| h1'chain
                   := ( Round_Declaration.wordops__rotate'
                          ( Round_Declaration.s_r_spark'
                              ( Round_Declaration.loop__1__j'' + (1 :: int) )
                          )
                          ( ( ( ( Round_Declaration.cra''
                                  + Round_Declaration.f_spark'
                                      ( (79 :: int) - ( Round_Declaration.loop__1__j'' + (1 :: int) ) )
                                      Round_Declaration.crb''
                                      Round_Declaration.crc''
                                      Round_Declaration.crd''
                                )
                                mod (4294967296 :: int)
                                + Round_Declaration.x''
                                    ( Round_Declaration.r_r_spark'
                                        ( Round_Declaration.loop__1__j'' + (1 :: int) )
                                    )
                              )
                              mod (4294967296 :: int)
                              + Round_Declaration.k_r_spark'
                                  ( Round_Declaration.loop__1__j'' + (1 :: int) )
                            )
                            mod (4294967296 :: int)
                          )
                        + Round_Declaration.cre''
                      )
                      mod (4294967296 :: int)
                |)
                (| h2'chain
                   := Round_Declaration.crb''
                |)
                (| h3'chain
                   := Round_Declaration.wordops__rotate' (10 :: int) Round_Declaration.crc''
                |)
                (| h4'chain
                   := Round_Declaration.crd''
                |)
          |)
          = Round_Specification.steps'
              ( Round_Declaration.chain_pair___default_rcd''
                (| left'chain_pair
                   := Round_Declaration.chain___default_rcd''
                      (| h0'chain
                         := Round_Declaration.ca___init''
                      |)
                      (| h1'chain
                         := Round_Declaration.cb___init''
                      |)
                      (| h2'chain
                         := Round_Declaration.cc___init''
                      |)
                      (| h3'chain
                         := Round_Declaration.cd___init''
                      |)
                      (| h4'chain
                         := Round_Declaration.ce___init''
                      |)
                |)
                (| right'chain_pair
                   := Round_Declaration.chain___default_rcd''
                      (| h0'chain
                         := Round_Declaration.ca___init''
                      |)
                      (| h1'chain
                         := Round_Declaration.cb___init''
                      |)
                      (| h2'chain
                         := Round_Declaration.cc___init''
                      |)
                      (| h3'chain
                         := Round_Declaration.cd___init''
                      |)
                      (| h4'chain
                         := Round_Declaration.ce___init''
                      |)
                |)
              )
              ( Round_Declaration.loop__1__j'' + (2 :: int) )
              Round_Declaration.x''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)

lemma goal76'1: 
  assumes R1: " (0 :: int) <= Round_Declaration.integer__size'' "
  assumes R2: 
  " Round_Declaration.integer__first'' <= Round_Declaration.integer__last''
  "
  assumes R3: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__base__last''
  "
  assumes R4: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__first''
  "
  assumes R5: 
  " Round_Declaration.integer__last''
    <= Round_Declaration.integer__base__last''
  "
  assumes R6: 
  " (0 :: int) <= Round_Declaration.interfaces__unsigned_32__size''
  "
  assumes R7: 
  " Round_Declaration.interfaces__unsigned_32__first'' = (0 :: int)
  "
  assumes R8: 
  " Round_Declaration.interfaces__unsigned_32__last''
    = (4294967295 :: int)
  "
  assumes R9: 
  " Round_Declaration.interfaces__unsigned_32__base__first''
    = (0 :: int)
  "
  assumes R10: 
  " Round_Declaration.interfaces__unsigned_32__base__last''
    = (4294967295 :: int)
  "
  assumes R11: 
  " Round_Declaration.interfaces__unsigned_32__modulus''
    = (4294967296 :: int)
  "
  assumes R12: 
  " (0 :: int) <= Round_Declaration.wordops__word__size''
  "
  assumes R13: 
  " Round_Declaration.wordops__word__first'' = (0 :: int)
  "
  assumes R14: 
  " Round_Declaration.wordops__word__last'' = (4294967295 :: int)
  "
  assumes R15: 
  " Round_Declaration.wordops__word__base__first'' = (0 :: int)
  "
  assumes R16: 
  " Round_Declaration.wordops__word__base__last''
    = (4294967295 :: int)
  "
  assumes R17: 
  " Round_Declaration.wordops__word__modulus'' = (4294967296 :: int)
  "
  assumes R18: 
  " (0 :: int) <= Round_Declaration.wordops__rotate_amount__size''
  "
  assumes R19: 
  " Round_Declaration.wordops__rotate_amount__first'' = (0 :: int)
  "
  assumes R20: 
  " Round_Declaration.wordops__rotate_amount__last'' = (15 :: int)
  "
  assumes R21: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes R22: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__first''
  "
  assumes R23: 
  " Round_Declaration.wordops__rotate_amount__last''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes R24: " (0 :: int) <= Round_Declaration.word__size'' "
  assumes R25: " Round_Declaration.word__first'' = (0 :: int) "
  assumes R26: 
  " Round_Declaration.word__last'' = (4294967295 :: int)
  "
  assumes R27: 
  " Round_Declaration.word__base__first'' = (0 :: int)
  "
  assumes R28: 
  " Round_Declaration.word__base__last'' = (4294967295 :: int)
  "
  assumes R29: 
  " Round_Declaration.word__modulus'' = (4294967296 :: int)
  "
  assumes R30: " (0 :: int) <= Round_Declaration.chain__size'' "
  assumes R31: 
  " ALL ( A'' :: chain' ) ( B'' :: chain' )
    .   h0'chain A'' = h0'chain B''
        & h1'chain A'' = h1'chain B''
        & h2'chain A'' = h2'chain B''
        & h3'chain A'' = h3'chain B''
        & h4'chain A'' = h4'chain B''
        --> A'' = B''
  "
  assumes R32: 
  " (0 :: int) <= Round_Declaration.block_index__size''
  "
  assumes R33: 
  " Round_Declaration.block_index__first'' = (0 :: int)
  "
  assumes R34: 
  " Round_Declaration.block_index__last'' = (15 :: int)
  "
  assumes R35: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__base__last''
  "
  assumes R36: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__first''
  "
  assumes R37: 
  " Round_Declaration.block_index__last''
    <= Round_Declaration.block_index__base__last''
  "
  assumes R38: 
  " (0 :: int) <= Round_Declaration.round_index__size''
  "
  assumes R39: 
  " Round_Declaration.round_index__first'' = (0 :: int)
  "
  assumes R40: 
  " Round_Declaration.round_index__last'' = (79 :: int)
  "
  assumes R41: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__base__last''
  "
  assumes R42: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__first''
  "
  assumes R43: 
  " Round_Declaration.round_index__last''
    <= Round_Declaration.round_index__base__last''
  "
  assumes R44: 
  " (0 :: int) <= Round_Declaration.chain_pair__size''
  "
  assumes R45: 
  " ALL ( A'' :: chain_pair' ) ( B'' :: chain_pair' )
    .   left'chain_pair A'' = left'chain_pair B''
        & right'chain_pair A'' = right'chain_pair B''
        --> A'' = B''
  "
  assumes R46: 
  " (0 :: int) <= Round_Declaration.rotate_amount__size''
  "
  assumes R47: 
  " Round_Declaration.rotate_amount__first'' = (0 :: int)
  "
  assumes R48: 
  " Round_Declaration.rotate_amount__last'' = (15 :: int)
  "
  assumes R49: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes R50: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__first''
  "
  assumes R51: 
  " Round_Declaration.rotate_amount__last''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes R52: 
  " ALL ( i1'' :: int ) ( v'' :: int )
    .   ( Round_Declaration.block___mk_const_arr' v'' ) i1'' = v''
  "
  assumes H1: 
  " Round_Declaration.chain_pair___default_rcd''
    (| left'chain_pair
       := Round_Declaration.chain___default_rcd''
          (| h0'chain
             := Round_Declaration.cla''
          |)
          (| h1'chain
             := Round_Declaration.clb''
          |)
          (| h2'chain
             := Round_Declaration.clc''
          |)
          (| h3'chain
             := Round_Declaration.cld''
          |)
          (| h4'chain
             := Round_Declaration.cle''
          |)
    |)
    (| right'chain_pair
       := Round_Declaration.chain___default_rcd''
          (| h0'chain
             := Round_Declaration.cra''
          |)
          (| h1'chain
             := Round_Declaration.crb''
          |)
          (| h2'chain
             := Round_Declaration.crc''
          |)
          (| h3'chain
             := Round_Declaration.crd''
          |)
          (| h4'chain
             := Round_Declaration.cre''
          |)
    |)
    = Round_Specification.steps'
        ( Round_Declaration.chain_pair___default_rcd''
          (| left'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ca___init''
                |)
                (| h1'chain
                   := Round_Declaration.cb___init''
                |)
                (| h2'chain
                   := Round_Declaration.cc___init''
                |)
                (| h3'chain
                   := Round_Declaration.cd___init''
                |)
                (| h4'chain
                   := Round_Declaration.ce___init''
                |)
          |)
          (| right'chain_pair
             := Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ca___init''
                |)
                (| h1'chain
                   := Round_Declaration.cb___init''
                |)
                (| h2'chain
                   := Round_Declaration.cc___init''
                |)
                (| h3'chain
                   := Round_Declaration.cd___init''
                |)
                (| h4'chain
                   := Round_Declaration.ce___init''
                |)
          |)
        )
        (80 :: int)
        Round_Declaration.x''
  "
  assumes H2: " (0 :: int) <= Round_Declaration.ca___init'' "
  assumes H3: 
  " Round_Declaration.ca___init'' <= (4294967295 :: int)
  "
  assumes H4: " (0 :: int) <= Round_Declaration.cb___init'' "
  assumes H5: 
  " Round_Declaration.cb___init'' <= (4294967295 :: int)
  "
  assumes H6: " (0 :: int) <= Round_Declaration.cc___init'' "
  assumes H7: 
  " Round_Declaration.cc___init'' <= (4294967295 :: int)
  "
  assumes H8: " (0 :: int) <= Round_Declaration.cd___init'' "
  assumes H9: 
  " Round_Declaration.cd___init'' <= (4294967295 :: int)
  "
  assumes H10: " (0 :: int) <= Round_Declaration.ce___init'' "
  assumes H11: 
  " Round_Declaration.ce___init'' <= (4294967295 :: int)
  "
  assumes H12: 
  " ALL ( i___1'' :: int )
    .   (0 :: int) <= i___1'' & i___1'' <= (15 :: int)
        --> (0 :: int) <= Round_Declaration.x'' i___1''
            & Round_Declaration.x'' i___1'' <= (4294967295 :: int)
  "
  assumes H13: " (0 :: int) <= Round_Declaration.clc'' "
  assumes H14: " Round_Declaration.clc'' <= (4294967295 :: int) "
  assumes H15: " (0 :: int) <= Round_Declaration.crd'' "
  assumes H16: " Round_Declaration.crd'' <= (4294967295 :: int) "
  assumes H17: 
  " (0 :: int)
    <= ( ( Round_Declaration.cb___init'' + Round_Declaration.clc'' )
         mod (4294967296 :: int)
         + Round_Declaration.crd''
       )
       mod (4294967296 :: int)
  "
  assumes H18: 
  " ( ( Round_Declaration.cb___init'' + Round_Declaration.clc'' )
      mod (4294967296 :: int)
      + Round_Declaration.crd''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H19: " (0 :: int) <= Round_Declaration.cld'' "
  assumes H20: " Round_Declaration.cld'' <= (4294967295 :: int) "
  assumes H21: " (0 :: int) <= Round_Declaration.cre'' "
  assumes H22: " Round_Declaration.cre'' <= (4294967295 :: int) "
  assumes H23: 
  " (0 :: int)
    <= ( ( Round_Declaration.cc___init'' + Round_Declaration.cld'' )
         mod (4294967296 :: int)
         + Round_Declaration.cre''
       )
       mod (4294967296 :: int)
  "
  assumes H24: 
  " ( ( Round_Declaration.cc___init'' + Round_Declaration.cld'' )
      mod (4294967296 :: int)
      + Round_Declaration.cre''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H25: " (0 :: int) <= Round_Declaration.cle'' "
  assumes H26: " Round_Declaration.cle'' <= (4294967295 :: int) "
  assumes H27: " (0 :: int) <= Round_Declaration.cra'' "
  assumes H28: " Round_Declaration.cra'' <= (4294967295 :: int) "
  assumes H29: 
  " (0 :: int)
    <= ( ( Round_Declaration.cd___init'' + Round_Declaration.cle'' )
         mod (4294967296 :: int)
         + Round_Declaration.cra''
       )
       mod (4294967296 :: int)
  "
  assumes H30: 
  " ( ( Round_Declaration.cd___init'' + Round_Declaration.cle'' )
      mod (4294967296 :: int)
      + Round_Declaration.cra''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H31: " (0 :: int) <= Round_Declaration.cla'' "
  assumes H32: " Round_Declaration.cla'' <= (4294967295 :: int) "
  assumes H33: " (0 :: int) <= Round_Declaration.crb'' "
  assumes H34: " Round_Declaration.crb'' <= (4294967295 :: int) "
  assumes H35: 
  " (0 :: int)
    <= ( ( Round_Declaration.ce___init'' + Round_Declaration.cla'' )
         mod (4294967296 :: int)
         + Round_Declaration.crb''
       )
       mod (4294967296 :: int)
  "
  assumes H36: 
  " ( ( Round_Declaration.ce___init'' + Round_Declaration.cla'' )
      mod (4294967296 :: int)
      + Round_Declaration.crb''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H37: " (0 :: int) <= Round_Declaration.clb'' "
  assumes H38: " Round_Declaration.clb'' <= (4294967295 :: int) "
  assumes H39: " (0 :: int) <= Round_Declaration.crc'' "
  assumes H40: " Round_Declaration.crc'' <= (4294967295 :: int) "
  assumes H41: 
  " (0 :: int)
    <= ( ( Round_Declaration.ca___init'' + Round_Declaration.clb'' )
         mod (4294967296 :: int)
         + Round_Declaration.crc''
       )
       mod (4294967296 :: int)
  "
  assumes H42: 
  " ( ( Round_Declaration.ca___init'' + Round_Declaration.clb'' )
      mod (4294967296 :: int)
      + Round_Declaration.crc''
    )
    mod (4294967296 :: int)
    <= (4294967295 :: int)
  "
  assumes H43: " (0 :: int) <= Round_Declaration.integer__size'' "
  assumes H44: 
  " Round_Declaration.integer__first'' <= Round_Declaration.integer__last''
  "
  assumes H45: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__base__last''
  "
  assumes H46: 
  " Round_Declaration.integer__base__first''
    <= Round_Declaration.integer__first''
  "
  assumes H47: 
  " Round_Declaration.integer__last''
    <= Round_Declaration.integer__base__last''
  "
  assumes H48: 
  " (0 :: int) <= Round_Declaration.interfaces__unsigned_32__size''
  "
  assumes H49: 
  " (0 :: int) <= Round_Declaration.wordops__word__size''
  "
  assumes H50: 
  " (0 :: int) <= Round_Declaration.wordops__rotate_amount__size''
  "
  assumes H51: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes H52: " (0 :: int) <= Round_Declaration.word__size'' "
  assumes H53: " (0 :: int) <= Round_Declaration.chain__size'' "
  assumes H54: 
  " (0 :: int) <= Round_Declaration.block_index__size''
  "
  assumes H55: 
  " Round_Declaration.block_index__base__first''
    <= Round_Declaration.block_index__base__last''
  "
  assumes H56: 
  " (0 :: int) <= Round_Declaration.round_index__size''
  "
  assumes H57: 
  " Round_Declaration.round_index__base__first''
    <= Round_Declaration.round_index__base__last''
  "
  assumes H58: 
  " (0 :: int) <= Round_Declaration.chain_pair__size''
  "
  assumes H59: 
  " (0 :: int) <= Round_Declaration.rotate_amount__size''
  "
  assumes H60: 
  " Round_Declaration.rotate_amount__base__first''
    <= Round_Declaration.rotate_amount__base__last''
  "
  assumes H61: 
  " Round_Declaration.wordops__rotate_amount__base__first''
    <= (0 :: int)
  "
  assumes H62: 
  " (15 :: int)
    <= Round_Declaration.wordops__rotate_amount__base__last''
  "
  assumes H63: 
  " Round_Declaration.block_index__base__first'' <= (0 :: int)
  "
  assumes H64: 
  " (15 :: int) <= Round_Declaration.block_index__base__last''
  "
  assumes H65: 
  " Round_Declaration.round_index__base__first'' <= (0 :: int)
  "
  assumes H66: 
  " (79 :: int) <= Round_Declaration.round_index__base__last''
  "
  assumes H67: 
  " Round_Declaration.rotate_amount__base__first'' <= (0 :: int)
  "
  assumes H68: 
  " (15 :: int) <= Round_Declaration.rotate_amount__base__last''
  "
  shows " Round_Declaration.chain___default_rcd''
          (| h0'chain
             := ( ( Round_Declaration.cb___init'' + Round_Declaration.clc'' )
                  mod (4294967296 :: int)
                  + Round_Declaration.crd''
                )
                mod (4294967296 :: int)
          |)
          (| h1'chain
             := ( ( Round_Declaration.cc___init'' + Round_Declaration.cld'' )
                  mod (4294967296 :: int)
                  + Round_Declaration.cre''
                )
                mod (4294967296 :: int)
          |)
          (| h2'chain
             := ( ( Round_Declaration.cd___init'' + Round_Declaration.cle'' )
                  mod (4294967296 :: int)
                  + Round_Declaration.cra''
                )
                mod (4294967296 :: int)
          |)
          (| h3'chain
             := ( ( Round_Declaration.ce___init'' + Round_Declaration.cla'' )
                  mod (4294967296 :: int)
                  + Round_Declaration.crb''
                )
                mod (4294967296 :: int)
          |)
          (| h4'chain
             := ( ( Round_Declaration.ca___init'' + Round_Declaration.clb'' )
                  mod (4294967296 :: int)
                  + Round_Declaration.crc''
                )
                mod (4294967296 :: int)
          |)
          = Round_Specification.round'
              ( Round_Declaration.chain___default_rcd''
                (| h0'chain
                   := Round_Declaration.ca___init''
                |)
                (| h1'chain
                   := Round_Declaration.cb___init''
                |)
                (| h2'chain
                   := Round_Declaration.cc___init''
                |)
                (| h3'chain
                   := Round_Declaration.cd___init''
                |)
                (| h4'chain
                   := Round_Declaration.ce___init''
                |)
              )
              Round_Declaration.x''
        " (is "?C1")
apply (insert assms) by (rule userlemmas)
end
