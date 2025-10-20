functor LeadsTo(Setup : CHECKING_SETUP) = struct
structure Passed = Setup.Passed
structure D = Setup.D
structure LeadsToSetup = LeadstoSetup(D)
structure PWList = PassedToPWList(structure P = Passed)
structure Reachability = ReachabilityChecker(Setup)
structure Cyclicity = CyclicityChecker(Setup)

fun nfoldli f = PWList.fold_until snd f

fun init n =
    Passed.mkTable n

fun leadsto succs_p succs_q p q P =
    let
      val st = init 32
      fun reachability P =
          Reachability.bfs (K false) succs_p P
      fun has_cycle q s =
          Cyclicity.dfs succs_q s st
      fun inner P =
          let
            val (P, _) = reachability P
          in
            nfoldli
                (fn (l, D, (passed, _)) =>
                    let val s = (l, D) in
                      if p s andalso q s then has_cycle q s passed |>> fst
                      else (passed, false) end)
                P (init 32, false)
          end
    in
      inner P
    end

fun check (system : D.t Network.system) =
    let
      val setup =
          LeadsToSetup.initial_setup system
      val (P, Q, norm, initial) = (
        LeadsToSetup.P setup,
        LeadsToSetup.Q setup,
        LeadsToSetup.norm setup,
        LeadsToSetup.initial setup
      )
      val succs = #trans system
      val succs_p = succs #> map norm
      val succs_q = succs #> filter Q #> map norm
      val insert = PWList.insert (K false)
      val PW = foldl
                   (fn (zone, pw) => if (D.empty o Network.zone) zone then pw
                                     else insert pw zone |> fst)
                  (PWList.make 4096)
                  [initial]
    in
      leadsto succs_p succs_q P Q PW
    end
end
