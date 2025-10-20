structure ReachabilityData = struct
val explored = Unsynchronized.ref 0
end

functor ReachabilityChecker(Setup : CHECKING_SETUP) = struct
structure D = Setup.D
structure Basic = BasicSetup(D)
structure Passed = Setup.Passed
structure PWList = PassedToPWList(structure P = Passed)

local open Unsynchronized in

val count = ReachabilityData.explored
fun counting f x = time count f x
fun bfs formula succs P = let
    fun fold_succs s =
      fold_until_snd (fn (norm, (state' as (pw, brk'))) =>
                      if (D.empty o Network.zone) norm then state'
                      else PWList.insert formula pw norm) s

    fun reachability pw =
      case PWList.get pw of
          NONE => (pw, false) |
          SOME ((ref l, ref D), pw) => (
            (Unsynchronized.inc count;
             case fold_succs (pw, false) (succs (l, D)) of
                (trace, true) => (trace, true) |
                (trace, _) => reachability trace
            )
          )
in
  reachability P
end
end

fun check system =
    let
      val setup = Basic.initial_setup system
      val (P, norm, initial) = (Basic.P setup,
                                Basic.norm setup,
                                Basic.initial setup)
      val succf = #trans system #> map norm
      val PW = foldl_until snd
                          (fn (state, (pw, b)) =>
                              if (D.empty o Network.zone) state then (pw, b)
                              else PWList.insert P pw state)
                          (PWList.make 4096, false)
                          [initial]
    in
      case PW of
          (PW, true) => (PW, true) |
          (PW, _ ) =>  bfs P succf PW
    end
end
