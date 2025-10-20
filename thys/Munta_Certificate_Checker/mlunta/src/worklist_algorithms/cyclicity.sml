structure CyclicityData = struct
val explored = Unsynchronized.ref 0
end

functor CyclicityChecker(Setup : CHECKING_SETUP) = struct
structure Passed = Setup.Passed
structure D = Setup.D
structure Basic = BasicSetup(D)

val count = CyclicityData.explored
fun time f = Unsynchronized.time count f
val pop = flip Passed.pop
val isloop =
    flip (Passed.exists (flip D.subsumption))

fun insert_p P = Passed.insert_p' P

val passed =
    flip (Passed.exists D.subsumption)
val not_empty = not o D.empty o Network.zone
fun dfs succs =
    let
      fun inner_dfs s ST P =
          if isloop s ST then ((P, ST), true)
          else if passed s P then ((P, ST), false)
          else let
            val ST = Passed.push ST s
            val ((P, ST), r) =
                fold_until_snd
                    (fn (s, acc as ((P', ST'), _)) =>
                        if not_empty s then inner_dfs s ST' P'
                        else acc)
                    ((P, ST), false) (succs s)
            val P = insert_p P s
            val _ = pop (Network.discrete s) ST
          in (Unsynchronized.inc count; ((P, ST), r)) end
    in
      inner_dfs
    end

fun check (system : D.t Network.system) =
    let
        val setup =
            Basic.initial_setup  system
        val (P, norm, initial) = (Basic.P setup,
                                  Basic.norm setup,
                                  Basic.initial setup)
        val succf = #trans system #> filter P #> map norm
        val pw =  Passed.mkTable 32
        val st = Passed.mkTable 32
    in
        dfs succf initial st pw
    end

end
