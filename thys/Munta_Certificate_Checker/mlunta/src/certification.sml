functor Certification(
  Setup : CHECKING_SETUP
) = struct

structure D = Setup.D
structure Basic = BasicSetup(D)
structure Passed = Setup.Passed
structure PWList = PassedToPWList(structure P = Passed)

val subsumes = D.subsumption

fun check_invariant (succs: (int array * int array) * D.zone -> ((int array * int array) * D.zone) list) passed =
  let
    val le = subsumes
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
  in
    Passed.fold_until not (fn (l, x, b) => all_subsumed l x andalso b) passed true
  end

fun check_invariant2 succs passed =
  let
    val le = subsumes
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check_pair (l, xs) = all (all_subsumed l) xs
    val pairs = Passed.kv_list passed
  in
    all check_pair pairs
  end

fun check_invariant3 succs passed =
  let
    val le = subsumes
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check_pair (l, xs) = all (all_subsumed l) xs
    val pairs = Passed.kv_list passed
  in
    all id (Par_List.map check_pair pairs)
  end

fun check_invariant3 succs passed =
  let
    val le = subsumes
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check_pair (l, xs) = all (all_subsumed l) xs
    val pairs = Passed.kv_list passed
  in
    all id (Par_List.map check_pair pairs)
  end

fun hm_sat P m k =
  case Isa_Map.hm_lookup1 k m of
    NONE => false
  | SOME x => P x

val array_to_list = Array.foldr (op ::) []

fun check_invariant4 succs passed =
  let
    val le = subsumes
    val pairs = Passed.kv_list passed
    fun map_pair (L, s) = (array_to_list L, array_to_list s)
    val m = Isa_Map.hashmap_of_list1 (map (fn (l, xs) => (map_pair l, xs)) pairs)
    fun is_subsumed (l, x) = hm_sat (exists (le x)) m (map_pair l)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check_pair (l, xs) = all (all_subsumed l) xs
  in
    all check_pair pairs
  end

fun check_invariant5 succs passed =
  let
    val le = subsumes
    val pairs = Passed.kv_list passed
    fun map_pair (L, s) = (array_to_list L, array_to_list s)
    val m = Isa_Map.hashmap_of_list1 (map (fn (l, xs) => (map_pair l, xs)) pairs)
    fun is_subsumed (l, x) = hm_sat (exists (le x)) m (map_pair l)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check_pair (l, xs) = all (all_subsumed l) xs
  in
    all id (Par_List.map check_pair pairs)
  end


fun check version discrete_succs system pw =
  let
    val setup = Basic.initial_setup system
    val (_, norm, initial) = (
      Basic.P setup,
      Basic.norm setup,
      Basic.initial setup)
    val succs = #trans system #> map norm #> flat
    val checker =
      case version of
        1 => check_invariant
      | 2 => check_invariant2
      | 3 => check_invariant3
      | 4 => check_invariant4
      | 5 => check_invariant5
      | _ => K false |> K
    val checker = fn succs => fn passed =>
      let
        val r = Benchmark.time_it (checker succs) passed
        val _ = Log.time "Time for certifiate checking" (#time r)
      in #result r end
  in
    if version > 0 then
      pw
      |> (fn x => (print "Starting certificate checking\n"; x))
      |> checker succs
      |> (fn x => (print "Finished certificate checking\n"; x))
    else false
  end

end