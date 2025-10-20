functor Compression(
  Setup : CHECKING_SETUP
) = struct

structure D = Setup.D
structure Basic = BasicSetup(D)
structure Passed = Setup.Passed
structure PWList = PassedToPWList(structure P = Passed)

(* This can go wrong if ?i<j. xs ! i <= xs ! j && xs ! j <= xs ! i *)
fun filter_subsumed (le: 'a -> 'a -> bool) (xs: 'a list): 'a list =
  let
    fun is_subsumed x i j [] = false
      | is_subsumed x i j (y :: ys) =
        if i = j then
          is_subsumed x i (j + 1) ys
        else
          le x y orelse is_subsumed x i (j + 1) ys
  in filter_index (fn i => fn x => is_subsumed x i 0 xs |> not) xs |> rev end

fun compress1 le _ _ _ = map (apsnd (filter_subsumed le))

fun compress2 le (succs: (int array * int array) * D.zone -> ((int array * int array) * D.zone) list) passed xs =
  let
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun f l xs =
      let
        val x = D.convex_hull xs
        val x = D.close x
      in if all_subsumed l x then (l, [x]) else (l, xs) end
  in map (fn (l, ys) => if length ys <= 1 then (l, ys) else f l ys) xs end

fun compress3 le (succs: (int array * int array) * D.zone -> ((int array * int array) * D.zone) list) passed xs =
  let
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun f l (ys as (x :: y :: xs)) =
      let
        (* XXX If we comment out this line, then we can produce an extremely small *valid*
           certificate for fischer_05.muntax *)
        val x = D.copy x
        val z = D.or x y
      in if all_subsumed l z then (l, z :: xs) else (l, ys) end
      | f l xs = (l, xs)
  in map (fn (l, ys) => f l ys) xs end

fun compress4 le succs passed xs =
  let
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check l xs i j =
      let
        val x = nth xs i
        val y = nth xs j
        val x = D.copy x
        val z = D.or x y
      in if all_subsumed l z then SOME z else NONE end
    fun loop l xs i n =
      let
        fun loopi j =
          if i = j then
            if j < n then loopi (j + 1) else NONE
          else
            case check l xs i j of
              SOME x => SOME (i, j, x)
            | NONE =>
              if j < n then
                loopi (j + 1)
              else if i < n then
                loop l xs (i + 1) n
              else NONE
      in loopi 0 end
    fun f l xs =
      if length xs > 1 then
        case loop l xs 0 (length xs - 1) of
          NONE => (l, xs)
        | SOME (i, j, x) => (l, x :: remove (j - 1) (remove i xs))
      else (l, xs)
  in map (fn (l, ys) => f l ys) xs end

fun compress5 le discrete_succs succs passed xs active =
  let
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check l xs i j =
      let
        val x = nth xs i
        val y = nth xs j
        val x = D.copy x
        val z = D.or x y
      in if all_subsumed l z then SOME z else NONE end
    fun loop l xs i n =
      let
        fun loopi j =
          if i = j then
            if j < n then loopi (j + 1) else NONE
          else
            case check l xs i j of
              SOME x => SOME (i, j, x)
            | NONE =>
              if j < n then
                loopi (j + 1)
              else if i < n then
                loop l xs (i + 1) n
              else NONE
      in loopi 0 end
    fun f l xs =
      if length xs > 1 andalso member (fn (x, y) => x = y) active l then
        case loop l xs 0 (length xs - 1) of
          NONE => NONE
        | SOME (i, j, x) => SOME (x :: remove (j - 1) (remove i xs))
      else NONE
    val (new, acc) = fold
      (fn (l, ys) => fn (new, acc) =>
        case f l ys of
          NONE => (new, (l, ys) :: acc)
        | SOME ys => (l :: new, (l, ys) :: acc)
      ) xs ([], [])
    val xs = rev acc
    val active =
      filter (discrete_succs #> exists (member (fn (x, y) => x = y) new)) (map fst xs) @ new
  in (active, xs) end

fun compress6 le discrete_succs succs passed xs active =
  let
    fun is_subsumed (l, x) = Passed.exists le passed (l, x)
    fun all_subsumed l x = all is_subsumed (succs (l, x))
    fun check l x y =
      let
        val x = D.copy x
        val z = D.or x y
      in if all_subsumed l z then SOME z else NONE end
    fun find_any l x acc [] = NONE
      | find_any l x acc (y :: xs) =
        case check l x y of
          NONE => find_any l x (y :: acc) xs
        | SOME z => SOME (rev (z :: acc) @ xs)
    fun loop l done [] = rev done
      | loop l done (x :: xs) =
        case find_any l x [] xs of
          NONE => loop l (x :: done) xs
        | SOME xs => loop l [] (rev done @ xs)
    fun f l xs =
      if length xs > 1 andalso member (fn (x, y) => x = y) active l then
        let
          val ys = loop l [] xs
        in if length ys < length xs then SOME ys else NONE end
      else NONE
    val (new, acc) = fold
      (fn (l, ys) => fn (new, acc) =>
        case f l ys of
          NONE => (new, (l, ys) :: acc)
        | SOME ys => (l :: new, (l, ys) :: acc)
      ) xs ([], [])
    val xs = rev acc
    val active =
      filter (discrete_succs #> exists (member (fn (x, y) => x = y) new)) (map fst xs)
  in (active, xs) end

fun sum_list (f: 'a -> int) xs: int = fold (fn x => fn s => f x + s) xs 0

val num_states_of = sum_list (fn (_, xs) => sum_list (fn _ => 1) xs)

fun table_from_list xs =
  let
    val init = Passed.mkTable (List.length xs)
    fun f (l, xs) = fold (fn x => fn passed => Passed.insert_p' passed (l, x)) xs
  in fold f xs init end

fun iter_compression compress le _ succs passed _ =
  let
    fun loop passed i =
      let
        val _ = i |> Int.toString |> (fn x => x ^ "\n") |> print
        val xs = Passed.kv_list passed
        val n1 = num_states_of xs
        val xs = compress le succs passed xs
        val n2 = num_states_of xs
      in
        if n1 = n2 then
          (i |> Int.toString |> (fn s => print ("Terminated after " ^ s ^ " iterations\n")); xs)
        else
          loop (table_from_list xs) (i + 1)
      end
  in loop passed 0 end

fun iter_compression2 compress le discrete_succs succs passed _ =
  let
    fun loop active passed i =
      let
        val _ = i |> Int.toString |> (fn x => x ^ "\n") |> print
        val xs = Passed.kv_list passed
        val n1 = num_states_of xs
        val (active, xs) = compress le discrete_succs succs passed xs active
        val n2 = num_states_of xs
      in
        if n1 = n2 then
          (i |> Int.toString |> (fn s => print ("Terminated after " ^ s ^ " iterations\n")); xs)
        else
          loop active (table_from_list xs) (i + 1)
      end
  in loop (passed |> Passed.kv_list |> map fst) passed 0 end

fun do_compression le discrete_succs (succs: (int array * int array) * D.zone -> ((int array * int array) * D.zone) list) compress passed =
  let
    val xs = Passed.kv_list passed
    val n1 = num_states_of xs
    val xs = compress le discrete_succs succs passed xs
    val n2 = num_states_of xs
    val factor = (1.0 - real n2 / real n1) * 100.0
    val _ = print ("Compressed certificate by: " ^ Real.toString factor ^ "%\n")
  in table_from_list xs end

fun compress compression discrete_succs system pw =
  let
    val setup = Basic.initial_setup system
    val (_, norm, initial) = (
      Basic.P setup,
      Basic.norm setup,
      Basic.initial setup)
    val succs = #trans system #> map norm #> flat
    val subsumes = D.subsumption
    val pw = pw |> do_compression subsumes discrete_succs succs compress1
    val compressor =
      case compression of
        2 => iter_compression compress2
      | 3 => iter_compression compress3
      | 4 => iter_compression compress4
      | 5 => iter_compression2 compress5
      | 6 => iter_compression2 compress6
      | _ => id |> K |> K |> K |> K
  in
    if compression > 1 then
      pw
      |> (fn x => (print "Starting second compression stage\n"; x))
      |> do_compression subsumes discrete_succs succs compressor
      |> (fn x => (print "Finished second compression stage\n"; x))
    else pw
  end

end
