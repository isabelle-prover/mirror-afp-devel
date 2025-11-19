structure FddiGen = struct
fun gen n = (--> List.tabulate) n

fun station_edges i =
      [
        {
          source = "0",
          target = "1",
          guard = "",
          label = "tt" ^ i ^ "?",
          update = "y" ^ i ^ " := 0, x" ^ i ^ ":= 0"
        },
        {
          source = "1",
          target = "2",
          guard = "x" ^ i ^ " >= 20 && z" ^ i ^ " < 320",
          label = "",
          update = ""
        },
        {
          source = "2",
          target = "3",
          guard = "",
          label = "rt" ^ i ^ "!",
          update = ""
        },
        {
          source = "1",
          target = "3",
          guard = "x"  ^ i ^" >= 20 && z" ^ i ^ " >= 320",
          label = "rt" ^ i ^ "!",
          update = ""
        },
        {
          source = "3",
          target = "4",
          guard = "",
          label = "tt" ^ i ^ "?",
          update = "z" ^ i ^ " := 0, x" ^ i ^ ":= 0"
        },
        {
          source = "4",
          target = "0",
          guard = "x" ^ i ^" >= 20 && y" ^ i ^ " >= 320",
          label = "rt" ^ i ^ "!",
          update = ""
        },
        {
          source = "4",
          target = "5",
          guard = "x" ^ i ^ " >= 20 && y" ^ i ^ " < 320",
          label = "",
          update = ""
        },
        {
          source = "5",
          target = "0",
          guard = "",
          label = "rt" ^ i ^ "!",
          update = ""
        }
      ]

fun station_nodes i =
      [
        {
          id = "0",
          name = "z_idle",
          invariant = ""
        },
        {
          id = "1",
          name = "z_sync",
          invariant = "x" ^ i ^ " <= 20"
        },
        {
          id = "2",
          name = "z_async",
          invariant = "z" ^ i ^ " <= 320"
        },
        {
          id = "3",
          name = "y_idle",
          invariant = ""
        },
        {
          id = "4",
          name = "y_sync",
          invariant = "x" ^ i ^ " <= 20"
        },
        {
          id = "5",
          name = "y_async",
          invariant = "y" ^ i ^ " <= 320"
       }
      ]

fun station init i =
    let val i = Int.toString (i + 1) in
      {
        name = "ST" ^ i,
        initial = Int.toString init,
        nodes = station_nodes i,
        edges = station_edges i
      }
    end

fun ring_nodes n =
    gen n (fn i => {id = Int.toString i, name = "ring_to_" ^ (Int.toString (i + 1)), invariant = "x <= 0"}) @
    gen n (fn i => {id = Int.toString (i + n), name = "ring_" ^ (Int.toString (i + 1)), invariant = ""})

fun ring_edges n =
    {
      source = Int.toString (n + n - 1),
      target = "0",
      guard = "",
      update = "x := 0",
      label = "rt" ^ (Int.toString n) ^ "?"
    } ::
    gen n (fn i => {
             source = (Int.toString i),
             target = Int.toString (i + n),
             guard = "x <= 0",
             update = "",
             label = "tt" ^ (Int.toString (i+1)) ^ "!"}) @
    gen (n - 1) (fn i => {
                   source = Int.toString (i + n),
                   target = Int.toString (i + 1),
                   guard = "",
                   update = "x := 0",
                   label = "rt" ^ (Int.toString (i + 1)) ^ "?"})
fun ring init n =
    let val i = Int.toString (n + 1) in
      {
        name = "RING",
        initial = Int.toString init,
        nodes = ring_nodes n,
        edges = ring_edges n
      }
    end

fun clocks str n =
    gen n (fn i => str ^ (Int.toString (i + 1)))

fun network n f =
    {
      automata = ring 0 n :: gen n (station 0),
      clocks = "x" :: clocks "x" n @ clocks "y" n @ clocks "z" n,
      vars = [],
      formula = f
    }

val leadsto_f = "((~ ST1.z_sync) || ST1.z_sync) --> ST1.z_sync"
val reach_f = "E<> " ^
              "((ST1.z_sync || ST1.z_async || ST1.y_sync || ST1.y_async) && " ^
              "(ST2.z_sync || ST2.z_async || ST2.y_sync || ST2.y_async) )"

fun string b n =
    network n (if b then reach_f else leadsto_f)
    |> BenchMarkTA.network_to_str

fun file b n =
    let
      val json_str = string b n
      val out_strm = TextIO.openOut ("benchmarks/resources/fddi_"
                                     ^ (if b then "R" else "L") ^ "_"
                                     ^ (Int.toString n)
                                     ^ ".muntax")
    in
      (
        TextIO.output (out_strm, json_str);
        TextIO.closeOut out_strm
      )
    end
end
