structure CsmaGen = struct
fun gen n = (--> List.tabulate) n
fun p0_nodes n =
    [
      {id = Int.toString n,
       name = "bus_idle",
      invariant = ""},
      {id = Int.toString (n + 1),
       name = "bus_active",
       invariant = ""}
    ] @ gen n (fn i => if i = 0 then {id = Int.toString i, name = "bus_collision" ^ (Int.toString (i + 1)),
                       invariant = "x <= 26"}
                      else {id = Int.toString i, name = "bus_collision" ^ (Int.toString (i + 1)),
                       invariant = "x <= 0"})
fun p0_edges n =
    [{
      source = Int.toString n,
      target = Int.toString (n + 1),
      guard = "",
      update = "x := 0",
      label = "begin?"
    },
     {
      source = Int.toString (n + 1),
      target = Int.toString n,
      guard = "",
      update = "x:=0",
      label = "end?"
     },
     {
      source = Int.toString (n + 1),
      target = Int.toString (n + 1),
      guard = "x >= 26",
      update = "",
      label = "busy!"
     },
     {
       source = Int.toString (n + 1),
       target = Int.toString 0,
       guard = "x < 26",
       update = "x := 0",
       label = "begin?"
     },
     {
       source = Int.toString (n - 1),
       target = Int.toString n,
       guard = "x <= 0",
       update = "x := 0",
       label = "cd" ^ (Int.toString n) ^ "!"
     }
    ] @ gen (n - 1) (fn i => let val id = i + 1 in
                             if i = 0 then
                               {
                                source = Int.toString i,
                                target = Int.toString id,
                                guard = "x < 26",
                                update = "",
                                label = "cd" ^ (Int.toString id) ^ "!"
                              }
                             else
                              {
                                source = Int.toString i,
                                target = Int.toString id,
                                guard = "x <= 0",
                                update = "",
                                label = "cd" ^ (Int.toString id) ^ "!"
                              } end)
fun p0 n =
    {
      name = "P0",
      nodes = p0_nodes n,
      edges = p0_edges n,
      initial = Int.toString n
    }

fun pi_nodes i = [
  {
    id = "0",
    name = "sender_wait",
    invariant = ""
  },
  {
    id = "1",
    name = "sender_transm",
    invariant = "x" ^ i ^ " <= 808"
  },
  {
    id = "2",
    name = "sender_retry",
    invariant = "x" ^ i ^ " <= 52"
  }]

fun pi_edges_wait i = [
  {
    source = "0",
    target = "1",
    update = "x" ^ i ^ " := 0",
    label = "begin!",
    guard = ""
  },
  {
    source = "0",
    target = "0",
    update = "x" ^ i ^ " := 0",
    label = "cd" ^ i ^ "?",
    guard = ""
  },
  {
    source = "0",
    target = "2",
    update = "x" ^ i ^ " := 0",
    label = "cd" ^ i ^ "?",
    guard = ""
  },
  {
    source = "0",
    target = "2",
    update = "x" ^ i ^ " := 0",
    label = "busy?",
    guard = ""
  }
]

fun pi_edges_transm i =
    [
      {
        source = "1",
        target = "0",
        update = "x := 0",
        label = "end!",
        guard = "x" ^ i ^ " = 808"

      },
      {
        source = "1",
        target = "2",
        update = "x" ^ i ^" := 0",
        label = "cd" ^ i ^ "?",
        guard = "x" ^ i ^ " < 52"
      }
    ]

fun pi_nodes_fst i = [
  {
    id = "0",
    name = "sender_wait",
    invariant = ""
  },
  {
    id = "1",
    name = "sender_transm",
    invariant = "x" ^ i ^ " <= 808"
  },
  {
    id = "2",
    name = "sender_retry",
    invariant = "x" ^ i ^ " <= 52"
  },
  {
    id = "3",
    name = "sender_transm_check",
    invariant = ""
  }
]

fun pi_edges_wait_fst i = [
  {
    source = "0",
    target = "1",
    update = "x" ^ i ^ " := 0",
    label = "begin!",
    guard = ""
  },
  {
    source = "0",
    target = "0",
    update = "x" ^ i ^ " := 0",
    label = "cd" ^ i ^ "?",
    guard = ""
  },
  {
    source = "0",
    target = "2",
    update = "x" ^ i ^ " := 0",
    label = "cd" ^ i ^ "?",
    guard = ""
  },
  {
    source = "0",
    target = "2",
    update = "x" ^ i ^ " := 0",
    label = "busy?",
    guard = ""
  }
]

fun pi_edges_transm_fst i =
    [
      {
        source = "1",
        target = "0",
        update = "x := 0",
        label = "end!",
        guard = "x" ^ i ^ " = 808"

      },
      {
        source = "1",
        target = "2",
        update = "x" ^ i ^" := 0",
        label = "cd" ^ i ^ "?",
        guard = "x" ^ i ^ " < 52"
      },
      {
        source = "1",
        target = "3",
        update = "",
        label = "",
        guard = "x" ^ i ^ " >= 52"
      },
      {
        source = "3",
        target = "1",
        update = "",
        label = "",
        guard = ""
      }
    ]

fun pi_edges_retry i =
    [
      {
        source = "2",
        target = "1",
        update = "x" ^ i ^ " := 0",
        label = "begin!",
        guard = "x" ^ i ^ " < 52"
      },
      {
        source = "2",
        target = "2",
        update = "x" ^ i ^ " := 0",
        label = "cd" ^ i ^ "?",
        guard = "x" ^ i ^ " < 52"
      }
    ]

fun pi_edges id =
    let val i = Int.toString id in
      (if id = 1 then
         pi_edges_wait_fst i @ pi_edges_transm_fst i else pi_edges_wait i @ pi_edges_transm i) @ pi_edges_retry i
    end
fun leadsto_f n = "( "
                  ^ (gen n (fn i => "P0.bus_collision" ^ (Int.toString (i + 1)))
                  |> separate " || " |> String.concat)
                  ^ " ) --> " ^ "P0.bus_active"
val reach_f = "E<> ( P1.sender_transm_check && P2.sender_transm )"

fun ta i = let fun pi_nodes' id = let val i = Int.toString id in (if id = 1 then pi_nodes_fst i else pi_nodes i) end in
    {
      name = "P" ^ (Int.toString (i + 1)),
      nodes = pi_nodes' (i + 1),
      edges = pi_edges (i + 1),
      initial = "0"
    } end
fun network n f =
    {
      automata = p0 n :: (gen n ta),
      clocks = "x" :: gen n (fn i => "x" ^ Int.toString (i + 1)),
      formula = f,
      vars = []
    }
fun string b n =
    network n (if b then reach_f else leadsto_f n)
    |> BenchMarkTA.network_to_str

fun file b n =
    let
      val json_str = string b n
      val out_strm = TextIO.openOut ("benchmarks/resources/csma_"
                                     ^ (if b then "R" else "L") ^ "_"
                                     ^ (Int.toString n) ^ ".muntax")
    in
      (
        TextIO.output (out_strm, json_str);
        TextIO.closeOut out_strm
      )
    end
end
