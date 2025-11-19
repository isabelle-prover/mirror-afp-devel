(* XXX: Maybe do this via the already defined jsonP*)
structure BenchMarkTA = struct
type edge = {
  source : string,
  target : string,
  label : string,
  update : string,
  guard : string
}

fun edge_to_str ({source, target, guard, label, update} : edge) =
    "{" ^
    "\"source\":" ^ source ^ "," ^
    "\"target\":" ^ target ^ "," ^
    "\"label\":\"" ^ label ^ "\"," ^
    "\"update\":\"" ^ update ^ "\"," ^
    "\"guard\":\"" ^ guard ^ "\"" ^
    "}"

type node = {
  name : string,
  id : string,
  invariant : string
}

fun node_to_str ({name, id, invariant} : node)=
    "{" ^
    "\"name\":\"" ^ name ^ "\"," ^
    "\"id\":" ^ id ^ "," ^
    "\"invariant\":\"" ^ invariant ^ "\"" ^
    "}"

type automaton = {
  name : string,
  initial : string,
  nodes : node list,
  edges : edge list
}

fun automaton_to_str ({name, initial, nodes, edges} : automaton) =
    "{" ^
    "\"name\":\"" ^ name ^ "\"," ^
    "\"initial\":" ^ initial ^ "," ^
    "\"nodes\":[" ^ (map node_to_str nodes |> separate "," |> String.concat) ^ "]," ^
    "\"edges\":[" ^ (map edge_to_str edges |> separate "," |> String.concat) ^ "]" ^
    "}"

type var_bound = {lower : int, upper : int, name : string}

fun var_to_str ({lower, upper, name} : var_bound) =
    name ^ "[" ^ (Int.toString lower) ^ ":" ^ (Int.toString upper) ^ "]"

type network = {
  automata : automaton list,
  clocks : string list,
  vars : var_bound list,
  formula: string
}
fun vars_to_str clocks =
    map var_to_str clocks
    |> separate ","
    |> String.concat

fun network_to_str ({automata, clocks, vars, formula} : network) =
    "{" ^
    "\"automata\":[" ^ (map automaton_to_str automata |> separate "," |> String.concat) ^ "]," ^
    "\"clocks\":\"" ^ (separate "," clocks |> String.concat) ^ "\"," ^
    "\"vars\":\"" ^ (vars_to_str vars) ^ "\"," ^
    "\"formula\":\"" ^ formula ^ "\"" ^
    "}"

end

structure FischerGen = struct
fun gen n = (curry List.tabulate) n

fun edges i =
      [
        {
          source = "0",
          target = "1",
          guard = "id = 0",
          label = "",
          update = "x" ^ i ^ " := 0"
        },
        {
          source = "1",
          target = "2",
          guard = "x" ^ i ^ " <= 2",
          label = "",
          update = "x" ^ i ^ " := 0, id := " ^ i
        },
        {
          source = "2",
          target = "1",
          guard = "id = 0",
          label = "",
          update = "x" ^ i ^ ":= 0"
        },
        {
          source = "2",
          target = "3",
          guard = "x" ^ i ^ " > 2 && id = " ^ i,
          label = "",
          update = ""
        },
        {
          source = "3",
          target = "0",
          guard = "",
          label = "",
          update = "x" ^ i ^ " := 0, id := 0"
        }
      ]

fun nodes i =
      [
        {
          id = "0",
          name = "A",
          invariant = ""
        },
        {
          id = "1",
          name = "B",
          invariant = "x" ^ i ^ " <= 2"
        },
        {
          id = "2",
          name = "C",
          invariant = ""
       },
        {
          id = "3",
          name = "CS",
          invariant = ""
        }
      ]

fun ta init i =
    let val i = Int.toString (i + 1) in
      {
        name = "P" ^ i,
        initial = Int.toString init,
        nodes = nodes i,
        edges = edges i
      }
    end

fun clocks str n =
    gen n (fn i => str ^ (Int.toString (i + 1)))

fun network n f =
    {
      automata = gen n (ta 0),
      clocks = clocks "x" n,
      vars = [{lower = 0, upper = n, name = "id"}],
      formula = f
    }

fun leadsto_f n = let val i = Int.toString n in "P" ^ i ^ ".B --> P" ^ i ^ ".C" end
fun reach_f n =
    let
      val F = "E<> ("
      val sections = flip gen (fn i => "P" ^ (Int.toString (i + 1)) ^ ".CS")
      fun ors i = if i = 0 then [] else gen (i - 1) (fn i => "P" ^ (Int.toString (i + 1) ^ ".CS"))
      fun inner n =
          sections n
          |> drop 1
          |> map_index (fn (i, e) => "(" ^ e ^ " && (" ^ (ors (i + 2) |> String.concatWith " || ") ^ "))")
          |> foldl1 (fn (p, acc) => acc ^ " || " ^ p)
    in
      if n >= 2 then F ^ inner n ^ ")"
      else Exn.error "Should have at least 2 as input"
    end

fun string b n =
    network n (if b then reach_f n else leadsto_f n)
    |> BenchMarkTA.network_to_str

fun file b n =
    let
      val json_str = string b n
      val out_strm = TextIO.openOut ("benchmarks/resources/fischer_"
                                     ^ (if b then "R" else "L") ^ "_"
                                     ^ (Int.toString n) ^ ".muntax")
    in
      (
        TextIO.output (out_strm, json_str);
        TextIO.closeOut out_strm
      )
    end
end
