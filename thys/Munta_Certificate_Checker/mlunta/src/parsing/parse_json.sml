signature PARSE_JSON = sig
  val ta:
      JsonP.json -> (string * ParseJsonTypes.automaton) Error.res

  val net:
      JsonP.json -> ParseJsonTypes.network Error.res
end

structure ParseJson : PARSE_JSON = struct
open Either

(* fun singleton_err f = f #> mapL single *)

(* getting Node info *)
val id' = JsonP.find_int "id"
val invar = JsonP.find_str "invariant"

(* getting edge info *)
val source = JsonP.find_int "source"
val target = JsonP.find_int "target"
val guard = JsonP.find_str "guard"
val update = JsonP.find_str "update"
val label = JsonP.find_str "label"

fun optional_list get =
    bindL (fn [errs] =>
              if Error.json_err_not_in errs then succeed []
              else fail [errs])
    #> bindR (combine_map get)
(* getting TA info *)
val name = JsonP.find_str "name"
val initial = JsonP.find_int "initial"
val e = JsonP.find_arr "edges"
val v = JsonP.find_arr "nodes"
val committed =
    JsonP.find_arr "committed" #> optional_list (JsonP.get_int "committed")

(* Getting Network info *)
val automata = JsonP.find_arr "automata"
val broadcast_channels =
    JsonP.find_arr "broadcast" #> optional_list (JsonP.get_str "broadcast")
val formula = JsonP.find_str "formula"
val clocks = JsonP.find_str "clocks"
val vars = JsonP.find_str "vars"

(* Constructors for the different types *)
val edge_constr = fn ((label,(l,g)),(upd, l')) =>
                     {
                       label = label,
                       source = l,
                       target = l',
                       guard = g,
                       update = upd
                     }

val node_constr = fn ((id, invar), name) =>
                     {
                       id = id,
                       name = name,
                       invar = invar
                     }

val ta_constr = fn (((name, initial), (E, V)), committed) =>
                   (name ,
                    {
                      nodes = V,
                      edges = E,
                      initial = initial,
                      committed = committed
                   })

val net_constr = fn (((clcks, vars), (formula, tas)), broadcast_channels) =>
                    {
                      automata = tas,
                      clocks = clcks,
                      vars = vars,
                      formula = formula,
                      broadcast_channels = broadcast_channels
                    }

fun edge json  =
    ((label json <|> (source json <|> guard json)) <|>
        (update json <|> target json))
    |> mapR edge_constr

fun node json =
    ((id' json <|> invar json) <|> name json)
    |> mapR node_constr

fun pipe f g x =
    x |> f |> bindR (combine_map g)

fun ta json =
    (((name json <|> initial json)
    <|> (pipe e edge json <|> pipe v node json))
    <|> committed json)
    |> mapR ta_constr

fun net json =
    (((clocks json <|>  vars json)
    <|> (formula json <|> pipe automata ta json))
    <|> broadcast_channels json)
    |> mapR net_constr

end
