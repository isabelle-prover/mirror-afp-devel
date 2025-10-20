signature PROTO_NETWORK = sig
type 'a edge =
     {
       target : int,
       clock_updates : 'a -> 'a,
       var_updates : int Array.array -> int Array.array option,
       g_data : int Array.array -> bool,
       g: 'a -> 'a
     }

type 'a node =
     {
       invariant : 'a -> 'a
     }

type 'a nodes = 'a node Array.array

type 'a edges_act = 'a edge list Inttab.table Array.array
type 'a edges_internal = 'a edge list Array.array

type 'a automaton =
     {
       edges_in : 'a edges_act,
       edges_out : 'a edges_act,
       broadcast_in : 'a edges_act option,
       broadcast_out : 'a edges_act option,
       edges_internal : 'a edges_internal,
       nodes : 'a nodes,
       initial : int,
       loc_dict : int IndexDict.t,
       name_dict : string IndexDict.t
     }

type process = int
type location = int
type label = int
type 'a processes = 'a automaton Array.array

type ('a, 'b) network =
     {
       G_d : ConstraintSet.set,
       automata : 'a processes,
       clock_dict : string IndexDict.t,
       var_dict : string IndexDict.t,
       label_dict : string IndexDict.t,
       ta_names : string IndexDict.t,
       var_bounds : (int * int) IndexDict.t,
       k_pos: int Array.array -> int -> 'b,
       k_neg: int Array.array -> int -> 'b,
       committed_location: int -> int -> bool,
       broadcast_dict : string IndexDict.t,
       formula : (Network.location -> bool) Formula.F
     }

val init_adj_act: int -> 'a edges_act
val init_adj_broadcast: int -> 'a edges_act
val init_adj_internal: int -> 'a edges_internal

val add_edge_act: int -> 'a edges_act -> (int * 'a edge) -> unit
val add_edge_broadcast: int -> 'a edges_act -> (int * 'a edge) -> unit
val add_edge_internal: int -> 'a edges_internal -> 'a edge -> unit

val get_automaton: 'a processes -> int -> 'a automaton
val node: int -> 'a automaton -> 'a -> 'a
val edges_in: 'a processes
              -> process
              -> location
              -> 'a edge list Inttab.table

val edges_out: 'a processes
               -> process
               -> location
               -> 'a edge list Inttab.table

val broadcast_in: 'a processes
                  -> process
                  -> location
                  -> 'a edge list Inttab.table

val broadcast_out: 'a processes
                   -> process
                   -> location
                   -> 'a edge list Inttab.table

val matching_edges_out: 'a processes
                        -> process
                        -> location
                        -> label
                        -> 'a edge list

val matching_edges_in: 'a processes
                       -> process
                       -> location
                       -> label
                       -> 'a edge list

val matching_broadcast_out: 'a processes
                            -> process
                            -> location
                            -> label
                            -> 'a edge list

val matching_broadcast_in: 'a processes
                           -> process
                           -> location
                           -> label
                           -> 'a edge list

val edges_internal: 'a processes
                    -> process
                    -> location
                    -> 'a edge list
end

structure ProtoNetwork : PROTO_NETWORK = struct

type 'a edge =
     {
       target : int,
       clock_updates : 'a -> 'a,
       var_updates : int Array.array -> int Array.array option,
       g_data : int Array.array -> bool,
       g: 'a -> 'a
     }

type 'a node =
     {
       invariant : 'a -> 'a
     }

type 'a nodes = 'a node Array.array


type 'a edges_act = 'a edge list Inttab.table Array.array
type 'a edges_internal = 'a edge list Array.array

type 'a automaton =
     {
       edges_in : 'a edges_act,
       edges_out : 'a edges_act,
       broadcast_in : 'a edges_act option,
       broadcast_out : 'a edges_act option,
       edges_internal : 'a edges_internal,
       nodes : 'a nodes,
       initial : int,
       loc_dict : int IndexDict.t,
       name_dict : string IndexDict.t
     }

type process = int
type location = int
type label = int
type 'a processes = 'a automaton Array.array

type ('a, 'b) network =
     {
       G_d : ConstraintSet.set,
       automata : 'a processes,
       clock_dict : string IndexDict.t,
       var_dict : string IndexDict.t,
       label_dict : string IndexDict.t,
       ta_names : string IndexDict.t,
       var_bounds : (int * int) IndexDict.t,
       k_pos: int Array.array -> int -> 'b,
       k_neg: int Array.array -> int -> 'b,
       committed_location: int -> int -> bool,
       broadcast_dict : string IndexDict.t,
       formula : (Network.location -> bool) Formula.F
     }


(* ************************************************************************** *)
(*               Creating Adjacency Graphs & Manipulating them                *)
(* ************************************************************************** *)

fun init_adj_act n = Array.array (n, Inttab.empty)
fun init_adj_broadcast n = init_adj_act n
fun init_adj_internal n = Array.array (n, [])

fun changei f i arr =
    let
        val at_i = Array.sub (arr, i)
    in
        Array.update (arr, i, f at_i)
    end

local

  fun eq_edges ( e : 'a edge) (e' : 'a edge) = false
  fun insert_es e = Inttab.insert_list (uncurry eq_edges) e

in
fun add_edge_act i adj_m e =
    changei (insert_es e) i adj_m
end

fun add_edge_broadcast i = add_edge_act i

fun add_edge_internal i adj_m e =
    changei (cons e) i adj_m

(* ************************************************************************** *)
(*                           Accessing invariants                             *)
(* ************************************************************************** *)

fun node i ({nodes, ...} : 'a automaton) =
    Array.sub (nodes, i) |> #invariant

fun get_automaton automata i =
    Array.sub (automata, i)

local
  fun get_edges l edges =
      Array.sub (edges, l)

  fun get_label label =
      flip Inttab.lookup_list label
in

(* ************************************************************************** *)
(*                           Accessing labeled edges                          *)
(* ************************************************************************** *)

fun edges_in (tas : 'a processes) p l =
    get_automaton tas p |> #edges_in |> get_edges l

fun matching_edges_in (tas : 'a processes) p l label =
    edges_in tas p l |> get_label label

fun edges_out (tas: 'a processes) p l =
    get_automaton tas p |> #edges_out |> get_edges l

fun matching_edges_out (tas : 'a processes) p l label =
    edges_out tas p l |> get_label label

(* ************************************************************************** *)
(*                           Accessing broadcast edges                        *)
(* ************************************************************************** *)

fun broadcast select (tas : 'a processes) p l =
    case (get_automaton tas p |> select) of
        NONE => Inttab.empty |
        SOME adj => get_edges l adj

fun broadcast_in (tas : 'a processes) =
    broadcast (#broadcast_in) tas

fun matching_broadcast_in (tas : 'a processes) p l label =
    broadcast_in tas p l |> get_label label

fun broadcast_out (tas: 'a processes) = broadcast (#broadcast_out) tas

fun matching_broadcast_out (tas : 'a processes) p l label =
    broadcast_out tas p l |> get_label label


(* ************************************************************************** *)
(*                           Accessing internal edges                         *)
(* ************************************************************************** *)

fun edges_internal  (tas: 'a processes) p l =
    get_automaton tas p |> #edges_internal |> get_edges l

end

end
