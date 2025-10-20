structure ConstructFunsTypes = struct
type 'a edge =
     {
       source : int,
       target : int,
       g : 'a -> 'a,
       g_data : int Array.array -> bool,
       label : int,
       clock_updates : 'a -> 'a,
       var_updates : int Array.array -> int Array.array option
     }
type 'a node =
     {
       id : int,
       invariant: 'a -> 'a,
       name : string
     }

type 'a automaton =
     {

       edges_in : 'a edge list,
       edges_out : 'a edge list,
       broadcast_in : 'a edge list,
       broadcast_out : 'a edge list,
       committed : Inttab.set,
       edges_internal : 'a edge list,
       nodes : 'a node list,
       initial : int,
       loc_dict : int IndexDict.t,
       name_dict: string IndexDict.t
     }

type ('a, 'b) network =
     {
       automata : (int * 'a automaton) list,
       G_d: ConstraintSet.set,
       clock_dict : string IndexDict.t,
       var_dict : string IndexDict.t,
       label_dict : string IndexDict.t,
       ta_names : string IndexDict.t,
       var_bounds : (int * int) IndexDict.t,
       k_pos: int Array.array -> int -> 'b,
       k_neg: int Array.array -> int -> 'b,
       formula : (Network.location -> bool) Formula.F,
       broadcast_dict: string IndexDict.t
     }

end
