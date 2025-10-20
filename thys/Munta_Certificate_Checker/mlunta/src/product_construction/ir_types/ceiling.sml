structure ClockCeilingTypes = struct
type edge =
     {
       source : int,
       target : int,
       g_data : (int, int) Syntax.guard list,
       g_single : ClockConstraint.t list,
       g_diag : ClockConstraint.t list,
       label : int,
       clock_updates : int Syntax.update list,
       var_updates : int Syntax.update list
     }
type node =
     {
       id : int,
       invariant: ClockConstraint.t list,
       name : string
     }

type automaton =
     {
       edges_in : edge list,
       edges_out : edge list,
       edges_internal : edge list,
       broadcast_in : edge list,
       broadcast_out : edge list,
       committed: Inttab.set,
       nodes : node list,
       initial : int,
       loc_dict : int IndexDict.t,
       name_dict : string IndexDict.t
     }

type 'a network =
     {
       automata : (int * automaton) list,
       clock_dict : string IndexDict.t,
       var_dict : string IndexDict.t,
       label_dict : string IndexDict.t,
       ta_names : string IndexDict.t,
       var_bounds : (int * int) IndexDict.t,
       broadcast_dict: string IndexDict.t,
       k_pos: int Array.array -> int -> 'a,
       k_neg: int Array.array -> int -> 'a,
       formula : (int, int) Syntax.formula
     }

end
