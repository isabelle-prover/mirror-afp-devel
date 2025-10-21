structure RenamingTypes = struct
type edge =
     {
       source : int,
       target : int,
       g_single : (int, int) Syntax.diff_constraint list,
       g_diag : (int, int) Syntax.diff_constraint list,
       g_data : (int, int) Syntax.guard list,
       label : int,
       clock_updates : int Syntax.update list,
       var_updates : int Syntax.update list
     }
type node =
     {
       id : int,
       invariant: (int, int) Syntax.constraint list,
       name : string
     }

type automaton =
     {
       edges_in : edge list,
       edges_out : edge list,
       edges_internal : edge list,
       broadcast_in : edge list,
       broadcast_out: edge list,
       committed: Inttab.set,
       nodes : node list,
       initial : int,
       loc_dict : int IndexDict.t,
       name_dict: string IndexDict.t,
       name_f: string -> (Error.t list, int) Either.t
     }
type network =
     {
       automata : (int * automaton) list,
       clock_dict : string IndexDict.t,
       var_dict : string IndexDict.t,
       label_dict : string IndexDict.t,
       broadcast_dict : string IndexDict.t,
       ta_names : string IndexDict.t,
       var_bounds : (int * int) IndexDict.t,
       formula : (int, int) Syntax.formula
     }
fun get_namef (ta : automaton) = #name_f ta
end
