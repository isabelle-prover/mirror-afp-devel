structure ProductTransitionTypes = struct
type 'a transition_data =
     {
       L' : int array,
       g_data: int Array.array -> bool,
       g: 'a -> 'a,
       clock_updates: 'a -> 'a,
       var_updates: int Array.array -> int Array.array option
     }

datatype 'a kind = Committed of 'a | Uncommitted of 'a

type 'a transitions = 'a transition_data list
type 'a transition_system = int Array.array -> 'a transitions kind

type ('a, 'b) network =
     {
       L : int Array.array,
       G_d: ConstraintSet.set,
       initial_dbm: 'a,
       transition_system : 'a transition_system,
       invars_at: int Array.array -> ('a -> 'a),
       clock_dict : string IndexDict.t,
       var_dict : string IndexDict.t,
       label_dict : string IndexDict.t,
       var_bounds : (int * int) IndexDict.t,
       loc_dict: int IndexDict.t IndexDict.t,
       ta_names : string IndexDict.t,
       name_dict: string IndexDict.t IndexDict.t,
       k_pos: int Array.array -> int -> 'b,
       k_neg: int Array.array -> int -> 'b,
       formula : (Network.location -> bool) Formula.F
     }
end
