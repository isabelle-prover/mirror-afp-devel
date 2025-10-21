structure RewriteBexpsTypes = struct
type edge =
     {
       source : int,
       target : int,
       g_single : (string, int) Syntax.diff_constraint list,
       g_diag : (string, int) Syntax.diff_constraint list,
       g_data : (string, int) Syntax.guard list,
       label : Symtab.key Syntax.action,
       clock_updates : string Syntax.update list,
       var_updates : string Syntax.update list
     }
type node =
     {
       id : int,
       invariant: (string, int) Syntax.constraint list,
       name : string
     }

type automaton =
     {
       edges_in : edge list,
       edges_out : edge list,
       edges_internal : edge list,
       broadcast_in : edge list,
       broadcast_out : edge list,
       nodes : node list,
       initial : int,
       committed: int list
     }
type network =
     {
       automata : (string * automaton) list,
       clocks : string list,
       vars : Syntax.var list,
       formula : (string, int) Syntax.formula,
       broadcast_channels : string list
     }
fun get_label ({label, ...} : edge) = label
end
