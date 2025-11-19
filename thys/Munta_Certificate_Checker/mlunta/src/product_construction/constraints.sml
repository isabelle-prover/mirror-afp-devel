signature REWRITE_CONSTRAINT = sig
  (* Maybe: What about Constraints like x - x ~ m? Add a check maybe?*)
  val node: RenamingTypes.node -> RewriteConstraintTypes.node
  val edge: RenamingTypes.edge -> RewriteConstraintTypes.edge
  val automaton: RenamingTypes.automaton ->
                 RewriteConstraintTypes.automaton
  val network: RenamingTypes.network ->
                 RewriteConstraintTypes.network
end

structure RewriteConstraint : REWRITE_CONSTRAINT = struct
open RenamingTypes
open Either

local open Syntax in
fun is_simple_update upd =
    case upd of
        Reset (_, 0) => true |
        Copy (_, _) => true |
        _ => false
end

fun edge ({source, target, g_single, g_diag,
               g_data, label, clock_updates, var_updates} : edge) =
    {
      source = source,
      target = target,
      g_data =  g_data,
      g_single = ClockConstraint.from_guard g_single,
      g_diag = ClockConstraint.from_guard g_diag,
      label = label,
      clock_updates = clock_updates,
      var_updates = var_updates
    }

fun simple_updates_edge ({clock_updates, ...} : RewriteConstraintTypes.edge) =
    List.all is_simple_update clock_updates

fun node ({id, invariant, name} : node) =
                    {
                      id = id,
                      invariant = map ClockConstraint.from_invar invariant |> flat,
                      name = name
                    }


fun automaton ({edges_in, edges_out, edges_internal, broadcast_in, broadcast_out,
                committed, nodes, initial, loc_dict,
                name_dict, name_f} : automaton) =
                  {
                    edges_in = map edge edges_in,
                    edges_out = map edge edges_out,
                    edges_internal = map edge edges_internal,
                    broadcast_in = map edge broadcast_in,
                    broadcast_out = map edge broadcast_out,
                    committed = committed,
                    nodes = map node nodes,
                    initial = initial,
                    loc_dict = loc_dict,
                    name_dict = name_dict
                  }


fun simple_updates_in_automaton ({edges_in, edges_out, edges_internal,
                                  broadcast_in, broadcast_out,...} : RewriteConstraintTypes.automaton) =
    let
      val check_edges = List.all simple_updates_edge
    in
      check_edges edges_in andalso
      check_edges edges_out andalso
      check_edges edges_internal andalso
      check_edges broadcast_in andalso
      check_edges broadcast_out
    end

fun network ({automata, clock_dict, var_dict,
              label_dict, ta_names, var_bounds, broadcast_dict, formula} : network) =
    let
      val automata = map (apsnd automaton) automata
      val only_simple_updates = List.all
                                    (simple_updates_in_automaton o snd)
                                    automata
    in
      {
        automata = automata,
        clock_dict = clock_dict,
        var_dict = var_dict,
        label_dict = label_dict,
        ta_names = ta_names,
        var_bounds = var_bounds,
        formula = formula,
        broadcast_dict = broadcast_dict,
        only_simple_updates = only_simple_updates
      }
    end
end
