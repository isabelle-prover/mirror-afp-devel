signature AUTOMATON_PREPROCESSING = sig
  val fill_adj_act: 'a ConstructFunsTypes.edge list ->
                    'a ProtoNetwork.edge list Inttab.table Array.array -> unit
  val automaton: 'b * 'a ConstructFunsTypes.automaton -> 'a ProtoNetwork.automaton
  val network: ('a, 'b) ConstructFunsTypes.network -> ('a, 'b) ProtoNetwork.network
end

structure AutomatonPreprocessing : AUTOMATON_PREPROCESSING = struct
open ConstructFunsTypes

fun get_info_e (e : 'a edge) =
    (#label e,
    {
      target = #target e,
      clock_updates = #clock_updates e,
      var_updates = #var_updates e,
      g_data = #g_data e,
      g = #g e
    })

fun get_info_n (n : 'a node) =
    {
      invariant = #invariant n
    }

fun fill_adj_act edges adj_m =
    edges
    |> List.app (fn edge => ProtoNetwork.add_edge_act (#source edge)
                                                    adj_m (get_info_e edge))

fun fill_adj_internal edges adj_m =
    edges
    |> List.app (fn edge => ProtoNetwork.add_edge_internal (#source edge)
                                                           adj_m ((get_info_e #> snd) edge))

(* XXX: Is renaming right such that nodes_ir ! 0 has id 0 *)
fun init_nodes nodes_ir =
    nodes_ir
    |> List.map get_info_n
    |> Array.fromList

(* XXX: Refactor for redability *)
fun automaton (i, (ta : 'a automaton)) =
    let
      val nodes_ir = #nodes ta
      val nodes_arr = init_nodes nodes_ir
      val edges_in_ir = #edges_in ta
      val edges_out_ir = #edges_out ta
      val edges_internal_ir = #edges_internal ta
      val broadcast_in_ir = #broadcast_in ta
      val broadcast_out_ir = #broadcast_out ta
      val n_locs = ta |> #loc_dict |> IndexDict.size
      val adj_m_in =
          ProtoNetwork.init_adj_act n_locs
      val adj_m_out =
          ProtoNetwork.init_adj_act n_locs
      val adj_m_internal =
          ProtoNetwork.init_adj_internal n_locs
      val broadcast_in =
          case broadcast_in_ir of
              [] => NONE |
              xs => SOME (ProtoNetwork.init_adj_act n_locs)
      val broadcast_out =
          case broadcast_out_ir of
              [] => NONE |
              xs => SOME (ProtoNetwork.init_adj_act n_locs)
      fun init (adj_m_in, adj_m_out, adj_m_internal) =
          (
            fill_adj_act edges_in_ir adj_m_in;
            fill_adj_act edges_out_ir adj_m_out;
            fill_adj_internal edges_internal_ir adj_m_internal
          )

      val (es_in, es_out, es_internal) =
          tap init (adj_m_in, adj_m_out, adj_m_internal)
      val broadcast_in =
          Option.map (tap (fill_adj_act broadcast_in_ir)) broadcast_in
      val broadcast_out =
          Option.map (tap (fill_adj_act broadcast_out_ir)) broadcast_out
    in
      {
            edges_in = es_in,
            edges_out = es_out,
            broadcast_in = broadcast_in,
            broadcast_out = broadcast_out,
            edges_internal = es_internal,
            nodes = nodes_arr,
            loc_dict = #loc_dict ta,
            name_dict = #name_dict ta,
            initial = #initial ta
      }
    end

fun network
      (
            {
              automata,
              G_d,
              clock_dict,
              var_dict,
              label_dict,
              ta_names,
              var_bounds,
              k_pos,
              k_neg,
              broadcast_dict,
              formula
            } : ('a, 'b) network) =
    let
      val committed_array =
          List.map (snd #> #committed) automata |> Array.fromList
      val automata = List.map automaton automata |> Array.fromList
      fun committed_location p l =
          (Array.sub (committed_array, p)
          |> flip Inttab.defined l)
    in
   {
      G_d = G_d,
      automata = automata,
      clock_dict = clock_dict,
      var_dict = var_dict,
      label_dict = label_dict,
      ta_names = ta_names,
      var_bounds = var_bounds,
      k_pos = k_pos,
      k_neg = k_neg,
      formula = formula,
      committed_location = committed_location,
      broadcast_dict = broadcast_dict
    }
    end
end
