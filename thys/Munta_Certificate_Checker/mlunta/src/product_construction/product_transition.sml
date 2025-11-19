signature PRODUCT_TRANSITION = sig
  structure Entry : DBM_ENTRY
  structure DBM : DBM_ALG

  type process
  type location
  structure Transition : sig
              val internal: process
                            -> location Array.array
                            -> DBM.t ProtoNetwork.edge
                            -> DBM.t ProductTransitionTypes.transition_data

              val binary: location Array.array
                          -> process * process
                          -> DBM.t ProtoNetwork.edge * DBM.t ProtoNetwork.edge
                          -> DBM.t ProductTransitionTypes.transition_data

              val broadcast: process
                             -> location Array.array
                             -> DBM.t ProtoNetwork.edge
                             -> DBM.t ProductTransitionTypes.transition_data

              val add_receiver: (process -> bool)
                                -> process
                                -> DBM.t ProductTransitionTypes.transition_data
                                   * bool
                                -> DBM.t ProtoNetwork.edge
                                -> DBM.t ProductTransitionTypes.transition_data
                                   * bool
            end

  val initial_dbm: int -> DBM.t

  val invars_at: DBM.t ProtoNetwork.automaton Array.array
                 -> location Array.array
                 -> DBM.t -> DBM.t

  val network: (DBM.t, 'b) ProtoNetwork.network
               -> (DBM.t, 'b) ProductTransitionTypes.network
end

functor ProductTransition(E :DBM_ENTRY) : PRODUCT_TRANSITION =
struct
structure Entry = E
structure DBM = DBM(structure E = E and M = LnLayoutMatrix)
open ProtoNetwork

fun array_foldli f =
    flip (Array.foldli f)
fun slice_foldli f =
    flip (ArraySlice.foldli f)


fun invars_at automata =
    Array.foldli
        (fn (p, l, acc) =>
            acc #> node l (get_automaton automata p))
        id

fun sides L p =
        (ArraySlice.slice (L, 0, SOME p),
         ArraySlice.slice (L, p + 1, NONE))


fun initial_location (automata : DBM.t ProtoNetwork.automaton Array.array) =
    let
      val L = Array.array (Array.length automata, 0)
      val _ = Array.appi (fn (p, ta) => Array.update (L, p, #initial ta)) automata
    in
      L
    end

fun initial_dbm clocks =
    DBM.init clocks

structure Transition = struct
type transition_data = DBM.t ProductTransitionTypes.transition_data
type edge = DBM.t ProtoNetwork.edge

fun internal p L (e : edge) =
    let
      fun upd arr = Array.update (arr, p, #target e)
    in
      {
            L' = L |> cp_arr |> tap upd,
            g_data = #g_data e,
            g = #g e,
            clock_updates = #clock_updates e,
            var_updates =  #var_updates e
      }
    end

fun binary L (p, q) ((e_out, e_in) : edge * edge) =
    let
      fun upd arr =
          (
            Array.update (arr, p, #target e_out);
            Array.update (arr, q, #target e_in)
          )
    in
       {
             L' = L |> cp_arr |> tap upd,
             g_data = #g_data e_out andf #g_data e_in,
             g = #g e_out #> #g e_in,
             clock_updates = #clock_updates e_out #> #clock_updates e_in,
             var_updates = Option.composePartial
                               (#var_updates e_in, #var_updates e_out)
       }
    end

fun broadcast p =
    internal p

fun add_receiver' (e : transition_data)
                 q (e_in : edge) : transition_data =
    let
      fun upd arr = Array.update (arr, q, #target e_in)
    in
      {
        L' = (#L' e) |> cp_arr |> tap upd,
        g_data = (fn vars => #g_data e vars andalso #g_data e_in vars),
        g = #g e_in #> #g e,
        clock_updates = #clock_updates e_in #> #clock_updates e,
        var_updates = Option.composePartial
                          (#var_updates e, #var_updates e_in)
      }
    end

fun add_receiver is_committed q (e, flag) e_in =
    let
      val e = add_receiver' e q e_in
    in
      if is_committed q then (e, true)
      else (e, flag)
    end
end

fun committed_locations_per_process is_committed =
    Array.foldli (fn (p, l, locs) =>
                     if is_committed p l then apfst (Inttab.update (p, l)) locs
                     else apsnd (Inttab.update (p, l)) locs)
                 (Inttab.empty, Inttab.empty)


structure Uncommitted = struct

fun internal_transitions automata L =
    let
      val internal_edges = edges_internal automata
    in
      array_foldli
          (fn (p, l, acc) =>
              fold (cons o (Transition.internal p L))
                   (internal_edges p l) acc)
          L
    end

fun binary_transition_pair L (p, q) es_in e_out =
    let
      val mk_trans = Transition.binary L (p, q)
    in
      fold (fn e_in => cons (mk_trans (e_out, e_in))) es_in
    end

fun transitions_label L (p, q) es_out es_in =
    let
      val transition_pair = binary_transition_pair L (p, q)
    in
      fold (transition_pair es_in) es_out
    end

fun find_matching_inputs tas L (p, q) =
    let
      val (l_p, l_q) = (Array.sub (L, p), Array.sub (L, q))
      val es_out = edges_out tas p l_p
      val transition_label' = transitions_label L (p, q)
      fun inner_fold (label, es_out) =
          transition_label' es_out (matching_edges_in tas q l_q label)
    in
      Inttab.fold inner_fold es_out
    end

fun one_side automata L p start_idx =
    let
      val trans_pq = find_matching_inputs automata L
    in
      slice_foldli
          (fn (q, _ , acc) => trans_pq (p, q + start_idx) acc)
    end

fun binary_transitions_p automata L p =
    let
      val (lhs, rhs) = sides L p
      val one_side' = one_side automata L p
    in
      one_side' 0 lhs
      #> one_side' (p + 1) rhs
    end

fun binary_transitions automata L =
    let
      val trans_p = binary_transitions_p automata L
    in
      array_foldli (fn (i, _, acc) => trans_p i acc) L
    end

fun compose_same_label is_committed broadcasts (q, input_edges) =
    let
      val add_receiver = cons oo Transition.add_receiver is_committed q
    in
      case input_edges of
          [] => broadcasts |
          inputs => fold (fn broadcast => fold (add_receiver broadcast) inputs)
                         broadcasts []
    end

fun compose_broadcast is_committed tas label start_idx =
    let
      val same_label = compose_same_label is_committed
    in
      slice_foldli (fn (p, l, broadcasts) =>
                       let val q = p + start_idx in
                         same_label broadcasts
                                    (q, matching_broadcast_in tas q l label)
                       end)
    end

fun other_processes is_committed tas L (p, emission)
                    (lhs_idx, rhs_idx) (lhs, rhs) =

    let val compose = compose_broadcast is_committed tas in
      Inttab.fold (
        fn (label, es_out) =>
           fold
               (fn output => fn acc =>
                   (Transition.broadcast p L output, is_committed p)
                   |> single
                   |> compose label lhs_idx lhs
                   |> compose label rhs_idx rhs
                   |> map_filter (fn (e, flag) =>
                                         if flag then SOME e else NONE)
                   |> flip append acc
               ) es_out
      ) emission
    end

fun collect_broadcast_p is_committed tas L p =
    let
      val (lhs, rhs) = sides L p
      val emission = broadcast_out tas p (Array.sub (L, p))
      val other_processes = other_processes is_committed tas L
    in
      other_processes (p, emission) (0, p + 1) (lhs, rhs)
    end

fun broadcast_transitions automata L =
    let
      val broadcast_p = collect_broadcast_p (K true) automata L
    in
      array_foldli (fn (p, _, acc) => broadcast_p p acc) L
    end

end

structure Committed = struct
fun internal_transitions C_L automata L =
    let
      val internal_edges = edges_internal automata
    in
      Inttab.fold (
        fn (p, l) =>
           fold (cons o (Transition.internal p L))
                (internal_edges p l)
      ) C_L
    end


fun collect_binary_committed tas L p =
    let
      val (lhs, rhs) = sides L p
      val one_side = Uncommitted.one_side tas L p
    in
      one_side 0 lhs
      #> one_side (p + 1) rhs
    end

fun collect_binary_uncommitted tas C_L L p =
    let
      val find_matches = curry (Uncommitted.find_matching_inputs tas L) p
    in
      Inttab.fold (fst #> find_matches) C_L
    end

fun collect_binary_p tas C_L L =
    (collect_binary_committed tas L, collect_binary_uncommitted tas C_L L)

fun collect_binary tas (C_L, UC_L) L =
    let
      val (committed, uncommitted) = collect_binary_p tas C_L L
    in
      Inttab.fold (fst #> committed) C_L
      #> Inttab.fold (fst #> uncommitted) UC_L
    end

fun binary_transitions automata =
    collect_binary automata

fun broadcast_transitions C_L tas L =
    let
      val is_committed = Inttab.defined C_L
      val broadcast_p = Uncommitted.collect_broadcast_p is_committed tas L
    in
      array_foldli (fn (p, _, acc) => broadcast_p p acc) L
    end
end


fun transition_system committed_locations automata L =
    let val (C_L, UC_L) = committed_locations L in
      if Inttab.is_empty C_L then
        []
        |> Uncommitted.broadcast_transitions automata L
        |> Uncommitted.binary_transitions automata L
        |> Uncommitted.internal_transitions automata L
        |> ProductTransitionTypes.Uncommitted
      else
        []
        |> Committed.broadcast_transitions C_L automata L
        |> Committed.binary_transitions automata (C_L, UC_L) L
        |> Committed.internal_transitions C_L automata L
        |> ProductTransitionTypes.Uncommitted
    end


(* XXX: do not loose info about broadcast_dict *)
fun network ({automata, G_d, clock_dict, var_dict, label_dict, broadcast_dict,
              committed_location,
              ta_names, var_bounds, k_pos, k_neg, formula}
             : (DBM.t, 'b) network) =
    let
      val L = initial_location automata
      fun dict_arr_to_dict2 f =
          Array.vector #> Vector.map f #> IndexDict.fromVector
      val committed_locations = committed_locations_per_process
                                    committed_location
    in
      {
        transition_system = transition_system committed_locations automata,
        L = L,
        initial_dbm = initial_dbm (IndexDict.size clock_dict),
        invars_at = invars_at automata,
        G_d = G_d,
        clock_dict = clock_dict,
        var_dict = var_dict,
        label_dict = label_dict,
        ta_names = ta_names,
        var_bounds = var_bounds,
        k_pos = k_pos,
        k_neg = k_neg,
        formula = formula,
        loc_dict = automata |> dict_arr_to_dict2 #loc_dict,
        name_dict = automata |> dict_arr_to_dict2 #name_dict
      }
    end
end
structure Transitions = ProductTransition(Entry64Bit)
