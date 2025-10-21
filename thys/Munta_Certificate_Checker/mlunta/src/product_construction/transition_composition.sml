signature TRANSITION_COMPOSITION = sig
  structure Entry : DBM_ENTRY
  structure DBM : DBM_ALG

  val gen_transitions: (Network.location -> DBM.t -> DBM.t) ->
                       DBM.t ProductTransitionTypes.transition_system ->
                       DBM.t Network.state -> DBM.t Network.state list

  val gen_discrete_transitions:
                       DBM.t ProductTransitionTypes.transition_system ->
                       Network.location -> Network.location list

  val network: bool -> (DBM.t, Entry.t) ProductTransitionTypes.network ->
               DBM.t Network.system
end

functor TransitionComposition(E: DBM_ENTRY) : TRANSITION_COMPOSITION = struct
open ProductTransitionTypes
structure Entry = E
structure DBM = DBM(structure E = E and M = LnLayoutMatrix)

val filter_empty = Option.filter (DBM.empty #> not)

fun discrete_state vars trans =
    Option.filter (#g_data trans) vars
    |> Option.map (fn arr => if Array.length arr = 0 then arr
                             else cp_arr arr)
    |> Option.mapPartial (#var_updates trans)
    |> Option.map (pair (#L' trans))

fun transitioning trans dbm =
    dbm
    |> #g trans
    |> filter_empty
    |> Option.map (#clock_updates trans)

fun dbm_pipeline_normal invar_at trans dbm L L' =
      dbm
      |> DBM.copy
      |> DBM.up
      |> invar_at L
      |> filter_empty
      |> Option.mapPartial (transitioning trans)
      |> Option.map (invar_at L')
      |> Option.mapPartial filter_empty
      |> Option.map (pair L')


fun dbm_pipeline_committed invar_at trans dbm L' =
      dbm
      |> DBM.copy
      |> transitioning trans
      |> Option.map (invar_at L')
      |> Option.mapPartial filter_empty
      |> Option.map (pair L')

fun pipeline_uncommitted L invar_at vars dbm =
    rev_map_filter (
      fn transition =>
         discrete_state vars transition
         |> Option.mapPartial (dbm_pipeline_normal invar_at transition dbm L)
    )

fun pipeline_committed invar_at vars dbm =
    rev_map_filter (
      fn transition =>
         discrete_state vars transition
         |> Option.mapPartial (dbm_pipeline_committed invar_at transition dbm)
    )

fun pipeline L invar_at vars dbm system =
    case system of
        Committed   transitions => pipeline_committed
                                       invar_at vars dbm transitions |
        Uncommitted transitions => pipeline_uncommitted
                                       L invar_at vars dbm transitions

fun get_transitions (Committed transitions) = transitions
  | get_transitions (Uncommitted transitions) = transitions

fun gen_discrete_transitions transition_system (L, vars) =
      L
      |> transition_system
      |> get_transitions
      |> rev_map_filter (discrete_state vars)

fun gen_transitions invar_at transition_system ((L, vars), dbm) =
      L
      |> transition_system
      |> pipeline (L, vars) invar_at vars dbm

fun network extra_lu ({
              L,
              G_d,
              initial_dbm,
              transition_system,
              invars_at,
              clock_dict,
              var_dict,
              label_dict,
              var_bounds,
              k_pos,
              k_neg,
              formula,
              loc_dict,
              name_dict,
              ta_names
            } : (DBM.t, E.t) network) =
    let
      open ClockConstraint
      fun gd_to_bound c =
              case c of
                  Lt (x, y, m) => (x, y, E.=< m) |
                  Le (x, y, m) => (x, y, E.==< m)
      fun var_bounds_to_init dict =
              Array.array (IndexDict.size dict, 0)
      val invar_at = fst #> invars_at
      val G = G_d |> ConstraintSet.keys |> map gd_to_bound
      fun norm_k_G L =
          if extra_lu then DBM.norm_k_G DBM.extra_lu (k_pos L, k_neg L) G
          else DBM.norm_k_G DBM.norm_k (k_pos L, k_neg L) G

    in
    {
      (* Maybe: For now all vars are initialized with 0 their lower bound*)
      initial = ((L, var_bounds_to_init var_bounds), initial_dbm),
      trans = gen_transitions invar_at transition_system,
      clock_dict = clock_dict,
      var_dict = var_dict,
      label_dict = label_dict,
      ta_names = ta_names,
      var_bounds = var_bounds,
      norm_k_G = norm_k_G,
      formula = formula,
      loc_dict = loc_dict,
      invars_at = invar_at,
      name_dict = name_dict
    }
    end
end
structure CompNetwork = TransitionComposition(Entry64Bit)
