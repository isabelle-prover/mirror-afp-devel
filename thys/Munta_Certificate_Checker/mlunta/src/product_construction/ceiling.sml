signature CEILING = sig
    structure Entry : DBM_ENTRY
    structure DBM : DBM_ALG
    val network: bool ->
                 RewriteConstraintTypes.network ->
                 Entry.t ClockCeilingTypes.network
end

functor GlobalClockCeiling(E : DBM_ENTRY) : CEILING = struct
structure Entry = E
structure DBM = DBM(structure E = E and M = LnLayoutMatrix)

open ClockConstraint
open RewriteConstraintTypes
fun update_ceiling k v =
    Inttab.update_if (curry (op >)) (k, v)

(* ceiling x - y < 10 ==> k x -> 10, k y -> - 10 *)
fun invar_ceiling map invar =
    let
      fun switch x m =
          map |> update_ceiling x m
    in
      case invar of
          Lt (x, 0, v) => update_ceiling x v map |
          Le (x, 0, v) => update_ceiling x v map |
          Lt (0, _, _) => map |
          Le (0, _, _) => map |
          Lt (x, y, v) => switch x v |
          Le (x, y, v) => switch x v
    end

fun fold_ceiling map =
    foldl (swap #> (uncurry invar_ceiling)) map

fun init clocks = IndexDict.foldli
                      (fn (c, _, tab') => update_ceiling c 0 tab')
                      Inttab.empty clocks

fun compile_ceiling_node start =
    #invariant #> fold_ceiling start

fun compile_ceiling_edge start E =
    fold_ceiling start (#g_single E)
    |> flip fold_ceiling (#g_diag E)

fun compile_ceiling_automaton (ta : automaton) =
    flip (foldl (fn (e, tab') => compile_ceiling_edge tab' e)) (#edges_in ta)
    #> flip (foldl (fn (e, tab') => compile_ceiling_edge tab' e)) (#edges_out ta)
    #> flip (foldl (fn (e, tab') => compile_ceiling_edge tab' e)) (#edges_internal ta)
    #> flip (foldl (fn (e, tab') => compile_ceiling_node tab' e)) (#nodes ta)

fun compile_ceiling_network clock_dict automata =
    init clock_dict
    |> flip (foldl (apfst snd #> (uncurry compile_ceiling_automaton))) automata

fun ceiling clock_dict automata =
    let
      fun neg_init e = (~ e |> Entry.=<)
      fun pos_init e = (Entry.==< e)
      val ceiling_map =  compile_ceiling_network clock_dict automata
      fun to_entry init = Inttab.map (K init)
      val neg_map = ceiling_map |> to_entry neg_init
      val pos_map = ceiling_map |> to_entry pos_init
      fun get_ceil map = IndexDict.tabulate (IndexDict.size clock_dict) (Inttab.lookup map #> the)
                         |> flip IndexDict.find
                         |> K
    in
      (neg_map, pos_map) |> apply2 get_ceil
    end

fun network _ ({automata, clock_dict, var_dict, label_dict, ta_names,
              var_bounds, formula, broadcast_dict, ...}
             : RewriteConstraintTypes.network) =
    let
      val (k_neg, k_pos) = ceiling clock_dict automata
    in
      {
       automata = automata,
       clock_dict = clock_dict,
       var_dict = var_dict,
       label_dict = label_dict,
       ta_names = ta_names,
       var_bounds = var_bounds,
       k_neg = k_neg,
       k_pos = k_pos,
       formula  = formula,
       broadcast_dict = broadcast_dict
     }
    end
end
