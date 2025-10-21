functor IntLocalClockCeiling(E: DBM_ENTRY) : CEILING = struct
structure Entry = E
structure DBM = DBM(structure E = E and M = LnLayoutMatrix)
structure LocalCeiling = NonTrivialLocalCeiling(E)
structure SimpleLocalCeiling = LocalCeilingFunction(E)


fun network extra_lu (n as {automata, clock_dict, var_dict, label_dict, ta_names,
                   var_bounds, formula, only_simple_updates, broadcast_dict}) =
    let
      val (k_neg, k_pos) =
          case (only_simple_updates, extra_lu) of
              (true, true) => SimpleLocalCeiling.lu n |
              (false, true) => LocalCeiling.lu n |
              (true, false) => SimpleLocalCeiling.ceil n |
              (false, false) => LocalCeiling.ceil n
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
