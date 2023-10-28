(*  Title:      ML_Utils/pair_generic_data_args.ML
    Author:     Kevin Kappelmann

Generic data arguments from pairs of generic data arguments.
*)
functor Pair_Generic_Data_Args(P : sig
  structure Data1 : GENERIC_DATA_ARGS
  structure Data2 : GENERIC_DATA_ARGS
  end) : GENERIC_DATA_ARGS =
struct

type T = P.Data1.T * P.Data2.T
val empty = (P.Data1.empty, P.Data2.empty)
fun merge ((d1, d2), (d1', d2')) = (P.Data1.merge (d1, d1'), P.Data2.merge (d2, d2'))

end
