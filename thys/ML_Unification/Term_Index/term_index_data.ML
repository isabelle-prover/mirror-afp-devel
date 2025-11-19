(*  Title: Term_Index/term_index_data.ML
    Author: Kevin Kappelmann

Term index stored in the generic context.
*)
signature TERM_INDEX_DATA_ARGS =
sig
  type data
  structure TI : TERM_INDEX
  val data_eq : data * data -> bool
end

functor Term_Index_Generic_Data_Args(P : TERM_INDEX_DATA_ARGS) : GENERIC_DATA_ARGS =
struct
open P
type T = data TI.term_index
val empty = TI.empty
fun merge (ti1, ti2) = TI.merge data_eq ti1 ti2
end

signature TERM_INDEX_DATA =
sig
  structure TI : TERM_INDEX
  structure TI_Data : GENERIC_DATA
end

functor Term_Index_Data(P : TERM_INDEX_DATA_ARGS) : TERM_INDEX_DATA =
struct

structure TI = P.TI
structure TI_Data = Generic_Data(Term_Index_Generic_Data_Args(P))

end
