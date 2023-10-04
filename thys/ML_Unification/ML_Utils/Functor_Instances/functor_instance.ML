(*  Title:      ML_Utils/functor_instance.ML
    Author:     Kevin Kappelmann

Functor instance arguments and utilities.
*)
signature FUNCTOR_INSTANCE_ARGS =
sig
  (*full name of the functor instance*)
  val full_name : string
  (*id for the functor instance*)
  val id : bstring
  (*position where the functor instance is created*)
  val pos : Position.T
end

signature FUNCTOR_INSTANCE_UTIL =
sig
  structure FIA : FUNCTOR_INSTANCE_ARGS

  (*create code that calls the given function of the functor instance*)
  val struct_op : string -> string
  val code_struct_op : string -> ML_Code_Util.code
  (*accessor of the functor instance, e.g. "My_Instance."*)
  val accessor : string

  val id_prefix : bstring

  val add_id_prefix : string -> bstring
  val mk_binding_id_prefix : bstring -> binding
end

functor Functor_Instance_Util(FIA : FUNCTOR_INSTANCE_ARGS) : FUNCTOR_INSTANCE_UTIL =
struct

val _ = @{assert} (FIA.full_name <> "")

structure FIA = FIA
val struct_op = ML_Syntax_Util.mk_struct_access FIA.full_name
val code_struct_op = ML_Code_Util.read o struct_op
val accessor = struct_op ""

val id_prefix = (FIA.id <> "" ? suffix "_") FIA.id

val add_id_prefix = prefix id_prefix
fun mk_binding_id_prefix binding = Binding.make (add_id_prefix binding, FIA.pos)

end