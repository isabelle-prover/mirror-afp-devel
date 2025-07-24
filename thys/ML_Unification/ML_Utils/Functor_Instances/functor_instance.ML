(*  Title:      ML_Utils/functor_instance.ML
    Author:     Kevin Kappelmann

Functor instance arguments and utilities.
*)
signature FUNCTOR_INSTANCE_BASE =
sig
  (*binding of the functor instance*)
  val binding : binding
  (*id for the functor instance*)
  val id : bstring
end

signature FUNCTOR_INSTANCE =
sig
  include FUNCTOR_INSTANCE_BASE

  val name : string
  val long_name : string
  val pos : Position.T

  (*create code that calls the given function of the functor instance*)
  val struct_op : string -> string
  val code_struct_op : string -> ML_Code_Util.code

  val prefix_id : string -> bstring
end

functor Functor_Instance(FI : FUNCTOR_INSTANCE_BASE) : FUNCTOR_INSTANCE =
struct
open FI

val long_name = Binding.name_of binding

val _ = @{assert} (long_name <> "")

val name = Binding.name_of binding
val long_name = Binding.long_name_of binding
val pos = Binding.pos_of binding

val struct_op = ML_Syntax_Util.mk_struct_access long_name
val code_struct_op = ML_Code_Util.read o struct_op

val id_prefix = (id <> "" ? suffix "_") id
val prefix_id = prefix id_prefix

end