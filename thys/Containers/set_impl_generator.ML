(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)
signature SET_IMPL_GENERATOR = 
sig 
  
  (* chooses a set implementation for a given type *)
  val derive_set_impl : string -> string -> theory -> theory

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end

structure Set_Impl_Generator : SET_IMPL_GENERATOR = 
struct
open Containers_Generator; 
open Derive_Aux;

val supported_set_impl = [
  ("rbt", @{const_name set_RBT}),
  ("dlist", @{const_name set_DList}),
  ("monad", @{const_name set_Monad}),
  ("collect", @{const_name set_Collect}),
  ("choose", @{const_name set_Choose})
  ]

val derive_set_impl = derive_set_map_impl @{const_name set_impl} @{sort set_impl} @{typ set_impl}
  supported_set_impl

val setup = 
  Derive_Manager.register_derive "set_impl" 
    ("choose " ^ alist_to_string supported_set_impl ^ " or any constant_name as set_impl for a datatype") derive_set_impl

end
