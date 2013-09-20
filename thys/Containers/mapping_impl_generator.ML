(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)

signature MAPPING_IMPL_GENERATOR = 
sig 
  
  (* chooses a mapping implementation for a given type *)
  val derive_mapping_impl : string -> string -> theory -> theory

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end

structure Mapping_Impl_Generator : MAPPING_IMPL_GENERATOR = 
struct
open Containers_Generator; 
open Derive_Aux;

val supported_mapping_impl = [
  ("rbt", @{const_name mapping_RBT}),
  ("assoclist", @{const_name mapping_Assoc_List}),
  ("mapping", @{const_name mapping_Mapping}),
  ("choose", @{const_name mapping_Choose})
  ] 

val derive_mapping_impl = derive_set_map_impl @{const_name mapping_impl} @{sort mapping_impl} @{typ mapping_impl}
  supported_mapping_impl

val setup = 
  Derive_Manager.register_derive "mapping_impl" 
    ("choose " ^ alist_to_string supported_mapping_impl ^ " as mapping_impl for a datatype") derive_mapping_impl

end
