signature DERIVE_MANAGER =
sig
  (* identifier, description, (fn dtyp_name => param => derive-method) *)
  val register_derive : string -> string -> (string -> string -> theory -> theory) -> theory -> theory
  (* identifier, description, (fn dtyp_name => param => derive-method) *)
  val register_local_derive : string -> string -> (string -> string -> local_theory -> local_theory) -> theory -> theory
  (* identifier, dtyp_name, param *)
  val derive : string -> string -> string -> theory -> theory
  (* identifier, dtyp_name, param *)
  val local_derive : string -> string -> string -> local_theory -> local_theory
  (* print all registered deriving-methods  *)
  val print_info : theory -> unit
end

structure Derive_Manager : DERIVE_MANAGER =
struct

structure LDerive_Data = Theory_Data(
  type T =
    (string * (string -> string -> local_theory -> local_theory)) Symtab.table  (* descr * derive-fun *)

  val empty = Symtab.empty
  val extend = I
  fun merge (x,y) = Symtab.merge (K true) (x,y)
)

structure Derive_Data = Theory_Data(
  type T =
    (string * (string -> string -> theory -> theory)) Symtab.table  (* descr * derive-fun *)

  val empty = Symtab.empty
  val extend = I
  fun merge (x,y) = Symtab.merge (K true) (x,y)
)

fun derive_options thy =
  Derive_Data.get thy |> Symtab.dest |> map (fn (id,(descr,_)) => (id,descr))

fun local_derive_options thy =
  LDerive_Data.get thy |> Symtab.dest |> map (fn (id,(descr,_)) => (id,descr))

(* FIXME: possibly use Pretty function for presentation. *)
fun print_info thy =
  let
    val _ = writeln "The following sorts can be derived"
    val _ = derive_options thy |> sort_wrt fst |> map (fn (id,descr) => writeln (id ^ ": " ^ descr))
  in () end

fun local_print_info thy =
  let
    val _ = writeln "The following elements can be derived"
    val _ = local_derive_options thy |> sort_wrt fst |> map (fn (id,descr) => writeln (id ^ ": " ^ descr))
  in () end


fun register_derive id descr f thy =
  if Symtab.defined (Derive_Data.get thy) id then
    error ("Identifier " ^ quote id ^ " already in use for " ^ quote "deriving")
  else
    Derive_Data.map (Symtab.update_new (id,(descr,f))) thy

fun register_local_derive id descr f thy = 
  if Symtab.defined (LDerive_Data.get thy) id then
    error ("Identifier " ^ quote id ^ " already in use for " ^ quote "deriving")
  else
    LDerive_Data.map (Symtab.update_new (id,(descr,f))) thy

fun gen_derive prep id dtname param thy =
  case Symtab.lookup (Derive_Data.get thy) id of
    NONE => error ("No handler to derive sort " ^ quote id ^
      " is registered. Try " ^ quote "print_derives" ^ " to see available sorts.")
  | SOME (_, f) => f (prep thy dtname) param thy

fun gen_lderive prep id dtname param (lthy : local_theory) =
  case Symtab.lookup (LDerive_Data.get (Proof_Context.theory_of lthy)) id of
    NONE => error ("No handler to locally derive " ^ quote id ^
      " is registered. Try " ^ quote "print_local_derives" ^ " to see available options.")
  | SOME (_, f) => f (prep lthy dtname) param lthy

val derive = gen_derive (K I)

val local_derive = gen_lderive (K I)

fun derive_cmd id dtname param = gen_derive
  (fn thy => fst o dest_Type o Syntax.parse_typ (Proof_Context.init_global thy)) id dtname param

fun local_derive_cmd id dtname param = gen_lderive
  (fn lthy => fst o dest_Type o Syntax.parse_typ lthy) id dtname param
  
(* TODO: also check for alternative of  *)
(* NB: Proof_Context.read_type_name_proper ctxt false could be an alternative. *)

val _ =
  Outer_Syntax.command @{command_spec "print_derives"} "lists all registered sorts which can be derived"
    (Scan.succeed (Toplevel.theory (tap print_info)))

val _ =
  Outer_Syntax.command @{command_spec "print_local_derives"} "lists all registered sorts which can be derived"
    (Scan.succeed (Toplevel.theory (tap local_print_info)))

val _ = Outer_Syntax.command @{command_spec "derive"} "derives some sort"
    (Parse.parname -- Parse.name -- Parse.type_const >> (fn ((param, s), dtname) => Toplevel.theory (derive_cmd s dtname param)))
    
val _ = Outer_Syntax.command @{command_spec "local_derive"} "derives something locally"
    (Parse.parname -- Parse.name -- Parse.type_const >> (fn ((param, s), dtname) => Toplevel.local_theory NONE (local_derive_cmd s dtname param)))

end;
