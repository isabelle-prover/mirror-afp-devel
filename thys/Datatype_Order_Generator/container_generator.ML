signature CONTAINER_GENERATOR = 
sig 
  (* if boolean is true, then Some op = is returned, else None *)
  val mk_some_eq_or_none : typ -> bool -> term;

  val mk_set_impl : typ -> string -> term;

  val mk_none_cenum : typ -> term;

  val supported_set_impl : string

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end


structure Container_Generator : CONTAINER_GENERATOR =
struct
open Derive_Aux;

val supported_set_impl = "(rbt,dlist,monad,collect,choose)"

fun mk_none_cenum ty =
  let 
    val lty = Type (@{type_name list}, [ty])
    val fty = (ty --> @{typ bool}) --> @{typ bool}
    val oty = Type (@{type_name option},[
      Type (@{type_name prod},[lty, Type (@{type_name prod},[fty,fty])])])
    val res = Const (@{const_name None}, oty)
  in res
end

fun mk_set_impl ty choice = 
  let 
    val sity = @{typ set_impl}
    val pty = Type (@{type_name phantom},[ty,sity])
    val ph = Const (@{const_name phantom}, sity --> pty)
    val si = 
      if choice = "rbt" then @{term set_RBT} else
      if choice = "dlist" then @{term set_DList} else
      if choice = "monad" then @{term set_Monad} else
      if choice = "collect" then @{term set_Collect} else
      if choice = "choose" then @{term set_Choose} else
      error ("invalid parameter for set_impl, choose one of " ^ supported_set_impl)
    val res = ph $ si
  in res
end

fun mk_some_eq_or_none ty choice =
  let 
    val eqt = ty --> ty --> @{typ bool}
    val eq = HOLogic.eq_const ty
    val oty = Type (@{type_name option},[eqt])
    val some = Const (@{const_name Some},eqt --> oty) $ eq
    val none = Const (@{const_name None},oty)
  in (if choice then some else none)
end  

fun typ_and_vs_of_typname thy typ_name sort =
  let 
    val ar = Type.arity_number (Proof_Context.tsig_of (Proof_Context.init_global thy)) typ_name
    val sorts = map (K sort) (1 upto ar)
    val ty_vars = Name.invent_names (Name.make_context [typ_name]) "a" sorts
    val ty = Type (typ_name,map TFree ty_vars)
  in (ty,ty_vars)
end

fun derive_ceq typ_name param thy = 
  let
    val choice = if (param = "") then true else if param = "no" then false else 
      error "optional parameter for class ceq must be 'no'"
    val base_name = Long_Name.base_name typ_name
    val _ = Output.writeln ("use " ^ (if choice then "" else "no ") ^ "equality for type " 
      ^ base_name)
    val sort = @{sort ceq}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val ceq_rhs = mk_some_eq_or_none ty choice
    val ceq_ty = Term.fastype_of ceq_rhs
    val ceq_def = mk_def ceq_ty @{const_name ceq} ceq_rhs
    val (ceq_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("ceq_" ^ base_name ^ "_def", ceq_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac [ceq_thm] ctxt
      THEN force_tac ctxt 1) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class ceq")  
  
  in thy' end

fun derive_cenum typ_name param thy = 
  let
    val choice = if (param = "no") then false else  
      error "currently only parameter 'no' is accepted for class cenum"
    val base_name = Long_Name.base_name typ_name
    val _ = Output.writeln ("use " ^ (if choice then "" else "no ") ^ "enum for type " 
      ^ base_name)
    val sort = @{sort cenum}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val cenum_rhs = mk_none_cenum ty
    val cenum_ty = Term.fastype_of cenum_rhs
    val cenum_def = mk_def cenum_ty @{const_name cEnum} cenum_rhs
    val (cenum_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("cEnum_" ^ base_name ^ "_def", cenum_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac [cenum_thm] ctxt
      THEN (REPEAT (force_tac ctxt 1))) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class cenum")  
  
  in thy' end

fun derive_set_impl typ_name param thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val _ = Output.writeln ("use " ^ param ^ " as set_impl for type " 
      ^ base_name)
    val sort = @{sort set_impl}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val set_impl_rhs = mk_set_impl ty param
    val set_impl_ty = Term.fastype_of set_impl_rhs
    val set_impl_def = mk_def set_impl_ty @{const_name set_impl} set_impl_rhs
    val (_,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("set_impl_" ^ base_name ^ "_def", set_impl_def)     
    val thy' = Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac []) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class set_impl")  
  in thy' end

val setup = 
  Derive_Manager.register_derive "ceq" "use (no) equality for class ceq" derive_ceq #>
  Derive_Manager.register_derive "cenum" "use (no) enumeration for class cenum" derive_cenum #>
  Derive_Manager.register_derive "set_impl" ("choose " ^ supported_set_impl ^ " as set_impl for a datatype") derive_set_impl

end
