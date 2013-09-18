signature CEQ_GENERATOR = 
sig 
  
  (* derives a trivial instance (None) for class ceq and any type *)
  val derive_no_ceq : string -> theory -> theory

  (* derives a class instance for ceq by using equality *)
  val derive_some_ceq : string -> theory -> theory

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end

structure Ceq_Generator : CEQ_GENERATOR = 
struct
open Container_Generator_Aux;
open Derive_Aux; 

fun mk_some_eq ty =
  let 
    val eqt = ty --> ty --> @{typ bool}
    val eq = HOLogic.eq_const ty
    val oty = Type (@{type_name option},[eqt])
    val some = Const (@{const_name Some},eqt --> oty) $ eq
  in some
end  

fun mk_none_ceq ty =
  let 
    val eqt = ty --> ty --> @{typ bool}
    val oty = Type (@{type_name option},[eqt])
    val none = Const (@{const_name None},oty)
  in none
end  

val derive_no_ceq = derive_none @{const_name ceq} @{sort ceq} mk_none_ceq

fun derive_some_ceq typ_name thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val _ = Output.writeln ("use equality for class ceq and type " 
      ^ base_name)
    val sort = @{sort ceq}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val ceq_rhs = mk_some_eq ty
    val ceq_ty = Term.fastype_of ceq_rhs
    val ceq_def = mk_def ceq_ty @{const_name ceq} ceq_rhs
    val (ceq_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("ceq_" ^ base_name ^ "_def", ceq_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac [ceq_thm] ctxt
      THEN force_tac ctxt 1) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class ceq")  
    val thy'' = derive_is_c_dots_lemma ty @{const_name is_ceq} [ceq_thm, @{thm is_ceq_def}] base_name thy' 
  in thy'' end

fun derive_ceq typ_name param thy = 
  let
    val choice = if (param = "") then true else if param = "no" then false else 
      error "optional parameter for class ceq must be 'no'"
  in (if choice then derive_some_ceq else derive_no_ceq) typ_name thy
  end

val setup = 
  Derive_Manager.register_derive "ceq" "use (no) equality for class ceq" derive_ceq 

end
