(* Author:  René Thiemann, UIBK *)
(* The generators have been written as part of the IsaFoR/CeTA formalization. *)

signature CONTAINERS_GENERATOR = 
sig 

  val mk_is_c_dots : typ -> string -> term 
  
  (*                        const     sort    choices            *)
  val derive_set_map_impl : string -> sort -> (string * term) list 
    -> string -> string -> theory -> theory

  (*                const_name, sort, mk_none,         typ_name *)
  val derive_none : string -> sort -> (typ -> term) -> string -> theory -> theory

  (*                             const_name  base_name *)
  val register_is_c_dots_lemma : string -> string -> thm -> theory -> theory

  (*                           typ    const_name  defs      base_name *)
  val derive_is_c_dots_lemma : typ -> string -> thm list -> string -> theory -> theory

end

structure Containers_Generator : CONTAINERS_GENERATOR =
struct
open Derive_Aux; 

fun mk_set_map_impl choices ty choice thy = 
  let 
    val smi = case AList.lookup (op =) choices choice of
      SOME smi => smi
    | NONE => if choice = "" then error "you must provide some constant as parameter"
        else Syntax.read_term (Proof_Context.init_global thy) choice
    val smi_ty = fastype_of smi
    val pty = Type (@{type_name phantom},[ty,smi_ty])
    val ph = Const (@{const_name phantom}, smi_ty --> pty)
    val res = ph $ smi
  in res
end

fun derive_set_map_impl smi_const smi_sort choices typ_name choice thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val smi_name = Long_Name.base_name smi_const
    val _ = Output.writeln ("use " ^ choice ^ " as " ^ smi_name ^ " for type " 
      ^ base_name)
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val set_map_impl_rhs = mk_set_map_impl choices ty choice thy
    val set_map_impl_ty = Term.fastype_of set_map_impl_rhs
    val set_map_impl_def = mk_def set_map_impl_ty smi_const set_map_impl_rhs
    val (_,lthy) = Class.instantiation ([typ_name],vs,smi_sort) thy
      |> define_overloaded (smi_name ^ "_" ^ base_name ^ "_def", set_map_impl_def)     
    val thy' = Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac []) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class " ^ smi_name)  
  in thy' end

fun derive_none const sort mk_none typ_name thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val const_name = Long_Name.base_name const
    val sort_name = hd sort |> Long_Name.base_name
    val _ = Output.writeln ("use None as trivial implementation of " ^ sort_name ^ " for type " 
      ^ base_name)
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val none_rhs = mk_none ty
    val none_ty = Term.fastype_of none_rhs
    val const_def = mk_def none_ty const none_rhs
    val (none_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded (const_name ^ "_" ^ base_name ^ "_def", const_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac [none_thm] ctxt
      THEN (REPEAT (force_tac ctxt 1))) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class " ^ sort_name)    
  in thy' end
 
fun mk_is_c_dots ty dots = 
  let 
    val ity = Type (@{type_name itself}, [ty])
    val it = Const (@{const_name "TYPE"},ity)
    val res = Const (dots, ity --> @{typ bool}) $ it
  in res
end

fun register_is_c_dots_lemma const_name base_name thm thy = let
      val name = Long_Name.base_name const_name ^ "_" ^ base_name
      val lthy_map = Local_Theory.note ((Binding.name name, 
          @{attributes [simp,code_post]}), [thm]) #> #2
      val thy' = Named_Target.theory_init thy |> lthy_map |> Local_Theory.exit_global
      val _ = Output.writeln ("derived " ^ name ^ "-lemma")
    in thy'
end

fun derive_is_c_dots_lemma ty const_name defs base_name thy  = let
      val is_c_dots = HOLogic.mk_Trueprop (mk_is_c_dots ty const_name)
      val thm = Goal.prove (Proof_Context.init_global thy) [] [] is_c_dots (fn {prems = _, context = ctxt} => 
        unfold_tac (defs @ @{thms ID_Some option.simps}) ctxt
        THEN blast_tac ctxt 1
      )
    in register_is_c_dots_lemma const_name base_name thm thy
end

end
