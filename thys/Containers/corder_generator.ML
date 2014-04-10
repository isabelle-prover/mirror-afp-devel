(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)

signature CORDER_GENERATOR = 
sig 
  
  (* derives a trivial instance (None) for class corder and any type *)
  val derive_no_corder : string -> theory -> theory

  (* derives a class instance for corder for some type which already is in class linorder *)
  val derive_corder_linorder : string -> theory -> theory

  (* derives a class instance for corder for some datatype by creating linear orders *)
  val derive_some_corder : string -> theory -> theory

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end

structure Corder_Generator : CORDER_GENERATOR = 
struct
open Containers_Generator; 
open Derive_Aux;
open Datatype; 
open Order_Generator;

fun mk_none_corder ty =
  let 
    val comp_ty = ty --> ty --> @{typ bool}
    val prod_ty = Type (@{type_name prod},[comp_ty, comp_ty])
    val opt_ty = Type (@{type_name option}, [prod_ty])
    val res = Const (@{const_name None}, opt_ty)     
  in res
end

fun mk_some_less_less_eq ty =
  let 
    val comp_ty = ty --> ty --> @{typ bool}
    val less = Const (@{const_name "Orderings.less"}, comp_ty)
    val less_eq = Const (@{const_name "Orderings.less_eq"}, comp_ty)
    val pair_ty = Type (@{type_name prod},[comp_ty,comp_ty])
    val pair = Const (@{const_name Pair}, comp_ty --> comp_ty --> pair_ty) $ less_eq $ less
  in mk_Some pair
end  

fun mk_linorder_thm dtyp_name lthy = 
  let
    val tyco = dtyp_name
    val thy = Proof_Context.theory_of lthy

    val base_name = Long_Name.base_name tyco
    val _ = writeln ("creating orders for datatype " ^ base_name)
    val info = Datatype.the_info thy tyco  
    val sort = @{sort linorder}
    val less_term = mk_less_idx thy info sort |> fst |> (fn x => x 0)
    val ty = Term.fastype_of less_term |> Term.dest_Type |> snd |> hd
    val comp_ty = ty --> ty --> @{typ bool}
    val class_ty = comp_ty -->  comp_ty --> @{typ bool}
    val x = Free ("x",ty)
    val y = Free ("y",ty)
    val less_eq_term = lambda x (lambda y (HOLogic.mk_disj (less_term $ x $ y, HOLogic.mk_eq (x,y))))
  
    (* derive instance for locale linorder *)
    val linorder_thm = 
        let          
          val [trans_eq,less,refl,antisym] = mk_order_thms thy info
          val linear = mk_linear_thm thy info
          fun order_tac {prems = _, context = ctxt} = 
            my_print_tac ctxt "enter order" THEN
            Locale.intro_locales_tac true ctxt [] THEN
            my_print_tac ctxt "after intro_locale" THEN
            rtac less 1 THEN
            my_print_tac ctxt "after less" THEN
            rtac refl 1 THEN
            my_print_tac ctxt "after refl" THEN
            rtac trans_eq 1 THEN atac 1 THEN atac 1 THEN
            my_print_tac ctxt "after trans" THEN
            rtac antisym 1 THEN atac 1 THEN atac 1 THEN
            my_print_tac ctxt "after antisym" THEN
            rtac linear 1
          val thm = Goal.prove lthy [] [] 
            (HOLogic.mk_Trueprop (Const (@{const_name class.linorder}, class_ty) $ less_eq_term $ less_term)) 
            order_tac 
          val _ = writeln ("proved that " ^ base_name ^ " is in locale linorder")
        in thm end   
      
  in linorder_thm end

val derive_no_corder = derive_none @{const_name corder} @{sort corder} mk_none_corder

fun derive_corder_linorder typ_name thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val _ = writeln ("use linorder to derive corder for type " ^ base_name)
    val sort = @{sort corder}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort linorder}
    val corder_rhs = mk_some_less_less_eq ty
    val corder_ty = Term.fastype_of corder_rhs
    val corder_def = mk_def corder_ty @{const_name corder} corder_rhs
    val (corder_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("corder_" ^ base_name ^ "_def", corder_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac ctxt [corder_thm]
      THEN my_print_tac ctxt "after class intro"
      THEN asm_full_simp_tac ctxt 1
      THEN my_print_tac ctxt "after simp"
      THEN Locale.intro_locales_tac true ctxt []) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class corder")
    val thy'' = derive_is_c_dots_lemma ty @{const_name is_corder} [corder_thm, @{thm is_corder_def}] base_name thy'

  in thy'' end


fun derive_some_corder dtyp_name thy = let
    val base_name = Long_Name.base_name dtyp_name
    
    val _ = writeln ("creating corder for datatype " ^ base_name)
    val info = Datatype.the_info thy dtyp_name
    val sort = @{sort linorder}
    val less = mk_less_idx thy info sort |> fst |> (fn x => x 0)
    val comp_ty = Term.fastype_of less
    val ty = comp_ty |> Term.dest_Type |> snd |> hd  
    val x = Free ("x",ty)
    val y = Free ("y",ty)
    val less_eq = lambda x (lambda y (HOLogic.mk_disj (less $ x $ y, HOLogic.mk_eq (x,y))))
    val vs_of_sort = 
      let val i = Datatype.the_spec thy dtyp_name |> #1 
      in fn sort => map (fn (n,_) => (n, sort)) i end
    val vs = vs_of_sort sort
    val linorder_thm = mk_linorder_thm dtyp_name (Proof_Context.init_global thy)
    val prod_ty = Type (@{type_name prod},[comp_ty, comp_ty])
    val some = Const (@{const_name "Pair"}, comp_ty --> comp_ty --> prod_ty) $ less_eq $ less |> mk_Some
    val corder_def = mk_def (fastype_of some) @{const_name corder} some
    val (corder_thm,lthy) = Class.instantiation ([dtyp_name],vs,@{sort corder}) thy
      |> define_overloaded ("corder_" ^ base_name ^ "_def", corder_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => (Class.intro_classes_tac []
      THEN my_print_tac ctxt "after class instance"
      THEN rtac (@{thm corder_intro} OF [linorder_thm]) 1
      THEN my_print_tac ctxt "after corder_intro"
      THEN unfold_tac ctxt [corder_thm]
      THEN (REPEAT (blast_tac ctxt 1))
      )) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class corder")
    val thy'' = derive_is_c_dots_lemma ty @{const_name is_corder} [corder_thm, @{thm is_corder_def}] base_name thy'

 in thy''
end 

fun derive_corder typ_name param thy = 
  if param = "" then derive_some_corder typ_name thy else
  if param = "no" then derive_no_corder typ_name thy else
  if param = "linorder" then derive_corder_linorder typ_name thy else
  error "(no) and (linorder) are only optional parameters for deriving corder"

val setup = 
  Derive_Manager.register_derive 
    "corder" 
    "derives an order for a datatype or (no) order for any type, or uses (linorder) instance for corder" 
    derive_corder
end
