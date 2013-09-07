signature CONTAINER_GENERATOR = 
sig 

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end


structure Container_Generator : CONTAINER_GENERATOR =
struct
open Derive_Aux; open Datatype; open Derive_Aux; open Order_Generator;

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

fun mk_none_corder ty =
  let 
    val comp_ty = ty --> ty --> @{typ bool}
    val prod_ty = Type (@{type_name prod},[comp_ty, comp_ty])
    val opt_ty = Type (@{type_name option}, [prod_ty])
    val res = Const (@{const_name None}, opt_ty)     
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

fun mk_some_less_less_eq ty =
  let 
    val comp_ty = ty --> ty --> @{typ bool}
    val less = Const (@{const_name "Orderings.less"}, comp_ty)
    val less_eq = Const (@{const_name "Orderings.less_eq"}, comp_ty)
    val pair_ty = Type (@{type_name prod},[comp_ty,comp_ty])
    val pair = Const (@{const_name Pair}, comp_ty --> comp_ty --> pair_ty) $ less_eq $ less
    val oty = Type (@{type_name option},[pair_ty])
    val some = Const (@{const_name Some}, pair_ty --> oty) $ pair
  in some
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

fun mk_linorder_thm dtyp_name lthy = 
  let
    val tyco = dtyp_name
    val thy = Proof_Context.theory_of lthy

    val base_name = Long_Name.base_name tyco
    val _ = Output.writeln ("creating orders for datatype " ^ base_name)
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
            my_print_tac "enter order" THEN
            Locale.intro_locales_tac true ctxt [] THEN
            my_print_tac "after intro_locale" THEN
            rtac less 1 THEN
            my_print_tac "after less" THEN
            rtac refl 1 THEN
            my_print_tac "after refl" THEN
            rtac trans_eq 1 THEN atac 1 THEN atac 1 THEN
            my_print_tac "after trans" THEN
            rtac antisym 1 THEN atac 1 THEN atac 1 THEN
            my_print_tac "after antisym" THEN
            rtac linear 1
          val thm = Goal.prove lthy [] [] 
            (HOLogic.mk_Trueprop (Const (@{const_name class.linorder}, class_ty) $ less_eq_term $ less_term)) 
            order_tac 
          val _ = Output.writeln ("proved that " ^ base_name ^ " is in locale linorder")
        in thm end   
      
  in linorder_thm end

fun derive_no_corder typ_name thy = let
    val base_name = Long_Name.base_name typ_name
    val _ = Output.writeln ("do not use order for type " 
      ^ base_name)
    val sort = @{sort corder}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val corder_rhs = mk_none_corder ty
    val corder_ty = Term.fastype_of corder_rhs
    val corder_def = mk_def corder_ty @{const_name corder} corder_rhs
    val (corder_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("corder_" ^ base_name ^ "_def", corder_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac [corder_thm] ctxt
      THEN (REPEAT (force_tac ctxt 1))) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class corder")  
  
  in thy' end

fun derive_corder_linorder typ_name thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val _ = Output.writeln ("use linorder to derive corder for type " 
      ^ base_name)
    val sort = @{sort corder}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort linorder}
    val corder_rhs = mk_some_less_less_eq ty
    val corder_ty = Term.fastype_of corder_rhs
    val corder_def = mk_def corder_ty @{const_name corder} corder_rhs
    val (corder_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("corder_" ^ base_name ^ "_def", corder_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac [corder_thm] ctxt
      THEN my_print_tac "after class intro"
      THEN asm_full_simp_tac ctxt 1
      THEN my_print_tac "after simp"
      THEN Locale.intro_locales_tac true ctxt []) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class corder")  
  
  in thy' end


fun derive_some_corder dtyp_name thy = let
    val base_name = Long_Name.base_name dtyp_name
    
    val _ = Output.writeln ("creating corder for datatype " ^ base_name)
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
    val opt_ty = Type (@{type_name option}, [prod_ty])
    val some = Const (@{const_name Some}, prod_ty --> opt_ty) $ 
      (Const (@{const_name "Pair"}, comp_ty --> comp_ty --> prod_ty) $ less_eq $ less)    
    val corder_def = mk_def opt_ty @{const_name corder} some
    val (corder_thm,lthy) = Class.instantiation ([dtyp_name],vs,@{sort corder}) thy
      |> define_overloaded ("corder_" ^ base_name ^ "_def", corder_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => (Class.intro_classes_tac []
      THEN my_print_tac "after class instance"
      THEN rtac (@{thm corder_intro} OF [linorder_thm]) 1
      THEN my_print_tac "after corder_intro"
      THEN unfold_tac [corder_thm] ctxt
      THEN (REPEAT (blast_tac ctxt 1))
      )) lthy
    val _ = Output.writeln ("registered " ^ base_name ^ " in class corder")
 in thy'
end 

fun derive_corder typ_name param thy = 
  if param = "" then derive_some_corder typ_name thy else
  if param = "no" then derive_no_corder typ_name thy else
  if param = "linorder" then derive_corder_linorder typ_name thy else
  error "(no) and (linorder) are only optional parameters for deriving corder"

val setup = 
  Derive_Manager.register_derive "corder" "derives an order for a datatype or (no) order for any type, or uses (linorder) instance for corder" derive_corder #>
  Derive_Manager.register_derive "ceq" "use (no) equality for class ceq" derive_ceq #>
  Derive_Manager.register_derive "cenum" "use (no) enumeration for class cenum" derive_cenum #>
  Derive_Manager.register_derive "set_impl" ("choose " ^ supported_set_impl ^ " as set_impl for a datatype") derive_set_impl

end
