(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)

signature CEQ_GENERATOR = 
sig 
  
  (* derives a trivial instance (None) for class ceq, works for every type *)
  val derive_no_ceq : string -> theory -> theory

  (* derives a class instance for ceq by using equality (op =), works for every type *)
  val derive_eq_ceq : string -> theory -> theory

  (* derives a class instance for ceq by using ceq for depending types, only for datatypes *)
  val derive_ceq_ceq : string -> theory -> theory

  (* registeres method in Derive-Manager *)
  val setup : theory -> theory

end

structure Ceq_Generator : CEQ_GENERATOR = 
struct
open Datatype_Aux; 
open Datatype; 
open Derive_Aux;
open Containers_Generator;

fun mk_some_eq ty = mk_Some (HOLogic.eq_const ty)

fun mk_none_ceq ty =
  let 
    val eqt = ty --> ty --> @{typ bool}
    val oty = Type (@{type_name option},[eqt])
    val none = Const (@{const_name None},oty)
  in none
end  

(* construct free variable x_i *)
fun mk_free_tysubst_i typ_subst x i ty = Free (x ^ string_of_int i, ty |> typ_subst)

fun mk_eq_list thy info sort = let
    val typ_subst = typ_subst_for_sort thy info sort 
    val descr = #descr info
    fun typ_of dty = typ_of_dtyp descr dty |> typ_subst
    val non_rec_dtys = descr |> map (#3 o snd) |> List.concat |> map snd |> List.concat
      |> filter (fn Datatype.DtRec _ => false | _ => true) |> distinct (op =)
    val eq_list = map_index (fn (i,dty) => 
      let val ty = typ_of dty
          val name = "eq_" ^ string_of_int i
        in (dty, Free (name, ty --> ty --> @{typ bool})) end) non_rec_dtys
    in eq_list
  end

fun mk_eq_idx eqs thy info sort =
  let 
    val typ_subst = typ_subst_for_sort thy info sort 
    val descr = #descr info
    fun typ_of dty = typ_of_dtyp descr dty |> typ_subst
    val rec_names = #rec_names info
    val mk_free_i = mk_free_tysubst_i typ_subst
    fun rec_idx i dtys = dt_number_recs (take i dtys) |> fst
    fun mk_rhss (idx,(ty_name,_,cons)) = 
      let 
        val ty = typ_of (DtRec idx) 
        val linfo = the_info thy ty_name
        val case_name = #case_name linfo
        fun mk_rhs (i,(_,dtysi)) = 
          let 
            val lvars = map_index (fn (i,dty) => mk_free_i "x_" i (typ_of dty)) dtysi
            fun res_var (i,oc) = mk_free_i "res_" oc (typ_of (DtRec i) --> @{typ bool});
            val res_vars = dt_number_recs dtysi
                     |> snd 
                     |> map res_var
            fun mk_case (j,(_,dtysj)) = 
              let 
                val rvars = map_index (fn (i,dty) => mk_free_i "y_" i (typ_of dty)) dtysj
                val x = nth lvars
                val y = nth rvars                    
                fun combine_dts [] = @{term True}
                  | combine_dts ((_,c) :: []) = c
                  | combine_dts ((_,c) :: ics) = HOLogic.mk_conj (c, combine_dts ics)
                fun eq_of_dty (i,DtRec j) = res_var (j,rec_idx i dtysj) $ y i
                  | eq_of_dty (i,dty) = 
                      let
                        val xi = x i
                        val ty = Term.type_of xi
                        val eq = eqs ty dty
                      in eq $ xi $ y i end
                val rhs = 
                  if i = j then map_index eq_of_dty dtysi
                    |> map_index I
                    |> combine_dts
                    else @{term False}
                val lam_rhs = fold lambda (rev rvars) rhs
              in lam_rhs end
            val cases = map_index mk_case cons
            val case_ty = (map type_of cases @ [ty]) ---> @{typ bool}
            val rhs_case = list_comb (Const (case_name, case_ty), cases)
            val rhs = fold lambda (rev (lvars @ res_vars)) rhs_case
          in rhs end
        val rec_args = map_index (fn (i,c) => (mk_rhs (i,c),i,idx)) cons 
      in rec_args end
    val nrec_args = List.concat (map mk_rhss descr)
    val rec_args = map #1 nrec_args
    fun mk_rec i = 
      let 
        val ty = typ_of (DtRec i)
        val rec_ty = map type_of rec_args @ [ty,ty] ---> @{typ bool}
        val rec_name = nth rec_names i
        val rhs = list_comb (Const (rec_name, rec_ty), rec_args)
      in rhs end
  in (mk_rec,nrec_args) end

fun mk_prop_trm eqs thy info sort
  (gen : (int -> term) -> (term -> term -> term)list -> term list * term list) = 
  let 
    fun main idx = 
      let
        val xs = mk_xs thy info sort idx
        fun eq a b = (mk_eq_idx eqs thy info sort |> fst) idx $ a $ b
      in gen xs [eq] end
  in #descr info  
    |> map (fst #> main)
  end

fun eq_prop_gen xs [eq] = 
  let 
    val (x,y) = (xs 1, xs 2)
  in ([HOLogic.mk_eq (eq x y,HOLogic.mk_eq (x,y))], [x,y]) end

fun mk_eq_thm thy info = 
  let
    val sort = @{sort "type"}
    fun main_tac ctxt ih_hyps ih_prems y_prem solve_with_tac _ _ _ _ _ = 
      (* TODO: for more complicated (wrt. nesting) datatypes, this simple tactic fails !
        e.g., datatype test = Foo "(test * test)list"    fails whereas 
              datatype test = Foo "(test option)list"    succeeds *)
      solve_with_tac ctxt (y_prem :: ih_prems @ ih_hyps)
    fun eqs ty = K (HOLogic.eq_const ty)
    val thm = mk_binary_thm (mk_prop_trm eqs) (mk_eq_idx eqs) @{const_name HOL.eq} thy info eq_prop_gen sort main_tac
  in 
    thm
  end

fun mk_ID_ceq eq_var = 
  let
    val ty = fastype_of eq_var
    val ceq = Const (@{const_name ceq}, Type (@{type_name option}, [ty]))
    val cty = fastype_of ceq
    val ID_ceq = Const (@{const_name ID}, cty --> cty) $ ceq
  in 
    ID_ceq
  end

fun mk_ceq_thm thy info = 
  let
    val sort = @{sort "ceq"}
    val eqs = mk_eq_list thy info sort
    val eq_vars = map snd eqs
    val prems = map (fn eq_var => let
        val ID_ceq = mk_ID_ceq eq_var
        val some_eq_var = mk_Some eq_var
      in HOLogic.mk_Trueprop (HOLogic.mk_eq (ID_ceq, some_eq_var))
      end) eq_vars
    val eq_thm = mk_eq_thm thy info
    val (rec_x_y, eq_x_y) = mk_prop_trm (fn _ => AList.lookup (op =) eqs #> Option.valOf) thy info sort eq_prop_gen
      |> prop_trm_to_major_imp |> fst |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
    fun remove_x_y t = dest_comb t |> fst |> dest_comb |> fst
    val (rec_t,eq_t) = (remove_x_y rec_x_y, remove_x_y eq_x_y)
    val equality = HOLogic.mk_Trueprop (HOLogic.mk_eq (rec_t,eq_t))
    val xs = map (dest_Free #> fst) eq_vars
    val thm = Goal.prove (Proof_Context.init_global thy) xs prems equality 
      (fn {context = ctxt, prems = prems'} => 
      let val prems = map_index (fn (i,prem') => let
          val eq_var = nth eq_vars i        
          val ty = fastype_of eq_var
          val eq = Const (@{const_name HOL.eq}, ty)
          val equality = HOLogic.mk_Trueprop (HOLogic.mk_eq (eq_var,eq))
          val prem = Goal.prove ctxt [] [] equality (K (
              rtac @{thm ID_ceq} 1
              THEN rtac prem' 1
            ))
        in prem end 
        ) prems' 
      in
        unfold_tac ctxt prems
        THEN rtac @{thm ext} 1
        THEN rtac @{thm ext} 1
        THEN rtac eq_thm 1
      end 
      )
     val success = mk_Some rec_t
     val res_ty = fastype_of success
     val none = Const (@{const_name None}, res_ty)
     val case_name = @{const_name option_case}
     val rhs = fold_rev (fn eq_var => fn t => let
         val eq_ty = fastype_of eq_var
         val case_t = Const (case_name, res_ty --> (eq_ty --> res_ty) --> Type (@{type_name option}, [eq_ty]) --> res_ty)         
         val case_applied = case_t $ none $ lambda eq_var t $ mk_ID_ceq eq_var 
       in
         case_applied
       end) eq_vars (mk_Some rec_t)
  in 
    (thm,rhs,eq_vars)
  end

fun derive_ceq_ceq dtyp_name thy =
  let
    val tyco = dtyp_name
 
    val base_name = Long_Name.base_name tyco
    val _ = writeln ("creating equality for datatype " ^ base_name)
    val sort = @{sort ceq}
    val info = Datatype.the_info thy tyco
    val vs_of_sort =
      let val i = Datatype.the_spec thy tyco |> #1
      in fn sort => map (fn (n,_) => (n, sort)) i end
    val vs = vs_of_sort sort
    val (ceq_eq_thm, ceq_rhs, eq_vars) = mk_ceq_thm thy info
    val ceq_ty = Term.fastype_of ceq_rhs
    val ceq_def = mk_def ceq_ty @{const_name ceq} ceq_rhs
    val (ceq_thm,lthy) = Class.instantiation ([dtyp_name],vs,sort) thy
      |> define_overloaded ("ceq_" ^ base_name ^ "_def", ceq_def)
    val thy' = Class.prove_instantiation_exit (fn ctxt => let
        fun split_tac ceq_eq_thm [] = 
          unfold_tac ctxt @{thms option.simps(1)}
          THEN unfold_tac ctxt [ceq_eq_thm]
          THEN blast_tac ctxt 1
        |  split_tac ceq_eq_thm (_ :: rest) = fn thm => let
            val ID_trm = Thm.prems_of thm |> hd 
              |> (fn t => if Logic.is_all t then Logic.dest_all t |> snd else t)
              |> Logic.dest_implies |> fst 
              |> HOLogic.dest_Trueprop
              |> HOLogic.dest_eq |> fst
              |> dest_comb |> snd
            fun sub_case_tac (ctxt,k,prems,_) = let
                val ID_eq_thm = nth prems 1
                val prem = hd prems
              in 
                if k = 1 then 
                  Method.insert_tac [prem] 1
                  THEN unfold_tac ctxt [ID_eq_thm]
                  THEN unfold_tac ctxt @{thms option.cases}
                  THEN split_tac (ceq_eq_thm OF [ID_eq_thm]) rest
              else 
                  Method.insert_tac [prem] 1
                  THEN unfold_tac ctxt [ID_eq_thm]
                  THEN unfold_tac ctxt @{thms option.simps}
              end
          in 
            mk_case_tac ctxt [[SOME ID_trm]] @{thm option.exhaust} sub_case_tac thm
          end
      in 
        Class.intro_classes_tac []
        THEN unfold_tac ctxt [ceq_thm]
        THEN split_tac ceq_eq_thm eq_vars
      end) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class ceq")
    val typ_subst = typ_subst_for_sort thy info sort 
    val main_ty = typ_of_dtyp (#descr info) (DtRec 0) |> typ_subst
    val param_tys = dest_Type main_ty |> snd   
    fun mk_is_ceq ty = mk_is_c_dots ty @{const_name is_ceq}
    val main_is_ceq = mk_is_ceq main_ty
    val param_is_ceq = map mk_is_ceq param_tys
    val is_ceq_thm_trm = HOLogic.mk_Trueprop (case param_is_ceq of 
      [] => main_is_ceq
    | _ => HOLogic.mk_eq (main_is_ceq,HOLogic_list_conj param_is_ceq))
    val is_ceq_thm = Goal.prove (Proof_Context.init_global thy') [] [] is_ceq_thm_trm 
      (fn {context = ctxt, prems = _} => 
        simp_tac (Splitter.add_split @{thm option.split} ctxt 
          addsimps (ceq_thm :: @{thms ID_Some ID_None is_ceq_def})
        ) 1
      )
    val thy'' = register_is_c_dots_lemma @{const_name is_ceq} base_name is_ceq_thm thy' 
  in thy'' end

val derive_no_ceq = derive_none @{const_name ceq} @{sort ceq} mk_none_ceq

fun derive_eq_ceq typ_name thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val _ = writeln ("use equality for class ceq and type " ^ base_name)
    val sort = @{sort ceq}
    val (ty,vs) = typ_and_vs_of_typname thy typ_name @{sort type}
    val ceq_rhs = mk_some_eq ty
    val ceq_ty = Term.fastype_of ceq_rhs
    val ceq_def = mk_def ceq_ty @{const_name ceq} ceq_rhs
    val (ceq_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> define_overloaded ("ceq_" ^ base_name ^ "_def", ceq_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac []
      THEN unfold_tac ctxt [ceq_thm]
      THEN force_tac ctxt 1) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class ceq")  
    val thy'' = derive_is_c_dots_lemma ty @{const_name is_ceq} [ceq_thm, @{thm is_ceq_def}] base_name thy' 
  in thy'' end

fun derive_ceq typ_name param thy = 
  (if (param = "") then derive_ceq_ceq else 
   if (param = "eq") then derive_eq_ceq else
   if (param = "no") then derive_no_ceq else
   error "optional parameter for class ceq must be 'no' or 'eq'")
   typ_name thy

val setup = 
  Derive_Manager.register_derive "ceq" "use (no) equality for class ceq" derive_ceq 

end
