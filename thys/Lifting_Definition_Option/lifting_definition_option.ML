(*  Title:       Lifting Definition Option
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2014 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
signature LIFTING_DEFINITION_OPTION =
sig
  val lift_def_opt:
    (binding * string option * mixfix) * term -> (Proof.context -> tactic) ->
    (*         type                      rhs  *)
      local_theory -> local_theory
end

structure Lifting_Definition_Option: LIFTING_DEFINITION_OPTION =
struct

val term_to_string = YXML.string_of_body o Term_XML.Encode.term;
val typ_to_string = YXML.string_of_body o Term_XML.Encode.typ;

fun tactic_state_to_lthy tactic state =
    Proof.global_terminal_proof 
      ((Method.Basic (SIMPLE_METHOD o tactic), Position.no_range), NONE) state

fun lift_def_ml (binding, mx) ty rhs tactic =
    Lifting_Def.lift_def_cmd
      ((binding, SOME (typ_to_string ty), mx), term_to_string rhs, [])
  #> tactic_state_to_lthy tactic

fun define (def_name, eq) mixfix attrs lthy =
  let
    val attrs = case attrs of NONE => (Binding.empty, []) | SOME attrs => attrs
    val mixfix = case mixfix of NONE => NoSyn | SOME mixfix => mixfix
    val rhs = eq |> Syntax.check_term lthy |>
      Logic.dest_equals |>> dest_Free |> snd;
    val ((t, (_, thm)), lthy') = Local_Theory.define
      ((Binding.name def_name, mixfix), (attrs, rhs)) lthy
  in (t, thm, lthy')
end

fun mk_abort t = 
   let val ty = fastype_of t 
     in Const (@{const_name Code.abort}, @{typ String.literal} --> (@{typ unit} --> ty) --> ty)
      $ @{term "STR ''internal error in lift_definition_option''"}
      $ lambda (Free ("x", @{typ unit})) t
   end        
 
fun mk_if c t e = let
  val ty = fastype_of t
  in 
    Const (@{const_name If}, @{typ bool} --> ty --> ty --> ty) $ c $ t $ e
  end

fun mk_Some t = let
  val ty = fastype_of t
  in 
    Const (@{const_name Some}, ty --> Type (@{type_name option}, [ty])) $ t
  end

fun type_dest ty = let
  val err = "result type must be option-type"
  val res_ty = case body_type ty of 
    Type (opt,[res_ty]) => if opt = @{type_name option} then res_ty else error err
  | _ => error err
in
  (binder_types ty, res_ty)
end


fun get_export_morph ctxt ctxt1 = Proof_Context.export_morphism ctxt ctxt1

fun strip_cases ctac = ctac #> Seq.map snd

fun mk_case_tac (ctxt : Proof.context)
  (insts : term option list list)
  (thm : thm)
  (sub_case_tac : Proof.context * thm list * (string * cterm) list -> tactic) =
    (
      DETERM o strip_cases o Induct.cases_tac ctxt false insts (SOME thm) []
      THEN_ALL_NEW (fn i => Subgoal.SUBPROOF (fn {context = ctxt, prems = hyps, params = params, ...}
        => sub_case_tac (ctxt, hyps, params)) ctxt i)
    )
    1

fun insert_abs abs rhs = let
  val xs = strip_abs_vars rhs |> map Free
  val ite = betapplys (rhs, xs)
  val (c,t) = case ite of Const _ $ c $ t $ _ => (c,t) | _ => error "could not decompose if-then-else"
  val base = case t of Const _ $ base => base | _ => error "could not decompose if ... then Some .. else ..."
  val t = mk_Some (abs $ base)
  val e = Const (@{const_name None}, fastype_of t)
  val ite = mk_if c t e
in
  ite
end

fun transfer_tac ctxt i = Transfer.gen_frees_tac [] ctxt i
              THEN Transfer.transfer_tac true ctxt i

fun add_split thms = Context.proof_map (Simplifier.map_ss (fold Splitter.add_split thms))

val debug_out = if false then writeln else (K ())

fun lift_def_opt_main (raw_var,fin_rhs) (lthy1 : local_theory) =
  Runtime.exn_trace (fn () =>
  let 
      val lthy = lthy1
      val ((fin_bind, SOME fin_ty, fin_mixfix), lthy) = yield_singleton Proof_Context.read_vars raw_var lthy
      val prefix = Binding.name_of fin_bind
      val fin_rhs = Syntax.check_term lthy fin_rhs
      val (impl_tys, restr_ty) = type_dest fin_ty
      val (restr_lname, restr_arg_tys) = dest_Type restr_ty
      val restr_name = Long_Name.base_name restr_lname
      
      (* extraction of P from typedef = { x. P x} , defining witness satisfying P *)
      val (P, wit, wit_thmI, ty_vars, fresh_ty_vars, base_ty, restr_ty, info, lthy) = let 
        val info = case Typedef.get_info lthy restr_lname of [info] => info
           | _ => error ("failed to extract information for type " ^ restr_lname)
        val inhabit = info |> #2 |> #inhabited
        val base_ty = info |> #1 |> #rep_type
        val restr_ty = info |> #1 |> #abs_type
        val ty_vars = dest_Type restr_ty |> snd (* in order of type def. *)

        (* get schematic variables from inhabit theorem and reorder them according to ty_vars *)
        val sch_vars = let
          val ty_vars_raw = Thm.prop_of inhabit |> (fn t => Term.add_tvars t [])
          val sch_vars = map TVar ty_vars_raw
          val ty_vars_sch = map (fn ((n,_),s) => TFree (n,s)) ty_vars_raw
          val ty_to_sch_map_index = AList.lookup (op =) (ty_vars_sch ~~ sch_vars) #> the
        in 
          map ty_to_sch_map_index ty_vars
        end
        (* create three types of fresh typ-variables: for initial definition of witness,
           for type_definition, and for remaining part *)
        fun convert (n,ty) = TFree (n, snd (dest_TFree ty))
        val (names, lthy') = Variable.variant_fixes (map (fst o dest_TFree) ty_vars) lthy
        val ty_vars' = names |> (fn names => map convert (names ~~ ty_vars))
        val (names, _) = Variable.variant_fixes (map (fst o dest_TFree) ty_vars) lthy'
        val ty_vars'' = names |> (fn names => map convert (names ~~ ty_vars))
        
        (* now instantiate inhabit thm to ty_vars' *)
        val ty_vars'_map = map (Thm.ctyp_of lthy') sch_vars ~~ map (Thm.ctyp_of lthy') ty_vars'
        val inhabit = Thm.instantiate (ty_vars'_map, []) inhabit
        val some_thm = @{thm someI_ex} OF [inhabit]
        val some = some_thm |> Thm.prop_of |> HOLogic.dest_Trueprop 
           |> (fn x => case x of ( _ $ wit $ _) => wit | _ => error "could not extract witness")
        val some_ty = fastype_of some
        val unit_ty = @{typ unit}
        val u = Free ("u", unit_ty)
        val wit_ty = unit_ty --> some_ty
        val P = some |> (fn x => case x of ( _ $ Abs (_, _, _ $ _ $ (_ $ P))) => P | _ => error "could not extract invariant property")
        val wit_name = prefix ^ "_witness"
        val eq = Logic.mk_equals (Free (wit_name, wit_ty), lambda u some)
        val (wit,wit_thm,lthy) = define (wit_name, eq) NONE (SOME (Binding.name (wit_name ^ "_def"),[])) lthy
        val _ = debug_out ("step 1: created definition for witness " ^ wit_name)

        val lthy = let (* code equation for witness as code abort, to avoid SOME *)
          val wit_code_eq_t = HOLogic.mk_Trueprop (HOLogic.mk_eq (wit $ u, mk_abort (wit $ u)))
          val wit_code_eq = Goal.prove lthy ["u"] [] wit_code_eq_t (K (simp_tac lthy 1))
          val lthy = Local_Theory.note ((Binding.empty, @{attributes [code]}), [wit_code_eq]) lthy |> snd
        in lthy end
        val wit = wit $ @{term "()"}
        val wit_thm = Goal.prove lthy [] [] (Logic.mk_equals (wit, some))
          (K (unfold_tac lthy [wit_thm]))
        
        val wit_thm = let (* proving "P wit" *)
          val wit_thm_t = HOLogic.mk_Trueprop (P $ wit)
          val wit_thm = Goal.prove lthy [] [] wit_thm_t 
            (K (Method.insert_tac [some_thm] 1
              THEN unfold_tac lthy [Thm.symmetric wit_thm]
              THEN rtac @{thm CollectE} 1
              THEN assume_tac lthy 1 THEN assume_tac lthy 1
              ))
          val _ = debug_out "step 2: proved that witness satisfies invariant"
        in wit_thm end

        (* export things to global context, to have schematic type variables for typedef *)
        val morph = get_export_morph lthy lthy1
        val wit_thm = Morphism.thm morph wit_thm 
        val sch_vars = map (Morphism.typ morph) ty_vars' |> map dest_TVar
        val sch_vars_mapI =
          map (Thm.ctyp_of lthy o TVar) sch_vars ~~ map (Thm.ctyp_of lthy) restr_arg_tys
        val wit_thmI = wit_thm |> Thm.instantiate (sch_vars_mapI, [])
        val morph_t = Morphism.term morph #> subst_TVars (map fst sch_vars ~~ ty_vars)
      in (morph_t P, morph_t wit, wit_thmI, ty_vars, ty_vars'', base_ty, restr_ty, info, lthy) end

      val inverse_thm = info |> #2 |> #Rep_inverse
      val base = Const (info |> #1 |> #Rep_name, restr_ty --> base_ty)
      val abs  = Const (info |> #1 |> #Abs_name, base_ty --> restr_ty)

      val bool_ty = @{typ bool}

      (* typedef restricted_cond = "{ (b :: base, c :: bool). c \<longrightarrow> P b}" by blast *)
      val restr_c_name = prefix ^ "_cond"
      val b = Free ("b", base_ty)
      val c = Free ("c", bool_ty)
      val pair_ty = HOLogic.mk_prodT (base_ty, bool_ty)
      val mixfix = NoSyn
      val (info, lthy) = let
        val t_fresh = subst_atomic_types (ty_vars ~~ fresh_ty_vars)
        val false_wit = HOLogic.mk_prod (Const (@{const_name undefined}, base_ty), @{term False})
        val ex_thm =
          Ctr_Sugar_Util.cterm_instantiate_pos
            [NONE, SOME (Thm.cterm_of lthy (t_fresh false_wit))] @{thm exI}
        val imp = HOLogic.mk_imp (c, P $ b)
        val lam = lambda b (lambda c imp)
        val lam_ty = Term.fastype_of lam
        val caset = Const (@{const_name case_prod}, lam_ty --> pair_ty --> bool_ty) $ lam
        val collect = Const (@{const_name Collect}, (pair_ty --> bool_ty) --> HOLogic.mk_setT pair_ty) $ caset
        fun tac ctxt = rtac ex_thm 1 THEN blast_tac ctxt 1
        val concealed = false
        val (info, lthy) =
          Typedef.add_typedef concealed
            (Binding.name restr_c_name, map dest_TFree fresh_ty_vars, mixfix) 
            (t_fresh collect) 
            NONE tac lthy
        val _ = debug_out ("step 3: created type " ^ restr_c_name)
      in 
        (info, lthy)
      end

      val morph = Proof_Context.export_morphism lthy
          (Proof_Context.init_global (Proof_Context.theory_of lthy))

      (* setup_lifting type_definition_restricted_bool *)
      val type_def_thm = info |> snd |> snd |> #type_definition |> Morphism.thm morph
      val lthy = Lifting_Setup.setup_by_typedef_thm type_def_thm lthy
      val _ = debug_out ("step 4: performed lifting_setup")

      val restr_c_ty = let (* convert type over fresh ty_vars into original ty_vars *)
        val restr_c_ty' = info |> snd |> fst |> #abs_type  
        val sch_vars = dest_Type (Morphism.typ morph restr_c_ty') |> snd |> map (fst o dest_TVar)
        val sch_subst_ty = typ_subst_TVars (sch_vars ~~ ty_vars)
      in 
        sch_subst_ty (Morphism.typ morph restr_c_ty')
      end

      (* here we instantiate the type-parameters from typedef 
         to the actual parameters *)
      val mapping = ty_vars ~~ restr_arg_tys
      val tyI = typ_subst_atomic mapping
      val tI = subst_atomic_types mapping
      val (restr_c_ty, restr_ty, base_ty, pair_ty) = @{apply 4} tyI 
          (restr_c_ty, restr_ty, base_ty, pair_ty)
      val (b, P, wit, abs, base) = @{apply 5} tI
          (b, P, wit, abs, base)

      (* lift_definition restricted_cond_bool :: "restricted_cond \<Rightarrow> bool" is snd . *)
      val restr_c_bool_name = restr_c_name ^ "_bool"
      val restr_c_bool_ty = restr_c_ty --> bool_ty
      val rhs = Const (@{const_name snd}, pair_ty --> bool_ty)
      val lthy =
        lift_def_ml (Binding.name restr_c_bool_name, mixfix) restr_c_bool_ty rhs (K all_tac) lthy
      val _ = debug_out ("step 5: created lift_definition for " ^ restr_c_bool_name)

      (* lift_definition restricted_cond_restrict :: "restricted_cond \<Rightarrow> restricted" is 
        "% (b, c). if c then b else wit" using P_wit by (cases (b,c), auto) *)

      val restr_c_restr_name = restr_c_name ^ "_" ^ restr_name
      val restr_c_restr_ty = restr_c_ty --> restr_ty
      val binding = Binding.name restr_c_restr_name
      val lam = lambda b (lambda c (mk_if c b wit))
      val lam_ty = Term.fastype_of lam
      val caset = Const (@{const_name case_prod}, lam_ty --> pair_ty --> base_ty) $ lam
      fun tac ctxt = Subgoal.FOCUS (fn focus =>            
             mk_case_tac ctxt [[SOME (#params focus |> hd |> snd |> Thm.term_of)]]
              @{thm prod.exhaust}
             (fn (ctxt, prems2, _) => 
                Method.insert_tac (#prems focus @ prems2 @ [wit_thmI]) 1 
              THEN auto_tac ctxt)
           ) ctxt 1
      val lthy = lift_def_ml (binding,mixfix) restr_c_restr_ty caset tac lthy
      val _ = debug_out ("step 6: created lift_definition for " ^ restr_c_restr_name)

      (* lift_definition restricted_cond :: "impl \<Rightarrow> restricted_cond" is
         "\<lambda> i. if check i then (gen i, True) else (wit, False)"
         unfolding simplify_cond
         by (rule resticted_condI, insert check, blast) *)

      val binding = Binding.name restr_c_name
      val xs = strip_abs_vars fin_rhs 
      val (check, gen) = case betapplys (fin_rhs, map Free xs) of 
          (_ $ check $ ( _ $ gen) $ _) => (check, gen) 
        | _ => error "internal error in lift_definition_option"
      val ite = mk_if check (HOLogic.mk_prod (gen, @{term True})) (HOLogic.mk_prod (wit, @{term False}))
      val rhs = fold_rev (fn x => fn t => lambda (Free x) t) xs ite
      val crucial_prop = fold_rev (fn x => fn t => Logic.all (Free x) t) xs (Logic.mk_implies (
         HOLogic.mk_Trueprop check, 
         HOLogic.mk_Trueprop (P $ gen)))


      fun after_qed check_thm lthy = let
          fun tac ctxt = unfold_tac ctxt @{thms simplify_cond}
            THEN rtac @{thm restrict_condI} 1
            THEN Method.insert_tac (hd check_thm) 1 
            THEN blast_tac ctxt 1
          val ty = impl_tys ---> restr_c_ty
          val lthy = lift_def_ml (binding,mixfix) ty rhs tac lthy
          val _ = debug_out ("step 7: created lift_definition for " ^ restr_c_name)
    
    
          (* definition restricted_of :: "impl \<Rightarrow> restricted option" where
              "restricted_of i \<equiv> let rci = restricted_cond i
                in if (restricted_cond_bool rci) then Some (restricted_cond_restricted rci) else None" *)
          
          val rcr = Free (restr_c_restr_name, restr_c_restr_ty) 
          val rcb = Free (restr_c_bool_name, restr_c_bool_ty) 
          val binding = fin_bind
          val mixfix = fin_mixfix
          val rc = Free (restr_c_name, ty)
          val rci = list_comb (rc, map (fn x_i => Bound (snd x_i)) (rev (xs ~~ (0 upto (length xs - 1)))))
          val lthy' = Variable.add_fixes (map fst xs) lthy |> snd
          val [r,rc_var] = Variable.variant_fixes ["r", "rc"] lthy' |> fst 
          val rc_var = Free (rc_var, restr_c_ty)
          val ro_ty = Type (@{type_name option}, [restr_ty])
          val ite = mk_if (rcb $ rc_var) 
            (mk_Some (rcr $ rc_var)) 
            (Const (@{const_name None}, ro_ty))
          val lett = Const (@{const_name Let}, restr_c_ty --> (restr_c_ty --> ro_ty) --> ro_ty)
            $ rci $ lambda rc_var ite
          val def_rhs = fold_rev (fn x_ty => fn t => Abs (fst x_ty, snd x_ty, t)) xs lett
          val r_of_name = prefix
          val ((r_of, (_, def_thm)), lthy) = Local_Theory.define
            ((binding, mixfix), ((Binding.name (r_of_name ^ "_def"), @{attributes [code]}), def_rhs)) lthy
          val _ = debug_out ("step 8: created definition for " ^ Binding.name_of binding)
          
          val def_thm' = Goal.prove lthy [] [] 
            (HOLogic.mk_eq (betapplys (r_of, map Free xs), betapplys (def_rhs, map Free xs)) |> HOLogic.mk_Trueprop)
            (K (unfold_tac lthy [def_thm]))
    
     (* lemma restricted_of: "restricted_of i = Some r \<Longrightarrow> base r = gen i"
          unfolding restricted_of_def Let_def
          by (transfer, force split: if_splits) *)
          val r = Free (r, restr_ty)
          val r_of_is = list_comb (r_of, map Free xs)
          val ass = HOLogic.mk_eq (r_of_is, mk_Some r) |> HOLogic.mk_Trueprop
          val concl = HOLogic.mk_eq (base $ r, gen) |> HOLogic.mk_Trueprop
          val some_thm = Goal.prove lthy (map fst (dest_Free r :: xs)) [ass] concl
            (fn {context = ctxt, prems = prems, ...} => (
                   Method.insert_tac prems 1
              THEN unfold_tac ctxt (def_thm :: @{thms Let_def})
              THEN transfer_tac ctxt 1
              THEN force_tac (add_split @{thms if_splits} lthy) 1
            ))
          val binding = Binding.name (r_of_name ^ "_Some")
          val lthy = Local_Theory.note ((binding, []), [some_thm]) lthy |> snd
          val _ = debug_out ("step 9: derived thm " ^ Binding.name_of binding)

          val eq = HOLogic.mk_eq (r_of_is, insert_abs abs fin_rhs) |> HOLogic.mk_Trueprop
          val pre_thm = @{thm valid_definition}
            |> Ctr_Sugar_Util.cterm_instantiate_pos 
             [SOME (Thm.cterm_of lthy abs),
              SOME (Thm.cterm_of lthy base),
              SOME (Thm.cterm_of lthy r_of_is), NONE, 
              SOME (Thm.cterm_of lthy rcb),
              SOME (Thm.cterm_of lthy rcr),
              SOME (Thm.cterm_of lthy gen),
              SOME (Thm.cterm_of lthy check)]
            |> (fn thm => thm OF [inverse_thm, def_thm', some_thm])  
          val eq_thm = Goal.prove lthy (map fst xs) [] eq (fn {context = ctxt, ...} =>
             rtac pre_thm 1
           THEN assume_tac ctxt 1
           THEN transfer_tac ctxt 1
           THEN rtac @{thm snd_if} 1)
          val eq_binding = Binding.name (r_of_name)
          val lthy = Local_Theory.note ((eq_binding, []), [eq_thm]) lthy |> snd
          val _ = debug_out ("step 10: derived thm " ^ Binding.name_of eq_binding)

          val _ =
            writeln
              ("registered code equations for " ^ Binding.name_of fin_bind ^ "\n" ^
               "derived theorems " ^ Binding.name_of binding ^ " and " ^ Binding.name_of eq_binding)
        in 
          lthy
        end      
      val state = Proof.theorem NONE after_qed [[(crucial_prop, [])]] lthy
  in state
  end)

fun lift_def_opt args tac lthy = lift_def_opt_main args lthy 
  |> tactic_state_to_lthy tac

val liftdef_parser = ((Parse.binding -- (@{keyword "::"} |-- Parse.typ -- Parse.opt_mixfix')) >> Parse.triple2)
    --| @{keyword "is"} -- Parse.term 

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "lift_definition_option"}
    "definition for constants of option type over the quotient type"
      ((liftdef_parser >> (fn ((b, ty, mf), t) => fn lthy =>
        lift_def_opt_main ((b, SOME ty, mf), 
          Syntax.parse_term lthy t) lthy)))
end
