(*  Title:      local_typedef.ML
    Author:     Ondřej Kunčar, TU München

    Implementation of Local Typedef Rule.
*)

signature LOCAL_TYPEDEF =
sig
  val cancel_type_definition: thm -> thm
  val cancel_type_definition_attr: attribute
end

structure Local_Typedef : LOCAL_TYPEDEF =
struct

(*
Local Typedef Rule (LT)

\<Gamma> \<turnstile> (\<exists>(Rep::'b \<Rightarrow> \<tau>) Abs. type_definition Rep Abs A) \<Longrightarrow> \<phi>
-------------------------------------------------------------  ['b not in \<phi>, \<Gamma>, A; sort('b) = HOL.type]
               \<Gamma> \<turnstile> A \<noteq> \<emptyset> \<Longrightarrow> \<phi>
*)

(** BEGINNING OF THE TRUSTED CODE **)

  fun dest_typedef (Const (@{const_name Ex}, _) $ Abs (_, _, 
        (Const (@{const_name Ex}, _) $ Abs (_, Abs_type,  
        (Const (@{const_name type_definition}, _)) $ Bound 1 $ Bound 0 $ set)))) = 
      (Abs_type, set)
    | dest_typedef t = raise TERM ("dest_typedef", [t]);
  
  fun cancel_type_definition thm =
    let
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm thm)
      val prop = Thm.prop_of thm
      val hyps = Thm.hyps_of thm
  
      val _ = if Thm.extra_shyps thm = [] then () 
        else error "The theorem has dangling sort constraints."
      val _ = if Thm.tpairs_of thm = [] then () 
        else error "The theorem contains unresolved flex-flex pairs."
  
      val (typedef_assm, phi) = Logic.dest_implies prop
        handle TERM _ => error "The theorem is not an implication."
      val (abs_type, set) = (dest_typedef o HOLogic.dest_Trueprop) typedef_assm
        handle TERM _ => error ("Assumption " ^ Syntax.string_of_term ctxt typedef_assm ^ 
          " is not of form ``(\<exists>Rep Abs. type_definition Rep Abs A)''.")
  
      val (repT, absT) = (dest_funT) abs_type;
      val _ = if is_TVar absT then ()
        else error ("Not a schematic type variable: " ^ Syntax.string_of_typ ctxt absT)
      val (absT_name, sorts) = dest_TVar absT;
      
      val _ = if sorts = @{sort type} then () else error "The abstract type is not of a sort '{type}'."
  
      fun check_absT_in_type msg typ = 
        let
          fun check_absT (tvar as TVar (name, _)) = if name = absT_name 
            then error ("The " ^ msg ^ " contains a forbidden type: " ^ Syntax.string_of_typ ctxt tvar)
            else I 
          | check_absT _ = I;
        in
          fold_atyps check_absT typ
        end;
       
      val _ = fold_types (check_absT_in_type "conclusion") phi ();
      val _ = fold (fold_types (check_absT_in_type "hypothesis")) hyps ()
      val _ = fold_types (check_absT_in_type "set term") set ();
  
      val not_empty_assm = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (set, HOLogic.mk_set repT [])))
      val prop = Logic.list_implies (hyps @ [not_empty_assm], phi)
    in
      Thm.cterm_of ctxt prop
    end;

(** END OF THE TRUSTED CODE **)

  val (_, cancel_type_definition_oracle) = Context.>>> (Context.map_theory_result
    (Thm.add_oracle (@{binding cancel_type_definition}, cancel_type_definition)));

  fun cancel_type_definition thm = cancel_type_definition_oracle (Thm.strip_shyps thm) |>
    fold (fn hyp => fn thm => Thm.assume hyp COMP thm) (thm |> Thm.chyps_of)

  val cancel_type_definition_attr = Thm.rule_attribute [] (K cancel_type_definition);

  val _ = Context.>> (Context.map_theory (Attrib.setup @{binding cancel_type_definition} 
    (Scan.succeed cancel_type_definition_attr) "cancels local type definition")) 
end