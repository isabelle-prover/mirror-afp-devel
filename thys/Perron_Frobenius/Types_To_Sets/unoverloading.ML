(*  Title:      unoverloading.ML
    Author:     Ondřej Kunčar, TU München

    Implementation of Unoverloading Rule.
*)

signature UNOVERLOADING =
sig
  val unoverloading: cterm -> thm -> thm
  val unoverloading_attr: cterm -> attribute
end

structure Unoverloading : UNOVERLOADING =
struct

(*
Unoverloading Rule (UO)

            \<turnstile>  \<phi>
---------------------------- [no type or constant in \<phi> depends on c::\<sigma>; c::\<sigma> is undefined]
  \<turnstile> \<forall>x::\<sigma>. \<phi>[x::\<sigma> / c::\<sigma>]
*)

(* The following functionality in functions match_args, reduct, collect_consts_types,
   prep, and not_instance_args was copied from already existing trusted code because
   the code is not public *)

  (* >= *)
  fun match_args (Ts, Us) =
    if Type.could_matches (Ts, Us) then
      Option.map Envir.subst_type
        (SOME (Type.raw_matches (Ts, Us) Vartab.empty) handle Type.TYPE_MATCH => NONE)
    else NONE;
  
  fun reduct Us (Ts, rhs) =
    (case match_args (Ts, Us) of
      NONE => NONE
    | SOME subst => SOME (map (apsnd (map subst)) rhs));
  fun reducts defs ((d, Us):Defs.entry) : Defs.entry list = 
    get_first (reduct Us) (Defs.get_deps defs d) |> these;

  fun collect_consts_types thy tm =
   let
     val consts =
       fold_aterms (fn Const const => insert (op =) (Theory.const_dep thy const) | _ => I) tm [];
     val types =
       (fold_types o fold_subtypes) (fn Type t => insert (op =) (Theory.type_dep t) | _ => I) tm [];
   in
     consts @ types
   end;

  fun prep (item, args) =
    (case fold Term.add_tvarsT args [] of
      [] => (item, map Logic.varifyT_global args)
    | vs => raise TYPE ("Illegal schematic type variable(s)", map TVar vs, []));

  fun not_instance_args (Ts, Us) =
    not (Type.could_matches (Ts, Us)) orelse
      ((Type.raw_matches (Ts, map (Logic.incr_tvar (maxidx_of_typs Ts + 1)) Us) Vartab.empty; false)
        handle Type.TUNIFY => true);

(* The actual implementation *)

(** BEGINNING OF THE TRUSTED CODE **)

fun unoverloading cconst thm =
    let
      val _ = if Thm.hyps_of thm = [] then ()
        else error "The theorem has meta hypotheses."
      val _ = if Thm.extra_shyps thm = [] then () 
        else error "The theorem has dangling sort constraints."
      val _ = if Thm.tpairs_of thm = [] then () 
        else error "The theorem contains unresolved flex-flex pairs."

      val thy = Thm.theory_of_thm thm
      val ctxt = Proof_Context.init_global thy
      val const = Thm.term_of cconst
      val _ = case const of Const _ => () |  t => 
        error ("The term is not a constant: " ^ Syntax.string_of_term ctxt t)
      val tm = Thm.prop_of thm
      val defs = Theory.defs_of thy

      fun check_dependencies thy tm ov_const =
        let
          val prt = Pretty.string_of oo Defs.pretty_entry;
      
          fun err context (c, Ts) (d, Us) =
            error (prt context (c, Ts) ^ " depends on " ^ prt context (d, Us));
      
          fun not_same (e1:Defs.entry) (e2:Defs.entry) =
            e1 <> e2
      
          val context = Defs.global_context thy
      
          fun no_dependency entry ov_entry = forall (not_same ov_entry) (reducts defs entry)
            orelse err context entry ov_entry;
      
          val tm = Logic.varify_global tm
          val ov_const = Logic.varify_global ov_const
          val ov_entry = Theory.const_dep thy (dest_Const ov_const);
          val const_types = collect_consts_types thy tm
        in
          forall (fn entry => no_dependency entry ov_entry) const_types
        end;
      
      val ([fixed_tm, fixed_const], ctxt) = Variable.import_terms true [tm, const] ctxt;

      val _ = check_dependencies thy fixed_tm fixed_const

      val const_delta = prep (Theory.const_dep thy (dest_Const fixed_const));
      
      val Uss = Defs.specifications_of defs (fst const_delta)
      val _ = map (fn spec => if not_instance_args (#lhs spec, snd const_delta) then () 
        else error "The constant instance has already a specification.") Uss
    in
      Thm.cterm_of ctxt (Logic.all const tm)
    end

(** END OF THE TRUSTED CODE **)

  val (_, unoverloading_oracle) = Context.>>> (Context.map_theory_result
    (Thm.add_oracle (@{binding unoverloading},
    fn (const, thm) => unoverloading const  thm)));

  fun unoverloading const thm = unoverloading_oracle (const, (Thm.strip_shyps thm))

  val parse_schematic_term = Args.context -- Scan.lift Parse.term >> 
    (fn (ctxt, str) => 
    let
      val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in       
      Syntax.read_term ctxt str 
    end)

  (*val parse_schematic_typ = Args.context -- Scan.lift Parse.typ >> 
    (fn (ctxt, str) => 
    let
      val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in       
      Syntax.read_typ ctxt str 
    end)

  val const = Args.context -- parse_schematic_term -- parse_schematic_typ >>
    (fn ((ctxt, Const (name, _)), typ) => Thm.cterm_of ctxt (Const (name, typ)) | ((ctxt, t), _) =>
    error ("The term is not a constant: " ^ Syntax.string_of_term ctxt t)); *)

val const = Args.context -- parse_schematic_term  >>
    (fn (ctxt, Const c) => Thm.cterm_of ctxt (Const c) | (ctxt, t) =>
    error ("The term is not a constant: " ^ Syntax.string_of_term ctxt t));

  fun unoverloading_attr const = 
    Thm.rule_attribute [] (fn _ => fn thm => (unoverloading const thm));

  val _ = Context.>> (Context.map_theory (Attrib.setup @{binding unoverloading} 
    (const >> unoverloading_attr) "unoverloads an uninterpreted constant"))

end