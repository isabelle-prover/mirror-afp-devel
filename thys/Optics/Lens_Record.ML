signature LENS_UTILS =
sig
  val add_alphabet :
     (string * class list) list * binding ->
       string option -> (binding * typ * mixfix) list -> theory -> theory

  val add_alphabet_cmd :
     (string * string option) list * binding ->
       string option -> (binding * string * mixfix) list -> theory -> theory

  val rename_alpha_vars : tactic
end;

structure Lens_Utils : LENS_UTILS =
struct

(* We set up the following syntactic entities that correspond to various parts of Isabelle syntax
  and names that we depend on. These code would need to be updated if the names of the Isabelle
  and lens theories and/or theorems change. *)

val FLDLENS = "FLDLENS"
val BASELENS = "BASELENS"
val base_lensN = "base\<^sub>L"
val child_lensN = "more\<^sub>L"
val all_lensN = "all\<^sub>L"
val base_moreN = "base_more"
val bij_lens_suffix = "_bij_lens"
val bij_lensesN = "bij_lenses"
val vwb_lens_suffix = "_vwb_lens"
val sym_lens_suffix = "_sym_lens"
val Trueprop = @{const_name Trueprop}
val HOLeq = @{const_name HOL.eq}

val lens_defsN = "lens_defs"
val lens_defs = (Binding.empty, [Token.make_src (lens_defsN, Position.none) []])
val alpha_splitsN = "alpha_splits"
val alpha_splits = [Token.make_src (alpha_splitsN, Position.none) []]
val equivN = "equivs"
val splits_suffix = ".splits"
val defs_suffix = ".defs"
val slens_view = "view"
val slens_coview = "coview"

(* The following code is adapted from the record package. We generate a record, but also create
   lenses for each field and prove properties about them. *)

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));


fun add_record_cmd overloaded (params, binding) raw_parent fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1; 
    val ctxt3 = fold Variable.declare_typ (map (fn (_, ty, _) => ty) fields) ctxt2
    val params' = (map (Proof_Context.check_tfree ctxt3) params);
  in thy |> Record.add_record overloaded (params', binding) parent fields end;

(* Get all the parents of a given named record *)

fun get_parents thy nm = 
  case Record.get_parent thy nm of
    SOME (ts, nm') => (ts, nm') :: get_parents thy nm' |
    NONE => [];

(* Construct a theorem and proof that a given field lens is very well-behaved *)

fun lens_proof tname x thy =
  Goal.prove_global thy [] []
  (hd (Type_Infer_Context.infer_types
          (Proof_Context.init_global thy)
          [Lens_Lib.mk_vwb_lens (Syntax.const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x))]))
  (fn {context = context, prems = _}
                       => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                                , PARALLEL_ALLGOALS (asm_simp_tac 
                                                      (fold Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def") :: Global_Theory.get_thms thy (tname ^ ".defs"))
                                                                     context))])

fun lens_sym_proof tname thy =
  Goal.prove_global thy [] []
  (hd (Type_Infer_Context.infer_types
          (Proof_Context.init_global thy)
          [ Const (Trueprop, dummyT)
          $ (Syntax.const Lens_Lib.sym_lensN $ Syntax.const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ all_lensN))]))
  (fn {context = context, prems = _}
                       => EVERY [ Classical.rule_tac context [@{thm sym_lens.intro}] [] 1
                                , PARALLEL_ALLGOALS (asm_simp_tac 
                                                      (fold Simplifier.add_simp (@{thms slens.defs} @ Global_Theory.get_thms thy (tname ^ ".defs"))
                                                                     context))])


fun prove_lens_goal tname thy ctx =
  auto_tac (fold Simplifier.add_simp (Global_Theory.get_thms thy lens_defsN @ 
                           Global_Theory.get_thms thy (tname ^ splits_suffix) @ 
                           [@{thm prod.case_eq_if}]) ctx)

fun prove_indep tname thy = 
  (fn {context, prems = _} =>
          EVERY [auto_tac (Simplifier.add_simp @{thm lens_indep_vwb_iff} context)
                ,prove_lens_goal tname thy context])

fun prove_sublens tname thy = 
  (fn {context, prems = _} =>
          EVERY [auto_tac (Simplifier.add_simp @{thm sublens_iff_sublens'} context)
                ,prove_lens_goal tname thy context])

fun prove_quotient tname thy = 
  (fn {context, prems = _} =>
          EVERY [prove_lens_goal tname thy context])

fun prove_equiv tname thy = 
  (fn {context, prems = _} =>
          EVERY [auto_tac (Simplifier.add_simp @{thm lens_equiv_iff_lens_equiv'} context)
                ,prove_lens_goal tname thy context])

 
(* Construct a proof that base + more is a bijective lens *)

fun lens_bij_proof tname thy =
  Goal.prove_global thy [] []
    (hd (Type_Infer_Context.infer_types
            (Proof_Context.init_global thy)
            [ Const (Trueprop, dummyT)
            $ (Syntax.const Lens_Lib.bij_lensN $ 
              (Syntax.const Lens_Lib.lens_plusN $ Syntax.const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ base_lensN)
                                  $ Syntax.const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ child_lensN)))]))
    (fn {context = context, prems = _}
                         => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                                  , auto_tac (fold Simplifier.add_simp (Global_Theory.get_thms thy lens_defsN @ [@{thm prod.case_eq_if}])
                                                                       context)])

(* Construct a theorem and proof that two lenses, x and y, are independent. Since some lenses exist
   both with the source type as the record extension, and in the context of the extended record
   we need two versions of this function. The first shows it for the lenses on the extension, and
   thus uses an "intro_locales" as a means to discharge the individual lens laws of the vwb_lens
   locale. *)

fun indep_proof tname thy (x, y) =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [Lens_Lib.mk_indep
                (Syntax.const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x))
                (Syntax.const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ y))
              ]))
      (prove_indep tname thy)

fun equiv_one_proof tname thy fs =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (Lens_Lib.lens_equivN, dummyT)
                $ Const (Lens_Lib.id_lensN, dummyT)
                $ foldr1 (fn (x, y) => Const (Lens_Lib.lens_plusN, dummyT) $ x $ y) 
                         (map (fn n => Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ n, dummyT)) (fs @ [child_lensN]))
                )]))
      (prove_equiv tname thy)


fun equiv_more_proof tname pname thy fs =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (Lens_Lib.lens_equivN, dummyT)
                $ Const (pname ^ "." ^ child_lensN, dummyT)
                $ foldr1 (fn (x, y) => Const (Lens_Lib.lens_plusN, dummyT) $ x $ y) 
                         (map (fn n => Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ n, dummyT)) (fs @ [child_lensN]))
                )]))
      (prove_equiv tname thy)

fun equiv_base_proof tname parent thy fs =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (Lens_Lib.lens_equivN, dummyT)
                $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                $ foldr1 (fn (x, y) => Const (Lens_Lib.lens_plusN, dummyT) $ x $ y) 
                         ((case parent of NONE => [] | SOME (_, pname) => [Const (pname ^ "." ^ base_lensN, dummyT)]) @ 
                          map (fn n => Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ n, dummyT)) fs)
                )]))
      (prove_equiv tname thy)

fun lenses_bij_proof tname parent thy fs =
  Goal.prove_global thy [] []
    (hd (Type_Infer_Context.infer_types
            (Proof_Context.init_global thy)
            [ Const (Trueprop, dummyT)
            $ (Syntax.const Lens_Lib.bij_lensN $ 
              (foldr1 (fn (x, y) => Const (Lens_Lib.lens_plusN, dummyT) $ x $ y) 
                        ((case parent of NONE => [] | SOME (_, pname) => [Const (pname ^ "." ^ base_lensN, dummyT)]) @ 
                          map (fn n => Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ n, dummyT)) (fs @ [child_lensN]))))
                                    ]))
    (fn {context = context, prems = _}
                         => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                                  , auto_tac (fold Simplifier.add_simp (Global_Theory.get_thms thy lens_defsN @ [@{thm prod.case_eq_if}])
                                                                       context)])


fun equiv_partition_proof tname thy =
  Goal.prove_global thy [] []
    (hd (Type_Infer_Context.infer_types
            (Proof_Context.init_global thy)
            [ Const (Trueprop, dummyT)
            $ ( Const (Lens_Lib.lens_equivN, dummyT)
              $ ( Const (Lens_Lib.lens_plusN, dummyT) 
                $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ child_lensN, dummyT))
              $ Const (Lens_Lib.id_lensN, dummyT)
              )]))
    (prove_equiv tname thy)


(* Prove a theorem that every child lens is a sublens of the parent. *)

fun sublens_proof tname pname thy y x =
  Goal.prove_global thy [] []
    (hd (Type_Infer_Context.infer_types
            (Proof_Context.init_global thy)
            [ Const (Trueprop, dummyT)
            $ ( Const (Lens_Lib.sublensN, dummyT)
              $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
              $ Const (pname ^ "." ^ y, dummyT)
              )]))
    (prove_sublens tname thy)

fun quotient_proof tname thy x =
  Goal.prove_global thy [] []
    (hd (Type_Infer_Context.infer_types
            (Proof_Context.init_global thy)
            [ Const (Trueprop, dummyT)
            $ ( Const (HOLeq, dummyT)
              $ (Const (Lens_Lib.lens_quotientN, dummyT) 
                 $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                 $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                )
              $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
              )]))
    (prove_quotient tname thy)

fun composition_proof tname thy x =
  Goal.prove_global thy [] []
    (hd (Type_Infer_Context.infer_types
            (Proof_Context.init_global thy)
            [ Const (Trueprop, dummyT)
            $ ( Const (HOLeq, dummyT)
              $ (Const (Lens_Lib.lens_compN, dummyT) 
                 $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                 $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                )
              $ Const (Context.theory_base_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
              )]))
    (prove_quotient tname thy)


(* Finally we have the function that actually constructs the record, lenses for each field,
   independence proofs, and also sublens proofs. *)

fun add_alphabet (params, binding) raw_parent ty_fields thy =
  let
    val tname = Binding.name_of binding
    val fields = map (fn (x, y, z) => (Binding.suffix_name Lens_Lib.lens_suffix x, y, z)) ty_fields
    val lnames = map (fn (x, _, _) => Binding.name_of x) ty_fields
    val (parent, _) = read_parent raw_parent (Proof_Context.init_global thy);
    fun ldef x = (x, x ^ " = " ^ FLDLENS ^ " " ^ x ^ Lens_Lib.lens_suffix)
    val pname = case parent of SOME (_,r) => r | NONE => "";
    val plchild =
      case raw_parent of
        SOME _ => child_lensN |
        NONE => ""
    val plchilds =
      case raw_parent of
        SOME _ => [child_lensN] |
        NONE => []
    val bldef = (base_lensN, base_lensN ^ " = " ^ BASELENS ^ " " ^ tname);
    val mldef = (child_lensN, child_lensN ^ " = " ^ FLDLENS ^ " more"); 
    val sldef = (all_lensN, all_lensN ^ " \<equiv> \<lparr> " ^ slens_view ^ " = " ^ base_lensN ^ ", " ^ slens_coview ^ " = " ^ child_lensN ^ " \<rparr>");
    val plnames = if (raw_parent = NONE) then [] else lnames @ [child_lensN];
    fun pindeps thy = map (fn thm => @{thm sublens_pres_indep} OF [thm]) (Global_Theory.get_thms thy Lens_Lib.sublensesN)
                    @ map (fn thm => @{thm sublens_pres_indep'} OF [thm]) (Global_Theory.get_thms thy Lens_Lib.sublensesN)
    val attrs = map (Attrib.attribute (Named_Target.theory_init thy)) @{attributes [simp, code_unfold, lens]}
 in thy     (* Add a new record for the new alphabet lenses *)
         |> add_record_cmd {overloaded = false} (params, binding) raw_parent fields
            (* Add the record definition theorems to lens_defs *)
         |> Named_Target.theory_map (snd o Specification.theorems_cmd "" [((Binding.empty, []), [(Facts.named (tname ^ defs_suffix), snd lens_defs)])] [] false)
            (* Add the record splitting theorems to the alpha_splits set for proof automation *)
         |> Named_Target.theory_map (snd o Specification.theorems_cmd "" [((Binding.empty, []), [(Facts.named (tname ^ splits_suffix), alpha_splits)])] [] false)
            (* Reorder parent splitting theorems, so the child ones have higher priority *)
         |> (fn thy => 
             let 
                 (* Get the splitting theorems of all parents in reverse order *)
                 val psplits = List.concat (map (#splits o Record.the_info thy) ((map snd (get_parents thy (Context.theory_base_name thy ^ "." ^ tname)))))
                 (* Remove the splitting theorems *)
                 val thy1 = Context.theory_map (fold (Named_Theorems.del_thm "Lens_Instances.alpha_splits") psplits) thy
                 (* Add them again, so they have lower priority than the child splitting theorems *)
                 val thy2 = Context.theory_map (fold (Named_Theorems.add_thm "Lens_Instances.alpha_splits") psplits) thy1
             in thy2 end)
            (* Add definitions for each of the lenses corresponding to each record field in-situ *)
         |> Sign.qualified_path false binding
         |> Named_Target.theory_map
              (fold (fn (n, d) => snd o Specification.definition_cmd (SOME (Binding.make (n, Position.none), NONE, NoSyn)) [] [] (lens_defs, d) true) (map ldef lnames @ [bldef, mldef]))
            (* Add definition of the underlying symmetric lens *)
         |> Named_Target.theory_map
              (fold (fn (n, d) => Specification.abbreviation_cmd Syntax.mode_default (SOME (Binding.make (n, Position.none), NONE, NoSyn)) [] d true) [sldef])
            (* Add a vwb lens proof for each field lens *)
         |> fold (fn x => fn thy => snd (Global_Theory.add_thm ((Binding.make (x ^ vwb_lens_suffix, Position.none), lens_proof tname x thy), attrs) thy)) (lnames @ [base_lensN, child_lensN])
            (* Add a bij lens proof for the base and more lenses *)                                                              
         |> (fn thy => snd (Global_Theory.add_thm ((Binding.make (base_moreN ^ bij_lens_suffix, Position.none), lens_bij_proof tname thy), attrs) thy))
            (* Add a bij lens proof for the summation of all constituent lenses and the more lens *)
         |> (fn thy => if raw_parent = NONE then snd (Global_Theory.add_thm ((Binding.make (bij_lensesN, Position.none), lenses_bij_proof tname parent thy lnames), attrs) thy) else thy)
            (* Add sublens proofs *)
         |> (fn thy => snd (Global_Theory.add_thmss [((Binding.make (Lens_Lib.sublensesN, Position.none), map (sublens_proof tname pname thy plchild) plnames @ map (sublens_proof tname (Context.theory_base_name thy ^ "." ^ tname) thy base_lensN) lnames), attrs)] thy))
            (* Add quotient proofs *)                                                                                             
         |> (fn thy => snd (Global_Theory.add_thmss [((Binding.make (Lens_Lib.quotientsN, Position.none), map (quotient_proof tname thy) lnames), attrs)] thy))
            (* Add composition proofs *)
         |> (fn thy => snd (Global_Theory.add_thmss [((Binding.make (Lens_Lib.compositionsN, Position.none), map (composition_proof tname thy) lnames), attrs)] thy))
            (* Add independence proofs for each pairing of lenses *)
         |> (fn thy => snd (Global_Theory.add_thmss
              [((Binding.make (Lens_Lib.indepsN, Position.none), map (indep_proof tname thy) (Lens_Lib.pairings (lnames @ [child_lensN]) @ Lens_Lib.pairings [base_lensN, child_lensN]) (*@ map (parent_indep_proof_1 tname pname thy plchild) plnames @ map (parent_indep_proof_2 tname pname thy plchild) plnames *) @ pindeps thy), attrs)] thy))
            (* Add equivalence properties *)
         |> (fn thy => snd (Global_Theory.add_thmss
              [((Binding.make (equivN, Position.none), (if (raw_parent = NONE) then [equiv_one_proof tname thy lnames] else [equiv_more_proof tname pname thy lnames]) @ [equiv_base_proof tname parent thy lnames, equiv_partition_proof tname thy]), attrs)] thy))
            (* Add a symmetric lens proof for the base and more lenses *)
         |> (fn thy => snd (Global_Theory.add_thm ((Binding.make (all_lensN ^ sym_lens_suffix, Position.none), lens_sym_proof tname thy), attrs) thy)) 
         |> Sign.parent_path
  end;


fun add_alphabet_cmd (raw_params, binding) raw_parent raw_fields thy =
  let val ctx = (Proof_Context.init_global thy)
      val params = map (apsnd (Typedecl.read_constraint ctx)) raw_params;
      val ctx1 = fold (Variable.declare_typ o TFree) params ctx;
      val ty_fields = map (fn (x, y, z) => (x, Syntax.read_typ ctx1 y, z)) raw_fields
  in add_alphabet (params, binding) raw_parent ty_fields thy
  end

fun remove_lens_suffixes i st =
  let
    val (_, _, Bi, _) = Thm.dest_state (st, i);
    val params = (map #1 (Logic.strip_params Bi))
    val params' = 
      map Lens_Lib.remove_lens_suffix params ;
  in if params = params' then Seq.empty else Seq.single (Thm.rename_params_rule (params', i) st)
  end;

val rename_alpha_vars = ALLGOALS (fn i => PRIMSEQ (remove_lens_suffixes i));

val _ =
  Outer_Syntax.command @{command_keyword alphabet} "define record with lenses"
    ((Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding)
    >> (fn (x, (y, z)) =>
        Toplevel.theory (add_alphabet_cmd x y z)));
end