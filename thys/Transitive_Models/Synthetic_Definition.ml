val $` = curry ((op $) o swap)
infix $`

infix 6 &&&
val op &&& = Utils.&&&

infix 6 ***
val op *** = Utils.***

fun arity_goal intermediate def_name lthy =
  let
    val thm = Proof_Context.get_thm lthy (def_name ^ "_def")
    val (_, tm, _) = Utils.thm_concl_tm lthy (def_name ^ "_def")
    val (def, tm) = tm |> Utils.dest_eq_tms'
    fun first_lambdas (Abs (body as (_, ty, _))) =
        if ty = @{typ "i"}
          then (op ::) (Utils.dest_abs body |>> Utils.var_i ||> first_lambdas)
          else Utils.dest_abs body |> first_lambdas o #2
      | first_lambdas _ = []
    val (def, vars) = Term.strip_comb def
    val vs = vars @ first_lambdas tm
    val def = fold (op $`) vs def
    val hyps = map (fn v => Utils.mem_ v Utils.nat_ |> Utils.tp) vs
    val concl = @{const IFOL.eq(i)} $ (@{const arity} $ def) $ Var (("ar", 0), @{typ "i"})
    val g_iff = Logic.list_implies (hyps, Utils.tp concl)
    val attribs = if intermediate then [] else @{attributes [arity]}
  in
    (g_iff, "arity_" ^ def_name ^ (if intermediate then "'" else ""), attribs, thm, vs)
  end

fun manual_arity intermediate def_name pos lthy =
  let
    val (goal, thm_name, attribs, _, _) = arity_goal intermediate def_name lthy
  in
    Proof.theorem NONE (fn thmss => Utils.display "theorem" pos
                                    o Local_Theory.note ((Binding.name thm_name, attribs), hd thmss))
    [[(goal, [])]] lthy
  end

fun prove_arity thms goal ctxt =
  let
    val rules = (Named_Theorems.get ctxt \<^named_theorems>\<open>arity\<close>) @
      (Named_Theorems.get ctxt \<^named_theorems>\<open>arity_aux\<close>)
  in
    Goal.prove ctxt [] [] goal
    (K (rewrite_goal_tac ctxt thms 1 THEN Method.insert_tac ctxt rules 1 THEN asm_simp_tac ctxt 1))
  end

fun auto_arity intermediate def_name pos lthy =
  let
    val (goal, thm_name, attribs, def_thm, vs) = arity_goal intermediate def_name lthy
    val intermediate_text = if intermediate then "intermediate" else ""
    val help = "You can manually prove the arity_theorem by typing:\n"
             ^ "manual_arity " ^ intermediate_text ^ " for \"" ^ def_name ^ "\"\n"
    val thm = prove_arity [def_thm] goal lthy
              handle ERROR s => help ^ "\n\n" ^ s |> Exn.reraise o ERROR
    val thm = Utils.fix_vars thm (map Utils.freeName vs) lthy
  in
    Local_Theory.note ((Binding.name thm_name, attribs), [thm]) lthy |> Utils.display "theorem" pos
  end

fun prove_tc_form goal thms ctxt =
  Goal.prove ctxt [] [] goal (K (rewrite_goal_tac ctxt thms 1 THEN auto_tac ctxt))

fun prove_sats_tm thm_auto thms goal ctxt =
  let
    val ctxt' = ctxt |> Simplifier.add_simp (hd thm_auto)
  in
    Goal.prove ctxt [] [] goal
    (K (rewrite_goal_tac ctxt thms 1 THEN PARALLEL_ALLGOALS (asm_simp_tac ctxt')))
  end

fun prove_sats_iff goal ctxt = Goal.prove ctxt [] [] goal (K (asm_simp_tac ctxt 1))

fun is_mem (@{const mem} $ _ $  _) = true
  | is_mem _ = false

fun pre_synth_thm_sats term set env vars vs lthy =
  let
    val (_, tm, ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs, ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vs' = map (Thm.term_of o #2) vs
    val vars' = map (Thm.term_of o #2) vars
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vs'
    val sats = @{const apply} $ (@{const satisfies} $ set $ r_tm) $ env
    val sats' = @{const IFOL.eq(i)} $ sats $ (@{const succ} $ @{const zero})
  in
    { vars = vars'
    , vs = vs'
    , sats = sats'
    , thm_refs = thm_refs
    , lthy = ctxt2
    , env = env
    , set = set
    }
  end

fun synth_thm_sats_gen name lhs hyps pos attribs aux_funs environment lthy =
  let
    val ctxt = (#prepare_ctxt aux_funs) lthy
    val ctxt = Utils.add_to_context (Utils.freeName (#set environment)) ctxt
    val (new_vs, ctxt') = (#create_variables aux_funs) (#vs environment, ctxt)
    val new_hyps = (#create_hyps aux_funs) (#vs environment, new_vs)
    val concl = (#make_concl aux_funs) (lhs, #sats environment, new_vs)
    val g_iff = Logic.list_implies (new_hyps @ hyps, Utils.tp concl)
    val thm = (#prover aux_funs) g_iff ctxt'
    val thm = Utils.fix_vars thm (map Utils.freeName ((#vars environment) @ new_vs)) lthy
  in
    Local_Theory.note ((name, attribs), [thm]) lthy |> Utils.display "theorem" pos
  end

fun synth_thm_sats_iff def_name lhs hyps pos environment =
  let
    val subst = Utils.zip_with (I *** I) (#vs environment)
    fun subst_nth (@{const "nth"} $ v $ _) new_vs = AList.lookup (op =) (subst new_vs) v |> the
      | subst_nth (t1 $ t2) new_vs = (subst_nth t1 new_vs) $ (subst_nth t2 new_vs)
      | subst_nth (Abs (v, ty, t)) new_vs = Abs (v, ty, subst_nth t new_vs)
      | subst_nth t _ = t
    val name = Binding.name (def_name ^ "_iff_sats")
    val iff_sats_attrib = @{attributes [iff_sats]}
    val aux_funs = { prepare_ctxt = fold Utils.add_to_context (map Utils.freeName (#vs environment))
                   , create_variables = fn (vs, ctxt) => Variable.variant_fixes (map Utils.freeName vs) ctxt |>> map Utils.var_i
                   , create_hyps = fn (vs, new_vs) => Utils.zip_with (fn (v, nv) => Utils.eq_ (Utils.nth_ v (#env environment)) nv) vs new_vs |> map Utils.tp
                   , make_concl = fn (lhs, rhs, new_vs) => @{const IFOL.iff} $ (subst_nth lhs new_vs) $ rhs
                   , prover = prove_sats_iff
                   }
  in
    synth_thm_sats_gen name lhs hyps pos iff_sats_attrib aux_funs environment
  end

fun synth_thm_sats_fm def_name lhs hyps pos thm_auto environment =
  let
    val name = Binding.name ("sats_" ^ def_name ^ "_fm")
    val simp_attrib = @{attributes [simp]}
    val aux_funs = { prepare_ctxt = I
                   , create_variables = K [] *** I
                   , create_hyps = K []
                   , make_concl = fn (rhs, lhs, _) => @{const IFOL.iff} $ lhs $ rhs
                   , prover = prove_sats_tm thm_auto (#thm_refs environment)
                   }
  in
    synth_thm_sats_gen name lhs hyps pos simp_attrib aux_funs environment
  end

fun synth_thm_tc def_name term hyps vars pos lthy =
  let
    val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vars' = map (Thm.term_of o #2) vars
    val tc_attrib = @{attributes [TC]}
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vars'
    val concl = @{const mem} $ r_tm $ @{const formula}
    val g = Logic.list_implies(hyps, Utils.tp concl)
    val thm = prove_tc_form g thm_refs ctxt2
    val name = Binding.name (def_name ^ "_fm_type")
    val thm = Utils.fix_vars thm (map Utils.freeName vars') ctxt2
  in
    Local_Theory.note ((name, tc_attrib), [thm]) lthy |> Utils.display "theorem" pos
  end

fun synthetic_def def_name thm_ref pos tc auto thy =
  let
    val thm = Proof_Context.get_thm thy thm_ref
    val thm_vars = rev (Term.add_vars (Thm.full_prop_of thm) [])
    val (((_,inst),thm_tms),_) = Variable.import true [thm] thy
    val vars = map (fn v => (v, the (Vars.lookup inst v))) thm_vars
    val (tm,hyps) = thm_tms |> hd |> Thm.concl_of &&& Thm.prems_of
    val (lhs,rhs) = tm |> Utils.dest_iff_tms o Utils.dest_trueprop
    val ((set,t),env) = rhs |> Utils.dest_sats_frm
    fun relevant ts (@{const mem} $ t $ _) =
          (not (t = @{term "0"})) andalso
          (not (Term.is_Free t) orelse member (op =) ts (t |> Term.dest_Free |> #1))
      | relevant _ _ = false
    val t_vars = sort_strings (Term.add_free_names t [])
    val vs = filter (Ord_List.member String.compare t_vars o #1 o #1 o #1) vars
    val at = fold_rev (lambda o Thm.term_of o #2) vs t
    val hyps' = filter (relevant t_vars o Utils.dest_trueprop) hyps
    val def_attrs = @{attributes [fm_definitions]}
  in
    Local_Theory.define ((Binding.name (def_name ^ "_fm"), NoSyn),
                        ((Binding.name (def_name ^ "_fm_def"), def_attrs), at)) thy
    |>> (#2 #> I *** single) |> Utils.display "theorem" pos |>
    (if tc then synth_thm_tc def_name (def_name ^ "_fm_def") hyps' vs pos else I) |>
    (if auto then
      pre_synth_thm_sats (def_name ^ "_fm_def") set env vars vs
      #> I &&& #lthy
      #> #1 &&& uncurry (synth_thm_sats_fm def_name lhs hyps pos thm_tms)
      #> uncurry (synth_thm_sats_iff def_name lhs hyps pos)
    else I)
  end

fun prove_schematic thms goal ctxt =
  let
    val rules = Named_Theorems.get ctxt \<^named_theorems>\<open>iff_sats\<close>
  in
    Goal.prove ctxt [] [] goal
    (K (rewrite_goal_tac ctxt thms 1 THEN REPEAT1 (CHANGED (resolve_tac ctxt rules 1 ORELSE asm_simp_tac ctxt 1))))
  end

val valid_assumptions = [ ("nonempty", Utils.mem_ @{term "0"})
                        ]

fun pre_schematic_def target assuming lthy =
let
    val thm = Proof_Context.get_thm lthy (target ^ "_def")
    val (vars, tm, ctxt1) = Utils.thm_concl_tm lthy (target ^ "_def")
    val (const, tm) = tm |> Utils.dest_eq_tms' o Utils.dest_trueprop |>> #1 o strip_comb
    val t_vars = sort_strings (Term.add_free_names tm [])
    val vs = List.filter (#1 #> #1 #> #1 #> Ord_List.member String.compare t_vars) vars
             |> List.filter ((curry op = @{typ "i"}) o #2 o #1)
             |> List.map (Utils.var_i o #1 o #1 o #1)
    fun first_lambdas (Abs (body as (_, ty, _))) =
        if ty = @{typ "i"}
          then (op ::) (Utils.dest_abs body |>> Utils.var_i ||> first_lambdas)
          else Utils.dest_abs body |> first_lambdas o #2
      | first_lambdas _ = []
    val vs = vs @ (first_lambdas tm)
    val ctxt1' = fold Utils.add_to_context (map Utils.freeName vs) ctxt1
    val (set, ctxt2) = Variable.variant_fixes ["A"] ctxt1' |>> Utils.var_i o hd
    val class = @{const "setclass"} $ set
    val (env, ctxt3) = Variable.variant_fixes ["env"] ctxt2 |>> Utils.var_i o hd
    val assumptions = filter (member (op =) assuming o #1) valid_assumptions |> map #2
    val hyps = (List.map (fn v => Utils.tp (Utils.mem_ v Utils.nat_)) vs)
               @ [Utils.tp (Utils.mem_ env (Utils.list_ set))]
               @ Utils.zip_with (fn (f,x) => Utils.tp (f x)) assumptions (replicate (length assumptions) set)
    val args = class :: map (fn v => Utils.nth_ v env) vs
    val (fm_name, ctxt4) = Variable.variant_fixes ["fm"] ctxt3 |>> hd
    val fm_type = fold (K (fn acc => Type ("fun", [@{typ "i"}, acc]))) vs @{typ "i"}
    val fm = Var ((fm_name, 0), fm_type)
    val lhs = fold (op $`) args const
    val fm_app = fold (op $`) vs fm
    val sats = @{const apply} $ (@{const satisfies} $ set $ fm_app) $ env
    val rhs = @{const IFOL.eq(i)} $ sats $ (@{const succ} $ @{const zero})
    val concl = @{const "IFOL.iff"} $ lhs $ rhs
    val schematic = Logic.list_implies (hyps, Utils.tp concl)
  in
    (schematic, ctxt4, thm, set, env, vs)
  end

fun str_join _ [] = ""
  | str_join _ [s] = s
  | str_join c (s :: ss) = s ^ c ^ (str_join c ss)

fun schematic_def def_name target assuming pos lthy =
  let
    val (schematic, ctxt, thm, set, env, vs) = pre_schematic_def target assuming lthy
    val assuming_text = if null assuming then "" else "assuming " ^ (map (fn s => "\"" ^ s ^ "\"") assuming |> str_join " ")
    val help = "You can manually prove the schematic_goal by typing:\n"
             ^ "manual_schematic [sch_name] for \"" ^ target ^ "\"" ^ assuming_text ^"\n"
             ^ "And then complete the synthesis with:\n"
             ^ "synthesize \"" ^ target ^ "\" from_schematic [sch_name]\n"
             ^ "In both commands, \<guillemotleft>sch_name\<guillemotright> must be the same and, if ommited, will be defaulted to sats_" ^ target ^ "_fm_auto.\n"
             ^ "You can also try adding new assumptions and/or synthetizing definitions of sub-terms."
    val thm = prove_schematic [thm] schematic ctxt
              handle ERROR s => help ^ "\n\n" ^ s |> Exn.reraise o ERROR
    val thm = Utils.fix_vars thm (map Utils.freeName (set :: env :: vs)) lthy
  in
    Local_Theory.note ((Binding.name def_name, []), [thm]) lthy |> Utils.display "theorem" pos
  end

fun schematic_synthetic_def def_name target assuming pos tc auto =
    (synthetic_def def_name ("sats_" ^ def_name ^ "_fm_auto") pos tc auto)
    o (schematic_def ("sats_" ^ def_name ^ "_fm_auto") target assuming pos)

fun manual_schematic def_name target assuming pos lthy =
  let
    val (schematic, _, _, _, _, _) = pre_schematic_def target assuming lthy
  in
    Proof.theorem NONE (fn thmss => Utils.display "theorem" pos
                                    o Local_Theory.note ((Binding.name def_name, []), hd thmss))
    [[(schematic, [])]] lthy
  end

local
  val simple_from_schematic_synth_constdecl =
       Parse.string --| (Parse.$$$ "from_schematic")
       >> (fn bndg => synthetic_def bndg ("sats_" ^ bndg ^ "_fm_auto"))

  val full_from_schematic_synth_constdecl =
       Parse.string -- ((Parse.$$$ "from_schematic" |-- Parse.thm))
       >> (fn (bndg,thm) => synthetic_def bndg (#1 (thm |>> Facts.ref_name)))

  val full_from_definition_synth_constdecl =
       Parse.string -- ((Parse.$$$ "from_definition" |-- Parse.string)) -- (Scan.optional (Parse.$$$ "assuming" |-- Scan.repeat Parse.string) [])
       >> (fn ((bndg,target), assuming) => schematic_synthetic_def bndg target assuming)

  val simple_from_definition_synth_constdecl =
     Parse.string -- (Parse.$$$ "from_definition" |-- (Scan.optional (Parse.$$$ "assuming" |-- Scan.repeat Parse.string)) [])
     >> (fn (bndg, assuming) => schematic_synthetic_def bndg bndg assuming)

  val synth_constdecl =
       Parse.position (full_from_schematic_synth_constdecl || simple_from_schematic_synth_constdecl
                       || full_from_definition_synth_constdecl
                       || simple_from_definition_synth_constdecl)

  val full_schematic_decl =
       Parse.string -- ((Parse.$$$ "for" |-- Parse.string)) -- (Scan.optional (Parse.$$$ "assuming" |-- Scan.repeat Parse.string) [])

  val simple_schematic_decl =
       (Parse.$$$ "for" |-- Parse.string >> (fn name => "sats_" ^ name ^ "_fm_auto") &&& I) -- (Scan.optional (Parse.$$$ "assuming" |-- Scan.repeat Parse.string) [])

  val schematic_decl = Parse.position (full_schematic_decl || simple_schematic_decl)

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn (f,p) => f p true true))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize_notc\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn (f,p) => f p false false))

  val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>generate_schematic\<close> "ML setup for schematic goals"
       (schematic_decl >> (fn (((bndg,target), assuming),p) => schematic_def bndg target assuming p))

  val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>manual_schematic\<close> "ML setup for schematic goals"
       (schematic_decl >> (fn (((bndg,target), assuming),p) => manual_schematic bndg target assuming p))

  val arity_parser = Parse.position ((Scan.option (Parse.$$$ "intermediate") >> is_some) -- (Parse.$$$ "for" |-- Parse.string))

  val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>manual_arity\<close> "ML setup for arities"
       (arity_parser >> (fn ((intermediate, target), pos) => manual_arity intermediate target pos))

  val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>arity_theorem\<close> "ML setup for arities"
       (arity_parser >> (fn ((intermediate, target), pos) => auto_arity intermediate target pos))

in

end