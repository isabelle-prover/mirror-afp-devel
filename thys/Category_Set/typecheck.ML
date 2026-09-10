(* check_cfunc determines if a given term is of type cfunc *)
fun check_cfunc binder_typs (t : term) = 
    case fastype_of1 (binder_typs, t) of
      Type (name, []) => (name = "Cfunc.cfunc") andalso not (loose_bvar (t, 0)) (* reject invalid terms with loose bvars *)
    | _ => false

(* find_cfunc_terms finds all the subterms of type cfunc in a term and returns them as a list *)
fun find_cfunc_terms binder_typs (a $ b) =
        (if check_cfunc binder_typs (a $ b) then [(a $ b)] else []) 
          @ find_cfunc_terms binder_typs a @ find_cfunc_terms binder_typs b
    | find_cfunc_terms binder_typs (Abs (n, typ, t)) =
        (if check_cfunc binder_typs (Abs (n, typ, t)) then [(Abs (n, typ, t))] else []) 
          @ find_cfunc_terms (typ::binder_typs) t 
    | find_cfunc_terms binder_typs t = if check_cfunc binder_typs t then [t] else []

(* match_term attempts to unify a term against a pattern, 
  returning a list of instantiations and a boolean indicating success *)
fun match_term bound_typs pat t = 
        let fun match_term' bound_typs (pat1 $ pat2) (t1 $ t2) =
                let val (matches1, success1) = match_term' bound_typs pat1 t1
                    val (matches2, success2) = match_term' bound_typs pat2 t2
                in (matches1 @ matches2, success1 andalso success2)
                end
            | match_term' bound_typs (Abs (_, patty, pat)) (Abs (_, ty, t)) =
                let val (matches, success) = match_term' (ty::bound_typs) pat t
                in (matches, success andalso patty = ty)
                end
            | match_term' bound_typs (Var (var, patty)) t =
                if fastype_of1 (bound_typs, t) = patty then ([(var, t)], true) else ([], false)
            | match_term' _ pat t = ([], pat aconv t)
            val (matches, success) = match_term' bound_typs pat t
        in if success then SOME matches else NONE
        end

(* extract_type_rule_term extracts the term f of type cfunc from a theorem of the form f : X \<rightarrow> Y *)
fun extract_type_rule_term rule =
          case Thm.concl_of rule of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("Cfunc.cfunc_type", _) $ t) $ _ $ _ => SOME t
              | _ => NONE)
          | _ => NONE

(* certify_instantiations lifts a list of term instantiations to a list of certified term instantiations *)
fun certify_instantiations ctxt bound_typs = 
      List.map (fn (x : indexname, t) => ((x, fastype_of1 (bound_typs, t)), Thm.cterm_of ctxt t))

(* match_type_rule checks if a given type rule is applicable to a given term,
  returning an instantiated version of the rule if it is *)
fun match_type_rule ctxt bound_typs t rule = 
          let val opt_insts =
                case extract_type_rule_term rule of
                  SOME pat => match_term bound_typs pat t
                | NONE => NONE
              val opt_insts' = Option.map (certify_instantiations ctxt bound_typs) opt_insts
          in case opt_insts' of
              SOME insts => SOME (Thm.instantiate (TVars.empty, Vars.make insts) rule)
            | NONE => NONE
          end

fun is_type_rule_term t =
          case Logic.strip_imp_concl t of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("Cfunc.cfunc_type", _) $ _) $ _ $ _ => true
              | _ => false)
          | _ => false

fun is_type_rule thm = is_type_rule_term (Thm.concl_of thm)

(* find_type_rule searches a list of type rules, attempting to match each in turn *)
fun find_type_rule _ _ _ [] = NONE (* no typing rules left *)
      | find_type_rule ctxt bound_typs t (rule::rules) =
          case match_type_rule ctxt bound_typs t rule of
            SOME rule' => SOME rule'
          | NONE => find_type_rule ctxt bound_typs t rules

(* elim_type_rule_prem attempts to eliminate a premise of a type rule by applying a lemma from a supplied list *)
fun elim_type_rule_prem _ _ _ [] = NONE (* no lemmas match the premise *)
      | elim_type_rule_prem ctxt thm prem (lem::lems) = 
          case match_term [] prem (Thm.prop_of lem) of
            SOME insts => 
              let val insts' = certify_instantiations ctxt [] insts
                  val inst_thm = Thm.instantiate (TVars.empty, Vars.make insts') thm
              in SOME (Thm.implies_elim inst_thm lem)
              end
          | NONE => elim_type_rule_prem ctxt thm prem lems

(* elim_type_rule_prems attempts to eliminate all premises of a type rule by applying lemmas from a supplied list,
  leaving those premises that cannot be eliminated *)
fun elim_type_rule_prems ctxt thm lems =
          let fun elim_type_rule_prems' thm [] = thm
                | elim_type_rule_prems' thm (prem::prems) =
                    case elim_type_rule_prem ctxt thm prem lems of
                      SOME thm' => elim_type_rule_prems' thm' prems
                    | NONE => (* can't eliminate premise, shift it to the back and continue *)
                        elim_type_rule_prems' (Thm.permute_prems 0 1 thm) prems
          in elim_type_rule_prems' thm (Thm.prems_of thm)
          end

fun elim_type_rule_prems_opt ctxt thm lems =
          let fun elim_type_rule_prems' thm [] = SOME thm
                | elim_type_rule_prems' thm (prem::prems) =
                    case elim_type_rule_prem ctxt thm prem lems of
                      SOME thm' => elim_type_rule_prems' thm' prems
                    | NONE => NONE
          in elim_type_rule_prems' thm (Thm.prems_of thm)
          end

(* variant that only eliminates type rules *)
fun elim_type_rule_prems_opt' ctxt thm lems =
          let fun elim_type_rule_prems' thm [] = SOME thm
                | elim_type_rule_prems' thm (prem::prems) =
                    case elim_type_rule_prem ctxt thm prem lems of
                      SOME thm' => elim_type_rule_prems' thm' prems
                    | NONE => if is_type_rule_term prem 
                              then NONE 
                              else (elim_type_rule_prems' (Thm.permute_prems 0 1 thm) prems)
          in elim_type_rule_prems' thm (Thm.prems_of thm)
          end

(* construct_cfunc_type_lemma attempts to construct a type lemma for a given term
  using a list of typing rules and a list of existing typing lemmas;
  the lemma is returned in a list, which is empty if no lemma can be constructed *)
fun construct_cfunc_type_lemma ctxt rules binder_typs lems t = 
          case find_type_rule ctxt binder_typs t rules of
            SOME rule => [elim_type_rule_prems ctxt rule (lems @ rules)]
          | NONE => []

(* construct_cfunc_type_lemmas1 constructs all the typing lemmas for a given term,
  taking a list of bound variable term types in to determine which terms are cfuncs *)
fun construct_cfunc_type_lemmas1 ctxt rules binder_typs (t $ u) =
          let val left_lems = construct_cfunc_type_lemmas1 ctxt rules binder_typs t
              val right_lems = construct_cfunc_type_lemmas1 ctxt rules binder_typs u
              val sublems = left_lems @ right_lems
              val this_lem = 
                if check_cfunc binder_typs (t $ u)
                then construct_cfunc_type_lemma ctxt rules binder_typs sublems (t $ u)
                else []
          in this_lem @ sublems
          end
      | construct_cfunc_type_lemmas1 ctxt rules binder_typs (Abs (n, typ, t)) =
          let val sublems = construct_cfunc_type_lemmas1 ctxt rules (typ::binder_typs) t
              val this_lem = if check_cfunc binder_typs (Abs (n, typ, t))
                then construct_cfunc_type_lemma ctxt rules binder_typs sublems (Abs (n, typ, t))
                else []
          in this_lem @ sublems
          end
      | construct_cfunc_type_lemmas1 ctxt rules binder_typs t =
          if check_cfunc binder_typs t then construct_cfunc_type_lemma ctxt rules binder_typs [] t else []

(* construct_cfunc_type_lemmas constructs all the typing lemmas for a given term,
  assuming there are no unbound bound variables *)
fun construct_cfunc_type_lemmas ctxt rules t = construct_cfunc_type_lemmas1 ctxt rules [] t

fun typecheck_cfunc ctxt rules t = 
      let val rules' = rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
          val lems = construct_cfunc_type_lemmas ctxt rules' t
      in hd lems
      end

(* extract_prems attempts to extract premises from a term that has the form of a theorem *)
fun extract_prems ((@{term Trueprop}) $ P) = extract_prems P
      | extract_prems (@{term "Pure.imp"} $ P $ Q) = P::extract_prems Q
      | extract_prems _ = []

(* typecheck_cfuncs_subproof implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the Subgoal.FOCUS combinator *)
fun typecheck_cfuncs_subproof ctxt type_rules subgoal n (focus : Subgoal.focus) = 
          let val type_rules' = type_rules @ (#prems focus) @ Named_Theorems.get ctxt "Cfunc.type_rule"
              val lems = construct_cfunc_type_lemmas ctxt type_rules' subgoal
          in Method.insert_tac ctxt lems n
          end

(* typecheck_cfuncs_subtac implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the SUBGOAL combinator *)
fun typecheck_cfuncs_subtac ctxt type_rules (subgoal, n) = 
          Subgoal.FOCUS (typecheck_cfuncs_subproof ctxt type_rules subgoal n) ctxt n
          THEN TRY (clarify_tac ctxt n)

(* typecheck_cfuncs_tac lifts typecheck_cfuncs_subproof to a tactic
  that generates cfunc type facts as assumptions of a specified goal *)
fun typecheck_cfuncs_tac ctxt type_rules =
  SUBGOAL (typecheck_cfuncs_subtac ctxt type_rules)

(* typecheck_cfuncs_method lifts typecheck_cfuncs_tac to a proof method that
  generates cfunc type facts for the first goal *)
fun typecheck_cfuncs_method opt_type_rules ctxt = 
      (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_tac ctxt (these opt_type_rules @ thms) 1))

(* typecheck_cfuncs_all_method lifts typecheck_cfuncs_tac to a proof method that
  generates cfunc type facts for the first goal *)
fun typecheck_cfuncs_all_method opt_type_rule ctxt = 
      CONTEXT_METHOD (fn thms => 
        CONTEXT_TACTIC (ALLGOALS (typecheck_cfuncs_tac ctxt (these opt_type_rule @ thms))))


(* typecheck_cfuncs_prems_subproof implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the Subgoal.FOCUS combinator *)
fun typecheck_cfuncs_prems_subproof ctxt assms _ n (focus : Subgoal.focus) = 
          let val type_rules' = assms @ (#prems focus) @ Named_Theorems.get ctxt "Cfunc.type_rule"
              val assms_to_typecheck = (filter (fn x => not (is_type_rule x)) assms)
              val prems_to_typecheck = (filter (fn x => not (is_type_rule x)) (#prems focus))
              val to_typecheck = assms_to_typecheck @ prems_to_typecheck
              val typecheck_func = fn x => construct_cfunc_type_lemmas ctxt type_rules' (Thm.prop_of x)
              val lems = flat (map typecheck_func to_typecheck)
          in Method.insert_tac ctxt lems n
          end

(* typecheck_cfuncs_prems_subtac implements a tactic that generates cfunc type facts as assumptions of a goal,
  in the right format to be passed to the SUBGOAL combinator *)
fun typecheck_cfuncs_prems_subtac ctxt type_rules (subgoal, n) = 
          Subgoal.FOCUS (typecheck_cfuncs_prems_subproof ctxt type_rules subgoal n) ctxt n
          THEN TRY (clarify_tac ctxt n)

(* typecheck_cfuncs_prems_tac lifts typecheck_cfuncs_subproof to a tactic
  that generates cfunc type facts as assumptions of a specified goal *)
fun typecheck_cfuncs_prems_tac ctxt type_rules =
  SUBGOAL (typecheck_cfuncs_prems_subtac ctxt type_rules)

(* typecheck_cfuncs_prems_method lifts typecheck_cfuncs_tac to a proof method that
  generates cfunc type facts for the first goal *)
fun typecheck_cfuncs_prems_method opt_type_rules ctxt = 
          (fn thms => CONTEXT_TACTIC (typecheck_cfuncs_prems_tac ctxt (these opt_type_rules @ thms) 1))

fun ETCS_resolve_subtac ctxt type_rules thm i (foc : Subgoal.focus) = 
      (* try to match the given theorem against the current subgoal*)
      case match_term [] (Thm.concl_of thm) (Thm.term_of (#concl foc)) of
        SOME insts =>
              (* certify any instantiations that result *)
          let val insts' = certify_instantiations ctxt [] insts
              (* instantiate the given theorem *)
              val inst_thm = Thm.instantiate (TVars.empty, Vars.make insts') thm
              (* generate typing lemmas and eliminate any typing premises required *)
              val type_lems =
                construct_cfunc_type_lemmas ctxt ((#prems foc) @ type_rules) (Thm.prop_of inst_thm)
              val inst_thm' = elim_type_rule_prems ctxt inst_thm type_lems
              (* generate typing lemmas for any remaining premises of the goal and try to eliminate them *)
              val prem_type_lems =
                flat (map (construct_cfunc_type_lemmas ctxt (type_rules)) (Thm.prems_of inst_thm'))
              val inst_thm'' = elim_type_rule_prems ctxt inst_thm' prem_type_lems
              (* look for unresolved type premises of the theorem *)
              val prems = Thm.prems_of inst_thm'';
              val type_prems = (filter (fn x => is_type_rule_term x) prems)
            (* resolve the current subgoal using the instantiated theorem *)
          in case type_prems of
               [] => resolve_tac ctxt [inst_thm''] i
             | _  => no_tac (* unresolved type premises, fail *)
          end
      | NONE => no_tac

fun ETCS_resolve_tac _    _          []          _ = all_tac
      | ETCS_resolve_tac ctxt type_rules (thm::thms) i = 
          (Subgoal.FOCUS (ETCS_resolve_subtac ctxt type_rules thm i) ctxt i)
            THEN ETCS_resolve_tac ctxt type_rules thms i

fun ETCS_resolve_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_resolve_tac ctxt (type_rules @ add_rules) thms 1)
      end

(* extract_subst_term extracts the term f of type cfunc from a theorem of the form "f = g" or "f \<equiv> g" *)
fun extract_subst_term rule =
          case Thm.concl_of rule of
            Const ("HOL.Trueprop", _) $ boolrule =>
              (case boolrule of 
                (Const ("HOL.eq", _) $ t) $ _ => SOME t
              | _ => NONE)
          | (Const ("Pure.eq", _) $ t) $ _ => SOME t
          | _ => NONE

(* match_nested_term tries to apply match_term over the structure of a term until it finds a match *)
fun match_nested_term bound_typs pat (t1 $ t2) = (
        (* try matching the toplevel first *)
        case match_term bound_typs pat (t1 $ t2) of
          SOME insts => SOME insts
        | NONE =>
            (* otherwise try matching in left of application *)
            case match_nested_term bound_typs pat t1 of
              SOME insts => SOME insts
              (* otherwise try matching in right of application *)
            | NONE => match_nested_term bound_typs pat t2
      )
    | match_nested_term bound_typs pat (Abs (v, ty, t)) = (
        (* try matching the toplevel first *)
        case match_term bound_typs pat (Abs (v, ty, t)) of
          SOME insts => SOME insts
          (* otherwise try matching quantified term *)
        | NONE => match_nested_term bound_typs pat t
      )
      (* finally, just try regular match *)
    | match_nested_term bound_typs pat t = match_term bound_typs pat t

fun instantiate_typecheck ctxt thm type_rules insts =
      let val cinsts = certify_instantiations ctxt [] insts
          val inst_thm = Thm.instantiate (TVars.empty, Vars.make cinsts) thm
          val gen_type_lems = construct_cfunc_type_lemmas ctxt type_rules
          val type_lems = flat (map (gen_type_lems o snd) insts)
      in elim_type_rule_prems_opt ctxt inst_thm type_lems
      end

fun instantiate_typecheck' ctxt thm type_rules insts =
      let val cinsts = certify_instantiations ctxt [] insts
          val inst_thm = Thm.instantiate (TVars.empty, Vars.make cinsts) thm
          val gen_type_lems = construct_cfunc_type_lemmas ctxt type_rules
          val type_lems = flat (map (gen_type_lems o snd) insts)
      in elim_type_rule_prems_opt' ctxt inst_thm type_lems
      end

(* match_nested_term_typecheck tries to apply match_term over the structure of a term until it finds
  a match that typechecks to leave no premises*)
fun match_nested_term_typecheck ctxt thm type_rules bound_typs pat (t1 $ t2) = (
        (* try matching the toplevel first and check if it passes typechecking *)
        case Option.mapPartial 
              (instantiate_typecheck ctxt thm type_rules)
              (match_term bound_typs pat (t1 $ t2)) of
          SOME inst_thm => SOME inst_thm
        | NONE =>
            (* otherwise try matching in left of application *)
            case match_nested_term_typecheck ctxt thm type_rules bound_typs pat t1 of
              SOME inst_thm => SOME inst_thm
              (* otherwise try matching in right of application *)
            | NONE => match_nested_term_typecheck ctxt thm type_rules bound_typs pat t2
      )
    | match_nested_term_typecheck ctxt thm type_rules bound_typs pat (Abs (v, ty, t)) = (
       (* try matching the toplevel first and check if it passes typechecking *)
        case Option.mapPartial 
              (instantiate_typecheck ctxt thm type_rules)
              (match_term bound_typs pat (Abs (v, ty, t))) of
          SOME inst_thm => SOME inst_thm
          (* otherwise try matching quantified term *)
        | NONE => match_nested_term_typecheck ctxt thm type_rules bound_typs pat t
      )
      (* finally, just try regular match and instantiate *)
    | match_nested_term_typecheck ctxt thm type_rules bound_typs pat t = 
        Option.mapPartial 
          (instantiate_typecheck ctxt thm type_rules)
          (match_term bound_typs pat t)

fun ETCS_subst_subtac ctxt type_rules thm i (foc : Subgoal.focus) =
          (* extract the left-hand side from the conclusion of the theorem *) 
      let val subst_term = extract_subst_term thm
          (* extract current subgoal *)
          val subgoal = (Thm.term_of (#concl foc))
          (* try to match the given theorem against the current subgoal*)
          val inst_thm_opt = case subst_term of
              SOME t => match_nested_term_typecheck ctxt thm ((#prems foc) @ type_rules) [] t subgoal
            | NONE   => NONE
      in 
        case inst_thm_opt of
          SOME inst_thm => EqSubst.eqsubst_tac ctxt [0] [inst_thm] i
          | NONE => no_tac
      end

fun ETCS_subst_tac _    _          []          _ = all_tac
      | ETCS_subst_tac ctxt type_rules (thm::thms) i = 
          (Subgoal.FOCUS (ETCS_subst_subtac ctxt type_rules thm i) ctxt i)
            THEN ETCS_subst_tac ctxt type_rules thms i

fun ETCS_subst_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_subst_tac ctxt (type_rules @ add_rules) thms 1)
      end

fun string_of_var (Const (str, _))    = str
      | string_of_var (Free (str, _))     = str
      | string_of_var (Var ((str, _), _)) = str
      | string_of_var _ = "" (*raise TERM ("string_of_var", [t])*)

fun ETCS_subst_asm_subtac type_rules thm i (foc : Subgoal.focus) =
          (* extract the left-hand side from the conclusion of the theorem *) 
          let val subst_term = (extract_subst_term thm)
          (* extract current subgoal *)
          val subgoal_prems = (#prems foc)
          val ctxt = (#context foc)
          (* try to match the given theorem against the current subgoal*)
          fun match_asm t (asm::asms) = 
              (* match_nested_term_typecheck ctxt thm type_rules bound_typs pat t *)
              (case match_nested_term_typecheck ctxt thm ((#prems foc) @ type_rules) [] t (Thm.prop_of asm) of
                SOME inst_thm => SOME (inst_thm, asm)
              | NONE => match_asm t asms)
            | match_asm _ [] = NONE;
          val inst_thm_opt = case subst_term of
              SOME t => match_asm t subgoal_prems
            | NONE   => NONE
          
      in 
        case inst_thm_opt of
          SOME (inst_thm, selected_prem) =>
                (* generalize selected premise for use outside of focus *)
            let val names_to_generalize = map (string_of_var o Thm.term_of o snd) (#params foc)
                val generalized_prem = Thm.generalize_cterm (Names.empty, Names.make_set names_to_generalize) 0 (Thm.cprop_of selected_prem)
                (* insert selected premise and substitute it using the instantiated theorem *)
            in ((cut_tac selected_prem i) THEN (EqSubst.eqsubst_asm_tac ctxt [0] [inst_thm] i),
                SOME generalized_prem)
            end
          | NONE => (no_tac, NONE)
      end

fun ETCS_subst_asm_tac _    _          []          _ goal = all_tac goal
      | ETCS_subst_asm_tac ctxt type_rules (thm::thms) i goal = 
          if Thm.nprems_of goal < i then Seq.empty
          else
            let val (foc as {context = ctxt', asms, params, ...}, goal') = Subgoal.focus ctxt i NONE goal
                val (inner_tac, selected_prem_opt) = ETCS_subst_asm_subtac type_rules thm i foc
                val tac1 = (Seq.lifts (Subgoal.retrofit ctxt' ctxt params asms i) (inner_tac goal'))
                val tac2 = case selected_prem_opt of
                  SOME selected_prem => 
                    let val match_prem = fn t => is_none (match_term [] (Thm.term_of selected_prem) t)
                        val remove_prem_tac = fn (foc : Subgoal.focus) => filter_prems_tac (#context foc) match_prem i
                    in (Subgoal.FOCUS_PARAMS remove_prem_tac ctxt i) THEN (Tactic.rotate_tac (0-1) i)
                    end
                | NONE => no_tac
            in (tac1 THEN tac2 THEN (ETCS_subst_asm_tac ctxt type_rules thms i)) goal
            end

fun ETCS_subst_asm_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_subst_asm_tac ctxt (type_rules @ add_rules) thms 1)
      end

fun ETCS_eresolve_subtac type_rules thm i (foc : Subgoal.focus) = 
      (* extract the first premise of the given theorem*)
      let val first_prem = try hd (Thm.prems_of thm)
          val subgoal_prems = (#prems foc)
          val ctxt = (#context foc)
          (* try to match the extracted premise against the current subgoal*)
          fun match_asm_inst t (asm::asms)= 
              (case Option.mapPartial
                  (instantiate_typecheck' ctxt thm ((#prems foc) @ type_rules)) 
                  (match_term [] t (Thm.prop_of asm)) of
                SOME thm => SOME (thm, asm)
              | NONE => match_asm_inst t asms)
            | match_asm_inst _ [] = NONE;
      in case Option.mapPartial (fn prem => match_asm_inst prem subgoal_prems) first_prem of
         SOME (inst_thm, selected_prem) =>
                (* generalize selected premise for use outside of focus *)
            let val names_to_generalize = map (string_of_var o Thm.term_of o snd) (#params foc)
                val generalized_prem = Thm.generalize_cterm (Names.empty, Names.make_set names_to_generalize) 0 (Thm.cprop_of selected_prem)
                (* insert selected premise and substitute it using the instantiated theorem *)
            in ((cut_tac selected_prem i) THEN (eresolve_tac ctxt [inst_thm] i),
                SOME generalized_prem)
            end
         | NONE => (no_tac, NONE)
               (*[] => eresolve_tac ctxt [inst_thm''] i*)
      end

fun ETCS_eresolve_tac _    _          []          _ goal = all_tac goal
      | ETCS_eresolve_tac ctxt type_rules (thm::thms) i goal = 
          if Thm.nprems_of goal < i then Seq.empty
          else
            let val (foc as {context = ctxt', asms, params, ...}, goal') = Subgoal.focus ctxt i NONE goal
                val (inner_tac, selected_prem_opt) = ETCS_eresolve_subtac type_rules thm i foc
                val tac1 = (Seq.lifts (Subgoal.retrofit ctxt' ctxt params asms i) (inner_tac goal'))
                val tac2 = case selected_prem_opt of
                  SOME selected_prem => 
                    let val match_prem = fn t => is_none (match_term [] (Thm.term_of selected_prem) t)
                        val remove_prem_tac = fn (foc : Subgoal.focus) => filter_prems_tac (#context foc) match_prem i
                    in (Subgoal.FOCUS_PARAMS remove_prem_tac ctxt i) THEN (Tactic.rotate_tac (0-1) i)
                    end
                | NONE => no_tac
            in (tac1 THEN tac2 THEN (ETCS_eresolve_tac ctxt type_rules thms i)) goal
            end

fun ETCS_eresolve_method (thms, opt_type_rules) ctxt =
      let val type_rules = these opt_type_rules @ Named_Theorems.get ctxt "Cfunc.type_rule"
      in METHOD (fn add_rules => ETCS_eresolve_tac ctxt (type_rules @ add_rules) thms 1)
      end