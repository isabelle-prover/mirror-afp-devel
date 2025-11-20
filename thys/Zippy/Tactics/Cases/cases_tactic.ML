(*  Title:      Zippy/cases_tactic.ML
    Author:     Kevin Kappelmann

Cases tactic supporting loose bvars and searching of subterms in the goal.
*)
signature CASES_TACTIC =
sig
  include HAS_LOGGER
  val cases_lifted_insts_tac : bool -> thm option -> term option list -> thm list ->
    Proof.context -> int -> tactic
  val cases_find_insts_tac : bool -> thm option -> (Term_Zipper.T -> bool) option list -> thm list ->
    Proof.context -> int -> tactic

  val cases_pattern_tac : bool ->
    (term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool) -> thm option ->
    (term * term list) option list -> thm list -> Proof.context -> int -> tactic
end

functor Cases_Tactic(
    val get_casesP : Proof.context -> thm list -> thm list
    val get_casesT : Proof.context -> typ list -> term option list -> thm list
    val trivial_tac : Proof.context -> int -> tactic
  ) : CASES_TACTIC =
struct

val logger = Logger.setup_new_logger Logger.root "Cases_Tactic"

structure Show = SpecCheck_Show
structure ZTac_Util = Zippy_ML_Tactic_Util

fun rev_vars_of tm = Term.fold_aterms (fn t as Var _ => insert (op =) t | _ => I) tm []

val pretty_insts = Show.list o Show.option o Show.term

(*adapted from induct.ML to work on fixed instances possibly containing loose bvars from the subgoal*)
fun cases_lifted_insts_tac simp opt_rule insts facts ctxt =
  let fun tac (binders, prems) i st = Seq.make (fn _ =>
    let
      val _  = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
          Pretty.block [Pretty.str "Running cases tactic for rule ",
            Show.option (Show.thm ctxt) opt_rule],
          Pretty.block [Pretty.str "instances: ", pretty_insts ctxt insts],
          Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
        ] |> Pretty.block0 |> Pretty.string_of)
      val nvars_subgoal_prems = Logic.mk_conjunction_list prems |> rev_vars_of |> length
      val nfacts = length facts
      fun inst_rule r =
        let
          val (_, consumes) = Rule_Cases.get r
          val m = Int.min (nfacts, consumes)
          val (thms, facts) = chop m facts
          val st = Method.insert_tac ctxt facts i st |> Seq.hd
          val r_lifted = Drule.incr_indexes st r |> Thm.lift_rule (Thm.cprem_of st i)
          val insts = insts
            |> map (Option.map (curry Logic.rlist_abs binders #> Thm.cterm_of ctxt))
            |> append (replicate nvars_subgoal_prems NONE)
          val r_lifted = Drule.infer_instantiate' ctxt insts r_lifted
            handle exn as THM _ => (@{log Logger.ERR} ctxt (fn _ => Pretty.breaks [
                Pretty.block [Pretty.str "Ill-typed instantion for rule ",
                  Show.thm ctxt r_lifted],
                Pretty.block [Pretty.str "instances: ",
                  pretty_insts ctxt (map (Option.map Thm.term_of) insts)]
              ] |> Pretty.block0 |> Pretty.string_of);
              Exn.reraise exn)
          val comp_nprems = let val nprems_diff = Thm.nprems_of r - Thm.nprems_of r_lifted
            in fn r_lifted_resolved => Thm.nprems_of r_lifted_resolved + nprems_diff end
        in
          HEADGOAL (RANGE (map (single #> resolve_tac ctxt) thms)) r_lifted
          |> Seq.map (rpair (comp_nprems, st))
        end
      val rulesq = case opt_rule of
          SOME r => inst_rule r
        | NONE =>
            let
              val rules = get_casesP ctxt facts @ get_casesT ctxt (map snd binders) insts
              val _ = if null rules
                then @{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
                    Pretty.block [Pretty.str "Could not find case rules for instantiations: ",
                      pretty_insts ctxt insts],
                    Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
                  ] |> Pretty.block0 |> Pretty.string_of)
                else @{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
                    Pretty.block [Pretty.str "Found case rules ",
                      Show.list (Thm.pretty_thm ctxt) rules],
                    Pretty.block [Pretty.str "for instantiations: ", pretty_insts ctxt insts],
                    Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
                  ] |> Pretty.block0 |> Pretty.string_of)
            in Seq.of_list rules |> Seq.maps (Seq.try inst_rule) |> Seq.flat end
      fun resolve_tac thm nprems = Tactic_Util.no_lift_resolve_tac thm nprems ctxt
    in
      rulesq
      |> Seq.maps (fn (rule, (comp_nprems, st)) => (resolve_tac rule (comp_nprems rule)
        THEN_ALL_NEW (if simp then TRY o trivial_tac ctxt else K all_tac)) i st)
      |> Seq.pull
    end)
  in Tactic_Util.SUBGOAL_STRIPPED (apsnd fst) tac end

fun cases_find_insts_tac simp opt_rule ps facts ctxt =
  let fun tac subgoal i st = Seq.make (fn _ =>
    let
      fun merge [] [] = []
        | merge (NONE :: _) [] = []
        | merge (NONE :: ps) ts = NONE :: merge ps ts
        | merge (SOME _ :: ps) ((t, _) :: ts) = SOME t :: merge ps ts
        | merge _ _ = error "unreachable code in cases_find_insts_tac"
      val insts = ZTac_Util.find_subterms_comb Term_Zipper_Search.all_td_lr (map_filter I ps) subgoal
    in
      Seq.of_list insts
      |> Seq.map (merge ps)
      |> Seq.maps (fn insts => cases_lifted_insts_tac simp opt_rule insts facts ctxt i st)
      |> Seq.pull
    end)
  in Tactic_Util.SUBGOAL_DATA I tac end

fun cases_pattern_tac simp match opt_rule patterns facts ctxt =
  let fun tac subgoal i st =
    let
      val params = Logic.strip_params subgoal
      val (paramTs, (binders, nbinders)) = fold_map
        (fn p => fn (rev_ps, i) => (snd p, (p :: rev_ps, i + 1))) params ([], 0)
      val (binders, ctxt) = Binders.fix_binders binders ctxt
      val prepare_pattern = Logic.incr_indexes (paramTs, Thm.maxidx_of st + 1)
        #> `(Term.maxidx_of_term #> Envir.empty)
      val patterns = patterns
        |> map (Option.map (fn (p, no_ps) => (prepare_pattern p, map prepare_pattern no_ps)))
      fun matches ((env, p), t) = match binders ctxt (p, t) env
      fun select (p, no_ps) (t, _) = not (loose_bvar (t, nbinders)) andalso matches (p, t)
        andalso forall (fn p => not (matches (p, t))) no_ps
      val ps = map (Option.map select) patterns
    in cases_find_insts_tac simp opt_rule ps facts ctxt i st end
  in Tactic_Util.SUBGOAL_DATA I tac end

end