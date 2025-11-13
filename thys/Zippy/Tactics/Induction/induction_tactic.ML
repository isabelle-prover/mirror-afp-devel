(*  Title:      Zippy/induction_tactic.ML
    Author:     Kevin Kappelmann
*)
signature INDUCTION_TACTIC_BASE =
sig
  type def_inst = binding option * (term * bool)
  val with_eq : binding option * term -> def_inst
  val without_eq : binding option * term -> def_inst
  val pretty_def_inst : Proof.context -> def_inst -> Pretty.T
  val def_inst_ord : term ord -> def_inst ord
  val print_def_inst : def_inst -> string
end

structure Induction_Tactic_Base =
struct
structure Show = SpecCheck_Show

type def_inst = binding option * (term * bool)
fun with_eq (b, t) = (b, (t, false))
fun without_eq (b, t) = (b, (t, true))
fun pretty_def_inst ctxt = Show.zip (Show.option Binding.pretty)
  (Show.zip (Show.term ctxt) Show.bool)
fun def_inst_ord term_ord = prod_ord (option_ord (apply2 Binding.long_name_of #> fast_string_ord))
  (prod_ord term_ord bool_ord)
local open ML_Syntax
in
val print_def_inst = print_pair
  (print_option (fn b => make_binding (Binding.name_of b, Binding.pos_of b)))
  (print_pair print_term Value.print_bool)
end

fun pretty_insts ctxt = Show.list (Show.list (Show.option (pretty_def_inst ctxt)))
end

signature INDUCTION_TACTIC =
sig
  include INDUCTION_TACTIC_BASE
  include HAS_LOGGER
  val induct_tac : bool -> bool -> thm list option -> def_inst option list list ->
    (string * typ) list list -> term option list -> thm list -> Proof.context -> int -> tactic

  val prepare_preds : (term -> bool) option list option -> (term -> bool) option ->
    Proof.context -> int -> thm -> def_inst option list Seq.seq * (string * typ) list
  val induct_find_tac : bool -> bool -> thm option -> (term -> bool) option list ->
    (term -> bool) -> term option list -> thm list -> Proof.context -> int -> tactic

  val prepare_patterns :
    (term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool) ->
    (term * term list) option list option -> (term list * term list) option -> Proof.context ->
    int -> thm -> (term -> bool) option list * (term -> bool)
  val induct_pattern_tac : bool -> bool ->
    (term Binders.binders -> Proof.context -> term * term -> Envir.env -> bool) -> thm option ->
    (term * term list) option list -> term list * term list -> term option list ->
    thm list -> Proof.context -> int -> tactic
end

functor Induction_Tactic(Induct : INDUCT) : INDUCTION_TACTIC =
struct
open Induction_Tactic_Base

val logger = Logger.setup_new_logger Logger.root "Induction_Tactic"

structure ZTac_Util = Zippy_ML_Tactic_Util

(*adapted from induct.ML*)
local open Induct
fun align_left ctxt msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then (@{log Logger.ERR} ctxt (fn _ => msg); error msg) else (take n xs ~~ ys) end
fun align_right ctxt msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then (@{log Logger.ERR} ctxt (fn _ => msg); error msg) else (drop (m - n) xs ~~ ys) end
fun prep_inst ctxt align tune (tm, ts) =
  let
    fun prep_var (Var (x, xT), SOME t) =
          let
            val ct = Thm.cterm_of ctxt (tune t)
            val tT = Thm.typ_of_cterm ct
          in
            if Type.could_unify (tT, xT) then SOME (x, ct)
            else let val msg = Pretty.string_of (Pretty.block
                [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
                  Syntax.pretty_term ctxt (Thm.term_of ct), Pretty.str " ::", Pretty.brk 1,
                  Syntax.pretty_typ ctxt tT])
              in (@{log Logger.ERR} ctxt (fn _ => msg); error msg) end
          end
      | prep_var (_, NONE) = NONE
    val xs = vars_of tm
  in
    align ctxt "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end
fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = Name.clean (Variable.revert_fixed ctxt z)
        fun index _ [] = []
          | index i (y :: ys) =
              if x = y then x ^ string_of_int i :: index (i + 1) ys
              else y :: index i ys
        fun rename_params [] = []
          | rename_params ((y, Type (U, _)) :: ys) =
              (if U = T then x else y) :: rename_params ys
          | rename_params ((y, _) :: ys) = y :: rename_params ys
        fun rename_asm A =
          let
            val xs = rename_params (Logic.strip_params A)
            val xs' =
              (case filter (fn x' => x' = x) xs of
                [] => xs
              | [_] => xs
              | _ => index 1 xs)
          in Logic.list_rename_params xs' A end
        fun rename_prop prop =
          let val (As, C) = Logic.strip_horn prop
          in Logic.list_implies (map rename_asm As, C) end
        val thm' = Thm.renamed_prop (rename_prop (Thm.prop_of thm)) thm
      in [Rule_Cases.save thm thm'] end
  | special_rename_params _ _ ths = ths
fun get_inductP ctxt (fact :: _) = map single (find_inductP ctxt (Thm.concl_of fact))
  | get_inductP _ _ = []
fun rule_instance ctxt inst rule =
  infer_instantiate ctxt (prep_inst ctxt align_left I (Thm.prop_of rule, inst)) rule
in
fun induct_tac close_trivial simp opt_rules def_insts arbitrary taking facts ctxt i st =
  Seq.make (fn _ =>
  let
    val _  = @{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
        Pretty.block [Pretty.str "Running induction tactic for rules ",
          Show.option (Show.list (Show.thm ctxt)) opt_rules],
        Pretty.block [Pretty.str "instances: ", pretty_insts ctxt def_insts],
        Pretty.block [Pretty.str "arbitraries: ",
          Show.list (Show.list (Show.zip Pretty.str (Show.typ ctxt))) arbitrary],
        Pretty.block [Pretty.str "takings: ", Show.list (Show.option (Show.term ctxt)) taking],
        Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
      ] |> Pretty.block0 |> Pretty.string_of)
    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list
    val atomized_defs = map (map (Conv.fconv_rule (atomize_cterm defs_ctxt))) defs

    fun inst_rule (concls, r) = (if null insts then `Rule_Cases.get r
        else let val insts = insts
            |> align_left ctxt "Rule has fewer conclusions than arguments given"
              (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r)))
            |> maps (prep_inst ctxt align_right (atomize_term ctxt))
          in (Rule_Cases.get r, infer_instantiate ctxt insts r) end)
      |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th))

    val ruleq = case opt_rules of
        SOME rs => Seq.single (inst_rule (Rule_Cases.strict_mutual_rule ctxt rs))
      | NONE =>
          let
            val rules = get_inductP ctxt facts @
              map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts)
            val _ = if null rules
              then @{log Logger.WARN} ctxt (fn _ => Pretty.breaks [
                  Pretty.block [Pretty.str "Could not find induction rules for instantiations: ",
                    pretty_insts ctxt def_insts],
                  Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
                ] |> Pretty.block0 |> Pretty.string_of)
              else @{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
                  Pretty.block [Pretty.str "Found induction rules ",
                    Show.list (Show.list (Thm.pretty_thm ctxt)) rules],
                  Pretty.block [Pretty.str "for instantiations: ", pretty_insts ctxt def_insts],
                  Pretty.block [Pretty.str "facts: ", Show.list (Show.thm ctxt) facts]
                ] |> Pretty.block0 |> Pretty.string_of)
          in
            Seq.of_list rules |> Seq.map_filter (Rule_Cases.mutual_rule ctxt)
            |> Seq.maps (Seq.try inst_rule)
          end

    fun main_tac i st =
      ruleq
      |> Seq.maps (Rule_Cases.consume defs_ctxt (flat defs) facts)
      |> Seq.maps (fn (((_, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            let
              val adefs = nth_list atomized_defs (j - 1)
              val frees = fold (Term.add_frees o Thm.prop_of) adefs []
              val xs = nth_list arbitrary (j - 1)
              val k = nth concls (j - 1) + more_consumes
            in
              Method.insert_tac defs_ctxt (more_facts @ adefs)
              THEN' (if simp
                then rotate_tac k (length adefs)
                  THEN' arbitrary_tac defs_ctxt k (List.partition (member op = frees) xs |> (op @))
                else arbitrary_tac defs_ctxt k xs)
            end)
          THEN' inner_atomize_tac defs_ctxt) j))
        THEN' atomize_tac defs_ctxt) i st
        |> Seq.maps (fn st' => guess_instance ctxt (internalize ctxt more_consumes rule) i st'
          |> Seq.map (rule_instance ctxt taking)
          |> Seq.maps (fn rule' => (resolve_tac ctxt [rule'] i
            THEN PRIMITIVE (singleton (Proof_Context.export defs_ctxt ctxt))) st')))
  in
    (main_tac
    THEN_ALL_NEW ((if simp
      then simplify_tac ctxt THEN' (if close_trivial then TRY o trivial_tac ctxt else K all_tac)
      else K all_tac)
    THEN_ALL_NEW rulify_tac ctxt)) i st
    |> Seq.pull
  end)
end

fun prepare_preds inst_ps arbitrary_p ctxt i st =
  let
    val subgoal = Thm.prem_of st i
    fun merge [] [] = []
      | merge (NONE :: _) [] = []
      | merge (NONE :: ps) ts = NONE :: merge ps ts
      | merge (SOME _ :: ps) (t :: ts) = SOME (NONE, (t, false)) :: merge ps ts
      | merge _ _ = error "unreachable code in prepare_preds"
    val instssq = case inst_ps of
        NONE => Seq.empty
      | SOME inst_ps => ZTac_Util.find_subterms_comb (map_filter I inst_ps) subgoal
          |> Seq.of_list |> Seq.map (merge inst_ps)
    val arbitrary = case arbitrary_p of
        NONE => []
      | SOME arbitrary_p =>singleton (fn ps => ZTac_Util.find_subterms ps subgoal) arbitrary_p
          |> map (fn x => dest_Free x handle exn as TERM _ =>
            (@{log Logger.ERR} ctxt (fn _ => "Can only set free variables as arbitrary");
            Exn.reraise exn))
    in (instssq, arbitrary) end

fun induct_find_tac close_trivial simp opt_rule inst_ps arbitrary_p taking facts ctxt i st =
  Seq.make (fn _ => PRIMSEQ (fn st =>
    let val (insts_psq, arbitrary) = prepare_preds (SOME inst_ps) (SOME arbitrary_p) ctxt i st
    in
      insts_psq
      |> Seq.maps (fn insts => induct_tac close_trivial simp (Option.map single opt_rule) [insts]
        [arbitrary] taking facts ctxt i st)
    end) st |> Seq.pull)

fun prepare_patterns match inst_patterns arbitrary_pattern ctxt i st =
  let
    val subgoal = Thm.prem_of st i
    val params = Logic.strip_params subgoal
    val (paramTs, binders) = fold_map (fn p => fn rev_ps => (snd p, p :: rev_ps)) params []
    val (binders, ctxt) = Binders.fix_binders binders ctxt
    val prepare_pattern = Logic.incr_indexes (paramTs, Thm.maxidx_of st + 1)
      #> `(Term.maxidx_of_term #> Envir.empty)
    fun prepare_entry (ps, no_ps) = (map prepare_pattern ps, map prepare_pattern no_ps)
    fun matches ((env, p), t) = match binders ctxt (p, t) env
    fun matches_pattern (ps, no_ps) t = exists (fn p => (matches (p, t))) ps
      andalso forall (fn p => not (matches (p, t))) no_ps
    fun inst_select p t = not (Term.is_open t) andalso not (exists_subterm is_Var t)
      andalso matches_pattern p t
    val inst_ps = the_default [] inst_patterns
      |> map (Option.map (apfst single #> prepare_entry #> inst_select))
    fun arbitrary_select p t = can dest_Free t andalso matches_pattern p t
    val arbitrary_p = \<^if_none>\<open>([], [])\<close> arbitrary_pattern |> prepare_entry |> arbitrary_select
  in (inst_ps, arbitrary_p) end

fun induct_pattern_tac close_trivial simp match opt_rule inst_patterns arbitrary_pattern taking facts ctxt i st =
  Seq.make (fn _ => PRIMSEQ (fn st =>
    let val (inst_ps, arbitrary_p) = prepare_patterns match (SOME inst_patterns)
      (SOME arbitrary_pattern) ctxt i st
    in induct_find_tac close_trivial simp opt_rule inst_ps arbitrary_p taking facts ctxt i st end)
    st |> Seq.pull)

end
