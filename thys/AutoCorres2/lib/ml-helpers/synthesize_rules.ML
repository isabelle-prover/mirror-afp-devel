(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature SYNTHESIZE_RULES =
sig
  structure Data: GENERIC_DATA
  type benv = (string * typ) list * int
  val bempty: benv
  type rule
  type rules
  val get_rules: Proof.context -> string -> rules option
  val retrieve_rules: Context.generic -> string -> term option -> term option * rule list
  val dest_rule: rule ->
        {name: binding,
         priority: int,
         rule: thm,
         tac: (Proof.context -> int -> tactic) option}
  (* Misc *)
  val strip_abs_prod: term -> (string * typ) list * term
  val arity_from_projection: term -> bool list
  val match_rule_vars: benv -> Proof.context -> term -> Vartab.key list -> term -> term list

  (* Tactics *)
  val resolve_split_thm: string -> Proof.context -> int -> tactic
  val resolve_tacs: rules -> Proof.context -> cterm -> (binding * (int -> context_tactic)) list
  val resolve_tacs': rules list -> Proof.context -> cterm -> (binding * (int -> context_tactic)) list
  val gen_cond_cache: ((Timing.timing * int * int) option -> term -> bool) ->
        (term -> term) -> (cterm -> thm -> int -> context_tactic) -> rules -> CT.ctxt_cache

  (* Diagnostics *)
  val print_rules: Context.generic -> string -> term option -> unit
  val print_rules_cmd: xstring * Position.T -> string option -> Proof.context -> Proof.context

  (* Declarations *)
  val comma_list: (Token.T list -> 'a * Token.T list) -> Token.T list -> 'a list * Token.T list
  val pattern_decls: ((string * Position.T) * (string * string list)) list parser

  val check: Context.generic -> xstring * Position.T -> string * rules
  val extern: Context.generic -> string -> xstring
  val intern: Context.generic -> xstring -> string
  val markup_extern: Context.generic -> string -> Markup.T * xstring

  val gen_pattern_fun: string -> Proof.context -> string * string list -> string

  val add_pattern_decls: binding -> ((string * Position.T) * (string * string list)) list ->
        Proof.context -> Proof.context
  val add_pattern_ml: binding -> Input.source -> Proof.context -> Proof.context
  val declare: binding -> Proof.context -> string * local_theory
  val declare_generic: binding -> Context.generic -> bstring * Context.generic

  val gen_add_rule: string -> {only_schematic_goal: bool} -> (Proof.context -> int -> tactic) option -> (Proof.context -> int -> term -> term) ->
        binding -> int -> thm -> Context.generic -> Context.generic
  val gen_add_split_rule: string -> {only_schematic_goal: bool} -> (Proof.context -> int -> term -> term) -> binding -> int -> string list ->
        thm -> Context.generic -> (Bin.Bin -> thm) * Context.generic
  val gen_add_infer_project_split_rule: (Proof.context -> int -> term -> term) ->
        (benv -> Proof.context -> term -> Vartab.key list -> term -> bool list) ->
        (Bin.Bin -> thm) -> string -> {only_schematic_goal: bool} -> binding -> int -> string list -> string list ->
        thm -> Context.generic -> (Bin.Bintab.key -> thm) * Context.generic
  val gen_add_project_split_rule: (Proof.context -> int -> term -> term) -> (Bin.Bin -> thm) -> string -> {only_schematic_goal: bool} ->
        binding -> int -> string ->
        thm -> Context.generic -> (Bin.Bintab.key -> thm) * Context.generic
  val add_rule: string -> {only_schematic_goal:bool} -> binding -> int -> thm -> Context.generic -> Context.generic
  val add_rule_attrib: string -> {only_schematic_goal:bool} -> binding -> int ->  attribute
  val add_rule_most_generic_pattern: string -> {only_schematic_goal:bool} -> binding -> int -> thm -> Context.generic -> Context.generic
  val add_rule_most_generic_pattern_attrib: string -> {only_schematic_goal:bool} -> binding -> int -> attribute
  val add_rules: string -> {only_schematic_goal:bool} -> (binding * int * thm) list -> Context.generic -> Context.generic
  val add_simple_rule: string -> {only_schematic_goal:bool} -> binding -> int -> thm -> Context.generic -> Context.generic
  val add_simple_rules: string -> {only_schematic_goal:bool} -> (binding * int * thm) list -> Context.generic -> Context.generic
  val add_split_rule: string -> {only_schematic_goal:bool} -> binding -> int -> string list -> thm -> Context.generic ->
        (Bin.Bin -> thm) * Context.generic
  val add_split_rules: string -> {only_schematic_goal:bool} -> (binding * int * string list * thm) list -> Context.generic ->
        (Bin.Bin -> thm) list * Context.generic
  val add_infer_project_split_rule: string -> {only_schematic_goal: bool} ->
        (benv -> Proof.context -> term -> Vartab.key list -> term -> bool list) ->
        (Bin.Bin -> thm) -> binding -> int -> string list -> string list ->
        thm -> Context.generic -> (Bin.Bintab.key -> thm) * Context.generic
  val add_tac_rule: string -> (Proof.context -> int -> tactic) -> binding -> int -> thm -> Context.generic -> Context.generic
  val add_tac_rules: string -> (Proof.context -> int -> tactic) ->
        (binding * int * thm) list -> Context.generic -> Context.generic
  val add_pattern_tac_rule: string -> (Proof.context -> int -> tactic) ->
        binding -> int -> term -> Context.generic -> Context.generic
  val add_project_split_rule: (Bin.Bintab.key -> thm) -> string -> {only_schematic_goal:bool} -> binding -> int ->
        string -> thm -> Context.generic -> (Bin.Bintab.key -> thm) * Context.generic
  val add_project_split_rules: (Bin.Bintab.key -> thm) -> string -> {only_schematic_goal:bool} -> (binding * int * string * thm) list ->
        Context.generic -> (Bin.Bintab.key -> thm) list * Context.generic

  val add_mk_patterns: string -> (binding * (Proof.context -> int -> term -> term)) list ->
        local_theory -> local_theory

  val gen_del_rule: string -> {only_schematic_goal: bool} -> (Proof.context -> int -> tactic) option -> (Proof.context -> int -> term -> term) ->
        binding -> int -> thm -> Context.generic -> Context.generic
  val del_rule: string -> {only_schematic_goal:bool} -> binding -> int -> thm -> Context.generic -> Context.generic
  val del_rule_attrib: string -> {only_schematic_goal:bool} -> binding -> int ->  attribute

  val gen_del_split_rule: string -> {only_schematic_goal: bool} -> (Proof.context -> int -> term -> term) -> binding -> int -> string list ->
        thm -> Context.generic -> Context.generic
  val del_split_rule: string -> {only_schematic_goal:bool} -> binding -> int -> string list -> thm -> Context.generic ->
        Context.generic

  (* used from ML antiquotations *)
  val fresh_var: int -> term -> term
  val get_maxidx: int -> term -> int
end

structure Synthesize_Rules : SYNTHESIZE_RULES =
struct

val verbose_msg = Utils.verbose_msg;

fun gen_map_loose_bnos lev f (t $ u) = gen_map_loose_bnos lev f t $ gen_map_loose_bnos lev f u
  | gen_map_loose_bnos lev f (Abs (a, T, t)) = Abs (a, T, gen_map_loose_bnos (lev + 1) f t)
  | gen_map_loose_bnos lev f (t as (Bound i)) = if i < lev then t else f (i - lev)
  | gen_map_loose_bnos lev f t = t

val map_loose_bnos = gen_map_loose_bnos 0;

fun dummyfy_loose_bnos (bounds, maxidx) =
  map_loose_bnos (fn i => let val (n, T) = nth bounds i in Var((n, maxidx + i), T) end)

fun match_rule_vars benv ctxt pattern rule_vars trm =
  let
    fun match p t vars =
      let
        val (ty_env, trm_env) = Pattern.first_order_match (Proof_Context.theory_of ctxt) (p,t)
              (Vartab.empty, Vartab.empty)
        val matched_vars = map (Vartab.lookup trm_env) vars
      in
        if forall is_some matched_vars
        then matched_vars |> map (snd o the)
        else []
      end

  in
    match pattern trm rule_vars
    handle TERM _ => (* fastype_of (Bound _) *) (
      let
        val trm = dummyfy_loose_bnos benv trm
      in match pattern trm rule_vars end
      handle Pattern.MATCH => [])
    | Pattern.MATCH => []
  end

fun match_rule_var benv ctxt pattern rule_var trm =
  case match_rule_vars benv ctxt pattern [rule_var] trm of
    [t] => SOME t
  | _ => NONE

fun strip_abs_prod t =
  case t of
    Abs (x, T, bdy) => ([(x,T)], bdy)
  | _ => case strip_comb t of
      (Const (@{const_name case_prod},_), Abs (x, xT, (Abs (y, yT, bdy)))::[]) =>
         ([(x,xT), (y, yT)], bdy)
     | (Const (@{const_name case_prod},cpT), Abs (x, xT, cp)::[]) =>
         (case strip_comb cp of
            (Const (@{const_name case_prod},_), _) =>
              let
                val (bounds, bdy) = strip_abs_prod cp
              in ((x,xT)::bounds, bdy) end
          | _ => (* eta expand lost abstraction in case_prod *)
                 ([(x,xT), (Tuple_Tools.strip_uu, nth (binder_types cpT) 1)], incr_boundvars 1 cp $ Bound 0))
     | (Const (@{const_name case_prod}, cpT), cp::[]) =>
             (* eta expand lost abstractions in case_prod *)
             let
               val [xT, yT] = take 2 (binder_types cpT)
             in ([(Tuple_Tools.strip_uu, xT), (Tuple_Tools.strip_uu, yT)], incr_boundvars 2 cp $ Bound 1 $ Bound 0) end
     | _ => ([], t);

fun arity_from_projection prj =
  let
    val (vars, bdy) = strip_abs_prod prj
    val loose = Term.loose_bnos bdy
    fun tag n [] = []
      | tag n (_::vs) = (if member (op =) loose n then true else false) :: tag (n - 1) vs
  in
    tag (length vars - 1) vars
  end

val _ = @{assert} ([true,false,false,true] = arity_from_projection @{term "\<lambda>(x1, x2, x3, x4). (x1, x4)"})

(* generalised notion of 'arity' including tuple projections *)
datatype derive_arity_mode = One | Infer_Projection | Pick_Projection | No_Projection
type benv = ((string * typ) list * int) (* bound variables, maxidx *)
val bempty = ([], ~1)

fun gen_derive_arity One _ _ _ = (fn _ => fn _ => fn _  => Bin.bin_of_int 1)
  | gen_derive_arity No_Projection _  pattern (arity_var::_) = (fn benv => fn ctxt => fn concl =>
      (case match_rule_var benv ctxt pattern arity_var concl of
                       SOME n => Bin.bin_of_int (Tuple_Tools.num_case_prod n + 1)
                     | NONE => []))
  | gen_derive_arity Pick_Projection _ pattern (prj_var::_) = (fn benv => fn ctxt => fn concl =>
      (case match_rule_var benv ctxt pattern prj_var concl of
                       SOME prj => arity_from_projection prj
                     | NONE => []))
  | gen_derive_arity Infer_Projection infer pattern vars = (fn benv => fn ctxt => fn concl => infer benv ctxt pattern vars concl)

fun no_infer _ _ _ _ _ = []

val bogus_thm = @{thm refl}

type rule =
  {name: binding,
   priority: int, \<comment>\<open>higher priority will be tried first in match\<close>
   rule: thm,
   mode: derive_arity_mode,
   pattern: term, \<comment>\<open>pattern used as index in the term-net\<close>
   derive_arity: benv -> Proof.context  -> term (* concl *) -> Bin.Bin,
   split: Bin.Bin -> thm, \<comment>\<open>Bin is interpreted as a natural number describing the tuple arity
                            by 'ordinary' rules,
                            whereas 'projection' rules interpret the true bits as the components
                            of the tuple that will remain after projection.\<close>
   cache: thm lazy Bin.Bintab.table Fun_Cache.handler, \<comment>\<open>cache for split function\<close>
   only_schematic_goal: bool, \<comment> \<open>only resolve with rule if the goal has some schematic variables to synthesize\<close>
   tac: (Proof.context -> int -> tactic) option \<comment>\<open>instead of a resolve_tac with thm use the tactic\<close>
};

fun dest_rule ({name, priority, rule, tac, ...}:rule) =
  {name = name, priority = priority, rule = rule, tac = tac}

fun mk_simple_rule name priority pattern only_schematic_goal thm =
  let val thm = Thm.trim_context thm
  in
   {name = name, priority = priority,rule = thm, mode = One, pattern = pattern,
    split = K thm,
    cache = Fun_Cache.dummy_handler Bin.Bintab.empty, tac = NONE,
    derive_arity = gen_derive_arity One no_infer pattern [], only_schematic_goal = only_schematic_goal}:rule
  end

fun mk_tac_rule name priority pattern thm tac =
  let val thm = Thm.trim_context thm
  in
   {name = name, priority = priority,rule = thm, mode = One, pattern = pattern,
    split = K thm,
    cache = Fun_Cache.dummy_handler Bin.Bintab.empty, tac = SOME tac,
    derive_arity = gen_derive_arity One no_infer pattern [], only_schematic_goal = false}
  end

fun mk_split_rule name priority only_schematic_goal thm pattern arity_var split cache =
  let val thm = Thm.trim_context thm
  in
   {name = name, priority = priority,rule = thm, mode = No_Projection, pattern = pattern,
    split = split,
    cache = cache, tac = NONE,
    derive_arity = gen_derive_arity No_Projection no_infer pattern [arity_var], 
    only_schematic_goal = only_schematic_goal}
  end

fun mk_project_split_rule name priority only_schematic_goal thm pattern prj_var split cache =
  let val thm = Thm.trim_context thm
  in
   {name = name, priority = priority, rule = thm, mode = Pick_Projection, pattern = pattern,
    split = split,
    cache = cache, tac = NONE,
    derive_arity = gen_derive_arity Pick_Projection no_infer pattern [prj_var],
    only_schematic_goal = only_schematic_goal}
  end

fun mk_infer_project_split_rule name priority only_schematic_goal thm pattern vars split cache infer =
  let val thm = Thm.trim_context thm
  in
   {name = name, priority = priority,rule = thm, mode = Infer_Projection, pattern = pattern,
    split = split,
    cache = cache, tac=NONE,
    derive_arity = gen_derive_arity Infer_Projection infer pattern vars,
    only_schematic_goal = only_schematic_goal}
  end

fun rule_eq ({rule=rule1,...}:rule, {rule=rule2,...}:rule) =
  Thm.eq_thm_prop (rule1, rule2)

type rules = {rules: rule Net.net, mk_patterns: (binding * (Proof.context -> int -> term -> term)) list}

fun merge_rule_net (n1, n2) =
  if pointer_eq (n1, n2) then n1
  else if Net.is_empty n2 then n1
  else if Net.is_empty n1 then n2
  else Net.merge rule_eq (n1, n2)

val merge_mk_patterns =
  merge ((op =) o apply2 fst)

fun map_rules f ({rules, mk_patterns}:rules) = {rules = f rules, mk_patterns = mk_patterns}:rules
fun map_mk_patterns f ({rules, mk_patterns}:rules) = {rules = rules, mk_patterns = f mk_patterns}:rules

structure Data = Generic_Data (
 type T = rules Name_Space.table;
 val empty = Name_Space.empty_table "rules";
 val merge = Name_Space.join_tables (fn _ =>  fn ({rules=r1, mk_patterns=ps1}, {rules=r2, mk_patterns=ps2}) =>
  {rules = merge_rule_net (r1, r2), mk_patterns = merge_mk_patterns (ps1, ps2)});
)

fun intern context = Data.get context |> Name_Space.space_of_table |> Name_Space.intern
fun extern context = Data.get context |> Name_Space.space_of_table |> Name_Space.extern (Context.proof_of context)
fun markup_extern context = Data.get context |> Name_Space.space_of_table |> Name_Space.markup_extern (Context.proof_of context)

(*
 val define: Context.generic -> bool -> binding * 'a -> 'a table -> string * 'a table
*)

fun check context  =
  Name_Space.check context (Data.get context)

fun dest_binding b = (Binding.name_of b, Binding.pos_of b)

fun declare binding lthy =
  let
    val upd_data = Name_Space.define (Context.Proof lthy) true (binding, {rules = Net.empty, mk_patterns = []}) #> snd

    val lthy' = lthy
      |> Local_Theory.background_theory (Context.theory_map (Data.map (upd_data)))
      |> Local_Theory.map_contexts (K (Context.proof_map (Data.map (upd_data))))
    val (name, _) = check (Context.Proof lthy') (dest_binding binding)
  in
    (name, lthy')
  end

fun declare_generic binding context =
  let
    val new_entry = Name_Space.define context true (binding, {rules = Net.empty, mk_patterns = []}) #> snd
    val context' = context |> Data.map new_entry
  in
    (Binding.name_of binding, context')
  end

fun pattern_ord thy (p1, p2) =
  if Pattern.matches thy (p1, p2)
  then if Pattern.matches thy (p2, p1) then EQUAL else GREATER
  else if Pattern.matches thy (p2, p1) then LESS
  else raise TERM ("pattern_ord: no order between patterns", [p1, p2])

fun first_mk_pattern (ps: (binding * (Proof.context -> int -> term -> term)) list) ctxt i t =
 case ps of
   [] =>
       let
           val _ = verbose_msg 5 ctxt (fn _ => "first_mk_pattern: no match found for " ^
                    quote (Syntax.string_of_term ctxt t) ^ ". Using identity")
       in t end
  | ((b, p):: ps') =>
      (case try (p ctxt i) t of
          SOME t' =>
            let
              val _ = verbose_msg 5 ctxt (fn _ => "first_mk_pattern: " ^ More_Binding.here b ^
                    " yields: " ^ quote (Syntax.string_of_term ctxt t'))
             in t' end
        | NONE => first_mk_pattern ps' ctxt i t )

local
  fun pretty_match ctxt ((b, _), t) = Pretty.strs ["mk_pattern", More_Binding.here b, "yields:", quote (Syntax.string_of_term ctxt t)]
  fun pretty_matches ctxt header ms = Pretty.big_list header (map (pretty_match ctxt) ms)
in
fun check_mk_pattern fresh (ps: (binding * (Proof.context -> int -> term -> term)) list) ctxt i t =
  let
    fun try_match (b, p) = try (p ctxt i) t |> Option.map (pair (b, p))
    val matches = map_filter try_match ps
  in
    case matches of
      [] =>
        let
           val _ = if fresh then () else warning ("check_mk_pattern: no match found for " ^
                    quote (Syntax.string_of_term ctxt t) ^ ". Using identity")
        in t end
    | [((b, p), t')] =>
        let
           val _ = if fresh then error ("check_mk_pattern: fresh pattern expected but found overlapping pattern: " ^ More_Binding.here b)
                   else verbose_msg 2 ctxt (fn _ => "selected mk_pattern: " ^ More_Binding.here b ^
                    " yields: " ^ quote (Syntax.string_of_term ctxt t'))
        in t' end
    | ((b, p), t'):: _ =>
        let
          val _ = warning (Pretty.string_of (pretty_matches ctxt "check_mk_pattern: multiple matches (default: first successful match)" matches))
        in t' end
  end

fun gen_most_generic_mk_pattern (ps: (binding * (Proof.context -> int -> term -> term)) list) ctxt i t =
  let
    fun try_match (b, p) = try (p ctxt i) t |> Option.map (pair (b, p))
    val matches = map_filter try_match ps |> sort (rev_order o pattern_ord (Proof_Context.theory_of ctxt) o apply2 snd)

  in
    case matches of
      [] => let val _ = verbose_msg 5 ctxt (fn _ => "most_generic_mk_pattern: no match found for " ^
                    quote (Syntax.string_of_term ctxt t) ^ ". Using identity")
            in t end
    | [m as ((b, p), t')] =>
        let val _ = verbose_msg 5 ctxt (fn _ => Pretty.string_of (pretty_match ctxt m))
        in t' end
    | ((b, p), t'):: _ =>
        let val _ = verbose_msg 5 ctxt (fn _ => Pretty.string_of (pretty_matches ctxt "most_generic_mk_pattern multiple matches (first is returned)" matches))
        in t' end
  end
end

fun standard_check_mk_pattern rules_name ctxt =
  Name_Space.lookup (Data.get (Context.Proof ctxt)) rules_name |> the |> #mk_patterns
  |> (fn ps => check_mk_pattern false ps ctxt)

fun check_fresh_mk_pattern rules_name ctxt =
  Name_Space.lookup (Data.get (Context.Proof ctxt)) rules_name |> the |> #mk_patterns
  |> (fn ps => check_mk_pattern true ps ctxt)

fun standard_mk_pattern rules_name ctxt =
  Name_Space.lookup (Data.get (Context.Proof ctxt)) rules_name |> the |> #mk_patterns
  |> (fn ps => first_mk_pattern ps ctxt)

fun most_generic_mk_pattern rules_name ctxt =
  Name_Space.lookup (Data.get (Context.Proof ctxt)) rules_name |> the |> #mk_patterns
  |> (fn ps => gen_most_generic_mk_pattern ps ctxt)

fun get_rules ctxt name =
 Name_Space.lookup (Data.get (Context.Proof ctxt)) name


fun add_mk_patterns rules_name (mk_patterns: (binding * (Proof.context -> int -> term -> term)) list) lthy =
  let
    val upd_data = Data.map (Name_Space.map_table_entry rules_name (map_mk_patterns (fn ps => ps @ mk_patterns)))
  in
    lthy
    |> Local_Theory.background_theory (Context.theory_map upd_data)
    |> Local_Theory.map_contexts (K (Context.proof_map upd_data))
  end

fun rule_ord (rule1, rule2) =  rev_order (int_ord (#priority (rule1:rule), #priority (rule2:rule)))

(* pretty printing *)

fun prt_term ctxt =
      singleton (Syntax.uncheck_terms ctxt) #>
      Type_Annotation.ignore_free_types #>
      Syntax.unparse_term ctxt;

fun pretty_entry label p = Pretty.block [(Pretty.str (suffix ": " label)), p]

fun string_of_mode One = "no tuple splitting"
  | string_of_mode No_Projection = "tuple splitting"
  | string_of_mode Pick_Projection = "tuple splitting with picked projection"
  | string_of_mode Infer_Projection = "tuple splitting with inferred projection"

fun string_of_bool true = "true"
  | string_of_bool false = "false"

fun markup_name ctxt rules_name =
  let
    val (m, str) = markup_extern (Context.Proof ctxt) rules_name
  in
    Markup.markup m str
  end

fun pretty_rule ctxt (rule: rule) =
  Pretty.item (
   [pretty_entry "rule" (More_Binding.here_pretty (#name rule)), Pretty.brk 1,
    Pretty.indent 2 (Thm.pretty_thm ctxt (#rule rule) |> Pretty.cartouche), Pretty.brk 1,
    pretty_entry "priority" (Pretty.str (string_of_int (#priority rule))), Pretty.brk 1,
    pretty_entry "pattern" (prt_term ctxt (#pattern rule) |> Pretty.cartouche), Pretty.brk 1,
    pretty_entry "mode" (Pretty.str (string_of_mode (#mode rule))), Pretty.brk 1,
    pretty_entry "only_schematic_goal" (Pretty.str (string_of_bool (#only_schematic_goal rule))), Pretty.brk 1,
    pretty_entry "consumes" (Pretty.str (string_of_int (Rule_Cases.get_consumes (#rule rule)))), Pretty.brk 1]
)

fun pretty_rules ctxt rules_name (pat_opt, rules: rule list) =
  let
    val pretty_rules_name = enclose "(" ")" (markup_name ctxt rules_name)
  in
    case pat_opt of
      NONE => Pretty.big_list ("rules " ^ pretty_rules_name) (map (pretty_rule ctxt) rules)
    | SOME pat => Pretty.block_enclose
       (Pretty.block [Pretty.str ("rules " ^ pretty_rules_name ^ " for "), prt_term ctxt pat |> Pretty.cartouche], Pretty.brk 0)
       (map (pretty_rule ctxt) rules)
  end

fun retrieve_rules context rules_name t_opt =
  let
    val rules = Name_Space.lookup (Data.get context) rules_name |> the
    val net = #rules rules
  in
    case t_opt of
      NONE => net |> Net.entries |> sort rule_ord |> pair NONE
    | SOME t =>
        let
          val pat = first_mk_pattern (#mk_patterns rules) (Context.proof_of context) (~1) t
        in (SOME pat, Net.match_term net pat) end
  end

fun print_rules context rules_name t_opt =
    retrieve_rules context rules_name t_opt |> pretty_rules (Context.proof_of context) rules_name
    |> Pretty.string_of |> writeln

(* adding rules *)

fun prep_split_rule {only_schematic_goal} mk_pattern name priority var_names thm ctxt =
 let
   val _ = assert (not (null var_names)) "add_split_rule: expecting at least one variable name"
   val concl = Thm.concl_of thm
   val (split, cache) = Fun_Cache.create_handler (Binding.map_name (fn name => ("split_rel_nondet_monad: " ^ name)) name)
     (fn c => @{make_string} c) Bin.Bintab.empty Bin.Bintab.lookup Bin.Bintab.update
     (Tuple_Tools.split_rule_bin ctxt var_names thm)
   val var = Term.add_vars concl [] |> filter (fn ((n, _),_) => n = hd var_names) |> hd |> fst
   val pattern = mk_pattern ctxt (~1) concl
   val _ = assert (member (op =) (map fst (Term.add_vars pattern [])) var)
        ("gen_add_split_rule: variable ^ '" ^ @{make_string} var ^ "' ^ must be present in pattern and rule-conclusion")
   val rule = mk_split_rule name priority only_schematic_goal thm pattern var split cache
 in (pattern, rule, split) end


fun gen_add_split_rule rules_name only_schematic_goal mk_pattern name priority var_names thm context =
 let
   val ctxt = Context.proof_of context
   val (pattern, rule, split) = prep_split_rule only_schematic_goal mk_pattern name priority var_names thm ctxt
   val _ = verbose_msg 8 ctxt (fn _ => "adding split rule '" ^ More_Binding.here name ^ "' with pattern: \n " ^
         Syntax.string_of_term ctxt pattern)
 in
   (split, Data.map (Name_Space.map_table_entry rules_name (map_rules (Net.insert_term_safe rule_eq (pattern, rule)))) context)
 end

fun add_split_rule rules_name only_schematic_goal name priority var_names thm context =
  gen_add_split_rule rules_name only_schematic_goal (standard_check_mk_pattern rules_name) name priority var_names thm context

fun add_split_rules rules_name only_schematic_goal = fold_map (fn (name, priority, names, thm) => add_split_rule rules_name only_schematic_goal name priority names thm)

fun gen_del_split_rule rules_name only_schematic_goal mk_pattern name priority var_names thm context =
 let
   val ctxt = Context.proof_of context
   val (pattern, rule, split) = prep_split_rule only_schematic_goal mk_pattern name priority var_names thm ctxt
   val _ = verbose_msg 8 ctxt (fn _ => "deleting split rule '" ^ More_Binding.here name ^ "' with pattern: \n " ^
         Syntax.string_of_term ctxt pattern)
 in
   Data.map (Name_Space.map_table_entry rules_name (map_rules (Net.delete_term rule_eq (pattern, rule)))) context
   handle Net.DELETE => (warning ("synthesize rule '" ^ More_Binding.here name ^ "' not in rules: " ^ rules_name); context)
 end

fun del_split_rule rules_name only_schematic_goal name priority var_names thm context =
  gen_del_split_rule rules_name only_schematic_goal (standard_check_mk_pattern rules_name) name priority var_names thm context


fun gen_add_infer_project_split_rule mk_pattern infer split rules_name {only_schematic_goal} name priority var_names more_var_names thm context =
 let
   val _ = assert (not (null var_names)) "gen_add_infer_project_split_rule: expecting at least one variable name"
   fun get_var name = Term.add_vars (Thm.prop_of thm) [] |> filter (fn ((n, _),_) => n = name)
     |> distinct (op =) |> the_single |> fst

   val concl = Thm.concl_of thm
   val ctxt = Context.proof_of context
   val pattern = mk_pattern ctxt (~1) concl
   val more_vars = map get_var more_var_names


   val (split, cache) = Fun_Cache.create_handler (Binding.map_name (fn name => (rules_name ^ ": " ^ name)) name)
     (fn c => @{make_string} c) Bin.Bintab.empty Bin.Bintab.lookup Bin.Bintab.update split
   val arity_var = Term.add_vars concl [] |> filter (fn ((n, _),_) => n = hd var_names) |> hd |> fst
   val _ = assert (member (op =) (map fst (Term.add_vars pattern [])) arity_var)
        ("gen_add_infer_project_split_rule: variable ^ '" ^ @{make_string} arity_var ^ "' ^ must be present in pattern and rule-conclusion")


   val rule = mk_infer_project_split_rule name priority only_schematic_goal thm pattern (arity_var::more_vars) split cache infer

   val _ = verbose_msg 8 ctxt (fn _ => Pretty.string_of (Pretty.block (Pretty.breaks [
     Pretty.str ("adding infer-project-split rule '" ^ More_Binding.here (#name rule)),
     Pretty.str_list "(" ")" [
       "mode: " ^ @{make_string} (#mode rule),
       "arity_var: " ^ @{make_string} arity_var,
       "more_vars: " ^ @{make_string} more_vars],
     Pretty.str ("with pattern: \n " ^ Syntax.string_of_term ctxt pattern)])))
 in
   (split, Data.map (Name_Space.map_table_entry rules_name
            (map_rules (Net.insert_term_safe rule_eq (pattern, rule)))) context)
 end

fun add_infer_project_split_rule rules_name only_schematic_goal infer split name priority var_names more_var_names thm context =
 gen_add_infer_project_split_rule (standard_check_mk_pattern rules_name) infer split
   rules_name only_schematic_goal name priority var_names more_var_names thm context

fun gen_add_project_split_rule mk_pattern split rules_name {only_schematic_goal} name priority prj_name thm context =
 let
   val concl = Thm.concl_of thm
   val ctxt = Context.proof_of context
   val pattern = mk_pattern ctxt (~1) concl
   val prj_var = Term.add_vars (Thm.prop_of thm) [] |> filter (fn ((n, _),_) => n = prj_name)
     |> distinct (op =) |> the_single |> fst

   val (split, cache) = Fun_Cache.create_handler (Binding.map_name (fn name => ("split_rel_nondet_monad: " ^ name)) name)
     (fn c => @{make_string} c) Bin.Bintab.empty Bin.Bintab.lookup Bin.Bintab.update split

   val rule = mk_project_split_rule name priority only_schematic_goal thm pattern prj_var split cache
   val _ = verbose_msg 8 ctxt (fn _ => Pretty.string_of (Pretty.block (Pretty.breaks [
     Pretty.str ("adding project-split rule '" ^ More_Binding.here (#name rule)),
     Pretty.str_list "(" ")" [
       "mode: " ^ @{make_string} (#mode rule),
       "prj_var: " ^ @{make_string} prj_var],
     Pretty.str ("with pattern: \n " ^ Syntax.string_of_term ctxt pattern)])))
 in
   (split, Data.map (Name_Space.map_table_entry rules_name
            (map_rules (Net.insert_term_safe rule_eq (pattern, rule)))) context)
 end

fun add_project_split_rule split rules_name only_schematic_goal name priority prj_name thm context =
  gen_add_project_split_rule (standard_check_mk_pattern rules_name) split
    rules_name only_schematic_goal name priority prj_name thm context

fun add_project_split_rules split rules_name only_schematic_goal = fold_map (fn (name, priority, prj_name, thm) =>
  add_project_split_rule split rules_name only_schematic_goal name priority prj_name thm)

fun prep_rule {only_schematic_goal} opt_tac mk_pattern name priority thm ctxt =
  let
    val concl = Thm.concl_of thm    
    val pattern = mk_pattern ctxt (~1) concl
    val rule = case opt_tac of SOME tac => mk_tac_rule name priority pattern thm tac | NONE => mk_simple_rule name priority pattern only_schematic_goal thm;
  in
    (pattern, rule)
  end

fun gen_add_rule rules_name only_schematic_goal opt_tac mk_pattern name priority thm context =
  let
    val ctxt = Context.proof_of context
    val (pattern, rule) = prep_rule only_schematic_goal opt_tac mk_pattern name priority thm ctxt
    val _ = verbose_msg 8 ctxt (fn _ => "adding rule '" ^ More_Binding.here name ^ "' with pattern: \n " ^
         Syntax.string_of_term ctxt pattern)
  in
    (Data.map (Name_Space.map_table_entry rules_name
         (map_rules (Net.insert_term_safe rule_eq (pattern, rule)))) context)
  end

fun gen_del_rule rules_name only_schematic_goal opt_tac mk_pattern name priority thm context =
  let
    val ctxt = Context.proof_of context
    val (pattern, rule) = prep_rule only_schematic_goal opt_tac mk_pattern name priority thm ctxt
    val _ = verbose_msg 8 ctxt (fn _ => "deleting rule '" ^ More_Binding.here name ^ "' with pattern: \n " ^
         Syntax.string_of_term ctxt pattern)
  in
    Data.map (Name_Space.map_table_entry rules_name
         (map_rules (Net.delete_term(*_safe*) rule_eq (pattern, rule)))) context
    handle Net.DELETE => (warning ("synthesize rule '" ^ More_Binding.here name ^ "' not in rules: " ^ rules_name); context)
  end

fun add_rule rules_name only_schematic_goal name priority thm context
  = gen_add_rule rules_name only_schematic_goal NONE (standard_check_mk_pattern rules_name) name priority thm context
fun add_rules rules_name only_schematic_goal = fold (fn (name, priority, thm) => add_rule rules_name only_schematic_goal name priority thm)

fun add_rule_attrib rules_name name priority only_schematic_goal = Thm.declaration_attribute (add_rule rules_name name priority only_schematic_goal)

fun del_rule rules_name only_schematic_goal name priority thm context
  = gen_del_rule rules_name only_schematic_goal NONE (standard_check_mk_pattern rules_name) name priority thm context
fun del_rule_attrib rules_name name priority only_schematic_goal = Thm.declaration_attribute (del_rule rules_name name priority only_schematic_goal)

fun add_rule_most_generic_pattern rules_name only_schematic_goal name priority  thm context
  = gen_add_rule rules_name only_schematic_goal NONE (most_generic_mk_pattern rules_name) name priority thm context
fun add_rule_most_generic_pattern_attrib rules_name name priority only_schematic_goal = 
  Thm.declaration_attribute (add_rule_most_generic_pattern rules_name name priority only_schematic_goal)


fun add_simple_rule rules_name only_schematic_goal = gen_add_rule rules_name only_schematic_goal NONE (K (K I))
fun add_simple_rules rules_name only_schematic_goal = fold (fn (name, priority, thm) => add_simple_rule rules_name only_schematic_goal name priority thm)

fun add_tac_rule rules_name tac name priority thm context =
  gen_add_rule rules_name {only_schematic_goal = false} (SOME tac) (standard_check_mk_pattern rules_name) name priority thm context
fun add_tac_rules rules_name tac = fold (fn (name, priority, thm) => add_tac_rule rules_name tac name priority thm)

fun add_pattern_tac_rule rules_name tac name priority pattern context =
  gen_add_rule rules_name {only_schematic_goal = false} (SOME tac) (K (K (K pattern))) name priority bogus_thm context

fun arity_string mode arity =
  case mode of
    One => string_of_int (Bin.int_of_bin arity)
  | No_Projection => string_of_int (Bin.int_of_bin arity)
  | _ => Bin.string_of_bin arity

fun string_of_mode mode =
  case mode of
     One => "arity"
   | No_Projection => "arity"
   | _ => "projection"


fun resolve_split_thm rules_name ctxt =
  let
    val rules = get_rules ctxt rules_name |> the |> #rules
  in
    SUBGOAL (fn (t, i) =>
      let
        val concl = Utils.concl_of_subgoal' ctxt t
      in
        case Net.match_term rules concl of (* FIXME: I guess we should make pattern of concl just as in resolve_tacs*) 
          [] => (verbose_msg 2 ctxt (fn _ => "resolve_split_thm: no match found"); no_tac)
        | rs =>
          let
            val _ = verbose_msg 2 ctxt (fn _ => "resolve_split_thm: rules potentially matching:" ^
              Pretty.string_of (Pretty.list "[" "]" (map (Pretty.str o More_Binding.here o #name) rs)))
            val ctxt = Context_Position.set_visible false ctxt
            fun split_rule r =
              let
                val n = #derive_arity r bempty ctxt concl
                val tac = the_default (fn ctxt => 
                     let 
                       val splitted_rule = #split r n; 
                     in resolve_tac ctxt [splitted_rule] end) (#tac r)
              in if null n then NONE else SOME (#priority r, (#name r,#mode r, n),
                tac ctxt) end;

            val split_rules = map_filter split_rule rs |> sort (rev_order o int_ord o apply2 (#1))
            val _ = verbose_msg 2 ctxt (fn _ => ("resolve_split_thm: trying rules: " ^
               Pretty.string_of (Pretty.list "[" "]"
                  ((map (Pretty.str o (fn (b, mode, n) => More_Binding.here b ^ enclose " " ":" (string_of_mode mode) ^ arity_string mode n) o #2) split_rules)))))
          in Utils.verbose_print_subgoal_tac 4 "before resolve" ctxt i THEN
             FIRST' (map #3 split_rules) i end
      end)
  end

fun resolve_tacs ({rules, mk_patterns}:rules) ctxt goal =
  let
    val (bounds, concl) = Utils.strip_concl_of_subgoal_open (Thm.term_of goal)
    val maxidx = Thm.maxidx_of_cterm goal
    val benv = (bounds, maxidx)
    val concl = first_mk_pattern mk_patterns ctxt maxidx concl
  in
    case Net.match_term rules concl |> sort rule_ord of
      [] => (verbose_msg 3 ctxt (fn _ => "resolve_tacs: no match found"); [])
    | rs =>
      let
        val _ = verbose_msg 2 ctxt (fn _ => "resolve_tacs: rules potentially matching:" ^
          Pretty.string_of (Pretty.list "[" "]" (map (Pretty.str o More_Binding.here o #name) rs)))
        fun split_rule r =
          let
            val n = #derive_arity r benv ctxt concl
            val tac = case #tac r of
                        SOME tac => (fn i => CT.CONTEXT_TACTIC' (fn ctxt => tac ctxt i))
                      | NONE => (CT.only_schematic_resolve_consumes_assm_tac (#only_schematic_goal r) [#split r n])
          in if null n then NONE else SOME (#priority r, (#name r,#mode r, n, #only_schematic_goal r), tac) end;

        val split_rules = map_filter split_rule rs
        val _ = verbose_msg 2 ctxt (fn _ => ("resolve_tacs: trying rules: " ^
           Pretty.string_of (Pretty.list "[" "]"
              ((map (Pretty.str o (fn (b, mode, n, only_schematic_goal) => More_Binding.here b ^ enclose " " ":" (string_of_mode mode) ^ arity_string mode n ^
                      (if only_schematic_goal then " (only_schematic_goal)" else "")) o #2) split_rules)))))
      in map (fn (_, (name, _ , _, _), tac) => (name, tac)) split_rules end
  end

fun resolve_tacs' ruless ctxt = CT.concat_goal_funs (map (fn rules => resolve_tacs rules ctxt) ruless)

(** setup **)


(* helpers *)
fun snoc x [] = [x]
  | snoc x (y::ys) = y::snoc x ys

val collect_vars = fold_aterms (fn Var v => snoc v | _ => I);

fun dest_pattern_scheme ctxt (t as @{term_pat \<open>Trueprop ?X\<close>}) =
  let
    val (head, args) = strip_comb X
    fun dest_var (("_dummy_", i), _) = NONE
      | dest_var (((x, _),_)) = SOME x

    val vars = [] |> fold collect_vars args |> map_filter dest_var
    val dups = duplicates (op =) vars
    val _ = if null dups then ()
            else error ("dest_pattern_scheme: duplicate variables: " ^ @{make_string} dups ^
                    " in " ^ quote (Syntax.string_of_term ctxt t))
  in
    (head, vars)
  end

fun check_pattern_scheme rules_name ctxt str =
  let
     val pat = Proof_Context.read_term_pattern ctxt str
     val (_, vars) =  pat |> dest_pattern_scheme ctxt
     val _ = if rules_name = "" then pat else check_fresh_mk_pattern rules_name ctxt (~1) pat
  in
    (pat, vars)
  end

fun fresh_var maxidx (Var ((n, i), T)) = Var (("_" ^ n, maxidx + 1), T)

fun get_maxidx maxidx t =
    if maxidx < 0
    then maxidx_of_term t
    else maxidx




structure Rules_Cache = Proof_Data (
  type T = thm Net.net;
  val init = K Net.empty;
)

local
  fun success env = (true, env)
  fun fail env = (false, env)
  fun bind (true, env) f = f env
    | bind (false, env) _ = (false, env)
in
fun gen_rule_eq (tm1, tm2) env =
  if pointer_eq (tm1, tm2) then success env
  else
    (case (tm1, tm2) of
      (t1 $ u1, t2 $ u2) => bind (gen_rule_eq (t1, t2) env) (gen_rule_eq (u1, u2))
    | (Abs (_, T1, t1), Abs (_, T2, t2)) => if T1 = T2 then gen_rule_eq (t1, t2) env else fail env
    | (Var (n1, T1), Var (n2, T2)) =>
         if T1 = T2 then
           if n1 = n2 then success env
           else
             (case Vartab.lookup env n1 of
                SOME x => if x = n2 then success env else fail env
              | NONE => success (Vartab.update (n1, n2) env))
         else fail env
    | (a1, a2) => if a1 = a2 then success env else fail env);
end

fun raw_rule_eq (tm1, tm2) = fst (gen_rule_eq (tm1, tm2) Vartab.empty)

(* alpha equivalence modulo renaming of schematic variables *)
val eq_rule = raw_rule_eq o apply2 Thm.full_prop_of


fun norm_rule ctxt thm =
  let
    val rule = thm |> Raw_Simplifier.norm_hhf ctxt |> Variable.gen_all ctxt (*|> Thm.strip_shyps |> Drule.zero_var_indexes;*)
  in
    Thm.flexflex_rule (SOME ctxt) rule |> Seq.hd
  end

fun match_cache check index lift ({mk_patterns,...}:rules) ctxt goal =
  let
    val concl = Utils.concl_of_subgoal_open (Thm.term_of goal)
    val maxidx = Thm.maxidx_of_cterm goal
    val concl = first_mk_pattern mk_patterns ctxt maxidx concl |> index
  in
    if check NONE concl then
      let
        val net = Rules_Cache.get ctxt
        val thms = Net.match_term net concl

        val _ = verbose_msg 5 ctxt
          (fn _ => "match_cache (" ^ "#content = " ^ string_of_int (Net.content net |> length) ^
                   "): found " ^ string_of_int (length thms) ^ " for: " ^
                    Syntax.string_of_term ctxt concl ^ "\n " ^ string_of_thms ctxt thms)
        val (fails, proofs) = Utils.split_filter (exists (fn p => p = @{term "PROP FALSE"}) o Thm.prems_of) thms

      in CT.FIRST' ([CT.resolve_assm_tac proofs] @ [CT.resolve_tac fails] @ map (lift goal) proofs) end
    else (verbose_msg 6 ctxt (fn _ => "match_cache skipped"); K CT.no_tac)
  end

fun update_cache check index ({mk_patterns,...}:rules) timing thm ctxt =
  let
    fun dest_FALSE @{term_pat \<open>PROP FALSE \<Longrightarrow> PROP ?P\<close>} = P
      | dest_FALSE t = t
    val concl = thm |> Thm.prop_of |> dest_FALSE |> Utils.concl_of_subgoal_open
  in
    if check (SOME timing) concl then
      let
         val rule = norm_rule ctxt thm
         val concl = Utils.concl_of_subgoal_open (Thm.prop_of rule)
         val maxidx = Thm.maxidx_of rule
         val concl = first_mk_pattern mk_patterns ctxt maxidx concl |> index
         val _ = verbose_msg 5 ctxt (fn _ => "update_cache rule: " ^ Thm.string_of_thm ctxt rule ^ "\n pattern: " ^  Syntax.string_of_term ctxt concl)
      in ctxt |> Rules_Cache.map (Net.insert_term_safe eq_rule (concl, rule)) end
    else (verbose_msg 6 ctxt (fn _ => "update_cache skipped"); ctxt)
  end


fun gen_cond_cache check index lift rules: CT.ctxt_cache = {
 lookup = match_cache check index lift rules,
 insert = update_cache check index rules,
 propagate = fn current => Rules_Cache.map (K (Rules_Cache.get current))
}

(* parser *)

fun comma_list inner =
      (inner >> (fn a => [a])) ||
          (Args.parens (inner -- (Scan.repeat (Args.$$$ "," -- inner >> snd)) >> (fn (a, b) => a :: b)))

val pattern = Parse.embedded_inner_syntax -- (Scan.optional (((comma_list Args.name))) [])
val pattern_decl = Parse.name_position --| \<^keyword>\<open>=\<close> -- pattern
val pattern_decls = Parse.and_list pattern_decl


(* ML antiquotations *)

fun print_tuple f = enclose "(" ")" o commas o map f;

local
open ML_Syntax

fun typ_pat (Type arg) = "Term.Type " ^ print_pair print_string (print_list typ_pat) arg
  | typ_pat (TFree arg) = "Term.TFree " ^ print_pair print_string print_sort arg
  | typ_pat (TVar arg) = "_";

val atom = enclose "(" ")"
fun app x y = atom x ^ " $ " ^ atom y

fun as_pat skeleton n t =
  if skeleton then n else atom (implode_space [n, "as", t])

fun abs skeleton T x bdy = enclose "Abs (" ")" (x ^ ", " ^ as_pat skeleton (x ^ "T") (typ_pat T) ^ ", " ^ bdy)



fun combine f g c n =
  let
    val (n1, v1) = f n
    val (n2, v2) = g n1
  in (n2, c v1 v2) end


fun atm term_placeholder n = (n + 1, term_placeholder ^ string_of_int n)
fun atm_dummy n = (n + 1, "_")

fun strip_dummy "_dummy_" = "dummy_"
  | strip_dummy s = s

fun var sfx (x, i) = (if i <= 0 then strip_dummy x else strip_dummy x ^ string_of_int i) ^ sfx
fun var_type T sfx (x, i) = enclose "Var (" ")" (var sfx (x,i) ^ ", " ^ T )
val var_dummy = "_"


fun aterm (Const arg) = "Term.Const " ^ print_pair print_string typ_pat arg
  | aterm (Free arg) = "Term.Free " ^ print_pair print_string typ_pat arg
  | aterm (Bound i) = "Term.Bound " ^ print_int i
  | aterm t = raise TERM ("aterm: can only print atomic terms", [t])


fun gen_term skeleton var atm t n =
  case t of
    t1 $ t2 => combine (gen_term skeleton var atm t1) (gen_term skeleton var atm t2) app n
  | Abs (_, T, t1) => combine atm (gen_term skeleton var atm t1) (abs skeleton T) n
  | Var (x, _) => (n, var x)
  | _ => let val (n, a) = atm n in (n, as_pat skeleton a (aterm t)) end


fun term skeleton var atm t = gen_term skeleton var atm t 1 |> snd

fun term_plain skeleton sfx = term skeleton (var sfx)
fun term_wildcard skeleton sfx = term skeleton (var_type "_" sfx)
fun term_dummy skeleton sfx = term skeleton (var_type "dummyT" sfx)

fun indent n x = space_implode "" (replicate n " ") ^ x
fun indents n x = x |> space_explode "\n" |> map (indent n) |> cat_lines

fun let_expr bindings expr =
 cat_lines
    (["let"] @
        map (indent 2) bindings @
     ["in", indent 2 expr, "end"])

fun val_binding v t = implode_space ["val", v, "=", t]

fun lam_pat args bdy =
  let
    val heading = map (fn n => implode_space ["fn", n, "=>"]) args |> implode_space
    val match_default = "| _ => raise Match"
  in
    atom (cat_lines [heading,  indents 4 (atom bdy), indent 4 match_default])
  end

fun apply f args = implode_space (f :: map atom args)


in

fun mk_pattern atm var_pattern var_infer var_result t =
  let

  in
    (let_expr
       [val_binding (term_wildcard true "" atm_dummy t) (ML_Syntax.print_term t)]
       (lam_pat ["ctxt", "mi", as_pat false "t" (term false var_pattern atm t)]
         (let_expr
            [val_binding "mi" (apply "Synthesize_Rules.get_maxidx" ["mi","t"]),
             val_binding "ctxt" "ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern"]
            (apply
              (lam_pat [(term true var_infer atm t)]
                (term true var_result atm t))
              [apply "singleton" [apply "Type_Infer_Context.infer_types" ["ctxt"], term_dummy true "" atm t] ]))))
  end

fun number_suffixes s = s |> Symbol.explode |> take_suffix (Symbol.is_digit) |> read_int |> fst
fun unique_suffix xs = map number_suffixes xs |> List.foldl Int.max 0 |> (fn n => n + 1) |> string_of_int

fun gen_pattern_fun rules_name ctxt (pattern_str, synth_args) =
  let
    val (t, all_args) = check_pattern_scheme rules_name ctxt pattern_str
    val sfx = unique_suffix all_args
    val atm = atm ("t" ^ sfx ^ "_")
    val _ = if not (subset (op =) (synth_args, all_args))
            then error ("mk_synthesize_pattern: synthesize argument(s) " ^ print_tuple I synth_args ^
                        " have to be subset of " ^ print_tuple I all_args)
            else ()
    fun gen_var synth other (arg, i) = if member (op =) synth_args arg orelse String.isPrefix "_dummy_" arg
                      then synth (arg, i)
                      else other (arg, i)

    val var_pattern = gen_var (K var_dummy) (var sfx)
    val var_result = gen_var
          (fn (arg, i) => "Synthesize_Rules.fresh_var mi " ^ var "" (arg, i))
          (fn (arg, i) => "Utils.open_beta_norm_eta " ^ suffix sfx arg)
    val var_infer = gen_var (var "") (K var_dummy)

    val result = mk_pattern atm var_pattern var_infer var_result t

    val _ = Utils.verbose_msg 4 ctxt (fn _ => ("gen_pattern_fun: " ^ result))
  in
    result
  end
end
(* commands *)

fun ml_from_pattern_decl rules_name ctxt =
  ML_Syntax.print_pair ML_Syntax.make_binding (gen_pattern_fun rules_name ctxt)

fun ml_from_pattern_decls rules_name ctxt =
  ML_Syntax.print_list (ml_from_pattern_decl rules_name ctxt)

fun gen_add_pattern prep rules_name decls lthy =
  let
    val (pos, lexed) = prep lthy decls
    val (name, _) = check (Context.Proof lthy)
         (Binding.name_of rules_name, Binding.pos_of rules_name)
  in
    lthy |> (
    ML_Context.expression pos
     (ML_Lex.read
       ("Theory.local_setup (Synthesize_Rules.add_mk_patterns " ^ ML_Syntax.print_string name)  @
           lexed  @ ML_Lex.read ")")
    |> Context.proof_map)
  end


val add_pattern_ml = gen_add_pattern (fn _ => fn source => (Input.pos_of source, ML_Lex.read_source source))
fun add_pattern_decls rules_name decls lthy =
  let
    val (name, _) = check (Context.Proof lthy) (Binding.name_of rules_name, Binding.pos_of rules_name)
  in
    lthy
     |> fold (gen_add_pattern (fn ctxt => fn decls => (Position.none, ML_Lex.read (ml_from_pattern_decls name ctxt decls))) rules_name)
        (map single decls)
  end

fun print_rules_cmd name term_opt lthy =
  let
    val (name, _)  = check (Context.Proof lthy) name
    val term_opt = Option.map (Proof_Context.read_term_pattern lthy) term_opt
    val _ = print_rules (Context.Proof lthy) name term_opt
  in
    lthy
  end
end

