structure With_Type : sig 
type with_type_info = {
  (* Name of the class that is being registered (xxx in the following comments). *)
  class: class,
  (* Name of the WITH_TYPE_CLASS_xxx constant.
     It has to be of type \<open>'rep set \<Rightarrow> REP_OPS \<Rightarrow> bool\<close> for some type REP_OPS.
     It describes which carrier sets and class operations (on the concrete type) are valid. *)
  rep_class: string,
  (* Name of the WITH_TYPE_REL_xxx constant.
     It has to be of type \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> REP_OPS \<Rightarrow> ABS_OPS\<close>.
     It transforms a relation between the concrete/abstract type into one between
     the operations on the concrete/abstract type.
     ABS_OPS must be the tuple of the class parameters (e.g., (plus,zero,minus,uminus)).
     If the class has no parameters (and no constant class.xxx is defined), then ABS_OPS=unit (and rep_rel r = (=)),
     if the class has no parameters (and class.xxx is defined), then ABS_OPS=TYPE('abs) (and rep_rel r = rel_unit_itself).     *)
  rep_rel: string,
  (* Names of the parameters of the class.
     E.g., ["plus","zero",\<dots>]. *)
  param_names: string list,
  (* Wellformedness theorem. It must say
     \<open>with_type_wellformed REP_CLASS ?S REP_REL\<close>
     (here REP_CLASS, REP_REL are the constants named by rep_class, rep_rel above.) *)
  with_type_wellformed: thm,
  (* Transfer theorem. It must say:
     \<open>bi_unique ?r \<Longrightarrow> right_total ?r \<Longrightarrow> (REP_REL ?r ===> (\<longleftrightarrow>)) (REP_CLASS (Collect (Domainp ?r))) CLASS'\<close>
     Here CLASS' is the constant defining the class (class.xxx), but uncurried (if it has several parameters),
     e.g., CLASS' := (\<lambda>(plus,zero). class.monoid_add plus zero).
     When the class has no defining constant (e.g., type class \<open>type\<close>), then transfer=NONE. *)
  transfer: thm option,
  (* Wellformedness property for REP_REL for operation-less classes. It must say:
     \<open>bi_unique ?r \<Longrightarrow> right_total ?r \<Longrightarrow> (REP_REL ?r) ?p TYPE(?'abs)\<close>
     Only needed if the class has a defining constant, but no operations.
     (I.e., the defining constant is of type \<open>'a itself \<Rightarrow> bool\<close>, cf. e.g. class.finite) *)
  rep_rel_itself: thm option
}

(* Register a `with_type_info` for a new class. *)
val add_with_type_info_global : with_type_info -> theory -> theory
(* TODO Check if all the requirements are satisfied *)

val add_with_type_info_generic : with_type_info -> Context.generic -> Context.generic

val morphism : Morphism.morphism -> with_type_info -> with_type_info

val cancel_with_type : Proof.context -> thm -> thm

val with_type_parse_translation : Proof.context -> term list -> term

val with_type_print_translation : Proof.context -> typ -> term list -> term

val get_with_type_info_by_class : Proof.context -> class -> with_type_info option

val with_type_mp_tac : Position.T -> thm list -> context_tactic

val with_type_case_cmd : binding option list -> Proof.state -> Proof.state

(* For debugging purposes only. *)
val get_all_type_info : Proof.context -> {
  by_class: with_type_info Symtab.table,
  by_const: with_type_info Symtab.table }

end = struct

val protect_conv = Conv.rewr_conv (@{thm Pure.prop_def[symmetric]})
val unprotect_conv = Conv.rewr_conv (@{thm Pure.prop_def})
fun protect_thm thm = Conv.fconv_rule protect_conv thm 
fun unprotect_thm thm = Conv.fconv_rule unprotect_conv thm 

fun unify_prems_12 thm = 
  (@{lemma \<open>PROP Pure.prop (PROP A \<Longrightarrow> PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP Pure.prop (PROP A \<Longrightarrow> PROP B)\<close> 
       by (unfold Pure.prop_def, rule distinct_prems_rl)}
    OF [protect_thm thm]) |> unprotect_thm

type with_type_info = {
  class: class,
  rep_class: string,
  rep_rel: string,
  param_names: string list,
  with_type_wellformed: thm, 
  transfer: thm option,
  rep_rel_itself: thm option
}

fun morphism m ({class, rep_class, rep_rel, with_type_wellformed, transfer, rep_rel_itself, param_names} : with_type_info) : with_type_info =
  {class=class, rep_class=rep_class, rep_rel=rep_rel, 
    with_type_wellformed = Morphism.thm m with_type_wellformed,
    transfer = Option.map (Morphism.thm m) transfer,
    param_names = param_names,
    rep_rel_itself = Option.map (Morphism.thm m) rep_rel_itself}

structure With_Type_Data = Generic_Data (
  type T = { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table }
  val empty = { by_class = Symtab.empty, by_const = Symtab.empty }
  fun merge ({by_class, by_const}, {by_class=by_class', by_const=by_const'}) =
    {by_class = Symtab.merge (K true) (by_class, by_class'),
     by_const = Symtab.merge (K true) (by_const, by_const')}
)

fun check_with_type_info _ _ = ()

fun add_with_type_info_generic data context = (check_with_type_info context data;
  With_Type_Data.map (fn {by_class, by_const} => 
    {by_class = Symtab.update (#class data, data) by_class,
     by_const = Symtab.update (#rep_class data, data) by_const}) context
)
val add_with_type_info_global = Context.theory_map o add_with_type_info_generic

fun get_with_type_info_by_const_generic context const = 
  Symtab.lookup (With_Type_Data.get context |> #by_const) const
val get_with_type_info_by_const = get_with_type_info_by_const_generic o Context.Proof

fun get_with_type_info_by_class_generic context class = 
  Symtab.lookup (With_Type_Data.get context |> #by_class) class
val get_with_type_info_by_class = get_with_type_info_by_class_generic o Context.Proof

fun get_all_type_info ctxt = With_Type_Data.get (Context.Proof ctxt)

(* Like Unoverload_Type.unoverload_type, but works if the theorem contains assumptions from the current context. *)
fun unoverload_type_local ctxt tvars thm = let
  val chyps = Thm.chyps_of thm
  val hyps = map Thm.term_of chyps
  val tvars_hyps = fold Term.add_tvars hyps [] |> map fst
  val bad_tvars = inter (op=) (distinct (op=) tvars_hyps) tvars
  val _ = null bad_tvars orelse
          raise THM ("unoverload_type_local: context assumptions contain type variables " ^
                String.concatWith ", " (map string_of_indexname bad_tvars) ^
                " that we are trying to unoverload", 0, [thm])
  val thm_no_assm = fold Thm.implies_intr chyps thm
  val (tfree_subst, thm_no_tfree) = Thm.varifyT_global' TFrees.empty thm_no_assm 
  val thm_unover = Unoverload_Type.unoverload_type (Context.Proof ctxt) tvars thm_no_tfree
  val skip_nprems = Thm.nprems_of thm_unover - Thm.nprems_of thm_no_tfree
  val _ = skip_nprems >= 0 orelse error ("unoverload_type_local: skip_nprems is negative")
  val _ = forall (fn ((_,s1),(_,s2)) => s1 = s2) tfree_subst orelse
            error ("unoverload_type_local: Thm.varifyT_global' returned inconsistent sorts")
  val tfree_subst' = map (fn ((n,s),nis) => (nis, TFree (n,s) |> Thm.ctyp_of ctxt)) tfree_subst |> TVars.make
  val thm_tfree = Thm.instantiate (tfree_subst', Vars.empty) thm_unover
  val all_prems = Assumption.all_prems_of ctxt
  fun remove_hyp i thm : thm = case Seq.pull (solve_tac ctxt all_prems (i+skip_nprems+1) thm) of
    NONE => raise THM ("unoverload_type_local: solving assumption failed", i+skip_nprems+1, thm :: all_prems)
  | SOME (thm,_) => thm
  val thm''' = fold remove_hyp (hyps |> map_index fst |> rev) thm_tfree
  in thm''' end


fun cancel_with_type ctxt thm = let
  datatype class_premise = CLASS_PREMISE_NONE | CLASS_PREMISE_ITSELF | CLASS_PREMISE_PARAMS
  fun debug (pos : Position.T) m = 
    if false then tracing (Markup.markup (Markup.properties (Position.properties_of pos) Markup.position) "\<^here>" ^ " " ^ m ()) else ()

  val _ = debug\<^here> (fn _ => "thm = " ^ \<^make_string> thm)
  
  (* like thm, but with 'abs replaced by ?'abs, unless it's already a schematic variable *)
  val thm = case Thm.prop_of thm of
      \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type _ _ abs _\<close> $ _ $ _ $ _ $ _ $ _) =>
         (case abs of
            TVar _ => thm
          | TFree (n,_) => Thm.generalize (Names.make1_set n, Names.empty) (Thm.maxidx_of thm + 1) thm
          | _ => raise TYPE ("with_type_cancel: bound type must be a type variable", [abs], [Thm.prop_of thm]))
    | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type ...)", [t])
  val _ = debug\<^here> (fn _ => "thm (after generalizing) = " ^ \<^make_string> thm)

  val (const_class, const_rel, rep_type, abs_type, P, S) = case Thm.prop_of thm of
      \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type rep _ abs _\<close>
                            $ Const(const_class, _) $ Const(const_rel, _)
                            $ S $ _ $ P)
             => (const_class, const_rel, rep, abs, P, S)
    | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type (constant,constant) ...)", [t])
  val _ = debug\<^here> (fn _ => "const_class = " ^ \<^make_string> const_class ^ "; const_rel = " ^ \<^make_string> const_rel ^ "; abs_type = " ^ \<^make_string> abs_type ^ "; P = " ^ \<^make_string> P)

  (* val rep_ctyp = Thm.ctyp_of ctxt rep_type *)
  val S_cterm = Thm.cterm_of ctxt S

  val _ = let val P' = betapplys (P, [Free("Rep", abs_type --> rep_type), Free("abs_ops", dummyT)])  in
            exists_type (exists_subtype (fn T => T=abs_type)) P'
              andalso raise ERROR ("with_type_cancel: body contains type " ^ Syntax.string_of_typ ctxt abs_type ^ " that is supposed to be removed") end

  val abs_type_name = case abs_type of
    TVar (n,_) => n
    | _ => raise TYPE ("with_type_cancel: abstract type must be a type variable (?'something)", [abs_type], [Thm.prop_of thm])
  val _ = debug\<^here> (fn _ => "abs_type_name = " ^ \<^make_string> abs_type_name)
  
  val info = get_with_type_info_by_const ctxt const_class |> the
  val _ = #rep_rel info = const_rel orelse raise TERM ("with_type_cancel: expected relator " ^ #rep_rel info ^ " instead of " ^ const_rel, [Thm.prop_of thm])

  (* class.name (\<dots> using ?'abs::type) \<Longrightarrow> with_type C R S p (\<lambda>_ _. P) *)
  (* class.name part may be absent for some type classes *)
  val unoverloaded = unoverload_type_local ctxt [abs_type_name] thm
  val _ = debug\<^here> (fn _ => "unoverloaded = " ^ \<^make_string> unoverloaded)
  val class_premise = case Thm.nprems_of unoverloaded of
       0 => CLASS_PREMISE_NONE
     | 1 => (case Thm.prems_of unoverloaded |> hd of
               \<^Const_>\<open>Trueprop\<close> $ (_ $ \<^Const_>\<open>Pure.type _\<close>) => CLASS_PREMISE_ITSELF
             | _ => CLASS_PREMISE_PARAMS)
     | _ => raise THM ("with_type_cancel: unoverload_type_local produced more premises", Thm.nprems_of unoverloaded, [thm, unoverloaded])
  val _ = debug\<^here> (fn _ => "class_premise = " ^ \<^make_string> class_premise)

  (* "with_type C R ?S ?p ?P \<Longrightarrow>
      \<exists>Rep Abs. type_definition Rep Abs ?S \<Longrightarrow> \<exists>x. class.name' x" *)
  (* Here class.name' is class.name, possibly uncurried (e.g., \<lambda>(x,y,z) class.name x y z) *)
  (* Only defined if class_premise = CLASS_PREMISE_PARAMS *)
  val with_type_transfer_class = 
    if class_premise = CLASS_PREMISE_PARAMS then
      case #transfer info of SOME transfer => 
        (@{thm with_type_transfer_class} OF [transfer, #with_type_wellformed info])
        |> (Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1) |> Seq.hd |> SOME
         | NONE => raise THM ("with_type_cancel: unoverloading produced a `class.name` premise, but #transfer is NONE", 0, [unoverloaded])
    else
      NONE
  val _ = debug\<^here> (fn _ => "with_type_transfer_class = " ^ \<^make_string> with_type_transfer_class)
 
  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> \<exists>x::?'abs_params2. class.name' x *)
  (* Only defined if class_premise = CLASS_PREMISE_PARAMS *)
  val ex_class = Option.map (fn th => th OF [thm]) with_type_transfer_class
  val _ = debug\<^here> (fn _ => "ex_class = " ^ \<^make_string> ex_class)

  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> class.name' (SOME \<dots>) *)
  (* Only defined if class_premise = CLASS_PREMISE_PARAMS *)
  val class_some = Option.map (fn thm => @{thm someI_ex} OF [thm]) ex_class
  val _ = debug\<^here> (fn _ => "class_some = " ^ \<^make_string> class_some)

  open Conv
  (* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> class.name \<dots> \<dots> \<dots> *)
  (* Only defined if class_premise = CLASS_PREMISE_PARAMS *)
  val uncurry_conv = repeat_conv (rewr_conv @{thm case_prod_beta[THEN eq_reflection]}) |> HOLogic.Trueprop_conv |> implies_concl_conv
  val class_some_uncurried = Option.map (fconv_rule uncurry_conv) class_some
  val _ = debug\<^here> (fn _ => "class_some_uncurried = " ^ \<^make_string> class_some_uncurried)

  (* with_type C R S ?p ?P \<Longrightarrow>\<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> class.name TYPE(?'abs2) *)
  (* Only defined if class_premise = CLASS_PREMISE_ITSELF *)
  val class_type' =
    if class_premise = CLASS_PREMISE_ITSELF then
      case (#transfer info, #rep_rel_itself info) of (SOME transfer, SOME itself) => 
            @{thm with_type_transfer_class2}
            |> Drule.infer_instantiate ctxt [(("S",0), S_cterm)]
            |> (fn thm => thm OF [transfer, #with_type_wellformed info, itself])
            |> (Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1) |> Seq.hd
            (* |> Thm.instantiate' [SOME rep_ctyp] [] *)
            |> SOME
       | (NONE, _) => raise THM ("with_type_cancel: unoverloading produced a `class.name` premise, but #transfer is NONE", 0, [unoverloaded])
       | (_, NONE) => raise THM ("with_type_cancel: unoverloading produced a `class.name TYPE(\<dots>)` premise, but #rep_rel_itself is NONE", 0, [unoverloaded])
    else
      NONE
  val _ = debug\<^here> (fn _ => "class_type' = " ^ \<^make_string> class_type')

  (* type_definition Rep Abs S \<Longrightarrow> class.name TYPE(?'abs2) *)
  (* Only defined if class_premise = CLASS_PREMISE_ITSELF *)
  val class_type = Option.map (fn th => th OF [thm]) class_type'
  val _ = debug\<^here> (fn _ => "class_type = " ^ \<^make_string> class_type)

  val class = case class_premise of
                CLASS_PREMISE_ITSELF => class_type | CLASS_PREMISE_PARAMS => class_some_uncurried | CLASS_PREMISE_NONE => NONE

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> with_type CR Sp (\<lambda>_ _. P) *)
  val unoverloaded' = case class of SOME thm => unoverloaded OF [thm] | NONE => unoverloaded
  val _ = debug\<^here> (fn _ => "unoverloaded' = " ^ \<^make_string> unoverloaded')

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs S [POSSIBLY TWICE!] \<Longrightarrow> P *)
  (* TWICE if class_premise = CLASS_PREMISE_PARAMS or CLASS_PREMISE_ITSELF *)
  val no_with_type = @{thm with_type_prepare_cancel} OF [unoverloaded']
  val _ = debug\<^here> (fn _ => "no_with_type = " ^ \<^make_string> no_with_type)

  (* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs S \<Longrightarrow> P *)
  val no_repetition = 
    if Thm.nprems_of no_with_type = 2 then unify_prems_12 no_with_type else no_with_type
  val _ = debug\<^here> (fn _ => "no_repetition = " ^ \<^make_string> no_repetition)

  val _ = Thm.nprems_of no_repetition = 1 orelse raise THM ("with_type_cancel: could not remove duplicate premise", 0, [no_repetition])

  (* S \<noteq> {} \<Longrightarrow> P *)
  val removed_abs_type = Local_Typedef.cancel_type_definition no_repetition
  val _ = debug\<^here> (fn _ => "removed_abs_type = " ^ \<^make_string> removed_abs_type)
  
  (* S \<noteq> {} *)
  val non_empty = @{thm with_type_nonempty} OF [thm]
  val _ = debug\<^here> (fn _ => "non_empty = " ^ \<^make_string> non_empty)
  val final_thm = removed_abs_type OF [non_empty]
  val _ = debug\<^here> (fn _ => "final_thm = " ^ \<^make_string> final_thm)
  in
    final_thm
  end

fun nth_of_m 0 1 t = t
  | nth_of_m 0 m t = if m <= 1 then raise ERROR "m <= 1" else \<^Const>\<open>fst dummyT dummyT\<close> $ t
  | nth_of_m n m t = if n <= 0 then raise ERROR "n <= 0" else \<^Const>\<open>snd dummyT dummyT\<close> $ (nth_of_m (n-1) (m-1) t)

fun substitute_params term names suffix = let
  val len = length names
  val ops = Free("ops_" ^ suffix, dummyT)
  val names = map (fn name => name ^ "_" ^ suffix) names
  fun subst (t as Const _) = t
    | subst (t $ u) = subst t $ subst u
    | subst (t as Var _) = t
    | subst (t as Bound _) = t
    | subst (Abs (n,T,body)) = Abs(n,T,subst body)
    | subst (t as Free(n,_)) = case find_index (fn m => n=m) names of
        ~1 => t
        | i => nth_of_m i len ops
in subst term end

fun with_type_parse_translation ctxt [typ_term, carrier, ops, prop] = let
  val (typname_raw,sort) = case typ_term of 
    Const ("_ofsort", _) $ Free (_, _) $ Free _ =>
      raise TERM ("with_type_parse_translation: abstract type must be annotated with a type class", [typ_term])
    | Const ("_ofsort", _) $ (Const ("_ofsort", _) $ Free (n, _) $ Free _) $ sort => (n, sort)
    | _ => raise TERM ("parse_translation _with_type: first argument must be a type variable", [typ_term])
  val typname = if typname_raw = "" then raise TERM ("parse_transtation _with_type: empty type variable name", [typ_term])
      else if not (String.isPrefix "'" typname_raw) then raise TERM ("parse_transtation _with_type: type variable name does not start with '", [typ_term])
      else String.extract (typname_raw,1,NONE)
  val class = case Syntax_Phases.decode_sort sort of [class] => class
                        | sort => error ("with_type_parse_translation: abstract type must be annotated with a single class, not " ^ Syntax.string_of_sort ctxt sort)
  val info = case get_with_type_info_by_class ctxt class of SOME info => info
              | NONE => error ("with_type_parse_translation: class "^ Syntax.string_of_sort ctxt [class] ^" not registered for use with \<forall>\<^sub>\<tau>")
  val typ = TFree("'" ^ typname, [class])
  val rep = Free("rep_" ^ typname, dummyT)
  val abs_ops = Free("ops_" ^ typname, dummyT)
  val prop = substitute_params prop (#param_names info) typname
  val prop = Syntax_Trans.abs_tr [rep, Syntax_Trans.abs_tr [abs_ops, prop]]
  val propT = (typ --> dummyT) --> dummyT --> HOLogic.boolT
  (* The "Config.put show_sorts true" is necessary here because otherwise "term_of_typ" ignores sorts. *)
  val prop = Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ prop $ Syntax_Phases.term_of_typ (Config.put show_sorts true ctxt) propT
  in Const(\<^const_name>\<open>with_type\<close>, dummyT) $ Const(#rep_class info, dummyT) $ Const(#rep_rel info, dummyT) $ 
        carrier $ ops $ prop end

  | with_type_parse_translation ctxt [typ_term, carrier, prop] = with_type_parse_translation ctxt [typ_term, carrier, \<^term>\<open>()\<close>, prop]
  | with_type_parse_translation _ Ts = raise TERM ("with_type_parse_translation: called with wrong number of arguments", Ts)

fun with_type_print_translation' ctxt typ args = let
  val [Const(C,_), Const(R,_), S, rep_ops, P (* Abs(_,_, Abs(_,_, Abs(_,_,P))) *)] = args 
  val Type("fun", [_, Type("fun", [Type("fun", [Type("fun", absT), _]), _])]) = typ
  val TFree(absT, abs_sort) = typ |> range_type |> domain_type |> domain_type |> range_type |> domain_type
  val [class] = abs_sort
  val _ = String.isPrefix "'" absT orelse raise Bind
  val suffix = String.extract (absT,1,NONE)
  val C = Lexicon.unmark_const C handle Fail _ => raise Bind
  val R = Lexicon.unmark_const R handle Fail _ => raise Bind
  val SOME info = get_with_type_info_by_class ctxt class
  val _ = C = #rep_class info orelse raise Bind
  val _ = R = #rep_rel info orelse raise Bind
(*    val output_typ = Syntax.const "_ofsort" $ (Syntax.const "_tfree" $ Syntax.free absT) $ 
      (Syntax.const "_sort" $ Syntax.const (Lexicon.mark_class class) ) *)
   val output_typ = Syntax.const "_with_type_sort_annotation" $ (Syntax.const "_tfree" $ Syntax.free absT) $ 
        Syntax.const (Lexicon.mark_class class)
  fun mark_var v = Syntax.const "_bound" $ Syntax.free (v^suffix)
  val P = Term.betapplys (P, [mark_var "rep_", mark_var "ops_"])
  val rep_ops_unit = case rep_ops of Const(\<^const_syntax>\<open>Unity\<close>,_) => true | _ => false
in 
  if rep_ops_unit
  then Const(\<^syntax_const>\<open>_with_type\<close>, dummyT) $ output_typ $ S $ P
  else Const(\<^syntax_const>\<open>_with_type_with\<close>, dummyT) $ output_typ $ S $ rep_ops $ P
end

val with_type_syntax = Attrib.setup_config_bool \<^binding>\<open>with_type_syntax\<close> (K true)

fun with_type_print_translation ctxt typ args = let
  fun no_processing () = fold (fn t => fn u => u $ t) args (Free("with_type", typ))
  val enabled = Config.get ctxt with_type_syntax
  in
    if enabled
    then with_type_print_translation' ctxt typ args handle Bind => no_processing()
    else no_processing()
  end

fun absT_name T = case T of TFree(name, _) => String.extract (name, 1, NONE) | _ => "t"

exception ERROR_IN_TACTIC of unit -> string
fun with_type_mp_tac pos facts (ctxt, st) = let
    val fact = case facts of [fact] => fact
            | _ => raise THM ("with_type_mp: expected exactly one fact", 1, facts)
    val rule = @{thm with_type_mp} OF [fact]
    val (repT, absT, C, S, ops, P, abs_opsT) = case Thm.cprem_of st 1 |> Thm.term_of of
             \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type repT rep_opsT absT abs_opsT\<close> 
                                    $ C $ _ $ S $ ops $ P)
                   => (repT, absT, C, S, ops, P, abs_opsT)
             | _ => raise ERROR_IN_TACTIC (fn _ => "with_type_mp: goal of the wrong form")
    val rep_name = "rep_" ^ absT_name absT
    val abs_ops_name = "ops_" ^ absT_name absT
    val st = case SINGLE (resolve_tac ctxt [rule] 1) st of SOME st => st
              | NONE => raise ERROR_IN_TACTIC (fn _ => "with_type_mp: could not apply with_type_mp")
    val prems_of_subgoal = Thm.cprem_of st (Thm.nprems_of st) |> Thm.term_of |> Logic.strip_assums_hyp
          |> map (fn t => Abs(rep_name, absT --> repT, Abs (abs_ops_name, abs_opsT, t)))
    val assm_bij :: assm_class :: assm_prem :: _ = prems_of_subgoal
    val rule_case = Rule_Cases.Case {
          fixes = [(Binding.make (rep_name, pos), absT --> repT), (Binding.make (abs_ops_name, pos), abs_opsT)],
          assumes = [("bij", [assm_bij]), ("class", [assm_class]), ("premise", [assm_prem])], 
          binds = [(("concl",0), SOME P)],
          cases = []}
    val ctxt = Proof_Context.update_cases [("with_type_mp", SOME rule_case)] ctxt
  in
    Seq.single (ctxt, st) |> Seq.make_results
  end
  handle ERROR_IN_TACTIC error => Seq.single (Seq.Error error)

(* TODO: print additional informative text when invoked *)
fun with_type_case_cmd args state : Proof.state = let
    val state = Proof.case_ ((Binding.empty, []), (("with_type_mp", Position.none), args)) state
    val thm_bij = Proof_Context.get_fact_single (Proof.context_of state) (Facts.named "local.with_type_mp.bij")
    val thm_class = Proof_Context.get_fact_single (Proof.context_of state) (Facts.named "local.with_type_mp.class")
    val thm_premise = Proof_Context.get_fact_single (Proof.context_of state) (Facts.named "local.with_type_mp.premise")
    val thm_type_def = @{thm type_definition_bij_betw_iff[THEN iffD2]} OF [thm_bij]
    val (rep, abs, S) = case Thm.prop_of thm_type_def of
        \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>type_definition _ _\<close> $ rep $ abs $ S) => (rep,abs,S)
    val \<^Type>\<open>fun absT _\<close> = fastype_of rep
    val state = Interpretation.interpret
              ([(\<^locale>\<open>type_definition\<close>, (("type_definition_" ^ absT_name absT,true), (Expression.Positional [SOME rep, SOME abs, SOME S], [])))],
              [(Binding.make ("i_dont_know_where_this_ends_up", Position.none), NONE, NoSyn)]) state
    val state = Proof.local_future_terminal_proof 
                    (((Method.Basic (Method.fact [thm_type_def]), Position.no_range), NONE)) state
    val state = Proof.set_facts [thm_type_def, thm_class, thm_premise] state
  in state end

end
