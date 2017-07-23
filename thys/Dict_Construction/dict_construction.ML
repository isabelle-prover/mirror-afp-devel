signature DICT_CONSTRUCTION =
sig
  type const

  type 'a sccs = (string * 'a) list list

  val annotate_code_eqs: local_theory -> string list -> (const sccs * local_theory)
  val new_names: local_theory -> const sccs -> (string * const) sccs
  val symtab_of_sccs: 'a sccs -> 'a Symtab.table

  val axclass: class -> local_theory -> Class_Graph.node * local_theory
  val instance: (string * const) Symtab.table -> string -> class -> local_theory -> term * local_theory
  val term: term Symreltab.table -> (string * const) Symtab.table -> term -> local_theory -> (term * local_theory)
  val consts: (string * const) Symtab.table -> (string * const) list -> local_theory -> local_theory

  (* certification *)

  type const_info =
    {fun_info: Function.info option,
     inducts: thm list option,
     base_thms: thm list,
     base_certs: thm list,
     simps: thm list,
     code_thms: thm list}

  type fun_target = (string * class) list * (term * term)

  type dict_thms =
    {base_thms: thm list,
     def_thm: thm}

  type dict_target = (string * class) list * (term * string * class)

  val prove_fun_cert: fun_target list -> const_info -> local_theory -> thm list
  val prove_dict_cert: dict_target -> dict_thms -> local_theory -> thm

  val the_info: Proof.context -> string -> const_info

  (* utilities *)

  val normalizer_conv: Proof.context -> conv
  val cong_of_const: Proof.context -> string -> thm option
  val get_code_eqs: Proof.context -> string -> thm list
  val group_code_eqs: Proof.context -> string list ->
    (string * (((string * sort) list * typ) * ((term list * term) * thm option) list)) list list
end

structure Dict_Construction: DICT_CONSTRUCTION =
struct

open Class_Graph
open Dict_Construction_Util

(** utilities **)

val normalizer_conv = Axclass.overload_conv

fun cong_of_const ctxt name =
  let
    val head =
      Thm.concl_of
      #> Logic.dest_equals #> fst
      #> strip_comb #> fst
      #> dest_Const #> fst
    fun applicable thm =
      try head thm = SOME name
  in
    Function_Context_Tree.get_function_congs ctxt
    |> filter applicable
    |> try hd
  end

fun group_code_eqs ctxt consts =
  let
    val thy = Proof_Context.theory_of ctxt
    val graph = #eqngr (Code_Preproc.obtain true { ctxt = ctxt, consts = consts, terms = [] })

    fun mk_eqs name = name
      |> Code_Preproc.cert graph
      |> Code.equations_of_cert thy ||> these
      ||> map (apsnd fst o apfst (apsnd fst o apfst (map fst)))
      |> pair name
  in
    map (map mk_eqs) (rev (Graph.strong_conn graph))
  end

fun get_code_eqs ctxt const =
  AList.lookup op = (flat (group_code_eqs ctxt [const])) const
  |> the |> snd
  |> map snd
  |> cat_options
  |> map (Conv.fconv_rule (normalizer_conv ctxt))

(** certification **)

type const_info =
  {fun_info: Function.info option,
   inducts: thm list option,
   base_thms: thm list,
   base_certs: thm list,
   simps: thm list,
   code_thms: thm list}

fun morph_const_info phi {fun_info, inducts, base_thms, base_certs, simps, code_thms} =
  {fun_info = Option.map (Function_Common.transform_function_data phi) fun_info,
   inducts = Option.map (map (Morphism.thm phi)) inducts,
   base_thms = map (Morphism.thm phi) base_thms,
   base_certs = map (Morphism.thm phi) base_certs,
   simps = map (Morphism.thm phi) simps,
   code_thms = code_thms (* sic *)}

type fun_target = (string * class) list * (term * term)

type dict_thms =
  {base_thms: thm list,
   def_thm: thm}

type dict_target = (string * class) list * (term * string * class)

fun fun_cert_tac base_thms base_certs simps code_thms =
  SOLVED' o Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
    let
      fun is_ih prem =
        Thm.prop_of prem |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop |> can HOLogic.dest_eq

      val (ihs, certs) = partition is_ih prems
      val super_certs = all_edges ctxt |> Symreltab.dest |> map (#subclass o snd)
      val simp_context = (clear_simpset ctxt) addsimps (certs @ super_certs @ base_certs)
      val param_dests = all_nodes ctxt |> Symtab.dest |> maps (#3 o #cert_thms o snd)
      val congs = Function_Context_Tree.get_function_congs ctxt @ map safe_mk_meta_eq @{thms cong}

      val ih_tac =
        resolve_tac ctxt ihs THEN_ALL_NEW
          (TRY' (SOLVED' (Simplifier.simp_tac simp_context)))

      val unfold_new =
        ANY' (map (CONVERSION o rewr_lhs_head_conv) simps)

      val normalize =
        CONVERSION (normalizer_conv ctxt)

      val unfold_old =
        ANY' (map (CONVERSION o rewr_rhs_head_conv) code_thms)

      val oldnew_base_rewr =
        CONVERSION (lhs_conv (Simplifier.rewrite (simp_context addsimps base_thms)))

      val subst_params =
        CONVERSION (lhs_conv (Simplifier.rewrite (simp_context addsimps param_dests)))

      fun walk_congs i = i |>
        ((resolve_tac ctxt [@{thm refl}] ORELSE'
          ih_tac ORELSE'
          Method.assm_tac ctxt ORELSE'
          (resolve_tac ctxt @{thms meta_eq_to_obj_eq} THEN'
            fo_resolve_tac congs ctxt)) THEN_ALL_NEW walk_congs)

      val tacs =
        [unfold_new, normalize, unfold_old, oldnew_base_rewr, subst_params, walk_congs]
    in
      EVERY' tacs 1
    end)

fun dict_cert_tac class def_thm base_thms =
  SOLVED' o Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
    let
      val (intro, sels) = case node ctxt class of
        SOME {cert_thms = (_, intro, _), data_thms = sels, ...} => (intro, sels)
      | NONE => error ("class " ^ class ^ " is not defined")

      val apply_intro =
        resolve_tac ctxt [intro]

      val unfold_dict =
        CONVERSION (Conv.rewr_conv def_thm |> Conv.arg_conv |> lhs_conv)

      val normalize =
        CONVERSION (normalizer_conv ctxt)

      val smash_sels =
        CONVERSION (lhs_conv (Conv.rewrs_conv sels))

      val solve =
        resolve_tac ctxt (@{thm HOL.refl} :: base_thms)

      val finally =
        resolve_tac ctxt prems

      val tacs =
        [apply_intro, unfold_dict, normalize, smash_sels, solve, finally]
    in
      EVERY (map PARALLEL_ALLGOALS tacs)
    end)

fun prepare_dicts classes names lthy =
  let
    val sorts = Symtab.make_list classes

    fun mk_dicts (param_name, (tvar, class)) =
      case node lthy class of
        NONE =>
          error ("unknown class " ^ class)
      | SOME {cert, qname, ...} =>
          let
            val sort = the (Symtab.lookup sorts tvar)
            val param = Free (param_name, Type (qname, [TFree (tvar, sort)]))
          in
            (param, HOLogic.mk_Trueprop (cert dummyT $ param))
          end

    val dict_names = Name.invent_names names "a" classes
    val names = fold Name.declare (map fst dict_names) names
    val (dict_params, prems) = split_list (map mk_dicts dict_names)
  in (dict_params, prems, names) end

fun prepare_fun_goal targets lthy =
  let
    fun mk_eq (classes, (lhs, rhs)) names =
      let
        val (lhs_name, _) = dest_Const lhs
        val (rhs_name, rhs_typ) = dest_Const rhs

        val (dict_params, prems, names) = prepare_dicts classes names lthy

        val param_names = fst (strip_type rhs_typ) |> map (K dummyT) |> Name.invent_names names "a"
        val names = fold Name.declare (map fst param_names) names
        val params = map Free param_names

        val lhs = list_comb (Const (lhs_name, dummyT), dict_params @ params)
        val rhs = list_comb (Const (rhs_name, dummyT), params)

        val eq = Const (@{const_name HOL.eq}, dummyT) $ lhs $ rhs

        val all_params = dict_params @ params
        val eq :: rest = Syntax.check_terms lthy (eq :: prems @ all_params)
        val (prems, all_params) = unappend (prems, all_params) rest

        val eq =
          if is_some (Axclass.inst_of_param (Proof_Context.theory_of lthy) rhs_name) then
            Thm.cterm_of lthy eq |> conv_result (Conv.arg_conv (normalizer_conv lthy))
          else
            eq

        val prop = prems ===> HOLogic.mk_Trueprop eq
      in ((all_params, prop), names) end
  in
    fold_map mk_eq targets Name.context
    |> fst
    |> split_list
  end

fun prepare_dict_goal (classes, (term, _, class)) lthy =
  let
    val cert = case node lthy class of
      NONE =>
        error ("unknown class " ^ class)
    | SOME {cert, ...} =>
        cert dummyT

    val names = Name.context
    val (dict_params, prems, _) = prepare_dicts classes names lthy
    val (term_name, _) = dest_Const term
    val dict = list_comb (Const (term_name, dummyT), dict_params)

    val prop = prems ===> HOLogic.mk_Trueprop (cert $ dict)
    val prop :: dict_params = Syntax.check_terms lthy (prop :: dict_params)
  in
    (dict_params, prop)
  end

fun prove_fun_cert targets {inducts, base_thms, base_certs, simps, code_thms, ...} lthy =
  let
    (* the props contain dictionary certs as prems
       we can't exclude them from the induction because the dicts are part of the function
       definition
       excluding them would mean that applying the induction rules becomes tricky or impossible
       proper fix would be if fun, akin to inductive, supported a "for" clause that marks parameters
       as "not changing" *)
    val (argss, props) = prepare_fun_goal targets lthy
    val frees = flat argss |> map (fst o dest_Free)

    (* we first prove the extensional variant (easier to prove), and then derive the
       contracted variant
       abs_def can't deal with premises, so we use our own version here *)
    val long_thms =
      Goal.prove_common lthy NONE frees [] props (fn {context, ...} =>
        maybe_induct_tac inducts argss [] context THEN
          ALLGOALS (fun_cert_tac base_thms base_certs simps code_thms context))
  in
    map (contract lthy) long_thms
  end

fun prove_dict_cert target {base_thms, def_thm} lthy =
  let
    val (args, prop) = prepare_dict_goal target lthy
    val frees = map (fst o dest_Free) args
    val (_, (_, _, class)) = target
  in
    Goal.prove_future lthy frees [] prop (fn {context, ...} =>
      dict_cert_tac class def_thm base_thms context 1)
  end

(** background data **)

type definitions =
  {instantiations: (term * thm) Symreltab.table, (* key: (class, tyco) *)
   constants: (string * (thm option * const_info)) Symtab.table (* key: constant name *) }

structure Definitions = Generic_Data
(
  type T = definitions
  val empty = {instantiations = Symreltab.empty, constants = Symtab.empty}
  val extend = I
  fun merge ({instantiations = i1, constants = c1}, {instantiations = i2, constants = c2}) =
    if Symreltab.is_empty i1 andalso Symtab.is_empty c1 andalso
       Symreltab.is_empty i2 andalso Symtab.is_empty c2 then
      empty
    else
      error "merging not supported"
)

fun map_definitions map_insts map_consts =
  Definitions.map (fn {instantiations, constants} =>
    {instantiations = map_insts instantiations,
     constants = map_consts constants})

fun the_info ctxt name =
  Symtab.lookup (#constants (Definitions.get (Context.Proof ctxt))) name
  |> the
  |> snd
  |> snd

fun add_instantiation (class, tyco) term cert =
  let
    fun upd phi =
      map_definitions
        (Symreltab.update_new ((class, tyco), (Morphism.term phi term, Morphism.thm phi cert))) I
  in
    Local_Theory.declaration {pervasive = false, syntax = false} upd
  end

fun add_constant name name' (cert, info) lthy =
  let
    val qname = Local_Theory.full_name lthy (Binding.name name')
    fun upd phi =
      map_definitions I (Symtab.update_new (name,
        (qname, (Option.map (Morphism.thm phi) cert, morph_const_info phi info))))
  in
    Local_Theory.declaration {pervasive = false, syntax = false} upd lthy
  end

(** classes **)

fun axclass class =
  ensure_class class
  #>> node_of

(** grouping and annotating constants **)

datatype const =
  Fun of
    {dicts: ((string * class) * typ) list,
     certs: term list,
     param_typs: typ list,
     typ: typ, (* typified *)
     new_typ: typ,
     eqs: {params: term list, rhs: term, thm: thm} list,
     info: Function_Common.info option,
     cong: thm option} |
  Constructor |
  Classparam of
    {class: class,
     typ: typ, (* varified *)
     selector: term (* varified *)}

type 'a sccs = (string * 'a) list list

fun symtab_of_sccs x = Symtab.make (flat x)

fun raw_dict_params tparams lthy =
  let
    fun mk_dict tparam class lthy =
      let
        val (node, lthy') = axclass class lthy
        val targ = TFree (tparam, @{sort type})
        val typ = dict_typ node targ
        val cert = #cert node targ
      in ((((tparam, class), typ), cert), lthy') end
    fun mk_dicts (tparam, sort) = fold_map
      (mk_dict tparam)
      (filter (Class.is_class (Proof_Context.theory_of lthy)) sort)
   in fold_map mk_dicts tparams lthy |>> flat end

fun dict_params context dicts =
  let
    fun dict_param ((_, class), typ) =
      Name.variant (mangle class) #>> rpair typ #>> Free
  in
    fold_map dict_param dicts context
  end

fun get_sel class param typ lthy =
  let
    val ({selectors, ...}, lthy') = axclass class lthy
  in
    case Symtab.lookup selectors param of
      NONE => error ("unknown class parameter " ^ param)
    | SOME sel => (sel typ, lthy')
  end

fun annotate_const name ((tparams, typ), raw_eqs) lthy =
  if Code.is_constr (Proof_Context.theory_of lthy) name then
    ((name, Constructor), lthy)
  else if null raw_eqs then
    (* this detection is reliable, because code equations with overloaded heads are not allowed *)
    let
      val (_, class) = the_single tparams ||> the_single
      val (selector, thy') = get_sel class name (TVar (("'a", 0), @{sort type})) lthy
      val typ = range_type (fastype_of selector)
    in
      ((name, Classparam {class = class, typ = typ, selector = selector}), thy')
    end
  else
    let
      val info = try (Function.get_info lthy) (Const (name, typ))
      val cong = cong_of_const lthy name
      val ((raw_dicts, certs), lthy') = raw_dict_params tparams lthy |>> split_list
      val dict_typs = map snd raw_dicts
      val typ' = typify_typ typ
      fun mk_eq ((raw_params, rhs), SOME thm) =
            let
              val norm = normalizer_conv lthy'
              val transform = Thm.cterm_of lthy' #> conv_result norm #> typify
              val params = map transform raw_params
            in
              if has_duplicates (op =) (flat (map all_frees' params)) then
                (warning "ignoring code equation with non-linear pattern"; NONE)
              else
                SOME {params = params, rhs = rhs, thm = Conv.fconv_rule norm thm}
            end
        | mk_eq _ =
            error "no theorem"
      val const =
        Fun
          {dicts = raw_dicts, certs = certs, typ = typ', param_typs = binder_types typ',
           new_typ = dict_typs ---> typ', eqs = map_filter mk_eq raw_eqs, info = info, cong = cong}
    in ((name, const), lthy') end

fun annotate_code_eqs lthy consts =
  fold_map (fold_map (uncurry annotate_const)) (group_code_eqs lthy consts) lthy

(** instances and terms **)

fun mk_path [] _ _ lthy = (NONE, lthy)
  | mk_path ((class, term) :: rest) typ goal lthy =
    let
      val (ev, lthy') = ensure_class class lthy
    in
      case find_path ev goal of
        SOME path => (SOME (fold_path path typ term), lthy')
      | NONE =>      mk_path rest typ goal lthy'
    end

fun instance consts tyco class lthy =
  case Symreltab.lookup (#instantiations (Definitions.get (Context.Proof lthy))) (class, tyco) of
    SOME (inst, _) =>
      (inst, lthy)
  | NONE =>
      let
        val thy = Proof_Context.theory_of lthy
        val tparam_sorts = param_sorts tyco class thy

        fun print_info ctxt =
          let
            val tvars =
              Name.invent_list [] Name.aT (length tparam_sorts) ~~ tparam_sorts
              |> map TFree
          in
            [Pretty.str "Defining instance ", Syntax.pretty_typ ctxt (Type (tyco, tvars)),
              Pretty.str " :: ", Syntax.pretty_sort ctxt [class]]
            |> Pretty.block
            |> Pretty.writeln
          end

        val ({make, ...}, lthy) = axclass class lthy

        val name = mangle class ^ "__instance__" ^ mangle tyco
        val tparams = Name.invent_names Name.context Name.aT tparam_sorts
        val ((dict_params, _), lthy) = raw_dict_params tparams lthy
          |>> map fst
          |>> dict_params (Name.make_context [name])
        val dict_context = Symreltab.make (flat_right tparams ~~ dict_params)

        val {params, ...} = Axclass.get_info thy class

        val (super_fields, lthy) = fold_map
          (obtain_dict dict_context consts (Type (tyco, map TFree tparams)))
          (super_classes class thy)
          lthy

        val tparams' = map (TFree o rpair @{sort type} o fst) tparams
        val typ_inst = (TFree ("'a", [class]), Type (tyco, tparams'))

        fun mk_field (field, typ) =
          let
            val param = Axclass.param_of_inst thy (field, tyco)
            (* check: did we already define all required fields? *)
            (* if not: abort (else we would run into an infinite loop) *)
            val _ = case Symtab.lookup (#constants (Definitions.get (Context.Proof lthy))) param of
              NONE =>
                (* necessary for zero_nat *)
                if Code.is_constr thy param then
                  ()
                else
                  error ("cyclic dependency: " ^ param ^ " not yet defined in the definition of " ^ tyco ^ " :: " ^ class)
            | SOME _ => ()
          in
            term dict_context consts (Const (param, typ_subst_atomic [typ_inst] typ))
           end

        val (fields, lthy) = fold_map mk_field params lthy

        val rhs = list_comb (make (Type (tyco, tparams')), super_fields @ fields)
        val typ = map fastype_of dict_params ---> fastype_of rhs
        val head = Free (name, typ)
        val lhs = list_comb (head, dict_params)
        val term = Logic.mk_equals (lhs, rhs)

        val (def, (lthy', lthy)) = lthy
          |> tap print_info
          |> Local_Theory.open_target |> snd
          |> define_params_nosyn term
          ||> `Local_Theory.close_target
        val phi = Proof_Context.export_morphism lthy lthy'
        val def = Morphism.thm phi def

        val base_thms =
          Definitions.get (Context.Proof lthy') |> #constants |> Symtab.dest
          |> map (apsnd fst o snd)
          |> map_filter snd

        val target = (flat_right tparams, (Morphism.term phi head, tyco, class))
        val args = {base_thms = base_thms, def_thm = def}
        val thm = prove_dict_cert target args lthy'

        val const = Const (Local_Theory.full_name lthy' (Binding.name name), typ)
      in
        (const, add_instantiation (class, tyco) const thm lthy')
      end
and obtain_dict dict_context consts =
  let
    val dict_context' = Symreltab.dest dict_context
    fun for_class (Type (tyco, args)) class lthy =
          let
            val inst_param_sorts = param_sorts tyco class (Proof_Context.theory_of lthy)
            val (raw_inst, lthy') = instance consts tyco class lthy
            val (const_name, _) = dest_Const raw_inst
            val (inst_args, lthy'') = fold_map for_sort (inst_param_sorts ~~ args) lthy'
            val head = Sign.mk_const (Proof_Context.theory_of lthy'') (const_name, args)
          in
            (list_comb (head, flat inst_args), lthy'')
          end
      | for_class (TFree (name, _)) class lthy =
          let
            val available = map_filter
              (fn ((tp, class), term) => if tp = name then SOME (class, term) else NONE)
              dict_context'
            val (path, lthy') = mk_path available (TFree (name, @{sort type})) class lthy
          in
            case path of
              SOME term => (term, lthy')
            | NONE => error "no path found"
          end
      | for_class (TVar _) _ _ = error "unexpected type variable"
    and for_sort (sort, typ) =
          fold_map (for_class typ) sort
  in for_class end
and term dict_context consts term lthy =
  let
    fun traverse (t as Const (name, typ)) lthy =
        (case Symtab.lookup consts name of
          NONE => error ("unknown constant " ^ name)
        | SOME (_, Constructor) =>
            (typify t, lthy)
        | SOME (_, Classparam {class, typ = typ', selector}) =>
            let
              val subst = Sign.typ_match (Proof_Context.theory_of lthy) (typ', typ) Vartab.empty
              val (_, targ) = the (Vartab.lookup subst ("'a", 0))
              val (dict, lthy') = obtain_dict dict_context consts targ class lthy
            in
              (subst_TVars [(("'a", 0), targ)] selector $ dict, lthy')
            end
        | SOME (name', Fun {dicts = dicts, typ = typ', new_typ, ...}) =>
            let
              val subst = Type.raw_match (Logic.varifyT_global typ', typ) Vartab.empty
                |> Vartab.dest |> map (apsnd snd)
              fun lookup tparam = the (AList.lookup (op =) subst (tparam, 0))
              val (dicts, lthy') =
                fold_map (uncurry (obtain_dict dict_context consts o lookup)) (map fst dicts) lthy
              val typ = typ_subst_TVars subst (Logic.varifyT_global new_typ)
              val head =
                case Symtab.lookup (#constants (Definitions.get (Context.Proof lthy))) name of
                  NONE => Free (name', typ)
                | SOME (n, _) => Const (n, typ)
              val res = list_comb (head, dicts)
            in
              (res, lthy')
            end)
      | traverse (f $ x) lthy =
          let
            val (f', lthy')  = traverse f lthy
            val (x', lthy'') = traverse x lthy'
          in (f' $ x', lthy'') end
      | traverse (Abs (name, typ, term)) lthy =
          let
            val (term', lthy') = traverse term lthy
          in (Abs (name, typify_typ typ, term'), lthy') end
      | traverse (Free (name, typ)) lthy = (Free (name, typify_typ typ), lthy)
      | traverse (Var (name, typ)) lthy  = (Var (name, typify_typ typ), lthy)
      | traverse (Bound n) lthy = (Bound n, lthy)
  in
    traverse term lthy
  end

(** group of constants **)

fun new_names lthy consts =
  let
    val (all_names, all_consts) = split_list (flat consts)
    val all_frees = map (fn Fun {eqs, ...} => eqs | _ => []) all_consts |> flat
      |> map #params |> flat
      |> map all_frees' |> flat
    val context = fold Name.declare (all_names @ all_frees) (Variable.names_of lthy)

    fun new_name (name, const) context =
      let val (name', context') = Name.variant (mangle name) context in
        ((name, (name', const)), context')
      end
  in
    fst (fold_map (fold_map new_name) consts context)
  end

fun consts consts group lthy =
  let
    val fun_config = Function_Common.FunctionConfig
      {sequential=true, default=NONE, domintros=false, partials=false}
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt

    val all_names = map fst group

    fun print_info ctxt =
      let
        val pretty_consts = map (pretty_const ctxt) all_names |> Pretty.commas
      in
        Pretty.str "Redefining constant(s) " :: pretty_consts
        |> Pretty.block
        |> Pretty.writeln
      end

    fun process_eqs (name, Fun {dicts, param_typs, new_typ, eqs, info, cong, ...}) lthy =
          let
            val new_name = case Symtab.lookup consts name of
              NONE => error ("no new name for " ^ name)
            | SOME (n, _) => n

            val all_frees = map #params eqs |> flat |> map all_frees' |> flat
            val context = Name.make_context (all_names @ all_frees)
            val (dict_params, context') = dict_params context dicts

            fun adapt_params param_typs params =
              let
                val real_params = dict_params @ params
                val ext_params = drop (length params) param_typs
                  |> map typify_typ
                  |> Name.invent_names context' "e0" |> map Free
              in (real_params, ext_params) end

            fun mk_eq {params, rhs, thm} lthy =
              let
                val (real_params, ext_params) = adapt_params param_typs params
                val lhs' = list_comb (Free (new_name, new_typ), real_params @ ext_params)
                val (rhs', lthy') = term (Symreltab.make (map fst dicts ~~ dict_params)) consts rhs lthy
                val rhs'' = list_comb (rhs', ext_params)
              in
                ((HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs', rhs'')), thm), lthy')
              end

            val is_fun = length param_typs + length dicts > 0
          in
            fold_map mk_eq eqs lthy
            |>> rpair is_fun
            |>> SOME
            |>> pair ((name, new_name, map fst dicts), {info = info, cong = cong})
          end
      | process_eqs (name, _) lthy =
          ((((name, name, []), {info = NONE, cong = NONE}), NONE), lthy)

    val (items, lthy') = fold_map process_eqs group lthy

    val ((metas, infos), ((eqs, code_thms), is_funs)) = items
      |> map_filter (fn (meta, eqs) => Option.map (pair meta) eqs)
      |> split_list
      ||> split_list ||> apfst (flat #> split_list #>> map typify)
      |>> split_list

    val is_fun =
      case distinct (op =) is_funs of
        [b] => b
      | [] => false
      | _ => error "unsupported feature: mixed non-function and function definitions"
    val bindings = map (fn (_, new_name, _) => (Binding.name new_name, NONE, NoSyn)) metas

    val {constants, instantiations} = Definitions.get (Context.Proof lthy')
    val base_thms = Symtab.dest constants |> map (apsnd fst o snd) |> map_filter snd
    val base_certs = Symreltab.dest instantiations |> map (snd o snd)

    val consts = Sign.consts_of (Proof_Context.theory_of lthy')

    fun prove_eq_fun (info as {simps = SOME simps, fs, inducts = SOME inducts, ...}) lthy =
      let
        fun mk_target (name, _, classes) new =
          (classes, (new, Const (Consts.the_const consts name)))
        val targets = map2 mk_target metas fs
        val args =
          {fun_info = SOME info, inducts = SOME inducts, simps = simps, base_thms = base_thms,
           base_certs = base_certs, code_thms = code_thms}
      in
        (prove_fun_cert targets args lthy, args)
      end

    fun prove_eq_def defs lthy =
      let
        fun mk_target (name, _, classes) new =
          (classes, (new, Const (Consts.the_const consts name)))
        val targets = map2 mk_target metas (map (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of) defs)
        val args =
          {fun_info = NONE, inducts = NONE, simps = defs,
           base_thms = base_thms, base_certs = base_certs, code_thms = code_thms}
      in
        (prove_fun_cert targets args lthy, args)
      end

    fun add_constants ((((name, name', _), _), SOME _) :: xs) ((thm :: thms), info) =
          add_constant name name' (SOME thm, info) #> add_constants xs (thms, info)
      | add_constants ((((name, name', _), _), NONE) :: xs) (thms, info) =
          add_constant name name' (NONE, info) #> add_constants xs (thms, info)
      | add_constants [] _ =
          I

    fun prove_termination {R = new_R, ...} ctxt =
      let
        fun fallback_tac warn st =
          (if warn then warning "Falling back to automatic termination proof ..." else ();
           Function_Common.termination_prover_tac true ctxt st)

        (*copied from BNF_Comp, in turn copied from Envir.expand_term_free*)
        fun expand_term_const defs =
          let
            val eqs = map ((fn ((x, U), u) => (x, (U, u))) o apfst dest_Const) defs;
            val get = fn Const (x, _) => AList.lookup (op =) eqs x | _ => NONE;
          in Envir.expand_term get end;

        fun map_comp_bnf typ =
          let
            (* we start from a fresh lthy to avoid local hyps interfering with BNF *)
            val lthy =
              Proof_Context.theory_of ctxt
              |> Named_Target.theory_init
              |> Config.put BNF_Comp.typedef_threshold ~1
            (* we just pretend that they're all live here *)
            val live_As = all_tfrees typ
            fun flatten_tyargs Ass =
              live_As
              |> filter (fn T => exists (fn Ts => member (op =) Ts T) Ass)
            (* Dont_Inline would create new definitions, always *)
            val ((bnf, _), ((_, {map_unfolds, ...}), _)) =
              BNF_Comp.bnf_of_typ false BNF_Def.Do_Inline I flatten_tyargs live_As [] typ
                ((BNF_Comp.empty_comp_cache, BNF_Comp.empty_unfolds), lthy)
            val subst = map (Logic.dest_equals o Thm.prop_of) map_unfolds
            val t = BNF_Def.map_of_bnf bnf
          in
            (live_As, expand_term_const subst t)
          end

        val tac = case try hd (cat_options (map #info infos)) of
          SOME {R = old_R, totality = SOME totality, ...} =>
            let
              fun get_eq R =
                Inductive.the_inductive ctxt R
                |> snd |> #eqs
                |> the_single
                |> Local_Defs.abs_def_rule ctxt
              val (old_R_eq, new_R_eq) = apply2 get_eq (old_R, new_R)

              fun get_typ R =
                fastype_of R
                |> strip_type
                |> fst |> hd
              val (old_R_typ, new_R_typ) = apply2 get_typ (old_R, new_R)

              (* simple strategy: old_R and new_R are identical *)
              val simple_tac =
                let
                  val totality' = Local_Defs.unfold ctxt [old_R_eq] totality
                in
                  Local_Defs.unfold_tac ctxt [new_R_eq] THEN
                    HEADGOAL (SOLVED' (resolve_tac ctxt [totality']))
                end

              (* smart strategy: new_R can be simulated by old_R *)
              (* FIXME this is trigger-happy *)
              val smart_tac = Exn.interruptible_capture (fn st =>
                let
                  val old_R_stripped =
                    Thm.prop_of old_R_eq
                    |> Logic.dest_equals |> snd
                    |> map_types (K dummyT)
                    |> Syntax.check_term ctxt

                  val futile =
                    old_R_stripped |> exists_type (exists_subtype
                      (fn TFree (_, sort) => sort <> @{sort type}
                        | TVar (_, sort) => sort <> @{sort type}
                        | _ => false))

                  fun costrip_prodT new_t old_t =
                    if Type.could_match (old_t, new_t) then
                      (0, new_t)
                    else
                      case costrip_prodT (snd (HOLogic.dest_prodT new_t)) old_t of
                        (n, stripped_t) => (n + 1, stripped_t)

                  fun construct_inner_proj new_t old_t =
                    let
                      val (diff, stripped_t) = costrip_prodT new_t old_t
                      val (tfrees, f_head) = map_comp_bnf stripped_t
                      val f_args = map (K (Abs ("x", dummyT, Const (@{const_name undefined}, dummyT)))) tfrees
                      fun add_snd 0 = list_comb (map_types (K dummyT) f_head, f_args)
                        | add_snd n = Const (@{const_name comp}, dummyT) $ add_snd (n - 1) $ Const (@{const_name snd}, dummyT)
                    in
                      add_snd diff
                    end

                  fun construct_outer_proj new_t old_t = case (new_t, old_t) of
                    (Type (@{type_name sum}, new_ts), Type (@{type_name sum}, old_ts)) =>
                      let
                        val ps = map2 construct_outer_proj new_ts old_ts
                      in list_comb (Const (@{const_name map_sum}, dummyT), ps) end
                  | _ => construct_inner_proj new_t old_t

                  val outer_proj = construct_outer_proj new_R_typ old_R_typ

                  val old_R_typ_imported =
                    yield_singleton Variable.importT_terms old_R ctxt
                    |> fst |> get_typ

                  val c =
                    outer_proj
                    |> Type.constraint (new_R_typ --> old_R_typ_imported)
                    |> Syntax.check_term ctxt
                    |> Thm.cterm_of ctxt

                  val wf_simulate =
                    Drule.infer_instantiate ctxt [(("g", 0), c)] @{thm wf_simulate_simple}

                  val old_wf = (@{thm wfP_implies_wf_set_of} OF [@{thm accp_wfPI} OF [totality]])

                  val inner_tac =
                    match_tac ctxt @{thms wf_implies_dom} THEN'
                      match_tac ctxt [wf_simulate] CONTINUE_WITH_FW
                        [resolve_tac ctxt [old_wf],
                         match_tac ctxt @{thms set_ofI} THEN'
                           dmatch_tac ctxt @{thms set_ofD} THEN'
                           SELECT_GOAL (Local_Defs.unfold_tac ctxt [old_R_eq, new_R_eq]) THEN'
                           TRY'
                             (REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE exE}) THEN'
                               hyp_subst_tac_thin true ctxt THEN'
                               REPEAT_ALL_NEW (match_tac ctxt @{thms conjI exI}))]

                  val unfold_tac =
                    Local_Defs.unfold_tac ctxt @{thms comp_apply id_apply prod.sel} THEN
                      auto_tac ctxt

                  val tac = SOLVED (HEADGOAL inner_tac THEN unfold_tac)
                in
                  if futile then
                    (warning "Termination relation has sort constraints; termination proof is unlikely to be automatic or may even be impossible";
                     Seq.empty)
                  else
                    (tracing "Trying to re-use termination proof ...";
                     tac st)
                end)
              #> Exn.get_res
              #> the_default Seq.empty
            in
              simple_tac ORELSE smart_tac ORELSE fallback_tac true
            end
        | _ => fallback_tac false
      in Function.prove_termination NONE tac ctxt end

    fun prove_cong data lthy =
      let
        fun rewr_cong _ NONE = NONE
          | rewr_cong thm (SOME cong) =
            if Thm.nprems_of thm > 0 then
              (warning "No fundef_cong rule can be derived; this will likely not work later"; NONE)
            else
              (writeln "Porting fundef_cong rule ...";
               SOME (Local_Defs.fold lthy [thm] cong))

        val congs' =
          map2 rewr_cong (fst data) (map #cong infos)
          |> cat_options

        fun add_congs phi =
          fold Function_Context_Tree.add_function_cong (map (Morphism.thm phi) congs')
      in
        (data, Local_Theory.declaration {pervasive = false, syntax = false} add_congs lthy)
      end

    fun mk_fun lthy =
      let
        val specs = map (fn eq => (((Binding.empty, []), eq), [], [])) eqs
        val (info, lthy') =
          Function.add_function bindings specs fun_config pat_completeness_auto lthy
          |-> prove_termination
        fun prove_eq phi =
          prove_eq_fun (Function_Common.transform_function_data phi info)
      in
        (prove_eq, lthy')
      end

    fun mk_def lthy =
      let
        val (defs, lthy') = fold_map define_params_nosyn eqs lthy
        fun prove_eq phi = prove_eq_def (map (Morphism.thm phi) defs)
      in
        (prove_eq, lthy')
      end
  in
    if null eqs then
      lthy'
    else
      let
        (* the redefinition itself doesn't have a sort constraint, but the equality prop may have
           one; hence the proof needs to happen after exiting the local theory target
           conceptually, everything happening locally would be great, but the type checker won't
           allow us to add sort constraints to TFrees after they have been declared *)
        val (prove_eq, (lthy', lthy)) = lthy'
          |> tap print_info
          |> Local_Theory.open_target |> snd
          |> (if is_fun then mk_fun else mk_def)
          ||> `Local_Theory.close_target
        val phi = Proof_Context.export_morphism lthy lthy'
      in
        lthy'
        |> `(prove_eq phi)
        |-> prove_cong
        |-> add_constants items
      end
  end

fun const_raw (binding, raw_consts) lthy =
  let
    val (name, _) = Syntax.read_terms lthy raw_consts |> map dest_Const |> split_list

    val (eqs, lthy) = annotate_code_eqs lthy name
    val tab = symtab_of_sccs (new_names lthy eqs)

    val lthy = fold (consts tab) eqs lthy

    val {instantiations, constants} = Definitions.get (Context.Proof lthy)
    val thms =
      map (snd o snd) (Symreltab.dest instantiations) @
        map_filter (fst o snd o snd) (Symtab.dest constants)
  in
    snd (Local_Theory.note (binding, thms) lthy)
  end

(** setup **)

val _ =
  Outer_Syntax.local_theory
    @{command_keyword "declassify"}
    "redefines a constant after applying the dictionary construction"
    (Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.const >> const_raw)

end