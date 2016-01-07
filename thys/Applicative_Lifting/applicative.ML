(* Author: Joshua Schneider, ETH Zurich *)

signature APPLICATIVE =
sig
  type afun
  val intern: Context.generic -> xstring -> string
  val extern: Context.generic -> string -> xstring
  val afun_of_generic: Context.generic -> string -> afun
  val afun_of: Proof.context -> string -> afun
  val afuns_of_term_generic: Context.generic -> term -> afun list
  val afuns_of_term: Proof.context -> term -> afun list
  val afuns_of_typ_generic: Context.generic -> typ -> afun list
  val afuns_of_typ: Proof.context -> typ -> afun list

  val name_of_afun: afun -> binding
  val terms_of_afun: afun -> term * term
  val unfolds_of_afun: afun -> thm list
  val lift_type: afun -> typ list -> typ -> typ
  val pure: afun -> typ list -> typ -> term
  val lift: afun -> typ list -> term -> term
  val ap: Proof.context -> afun -> typ -> term
  val lift_comb: Proof.context -> afun -> term * term -> term
  val dest_type: Proof.context -> afun -> typ -> typ * typ list
  val dest_pure: Proof.context -> afun -> term -> term
  val dest_comb: Proof.context -> afun -> term -> term * term

  val afun_unfold_tac: Proof.context -> afun -> int -> tactic
  val afun_fold_tac: Proof.context -> afun -> int -> tactic
  val unfold_all_tac: Proof.context -> int -> tactic
  val normalform_conv: Proof.context -> afun -> conv
  val normalize_eq_tac: Proof.context -> afun -> int -> tactic
  val general_normalform_conv: Proof.context -> afun -> cterm * cterm -> thm * thm
  val general_normalize_eq_tac: Proof.context -> afun -> int -> tactic
  val forward_lift_rule: Proof.context -> afun -> thm -> thm
  val unfold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val fold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val normalize_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val lifting_wrapper_tac: Proof.context -> afun option -> int -> tactic

  val applicative_cmd: binding -> string -> string -> string list -> local_theory -> Proof.state
  val print_afuns: Proof.context -> unit
  val add_unfold_attrib: xstring option -> attribute
  val forward_lift_attrib: xstring -> attribute
  val parse_opt_afun: afun option context_parser
end;

structure Applicative : APPLICATIVE =
struct

(** General utilities **)

fun option none some x = case x of NONE => none | SOME y => some y;

fun filter_flag [] = []
  | filter_flag ((flag, x)::xs) = if flag then x :: filter_flag xs else filter_flag xs;

fun pick_if false xs = (NONE, xs)
  | pick_if true (x::xs) = (SOME x, xs)
  | pick_if true _ = raise List.Empty;

fun mk_TFrees Ss ctxt = Variable.invent_types Ss ctxt |>> map TFree;
val mk_TFrees' = mk_TFrees oo replicate;

fun mk_Free name typ ctxt = Variable.variant_fixes [name] ctxt
  |>> (fn name' => Free (name', typ)) o the_single;


(** Internal representation **)

type sign =
 {pure: term,
  ap: term,
  T: typ * typ,  (* variable, type pattern *)
  sort: sort,
  params: typ list,
  param_sorts: sort list};

fun map_sign f1 f2 f3 f4 f5 f6 {pure, ap, T, sort, params, param_sorts} =
  {pure = f1 pure, ap = f2 ap, T = f3 T, sort = f4 sort, params = f5 params,
    param_sorts = f6 param_sorts};

fun morph_sign phi = map_sign (Morphism.term phi) (Morphism.term phi) (apply2 (Morphism.typ phi))
  I (map (Morphism.typ phi)) I;

type axioms =
 {identity: thm,
  composition: thm,
  homomorphism: thm,
  interchange: thm,
  flip: thm option,
  const: thm option,
  duplicate: thm option};

fun map_axioms f {identity, composition, homomorphism, interchange, flip, const, duplicate} =
  {identity = f identity, composition = f composition, homomorphism = f homomorphism,
    interchange = f interchange, flip = Option.map f flip, const = Option.map f const,
    duplicate = Option.map f duplicate};

val morph_axioms = map_axioms o Morphism.thm;

type facts =
 {I_intro: thm,
  B_intro: thm,
  C_intro: thm option,
  K_intro: thm option,
  W_intro: thm option,
  merge: thm,
  swap: thm,
  B_pure: thm};

fun map_facts f {I_intro, B_intro, C_intro, K_intro, W_intro, merge, swap, B_pure} =
  {I_intro = f I_intro, B_intro = f B_intro, C_intro = Option.map f C_intro,
    K_intro = Option.map f K_intro, W_intro = Option.map f W_intro, merge = f merge, swap = f swap,
    B_pure = f B_pure};

val morph_facts = map_facts o Morphism.thm;

datatype afun = AFun of
 {name: binding,
  sign: sign,
  axioms: axioms,
  facts: facts,
  unfolds: thm list};

fun rep_afun (AFun af) = af;
val name_of_afun = #name o rep_afun;
val sign_of_afun = #sign o rep_afun;
val axioms_of_afun = #axioms o rep_afun;
val unfolds_of_afun = #unfolds o rep_afun;
val facts_of_afun = #facts o rep_afun;
fun terms_of_afun af = let val {pure, ap, ...} = sign_of_afun af in (pure, ap) end;

fun has_axiom f = is_some o f o axioms_of_afun;

fun mk_afun name sign axioms facts =
  AFun {name = name, sign = sign, axioms = axioms, facts = facts, unfolds = []};

fun map_afun f1 f2 f3 f4 f5 (AFun {name, sign, axioms, facts, unfolds}) =
  AFun {name = f1 name, sign = f2 sign, axioms = f3 axioms, facts = f4 facts,
    unfolds = f5 unfolds};

fun morph_afun phi =
  map_afun (Morphism.binding phi) (morph_sign phi) (morph_axioms phi) (morph_facts phi)
    (map (Morphism.thm phi));

(* FIXME is this (i.e. Thm.transfer) really needed? *)
val transfer_afun = morph_afun o Morphism.transfer_morphism;

fun add_unfolds thms = map_afun I I I I (union Thm.eq_thm_prop thms);


(** Term construction and destruction **)

fun lift_type_sign {T = (var, tycon), params, ...} insts baseT =
  Term.typ_subst_atomic ((var, baseT) :: (params ~~ insts)) tycon;

fun pure_sign {pure, params, ...} insts baseT =
  let val (var, _) = Term.fastype_of pure |> Term.dest_funT;
  in Term.subst_atomic_types ((var, baseT) :: (params ~~ insts)) pure end;

fun lift_sign sign insts t = Term.betapply (pure_sign sign insts (Term.fastype_of t), t);

fun ap_sign ctxt {ap, ...} funT =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, _) = Term.fastype_of ap |> Term.dest_funT;
    val tyenv = Sign.typ_match thy (pat, funT) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("ap_sign", [funT, pat], []);
  in Envir.subst_term_types tyenv ap end

fun comb_sign ctxt sign (t1, t2) =
  Term.betapplys (ap_sign ctxt sign (Term.fastype_of t1), [t1, t2]);

val lift_type = lift_type_sign o sign_of_afun;
val pure = pure_sign o sign_of_afun;
val lift = lift_sign o sign_of_afun;
fun ap ctxt = ap_sign ctxt o sign_of_afun;
fun lift_comb ctxt = comb_sign ctxt o sign_of_afun;

fun pure_pattern af =
  let
    val {pure, ...} = sign_of_afun af;
    val (argT, _) = Term.fastype_of pure |> Term.dest_funT;
    val var = ((Name.uu, Term.maxidx_of_term pure + 1), argT);
  in (Term.betapply (pure, Var var), var) end;

fun ap_pattern af =
  let
    val {ap, ...} = sign_of_afun af;
    val (arg1T, (arg2T, _)) = Term.fastype_of ap |> Term.dest_funT ||> Term.dest_funT;
    val i = Term.maxidx_of_term ap;
    val var1 = ((Name.uu, i + 1), arg1T);
    val var2 = ((Name.uu, i + 2), arg2T);
  in (Term.betapplys (ap, [Var var1, Var var2]), (var1, var2)) end;

fun patterns_of_afun af = [#1 (pure_pattern af), #1 (ap_pattern af),
  sign_of_afun af |> #T |> #2 |> Net.encode_type];

fun dest_type ctxt af T =
  let
    val thy = Proof_Context.theory_of ctxt;
    val {T = (var, tycon), params, ...} = sign_of_afun af;
    val tyenv = Sign.typ_match thy (tycon, T) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("dest_type", [T, tycon], []);
  in (the (Type.lookup tyenv (Term.dest_TVar var)),
    map (the o Type.lookup tyenv o Term.dest_TVar) params) end;

fun dest_pure ctxt af t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, var) = pure_pattern af;
    val (_, env) = Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_pure", [t, pat]);
  in the (Envir.lookup1 env var) end;

fun dest_comb ctxt af t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, vars) = ap_pattern af;
    val (_, env) = Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_ap", [t, pat]);
  in apply2 (the o Envir.lookup1 env) vars end;


(** Registration **)

(* Context data *)

(* FIXME carefully verify context storage *)
(* FIXME needs tests, especially around theory merging *)

fun join_afuns _ (af1, af2) = if pointer_eq (af1, af2)
  then raise Change_Table.SAME
  else add_unfolds (unfolds_of_afun af2) af1;

structure Data = Generic_Data
(
  type T = afun Name_Space.table * (string * term list) Item_Net.T;
  val empty = (Name_Space.empty_table "applicative functor", Item_Net.init (op = o apply2 #1) #2);
  val extend = I;
  fun merge ((t1, n1), (t2, n2)) =
    (Name_Space.join_tables join_afuns (t1, t2), Item_Net.merge (n1, n2));
);

val get_afuns = #1 o Data.get;
val get_afun_space = Name_Space.space_of_table o get_afuns;

val intern = Name_Space.intern o get_afun_space;
fun extern context = Name_Space.extern (Context.proof_of context) (get_afun_space context);

local fun undeclared name = error ("Undeclared applicative functor " ^ quote name);
in

fun afun_of_generic context name = case Name_Space.lookup (get_afuns context) name of
    SOME af => transfer_afun (Context.theory_of context) af
  | NONE => undeclared name;

val afun_of = afun_of_generic o Context.Proof;

fun update_afun name f context = if Name_Space.defined (get_afuns context) name
  then Data.map (apfst (Name_Space.map_table_entry name f)) context
  else undeclared name;

end;

fun match_term context = map #1 o Item_Net.retrieve_matching (#2 (Data.get context));
fun match_typ context = match_term context o Net.encode_type;

(* works only with terms which are combinations of pure and ap *)
fun afuns_of_term_generic context = map (afun_of_generic context) o match_term context;
val afuns_of_term = afuns_of_term_generic o Context.Proof;

fun afuns_of_typ_generic context = map (afun_of_generic context) o match_typ context;
val afuns_of_typ = afuns_of_typ_generic o Context.Proof;

fun all_unfolds_of_generic context =
  Name_Space.fold_table (fn (_, af) => append (unfolds_of_afun af)) (get_afuns context) [];
val all_unfolds_of = all_unfolds_of_generic o Context.Proof;

(* FIXME pervasive? *)
fun register_afun af =
  let fun decl phi context = Data.map (fn (names, patterns) =>
    let
      val af' = morph_afun phi af;
      val (name, names') = Name_Space.define context true (name_of_afun af, af') names;
      val patterns' = Item_Net.update (name, patterns_of_afun af') patterns;
    in (names', patterns') end) context;
  in Local_Theory.declaration {syntax = false, pervasive = false} decl end;


(* Declaration *)

fun mk_sign ctxt (raw_pure, raw_ap) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val show_term = quote o Syntax.string_of_term ctxt;
    fun bad_types _ = error "Bad type(s)";

    fun closed_poly_term t =
      let val poly_t = singleton (Variable.polymorphic ctxt) t;
      in case Term.add_vars (singleton
          (Variable.export_terms (Variable.auto_fixes t ctxt) ctxt) t) [] of
          [] => (case (Term.hidden_polymorphism poly_t) of
              [] => poly_t
            | _ => error ("Hidden type variables in term " ^ show_term t))
        | _ => error ("Locally free variables in term " ^ show_term t)
      end;

    val pure = closed_poly_term raw_pure;
    val (var as (_, pure_sort), tycon) = Term.fastype_of pure |> Term.dest_funT |>> Term.dest_TVar
      handle TYPE _ => bad_types ();
    val params = subtract (op =) [var] (Term.add_tvars pure []);
    val param_sorts = map (fn (_, S) => Sign.inter_sort thy (S, @{sort HOL.type})) params;

    val ap = closed_poly_term raw_ap;
    val i = Term.maxidx_of_term pure;
    val ap_var1 = ((Name.uu, i + 1), []);
    val ap_var2 = ((Name.uu, i + 2), []);
    fun lift T = Term_Subst.instantiateT [(var, T)] tycon;
    val ap_pat = lift (TVar ap_var1 --> TVar ap_var2) --> lift (TVar ap_var1) -->
      lift (TVar ap_var2);
    val tyenv = Sign.typ_match thy (ap_pat, Term.fastype_of ap) Vartab.empty
      handle Type.TYPE_MATCH => bad_types ();
    val ((ap_var1', ap_sort1), (ap_var2', ap_sort2)) =
      apply2 (Term.dest_TVar o the o Type.lookup tyenv) (ap_var1, ap_var2)
      handle
          Option.Option => bad_types ()
        | TYPE _ => bad_types ();
    val _ = ap_var1' <> ap_var2' orelse bad_types ();
    (* FIXME check additional type params *)

    val sort = foldl1 (Sign.inter_sort thy) [pure_sort, ap_sort1, ap_sort2, @{sort HOL.type}];
    val _ = Sign.of_sort thy (Term.aT sort --> Term.aT sort, sort) orelse
      error ("Sort constraint " ^ quote (Syntax.string_of_sort ctxt sort) ^
        " not closed under function types");
  in
   {pure = pure, ap = ap, T = (TVar var, tycon), sort = sort, params = map TVar params,
     param_sorts = param_sorts}
  end;

fun mk_facts ctxt sign axioms =
  let
    fun comb_intro thm = Thm.symmetric (thm RS eq_reflection);
    val B_intro = comb_intro (#composition axioms);
    val merge_rule = #homomorphism axioms RS eq_reflection;

    val B_pure =
      let
        val (([T1, T2, T3], Ts), ctxt') = ctxt
          |> mk_TFrees' 3 (#sort sign)
          ||>> mk_TFrees (#param_sorts sign);
        val (((g, f), x), ctxt'') = ctxt'
          |> mk_Free "g" (T2 --> T3)
          ||>> mk_Free "f" (lift_type_sign sign Ts (T1 --> T2))
          ||>> mk_Free "x" (lift_type_sign sign Ts T1);
        val comb = comb_sign ctxt'' sign;
        val lhs = comb (lift_sign sign Ts g, comb (f, x));
        val B_g = Abs ("f", T1 --> T2, Abs ("x", T1, Term.betapply (g, Bound 1 $ Bound 0)));
        val rhs = comb (comb (lift_sign sign Ts B_g, f), x);
        val prop = Logic.mk_equals (lhs, rhs);
        val tac =
          HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt'' [B_intro, merge_rule] THEN'
          resolve_tac ctxt'' [reflexive_thm]);
      in singleton (Variable.export ctxt'' ctxt) (Goal.prove ctxt'' [] [] prop (K tac)) end;
  in
    {I_intro = comb_intro (#identity axioms),
      B_intro = B_intro,
      C_intro = Option.map comb_intro (#flip axioms),
      K_intro = Option.map comb_intro (#const axioms),
      W_intro = Option.map comb_intro (#duplicate axioms),
      merge = merge_rule,
      swap = #interchange axioms RS eq_reflection,
      B_pure = B_pure}
  end;

fun mk_comb_prop comb sign ctxt =
  let
    val comb_tfrees = Term.add_tfrees comb [];
    val ((Ts, Us), ctxt') = ctxt
      |> mk_TFrees' (length comb_tfrees) (#sort sign)
      ||>> mk_TFrees (#param_sorts sign);
    val comb' = Term.subst_atomic_types (map TFree comb_tfrees ~~ Ts) comb;
    val (bound_names, bound_Ts) = split_list (Term.strip_abs_vars comb');
    val (var_names, ctxt'') = Variable.variant_fixes bound_names ctxt';
    val vars = map (fn (var, T) => Free (var, lift_type_sign sign Us T)) (var_names ~~ bound_Ts);
    val lift_map = rev vars;

    fun list_comb t [] = t
      | list_comb t (x::xs) = list_comb (comb_sign ctxt'' sign (t, x)) xs;

    fun lift_term (Bound i) = nth lift_map i
      | lift_term (s $ t) = comb_sign ctxt'' sign (lift_term s, lift_term t)
      | lift_term t = raise TERM ("mk_comb_prop", [t]);

    val lhs = list_comb (lift_sign sign Us comb') vars;
    val rhs = lift_term (Term.strip_abs_body comb');
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in fold Logic.all lift_map prop end;

val mk_id_prop = mk_comb_prop @{term "\<lambda>x. x"};
val mk_comp_prop = mk_comb_prop @{term "\<lambda>g f x. g (f x)"};
val mk_flip_prop = mk_comb_prop @{term "\<lambda>f x y. f y x"};
val mk_const_prop = mk_comb_prop @{term "\<lambda>x y. x"};
val mk_duplicate_prop = mk_comb_prop @{term "\<lambda>f x. f x x"};

fun mk_homomorphism_prop sign ctxt =
  let
    val (([T1, T2], Us), ctxt') = ctxt
      |> mk_TFrees' 2 (#sort sign)
      ||>> mk_TFrees (#param_sorts sign);
    val ((f, x), ctxt'') = ctxt'
      |> mk_Free "f" (T1 --> T2)
      ||>> mk_Free "x" T1;
    val lhs = comb_sign ctxt'' sign (lift_sign sign Us f, lift_sign sign Us x);
    val rhs = lift_sign sign Us (f $ x);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in Logic.all f (Logic.all x prop) end;

fun mk_interchange_prop sign ctxt =
  let
    val (([T1, T2], Us), ctxt') = ctxt
      |> mk_TFrees' 2 (#sort sign)
      ||>> mk_TFrees (#param_sorts sign);
    val ((f, x), ctxt'') = ctxt'
      |> mk_Free "f" (lift_type_sign sign Us (T1 --> T2))
      ||>> mk_Free "x" T1;
    val lhs = comb_sign ctxt'' sign (f, lift_sign sign Us x);
    val T_x = Abs ("f", T1 --> T2, Bound 0 $ x);
    val rhs = comb_sign ctxt'' sign (lift_sign sign Us T_x, f);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in Logic.all f (Logic.all x prop) end;

fun note_afun_thms af =
  let
    val axioms = axioms_of_afun af;
    val named_thms =
      [("afun_id", #identity axioms),
        ("afun_comp", #composition axioms),
        ("afun_hom", #homomorphism axioms),
        ("afun_ichng", #interchange axioms)]
      |> option I (cons o pair "afun_flip") (#flip axioms)
      |> option I (cons o pair "afun_const") (#const axioms)
      |> option I (cons o pair "afun_dup") (#duplicate axioms);

    val base_name = Binding.name_of (name_of_afun af);
    fun mk_note (name, thm) =
      ((Binding.qualify true base_name (Binding.name name), []), [([thm], [])]);
  in Local_Theory.notes (map mk_note named_thms) #> #2 end;

fun applicative_cmd name pure ap flags lthy =
  let
    (* FIXME *)
    val (C, K, W) = fold (fn ident => fn (C, K, W) =>
      if ident = "C" then (true, K, W)
      else if ident = "K" then (C, true, W)
      else if ident = "W" then (C, K, true)
      else error ("Unknown combinator " ^ ident)) flags (false, false, false);
    val raw_pure = Syntax.read_term lthy pure;
    val raw_ap = Syntax.read_term lthy ap;

    val sign = mk_sign lthy (raw_pure, raw_ap);
    (* FIXME fix variables here, then reuse in each mk_*_prop (à la BNF_Def) *)
    val basic_props = [mk_id_prop, mk_comp_prop, mk_homomorphism_prop, mk_interchange_prop];
    val extra_props = filter_flag [(C, mk_flip_prop), (K, mk_const_prop), (W, mk_duplicate_prop)];
    val props = map (fn mk_prop => mk_prop sign lthy) (basic_props @ extra_props);

    fun after_qed thmss lthy =
      let
        val (id_thm :: comp_thm :: hom_thm :: interchange_thm :: extra_thms) = flat thmss;
        val (((flip_thm), const_thm), duplicate_thm) = extra_thms
          |> pick_if C
          ||>> pick_if K
          ||>> pick_if W
          |> #1;
        val axioms = {identity = id_thm, composition = comp_thm, homomorphism = hom_thm,
          interchange = interchange_thm, flip = flip_thm, const = const_thm,
          duplicate = duplicate_thm};
        val facts = mk_facts lthy sign axioms;
        val af = mk_afun name sign axioms facts;
      in lthy
        |> register_afun af
        |> note_afun_thms af
      end;
  in
    Proof.theorem NONE after_qed (map (fn t => [(t, [])]) props) lthy
    |> Proof.refine (Method.primitive_text (Library.K I))
    |> Seq.the_result ""
  end;

fun print_afuns ctxt =
  let
    fun pretty_afun (name, af) =
      let
        val {pure, ap, T, ...} = sign_of_afun af;
        val (tvar, typ) = T;
        val combinators = filter_flag [(has_axiom #flip af, "C"), (has_axiom #const af, "K"),
          (has_axiom #duplicate af, "W")];
      in Pretty.block (Pretty.fbreaks [Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt typ), Pretty.brk 1, Pretty.str "of", Pretty.brk 1,
          Syntax.pretty_typ ctxt tvar],
        Pretty.block [Pretty.str "pure:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt pure)],
        Pretty.block [Pretty.str "ap:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt ap)],
        Pretty.block ([Pretty.str "combinators:", Pretty.brk 1] @
          Pretty.commas (map Pretty.str combinators))]) end;
    val afuns = sort_by #1 (Name_Space.fold_table cons (get_afuns (Context.Proof ctxt)) []);
  in Pretty.writeln (Pretty.big_list "Registered applicative functors:" (map pretty_afun afuns)) end;


(* Unfolding *)

fun add_unfold_thm name thm context =
  let
    val (lhs, _) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      handle TERM _ => error "Not an equation";
    val names = case name of
        SOME n => [intern context n]
      | NONE => case match_typ context (Term.fastype_of lhs) of
          ns as (_::_) => ns
        | [] => error "Unable to determine applicative functor instance";
    val _ = map (afun_of_generic context) names;
    (* TODO check equation *)
    (* FIXME could also use Local_Defs.meta_rewrite_rule or unfold_tac *)
    val thm' = thm RS @{thm eq_reflection};
  in fold (fn n => update_afun n (add_unfolds [thm'])) names context end;

fun add_unfold_attrib name = Thm.declaration_attribute (add_unfold_thm name);

(* TODO deletion? *)


(** Reasoning with applicative functors **)

(* Utilities *)

val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

(* based on term_name from Pure/term.ML *)
fun term_to_vname (Const (x, _)) = Long_Name.base_name x
  | term_to_vname (Free (x, _)) = clean_name x
  | term_to_vname (Var ((x, _), _)) = clean_name x
  | term_to_vname _ = "x";

fun afuns_of_eq precise ctxt t =
  let val (lhs, rhs) = Variable.focus NONE t ctxt
    |> #1 |> #2
    |> Logic.strip_imp_concl
    |> Envir.beta_eta_contract
    |> HOLogic.dest_Trueprop
    |> HOLogic.dest_eq;
  in if precise
    then (case afuns_of_term ctxt lhs of
        [] => afuns_of_term ctxt rhs
      | afs => afs)
    else afuns_of_typ ctxt (Term.fastype_of lhs) end;

fun AUTO_AFUNS precise tac ctxt opt_af = case opt_af of
    SOME af => tac [af]
  | NONE => SUBGOAL (fn (goal, i) => (case afuns_of_eq precise ctxt goal of
      [] => no_tac
    | afs => tac afs i) handle TERM _ => no_tac);

fun AUTO_AFUN precise tac = AUTO_AFUNS precise (tac o hd);

fun binop_par_conv cv ct =
  let
    val ((binop, arg1), arg2) = Thm.dest_comb ct |>> Thm.dest_comb;
    val (th1, th2) = cv (arg1, arg2);
  in Drule.binop_cong_rule binop th1 th2 end;

fun hol_eq_par_conv cv ct = case Thm.term_of ct of
    Const (@{const_name HOL.eq}, _) $ _ $ _ => binop_par_conv cv ct
  | _ => raise CTERM ("hol_eq_par_conv", [ct]);

fun hol_eq_conv_tac cv = CONVERSION (HOLogic.Trueprop_conv (hol_eq_par_conv cv));

val fold_goal_tac = SELECT_GOAL oo Raw_Simplifier.fold_goals_tac;


(* Unfolding of lifted constants *)

fun afun_unfold_tac ctxt af = Raw_Simplifier.rewrite_goal_tac ctxt (unfolds_of_afun af);
fun afun_fold_tac ctxt af = fold_goal_tac ctxt (unfolds_of_afun af);

fun unfold_all_tac ctxt = Raw_Simplifier.rewrite_goal_tac ctxt (all_unfolds_of ctxt);


(* Normal form conversion *)

fun rename_rewr_conv mk_map rule ct =
  let val rule' = Drule.rename_bvars (mk_map (Thm.term_of ct)) rule
  in Conv.rewr_conv rule' ct end;

fun rename_rr_conv v = rename_rewr_conv (fn t =>
    (case t of
        _ $ (_ $ t') => [(v, term_to_vname t')]
      | _ => raise TERM ("rename_rr_conv", [t])));

fun normalform_conv ctxt af =
  let
    val rules = facts_of_afun af;

    val leaf_conv = rename_rewr_conv (fn t => [("x", term_to_vname t)]) (#I_intro rules);
    val merge_conv = Conv.rewr_conv (#merge rules);
    val swap_conv = Conv.rewr_conv (#swap rules);
    val rotate_conv = rename_rr_conv "x" (#B_intro rules);
    val pure_rotate_conv = rename_rr_conv "x" (#B_pure rules);
    fun normalize_pure_nf ct =
      ((pure_rotate_conv then_conv Conv.arg1_conv normalize_pure_nf) else_conv merge_conv) ct;
    val normalize_nf_pure = swap_conv then_conv normalize_pure_nf;
    fun normalize_nf_nf ct =
      ((rotate_conv then_conv
        Conv.arg1_conv (Conv.arg1_conv normalize_pure_nf then_conv normalize_nf_nf)) else_conv
      normalize_nf_pure) ct;

    fun normalize ct =
      let val t = Thm.term_of ct
      in if can (dest_comb ctxt af) t
        then (Conv.arg1_conv normalize then_conv Conv.arg_conv normalize then_conv
            normalize_nf_nf) ct
        else if can (dest_pure ctxt af) t
          then Conv.all_conv ct
          else leaf_conv ct
      end;
  in normalize end;

val normalize_eq_tac = hol_eq_conv_tac o apply2 oo normalform_conv;


(* Bracket abstraction and generalized unlifting *)

datatype apterm =
    Pure of term  (* includes pure application *)
  | ApVar of int * term  (* unique index, instantiated term *)
  | Ap of apterm * apterm;

fun apterm_vars (Pure _) = I
  | apterm_vars (ApVar v) = cons v
  | apterm_vars (Ap (t1, t2)) = apterm_vars t1 #> apterm_vars t2;

fun occurs_any _ (Pure _) = false
  | occurs_any vs (ApVar (i, _)) = exists (fn j => i = j) vs
  | occurs_any vs (Ap (t1, t2)) = occurs_any vs t1 orelse occurs_any vs t2;

fun term_of_apterm ctxt af t =
  let
    fun tm_of (Pure t) = t
      | tm_of (ApVar (_, t)) = t
      | tm_of (Ap (t1, t2)) = lift_comb ctxt af (tm_of t1, tm_of t2);
  in tm_of t end;

fun apterm_of_term ctxt af t =
  let
    fun aptm_of t i = case try (dest_comb ctxt af) t of
        SOME (t1, t2) => i |> aptm_of t1 ||>> aptm_of t2 |>> Ap
      | NONE => if can (dest_pure ctxt af) t
          then (Pure t, i)
          else (ApVar (i, t), i + 1);
  in aptm_of t end;

fun consolidate ctxt af (t1, t2) =
  let
    fun common_inst (i, t) (j, insts) = case Termtab.lookup insts t of
        SOME k => (((i, t), k), (j, insts))
      | NONE => (((i, t), j), (j + 1, Termtab.update (t, j) insts));

    val (vars, _) = (0, Termtab.empty)
      |> fold_map common_inst (apterm_vars t1 [])
      ||>> fold_map common_inst (apterm_vars t2 []);

    fun merge_adjacent (([], _), _) [] = []
      | merge_adjacent ((is, t), d) [] = [((is, t), d)]
      | merge_adjacent (([], _), _) (((i, t), d)::xs) = merge_adjacent (([i], t), d) xs
      | merge_adjacent ((is, t), d) (((i', t'), d')::xs) = if d = d'
          then merge_adjacent ((i'::is, t), d) xs
          else ((is, t), d) :: merge_adjacent (([i'], t'), d') xs;

    fun align _ [] = NONE
      | align ((i, t), d) (((i', t'), d')::xs) = if d = d'
          then SOME ([((i @ i', t), d)], xs)
          else Option.map (apfst (cons ((i', t'), d'))) (align ((i, t), d) xs);
    fun merge ([], ys) = ys
      | merge (xs, []) = xs
      | merge ((xs as ((is1, t1), d1)::xs'), ys as (((is2, t2), d2)::ys')) = if d1 = d2
          then ((is1 @ is2, t1), d1) :: merge (xs', ys')
          else case (align ((is2, t2), d2) xs, align ((is1, t1), d1) ys) of
              (SOME (zs, xs''), NONE) => zs @ merge (xs'', ys')
            | (NONE, SOME (zs, ys'')) => zs @ merge (xs', ys'')
            | _ => ((is1, t1), d1) :: ((is2, t2), d2) :: merge (xs', ys');

    fun unbalanced vs = error ("Unbalanced opaque terms " ^
      commas_quote (map (Syntax.string_of_term ctxt o #2 o #1) vs));
    fun mismatch (t1, t2) = error ("Mismatched opaque terms " ^
      quote (Syntax.string_of_term ctxt t1) ^ " and " ^ quote (Syntax.string_of_term ctxt t2));
    fun same ([], []) = []
      | same ([], ys) = unbalanced ys
      | same (xs, []) = unbalanced xs
      | same ((((i1, t1), d1)::xs), (((i2, t2), d2)::ys)) = if d1 = d2
          then ((i1 @ i2, t1), d1) :: same (xs, ys)
          else mismatch (t1, t2);
  in vars
    |> has_axiom #flip af ? apply2 (sort (int_ord o apply2 #2))
    |> apply2 (if has_axiom #duplicate af
        then merge_adjacent (([], Term.dummy), 0)
        else map (apfst (apfst single)))
    |> (if has_axiom #const af then merge else same)
    |> map #1
  end;

fun rewr_subst_ap ctxt af rewr thm1 thm2 =
  let
    val funT = thm1 |> Thm.lhs_of |> Thm.typ_of_cterm;
    val ap_inst = Thm.cterm_of ctxt (ap ctxt af funT);
    val rule1 = Drule.binop_cong_rule ap_inst thm1 thm2;
    val rule2 = Conv.rewr_conv rewr (Thm.rhs_of rule1);
  in Thm.transitive rule1 rule2 end;

fun squash_atoms ctxt af tt =
  let
    val {merge, ...} = facts_of_afun af;
    fun squash (Pure t) = SOME (Thm.reflexive (Thm.cterm_of ctxt t))
      | squash (ApVar _) = NONE
      | squash (Ap (tt1, tt2)) = case squash tt1 of
          NONE => NONE
        | SOME thm1 => case squash tt2 of
            NONE => NONE
          | SOME thm2 => SOME (rewr_subst_ap ctxt af merge thm1 thm2);
  in squash tt end;

exception ASSERT of string;

fun eliminate ctxt af tt (v, v_tm) =
  let
    val rules = facts_of_afun af;

    val rewr_subst_ap = rewr_subst_ap ctxt af;
    fun extract_comb n thm = Pure (thm |> Thm.rhs_of |> funpow n Thm.dest_arg1 |> Thm.term_of);
    fun refl_step tt = (tt, Thm.reflexive (Thm.cterm_of ctxt (term_of_apterm ctxt af tt)));
    fun comb2_step def (tt1, thm1) (tt2, thm2) =
      let val thm = rewr_subst_ap def thm1 thm2;
      in (Ap (Ap (extract_comb 3 thm, tt1), tt2), thm) end;
    val B_step = comb2_step (#B_intro rules);
    fun swap_B_step (tt1, thm1) thm2 =
      let
        val thm3 = rewr_subst_ap (#swap rules) thm1 thm2;
        val thm4 = Thm.transitive thm3 (Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm3));
      in (Ap (Ap (extract_comb 3 thm4, extract_comb 1 thm3), tt1), thm4) end;
    fun I_step tm =
      let val thm = Conv.rewr_conv (#I_intro rules) (Thm.cterm_of ctxt tm)
      in (extract_comb 1 thm, thm) end;
    fun W_step s1 s2 =
      let
        val (Ap (Ap (tt1, tt2), tt3), thm1) = B_step s1 s2;
        val thm2 = Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm1 |> funpow 2 Thm.dest_arg1);
        val thm3 = squash_atoms ctxt af tt3 |> the;
        val (tt4, thm4) = swap_B_step (Ap (Ap (extract_comb 3 thm2, tt1), tt2), thm2) thm3;
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm5 = rewr_subst_ap (#W_intro rules |> the) thm4 (Thm.reflexive var);
        val thm6 = Thm.transitive thm1 thm5;
      in (Ap (extract_comb 2 thm6, tt4), thm6) end;
    fun S_step s1 s2 =
      let
        val (Ap (Ap (tt1, tt2), tt3), thm1) = comb2_step (#C_intro rules |> the) s1 s2;
        val thm2 = Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm1 |> Thm.dest_arg1);
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm3 = rewr_subst_ap (#W_intro rules |> the) thm2 (Thm.reflexive var);
        val thm4 = Thm.transitive thm1 thm3;
        val tt = Ap (extract_comb 2 thm4, Ap (Ap (extract_comb 3 thm2, Ap (tt1, tt2)), tt3));
      in (tt, thm4) end;
    fun K_step tt tm =
      let
        val ct = Thm.cterm_of ctxt tm;
        val T = Term.fastype_of tm |> dest_type ctxt af |> #1 |> Thm.ctyp_of ctxt;
        val thm = Thm.instantiate' [SOME T] [SOME ct]
          (Conv.rewr_conv (#K_intro rules |> the) (term_of_apterm ctxt af tt |> Thm.cterm_of ctxt))
      in (Ap (extract_comb 2 thm, tt), thm) end;
    fun unreachable _ = raise ASSERT "eliminate: assertion failed";
    fun elim (Pure _) = unreachable ()
      | elim (ApVar (i, t)) = if exists (fn x => x = i) v then I_step t else unreachable ()
      | elim (Ap (t1, t2)) = (case (occurs_any v t1, occurs_any v t2) of
            (false, false) => unreachable ()
          | (false, true) => B_step (refl_step t1) (elim t2)
          | (true, false) => (case squash_atoms ctxt af t2 of
                SOME thm => swap_B_step (elim t1) thm
              | NONE => comb2_step (#C_intro rules |> the) (elim t1) (refl_step t2))
          | (true, true) => if has_axiom #flip af
              then S_step (elim t1) (elim t2)
              else W_step (elim t1) (elim t2));
  in if occurs_any v tt
    then elim tt
    else K_step tt v_tm
  end;

fun rename_boundvars ctxt af vs thm =
  let
    fun rename [] t = t
      | rename ((_, v)::vs) (Abs (_, T, t)) = Abs (term_to_vname v, T, rename vs t)
      | rename _ t = t;
    fun rename_pure t = t
      |> dest_pure ctxt af
      |> rename (rev vs)
      |> lift af (Term.fastype_of t |> dest_type ctxt af |> #2);
    val prop' = Thm.prop_of thm
      |> Logic.dest_equals
      ||> rename_pure
      |> Logic.mk_equals;
  in Thm.renamed_prop prop' thm end;

fun general_normalform_conv ctxt af cts =
  let
    val (t1, t2) = apply2 (Thm.term_of) cts;
    val ((apt1, apt2), _) = 0 |> apterm_of_term ctxt af t1 ||>> apterm_of_term ctxt af t2;
    val vs = consolidate ctxt af (apt1, apt2);
    fun elim_all tt [] = squash_atoms ctxt af tt |> the |> rename_boundvars ctxt af vs
      | elim_all tt (v::vs) =
          let
            val (tt', rule1) = eliminate ctxt af tt v;
            val rule2 = elim_all tt' vs;
            (* FIXME remaining use of plain term destruction instead of Applicative.dest_comb *)
            val ((ct1, _), ct3) = rule1 |> Thm.rhs_of |> Thm.dest_comb |>> Thm.dest_comb;
            val rule3 = Thm.combination (Thm.combination (Thm.reflexive ct1) rule2) (Thm.reflexive ct3);
          in Thm.transitive rule1 rule3 end;
  in (elim_all apt1 vs, elim_all apt2 vs) end;

val general_normalize_eq_tac = hol_eq_conv_tac oo general_normalform_conv;


(* Reduce canonical forms to base equation *)

(*
  (pure f <> x1 <> ... <> xn = pure g <> x1 <> ... <> xn)
    ===> !!x1 ... xn. (f x1 ... xn = g x1 ... xn)
  This tactic tries to be as precise as possible to prevent unexpected outcomes.
  Succeeds if partial progress can be made.
*)
fun head_cong_tac ctxt af = SUBGOAL (fn (goal, i) =>
  let
    fun reduce_ap (t, t') = case (try (dest_comb ctxt af) t, try (dest_comb ctxt af) t') of
        (SOME (tl, tr), SOME (tl', tr')) => if tr aconv tr'
          then reduce_ap (tl, tl') ||> cons tr
          else ((false, (t, t')), [])
      | (NONE, NONE) => ((true, (t, t')), [])
      | _ => ((false, (t, t')), []);

    fun reduce_pure (t, t') = case (try (dest_pure ctxt af) t, try (dest_pure ctxt af) t') of
        (SOME ta, SOME ta') => (true, (ta, ta'))
      | _ => (false, (t, t'));

    fun ap_cong1_rule ctxt t thm =
      let
        val funT = thm |> Thm.lhs_of |> Thm.typ_of_cterm;
        val ap_inst = Thm.cterm_of ctxt (ap ctxt af funT);
      in Drule.fun_cong_rule (Drule.arg_cong_rule ap_inst thm) (Thm.cterm_of ctxt t) end;

    fun pure_cong_rule ctxt Ts thm =
      let
        val argT = thm |> Thm.lhs_of |> Thm.typ_of_cterm;
        val pure_inst = Thm.cterm_of ctxt (pure af Ts argT);
      in Drule.arg_cong_rule pure_inst thm end;

    val (lhs, rhs) = goal |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
    val (_, Ts) = dest_type ctxt af (Term.fastype_of lhs);
    val ((is_head, (lhs', rhs')), args) = reduce_ap (lhs, rhs);
    val (is_base, (lhs'', rhs'')) = if is_head
      then reduce_pure (lhs', rhs')
      else (false, (lhs', rhs'));
    val hyp = (lhs'', rhs'') |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;
    val (base_eq, ctxt') = yield_singleton Assumption.add_assumes (Thm.cterm_of ctxt hyp) ctxt;
    val concl = (base_eq RS @{thm eq_reflection})
      |> is_base ? pure_cong_rule ctxt' Ts
      |> fold_rev (ap_cong1_rule ctxt') args;
    val concl' = concl RS @{thm HOL.meta_eq_to_obj_eq};
    val rule = Assumption.export false ctxt' ctxt concl';
    val post_tac = if is_base
      then REPEAT_DETERM o resolve_tac ctxt [ext]
      else K all_tac;
  in (resolve_tac ctxt [rule] THEN' post_tac) i end
  handle TERM _ => no_tac | TYPE _ => no_tac);


(* Forward lifting *)

fun forward_lift_rule ctxt af thm =
  let
    val sign = sign_of_afun af;
    val prop = Thm.prop_of thm;
    val tvars = Term.add_tvars prop [];
    val ((Ts, Us), ctxt') = ctxt
      |> mk_TFrees (map #2 tvars)
      ||>> mk_TFrees (#param_sorts sign);
    val prop' = Term.subst_atomic_types (map TVar tvars ~~ Ts) prop;
    val (var_names, var_Ts) = split_list (Term.add_vars prop' []);
    val (free_names, ctxt'') = Variable.variant_fixes (map #1 var_names) ctxt';
    val frees = map (fn (var, T) => Free (var, lift_type af Us T)) (free_names ~~ var_Ts);
    val var_map = var_names ~~ frees;

    fun is_pure t = null (Term.add_vars t []);

    fun lift_term (Const c) = lift af Us (Const c)
      | lift_term (Abs a) = lift af Us (Abs a)
      | lift_term (Var (var, _)) = the (AList.lookup (op =) var_map var)
      | lift_term (s $ t) = (case (is_pure s, is_pure t) of
              (true, true) => lift af Us (s $ t)
            | (true, false) => lift_comb ctxt'' af (lift af Us s, lift_term t)
            | (false, true) => lift_comb ctxt'' af (lift_term s, lift af Us t)
            | (false, false) => lift_comb ctxt'' af (lift_term s, lift_term t))
      | lift_term t = raise TERM ("forward_lift_rule", [t]);

    val (lhs, rhs) = prop' |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
    val lifted_prop = HOLogic.mk_eq (lift_term lhs, lift_term rhs) |> HOLogic.mk_Trueprop;
    val tac = general_normalize_eq_tac ctxt'' af THEN'
      head_cong_tac ctxt'' af THEN'
      resolve_tac ctxt'' [thm];
    val thm' = singleton (Variable.export ctxt'' ctxt)
      (Goal.prove ctxt'' [] [] lifted_prop (K (tac 1)));
    val thm'' = Raw_Simplifier.fold_rule ctxt (unfolds_of_afun af) thm';
  in thm'' end;

fun forward_lift_attrib name =
  Thm.rule_attribute [] (fn context => fn thm =>
    let val af = afun_of_generic context (intern context name)  (* FIXME !?!? *)
    in forward_lift_rule (Context.proof_of context) af thm end);


(* High-level tactics *)

fun unfold_wrapper_tac ctxt = AUTO_AFUNS false (fn afs =>
  Simplifier.safe_asm_full_simp_tac (ctxt addsimps flat (map unfolds_of_afun afs))) ctxt;

fun fold_wrapper_tac ctxt = AUTO_AFUN true (fold_goal_tac ctxt o unfolds_of_afun) ctxt;

fun WRAPPER tac ctxt opt_af =
  REPEAT_DETERM o resolve_tac ctxt [@{thm HOL.allI}] THEN'
  Subgoal.FOCUS (fn {context = ctxt, ...} =>
      AUTO_AFUNS false (EVERY' o map (afun_unfold_tac ctxt)) ctxt opt_af 1 THEN
      AUTO_AFUN true (fn af =>
        afun_unfold_tac ctxt af THEN'
        CONVERSION Drule.beta_eta_conversion THEN'
        tac ctxt af THEN'
        head_cong_tac ctxt af) ctxt opt_af 1) ctxt;

val normalize_wrapper_tac = WRAPPER normalize_eq_tac;
val lifting_wrapper_tac = WRAPPER general_normalize_eq_tac;

val parse_opt_afun = Scan.peek (fn context =>
  Scan.option Parse.xname >> Option.map (intern context #> afun_of_generic context));

end;
