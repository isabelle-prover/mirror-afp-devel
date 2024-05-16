(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ML_Infer_Instantiate
  imports Main 
begin

section \<open>Instantiation, inferring type instantiation from term instantiation.\<close>

ML_val
\<open>
\<^instantiate>\<open>'a=\<^typ>\<open>nat\<close> and x=\<^term>\<open>1::nat\<close> in term \<open>x + x\<close> for x::"'a::plus"\<close>
\<close>

text \<open>
This is a variant of of the instantiate antiquotation, e.g.:
 @{ML \<open>\<^instantiate>\<open>'a=\<^typ>\<open>nat\<close> and x=\<^term>\<open>1::nat\<close> in term \<open>x + x\<close> for x::\<open>'a::plus\<close>\<close>\<close>}.

The instantiate antiquotation requires the explicit instantiation of type-variables, including
those that can be inferred from the term instantiation. This makes the code very explicit, 
predictable and efficient as no types have to be calculated at runtime or be 'guessed' by the reader.
On the other hand it can make the resulting code quite verbose when the number of type variables increases. 

In this theory we provide a variant, that allows to omit those type-instantiations that 
are already fixed by the given term instantiations. This 
follows the same idea as e.g. @{ML Drule.infer_instantiate}.

Moreover, we provide a variant that also takes a morphism into account. The use-case here is that
the instantiate expression is written within a locale context but later on is used in an
interpretation of the locale (given by morphism phi). Before instantiation the term is 
exported (according to morphism phi).
\<close>


ML \<open>
fun pretty_terms ctxt ts =
  Pretty.list "[" "]" (map (Syntax.pretty_term ctxt) ts)
fun string_of_terms ctxt ts = pretty_terms ctxt ts |> Pretty.string_of
fun pretty_thms ctxt thms =
  Pretty.list "[" "]" (map (Thm.pretty_thm ctxt) thms)
fun pretty_big_list_thms name ctxt thms =
  Pretty.big_list name  (map (Thm.pretty_thm_item ctxt) thms)

fun string_of_thms ctxt thms = pretty_thms ctxt thms |> Pretty.string_of
\<close>

ML \<open>
signature ML_INFER_INSTANTIATE =
sig
  val make_cterm: Proof.context -> term -> cterm
  type insts = ((indexname * sort) * typ) list * ((indexname * typ) * term) list
  type cinsts = ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list
  val morph_instantiate_term: Position.T -> insts -> term -> Morphism.morphism -> Proof.context -> term
  val morph_instantiate_cterm: Position.T -> cinsts -> cterm -> Morphism.morphism -> Proof.context -> cterm
  val morph_instantiate_thm: Position.T -> cinsts -> thm -> Morphism.morphism -> Proof.context -> thm
  val morph_instantiate_thms: Position.T -> cinsts -> thm list -> Morphism.morphism -> Proof.context -> thm list
  val instantiate_term: Position.T -> insts -> term -> Proof.context -> term
  val instantiate_cterm: Position.T -> cinsts -> cterm -> Proof.context -> cterm
  val instantiate_thm: Position.T -> cinsts -> thm -> Proof.context -> thm
  val instantiate_thms: Position.T -> cinsts -> thm list -> Proof.context -> thm list
  val get_thms: Proof.context -> int -> thm list
  val get_thm: Proof.context -> int -> thm
end;

structure ML_Infer_Instantiate:ML_INFER_INSTANTIATE =
struct

(* exported operations *)

fun make_cterm ctxt t = Thm.cterm_of ctxt t |> Thm.trim_context_cterm;

type insts = ((indexname * sort) * typ) list * ((indexname * typ) * term) list
type cinsts = ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list

type 'a operations = {
  type_of: 'a -> typ, 
  transfer: theory -> 'a -> 'a,
  maxidx_of: 'a -> int,
  term_of: 'a -> term}

val term_operations = {
  type_of   = fastype_of, 
  transfer  = K I, 
  maxidx_of = Term.maxidx_of_term,
  term_of   = I}: term operations

val cterm_operations = {
  type_of   = Thm.typ_of_cterm, 
  transfer  = Thm.transfer_cterm, 
  maxidx_of = Thm.maxidx_of_cterm,
  term_of   = Thm.term_of}: cterm operations

\<comment> \<open>cf. @{ML Drule.infer_instantiate_types}\<close>
fun gen_infer (operations:'a operations) ctxt ((xi, T), cu) (tyenv, maxidx) =
  let
    val thy = Proof_Context.theory_of ctxt         
    val _ = Thm.ctyp_of ctxt T;
    val _ = #transfer operations thy cu;
    val U = #type_of operations cu;
    val maxidx' = maxidx
      |> Integer.max (#2 xi)
      |> Term.maxidx_typ T
      |> Integer.max (#maxidx_of operations cu);
    val (tyenv', maxidx'') = Sign.typ_unify thy (T, U) (tyenv, maxidx')
      handle Type.TUNIFY =>
        let
          val t = Var (xi, T);
          val u = #term_of operations cu;   
        in
          raise TERM ("ML_Infer_Instantiate.gen_infer: type " ^
            Syntax.string_of_typ ctxt (Envir.norm_type tyenv T) ^ " of variable " ^
            Syntax.string_of_term ctxt (Term.map_types (Envir.norm_type tyenv) t) ^
            "\ncannot be unified with type " ^
            Syntax.string_of_typ ctxt (Envir.norm_type tyenv U) ^ " of term " ^
            Syntax.string_of_term ctxt (Term.map_types (Envir.norm_type tyenv) u),
            [t, u])
        end;
  in (tyenv', maxidx'') end;

val infer = gen_infer term_operations
val cterm_infer = gen_infer cterm_operations

fun incr_instT k (((n, i), S), T) = (((n, i + k), S), T)
fun incr_inst k (((n, i), T), t) = (((n, i + k), Logic.incr_tvar k T), t)
val maxidx_ctyp = Term.maxidx_typ o Thm.typ_of
val maxidx_cterm = Integer.max o Thm.maxidx_of_cterm

fun mk_term ctxt P =
  if Thm.typ_of_cterm P = propT then 
    P 
  else
    \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm P\<close> and P = \<open>Thm.transfer_cterm (Proof_Context.theory_of ctxt) P\<close> 
     in cterm \<open>TERM P\<close> for P::'a\<close>

fun dest_term ct = 
  if can Logic.dest_term (Thm.term_of ct) then 
    Thm.dest_arg ct 
  else 
    ct
   

(* Simultaneous export on instantions and term *)
type 'a morph_operations = {
  mk_typ: Proof.context -> (indexname * sort) -> 'a,
  dest_typ: 'a -> (indexname * sort),
  mk_term: Proof.context -> (indexname * typ) -> 'a,
  dest_term: 'a -> (indexname * typ),
  wrap: Proof.context -> 'a -> 'a,
  unwrap: 'a -> 'a,
  mk_conjunctions: 'a list -> 'a,
  dest_conjunctions: int -> 'a -> 'a list,
  morph: Morphism.morphism -> 'a -> 'a
}

val term_morph_operations: term morph_operations = {
  mk_typ = fn _ => Logic.mk_term o Logic.mk_type o TVar,
  dest_typ = dest_TVar o Logic.dest_type o Logic.dest_term,
  mk_term = fn _ => Logic.mk_term o Var,
  dest_term = dest_Var o Logic.dest_term,
  wrap = K I,
  unwrap = I,
  mk_conjunctions =  Logic.mk_conjunction_list,
  dest_conjunctions = fn _ =>  Logic.dest_conjunction_list,
  morph = Morphism.term
}

val cterm_morph_operations: cterm morph_operations = {
  mk_typ = fn ctxt => Thm.cterm_of ctxt o Logic.mk_term o Logic.mk_type o TVar,
  dest_typ = dest_TVar o Logic.dest_type o Logic.dest_term o Thm.term_of,
  mk_term = fn ctxt => Thm.cterm_of ctxt o Logic.mk_term o Var,
  dest_term = dest_Var o Logic.dest_term o Thm.term_of,
  wrap = mk_term,
  unwrap =  dest_term,
  mk_conjunctions = Conjunction.mk_conjunction_balanced,
  dest_conjunctions = fn _ => Conjunction.dest_conjunctions,
  morph = Morphism.cterm
}

val thm_morph_operations: thm morph_operations = {
  mk_typ = fn ctxt => Thm.reflexive o Thm.cterm_of ctxt o Logic.mk_term o Logic.mk_type o TVar,
  dest_typ = dest_TVar o Logic.dest_type o Logic.dest_term o fst o Logic.dest_equals o Thm.concl_of,
  mk_term = fn ctxt => Thm.reflexive o Thm.cterm_of ctxt o Logic.mk_term o Var,
  dest_term = dest_Var o Logic.dest_term o fst o Logic.dest_equals o Thm.concl_of,
  wrap = K I,
  unwrap = I,
  mk_conjunctions = Conjunction.intr_balanced,
  dest_conjunctions = Conjunction.elim_balanced,
  morph = Morphism.thm
}

fun gen_morph_insts (ops:'a morph_operations) ctxt phi t (type_insts, term_insts) =
  if Morphism.is_identity phi then (t, (type_insts, term_insts))
  else
  let
    val Ts = map (#mk_typ ops ctxt o fst) type_insts
    val ts = map (#mk_term ops ctxt o fst) term_insts
    val n = length Ts + length ts + 1
    val (Ts', t'::ts') = #mk_conjunctions ops (Ts @ #wrap ops ctxt t::ts) 
      |> #morph ops phi 
      |> #dest_conjunctions ops n
      |> chop (length Ts)
    val type_insts' = map (#dest_typ ops) Ts' ~~ map snd type_insts
    val term_insts' = map (#dest_term ops) ts' ~~ map snd term_insts
    val t' = #unwrap ops t'
  in
    (t', (type_insts', term_insts'))
  end

val morph_insts_term = gen_morph_insts term_morph_operations
val morph_insts_cterm = gen_morph_insts cterm_morph_operations
val morph_insts_thm = gen_morph_insts thm_morph_operations

fun prep_insts (insts: insts) =
  let
    val maxidx = ~1
      |> fold Term.maxidx_typ (map snd (#1 insts))
      |> fold Term.maxidx_term (map snd (#2 insts))
    val insts = (map (incr_instT (maxidx + 1)) (#1 insts), map (incr_inst (maxidx + 1)) (#2 insts))
  in (insts, maxidx) end

fun init_tenv tinsts = Vartab.make (map (fn ((xi, S), T) => (xi, (S, T))) tinsts)
fun init_ctenv tinsts = Vartab.make (map (fn ((xi, S), cT) => (xi, (S, Thm.typ_of cT))) tinsts)

fun morph_instantiate_term pos (insts: insts) t phi ctxt =
  let
    val (t, insts) = morph_insts_term ctxt phi t insts
    val (insts, maxidx) = prep_insts insts
    val t = t |> Logic.incr_indexes ([], maxidx + 1)
    val instT = TVars.make (#1 insts);
    val instantiateT = Term_Subst.instantiateT instT;
    val inst = (map o apfst o apsnd) instantiateT (#2 insts);
    val (tyenv, _) = fold (infer ctxt) inst (init_tenv (#1 insts), maxidx + 1)
    val instT = TVars.build (tyenv |> Vartab.fold (fn (xi, (S, T)) =>
          TVars.add ((xi, S), Envir.norm_type tyenv T)));
    val inst = Vars.build (#2 insts |> fold (fn ((xi, T), t) =>
         Vars.add ((xi, Envir.norm_type tyenv T),
          Term_Subst.instantiate (instT, Vars.empty) t)));
  in Term_Subst.instantiate_beta (instT, inst) t end
  handle TERM (msg, args) => Exn.reraise (TERM (msg ^ Position.here pos, args));

fun instantiate_term pos (insts: insts) t = morph_instantiate_term pos (insts: insts) t Morphism.identity
 
fun make_cinsts ctxt maxidx (cinsts: cinsts) =
  let                    
    val cinstT = TVars.make (#1 cinsts);                    
    val instantiateT = Term_Subst.instantiateT (TVars.map (K Thm.typ_of) cinstT);  
    val cinst = (map o apfst o apsnd) instantiateT (#2 cinsts);
    val (tyenv, _) = fold (cterm_infer ctxt) cinst (init_ctenv (#1 cinsts), maxidx + 1)
    val cinstT = TVars.build (tyenv |> Vartab.fold (fn (xi, (S, T)) =>
          TVars.add ((xi, S), Thm.ctyp_of ctxt (Envir.norm_type tyenv T)))); 
    val thy = Proof_Context.theory_of ctxt
    val cinst =
      Vars.build (#2 cinsts |> fold (fn ((xi, T), cu) =>
        Vars.add ((xi, Envir.norm_type tyenv T),
          Thm.instantiate_cterm (cinstT, Vars.empty) (Thm.transfer_cterm thy cu))));
  in (cinstT,  cinst) end;

fun prep_cinsts cinsts =
 let
    val maxidx = ~1
      |> fold maxidx_ctyp (map snd (#1 cinsts))
      |> fold maxidx_cterm (map snd (#2 cinsts))
    val cinsts = (map (incr_instT (maxidx + 1)) (#1 cinsts), map (incr_inst (maxidx + 1)) (#2 cinsts))
  in (cinsts, maxidx) end

fun morph_instantiate_cterm pos cinsts ct phi ctxt =
  let
    val (ct, cinsts) = morph_insts_cterm ctxt phi ct cinsts 
    val (cinsts, maxidx) = prep_cinsts cinsts
    val ct = Thm.incr_indexes_cterm (maxidx + 1) ct 
  in
    Thm.instantiate_beta_cterm (make_cinsts ctxt maxidx cinsts) ct
  end
  handle CTERM (msg, args) => Exn.reraise (CTERM (msg ^ Position.here pos, args))
       | TERM (msg, args) => Exn.reraise (TERM (msg ^ Position.here pos, args));

fun instantiate_cterm pos cinsts ct = morph_instantiate_cterm pos cinsts ct Morphism.identity

fun morph_instantiate_thm pos cinsts th phi ctxt =
  let
    val (th, cinsts) = morph_insts_thm ctxt phi th cinsts
    val (cinsts, maxidx) = prep_cinsts cinsts
    val th = Thm.incr_indexes (maxidx + 1) th
  in
    Thm.instantiate_beta (make_cinsts ctxt maxidx cinsts) th
  end
  handle THM (msg, i, args) => Exn.reraise (THM (msg ^ Position.here pos, i, args))
       | TERM (msg, args) => Exn.reraise (TERM (msg ^ Position.here pos, args));

fun instantiate_thm pos cinsts th = morph_instantiate_thm pos cinsts th Morphism.identity

fun morph_instantiate_thms pos cinsts ths phi ctxt = map (fn th => morph_instantiate_thm pos cinsts th phi ctxt) ths;

fun instantiate_thms pos cinsts ths = morph_instantiate_thms pos cinsts ths Morphism.identity


(* context data *)

structure Data = Proof_Data
(
  type T = int * thm list Inttab.table;
  fun init _ = (0, Inttab.empty);
);

fun put_thms ths ctxt =
  let
    val (i, thms) = Data.get ctxt;
    val ctxt' = ctxt |> Data.put (i + 1, Inttab.update (i, map Thm.trim_context ths) thms);
  in (i, ctxt') end;

fun get_thms ctxt i = the (Inttab.lookup (#2 (Data.get ctxt)) i);
fun get_thm ctxt i = the_single (get_thms ctxt i);


(* ML antiquotation *)

local

val make_keywords =
  Thy_Header.get_keywords'
  #> Keyword.no_major_keywords
  #> Keyword.add_major_keywords ["term", "prop", "cterm", "cprop", "lemma"];

val parse_inst_name = Parse.position (Parse.type_ident >> pair true || Parse.name >> pair false);

val parse_inst =
  (parse_inst_name -- (Parse.$$$ "=" |-- Parse.!!! Parse.embedded_ml) ||
    Scan.ahead parse_inst_name -- Parse.embedded_ml)
  >> (fn (((b, a), pos), ml) => (b, ((a, pos), ml)));

val parse_insts =
  Parse.and_list1 parse_inst >> (List.partition #1 #> apply2 (map #2));

val ml = ML_Lex.tokenize_no_range;
val ml_range = ML_Lex.tokenize_range;
fun ml_parens x = ml "(" @ x @ ml ")";
fun ml_bracks x = ml "[" @ x @ ml "]";
fun ml_commas xs = flat (separate (ml ", ") xs);
val ml_list = ml_bracks o ml_commas;
fun ml_pair (x, y) = ml_parens (ml_commas [x, y]);
val ml_list_pair = ml_list o ListPair.map ml_pair;
val ml_here = ML_Syntax.atomic o ML_Syntax.print_position;

fun get_tfree envT (a, pos) =
  (case AList.lookup (op =) envT a of
    SOME S => (a, S)
  | NONE => error ("No occurrence of type variable " ^ quote a ^ Position.here pos));

fun check_free ctxt env (x, pos) =
  (case AList.lookup (op =) env x of
    SOME T =>
      (Context_Position.reports ctxt (map (pair pos) (Syntax_Phases.markup_free ctxt x)); (x, T))
  | NONE => error ("No occurrence of variable " ^ quote x ^ Position.here pos));

fun missing_instT pos envT instT =
  (case filter_out (fn (a, _) => exists (fn (b, _) => a = b) instT) envT of
    [] => ()
  | bad =>
      error ("No instantiation for free type variable(s) " ^ commas_quote (map #1 bad) ^
        Position.here pos))
fun missing_inst pos env inst =
  (case filter_out (fn (a, _) => exists (fn (b, _) => a = b) inst) env of
    [] => ()
  | bad =>
      error ("No instantiation for free variable(s) " ^ commas_quote (map #1 bad) ^
        Position.here pos));

fun make_instT (a, pos) T =
  (case try (Term.dest_TVar o Logic.dest_type) T of
    NONE => error ("Not a free type variable " ^ quote a ^ Position.here pos)
  | SOME v => ml (ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_sort v));

fun make_inst (a, pos) t =
  (case try Term.dest_Var t of
    NONE => error ("Not a free variable " ^ quote a ^ Position.here pos)
  | SOME v => ml (ML_Syntax.print_pair ML_Syntax.print_indexname ML_Syntax.print_typ v));

fun make_env ts =
  let
    val envT = fold Term.add_tfrees ts [];
    val env = fold Term.add_frees ts [];
  in (envT, env) end;

fun prepare_insts morph pos {schematic} ctxt1 ctxt0 (instT, inst) ts =
  let
    val (envT, env) = make_env ts;
    val freesT = map (Logic.mk_type o TFree o get_tfree envT) instT;
    val frees = map (Free o check_free ctxt1 env) inst;
    val (ts', (varsT, vars)) =
      Variable.export_terms ctxt1 ctxt0 (ts @ freesT @ frees)
      |> chop (length ts) ||> chop (length freesT);
    val ml_insts = (map2 make_instT instT varsT, map2 make_inst inst vars);
  in
    if schematic then ()
    else
      let val (envT', env') = make_env ts' 
        val holes = subtract (eq_fst op =) env' env
        val inferableTs = fold Term.add_tfreesT (map snd holes) []
        val holesT = subtract (eq_fst op =) envT' envT
        val _ = if null holesT andalso not morph
            then warning ("All type instances are already explict and do not have to be" ^
                    " inferred from the term instantiations.\n " ^ 
                    "Use antiquotation 'instantiate' instead." ^ Position.here pos)
            else ()
        val holesT = subtract (eq_fst op =) inferableTs holesT
      in
        missing_instT pos holesT instT;
        missing_inst pos holes inst
      end;
    (ml_insts, ts')
  end;

fun prepare_ml range kind ml1 ml2 ml_val (ml_instT, ml_inst) ctxt =
  let
    val (ml_name, ctxt') = ML_Context.variant kind ctxt;
    val ml_env = ml ("val " ^ ml_name ^ " = ") @ ml ml1 @ ml_parens (ml ml_val) @ ml ";\n";
    fun ml_body (ml_argsT, ml_args) =
      ml_parens (ml ml2 @
        ml_pair (ml_list_pair (ml_instT, ml_argsT), ml_list_pair (ml_inst, ml_args)) @
        ml_range range (ML_Context.struct_name ctxt ^ "." ^ ml_name));
  in ((ml_env, ml_body), ctxt') end;

fun prepare_term morph read range ((((kind, pos), ml1, ml2), schematic), (s, fixes)) insts ctxt =
  let
    val ctxt' = #2 (Proof_Context.add_fixes_cmd fixes ctxt);
    val t = read ctxt' s;
    val ctxt1 = Proof_Context.augment t ctxt';
    val (ml_insts, t') = prepare_insts morph pos schematic ctxt1 ctxt insts [t] ||> the_single;
  in prepare_ml range kind ml1 ml2 (ML_Syntax.print_term t') ml_insts ctxt end;

fun prepare_lemma morph range ((pos, schematic), make_lemma) insts ctxt =
  let
    val (ths, (props, ctxt1)) = make_lemma ctxt
    val (i, thms_ctxt) = put_thms ths ctxt;
    val ml_insts = #1 (prepare_insts morph pos schematic ctxt1 ctxt insts props);
    val ml_instantiate_thm = 
      if morph then 
        "ML_Infer_Instantiate.morph_instantiate_thm " 
        else 
        "ML_Infer_Instantiate.instantiate_thm "
    val ml_instantiate_thms = 
      if morph then 
        "ML_Infer_Instantiate.morph_instantiate_thms " 
        else 
        "ML_Infer_Instantiate.instantiate_thms "
    val (ml1, ml2) =
      if length ths = 1
      then ("ML_Infer_Instantiate.get_thm ML_context", 
              ml_instantiate_thm ^ ml_here pos)
      else ("ML_Infer_Instantiate.get_thms ML_context", 
              ml_instantiate_thms ^ ml_here pos);
  in prepare_ml range "lemma" ml1 ml2 (ML_Syntax.print_int i) ml_insts thms_ctxt end;

fun term_ml morph (kind, pos: Position.T) = 
  let
    val ml_instantiate_term = 
      if morph then 
        "ML_Infer_Instantiate.morph_instantiate_term " 
      else 
        "ML_Infer_Instantiate.instantiate_term "
  in
    ((kind, pos), "", ml_instantiate_term ^ ml_here pos)
  end

fun cterm_ml morph (kind, pos) =
  let
    val ml_instantiate_cterm = 
      if morph then 
        "ML_Infer_Instantiate.morph_instantiate_cterm " 
      else 
        "ML_Infer_Instantiate.instantiate_cterm "
  in
    ((kind, pos),
      "ML_Infer_Instantiate.make_cterm ML_context", 
         ml_instantiate_cterm ^ ml_here pos)
  end

val command_name = Parse.position o Parse.command_name;

val parse_schematic = Args.mode "schematic" >> (fn b => {schematic = b});

fun parse_body morph range =
  (command_name "term" >> term_ml morph || command_name "cterm" >> cterm_ml morph) -- parse_schematic --
    Parse.!!! (Parse.term -- Parse.for_fixes) >> prepare_term morph Syntax.read_term range ||
  (command_name "prop" >> term_ml morph || command_name "cprop" >> cterm_ml morph) -- parse_schematic --
    Parse.!!! (Parse.term -- Parse.for_fixes) >> prepare_term morph Syntax.read_prop range ||
  (command_name "lemma" >> #2) -- parse_schematic -- ML_Thms.embedded_lemma >> prepare_lemma morph range;

fun antiquotation morph =
 (fn range => fn src => fn ctxt =>
      let
        val (insts, prepare_val) = src
          |> Parse.read_embedded ctxt (make_keywords ctxt)
              ((parse_insts --| Parse.$$$ "in") -- parse_body morph range);

        val (((ml_env, ml_body), decls), ctxt1) = ctxt
          |> prepare_val (apply2 (map #1) insts)
          ||>> ML_Context.expand_antiquotes_list (op @ (apply2 (map #2) insts));
      
        fun decl' ctxt' =
          let val (ml_args_env, ml_args) = split_list (decls ctxt')
          in (ml_env @ flat ml_args_env, ml_body (chop (length (#1 insts)) ml_args)) end;   
      in (decl', ctxt1) end)

val _ = Theory.setup
  (ML_Context.add_antiquotation_embedded \<^binding>\<open>infer_instantiate\<close> (antiquotation false) #>
   ML_Context.add_antiquotation_embedded \<^binding>\<open>morph_infer_instantiate\<close> (antiquotation true)) 

in end;

end
\<close>

text \<open>Here an example with explicit instantiation.\<close>
ML_val \<open>
val b = Free("n", \<^typ>\<open>nat\<close>)
val t1 = \<^instantiate>\<open>'a = \<^typ>\<open>nat\<close> and a = \<open>@{term "1::nat"}\<close> and b=\<open>b\<close> 
      in term  \<open>a + b\<close> for a b::"'a::plus"\<close>
\<close>

text \<open>With the new variant the type instantiation can be omitted as it is already inferred
from the term instantiations. Note that the result of the antiquotation is function that
expects a @{ML_type Proof.context}. This is used to perform the necessary type inference and provide
context sensitive error messages. \<close>

ML_val \<open>
val b = Free("n", \<^typ>\<open>nat\<close>)
val t1 = \<^infer_instantiate>\<open>a =\<^term>\<open>1::nat\<close> and b=\<open>b\<close> 
      in term  \<open>a + b\<close> for a b::"'a::plus"\<close> @{context}
\<close>

text \<open>This can be shortened:\<close>

ML_val \<open>
val b = Free("n", \<^typ>\<open>nat\<close>)
val t1 = \<^infer_instantiate>\<open>a = \<^term>\<open>1::nat\<close> and b=\<open>b\<close> 
      in term  \<open>a + b\<close>\<close> @{context}
\<close>

text \<open>Here is an example were not all type variables can be inferred from the term
instantiation. Those types can be explicitly instantiated.\<close>
ML_val \<open>
val t1 = \<^infer_instantiate>\<open>'b = \<^typ>\<open>int\<close> and a = \<open>@{term "1::nat"}\<close>  
      in term  \<open>Pair a\<close> for a ::'a \<close> @{context}
\<close>

ML_val \<open>
val t1 = \<^morph_infer_instantiate>\<open>'b = \<^typ>\<open>int\<close> and a = \<open>@{term "1::nat"}\<close>  
      in term  \<open>Pair a\<close> for a ::'a \<close> Morphism.identity @{context}
\<close>

ML_val \<open>
val v = Proof_Context.read_term_pattern @{context} "v"
val t1 = \<^infer_instantiate>\<open>'b = \<^typ>\<open>int\<close> and a = v  
      in term  \<open>Pair a\<close> for a ::'a \<close> @{context}
\<close>

ML_val \<open>
val v = Proof_Context.read_term_pattern @{context} "v::'a::type" |> Thm.cterm_of @{context}
val t1 = \<^infer_instantiate>\<open>'b = \<^ctyp>\<open>int\<close> and a = v  
      in cterm  \<open>Pair a\<close> for a ::'a \<close> @{context}
\<close>

ML_val \<open>
val t1 = \<^infer_instantiate>\<open>'b = \<^ctyp>\<open>int\<close> and a = \<open>@{cterm "1::nat"}\<close>  
      in cterm  \<open>Pair a\<close> for a ::"'a" \<close> @{context}
\<close>

context 
  fixes x::"'a::plus"
begin
ML_val \<open>
val b = Free("n", \<^typ>\<open>nat\<close>)
val t1 = \<^infer_instantiate>\<open>a = \<open>@{term "1::nat"}\<close> and b=\<open>b\<close> 
in term  \<open>a + b\<close> for a b\<close> @{context}
\<close>
end
text \<open>Note that the antiquotation only makes some local type-inference on the term parameters
alone. There might be further use cases to perform a type inference on the whole term instead.
This might be further fine-tuned by inserting explicit dummy types to be inferred: \<^typ>\<open>_\<close>.
\<close>

ML \<open>
fun infer_types_simple ctxt =
   singleton (Type_Infer_Context.infer_types ctxt) #>
   singleton (Type_Infer.fixate ctxt false);

val b = Free("n", dummyT)
val t1 = \<^instantiate>\<open>'a = \<^typ>\<open>_\<close> and a = \<open>@{term "1::nat"}\<close> and b=\<open>b\<close> 
in prop  \<open>a + b = a + b\<close> for a b::"'a::plus" \<close> |> infer_types_simple @{context}
\<close>

end