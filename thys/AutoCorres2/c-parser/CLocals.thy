
section \<open>Modelling Local Variables\<close>

theory CLocals
  imports UMM
   "HOL-Library.Code_Binary_Nat"
   "ML_Record_Antiquotation"
begin


ML \<open>
structure Code_Simproc =
struct

val meta_eq_to_prop = @{lemma \<open>(PROP P \<equiv> Trueprop True) \<Longrightarrow> PROP P\<close> for P by simp}

fun solved_eq eq =
  case Thm.prop_of eq of
    @{term_pat "_ \<equiv> Trueprop True"} => true
    | _ => false


fun code_prove ctxt prop =
  let
    val code_eq = SOME (Code_Runtime.dynamic_holds_conv ctxt prop) handle ERROR x => (warning x; NONE)
    val _ = Utils.verbose_msg 4 ctxt (fn _ => "code_prove: " ^ @{make_string} code_eq)
  in
    code_eq |> Option.mapPartial (fn eq =>
      if solved_eq eq then
        SOME (meta_eq_to_prop OF [Code_Simp.dynamic_conv ctxt prop])
      else NONE)
  end

fun fill_default default xs =
  let
    fun fill ys _ [] = rev ys
      | fill ys n (zs as ((i, z)::zs')) =
         if n = i then
           fill (z::ys) (n + 1) zs'
         else
           if n < i then fill (default::ys) (n + 1) zs
         else error ("fill_default: expecting indexes in ascending order" ^ @{make_string} (map fst xs))
  in
    fill [] 0 xs
  end

fun code_simp_prems cond_eq_rule0 ps ctxt ct =
  let
    val cond_eq_rule = Thm.transfer' ctxt cond_eq_rule0
    val _ = Utils.verbose_msg 4 ctxt (fn _ => "code_simp_prems: " ^ @{make_string} (ct, cond_eq_rule))
    val ps = sort int_ord ps
    val lhs = cond_eq_rule |> Thm.cconcl_of |> Thm.dest_equals_lhs
    val eq = Thm.instantiate (Thm.match (lhs, ct)) cond_eq_rule
    val prems = Thm.cprems_of eq
    fun solve i = code_prove ctxt (nth prems i)
    val solved = map_filter solve ps
  in
    if length solved = length ps then
      SOME (eq OF (fill_default Drule.asm_rl (ps ~~ solved)))
    else
      NONE
  end

fun is_eq (@{term_pat "Trueprop (_ = _)"}) = true
  | is_eq (@{term_pat "_ \<equiv> _"}) = true
  | is_eq _ = false

fun positions_of len interval =
  case interval of
    Facts.FromTo (i, j) => (@{assert} (j <= len) ; (i - 1) upto (j - 1))
  | Facts.From i => (@{assert} (i <= len) ; (i - 1) upto (len - 1))
  | Facts.Single i => (@{assert} (i <= len); [i - 1])

fun positions_of_intervals len =
  map (positions_of len) #> flat #> sort_distinct int_ord

fun lhs_pattern ctxt eq =
 let
   val ((_, [eq]), _) = Variable.import false [eq] ctxt
 in
   eq |> Thm.concl_of |> Logic.dest_equals |> fst
 end

structure Data = Generic_Data (
  type T = simproc list Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K false))

fun get_simprocs ctxt named_thms =
 let
   val simprocs = Data.get (Context.Proof ctxt)
 in
   Symtab.lookup_list simprocs named_thms
 end

(* piggy back name-space of named theorems *)
fun check context named_thms =
  let
    val ctxt = Context.proof_of context
    val facts = (Proof_Context.facts_of ctxt);
  in
    Facts.check context facts named_thms
  end

fun add_simproc pos named_thms (intervals: Facts.interval list) thm context =
  let
    val ctxt = Context.proof_of context
    val named_thms = if fst (named_thms) = "" then "" else (check context named_thms )
    val _ = is_eq (Thm.concl_of thm) orelse error ("Code_Simproc.add_simproc: conclusion is not an equality")
    val _ = Thm.has_name_hint thm orelse error ("Code_Simproc.add_simproc: theorem has no name")
    val name_hint = Thm_Name.short (Thm.get_name_hint thm)
    val base_name = Long_Name.base_name name_hint
    val thm1 = safe_mk_meta_eq thm
    val nprems = Thm.nprems_of thm1
    val _ = nprems > 0 orelse error ("Code_Simproc.add_simprocs: theorem has no premises")
    val positions = if null intervals then 0 upto nprems - 1 else positions_of_intervals nprems intervals
    val patterns = thm1 |> lhs_pattern ctxt |> single
    val thm2 = Thm.trim_context thm1
  in
    if Local_Theory.level ctxt = 0 then context
    else
      context 
      |> Context.map_proof_result (Simplifier.define_simproc {name = Binding.make (base_name, pos), passive=false, identifier=[],
           lhss = patterns, proc = fn _ => code_simp_prems thm2 positions})
      |-> (fn simproc => Context.map_proof (
            Local_Theory.declaration {pervasive=false, syntax=false, pos = \<^here>} (fn _ =>
              (Data.map (Symtab.map_default (named_thms, [simproc]) (cons simproc))))))
  end
end
\<close>


setup \<open>
let
  fun position scan = (Scan.ahead (Scan.one (K true)) >> Token.pos_of) -- scan >> Library.swap;
in
  Attrib.setup \<^binding>\<open>code_simproc\<close>
    (Scan.lift (position
      (Scan.optional Parse.name_position ("", Position.none) -- Scan.optional Parse.thm_sel []) >>
    (fn ((named_thms, intervals), pos) =>
      Thm.declaration_attribute (fn thm => Code_Simproc.add_simproc pos named_thms intervals thm))))
    "solve preconditions with code_simp" #>
  ML_Antiquotation.value_embedded \<^binding>\<open>code_simprocs\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => "Code_Simproc.get_simprocs ML_context " ^
         ML_Syntax.print_string (Code_Simproc.check (Context.Proof ctxt) name)))
end
\<close>

ML \<open>
String.str
\<close>
type_synonym locals = "nat \<Rightarrow> byte list"


definition "clookup" :: "nat \<Rightarrow> locals \<Rightarrow> 'a::mem_type" where
  "clookup n l = from_bytes (l n)"

definition "cupdate" :: "nat \<Rightarrow> ('a::mem_type \<Rightarrow> 'a) \<Rightarrow> locals \<Rightarrow> locals" where
  "cupdate n f l = l(n := to_bytes (f (from_bytes (l (n)))) (replicate (size_of TYPE('a)) 0))"

lemma clookup_cupdate_same[simp, state_simp]: "clookup n (cupdate n f l) = f (clookup n l)"
  by (simp add: clookup_def cupdate_def)

lemma clookup_cupdate_same_cond[code_simproc state_simp]:
  "n = 0 \<Longrightarrow> clookup n (cupdate 0 f l) = f (clookup n l)"
  "n = 0 \<Longrightarrow> clookup 0 (cupdate n f l) = f (clookup n l)"
  "n = 1 \<Longrightarrow> clookup n (cupdate 1 f l) = f (clookup n l)"
  "n = Suc 0 \<Longrightarrow> clookup n (cupdate (Suc 0) f l) = f (clookup n l)"
  "n = 1 \<Longrightarrow> clookup 1 (cupdate n f l) = f (clookup n l)"
  "n = Suc 0 \<Longrightarrow> clookup (Suc 0) (cupdate n f l) = f (clookup n l)"
  "n = numeral m \<Longrightarrow> clookup n (cupdate (numeral m) f l) = f (clookup n l)"
  "n = numeral m \<Longrightarrow> clookup (numeral m) (cupdate n f l) = f (clookup n l)"
  by (auto simp add: clookup_def cupdate_def)

lemma clookup_refl_cond[code_simproc state_simp]:
  "n = m  \<Longrightarrow> clookup n l = clookup m l \<longleftrightarrow> True"
  by (simp_all add: clookup_def)

lemma clookup_cupdate_other[code_simproc state_simp]: "n \<noteq> m \<Longrightarrow> clookup n (cupdate m f l) = (clookup n l)"
  by (auto simp add: clookup_def cupdate_def)

lemma cupdate_compose[simp, state_simp]: "cupdate n f (cupdate n g l) = cupdate n (f o g) l"
  by (simp add: cupdate_def)

lemma cupdate_compose_cond[code_simproc state_simp]:
  "n = 0 \<Longrightarrow> cupdate n f (cupdate 0 g l) = cupdate n (f o g) l"
  "n = 0 \<Longrightarrow> cupdate 0 f (cupdate n g l) = cupdate n (f o g) l"
  "n = 1 \<Longrightarrow> cupdate n f (cupdate 1 g l) = cupdate n (f o g) l"
  "n = Suc 0 \<Longrightarrow> cupdate n f (cupdate (Suc 0) g l) = cupdate n (f o g) l"
  "n = Suc 0 \<Longrightarrow> cupdate (Suc 0) f (cupdate n g l) = cupdate n (f o g) l"
  "n = numeral m \<Longrightarrow> cupdate n f (cupdate (numeral m) g l) = cupdate n (f o g) l"
  "n = numeral m \<Longrightarrow> cupdate (numeral m) f (cupdate n g l) = cupdate n (f o g) l"
  by (auto simp add: cupdate_def)

lemma clookup_cupdate_other_numeral[simplified, simp, state_simp]:
  "clookup 0 (cupdate 1 f l) = (clookup 0 l)"
  "clookup 0 (cupdate (numeral m) f l) = (clookup 0 l)"
  "clookup 1 (cupdate 0 f l) = (clookup 1 l)"
  "numeral m \<noteq> (1::nat) \<Longrightarrow>
   clookup 1 (cupdate (numeral m) f l) = (clookup 1 l)"


  "clookup (numeral n) (cupdate 0 f l) = (clookup (numeral n) l)"
  "numeral n \<noteq> (1::nat) \<Longrightarrow>
   clookup (numeral n) (cupdate 1 f l) = (clookup (numeral n) l)"

  "n \<noteq> m \<Longrightarrow>
   clookup (numeral n) (cupdate (numeral m) f l) = (clookup (numeral n) l)"
  by (auto simp add: clookup_def cupdate_def)

lemma cupdate_commute: "n \<noteq> m \<Longrightarrow> cupdate n f (cupdate m g l) = cupdate m g (cupdate n f l)"
  by (auto simp add: cupdate_def fun_upd_def)

lemma cupdate_commute_ordered[code_simproc state_simp]: "n < m \<Longrightarrow> cupdate n f (cupdate m g l) = cupdate m g (cupdate n f l)"
  by (auto simp add: cupdate_def fun_upd_def)

lemma cupdate_commute_numeral_simp[simplified, simp, state_simp]:
  "cupdate 0 f (cupdate 1 g l) = cupdate 1 g (cupdate 0 f l)"
  "cupdate 0 f (cupdate (numeral m) g l) = cupdate (numeral m) g (cupdate 0 f l)"

  "numeral m \<noteq> (1::nat) \<Longrightarrow>
   cupdate 1 f (cupdate (numeral m) g l) = cupdate (numeral m) g (cupdate 1 f l)"

  "n < m \<Longrightarrow> cupdate (numeral n) f (cupdate (numeral m) g l) = cupdate (numeral m) g (cupdate (numeral n) f l)"
  by (auto simp add: cupdate_def fun_upd_def)


lemma const_compose [simp, state_simp]:
  "cupdate n ((\<lambda>_. x) \<circ> f) = cupdate n (\<lambda>_. x)"
  "cupdate n (f \<circ> (\<lambda>_. x)) = cupdate n (\<lambda>_. f x)"
  by (auto simp add: comp_def)

lemma K_eq_cong: "((\<lambda>_. x) = (\<lambda>_. y)) \<longleftrightarrow> x = y"
  by (simp add: fun_eq_iff)

ML_file \<open>positional_symbol_table.ML\<close>

named_theorems locals

consts clocals_string_embedding :: "string \<Rightarrow> nat" 
consts exit_'::nat

definition "global_exn_var_clocal = clocals_string_embedding ''global_exn_var''"

bundle clocals_string_embedding
begin
notation clocals_string_embedding ("\<S>")
end

ML \<open>
structure CLocals =
struct
structure Locals = Positional_Symbol_Table(type key = string val ord = fast_string_ord);

@{record \<open>datatype entry = Entry of {typ : typ, term: term, def: thm, kind: NameGeneration.var_kind}\<close>}

fun morph_entry phi {typ, term, def, kind} = make_entry
  {typ = Morphism.typ phi typ, term = Morphism.term phi term, def = Morphism.thm phi def, kind = kind};

fun entry_ord (Entry {kind = kind1, typ = T1, term = t1, def = thm1}, Entry {kind = kind2, typ = T2, term = t2, def = thm2})
  = prod_ord NameGeneration.var_kind_ord (prod_ord Term_Ord.typ_ord (prod_ord Term_Ord.fast_term_ord Thm.thm_ord))
      ((kind1, (T1, (t1, thm1))), (kind2, ((T2, (t2, thm2)))))

val entry_eq = is_equal o entry_ord

type locals_scope = {locals: entry Locals.symbol_table, scope: Locals.qualifier}

structure Data = Generic_Data (struct
  type T = locals_scope
  val empty = {locals = Locals.empty, scope = []}
  fun merge ({locals=locals1, ...}, {locals=locals2, ...}) =
       {locals = Locals.merge entry_eq (locals1, locals2),
        scope = []}
  end)

fun map_locals f ({locals, scope}:locals_scope) =
  ({locals = f locals, scope = scope}:locals_scope)

fun map_scope f ({locals, scope}:locals_scope) = ({locals = locals, scope = f scope}:locals_scope)


fun locals_map f  = Data.map (map_locals f)
fun scope_map f  = Data.map (map_scope f)
fun enter_scope n = map_scope (fn xs => xs @ [n])
val exit_scope = map_scope (fst o split_last)

fun switch_scope fname =
 Context.proof_map (Data.map (exit_scope #> enter_scope fname))


fun program_name ctxt =
  case #scope (Data.get (Context.Proof ctxt)) of
     (prog_name::_) => prog_name
   | _ => ""

fun function_name ctxt =
  case #scope (Data.get (Context.Proof ctxt)) of
    [_, fun_name] => fun_name
  | _ => ""

fun read_function_pointer ctxt s =
  let
     val s = if Long_Name.is_qualified s then s else Long_Name.qualify (program_name ctxt) s
  in
    Proof_Context.read_const {proper=true, strict=true} ctxt s
  end

fun mk_lookup_positional T i =
  \<^Const>\<open>clookup T\<close> $ HOLogic.mk_number @{typ nat} i

fun lookup_by_short_name ctxt x =
  let
    val {scope, locals} = Data.get (Context.Proof ctxt)
    val x = NameGeneration.un_varname x
    val (qualifier, base) = Long_Name.explode x |> split_last
    val common_scope = rev scope |> drop (length qualifier) |> rev
    val full_scope = (if null common_scope then scope else common_scope) @ qualifier
    fun proj (name,  (pos, Entry {typ, term,...})) = (name, (typ, term))
    val hits =
         Locals.lookup locals full_scope base |> Option.map (proj o pair x)
  in
    case hits of
      SOME v => v
    | NONE => error ("lookup_by_short_name: " ^ quote base ^ " not defined in scope " ^ @{make_string} full_scope)
  end

fun info_from_term ctxt t =
  let
    val {scope, locals} = Data.get (Context.Proof ctxt)
  in
    case t of
      Const (n, _) =>
        let
          val name = NameGeneration.un_varname (Long_Name.base_name n)
        in Locals.lookup locals scope name |> Option.map (fn (p, x) => (name, (p, x))) end
    | _ => try Utils.dest_nat_or_number t
           |> Option.mapPartial (fn p =>
                Locals.lookup_positional locals scope p
                |> Option.map (fn (name, x) => (name, (p, x))))
  end

fun kind_from_term ctxt t = info_from_term ctxt t
    |> Option.map (fn (_, (_, Entry {kind, ...})) => kind)

fun is_defined ctxt x =
  is_some (try (lookup_by_short_name ctxt) x)

fun gen_mk_lookup ctxt (NameGeneration.Named x) =
     let val (_, (typ, term)) = lookup_by_short_name ctxt x
     in (\<^Const>\<open>clookup typ\<close> $ term, typ) end
  | gen_mk_lookup _ (NameGeneration.Positional (i, T)) =
      (\<^Const>\<open>clookup T\<close> $ HOLogic.mk_number @{typ nat} i, T)

fun get_position ctxt n =
 let
   val {scope, locals} = Data.get (Context.Proof ctxt)
 in Locals.lookup locals scope n |> Option.map fst end

fun get_default_position ctxt n = the_default (~1) (get_position ctxt n)


fun positional_ord ctxt = int_ord o apply2 (get_default_position ctxt)
fun get_locals ctxt  =
  let
    val {scope, locals} = Data.get (Context.Proof ctxt)
    val locals = Locals.get_scope (locals) scope
  in
    locals
    |> Locals.Keytab.dest
    |> map (fn (n, (_, Entry {typ, term, ...})) =>
        (Long_Name.base_name n, (typ, (\<^Const>\<open>clookup typ\<close> $ term))))
  end

fun mk_lookup ctxt x = fst (gen_mk_lookup ctxt (NameGeneration.Named x))

fun mk_update ctxt x =
  let val (_, (typ, term)) = lookup_by_short_name ctxt x
  in \<^Const>\<open>cupdate typ\<close> $ term end

fun mk_update_positional T i =
  \<^Const>\<open>cupdate T\<close> $ HOLogic.mk_number @{typ nat} i

fun get_name ctxt n = \<^try>\<open>
  let val (n, (typ, _)) = lookup_by_short_name ctxt n
  in (n, typ) end
  catch _ => raise Match\<close>

(* Name hints for bound variable names. Special treatment to unprime return variable name *)
fun return_name_hint "ret" = "ret'"
  | return_name_hint x = x

fun dest_return_name_hint "ret'" = "ret"
  | dest_return_name_hint x = x

fun embedded_name_hint n = @{const clocals_string_embedding} $ Utils.encode_isa_string n

fun name_hint ctxt n =
 if n = NameGeneration.global_exn_var_name then
   @{const global_exn_var_clocal}
 else
   (case try (lookup_by_short_name ctxt) (return_name_hint n) of
     SOME (_, (_, term)) => term
   | NONE =>
      let
        val _ = warning ("name_tag: no match for " ^ quote n ^ ". Using string embedding.")
      in
        embedded_name_hint n
      end)

fun name_hints ctxt = map (name_hint ctxt) #> Utils.encode_isa_list @{typ nat}

fun dest_name_hint (\<^Const_>\<open>clocals_string_embedding for s\<close>) = HOLogic.dest_string s
  | dest_name_hint (\<^const>\<open>global_exn_var_clocal\<close>) = NameGeneration.global_exn_var_name
  | dest_name_hint (Const (n, @{typ nat})) = dest_return_name_hint (NameGeneration.un_varname (Long_Name.base_name n))
  | dest_name_hint _ = raise Match

val dest_name_hints = Utils.decode_isa_list #> map dest_name_hint

fun split_scope n =
  case rev (Long_Name.explode n) of
    (base:: fname :: prog_name:: _) => ([prog_name, fname], base)
  | _ => raise Match

fun strip_common [] [] = []
  | strip_common (x::xs) (y::ys) = if x = y then strip_common xs ys else (y::ys)
  | strip_common [] ys = ys
  | strip_common _ [] = []


val short_names = Attrib.setup_config_bool \<^binding>\<open>clocals_short_names\<close> (K false);

fun print_tr ctxt (c as (Const (n, T))) =
      let
        val {scope, locals} = Data.get (Context.Proof ctxt)
        val (name_scope, base_name) = split_scope n
        val base_name = NameGeneration.un_varname base_name
        val min_scope = strip_common scope name_scope
        val short_name = base_name
           |> not (Config.get ctxt short_names) ? fold Long_Name.qualify min_scope
       in
        case Locals.lookup locals name_scope base_name of
          SOME (_, Entry {typ, ...}) =>
            Syntax.const \<^syntax_const>\<open>_constrain\<close> $ Const (short_name, T) $ Syntax_Phases.term_of_typ ctxt typ
         | _  => raise Match
      end
  | print_tr _ t = raise Match

fun is_lookup ctxt (Const (@{const_name clookup}, _ ) $ _) = true
  | is_lookup ctxt (Const (@{const_syntax clookup}, _ ) $ _) = true
  | is_lookup ctxt _ = raise Match

fun lookup_tr' ctxt (Const (@{const_name clookup}, _ ) $ (c as Const _)) = print_tr ctxt c
  | lookup_tr' ctxt (Const (@{const_syntax clookup}, _ ) $ (c as Const _)) = print_tr ctxt c
  | lookup_tr' ctxt t = raise Match

fun dest_update_tr' ctxt ((c as (Const (@{const_syntax cupdate}, _ ) $  Const _ )) $ v $ s) =
      (c, v, SOME s)
  | dest_update_tr' ctxt ((c as (Const (@{const_name cupdate}, _ ) $  Const _ )) $ v $ s) =
      (c, v, SOME s)
  | dest_update_tr' ctxt ((c as (Const (@{const_syntax cupdate}, _ ) $  Const _ )) $ v) =
      (c, v, NONE)
  | dest_update_tr' ctxt ((c as (Const (@{const_name cupdate}, _ ) $  Const _ )) $ v) =
      (c, v, NONE)
  | dest_update_tr' ctxt t = raise Match

fun update_tr' ctxt (Const (@{const_name cupdate}, _ ) $ (c as Const _)) = print_tr ctxt c
  | update_tr' ctxt (Const (@{const_syntax cupdate}, _ ) $ (c as Const _)) = print_tr ctxt c
  | update_tr' ctxt t = t

fun locals_insert qualifier pos name typ kind def tab =
  let
    val tab' = tab |> Locals.update_new qualifier (name, 
      Entry {typ=typ, term = Thm.concl_of def |> Utils.lhs_of_eq, def = Thm.trim_context def, kind = kind})
    val _ = @{assert} ((Locals.lookup tab' qualifier name |> Option.map fst) = SOME pos)
  in
    tab'
  end

fun add_entry qualifier pos name typ kind def =
 locals_map (locals_insert qualifier pos name typ kind def)

fun add_entry_attr qualifier pos name typ kind =
  Thm.declaration_attribute (add_entry qualifier pos name typ kind)


fun define_locals qualifier decls thy =
  let
    val _ = @{assert} (not (null qualifier))
    val fname = split_last qualifier |> snd
    val lthy = Named_Target.theory_init thy
    fun define (i, (name, typ, kind)) lthy =
      let
        val vname = NameGeneration.ensure_varname name
        val b = Binding.make (vname, \<^here>) |> fold_rev (Binding.qualify true) qualifier
        val attrib = Attrib.internal \<^here> (fn _ => add_entry_attr qualifier i name typ kind)
        val rhs = HOLogic.mk_number @{typ nat} i
        val ((t, (s, thm)), lthy) = lthy
         |> Local_Theory.define ((b, Mixfix.NoSyn), ((Binding.suffix_name "_def" b, [attrib] @ @{attributes [locals]} ), rhs))
      in
        lthy |> Code.declare_default_eqns [(thm, true)]
 (*|>
          Local_Theory.declaration {pervasive=true, syntax=false} (fn _ =>
          Context.mapping
            (Code.declare_default_eqns_global [(thm, true)])
            I)*)
      end
    val lthy = lthy
      |> fold define (tag_list 0 decls)
      |> Bundle.bundle (Binding.make (suffix "_scope" fname, \<^here>),
           Attrib.internal_declaration \<^here> (Morphism.entity (fn _ => scope_map (K (qualifier))))) []
  in
    lthy |> Local_Theory.exit_global
  end

fun symmetric ctxt thm = fst (Thm.apply_attribute Calculation.symmetric thm (Context.Proof ctxt))

fun gen_unfolded {sym} qualifier ctxt thm =
 let
   val {scope, locals} = Data.get (Context.Proof ctxt)
   val qualifier = if null qualifier then scope else qualifier
   val defs0 = Locals.get_scope locals qualifier |> Locals.Keytab.dest 
       |> map (fn (_, (_, Entry {def,...})) => Thm.transfer' ctxt def)
   val defs = defs0 |> sym ? map (symmetric ctxt)
 in
   Simplifier.simplify (Simplifier.put_simpset HOL_basic_ss ctxt addsimps defs) thm
 end

val unfolded_with = gen_unfolded {sym = false}
val folded_with  = gen_unfolded {sym = true}

val unfolded = unfolded_with []
val folded  = folded_with []

fun check_scope ctxt (qualifier, pos) =
  let
    val {locals, scope} = Data.get (Context.Proof ctxt)
    val exploded = Long_Name.explode qualifier
    val extended = if length exploded = 1 then
                     take 1 scope @ exploded
                   else
                     exploded
  in
    if null extended orelse Locals.defined_scope locals extended then
      extended
    else
      error ("undefined scope: " ^ quote (Long_Name.implode extended) ^ Position.here pos)
  end
end

\<close>

setup \<open>
Attrib.setup \<^binding>\<open>fold_locals\<close>
  (Args.context -- Scan.lift (Scan.optional Parse.name_position ("", Position.none)) >>
  (fn (ctxt, (qualifier, pos)) =>
     let
        val exploded = CLocals.check_scope ctxt (qualifier, pos)
     in
       Thm.rule_attribute [] (CLocals.folded_with exploded o Context.proof_of)
     end))
  "fold local variables within optional scope qualifier" #>

Attrib.setup \<^binding>\<open>unfold_locals\<close>
  (Args.context -- Scan.lift (Scan.optional Parse.name_position ("", Position.none)) >>
  (fn (ctxt, (qualifier, pos)) =>
     let
        val exploded = CLocals.check_scope ctxt (qualifier, pos)
     in
       Thm.rule_attribute [] (CLocals.unfolded_with exploded o Context.proof_of)
     end))
  "unfold local variables within optional scope qualifier"
\<close>




nonterminal localsupdbinds and localsupdbind

syntax
  "_localsupdbind" :: "'a \<Rightarrow> 'a \<Rightarrow> localsupdbind"             ("(2_ :=\<^sub>\<L>/ _)")
  ""         :: "localsupdbind \<Rightarrow> localsupdbinds"             ("_")
  "_localsupdbinds":: "localsupdbind \<Rightarrow> localsupdbinds \<Rightarrow> localsupdbinds" ("_,/ _")


syntax
  "_statespace_lookup" :: "locals \<Rightarrow> 'name \<Rightarrow> 'c"  ("_ \<cdot> _" [60, 60] 60)
  "_statespace_locals_lookup" :: "('g, locals, 'e, 'x) state_scheme \<Rightarrow> 'name \<Rightarrow> 'c"
    ("_ \<cdot>\<^sub>\<L> _" [60, 60] 60)

  "_statespace_update" :: "locals \<Rightarrow> 'name \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> locals"
  "_statespace_updates" :: "locals \<Rightarrow> updbinds \<Rightarrow> locals"  ("_\<langle>_\<rangle>" [900, 0] 900)

  "_statespace_locals_update" :: "('g, locals, 'e, 'x) state_scheme \<Rightarrow> 'name \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('g, locals, 'e, 'x) state_scheme"
  "_statespace_locals_updates" :: "locals \<Rightarrow> localsupdbinds \<Rightarrow> locals"  ("_\<langle>_\<rangle>" [900, 0] 900)

  "_statespace_locals_map" ::
  "'name \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('g, locals, 'e, 'x) state_scheme \<Rightarrow> ('g, locals, 'e, 'x) state_scheme"
  ("(2_:=\<^sub>\<L>/ _)" [1000, 1000] 1000)

translations
  "_statespace_updates f (_updbinds b bs)" ==
    "_statespace_updates (_statespace_updates f b) bs"
  "s\<langle>x := y\<rangle>" == "_statespace_update s x y"


  "_statespace_locals_updates f (_localsupdbinds b bs)" ==
    "_statespace_locals_updates (_statespace_locals_updates f b) bs"
  "s\<langle>x :=\<^sub>\<L> y\<rangle>" == "_statespace_locals_update s x y"

parse_translation
\<open>
let
fun lookup_tr ctxt [s, x] =
  let
  in
    (case Term_Position.strip_positions x of
      Free (n,_) => CLocals.mk_lookup ctxt n $ s
    | _ => raise Match)
  end

fun locals_lookup_tr ctxt [s, x] =
  (case Term_Position.strip_positions x of
    Free (n,_) =>
      CLocals.mk_lookup ctxt n $ (Syntax.const \<^const_name>\<open>locals\<close> $ s)
  | _ => raise Match);

fun update_tr ctxt [s, x, v] =
  (case Term_Position.strip_positions x of
     Free (n, _) =>
       let
         val upd = CLocals.mk_update ctxt n
       in upd $ v $ s end
   | _ => raise Match);

fun locals_update_tr ctxt [s, x, v] =
  let
    val upd $ n $ v' $ _ = update_tr ctxt [s, x, v]

  in
    Syntax.const \<^const_name>\<open>locals_update\<close> $ (upd $ n $ v') $ s
  end


fun locals_map_tr ctxt [x, v] =
  let
     val upd $ s = locals_update_tr ctxt [Bound 0, x, v]
  in
    upd
  end

in

 [(\<^syntax_const>\<open>_statespace_lookup\<close>, lookup_tr),
  (\<^syntax_const>\<open>_statespace_locals_lookup\<close>, locals_lookup_tr),
  (\<^syntax_const>\<open>_statespace_update\<close>, update_tr),
  (\<^syntax_const>\<open>_statespace_locals_update\<close>, locals_update_tr),
  (\<^syntax_const>\<open>_statespace_locals_map\<close>, locals_map_tr)]
end
\<close>

print_translation \<open>
let

  fun dest_number (Const (\<^const_syntax>\<open>Groups.zero\<close>, _)) = 0
    | dest_number (Const (\<^const_syntax>\<open>Groups.one\<close>, _)) = 1
    | dest_number (Const (\<^const_syntax>\<open>numeral\<close>, _) $ n) = Numeral.dest_num_syntax n

  fun lookup_tr' ctxt (args as [n, s]) =
    let
      val n' = CLocals.print_tr ctxt n
    in
      case s of
        Const (\<^const_syntax>\<open>locals\<close>, _) $ s'' =>
          Syntax.const \<^syntax_const>\<open>_statespace_locals_lookup\<close> $ s'' $ n'
      | Const (\<^syntax_const>\<open>_antiquoteCur\<close>, _) $ Const ("get_actuals", _) =>
          Syntax.const \<^syntax_const>\<open>_antiquoteCur\<close> $ n'
      | _ =>  Syntax.const \<^syntax_const>\<open>_statespace_lookup\<close> $ s $ n'
   end

  fun update_tr' ctxt (args as [n, v, s]) =
    let
      val n' = CLocals.print_tr ctxt n
    in
      Syntax.const \<^syntax_const>\<open>_statespace_update\<close> $ s $ n' $ v
    end

  fun locals_update_tr' ctxt (args as [upd, s]) =
    let
      val _ $ s' $ n' $ v = update_tr' ctxt ((snd (strip_comb upd)) @ [s])
    in
      Syntax.const \<^syntax_const>\<open>_statespace_locals_update\<close> $ s' $ n' $ v
    end
  | locals_update_tr' ctxt (args as [upd]) =
    let
      val _ $ _ $ n' $ v = update_tr' ctxt ((snd (strip_comb upd)) @ [Bound 0])
    in
      Syntax.const \<^syntax_const>\<open>_statespace_locals_map\<close> $ n' $ v
    end

  fun assign_tr' ctxt (args as [(aq as Const ("_antiquoteCur", _)) $ (c as Const ("locals", _)), upd]) =
    let
      fun dest_K (Abs ("_", _, v)) = v
        | dest_K t = t

      val s = Bound 0
      val _ $ _ $ n $ v = locals_update_tr' ctxt [upd, s]
    in
      Syntax.const \<^syntax_const>\<open>_Assign\<close> $ (aq $ n) $ (dest_K v)
    end
    | assign_tr' ctxt t = raise Match


in
  [(\<^const_syntax>\<open>clookup\<close>, lookup_tr'),
   (\<^const_syntax>\<open>cupdate\<close>, update_tr'),
   (\<^const_syntax>\<open>locals_update\<close>, locals_update_tr'),
   (\<^syntax_const>\<open>_Assign\<close>, assign_tr')]

end
\<close>


end
