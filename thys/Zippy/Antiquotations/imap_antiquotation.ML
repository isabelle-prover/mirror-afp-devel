(*  Title:      Zippy/imap_antiquotation.ML
    Author:     Kevin Kappelmann

Antiquotation for lists of arguments.
*)
@{parse_entries (sig) PARSE_IMAP_ANTIQUOTATION_ARGS [sep, encl, encl_inner, start, stop, f]}
@{parse_entries (sig) PARSE_IMAP_ANTIQUOTATION_CONFIG_ARGS [sep, encl, encl_inner, start, stop]}

signature IMAP_ANTIQUOTATION_ARGS =
sig
  structure PA : PARSE_IMAP_ANTIQUOTATION_ARGS
  structure PCA : PARSE_IMAP_ANTIQUOTATION_CONFIG_ARGS
  val PCA_entries_from_PA_entries : ('a, 'b, 'c, 'd, 'e, 'f) PA.entries ->
    ('a, 'b, 'c, 'd, 'e) PCA.entries
  val PA_entries_from_PCA_entries : ('a, 'b, 'c, 'd, 'e) PCA.entries -> 'f ->
    ('a, 'b, 'c, 'd, 'e, 'f) PA.entries

  type args = (string, string * string, string * string, int, int, string * Input.source) PA.entries
  type config_args = (string, string * string, string * string, int, int) PCA.entries
  val mk_code : args -> Proof.context -> string * Proof.context
  val arg_parsers : (string parser, (string * string) parser, (string * string) parser, int context_parser,
    int context_parser, (string * Input.source) parser) PA.entries
end

structure IMap_Antiquotation_Args : IMAP_ANTIQUOTATION_ARGS =
struct

structure PU = Parse_Util

@{parse_entries (struct) PA [sep, encl, encl_inner, start, stop, f]}
@{parse_entries (struct) PCA [sep, encl, encl_inner, start, stop]}
fun PCA_entries_from_PA_entries {sep, encl, encl_inner, start, stop,...} =
  {sep = sep, encl = encl, encl_inner = encl_inner, start = start, stop = stop}
fun PA_entries_from_PCA_entries {sep, encl, encl_inner, start, stop} f =
  {sep = sep, encl = encl, encl_inner = encl_inner, start = start, stop = stop, f = SOME f}

type args = (string, string * string, string * string, int, int, string * Input.source) PA.entries
type config_args = (string, string * string, string * string, int, int) PCA.entries

fun map_input_text f input = Input.source (Input.is_delimited input) (f (Input.text_of input))
  (Input.range_of input)

fun mk_code entries ctxt =
  let
    val (templatei, f) = PA.get_f entries
    fun replace_run i ctxt = f
      |> map_input_text (General_Util.replace templatei (string_of_int i))
      |> (fn f => ML_Context.read_antiquotes f ctxt)
    fun run_decl ctxt decl = decl ctxt
    val string_of_tokens = map ML_Lex.content_of #> implode
    fun prepare_decl ctxt = run_decl ctxt #> snd #> string_of_tokens
      #> uncurry enclose (PA.get_encl_inner entries)
  in
    (PA.get_start entries upto PA.get_stop entries)
    |> (fn is => fold_map replace_run is ctxt)
    |> (fn (decls, ctxt) => map (prepare_decl ctxt) decls |> rpair ctxt)
    |>> separate (PA.get_sep entries)
    |>> implode
    |>> uncurry enclose (PA.get_encl entries)
  end

val encl_parser = Parse.embedded -- Parse.embedded
fun pos_n_parser fail_neg = PU.filter (curry (op <=) 0) (PU.fail fail_neg)
  (Parse_Util.ML_int (K "number most not be empty"))

val fun_parser = Parse.embedded --| Parse.$$$ "=>" -- Parse.embedded_input

val arg_parsers = {
  sep = SOME Parse.embedded,
  encl = SOME encl_parser,
  encl_inner = SOME encl_parser,
  start = SOME (pos_n_parser (K "start index must be non-negative")),
  stop = SOME (pos_n_parser (K "end index must be non-negative")),
  f = SOME fun_parser
}

end

signature IMAP_ANTIQUOTATION =
sig
  structure Data : GENERIC_DATA
  where type T = IMap_Antiquotation_Args.config_args

  val get_config_args : Context.generic -> IMap_Antiquotation_Args.config_args
  val map_config_args :
    (IMap_Antiquotation_Args.config_args -> IMap_Antiquotation_Args.config_args) ->
    Context.generic -> Context.generic

  val get_sep : Context.generic -> string
  val map_sep : (string -> string) -> Context.generic -> Context.generic

  val get_encl : Context.generic -> string * string
  val map_encl : (string * string -> string * string) -> Context.generic -> Context.generic

  val get_encl_inner : Context.generic -> string * string
  val map_encl_inner : (string * string -> string * string) -> Context.generic -> Context.generic

  val get_start : Context.generic -> int
  val map_start : (int -> int) -> Context.generic -> Context.generic

  val get_stop : Context.generic -> int
  val map_stop : (int -> int) -> Context.generic -> Context.generic

  val mk_code_config_args : IMap_Antiquotation_Args.config_args -> string * Input.source ->
    Proof.context -> string * Proof.context
  val mk_code : string * Input.source -> Proof.context -> string * Proof.context

  val binding : binding

  val parse_config_args : (string, string * string, string * string, int, int)
    IMap_Antiquotation_Args.PCA.entries context_parser
  val attribute : IMap_Antiquotation_Args.config_args -> attribute
  val parse_attribute : attribute context_parser
  val setup_attribute : string option -> local_theory -> local_theory

  val parse_antiquotation_args : (Proof.context -> string * Proof.context) context_parser
  val setup_antiquotation : theory -> theory
end

functor IMap_Antiquotation(
    structure FI : FUNCTOR_INSTANCE_BASE
    val init_args : IMap_Antiquotation_Args.config_args
  ) : IMAP_ANTIQUOTATION =
struct

structure IAA = IMap_Antiquotation_Args
structure PA = IAA.PA
structure PCA = IAA.PCA
structure FI = Functor_Instance(FI)

structure Data = Generic_Data(
  type T = IAA.config_args
  val empty = init_args
  val merge = fst
)

val get_config_args = Data.get
val map_config_args = Data.map

val get_sep = PCA.get_sep o get_config_args
val map_sep = map_config_args o PCA.map_sep

val get_encl = PCA.get_encl o get_config_args
val map_encl = map_config_args o PCA.map_encl

val get_encl_inner = PCA.get_encl_inner o get_config_args
val map_encl_inner = map_config_args o PCA.map_encl_inner

val get_start = PCA.get_start o get_config_args
val map_start = map_config_args o PCA.map_start

val get_stop = PCA.get_stop o get_config_args
val map_stop = map_config_args o PCA.map_stop

fun mk_code_config_args entries f = IAA.PA_entries_from_PCA_entries entries f |> IAA.mk_code
fun mk_code f ctxt = mk_code_config_args (get_config_args (Context.Proof ctxt)) f ctxt

val binding = Binding.make (FI.prefix_id "imap", FI.pos)

val parse_config_args =
  let
    val parsers = IAA.arg_parsers
    val parse_value = PCA.parse_entry (Scan.lift (PA.get_sep parsers))
      (Scan.lift (PA.get_encl parsers)) (Scan.lift (PA.get_encl_inner parsers))
      (PA.get_start parsers) (PA.get_stop parsers)
    val parse_entry = Parse_Key_Value.parse_entry' (Scan.lift PCA.parse_key)
      (K (Scan.lift (Parse.$$$ ":"))) parse_value
    val default_entries = PCA.empty_entries ()
  in PCA.parse_entries_required' Scan.repeat1 true [] parse_entry default_entries end

fun attribute entries = Thm.declaration_attribute (K (map_config_args (PCA.merge_entries entries)))

val parse_attribute = parse_config_args >> attribute

val setup_attribute = Attrib.local_setup binding (Parse.!!!! parse_attribute) o
  the_default ("configure imap antiquotation data " ^ enclose "(" ")" FI.long_name)

val parse_antiquotation_args =
  Scan.lift (PA.get_f IAA.arg_parsers)
  -- (parse_config_args |> Parse.!!!! |> Parse_Util.option')
  >> (fn (f, opt_entries) => fn ctxt =>
    let val entries = get_config_args (Context.Proof ctxt)
      |> PCA.merge_entries (\<^if_none>\<open>PCA.empty_entries ()\<close> opt_entries)
    in mk_code_config_args entries f ctxt end)

fun read_antiquotation input ctxt =
  let
    val keywords = Thy_Header.get_keywords' ctxt
    val (f, ctxt) = input
      |> Parse.read_embedded ctxt keywords
        (pair (Context.Proof ctxt) #> parse_antiquotation_args #> apsnd snd)
      |> (fn f => f ctxt)
  in ML_Context.expand_antiquotes (ML_Code_Util.read f) ctxt end

val setup_antiquotation = ML_Context.add_antiquotation_embedded binding (K read_antiquotation)

end