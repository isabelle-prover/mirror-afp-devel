(*  Title:      ML_Utils/parse_key_value.ML
    Author:     Kevin Kappelmann

Parsing of key-value pairs.
*)
signature PARSE_KEY_VALUE =
sig
  type ('k, 'v) entry = ('k * 'v)
  type ('k, 'v) entries = ('k, 'v) entry list

  (*takes key parser, delimiter parser, value parser*)
  val parse_entry : 'k parser -> ('k -> 'd parser) -> ('k -> 'v parser) -> (('k, 'v) entry) parser
  val parse_entry' : 'k context_parser -> ('k -> 'd context_parser) -> ('k -> 'v context_parser) ->
    (('k, 'v) entry) context_parser

  val pretty_keys : ('k -> string) -> 'k list -> Pretty.T
  val parse_key : string list -> (string -> 'k option) -> 'k parser

  val has_required_keys : ('k * ('k, 'v) entry -> bool) -> 'k list -> ('k, 'v) entries -> bool

  val parse_entries_required : ('k * 'k -> bool) -> ('k -> string) -> bool -> 'k list ->
    (('k, 'v) entries) parser -> (('k, 'v) entries) parser
  val parse_entries_required' : ('k * 'k -> bool) -> ('k -> string) -> bool -> 'k list ->
    (('k, 'v) entries) context_parser -> (('k, 'v) entries) context_parser
end

structure Parse_Key_Value : PARSE_KEY_VALUE =
struct

structure Util = Parse_Util

type ('k, 'v) entry = ('k * 'v)
type ('k, 'v) entries = ('k, 'v) entry list

fun gen_parse_entry cut parse_key parse_delim parse_value = parse_key
  :-- (fn n => parse_delim n
  |-- cut (parse_value n))
fun parse_entry parse_key = gen_parse_entry Parse.!!! parse_key
fun parse_entry' parse_key = gen_parse_entry Parse.!!!! parse_key

fun pretty_keys key_to_string = map (Pretty.str o key_to_string) #> Pretty.commas #> Pretty.block

fun parse_key names key_from_string =
  let
    val pretty_keys = pretty_keys I names |> Pretty.string_of
    val parse_key = Parse.token (Parse.short_ident || Parse.long_ident)
      :|-- (fn tok => case key_from_string (Token.content_of tok) of
          NONE => Scan.fail ()
        | SOME key =>
          let val _ = Token.assign (SOME (Token.Literal (false, Markup.quasi_keyword))) tok
          in Scan.succeed key end)
  in Parse.group (K pretty_keys) parse_key end

fun eq_key_entry eq_key (rn, (xn, _)) = eq_key (rn, xn)

fun has_required_keys eq_key_entry rks ks = subset eq_key_entry (rks, ks)

fun gen_parse_entries_required filter_parser eq_key key_to_string check_dups ks parse_entries =
  let
    val eq_key_entry = eq_key_entry eq_key
    fun failure_required es = Pretty.fbreaks [
        Pretty.block [
          Pretty.str "Missing keys: ",
          pretty_keys key_to_string (subtract (eq_key_entry o swap) es ks)
        ],
        Pretty.block [
          Pretty.str "Required keys: ",
          pretty_keys key_to_string ks
        ]
      ] |> Pretty.block |> Pretty.string_of
    fun failure_distinct es _ = Pretty.block [
        Pretty.str "All keys must be distinct. Duplicates: ",
        duplicates eq_key (map fst es) |> pretty_keys key_to_string
      ] |> Pretty.string_of
  in
    filter_parser
      (has_required_keys eq_key_entry ks) (Util.fail failure_required) parse_entries
    |> check_dups ? Util.distinct_list (eq_key o apply2 fst) failure_distinct
  end

fun parse_entries_required eq_key = gen_parse_entries_required Util.filter_cut eq_key
fun parse_entries_required' eq_key = gen_parse_entries_required Util.filter_cut' eq_key

end