(*  Title:      ML_Utils/util.ML
    Author:     Kevin Kappelmann

Parsing utilities.
*)
signature PARSE_UTIL =
sig
  (*cut for context parsers*)
  val !!!+ : 'a context_parser -> 'a context_parser

  val enum1' : string -> 'a context_parser -> 'a list context_parser
  val enum' : string -> 'a context_parser -> 'a list context_parser
  val and_list1' : 'a context_parser -> 'a list context_parser
  val and_list' : 'a context_parser -> 'a list context_parser

  (*indexed state monad (generalising parsers and context parsers)*)
  type ('i, 'j, 'a) istate = 'i -> 'a * 'j

  (*"if_ahead p1 f p2" applies f to result of p1 if p1 is successful; otherwise runs p2*)
  val if_ahead : ('a, 'b, 'c) istate -> ('c -> 'a -> 'd) -> ('a, 'a, 'd) istate ->
    ('a, 'a, 'd) istate

  (*if_ahead applied to end-of-file parser*)
  val if_eof : (string -> Token.T list -> 'a) -> 'a parser -> 'a parser
  val if_eof' : (string -> Context.generic * Token.T list -> 'a) -> 'a context_parser ->
    'a context_parser

  val option : 'a parser -> ('a option) parser
  val option' : 'a context_parser -> ('a option) context_parser
  val optional : 'a parser -> 'a -> 'a parser
  val optional' : 'a context_parser -> 'a -> 'a context_parser

  val position : 'a parser -> ('a * Position.T) parser
  val position' : 'a context_parser -> ('a * Position.T) context_parser

  val fail : ('a -> string) -> 'a -> 'b
  (*scanner raising Scan.ABORT with given error message*)
  val abort : (Token.T list -> string) -> 'a parser
  val abort' : (Context.generic * Token.T list -> string) -> 'a context_parser

  (*"filter f err p" runs parser p to obtain result x and returns x if "f x" holds and "err x" otherwise*)
  val filter : ('a -> bool) -> ('a -> ('b, 'b, 'a) istate) -> ('c, 'b, 'a) istate ->
    ('c, 'b, 'a) istate
  (*filter with cuts in case of failure*)
  val filter_cut : ('a -> bool) -> ('a -> Token.T list -> string) -> 'a parser -> 'a parser
  val filter_cut' : ('a -> bool) -> ('a -> Context.generic * Token.T list -> string) ->
    'a context_parser -> 'a context_parser

  val nonempty_list : ('b -> string) -> ('a, 'b, 'c list) istate -> ('a, 'b, 'c list) istate
  val distinct_list : ('a * 'a -> bool) -> ('a list -> 'c -> string) -> ('b, 'c, 'a list) istate ->
    ('b, 'c, 'a list) istate

  val nonempty_name : (Token.T list -> string) -> string parser

  val code : ML_Code_Util.code parser
  val nonempty_code : (Token.T list -> string) -> ML_Code_Util.code parser

  val bool : bool parser
  val eq : string parser
  val parenths : 'a parser -> 'a parser
  val parenths' : 'a context_parser -> 'a context_parser

  val thm : thm context_parser
  val multi_thm : (thm list) context_parser
  val thms : (thm list) context_parser
  val nonempty_thms : (Context.generic * Token.T list -> string) -> (thm list) context_parser

  (*the following structure may be ignored; it is needed for below ML_int parser*)
  structure Internal_Int_Data : GENERIC_DATA
  val ML_int : (Token.T list -> string) -> int context_parser
end

structure Parse_Util : PARSE_UTIL =
struct

(*FIXME: move to Isabelle kernel?*)
fun get_tokens_pos [] = " (end-of-input)"
  | get_tokens_pos (tok :: _) = Position.here (Token.pos_of tok);

fun cut get_pos kind scan =
  let
    fun err (x, NONE) = (fn () => kind ^ get_pos x)
      | err (x, SOME msg) =
          (fn () =>
            let val s = msg () in
              if String.isPrefix kind s then s
              else kind ^ get_pos x ^ ": " ^ s
            end);
  in Scan.!! err scan end;

fun !!!+ scan = cut (get_tokens_pos o snd) "Outer syntax error" scan

fun enum1' sep scan = scan ::: Scan.repeat (Scan.lift (Parse.$$$ sep) |-- !!!+ scan);
fun enum' sep scan = enum1' sep scan || Scan.succeed [];
fun and_list1' scan = enum1' "and" scan;
fun and_list' scan = enum' "and" scan;

type ('i, 'j, 'a) istate = 'i -> 'a * 'j

fun if_ahead ahead f scan =
  (Scan.ahead ahead :|-- (fn st => fn xs => (f st xs, xs))) || scan

fun if_eof scan = if_ahead Parse.eof scan
fun if_eof' scan = if_ahead (Scan.lift Parse.eof) scan

fun option scan = if_eof (K o K NONE) (Scan.option scan)
fun option' scan = if_eof' (K o K NONE) (Scan.option scan)
fun optional scan default = option scan >> the_default default
fun optional' scan default = option' scan >> the_default default

fun gen_position not_eof scan =
  (Scan.optional (Scan.ahead not_eof >> Token.pos_of) Position.none
  >> (snd o Position.default))
  -- scan
  >> swap

fun position scan = gen_position Parse.not_eof scan
fun position' scan = gen_position (Scan.lift Parse.not_eof) scan

fun fail msg_of = Scan.fail_with (fn x => fn _ => msg_of x)
fun gen_abort cut msg_of = fail msg_of |> cut

fun abort msg_of = gen_abort Parse.!!! msg_of
fun abort' msg_of = gen_abort !!!+ msg_of

fun filter p err scan = scan :|-- (fn x => if p x then pair x else err x)
fun gen_filter_cut abort p msg_of = filter p (abort o msg_of)
fun filter_cut p = gen_filter_cut abort p
fun filter_cut' p = gen_filter_cut abort' p

fun nonempty_list msg_of = filter (not o null) (K (fail msg_of))
fun distinct_list eq msg_of = filter (not o has_duplicates eq) (fail o msg_of)
fun nonempty_name msg_of = filter (curry (op <>) "") (K (fail msg_of)) Args.name

val code = if_eof (K o K []) ML_Code_Util.parse_code
fun nonempty_code msg_of = nonempty_list msg_of code

val bool = Scan.recover (Args.name >> Value.parse_bool)
  (fail (K "expected \"true\" or \"false\""))

val eq = Parse.$$$ "\<equiv>" || Parse.$$$ "=" || fail (K "expected \"=\" or \"\<equiv>\"")

fun parenths scan = Parse.$$$ "(" |-- scan --| Parse.$$$ ")"
fun parenths' scan = (Scan.lift (Parse.$$$ "(")) |-- scan --| (Scan.lift (Parse.$$$ ")"))

(*for better error messages than Attrib.thm and friends*)
fun thm x = Attrib.thm x handle ERROR m => fail (K m) ()
fun multi_thm x = Attrib.multi_thm x handle ERROR m => fail (K m) ()
val thms = Scan.repeats multi_thm
fun nonempty_thms msg_of = nonempty_list msg_of thms

structure Internal_Int_Data = Generic_Data( type T = int val empty = 0 val merge = fst)

fun ML_int msg_of =
  let fun int_from_code ((code, ctxt), pos) =
    let val put_int_code = ML_Code_Util.read "Parse_Util.Internal_Int_Data.put"
      @ ML_Code_Util.atomic code
    in
      Context.Proof ctxt
      |> ML_Attribute_Util.attribute_map_context (ML_Attribute.run_map_context (put_int_code, pos))
      |> Internal_Int_Data.get
    end
  in
    Scan.lift Parse.int
    || ((Scan.lift (nonempty_code msg_of) -- Args.context |> position') >> int_from_code)
  end
end
