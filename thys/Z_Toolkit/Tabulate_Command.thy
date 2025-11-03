section \<open> Tabulating terms \<close>

theory Tabulate_Command
  imports Main
  keywords "tabulate" :: diag
begin

text \<open> The following little tool allows creation truth tables for predicates with a finite domain \<close>

definition "tabulate" :: "('a::enum \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list" where
"tabulate f = map (\<lambda> x. (x, f x)) (rev Enum.enum)"

ML \<open> 
structure Tabulate_Command =
struct

fun space_out cwidth str =
  str ^ Library.replicate_string ((cwidth - length (Symbol.explode str))) Symbol.space;

fun print_row cwidths row =
  String.concat (Library.separate " | " (map (fn (w, r) => space_out w r) (ListPair.zip (cwidths, row))));
 
(* Print an ASCII art table, given a heading and list of rows *)
fun print_table heads rows =
  let
  val cols = map (fn i => map (fn xs => nth xs i) (heads :: rows)) (0 upto length heads - 1)
  val cwidths = map (fn c => foldr1 Int.max (map length (map Symbol.explode c))) cols
  val llength = foldr1 (fn (c, x) => (c + 4) + x) cwidths + 2
  in Print_Mode.with_modes [] (fn () =>
              Pretty.paragraph ([Pretty.str (print_row cwidths heads)
                                , Pretty.fbrk
                                , Pretty.para ((Library.replicate_string llength "="))
                                , Pretty.fbrk]
                                @ Library.separate Pretty.fbrk (map (Pretty.str o print_row cwidths) rows))) () end;
  
fun tabulate_cmd raw_t state =
  let 
    open Syntax
    open Pretty
    open HOLogic
    val ctx = Toplevel.context_of state;
    (* Parse the term we'd like to tabulate *)
    val t = Syntax.read_term ctx raw_t;
    val ctx' = Proof_Context.augment t ctx;
    (* Extract the set of free variables from the term *)
    val xs = Term.add_frees t []
    val xp = foldr1 mk_prod (map Free (rev xs))
    val t' = HOLogic.tupled_lambda xp t
    (* Close the term, apply the tabulate function, and evaluate *)
    val ts' = dest_list (Value_Command.value ctx (check_term ctx (const @{const_name "tabulate"} $ t')));
    fun term_string t = XML.content_of (YXML.parse_body (symbolic_string_of (pretty_term ctx' t)));
    val heads = (map term_string (map Free (rev xs)) @ [term_string t])
    val rows = (map ((fn (x, y) => (map term_string (strip_tuple x) @ [term_string y])) o dest_prod) ts');
  in Pretty.writeln ((print_table heads rows)) end;

end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>tabulate\<close> "tabulate the values of a term"
    (Parse.term
      >> (fn t => Toplevel.keep (Tabulate_Command.tabulate_cmd t)))

\<close>

end