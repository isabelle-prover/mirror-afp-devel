fun inLine istr = case TextIO.inputLine istr of
                    NONE => ""
                  | SOME s => s

fun lex fname = let
    val istream = TextIO.openIn fname
    val lexer = Mlex.makeLexer (fn _ => inLine istream)
in
    lexer ()
end


structure Main = struct

open OS.Process


(* takes a file name on the command-line, and attempts to parse it *)
fun die s = (print s; print "\n"; exit failure)
val execname = CommandLine.name()

fun usage() = die ("Usage: "^execname^" filename1 filename2 ...")

fun do_lex (fname, _) = lex fname

fun handle_args args =
    case args of
      [] => usage()
    | files => (List.foldl do_lex 0 files; exit success)

val _ = handle_args (CommandLine.arguments())

end;


(* Local variables: *)
(* mode: sml *)
(* End: *)
