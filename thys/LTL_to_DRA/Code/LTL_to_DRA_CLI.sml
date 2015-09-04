(* Initialise Parser *)
structure LtlParser = Ltl(PropLtl)

(* Printers *)
fun println x = print (x ^ "\n")
fun printlnErr x = (TextIO.output (TextIO.stdErr, x ^ "\n"); TextIO.flushOut TextIO.stdErr)

(* Main *)
fun usage () = println ("Usage:" ^ CommandLine.name () ^ " ltlformula");

fun main () =
  let 
    val e = fn () => OS.Process.exit (OS.Process.failure)
    val u = fn () => (usage(); e())
    val default_ltl = "F G a"
    val ltl = case CommandLine.arguments () of [] => default_ltl | (x::xs) => x
    val phi = LtlParser.compile_from_string ltl handle LtlParser.LtlError msg => (printlnErr ("LTL Error: " ^ msg); e())
    val res = LTL_to_DRA_Translator.ltlc_to_rabin phi
  in 
    println (PolyML.makestring res)
  end