open Complementation
open Automaton
open List

fun eq x y = (x = y)

fun write_automaton path automaton =
let
	fun t (p, (a, q)) = Int.toString (integer_of_nat p) ^ " " ^ a ^ " " ^ Int.toString (integer_of_nat q) ^ "\n"
	val out = TextIO.openOut path
	fun write [] = () | write (x :: xs) = (TextIO.output (out, t x); write xs)
	val _ = write (transitionei automaton)
	val _ = TextIO.closeOut out
in
	()
end

(* TODO: output number of explored states in emptiness check *)

val parameters = CommandLine.arguments ()
val _ = case hd parameters of
	"help" => print "Available Commands: help | complement <automaton> | equivalence <automaton1> <automaton2>\n" |
	"complement" => write_automaton (nth (parameters,  1)) (complement_impl (nbae_nba_impl eq eq automaton1)) |
	"equivalence" => print (Bool.toString (language_equal_impl {equal = eq} (nbae_nba_impl eq eq automaton1) (nbae_nba_impl eq eq automaton2)) ^ "\n")
