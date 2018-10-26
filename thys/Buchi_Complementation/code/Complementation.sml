open Complementation
open Automaton

val _ =
(
	print (Int.toString (integer_of_nat (test automaton)) ^ "\n");
	print (Statistics.pretty_stats (Statistics.get_active_stats ()) ^ "\n")
)
