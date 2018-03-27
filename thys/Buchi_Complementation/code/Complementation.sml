open Complementation

fun nth l 0 = hd l
  | nth l n = nth (tl l) (n - 1)

fun getParameterString n default =
	if length (CommandLine.arguments ()) <= n
	then default
	else nth (CommandLine.arguments ()) n

fun getParameterInteger n default =
	if length (CommandLine.arguments ()) <= n
	then default
	else
		case Int.fromString (nth (CommandLine.arguments ()) n)
		of SOME k => k
		 | NONE => default

fun naturalNumbers 0 = []
  | naturalNumbers n = naturalNumbers (n - 1) @ [n - 1]

fun run_test n =
(
	print (Int.toString (integer_of_nat (test n)) ^ "\n");
	print (Statistics.pretty_stats (Statistics.get_active_stats ()) ^ "\n")
)

val _ = run_test (nat_of_integer (getParameterInteger 0 4))
