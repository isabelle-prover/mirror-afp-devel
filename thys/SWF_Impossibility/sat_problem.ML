
signature SAT_PROBLEM =
sig

type T = {
  n_vars : int,
  vars : cterm option array,
  n_clauses : int,
  clauses : (int list * thm) Array_Map.T
}

val mk_dimacs : T -> Bytes.T
val write_dimacs : T -> Path.T -> unit

end


structure SAT_Problem : SAT_PROBLEM =
struct

type T = {
  n_vars : int,
  vars : cterm option array,
  n_clauses : int,
  clauses : (int list * thm) Array_Map.T
}

fun dimacs_gen st put {n_vars, n_clauses, clauses, ...} =
  let
    fun write_clause st (cs, _) =
      put st (implode_space (map signed_string_of_int cs) ^ " 0")
    val st = put st ("p cnf " ^ string_of_int n_vars ^ " " ^ string_of_int n_clauses ^ "")
    fun write_clauses st i = if i > n_clauses then st else
      let
        val st =
          case Array_Map.sub (clauses, i) of
            SOME c => write_clause st c
          | NONE => raise Match
      in
        write_clauses st (i + 1)
      end
    val st = write_clauses st 1
  in
    st
  end

fun write_dimacs sat dimacs_file =
  dimacs_file |> File_Stream.open_output (fn out =>
    dimacs_gen () (fn _ => fn s => File_Stream.output out (s ^ "\n")) sat)

fun mk_dimacs sat =
  dimacs_gen Bytes.empty (fn buf => fn s => Bytes.add (s ^ "\n") buf) sat

end