(*
  File:     sat_replay.ML
  Author:   Manuel Eberl, University of Innsbruck 

  This file implements replaying RUP proofs found by external SAT solvers. The proofs are
  expected to be in the GRAT format introduced by Peter Lammich:

    https://www21.in.tum.de/~lammich/grat/

  Note that clauses are stored in arrays and arrays in Poly/ML may have a relatively small
  number of maximum entries (e.g. 2^24, roughly 16 million, for x86_64_32). This leads to
  crashes for large SAT proofs.

  An easy fix would be to use arrays of arrays instead.
*)

signature REPLAY_RUP = sig

type rup_input =
  {
    n_vars : int,
    vars : cterm option array,
    clauses : (int list * thm) Array_Map.T,
    tracing : bool,
    ctxt : Proof.context
  }

val replay_rup : rup_input -> (unit -> int list option) -> thm

(* flag = true if file is XZ-compressed *)
val replay_rup_file : rup_input -> Path.T * bool -> thm

exception DIMACS of string
exception GRAT_PARSE of string
exception CLAUSE of string * int list
exception NO_SUCH_VAR of int
exception INTERNAL of string
exception RUP of string

end


structure Replay_RUP : REPLAY_RUP = struct

type clause_thm = thm

type lit_thm = thm

type rup_context =
  {vars : cterm option array,
   assignments : (bool * lit_thm) option array,
   clauses : (int list * clause_thm) Array_Map.T,
   tracing : bool,
   local_assignments : int list Unsynchronized.ref,
   local_mode : bool Unsynchronized.ref,
   n_unit_props : int Unsynchronized.ref,
   n_unit_prop_steps : int Unsynchronized.ref,
   ctxt : Proof.context}

fun trace (rupctxt : rup_context) s =
  if #tracing rupctxt then writeln (s ()) else ()

fun butlast xs = rev (drop 1 (rev xs))


exception DIMACS of string

fun read_dimacs itr =
  let
    fun is_comment c = c = #"c" orelse c = #"\n"
    val words = String.tokens (fn c => c = #" ")

    fun get_line () =
      case itr () of
        NONE => NONE
      | SOME l =>
          if String.size l = 0 orelse is_comment (String.sub (l, 0)) then
            get_line () (* empty line or comment *)
          else
            SOME l

    val l = get_line ()
    val _ = if is_none l then raise DIMACS "Missing header line" else ()

    val (n_vars, n_clauses) =
      case words (the l) of
        ["p", "cnf", x, y] => (
          case apply2 Int.fromString (x, y) of
            (SOME n_vars, SOME n_clauses) => (n_vars, n_clauses)
          | _ => raise DIMACS "Illegal header line")
      | _ => raise DIMACS "Illegal header line"

    val process_line =
      butlast o map (the o Int.fromString) o words
    fun go acc =
      case get_line () of
        NONE => rev acc
      | SOME l => go (process_line l :: acc)
    val result = go []
  in
    (n_vars, n_clauses, result)
  end

fun list_iterator ls =
  let
    val r = Unsynchronized.ref ls
    fun itr () =
      case ! r of
        [] => NONE
      | l :: ls =>
          let
            val _ = r := ls
          in
            SOME l
          end
  in
    itr
  end

fun file_iterator f = list_iterator (File.read_lines f)  

fun read_dimacs_file f = read_dimacs (file_iterator f)

exception GRAT_PARSE of string

fun read_grat itr =
  let
    val words = String.tokens (fn c => c = #" ")
    val l = itr ()
    val _ = if is_none l then raise GRAT_PARSE "Missing header line" else ()
    val _ =
      case words (the l) of
        ["GRATbt", _, _] => ()
      | _ => raise GRAT_PARSE "Illegal header line"

    val process_line =
      butlast o map (the o Int.fromString) o words
    fun go acc =
      case itr () of
        NONE => acc
      | SOME l => go (process_line l :: acc)
    val result = go []
  in
    result
  end

fun read_grat_file (gratfile, false) = read_grat (file_iterator gratfile)
  | read_grat_file (gratfile, true) =
      gratfile
      |> Bytes.read
      |> XZ.uncompress 
      |> Bytes.trim_split_lines
      |> list_iterator
      |> read_grat

fun disj_list [] = raise Empty
  | disj_list [ct] = ct
  | disj_list (ct :: cts) = Thm.apply (Thm.apply \<^cterm>\<open>HOL.disj\<close> ct) (disj_list cts)

fun build_clauses ctxt (n_vars, n_clauses) clauses =
  let
    val vars = Array.array (n_vars + 1, NONE)
    val clauses' = Array_Map.empty (n_clauses + 1)
    fun possibly_negate i v = if i > 0 then v else Thm.apply \<^cterm>\<open>HOL.Not\<close> v
    fun go i =
      case Array.sub (vars, abs i) of
        SOME v => possibly_negate i v
      | NONE =>
          let
            val s = "v" ^ Int.toString (abs i)
            val v = Thm.cterm_of ctxt (Free (s, @{typ "bool"})) 
            val _ = Array.update (vars, abs i, SOME v)
          in
             possibly_negate i v
          end
     fun build_clauses _ [] = ()
       | build_clauses i (c :: cs) =
           let
             val c = c |> take_prefix (fn x => x <> 0)
             val c' =
               c
               |> map go |> disj_list
               |> Thm.apply \<^cterm>\<open>HOL.Trueprop\<close> |> Skip_Proof.make_thm_cterm
             val _ = Array_Map.update (clauses', i, SOME (c, c'))
           in
             build_clauses (i + 1) cs
           end
    val _ = build_clauses 1 clauses
  in
    (vars, clauses')
  end

exception NO_SUCH_VAR of int

fun lookup_var (rupctxt : rup_context) v_id =
  (case Array.sub (#vars rupctxt, abs v_id) of
    SOME x => if v_id > 0 then x else Thm.apply \<^cterm>\<open>HOL.Not\<close> x
  | NONE => raise NO_SUCH_VAR v_id)
  handle Subscript => raise NO_SUCH_VAR v_id

fun lookup_var_assignment_thm (rupctxt : rup_context) v =
  (case Array.sub (#assignments rupctxt, abs v) of
    SOME x => SOME (snd x)
  | NONE => NONE)
  handle Subscript => raise NO_SUCH_VAR v

fun lookup_var_assignment (rupctxt : rup_context) v = (
  case Array.sub (#assignments rupctxt, abs v) of
    SOME x => SOME (if v < 0 then not (fst x) else fst x)
  | NONE => NONE)
  handle Subscript => raise NO_SUCH_VAR v

exception CLAUSE of (string * int list)

fun lookup_clause (rupctxt : rup_context) clause_id =
  (case Array_Map.sub (#clauses rupctxt, clause_id) of
    SOME cl => cl
  | NONE => raise CLAUSE ("No such clause", [clause_id]))
  handle Subscript => raise CLAUSE ("No such clause", [clause_id])

fun print_assignments ({assignments, ...} : rup_context) =
  let
    fun f (i, x, acc) =
      case x of
        NONE => acc
      | SOME (b, thm) => (i, b, thm) :: acc
    val assns = Array.foldri f [] assignments
  in
    @{make_string} assns
  end

fun build_clauses' ctxt n_vars clauses =
  let
    val arr = Array.array (n_vars + 1, NONE)
    fun possibly_negate i v = if i > 0 then v else Thm.apply \<^cterm>\<open>HOL.Not\<close> v
    fun go i ctxt =
      case Array.sub (arr, abs i) of
        SOME v => (possibly_negate i v, ctxt)
      | NONE =>
          let
            val s = "v" ^ Int.toString (abs i)
            val (s', ctxt') = yield_singleton Variable.add_fixes s ctxt
            val v = Thm.cterm_of ctxt (Free (s', @{typ "bool"})) 
            val _ = Array.update (arr, abs i, SOME v)
          in
             (possibly_negate i v, ctxt')
          end
     fun build_clause clause ctxt =
           fold_map go clause ctxt |> apfst disj_list
  in
    fold_map build_clause clauses ctxt
  end


fun is_pos_lit ct =
  case Thm.term_of ct of
    \<^const>\<open>HOL.Not\<close> $ _ => false
  | _ => true

val is_pos_lit_thm = Thm.cconcl_of #> Thm.dest_arg #> is_pos_lit

val [neg_clauseE_thm1, neg_clauseE_thm2, neg_clauseE_thm3] =
   @{lemma "\<not>(A \<or> B) \<Longrightarrow> \<not>A" and "\<not>(\<not>A \<or> B) \<Longrightarrow> A" and "\<not>(A \<or> B) \<Longrightarrow> \<not>B" by blast+}

val notnotD_thm = @{lemma "\<not>\<not>A \<Longrightarrow> A" by blast}

fun negate_clause rupctxt (clause, clause_cterm) =
  let
    fun mk_inst (x, y) = (((x, 0), \<^typ>\<open>bool\<close>), y)
    fun inst insts thm = Thm.instantiate (TVars.empty, Vars.make (map mk_inst insts)) thm
    fun lookup v = lookup_var rupctxt v

    val neg_clause_cterm =
      clause_cterm
      |> Thm.apply \<^cterm>\<open>HOL.Not\<close>
      |> Thm.apply \<^cterm>\<open>HOL.Trueprop\<close>
    val neg_clause_thm = Thm.assume neg_clause_cterm
    fun go [] _ _ _ = raise Empty
      | go [v] thm _ acc =
          let
            val thm' =
              if v > 0 then thm
            else
              notnotD_thm |> inst [("A", lookup (abs v))] |> Thm.elim_implies thm
          in
            rev (thm' :: acc)
          end
      | go (v :: vs) thm ct acc =
          let
            val lit_thm = if v > 0 then neg_clauseE_thm1 else neg_clauseE_thm2
            val ct' = Thm.dest_arg ct
            val lit_thm =
              lit_thm
              |> inst [("A", lookup (abs v)), ("B", ct')]
              |> Thm.elim_implies thm
            val thm' =
              neg_clauseE_thm3
              |> inst [("A", lookup v), ("B", ct')]
              |> Thm.elim_implies thm
          in
            go vs thm' ct' (lit_thm :: acc)
          end
  in
    (neg_clause_cterm, go clause neg_clause_thm clause_cterm [])
  end

local
  val [lit_eq_false_thm1, lit_eq_false_thm2] =
    @{lemma "P \<Longrightarrow> \<not>P \<equiv> False" "\<not>P \<Longrightarrow> P \<equiv> False" by (rule eq_reflection, blast)+}
  val [reduce_right_thm1, reduce_right_thm2] =
    @{lemma "P \<Longrightarrow> R \<equiv> False \<Longrightarrow> \<not>P \<or> R \<equiv> False"
            "\<not>P \<Longrightarrow> R \<equiv> False \<Longrightarrow> P \<or> R \<equiv> False" by (rule eq_reflection, blast)+}
  val [reduce_left_thm1, reduce_left_thm2] =
    @{lemma "P \<Longrightarrow> \<not>P \<or> Q \<Longrightarrow> Q" and "\<not>P \<Longrightarrow> P \<or> Q \<Longrightarrow> Q" by blast+}
  val [reduce_left_terminal_thm1, reduce_left_terminal_thm2] =
    @{lemma "P \<Longrightarrow> \<not>P \<Longrightarrow> False" and "\<not>P \<Longrightarrow> P \<Longrightarrow> False" by blast+}

  fun lit_eq_false_thm b = if b then lit_eq_false_thm1 else lit_eq_false_thm2
  fun reduce_right_thm b = if b then reduce_right_thm1 else reduce_right_thm2
  fun reduce_left_thm b = if b then reduce_left_thm1 else reduce_left_thm2
  fun reduce_left_terminal_thm b =
    if b then reduce_left_terminal_thm1 else reduce_left_terminal_thm2

  val join_thm =
    @{lemma "Q \<or> R \<Longrightarrow> R \<equiv> False \<Longrightarrow> Q" by blast}

in

fun unit_prop rupctxt clause_id =
  let
    val (clause, thm) = lookup_clause rupctxt clause_id
    val _ = trace rupctxt (fn _ => "Performing unit propagation on clause " ^
              Int.toString clause_id ^ " = " ^ @{make_string} clause)
    val _ = trace rupctxt (fn _ => "Current assignments: " ^ print_assignments rupctxt)
    val clause = map (fn v => (v, lookup_var_assignment rupctxt v)) clause
    fun is_assigned (_, NONE) = false
      | is_assigned (_, SOME false) = true
      | is_assigned (v, SOME true) =
          raise CLAUSE ("Blocked literal " ^ Int.toString v ^ " in clause", [clause_id])
    val clause' = map fst (filter_out is_assigned clause)
    val _ = trace rupctxt (fn _ => "Unit propagation resulted in clause " ^ @{make_string} clause')
    fun inst insts =
      Thm.instantiate (TVars.empty, Vars.make (map (apfst (fn v => ((v, 0), \<^typ>\<open>bool\<close>))) insts))

    val clause_info = clause |>
      map (fn (v, b) =>
             (v, b, lookup_var rupctxt (abs v), lookup_var_assignment_thm rupctxt (abs v)))
    
    fun reduce_right [(v, SOME b, v_cterm, SOME v_thm)] =
          lit_eq_false_thm ((v > 0) = b)
          |> inst [("P", v_cterm)]
          |> Thm.elim_implies v_thm
      | reduce_right ((v, SOME b, v_cterm, SOME v_thm) :: vs) =
          let
            val eq_thm = reduce_right vs
          in
            reduce_right_thm ((v > 0) = b)
            |> inst [("P", v_cterm), ("R", Thm.lhs_of eq_thm)]
            |> Thm.elim_implies v_thm
            |> Thm.elim_implies eq_thm
          end
      | reduce_right _ = raise Match

    fun reduce_left [(_, NONE, _, _)] thm = thm
      | reduce_left [(v, SOME b, v_cterm, SOME v_thm)] thm =
          reduce_left_terminal_thm ((v > 0) = b)
          |> inst [("P", v_cterm)]
          |> Thm.elim_implies v_thm
          |> Thm.elim_implies thm
      | reduce_left ((_, NONE, _, _) :: vs) thm =
          let
            val eq_thm = reduce_right vs
            val q = thm |> Thm.cconcl_of |> Thm.dest_arg |> Thm.dest_arg1
          in
            join_thm
            |> inst [("Q", q), ("R", Thm.lhs_of eq_thm)]
            |> Thm.elim_implies thm
            |> Thm.elim_implies eq_thm
          end
      | reduce_left ((v, SOME b, v_cterm, SOME v_thm) :: vs) thm =
          let
            val q = thm |> Thm.cconcl_of |> Thm.dest_arg |> Thm.dest_arg
          in
            reduce_left_thm ((v > 0) = b)
            |> inst [("P", v_cterm), ("Q", q)]
            |> Thm.elim_implies v_thm
            |> Thm.elim_implies thm
            |> reduce_left vs
          end
      | reduce_left _ _ = raise Match
    
    val thm' = reduce_left clause_info thm

    val _ = Unsynchronized.change (#n_unit_props rupctxt) (fn n => n + 1)
    val _ = Unsynchronized.change (#n_unit_prop_steps rupctxt) (fn n => n + length clause)

  in
    (clause', thm')
  end

end

exception INTERNAL of string

fun mk_assn rupctxt v lit_thm =
  let
    val t = Thm.concl_of lit_thm |> HOLogic.dest_Trueprop
(*    val v_term = Thm.term_of (lookup_var rupctxt v) *)
    val (pos, v_term') =
      case t of
        \<^const>\<open>HOL.Not\<close> $ t' => (false, t')
      | _ => (true, t)
(*    val _ =
       if v_term aconv v_term' then () else
         let
           val _ = trace rupctxt
               (fn _ => "Illegal assignment for variable " ^ Int.toString v ^
                          "\n" ^ @{make_string} lit_thm)
         in
           raise INTERNAL ("Illegal assignment for variable " ^ Int.toString v)
         end*)
  in
    (pos, lit_thm)
  end

fun add_assignment (rup_ctxt : rup_context) (v, lit_thm) =
  let
    val lit_thm = Thm.transfer' (#ctxt rup_ctxt) lit_thm
    val _ =
      Array.update (#assignments rup_ctxt, v, SOME (mk_assn rup_ctxt v lit_thm))
    val _ =
      if ! (#local_mode rup_ctxt) then
        Unsynchronized.change (#local_assignments rup_ctxt) (fn xs => v :: xs)
      else
        ()
  in
    ()
  end
    handle Subscript => raise NO_SUCH_VAR v

fun delete_assignment' tab v =
  Array.update (tab, v, NONE)
  handle Subscript => raise NO_SUCH_VAR v

fun add_assignments rupctxt assns =
  fold (fn assn => fn _ => add_assignment rupctxt assn) assns ()

fun delete_assignment ({assignments, ...} : rup_context) v =
  delete_assignment' assignments v

fun delete_assignments rupctxt assns =
  fold (fn v => fn _ => delete_assignment rupctxt v) assns ()

fun set_local_mode (rupctxt : rup_context) b =
  let
    val _ = delete_assignments rupctxt (! (#local_assignments rupctxt))
    val _ = #local_mode rupctxt := b
    val _ = #local_assignments rupctxt := []
  in
    ()
  end

fun get_assn_by_unit_prop rupctxt clause_id =
  let
    val (clause', clause_thm') = unit_prop rupctxt clause_id
  in
    case clause' of
      [v] => (abs v, clause_thm')
    | _ => raise CLAUSE ("Not a unit clause", [clause_id])
  end

fun mk_clause _ [] = raise Empty
  | mk_clause rupctxt (i :: is) =
      let
        fun possibly_negate i v = if i >= 0 then v else Thm.apply \<^cterm>\<open>HOL.Not\<close> v
        fun lookup i = possibly_negate i (lookup_var rupctxt (abs i))
      in
        if null is orelse hd is = 0 then
          lookup i
        else
          Thm.apply (Thm.apply \<^cterm>\<open>HOL.disj\<close> (lookup i)) (mk_clause rupctxt is)
      end


val ccontr_thm = @{lemma "(\<not>P \<Longrightarrow> False) \<Longrightarrow> P" by blast}

fun rup rupctxt clause up_ids confl_id =
  let
    val trace = trace rupctxt

    val _ = trace (fn _ => "Clause: " ^ @{make_string} clause)
    val _ = trace (fn _ => "Unit propagations: " ^ @{make_string} up_ids)
    val _ = trace (fn _ => "Conflict: " ^ Int.toString confl_id)

    val clause_cterm = mk_clause rupctxt clause
    val (neg_clause, neg_lits) = negate_clause rupctxt (clause, clause_cterm)

    val _ = set_local_mode rupctxt true
    val local_assns =
      (map abs clause ~~ neg_lits)
      |> filter_out (fn (v, _) => is_some (lookup_var_assignment rupctxt v))
    val _ = add_assignments rupctxt local_assns

    fun go [] =
          let
            val (confl_clause, confl_clause_thm) = unit_prop rupctxt confl_id
            val _ = set_local_mode rupctxt false
          in
            if null confl_clause then
              confl_clause_thm
            else
              let
                val _ = trace (fn _ => "Conflict clause " ^ Int.toString confl_id ^
                                  " simplifies to: " ^ @{make_string} confl_clause)
              in
                raise CLAUSE ("Not a conflict clause", [confl_id])
              end
          end
      | go (up_id :: up_ids) =
          let
            val _ =
               get_assn_by_unit_prop rupctxt up_id
               |> add_assignment rupctxt
          in
            go up_ids
          end

    val contradiction_thm' = Thm.implies_intr neg_clause (go up_ids)
    val ccontr =
      ccontr_thm
      |> Thm.instantiate (TVars.empty, Vars.make [((("P", 0), \<^typ>\<open>bool\<close>), clause_cterm)])
    val thm = Thm.implies_elim ccontr contradiction_thm'
  in
    thm
  end

fun add_clause ({clauses, ...} : rup_context) (id, clause) =
  Array_Map.update (clauses, id, SOME clause)
  handle Subscript => raise CLAUSE ("No such clause", [id])

fun rup' rupctxt (id, clause) up_ids confl_id =
  let
    val _ = add_clause rupctxt (id, (clause, rup rupctxt clause up_ids confl_id))
    val _ = trace rupctxt
       (fn _ => "Successful RUP deduction of clause " ^ Int.toString id ^ " = " ^ 
                @{make_string} clause)
  in
    ()
  end

fun delete_clause ({clauses, ...} : rup_context) id =
  Array_Map.update (clauses, id, NONE)
  handle Subscript => raise CLAUSE ("No such clause", [id])

fun delete_clauses rup_ctxt ids =
  fold (fn id => fn _ => delete_clause rup_ctxt id) ids ()

exception RUP of string

type rup_input =
  {
    n_vars : int,
    vars : cterm option array,
    clauses : (int list * clause_thm) Array_Map.T,
    tracing : bool,
    ctxt : Proof.context
  }

fun mk_rup_context ({n_vars, vars, clauses, tracing, ctxt} : rup_input) =
  let
    val assignments = Array.array (n_vars + 1, NONE)
  in
    {assignments = assignments,
     tracing = tracing,
     local_mode = Unsynchronized.ref false,
     vars = vars,
     local_assignments = Unsynchronized.ref [],
     clauses = Array_Map.clone clauses,
     n_unit_props = Unsynchronized.ref 0,
     n_unit_prop_steps = Unsynchronized.ref 0,
     ctxt = ctxt} : rup_context
  end

fun replay_rup rup_input prf_iterator =
  let
    fun trace' f = if #tracing rup_input then f () else ()
    fun trace s = trace' (fn _ => writeln (s ()))

    val rupctxt = mk_rup_context rup_input

    fun trace_step step s =
      trace (fn _ => "\nStep " ^ Int.toString step ^ ": " ^ s ())

    exception RUP_RESULT of thm

    fun process_line [] _ = ()
      | process_line (1 :: ups) step =
          let
            val ups' = take_prefix (fn x => x <> 0) ups
            val _ = trace_step step (fn _ => "Unit Propagation of " ^ @{make_string} ups')
            val _ = trace (fn _ => "Current assignments: " ^ print_assignments rupctxt)
            fun go' id =
              let
                val (v, thm) = get_assn_by_unit_prop rupctxt id
                val _ = trace (fn _ => "Successfully deduced new assignment v = " ^
                                 @{make_string} (is_pos_lit_thm thm))
              in
                add_assignment rupctxt (v, thm)
              end
  
            val _ = map go' ups'
          in
            ()
          end
      | process_line (2 :: dels) step =
          let
            val dels' = take_prefix (fn x => x <> 0) dels
            val _ = trace_step step (fn _ => "Deletion of " ^ @{make_string} dels')
            val _ = delete_clauses rupctxt dels'
          in
            ()
          end
      | process_line (3 :: rupline) step =
          let
            fun err () = raise RUP "Malformed RUP line"
            val (new_id, rupline) = if null rupline then err () else (hd rupline, tl rupline)
            val _ = if null rupline then err () else ()
            val clause = take_prefix (fn x => x <> 0) rupline
            val rupline = drop_prefix (fn x => x <> 0) rupline
            val rupline = if null rupline then err () else tl rupline
            val up_ids = take_prefix (fn x => x <> 0) rupline
            val rupline = drop_prefix (fn x => x <> 0) rupline
            val rupline = if null rupline then err () else tl rupline
            val confl_id = hd rupline
            val _ = trace_step step (fn _ => "RUP proof of new clause " ^ Int.toString new_id)
            val _ = trace (fn _ => "Current assignments: " ^ print_assignments rupctxt)

            val _ = rup' rupctxt (new_id, clause) up_ids confl_id
          in
            ()
          end
       | process_line (4 :: _) _ =
           raise RUP "RAT proofs are not supported."
       | process_line (5 :: confl) step =
            let
              val _ = if null confl then raise RUP "Malformed conflict line" else ()
              val confl_id = hd confl
              val _ = trace_step step (fn _ => "Conflict clause " ^ Int.toString confl_id)
              val (clause', thm) = unit_prop rupctxt confl_id
              val _ = trace (fn _ => "Unit propagation resulted in theorem " ^ @{make_string} clause')
            in
              if null clause' then
                raise RUP_RESULT thm
              else
                raise CLAUSE ("Not a conflict clause", [confl_id])
            end
       | process_line (6 :: _) _ = ()
       | process_line _ _ = raise RUP "Unknown proof line type"

     fun go step : thm =
       case prf_iterator () of
         NONE => raise RUP "GRAT proof ended unexpectedly"
       | SOME rupline => 
           let 
             val _ = process_line rupline step 
           in 
             go (step + 1)
           end

     val result = go 1 handle RUP_RESULT thm => thm
  in
    result
  end

fun replay_rup_file rup_input grat_file =
  let
    val ls = Unsynchronized.ref (read_grat_file grat_file)
    fun itr () =
      case ! ls of
        [] => NONE
      | (l :: ls') => let val _ = ls := ls' in SOME l end
    val res = replay_rup rup_input itr
  in
    res
  end

end
