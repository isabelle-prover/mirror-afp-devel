(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

val foldl = List.foldl 
val foldr = List.foldr 



fun group_by eq xs =
  let
     val pivots = distinct eq xs
  in
    map (fn pivot => filter (fn x => eq (pivot, x)) xs) pivots
  end

fun representative_for eq xs = group_by eq xs |> map hd

fun safe_unsuffix sfx str = the_default str (try (unsuffix sfx) str)

structure Symtab = struct
open Symtab
fun fold_map f t s = 
  let
    val elems = dest t
    fun f' (elem as (key, _)) s = let val (res, s') = f elem s in ((key, res), s') end
    val (elems', s') = Basics.fold_map f' elems s 
  in (make elems', s') end
end

fun strip_comb_depth_of_term tm =
  let 
    fun depth (t $ u) is_head n = let val n' = if is_head then n else n + 1 
                                  in Int.max (depth t true n', depth u false n') end
      | depth (Abs (_, _ , t)) is_head n = depth t false (n + 1)
      | depth _ is_head n = n + 1
  in depth tm false 0 end

fun comb_depth_of_term tm =
  let 
    fun depth (t $ u) n = let val n' = n + 1 
                          in Int.max (depth t n', depth u n') end
      | depth (Abs (_, _ , t)) n = depth t (n + 1)
      | depth _ n = n + 1
  in depth tm 0 end

fun with_goal_depth tac = SUBGOAL (fn (t, i) => 
  tac (strip_comb_depth_of_term t) i)

fun strip_comb_depth_of_term_destructive t =
  case t of
    Abs (_, _, t) => 1 + strip_comb_depth_of_term_destructive t 
  | (_$_) =>
    let
      val (f, args) = strip_comb t
    in map strip_comb_depth_of_term_destructive (f:: args) 
      |> List.foldl Int.max 0 
      |> (fn i => i + 1) 
    end
 | _ => 1

local
  val t1 = @{term "f (b y) (c x)"}
  val t2 = @{term "f x"}
  val t3 = @{term "f (\<lambda>x. k x) y"}
  val t4 = @{term "\<lambda>x. f x"}
  val t5 = @{term "(\<lambda>y g. f (h (g y)))"}
  val t6 = @{term "x"}

  val tests = [t1, t2, t3, t4, t5, t6, t5$t6]


  fun comp t = (strip_comb_depth_of_term_destructive t, 
    strip_comb_depth_of_term t, (* should be same as before, but without generating garbage *)
    comb_depth_of_term t, 
    Term.size_of_term t)
  val res = map comp tests;
in
  val _ = @{assert} (res = 
     [(3, 3, 4, 5), 
      (2, 2, 2, 2), 
      (4, 4, 5, 5), 
      (3, 3, 3, 3), 
      (6, 6, 6, 6), 
      (1, 1, 1, 1),
      (7, 7, 7, 7)])
end

fun opt_print_unsolved_tac opt msg ctxt st = 
  if opt ctxt andalso Thm.nprems_of st > 0 then print_tac ctxt msg st else all_tac st 

val print_unsolved_tac = opt_print_unsolved_tac (K true)

structure HoarePackage = Hoare

structure More_Local_Theory =
struct


fun gen_in_theory_result transfer_data f lthy =
  let
    val (reinit, thy) = Named_Target.exit_global_reinitialize lthy
  in
    f thy ||> reinit ||> transfer_data lthy
  end


fun gen_in_theory transfer_data f lthy =
  let
    val (reinit, thy) = Named_Target.exit_global_reinitialize lthy
  in
    f thy |> reinit |> transfer_data lthy
  end

end



structure Utils = 
struct
open Utils


fun first_match [] t = raise Match
  | first_match (f::fs) t = f t handle Match => first_match fs t

fun add_match g f = first_match [g, f];
 
fun fast_eq eq (x, y) = pointer_eq (x, y) orelse eq (x, y)
fun fast_merge merge (x, y) = if pointer_eq (x, y) then x else merge (x, y)

fun distinct_strs xs =
 let
   fun dist seen [] = []
     | dist seen (x::xs) = 
         let val seen' = Symtab.insert (K false) (x, ()) seen 
         in
           x :: dist seen' xs
         end
         handle Symtab.DUP _ => dist seen xs
 in
   dist Symtab.empty xs
 end

fun ord_like_list eq xs (x, y) = int_ord (find_index (curry eq x) xs, find_index (curry eq y) xs)
fun sort_like_list eq xs = sort (ord_like_list eq xs)

(*
 * Catch-all for invalid inputs: Instead of raising MATCH, describe what
 * the invalid input was.
 *)
exception InvalidInput of string;
fun invalid_typ s (t : typ) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ Protocol_Message.clean_output (@{make_string} t) ^ "'")
fun invalid_term s (t : term) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ Protocol_Message.clean_output (@{make_string} t) ^ "'")
fun invalid_term' ctxt s (t : term) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ Protocol_Message.clean_output (Pretty.string_of (Syntax.pretty_term ctxt t)) ^ "'")
fun invalid_input s t =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ Protocol_Message.clean_output t ^ "'")

(*
 * Decoding and parsing Isabelle terms into ML terms.
 *)

(* Decode a list. *)
fun decode_isa_list t =
  HOLogic.dest_list t handle TERM _ => invalid_term "isabelle list" t

(* Encode a list. *)
fun encode_isa_list T xs = HOLogic.mk_list T xs

(* Decode a chracter. *)
fun decode_isa_char t =
  Char.chr (HOLogic.dest_char t) handle TERM _ => invalid_term "isabelle char" t

(* Encode a character. *)
fun encode_isa_char t = HOLogic.mk_char (Char.ord t)

(* Decode a string. *)
fun decode_isa_string t =
  decode_isa_list t
  |> map decode_isa_char
  |> String.implode

(* Encode a string. *)
fun encode_isa_string s =
  String.explode s
  |> map encode_isa_char
  |> encode_isa_list @{typ char}

(* Transform an ML list of strings into an isabelle list of strings. *)
fun ml_str_list_to_isa s =
  map encode_isa_string s
  |> encode_isa_list @{typ "string"}

(* Transform an isabelle list of strings into an ML list of strings. *)
fun isa_str_list_to_ml t =
  decode_isa_list t
  |> map decode_isa_string

(* Printing of rules with optional name links *)
fun pretty_rule ctxt thm =
  let
    val prule = Thm.pretty_thm ctxt thm
  in
    case Properties.get (Thm.get_tags thm) Markup.nameN of
      NONE => prule
    | SOME name => Pretty.block [
        Pretty.marks_str (Proof_Context.markup_extern_fact ctxt name), 
        Pretty.str ": ", 
        prule]
  end

val string_of_rule = Pretty.string_of oo pretty_rule

fun split_path p =
  let
    fun split_single p = [Path.dir p, Path.base p] handle ERROR _ => [p]
    fun split p ps = 
      case split_single p of
        [dir, base] => split dir (base :: ps)
      | ps' => ps' @ ps  
  in
    split p []
  end

fun implode_path [] = Path.root
  | implode_path ps = foldl1 (uncurry Path.append) ps

fun make_relative p =
  if Path.is_absolute p then
    split_path p |> filter_out (fn p => p = Path.root) |> implode_path
  else p
         
fun sanitized_path thy tmp_dir orig_path =
  let
    val master_dir = Resources.master_directory thy
  in
     Path.append tmp_dir 
       (make_relative (Path.append (Path.expand master_dir) orig_path))
  end

(* Different sides of a binary operator. *)
fun rhs_of (Const _ $ _ $ r) = r
  | rhs_of t = raise (TERM ("rhs_of", [t]))
fun lhs_of (Const _ $ l $ _) = l
  | lhs_of t = raise (TERM ("lhs_of", [t]))

fun rhs_of_eq (Const (@{const_name "Trueprop"}, _) $ eq) = rhs_of_eq eq
  | rhs_of_eq (Const (@{const_name "Pure.eq"}, _) $ _ $ r) = r
  | rhs_of_eq (Const (@{const_name "HOL.eq"}, _) $ _ $ r) = r
  | rhs_of_eq t = raise (TERM ("rhs_of_eq", [t]))

fun lhs_of_eq (Const (@{const_name "Trueprop"}, _) $ eq) = lhs_of_eq eq
  | lhs_of_eq (Const (@{const_name "Pure.eq"}, _) $ l $ _) = l
  | lhs_of_eq (Const (@{const_name "HOL.eq"}, _) $ l $ _) = l
  | lhs_of_eq t = raise (TERM ("lhs_of_eq", [t]))

fun clhs_of ct = nth (Drule.strip_comb ct |> #2) 0
fun crhs_of ct = nth (Drule.strip_comb ct |> #2) 1

fun dest_eq ct =
  let
    val [lhs, rhs] = snd (Drule.strip_comb ct)
  in (lhs, rhs) end


fun crhs_of_eq ct = case Thm.term_of ct of
      (Const (@{const_name "Trueprop"}, _) $ eq) => crhs_of_eq (snd (Thm.dest_comb ct))
    | (Const (@{const_name "Pure.eq"}, _) $ _ $ _) => crhs_of ct
    | (Const (@{const_name "HOL.eq"}, _) $ _ $ _) => crhs_of ct
    | t => raise (TERM ("crhs_of_eq", [t]))

fun clhs_of_eq ct = case Thm.term_of ct of
      (Const (@{const_name "Trueprop"}, _) $ eq) => clhs_of_eq (snd (Thm.dest_comb ct))
    | (Const (@{const_name "Pure.eq"}, _) $ _ $ _) => clhs_of ct
    | (Const (@{const_name "HOL.eq"}, _) $ _ $ _) => clhs_of ct
    | t => raise (TERM ("clhs_of_eq", [t]))

fun dest_eq' ct = case Thm.term_of ct of
      (Const (@{const_name "Trueprop"}, _) $ eq) => dest_eq (snd (Thm.dest_comb ct))
    | (Const (@{const_name "Pure.eq"}, _) $ _ $ _) => dest_eq ct
    | (Const (@{const_name "HOL.eq"}, _) $ _ $ _) => dest_eq ct
    | t => raise (TERM ("dest_eq'", [t]))

fun chead_of ct = Drule.strip_comb ct |> fst
fun ctail_of ct = Drule.strip_comb ct |> snd |> hd
fun cterm_nth_arg ct n =
  (Drule.strip_comb ct |> snd |> (fn x => nth x n))
  handle Subscript =>
    raise CTERM ("Argument " ^ (@{make_string} n) ^ " doesn't exist", [ct])
fun term_nth_arg t n =
  (Term.strip_comb t |> snd |> (fn x => nth x n))
  handle Subscript =>
    raise TERM ("Argument " ^ (@{make_string} n) ^ " doesn't exist", [t])

fun dest_nat_or_number t =
  case try HOLogic.dest_number t of
     SOME (_, n) => n
   | NONE => HOLogic.dest_nat t

fun eta_redex t =
  let
    fun eta bs (Abs (_, _, b)) = eta (Bound (length bs) :: bs) b
      | eta bs (t as (_ $ _ )) = (case strip_comb t of
         (head, args) => if is_prefix (op =) (rev bs) (rev args)
           then (true, list_comb (head, (rev (drop (length bs) (rev args)))))
           else (false, t))
      | eta _ t = (false, t)
  in case eta [] t of
       (true, x) => (true, x)
     | (false, _) => (false, t)
  end

fun norm_eta (t as Abs _) =
      (case eta_redex t of (true, t') => (true, snd (norm_eta t')) | _ => (false, t))
  | norm_eta (t as (t1 $ t2)) =
      let
        val (b1, t1') = norm_eta t1
        val (b2, t2') = norm_eta t2
        val b = b1 orelse b2
      in if b then (b, t1' $ t2') else (false, t) end
  | norm_eta t = (false, t)

val cterm_eq = is_equal o Thm.fast_term_ord

val trivial_eq = Match_Cterm.switch [
  @{cterm_match \<open>Trueprop (?lhs = ?rhs)\<close>} #> (fn {lhs, rhs,...} => 
     cterm_eq (lhs, rhs)), 
  (fn _ => false)]

val trivial_meta_eq = Match_Cterm.switch [
  @{cterm_match \<open>(?lhs \<equiv> ?rhs)\<close>} #> (fn {lhs, rhs,...} => 
     cterm_eq (lhs, rhs)), 
  (fn _ => false)]

val trivial_eq_thm = Thm.cconcl_of #> trivial_eq

val trivial_meta_eq_thm = Thm.cconcl_of #> trivial_meta_eq

val _ = Theory.setup
  (ML_Antiquotation.inline \<^binding>\<open>assert_msg\<close>
    (Scan.succeed "(fn b => fn msg => if b then () else raise General.Fail (msg ()))"))
end


