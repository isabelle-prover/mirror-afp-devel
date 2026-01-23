
signature SWF_UTIL =
sig

exception RANKING_INDEX of int
exception PARSE

type ranking = int list
type sp_clauses = ranking list * ranking list * (ranking * ranking) list
type line_iterator = unit -> string option

(* general functions *)
val fold1 : ('a -> 'a -> 'a) -> 'a list -> 'a
val bind_list : 'a list -> ('a -> 'b list) -> 'b list
val par_bind_list : 'a list -> ('a -> 'b list) -> 'b list
val subtract1 : ('a * 'b -> bool) -> 'a list -> 'b list -> 'b list

val lists_of_length : int -> 'a list -> 'a list list
val multisets_of_length : int -> 'a list -> 'a list list
val permutations : 'a list -> 'a list list

val majority_ord : 'a ord list -> 'a ord

val fact : int -> int
val inversions : 'a ord -> 'a list -> int
val swap_dist : ''a list -> ''a list -> int

(* functions dealing with rankings *)
val ord_of_ranking : ''a list -> ''a ord
val ranking_to_nat : ranking -> int
val nat_to_ranking : int -> int -> ranking

(* proving things *)
val mk_distinct_thms : Proof.context -> thm -> thm list
val mk_inversion_cache : Proof.context -> int -> (int * thm) array
val prove_mset_eq : Proof.context -> cterm * cterm -> thm
val simp_prove : Proof.context -> cterm -> thm
val simp_discharge : Proof.context -> thm -> thm
val simp_discharge_all : Proof.context -> thm -> thm

(* parsing and i/o *)
val list_iterator : string list -> line_iterator
val file_iterator : Path.T -> line_iterator
val read_profiles_gen : line_iterator -> ranking list list
val read_profiles_file : Path.T * bool -> ranking list list
val read_sp_clauses_file : Path.T * bool -> sp_clauses list
val read_sp_clauses_gen : line_iterator -> sp_clauses list

end


structure SWF_Util : SWF_UTIL =
struct

type ranking = int list
type sp_clauses = ranking list * ranking list * (ranking * ranking) list
type line_iterator = unit -> string option

val distinct_unfold_thms =
  [@{lemma "distinct [] \<longleftrightarrow> True" by simp},
   @{lemma "distinct (x # xs) \<longleftrightarrow> list_all (\<lambda>y. x \<noteq> y \<and> y \<noteq> x) xs \<and> distinct xs"
     by (auto simp: list.pred_set)}]

(*
  Turns a theorem of the form "distinct [x1, ..., xn]" into the list of theorems consisting of
  all inequalities "xi != xj" for all i, j with i != j.
*)
fun mk_distinct_thms ctxt thm =
  thm
  |> Local_Defs.unfold ctxt (distinct_unfold_thms @ @{thms HOL.simp_thms list.pred_inject})
  |> HOLogic.conj_elims

(* all lists of length n formed of elements of xs, in lexicographic order *)
fun lists_of_length n xs =
  let
    fun go acc 0 = [rev acc]
      | go acc n = maps (fn x => go (x :: acc) (n-1)) xs
  in
    go [] n
  end

(* all multisets of size n formed of elements of xs, in lexicographic order *)
fun multisets_of_length n xs =
  let
    fun go acc 0 _ = [rev acc]
      | go _ _ [] = []
      | go acc n (x :: xs) = go (x :: acc) (n-1) (x :: xs) @ go acc n xs
  in
    go [] n xs
  end

(* all pairs of the form (x, xs without x) *)
fun pick1 xs =
  let
    fun go _ [] = []
      | go acc (x :: xs) = (x, rev acc @ xs) :: go (x :: acc) xs
  in
    go [] xs
  end

(* all permutations of the given list, in lexicographic order *)
fun permutations xs =
  let
    fun go acc [] = [rev acc]
      | go acc xs =
          maps (fn (x, ys) => go (x :: acc) ys) (pick1 xs)
  in
    go [] xs
  end

(* number of elements in xs that satisfy p *)
fun count p xs = fold (fn x => fn acc => if p x then acc + 1 else acc) xs 0

(* number of inversions in the given list, i.e. indices i,j with i < j but x_i > x_j *)
fun inversions ord =
  let
    fun go acc [] = acc
      | go acc (x :: xs) = go (acc + count (fn y => is_less (ord (y, x))) xs) xs
  in
    go 0
  end

(*
  The swap distance (Kendall tau distance) of two lists. The lists are assumed to have no
  repeated elements and be permutations of each other (i.e. contain the same elements up to order).
*)
fun swap_dist xs ys =
  map (fn y => find_index (fn x => x = y) xs) ys
  |> inversions int_ord

(* 
  The order induced by a given ranking, where a ranking is a list of elements 
  sorted in descending order
*)
fun ord_of_ranking zs (x, y) =
  let
    fun go (z ::zs) =
      if z = y then if z = x then EQUAL else LESS else if z = x then GREATER else go zs
    | go _ = raise Match
  in
    go zs
  end

(*
  The majority relation induced by the given list of orders. In general, this relation is neither
  antisymmetric nor transitive.
*)
fun majority_ord zss (x,y) =
  let
    val (d1, d2) =
       List.partition (fn ord => is_less_equal (ord (x,y))) zss
       |> apply2 length
  in
    int_ord (d2, d1)
  end

(* the factorial n! *)
fun fact n = if n <= 1 then 1 else n * fact (n - 1)

(*
  Convert a ranking (or more generally a permutation) of the elements [0,..,n-1] to a number
  in the interval [0, n!). The mapping is strictly monotonic w.r.t. the lexicographic order.
*)
fun ranking_to_nat xs =
  let
    fun go acc _ [] = acc
      | go acc n (x :: xs) = go (acc * n + x) (n-1) (map (fn y => if y < x then y else y - 1) xs)
  in
    go 0 (length xs) xs
  end


(*
  The reverse of the above operation.
*)
exception RANKING_INDEX of int
fun nat_to_ranking n k =
  let
    fun go 0 _ = []
      | go n k =
          let
            val (x, y) = Integer.div_mod k (fact (n - 1))
          in
            x :: map (fn y => if y < x then y else y + 1) (go (n-1) y)
          end
    val _ = if k < 0 orelse k >= fact n then raise RANKING_INDEX k else ()
  in
    go n k
  end


val inversion_cache_simpset = simpset_of (
  @{context}
    delsimps @{thms snd_sort_and_count_inversions}
    addsimps @{thms snd_sort_and_count_inversions[symmetric]
                    sort_and_count_inversions.simps split_list_def})

(*
  For given n, build a cache that maps any permutation of [0,..,n-1] to the number of
  inversions in that list, and a theorem that witnesses this result. The permutations are
  encoded using the ranking_to_nat convention. 
*)
fun mk_inversion_cache ctxt n =
  let
    fun mk_thm i =
      let
        val xs = nat_to_ranking n i
        val t_xs = xs |> map (HOLogic.mk_number HOLogic.natT) |> HOLogic.mk_list HOLogic.natT
        val res = inversions int_ord xs
        val t_res = res |> HOLogic.mk_number HOLogic.natT
        val goal =
          \<^instantiate>\<open>xs = t_xs and res = t_res in prop "inversion_number (xs :: nat list) = res"\<close>
        val thm = Goal.prove ctxt [] [] goal (fn {context = ctxt, ...} => 
          ALLGOALS (Simplifier.simp_tac (put_simpset inversion_cache_simpset ctxt)))
      in
        (res, thm)
      end
  in
    Array.fromList (Par_List.map mk_thm (0 upto (fact n - 1)))
  end
  
(*
  Prove that two concrete multisets are equal, e.g. {#A,C,A,B#} = {#C,A,B,A#}
*)
fun normalize_mset_conv (ctxt : Proof.context) ct =
  let
    fun add_mset_conv ct =
      ct |> (
      case Thm.term_of ct of
        Const (\<^const_name>\<open>add_mset\<close>, _) $ t_x $
          (Const (\<^const_name>\<open>add_mset\<close>, _) $ t_y $ _) =>
        if is_less_equal (Term_Ord.term_ord (t_x, t_y)) then
          Conv.all_conv
        else
          Conv.rewr_conv @{thm add_mset_commute[THEN eq_reflection]}
          then_conv Conv.arg_conv add_mset_conv
      | _ => Conv.all_conv)
  in
    ct |> (
    case Thm.term_of ct of
      Const (\<^const_name>\<open>zero_class.zero\<close>, _) => Conv.all_conv
    | Const (\<^const_name>\<open>add_mset\<close>, _) $ _ $ _ =>
        Conv.arg_conv (normalize_mset_conv ctxt)
        then_conv add_mset_conv
    | _ => Conv.no_conv)
  end

fun prove_mset_eq ctxt (ct1, ct2) =
  let
    val (thm1, thm2) = apply2 (normalize_mset_conv ctxt) (ct1, ct2)
  in
    Thm.transitive thm1 (Thm.symmetric thm2)
  end

(* Prove the given proposition using the simplifier. *)
fun simp_prove ctxt ct =
  let
    val result =
      ct |> Goal.init |> SINGLE (ALLGOALS (Simplifier.simp_tac ctxt))
  in
    case result of
      SOME thm => Goal.finish ctxt thm
    | NONE => raise CTERM ("simp_prove: Failed to finish proof", [])
  end

(* Turn the theorem "A ==> B" into "B" using the simplifier. *)
fun simp_discharge ctxt thm =
  let
    val prem = Thm.cprem_of thm 1
  in
    Thm.implies_elim thm (simp_prove ctxt prem)
  end

(* Turn the theorem "[|A1, ..., An|] ==> B" into "B" using the simplifier. *)
fun simp_discharge_all ctxt thm =
  if Thm.nprems_of thm = 0 then thm else simp_discharge_all ctxt (simp_discharge ctxt thm)


fun fold1 _ [] = raise Empty
  | fold1 f (x :: xs) = fold f xs x

fun bind_list xs f = maps f xs

fun par_bind_list xs f = flat (Par_List.map f xs)


(*
  subtract first multiset from second multiset
*)
fun subtract1 eq = fold (remove1 eq)


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

(*
  Read a list of strategyproofness clauses from a file.
  Format: first line is "m n" where m = number of alternatives, n = number of agents.
  Following lines are a list of integers representing rankings. Each line is of the form 
  "r1 ... rn s1 ... sn (t1 t2)+" where r1 ... rn and s2 ... sn are profiles
  and each t1 and t2 is a pair of rankings such that f(r) = t1 and f(s) = t2 cannot occur
  simultaneously due to strategyproofness.

  Comments can be written in lines starting with a #
*)
fun read_sp_clauses_gen it =
  let
    exception PARSE
    fun it' () =
      case it () of
        NONE => NONE
      | SOME l =>
          if String.size l = 0 orelse String.sub (l, 0) = #"#" then it' ()
          else SOME (map (the o Int.fromString) (String.tokens (fn c => c = #" ") l))
            handle Option.Option => raise PARSE
    val SOME [m, n] = it' () handle Bind => raise PARSE
    val f = nat_to_ranking m
      handle RANKING_INDEX m => raise RANKING_INDEX m

    fun go acc =
          case it' () of
            NONE => rev acc
          | SOME xs =>
              let
                val (p1, xs) = chop n xs
                val (p2, xs) = chop n xs
                val ys = map (fn [x, y] => (f x, f y)) (chop_groups 2 xs) 
                  handle Match => raise PARSE
              in
                go ((map f p1, map f p2, ys) :: acc)
              end          
  in
    go []
 end

fun read_sp_clauses_file (path, false) =
      read_sp_clauses_gen (file_iterator path)
  | read_sp_clauses_file (path, true) =
      path
      |> Bytes.read
      |> XZ.uncompress 
      |> Bytes.trim_split_lines
      |> list_iterator
      |> read_sp_clauses_gen

exception PARSE


(*
  Read a list of profiles. First line is of the form "m n" with m = number of alternatives
  and n = number of agents. Following lines contain one profile each, encoded as a list of
  n integers separated by spaces. Each integer represents a ranking in the usual encoding.

  Comments can be written in lines starting with a #
*)
fun read_profiles_gen it =
  let
    fun it' () =
      case it () of
        NONE => NONE
      | SOME l =>
          if String.size l = 0 orelse String.sub (l, 0) = #"#" then it' ()
          else SOME (map (the o Int.fromString) (String.tokens (fn c => c = #" ") l))
            handle Option.Option => raise PARSE
    val SOME [m, n] = it' ()
    val f = nat_to_ranking m
      handle RANKING_INDEX m => raise RANKING_INDEX m

    fun go acc =
          case it' () of
            NONE => rev acc
          | SOME xs => if length xs <> n then raise PARSE else go (map f xs :: acc)
  in
    go []
 end
   handle Bind => raise PARSE

fun read_profiles_file (path, false) =
      read_profiles_gen (file_iterator path)
  | read_profiles_file (path, true) =
      path
      |> Bytes.read
      |> XZ.uncompress 
      |> Bytes.trim_split_lines
      |> list_iterator
      |> read_profiles_gen

end
