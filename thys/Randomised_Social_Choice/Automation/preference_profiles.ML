signature PREFERENCE_PROFILES =
sig

type prefs
type profile
type support
type lottery
type 'a permutation


val apply_permutation : ('a * 'a -> bool) -> 'a permutation -> 'a -> 'a
val apply_reverse_permutation : ('a * 'a -> bool) -> 'a permutation -> 'a -> 'a
val is_identity : ('a * 'a -> bool) -> 'a permutation -> bool
val fixpoints : ('a * 'a -> bool) -> 'a permutation -> 'a list
val permutations : ('a * 'a -> bool) -> 'a list -> 'a permutation Seq.seq
val cycles : ('a * 'a -> bool) -> 'a permutation -> 'a list list

(* Equality of weak rankings *)
val eq_prefs : (prefs * prefs) -> bool

(* Equivalence of preference profiles up to permutation of agents *)
val equiv_profile_anonymity : (profile * profile) -> bool

val agents_of_profile : profile -> term list
val agentT : profile -> typ
val alts_of_profile : profile -> term list
val altT : profile -> typ

val permute_profile : term permutation -> profile -> profile

val ranking : prefs -> term * term -> bool
val strict_ranking : prefs -> term * term -> bool
val pareto : profile -> term * term -> bool
val strict_pareto : profile -> term * term -> bool
val relation_of_prefs : prefs -> (term * term) list

val probability : lottery -> term list -> Rat.rat
val stochastic_dominance : prefs -> lottery * lottery -> bool
val strict_stochastic_dominance : prefs -> lottery * lottery -> bool
val mk_support_witness : profile -> support * lottery -> support * lottery * term

(* Lazy list of all permutations that, when applied to the first profile, yield one 
   anonymity-equivalent to the second profile *)
val find_an_isomorphisms : profile * profile -> term permutation Seq.seq

(* Return the first such isomorphism (or NONE) *)
val find_an_isomorphism : profile * profile -> term permutation option

(* Find all non-trivial automorphisms of a preference profile *)
val find_an_automorphisms : profile -> ((term * term) * term permutation) list

(* Compute a list of normalising equations implied by the automorphisms of a 
   preference profile *)
val derive_orbit_equations : profile -> ((term * term) * term permutation) list

(* The list of alternatives that are weakly preferred to the given alternative *)
val preferred_alts : prefs -> term -> term list

(* The list of Pareto-domination pairs (first element dominates second; strict preference
   for the agent in the third component) *)
val pareto_pairs : profile -> (term * term * term) list

(* The set of all Pareto losers in a profile *)
val pareto_losers : profile -> (term * term * term) list

val find_pareto_witness : profile -> term -> (term * term * term) option

(* Construct the linear program that encodes SD inefficiency of the given support *)
val mk_inefficiency_lp : profile -> support -> (string list * string * int) list

(* Find a lottery that is strictly SD-preferred to the given support and the agent who
   strictly prefers it. *)
val find_inefficiency_witness : profile -> support -> (lottery * term) option

(* Finds all non-singleton inefficient supports with a inefficiency certificate for each one.
   (non-singleton because singleton inefficient supports are simply Pareto losers *)
val find_minimal_inefficient_supports : profile -> (support * lottery * term) list

val manipulation_distance : (prefs * prefs) -> int

(* Finds all ways for one voter to manipulate the first given profile to obtain a profile
   that is equivalent to the second profile modulo anonymity and neutrality.
   Returns a witness for each possible manipulation, consisting of the manipulating voter, 
   the voter with whose preferences her preferences need to be replaced, 
   and the permutation of alternatives.
 *)
val find_manipulations : profile * profile -> (term * term * int * term permutation) list

end

structure Preference_Profiles : PREFERENCE_PROFILES =
struct

type prefs = term list list
type profile = (term * prefs) list
type 'a permutation = ('a * 'a) list
type support = term list
type lottery = (term * Rat.rat) list

val eq_prefs = eq_list (eq_set (op aconv))

fun equiv_profile_anonymity xy = 
  let
    val xy = apply2 (map snd) xy
  in
    submultiset eq_prefs xy andalso submultiset eq_prefs (swap xy)
  end

val agents_of_profile = map fst
val agentT = hd #> fst #> fastype_of
val alts_of_profile = hd #> snd #> List.concat
val altT = hd #> snd #> hd #> hd #> fastype_of

local
  val mem = member op aconv
in

fun ranking [] _ = false
  | ranking (xs :: xss) (x, y) = mem xs y orelse (not (mem xs x) andalso ranking xss (x, y))

fun strict_ranking [] _ = false
  | strict_ranking (xs :: xss) (x, y) = 
      not (mem xs x) andalso (mem xs y orelse strict_ranking xss (x, y))
end

fun fixpoints eq xs = xs |> filter eq |> map fst

fun apply_permutation _ [] x = x
  | apply_permutation eq ((x,y)::p) x' = if eq (x,x') then y else apply_permutation eq p x'

fun apply_reverse_permutation _ [] x = x
  | apply_reverse_permutation eq ((y,x)::p) x' = 
      if eq (x,x') then y else apply_reverse_permutation eq p x'

val is_identity = forall

fun cycles eq =
  let
    fun go3 _ _ [] = raise Match
      | go3 acc a ((b,c) :: xs) =
         if eq (a,b) then (c, acc @ xs) else go3 ((b,c) :: acc) a xs
    fun go2 cyc a b xs =
      if eq (a,b) then 
        (cyc, xs) 
      else case go3 [] b xs of
        (c, xs) => go2 (b::cyc) a c xs
    fun go1 acc [] = acc
      | go1 acc ((a,b) :: xs) = 
          case go2 [a] a b xs of (cyc, xs') => go1 (rev cyc :: acc) xs'
  in
    rev o go1 []
  end    

fun permutations eq xs = 
  let
    fun go acc [] = Seq.single acc
      | go acc xs = Seq.maps (fn x => go (x::acc) (remove1 eq x xs)) (Seq.of_list xs)
  in
    Seq.map (fn ys => xs ~~ ys) (go [] xs)
  end

fun probability (lott1 : lottery) xs =
  lott1 |> filter (member op aconv xs o fst) |> (fn xs => fold (fn x => fn y => snd x +/ y) xs Rat.zero)

fun uniform_lottery xs = 
  let
    val p = Rat.rat_of_quotient (1, length xs)
  in
    map (fn x => (x, p)) xs
  end

fun stochastic_dominance p (lott1, lott2) =
  let
    fun go _ [] = true
      | go _ [_] = true
      | go (prob1 : Rat.rat, prob2 : Rat.rat) (xs::xss) = 
          let 
            val (prob1, prob2) = (prob1 +/ probability lott1 xs, prob2 +/ probability lott2 xs)
          in  
            prob1 <=/ prob2 andalso go (prob1, prob2) xss
          end
  in
    go (Rat.zero, Rat.zero) p
  end

fun strict_stochastic_dominance p (lott1, lott2) =
  stochastic_dominance p (lott1, lott2) andalso not (stochastic_dominance p (lott2, lott1))  

fun mk_support_witness p (supp, lott) =
  let
    val lott' = uniform_lottery supp
    val i = find_first (fn (_, ps) => not (stochastic_dominance ps (lott, lott'))) p
            |> Option.map fst
  in
    case i of
      NONE => error "Not a proper inefficiency wittnes."
    | SOME i => (supp, lott, i)
  end

fun permute_profile p = map (fn (x, yss) => (x, map (map (apply_permutation op aconv p)) yss))

fun find_an_isomorphisms (xs, ys) =
  let
    fun is_iso p = equiv_profile_anonymity (permute_profile p xs, ys)
  in
    permutations (op aconv) (alts_of_profile xs)
    |> Seq.filter (is_iso)
  end

val find_an_isomorphism =
  find_an_isomorphisms #> Seq.pull #> Option.map fst

fun seq_fold f s acc =
  case Seq.pull s of
    NONE => acc
  | SOME (x,s) => seq_fold f s (f x acc)

fun find_an_automorphisms xs =
  let
    fun eq (((a,b),_), ((c,d),_)) = a aconv c andalso b aconv d
  in
    (xs, xs) 
    |> find_an_isomorphisms
    |> Seq.map (filter_out (op aconv))
    |> Seq.filter (not o null)
    |> Seq.maps (fn xs => Seq.of_list (map (fn x => (x, xs)) xs))
    |> (fn s => seq_fold (fn x => fn y => insert eq x y) s [])
  end


fun preferred_alts r x =
  let
    fun go acc [] = acc
      | go acc (xs::xss) =
          if member op aconv xs x then (xs @ acc) else go (xs @ acc) xss
  in
    go [] r
  end

fun pareto p (x,y) = forall (fn (_, prefs) => ranking prefs (x,y)) p
fun strict_pareto p (x,y) = pareto p (x,y) andalso not (pareto p (y,x))

fun pareto_pairs p =
  let
    val alts = alts_of_profile p
    fun dom_set x =
      let
        fun go [] = []
          | go (xs::xss) = 
              if member op aconv xs x then List.concat (xs::xss) else go xss
      in
        fold (fn (_, xss) => inter op aconv (go xss)) p alts
      end
    fun filter_out_symmetric xs =
      filter_out (fn (x,y) => member (eq_pair op aconv op aconv) xs (y, x)) xs
    val filter_out_trans =
      let
        fun go acc [] = acc
          | go acc (x::xs) =
              if member (op aconv o apply2 snd) acc x then 
                go acc xs 
              else 
                go (x::acc) xs
      in
        go []
      end
  in
    alts
    |> map (fn x => map (fn y => (x, y)) (dom_set x))
    |> List.concat
    |> filter_out_symmetric
    |> filter_out_trans
    |> map (fn (x,y) => (x, y, find_first (fn (_, p) => strict_ranking p (y,x)) p |> the |> fst))
  end

val pareto_losers = 
  pareto_pairs #> map (fn (a,b,c) => (b,a,c)) #> distinct (op aconv o apply2 #1)

fun find_pareto_witness p x =
  alts_of_profile p
  |> remove op aconv x
  |> get_first (fn y => 
       if forall (fn (_, prefs) => ranking prefs (x,y)) p then
         find_first (fn (_, prefs) => not (ranking prefs (y,x))) p
         |> Option.map (fn (i, _) => (x,y,i))
       else
         NONE)

(* Poor man's Union-Find *)
fun eqclasses eq carrier eqs = 
  let
    fun merge (a, b) m =
      let
        val ra = the (AList.lookup eq m a)
        val rb = the (AList.lookup eq m b)
      in
        map (apsnd (fn r => if eq (r, ra) then rb else r)) m
      end
  in
    fold merge eqs (carrier ~~ carrier)
  end

fun derive_orbit_equations p =
  let
    val alts = alts_of_profile p
    val automorphisms = find_an_automorphisms p
    val reprs = eqclasses op aconv alts (map fst automorphisms)
    val repr = AList.lookup op aconv reprs #> the
    val automorphisms = filter (fn ((a,b), _) => b aconv repr a) automorphisms
  in
    automorphisms
  end


fun mk_inefficiency_lp p support =
  let
    val alts = alts_of_profile p
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    val in_support = member op aconv support
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    fun mk_slack_var i j = "r" ^ Int.toString i ^ "_" ^ Int.toString j

    fun mk_ineqs_for_agent acc _ [] _ _ = acc
      | mk_ineqs_for_agent acc _ [_] _ _ = acc
      | mk_ineqs_for_agent acc (lhs, rhs) (xs::xss) j i =
          let
            val lhs' = map mk_lottery_var xs @ lhs
            val rhs' = length (filter in_support xs) + rhs
          in
            mk_ineqs_for_agent ((lhs',mk_slack_var i j,rhs')::acc) (lhs',rhs') xss (j+1) i
          end
  in
    fold (fn (_, r) => fn (i,acc) => (i+1, mk_ineqs_for_agent acc ([],0) r 0 i)) p (0, []) |> snd
  end

local
open Rat_Linear_Program
in

fun lp_constr_to_qsopt_constr n (lhs, slack, rhs) =
  let
    val n = Rat.rat_of_int n
    val lhs' = (Rat.rat_of_int (~1), slack) :: map (fn x => (n, x)) lhs
  in
    (lhs', EQ, Rat.rat_of_int rhs)
  end

fun mk_inefficiency_lp_qsopt p support =
  let
    val constrs = mk_inefficiency_lp p support
    val alts = alts_of_profile p
    val n = length support
    val sum = map (fn x => (Rat.one, x))
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    val lottery_vars = map mk_lottery_var alts
    val slack_vars = map #2 constrs
 
    val constrs' = map (lp_constr_to_qsopt_constr n) constrs
    val eq = (sum lottery_vars, EQ, Rat.one)
  in
    (MAXIMIZE, sum slack_vars, eq :: constrs', [])
  end


fun find_inefficiency_witness p lottery =
  let
    val alts = alts_of_profile p
    val lottery_vars = List.tabulate (length alts, fn x => "q" ^ Int.toString x);
    val slack_vars = 
      p ~~ List.tabulate (length p, Int.toString)
      |> map (fn ((x,prefs),i) => 
           (x, List.tabulate (length prefs - 1, fn j => "r" ^ i ^ "_" ^ Int.toString j)))
    fun the_default x NONE = x
      | the_default _ (SOME y) = y

    fun process_solution (diff, assignments) = 
      let
        val get_val = the_default Rat.zero o AList.lookup op= assignments
        val i =
          slack_vars 
          |> find_first (snd #> exists (fn x => get_val x >/ Rat.zero)) 
          |> Option.map fst
      in 
        if diff = Rat.zero then 
          NONE 
        else 
          Option.map (fn i => (alts ~~ map get_val lottery_vars, i)) i
      end
  in 
    case solve_program (mk_inefficiency_lp_qsopt p lottery) of
      Optimal x => process_solution x
    | _ => raise Match
  end

fun power_set xs =
  let
    fun go acc [] = [acc]
      | go acc (x::xs) = go acc xs @ go (x::acc) xs
  in
    go [] xs |> sort (int_ord o apply2 length)
  end

fun is_singleton [_] = true
  | is_singleton _ = false

fun find_minimal_inefficient_supports p =
  let
    val alts = subtract op aconv (map #1 (pareto_losers p)) (alts_of_profile p)
    fun go supp acc =
      if List.null supp orelse is_singleton supp orelse
            member (fn (a, b) => subset op aconv (#1 b, a)) acc supp then
        acc
      else 
        case find_inefficiency_witness p supp of
          NONE => acc
        | SOME (lott, i) => (supp, lott, i) :: acc
  in
    fold go (power_set alts) []
  end

fun manipulations xs y =
  let
    fun go acc _ [] = acc
      | go acc xs1 (x::xs2) = 
          go ((fst x, y, rev xs1 @ (fst x,y) :: xs2) :: acc) (x::xs1) xs2
  in
    rev (go [] [] xs)
  end

val bind = Seq.maps
fun bind' f x = bind f (Seq.of_list x)

val relation_of_prefs =
  let
    fun go acc [] = acc
      | go acc (xs::xss) =
          go (maps (fn x => map (pair x) (flat (xs::xss))) xs @ acc) xss
  in
    go []
  end

fun manipulation_distance (prefs1, prefs2) =
  let
    val r1 = relation_of_prefs prefs1
    val r2 = relation_of_prefs prefs2
    val subtract' = subtract (eq_pair op aconv op aconv)
  in
    length (subtract' r1 r2) + length (subtract' r2 r1)
  end

fun find_manipulations (p1, p2) =
  let
    val alts = alts_of_profile p1
    fun prefs p i = the (AList.lookup op aconv p i)
  in
    permutations op aconv alts |> bind (fn sigma =>
      p2 |> bind' (fn (j, prefs) =>
        Seq.of_list (manipulations (permute_profile sigma p1) prefs)
        |> Seq.filter (fn (_, _, p1') => equiv_profile_anonymity (p1', p2))
        |> Seq.map (fn (a, _, _) => (a, j, sigma))))
        |> Seq.map_filter (fn (i, j, sigma) =>
             let
               val (prefs1, prefs2) = (prefs p1 i, prefs p2 j)
               val prefs1 = map (map (apply_permutation op aconv sigma)) prefs1
               val dist = manipulation_distance (prefs1, prefs2)
             in
               SOME (i, j, dist, sigma)
             end)
    |> Seq.list_of
  end

end

end