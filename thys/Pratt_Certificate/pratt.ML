signature PRATT =
sig

datatype pratt = Prime of int | Triple of int * int * int
type pratt_cert = pratt list

val termify_pratt : pratt -> term
val termify_cert : pratt_cert -> term
val certify_prime : int -> pratt_cert option
val pratt_tac : pratt_cert option -> Proof.context -> int -> tactic

val pretty_pratt : pratt -> Pretty.T
val pretty_cert : pratt_cert -> Pretty.T

val parse_pratt : pratt parser 
val parse_cert : pratt_cert parser

end

structure Pratt : PRATT =
struct

fun mod_exp _ 0 m = if m = 1 then 0 else 1
  | mod_exp b e m = 
      case Integer.div_mod e 2 of
        (e', 0) => mod_exp ((b * b) mod m) e' m
      | (e', _) => (b * mod_exp ((b * b) mod m) e' m) mod m

datatype pratt = Prime of int | Triple of int * int * int

type pratt_cert = pratt list

fun termify_pratt (Prime p) = @{term Prime} $ HOLogic.mk_number @{typ Nat.nat} p
  | termify_pratt (Triple (p,a,x)) = 
      Term.betapplys (@{term Triple}, map (HOLogic.mk_number @{typ Nat.nat}) [p,a,x])

val termify_cert = map termify_pratt #> HOLogic.mk_list @{typ pratt}

val parse_pratt = 
    (Parse.nat >> Prime) || 
    (Args.parens (Parse.nat --| Args.$$$ "," -- Parse.nat --| Args.$$$ "," -- Parse.nat) >> 
      (fn ((a,b),c) => Triple (a,b,c)))

val parse_cert = Parse.list1 parse_pratt

local
  fun calc_primes mode ps i n =
      if n = 0 then ps
      else if List.exists (fn p => i mod p = 0) ps then
        let
          val i = i + 1
          and n = if mode then n else n - 1
        in
          calc_primes mode ps i n
        end
      else
        let
          val ps = ps @ [i]
          and i = i + 1
          and n = n - 1
        in
          calc_primes mode ps i n
        end;
in
  fun primes_up_to n =
      if n < 2 then []
      else calc_primes false [2] 3 (n - 2);
end;

fun certify_prime p =
  let
    val primes = primes_up_to (p - 1)
    fun prime_factors n =
      let
        fun go acc [] = acc
          | go acc (p::ps) = go (if n mod p = 0 then p::acc else acc) ps
      in
        go [] primes
      end

    fun find_prime_factor n =
      let
        fun go [] = NONE
          | go (p::ps) =
              if p > n then 
                NONE 
              else
                case Integer.div_mod n p of
                  (q, 0) => SOME (p, q)
                | _ => go ps
      in
        go primes
      end

    fun find_wit p factors =
      let
        fun go a =
          if a >= p then
            NONE
          else if mod_exp a (p - 1) p = 1 andalso
                    forall (fn q => mod_exp a ((p - 1) div q) p <> 1) factors then
            SOME a
          else
            go (a + 1)
      in
        go 1
      end

    fun add_goals ctxt goals goals' =
      fold (fn goal => fn goals => 
        if member op= goals goal orelse member op= ctxt goal then goals else goal :: goals) 
        goals' goals

    fun prove' ctxt [] = SOME ctxt
      | prove' ctxt (goal :: goals) =
          if member op = goals goal then
            prove' ctxt goals
          else
            Option.map (fn ctxt => goal :: ctxt) (prove ctxt (goal :: goals))     
    and prove ctxt [] = SOME ctxt
      | prove ctxt (Prime p :: goals) =
          let
            val factors = prime_factors (p - 1)
            val wit = find_wit p factors
          in
            case wit of
              NONE => NONE
            | SOME a => prove' ctxt (add_goals ctxt goals [Triple (p, a, p - 1)])
          end
     | prove ctxt (Triple (p, a, y) :: goals) =
         case find_prime_factor y of
           NONE => prove' ctxt goals
         | SOME (q, x) => prove' ctxt (add_goals ctxt goals [Prime q, Triple (p, a, x)])
  in
    prove' [] [Prime p]
  end

local
  val pretty_int = Pretty.str o Int.toString
in
fun pretty_pratt (Prime p) = pretty_int p
  | pretty_pratt (Triple (a,b,c)) = 
      [a,b,c] |> map pretty_int |> Pretty.commas |> Pretty.enclose "(" ")"
      
val pretty_cert = Pretty.list "[" "]" o map pretty_pratt
end
  
fun pratt_tac cert ctxt i =
  let
    fun print_cert cert =
      [Pretty.keyword1 "by", Pretty.brk 1, Pretty.str "(", Pretty.str "pratt ", 
        Pretty.blk (2, [pretty_cert cert]), Pretty.str ")"]
      |> Pretty.blk o pair 4
      |> Pretty.string_of
      |> Active.sendback_markup_command
      |> prefix "To repeat this proof with a pre-computed certificate, use:\n"
      |> Output.information
    fun certify p =
      case cert of
        SOME cert => SOME cert
      | NONE =>         
        let
          val p' = p |> HOLogic.dest_Trueprop |> dest_comb |> snd |> HOLogic.dest_number |> snd
        in
          case certify_prime p' of
            NONE => NONE
          | SOME cert => let val _ = print_cert cert in SOME cert end
        end
    fun tac cert =
      let
        val thm = Thm.instantiate' [] [SOME (Thm.cterm_of ctxt (termify_cert cert))] 
          @{thm pratt_primeI}
        val unfold_thms = @{thms eval_valid_cert bex_simps_lazy HOL.simp_thms set_simps pratt.simps}
      in
        SOLVE (SELECT_GOAL (
          HEADGOAL (resolve_tac ctxt [thm])
          THEN Local_Defs.unfold_tac ctxt unfold_thms
          THEN DETERM (HEADGOAL (REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI})))
          THEN PARALLEL_ALLGOALS (Simplifier.simp_tac ctxt)
        ) i)
      end
  in
    Subgoal.FOCUS_PARAMS (fn {concl, ...} => 
      case certify (Thm.term_of concl) of
        NONE => no_tac
      | SOME cert => tac cert) ctxt i
  end

end
