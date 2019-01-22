signature PRATT =
sig

type prime_thm_cache = (int * thm) list
datatype cert = Pratt_Node of int * int * cert list
exception INVALID_CERT of cert

val get_cert_number : cert -> int

val mk_cert : int -> cert option
val check_cert : cert -> bool
val replay_cert : prime_thm_cache -> cert -> Proof.context -> thm * prime_thm_cache
val prove_prime : prime_thm_cache -> int -> Proof.context -> thm option * prime_thm_cache

val pretty_cert : cert -> Pretty.T
val parse_cert : Input.source -> cert

val cert_cartouche : cert parser 
val tac : bool -> prime_thm_cache -> cert option -> Proof.context -> int -> tactic

end

structure Pratt : PRATT =
struct

fun mod_exp _ 0 m = if m = 1 then 0 else 1
  | mod_exp b e m = 
      case Integer.div_mod e 2 of
        (e', 0) => mod_exp ((b * b) mod m) e' m
      | (e', _) => (b * mod_exp ((b * b) mod m) e' m) mod m

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

fun fold_accum f xs acc =
  fold (fn x => fn (ys, acc) => case f x acc of (y, acc') => (y :: ys, acc')) xs ([], acc)
  |> apfst rev

val small_primes = primes_up_to 100

fun factorise n =
  let
    val init = (small_primes, 101, false)
    fun get_divisor (p :: _, _, _) = p
      | get_divisor ([], k, _) = k
    fun next (_ :: ps, k, b) = (ps, k, b)
      | next ([], k, b) = ([], k + (if b then 4 else 2), not b)

    fun divide_out d n =
      let
        fun go (n, acc) =
          if n mod d = 0 then
            go (n div d, acc + 1)
          else
            (n, acc)
      in
        go (n, 0)
      end
    
    fun go st n acc =
      let
        val d = get_divisor st
      in
        if n <= 1 then
          rev acc
        else if d * d > n then
          rev ((n, 1) :: acc)
        else
          case divide_out d n of
            (n', k) => go (next st) n' (if k = 0 then acc else (d, k) :: acc)
      end
  in
    go init n []
  end


type prime_thm_cache = (int * thm) list

datatype cert = Pratt_Node of int * int * cert list

exception INVALID_CERT of cert

fun get_cert_number (Pratt_Node (n, _, _)) = n

fun mk_cert n =
  let
    exception PRATT
    fun cert n ctxt =
      if AList.defined op= ctxt n then
        ctxt
      else
        let
          val ps = map fst (factorise (n - 1))
          fun suitable' a p = mod_exp a ((n - 1) div p) n <> 1
          fun suitable a = mod_exp a (n - 1) n = 1 andalso forall (suitable' a) ps
          val a =
            case find_first suitable (1 upto n) of
              NONE => raise PRATT
            | SOME a => a
          val ctxt = fold cert ps ctxt
          val proofs = map (the o AList.lookup op= ctxt) ps
        in
          (n, Pratt_Node (n, a, proofs)) :: ctxt
        end
  in
    AList.lookup op= (cert n []) n
      handle PRATT => NONE
  end


fun prove_list_all ctxt property thms =
  let
    val thm =
      Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt property)]
        @{thm list.pred_inject(1)}
    fun go acc [] = acc
      | go acc (thm :: thms) = go (@{thm list_all_ConsI} OF [thm, acc]) thms
  in
    go thm (rev thms)
  end

fun check_prime_factors_subset 0 _ = false
  | check_prime_factors_subset n [] = n = 1
  | check_prime_factors_subset n (p :: ps) =
      if n mod p = 0 then
        check_prime_factors_subset (n div p) (p :: ps)
      else
        check_prime_factors_subset n ps

fun check_cert' (Pratt_Node (n, a, ts)) =
  let
    val ps = map get_cert_number ts
  in
    check_prime_factors_subset (n - 1) ps
    andalso forall (fn p => mod_exp a ((n - 1) div p) n <> 1) ps
    andalso mod_exp a (n - 1) n = 1
  end

fun check_cert (Pratt_Node (n, a, ts)) =
      check_cert' (Pratt_Node (n, a, ts)) andalso forall check_cert ts

fun replay_cert cache cert ctxt =
  let
    val mk_nat = HOLogic.mk_number @{typ "Nat.nat"}
    val mk_eq_thm = Thm.cterm_of ctxt #> Thm.reflexive

    fun aux (Pratt_Node (n, a, ts)) cache =
      case AList.lookup op= cache n of
        SOME thm => (thm, cache)
      | NONE =>
          let
            val _ = if check_cert' cert then () else raise INVALID_CERT cert
            val (prime_thms, cache) = fold_accum aux ts cache
            val (n', a') = apply2 mk_nat (n, a)
            val prime_thm = prove_list_all ctxt @{term "prime :: nat \<Rightarrow> bool"} prime_thms

            val thm =
              (@{thm lehmers_theorem'} OF [prime_thm, mk_eq_thm a', mk_eq_thm n'])
            fun mk_thm () =
              Goal.prove ctxt [] []
                (HOLogic.mk_Trueprop (@{term "prime :: nat \<Rightarrow> bool"} $ mk_nat n))
                (fn {context = ctxt, ...} =>
                   HEADGOAL (resolve_tac ctxt [thm])
                   THEN ALLGOALS (TRY o REPEAT_ALL_NEW
                     (resolve_tac ctxt @{thms list_all_ConsI list.pred_inject(1)}))
                   THEN PARALLEL_ALLGOALS (Simplifier.simp_tac ctxt))
          in
            case try mk_thm () of
              NONE => raise THM ("replay_cert", 0, [thm])
            | SOME thm => (thm, (n, thm) :: cache)
          end
  in
    aux cert cache
  end

fun prove_prime cache n ctxt =
  case mk_cert n of
    NONE => (NONE, cache)
  | SOME cert =>
      case replay_cert cache cert ctxt of
        (thm, cache) => (SOME thm, cache)

fun parse_cert input =
  let
    datatype token = Nat of int | Comma | Open_Brace | Close_Brace | Space
    val foo = Source.of_list (Symbol_Pos.explode (Input.source_content input))

    fun space_symbol (s, _) = Symbol.is_blank s andalso s <> "\n";
    val scan_space =
      Scan.many1 space_symbol @@@ Scan.optional (Symbol_Pos.$$$ "\n") [] ||
      Scan.many space_symbol @@@ Symbol_Pos.$$$ "\n";
    
    val tokenizer =
      Symbol_Pos.scan_nat >> (Nat o fst o Library.read_int o map fst) ||
      Symbol_Pos.$$$ "," >> K Comma ||
      Symbol_Pos.$$$ "{" >> K Open_Brace ||
      Symbol_Pos.$$$ "}" >> K Close_Brace ||
      scan_space >> K Space
    val nat = Scan.one (fn Nat _ => true | _ => false) >> (fn Nat n => n | _ => raise Match)
    val comma = Scan.one (fn Comma => true | _ => false) >> K ()
    val obr = Scan.one (fn Open_Brace => true | _ => false) >> K ()
    val cbr = Scan.one (fn Close_Brace => true | _ => false) >> K ()

    fun enum1 scan = scan ::: Scan.repeat (comma |-- scan);
    fun enum scan = enum1 scan || Scan.succeed [];
    fun list scan = obr |-- enum scan --| cbr

    fun parser s =
      ((obr |-- nat --| comma -- nat --| comma -- list parser --| cbr) >>
        (fn ((a,b),c) => Pratt_Node (a, b, c)) 
       || nat >> (fn a => Pratt_Node (a, 1, []))) s
    val tokens = Source.exhaust (Source.source Symbol_Pos.stopper (Scan.bulk tokenizer) foo)
    val tokens = filter (fn Space => false | _ => true) tokens
  in
    case parser tokens of
      (result, []) => result
    | _ => raise Match
  end

val cert_cartouche = Args.cartouche_input >> parse_cert


local
  val pretty_int = Pretty.str o Int.toString
in
fun pretty_cert (Pratt_Node (2, _, _)) = pretty_int 2
  | pretty_cert (Pratt_Node (n, a, ts)) =
      Pretty.list "{" "}"
        [pretty_int n, pretty_int a, Pretty.enum "," "{" "}" (map pretty_cert ts)]
end

fun tac print cache cert ctxt i =
  let
    fun print_cert cert =
      [Pretty.keyword1 "by", Pretty.brk 1, Pretty.str "(", Pretty.str "pratt ", 
        Pretty.blk (2, [Pretty.cartouche (pretty_cert cert)]), Pretty.str ")"]
      |> Pretty.blk o pair 4
      |> Pretty.string_of
      |> Active.sendback_markup_command
      |> prefix "To repeat this proof with a pre-computed certificate, use:\n"
      |> Output.information
    fun cert_err cert =
      let
        val _ =
          if print then
            Pretty.chunks [Pretty.str "Invalid Pratt certificate:",
              Pretty.indent 2 (pretty_cert cert)]
            |> Pretty.string_of
            |> warning
          else
            ()
      in
        no_tac
      end
    fun not_prime_err n =
      let
        val _ = if print then warning ("Not a prime number: " ^ Int.toString n) else ()
      in
        NONE
      end

    fun certify p =
      case cert of
        SOME cert => SOME cert
      | NONE =>         
        let
          val p' = p |> HOLogic.dest_Trueprop |> dest_comb |> snd |> HOLogic.dest_number |> snd
        in
          case mk_cert p' of
            SOME cert => let val _ = if print then print_cert cert else () in SOME cert end
          | NONE => not_prime_err p'
        end
  in
    Subgoal.FOCUS_PARAMS (fn {concl, ...} =>
      case certify (Thm.term_of concl) of
        NONE => no_tac
      | SOME cert =>
          HEADGOAL (resolve_tac ctxt [fst (replay_cert cache cert ctxt)])
            handle INVALID_CERT cert => cert_err cert
    ) ctxt i
  end

end
