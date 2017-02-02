signature BERTRAND = 
sig

type cache = (int * thm) list
datatype primepow_thm = PrimepowThm of thm * thm | NotPrimepowThm of thm

val prime_conv : Proof.context -> cache -> conv
val primepow_conv : Proof.context -> cache -> conv
val pre_mangoldt_conv : Proof.context -> cache -> conv

val prove_prime : Proof.context -> cache -> term -> thm
val prove_primepow : Proof.context -> cache -> term -> primepow_thm
val prove_pre_mangoldt : Proof.context -> cache -> term -> thm
val prove_psi : Proof.context -> int -> (int * int * thm) list

val mk_prime_cache : Proof.context -> int -> cache

end

structure Bertrand : BERTRAND = 
struct

type cache = (int * thm) list

datatype primepow_cert = Primepow of int * int | NotPrimepow of int * int
datatype primepow_thm = PrimepowThm of thm * thm | NotPrimepowThm of thm

fun get_cached_prime_thm cache p = AList.lookup op = cache p

val mk_nat = HOLogic.mk_number @{typ nat}

fun mk_primepow_cert n =
  let
    fun find_prime_divisor n =
      let fun go k = if n mod k = 0 then k else go (k + 1) in go 2 end
    fun divide_out p m acc =
      if m mod p = 0 then divide_out p (m div p) (acc + 1) else (acc, m)
    val p = find_prime_divisor n
    val (k, m) = divide_out p n 0
  in
    if m = 1 then Primepow (p, k) else NotPrimepow (p, find_prime_divisor m)
  end

val prime_eval_conv =
  Code_Runtime.static_holds_conv {consts = [@{const_name prime_nat_consts}], ctxt = @{context}}

fun prove_prime ctxt cache p =
  case get_cached_prime_thm cache (snd (HOLogic.dest_number p)) of
    SOME thm => thm
  | NONE =>
      @{term "prime :: nat \<Rightarrow> bool"} $ p
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of ctxt
      |> prime_eval_conv ctxt

fun bool_thm_to_eq_thm thm =
  case HOLogic.dest_Trueprop (Thm.concl_of thm) of
    @{term "HOL.Not"} $ _ => thm RS @{thm Eq_FalseI}
  | _ => thm RS @{thm Eq_TrueI}

fun prime_conv ctxt cache = bool_thm_to_eq_thm o prove_prime ctxt cache o Thm.term_of

fun prime_sieve n =
let
  fun go ps k =
    if k > n then
      rev ps
    else
      if exists (fn p => k mod p = 0) ps then
        go ps (k + 1)
      else
        go (k :: ps) (k + 1)
in
  go [] 2
end

fun mk_prime_cache ctxt n =
  let
    val ps = prime_sieve n
    val t = ps |> map mk_nat |> HOLogic.mk_set @{typ nat}
    val prop = betapply (@{term "\<lambda>A. \<forall>p\<in>A. prime (p :: nat)"}, t)
      |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt
    val thm = prime_eval_conv ctxt prop
    fun deconstruct_thm thm acc =
      case Thm.concl_of thm of
        Const (@{const_name HOL.Trueprop}, _) $
          (Const (@{const_name Set.Ball}, _) $ (Const (@{const_name Set.insert}, _) $ n $ _) $ _)
        => deconstruct_thm (thm RS @{thm Ball_insertD(2)})
             ((snd (HOLogic.dest_number n), thm RS @{thm Ball_insertD(1)}) :: acc)
      | _ => rev acc
  in
    deconstruct_thm (thm RS @{thm meta_eq_TrueE}) []
  end

fun prove_primepow ctxt cache t =
  let
    val (_, n) = HOLogic.dest_number t
    fun inst xs = Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt o mk_nat) xs)
    val prove_prime' = prove_prime ctxt cache o mk_nat
    val prove = Goal.prove ctxt [] []
  in
    if n <= 0 then
      raise TERM ("prove_primepow", [t])
    else if n = 1 then
      NotPrimepowThm @{thm not_primepow_1}
    else
      case mk_primepow_cert n of
        Primepow (p, k) =>
          let
            val thm = prove_prime' p RS inst [p, k, n] @{thm primepowI}
            val thm' = prove (Thm.concl_of thm) (fn {context = ctxt, ...} =>
              HEADGOAL (resolve_tac ctxt [thm]) THEN ALLGOALS (Simplifier.simp_tac ctxt))
          in
            PrimepowThm (thm' RS @{thm conjunct1}, thm' RS @{thm conjunct2})
          end
      | NotPrimepow (p, q) =>
          let
            val thm = inst [p, q, n] @{thm not_primepowI} OF (map prove_prime' [p, q])
            val thm' = prove (Thm.concl_of thm) (fn {context = ctxt, ...} =>
              HEADGOAL (resolve_tac ctxt [thm]) THEN ALLGOALS (Simplifier.simp_tac ctxt))
          in
            NotPrimepowThm thm'
          end
  end

fun primepow_conv ctxt cache ct = 
  case prove_primepow ctxt cache (Thm.term_of ct) of
    PrimepowThm (thm, _) => bool_thm_to_eq_thm thm
  | NotPrimepowThm thm => bool_thm_to_eq_thm thm

fun prove_pre_mangoldt ctxt cache t =
  case prove_primepow ctxt cache t of
    PrimepowThm (thm1, thm2) => @{thm pre_mangoldt_primepow} OF [thm1, thm2]
  | NotPrimepowThm thm => thm RS @{thm pre_mangoldt_notprimepow}

fun pre_mangoldt_conv ctxt cache = 
  (fn thm => thm RS @{thm eq_reflection}) o prove_pre_mangoldt ctxt cache o Thm.term_of

val nat_eq_ss =
  simpset_of (put_simpset HOL_basic_ss @{context} addsimps @{thms Numeral_Simprocs.semiring_norm})

fun prove_nat_eq ctxt (t1, t2) =
  let
    val goal = HOLogic.mk_eq (t1, t2) |> HOLogic.mk_Trueprop
    fun tac {context = ctxt, ...} =
      HEADGOAL (resolve_tac ctxt @{thms mult_1_left mult_1_right})
      ORELSE HEADGOAL (Simplifier.simp_tac (put_simpset nat_eq_ss ctxt))
  in
    Goal.prove ctxt [] [] goal tac
  end

fun prove_psi ctxt n =
  let
    val cache = mk_prime_cache ctxt n
    fun go thm x x' k acc =
      if k > n then
        rev acc
      else
        let
          val pre_mangoldt_thm = prove_pre_mangoldt ctxt cache (mk_nat k)
          val y = pre_mangoldt_thm
            |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
          val y' = HOLogic.dest_number y |> snd
          val eq_thm1 = prove_nat_eq ctxt
            (@{term "op + :: nat \<Rightarrow> _"} $ mk_nat (k - 1) $ @{term "1 :: nat"}, mk_nat k)
          val z = if y' = 1 then x else mk_nat (x' * y')
          val eq_thm2 = prove_nat_eq ctxt
            (@{term "op * :: nat => _"} $ x $ y, z)
          val thm' = @{thm eval_psi_aux2} OF [thm, pre_mangoldt_thm, eq_thm1, eq_thm2]
        in
          go thm' z (x' * y') (k + 1) ((k - 1, x', thm) :: acc)
        end
  in
    go @{thm eval_psi_aux1} @{term "numeral Num.One :: nat"} 1 1 []
  end

end