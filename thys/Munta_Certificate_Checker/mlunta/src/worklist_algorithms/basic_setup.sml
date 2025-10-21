signature PASSED_SET = MONO_PASSED_SET where type Key.key = Location.key

signature CHECKING_SETUP = sig
(*structure D : DBM*)
structure D : DBM
structure Passed : PASSED_SET
                       where type Zone.zone = D.zone
end

signature SETUP = sig
  structure D : DBM
  type setup
  val initial_state: (Network.location -> (D.t -> D.t)) ->
               D.t Network.state -> D.t Network.state
  val approx: (int Array.array -> D.t -> D.t list) ->
                 D.t Network.state -> D.t Network.state list
  val initial_setup: D.t Network.system -> setup
  val P: setup -> D.t Network.state -> bool
  val initial: setup -> D.t Network.state
  val norm: setup -> D.t Network.state -> D.t Network.state list
end

functor BasicSetup(D : DBM) : SETUP = struct
structure D = D
type setup = {
    initial : D.t Network.state,
    P : D.t Network.state -> bool,
    norm : D.t Network.state -> D.t Network.state list
}
fun get_formula F =
    fst #> Formula.the_formula F

fun initial_state invars_at (l, D) =
    let val invars = invars_at l in
      (l, D |> invars |> D.up |> invars)
    end

fun approx norm_k_G =
    fn (l, D) => map (pair l) (norm_k_G (fst l) D)

fun initial_setup (system : D.t Network.system) =
    let
        val P = get_formula (#formula system)
        val norm_k_G = #norm_k_G system
        val initial = #initial system
        val normalize = approx norm_k_G
    in
        {
          initial = initial,
          P = P,
          norm = normalize
        }
    end
fun P ({P, ...} : setup)  = P
fun initial ({initial, ...} : setup) = initial
fun norm ({norm, ...} : setup) = norm
end

signature LEADSTO_SETUP = sig
  include SETUP
  val Q: setup -> D.t Network.state -> bool
end

functor LeadstoSetup(D : DBM) : LEADSTO_SETUP = struct
structure D = D
type setup = {
    initial : D.t Network.state,
    Q : D.t Network.state -> bool,
    P : D.t Network.state -> bool,
    norm : D.t Network.state -> D.t Network.state list
}

fun get_formula F =
    let
      val (P, Q) =  Formula.p_q F
    in
      (fst #> P, fst #> Q)
    end

fun initial_state invar_at (l, D) =
    (l, D |> D.up |> invar_at l)

fun approx norm_k_G =
    fn (l, D) => map (pair l) (norm_k_G (fst l) D)

fun initial_setup (system : D.t Network.system) =
    let
        val (P, Q) = get_formula (#formula system)
        val norm_k_G = #norm_k_G system
        val initial = #initial system
        val normalize = approx norm_k_G
    in
        ({
          initial = initial,
          P = P,
          Q = Q,
          norm = normalize
        } : setup)
    end

fun P ({P, ...} : setup)  = P
fun Q ({Q, ...} : setup)  = Q
fun initial ({initial, ...} : setup) = initial
fun norm ({norm, ...} : setup) = norm
end
