(*  Title:      Zippy/zippy_ztactic.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ZTACTIC =
sig
  include ZIPPY_ZTACTIC_RESULT
  structure RTac : ZIPPY_RTACTIC

  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close>
  where type (@{ParaT_args} 'a) t = 'a Seq.seq
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close>
  where type (@{ParaT_args} 'a) K.M.t = 'a Seq.seq

  type 'm ztactic = state -> 'm result Seq.seq (*equivalent to "(_, state, 'm result) A.cat"*)

  val no_ztac : 'm ztactic
  val all_ztac : 'm -> 'm ztactic

  val lift_rtac_single_goal : (int -> 'm RTac.rtactic) -> GPU.GCS.goal_pos -> 'm ztactic

  val gen_lift_tac_focus :
    ((GPU.GCS.goal_pos -> 'a -> 'b Seq.seq) -> GPU.GCS.goal_pos list -> 'a -> 'b Seq.seq) ->
    (GPU.GCS.goal_pos -> 'a -> 'b Seq.seq) -> GPU.F.focus -> 'a -> 'b Seq.seq

  val zTRY : 'm -> 'm ztactic -> 'm ztactic
  val zTRY' : 'm -> ('a -> 'm ztactic) -> ('a -> 'm ztactic)

  (*first parameter specifies how to combine the consecutive "more" data*)
  val depzTHEN : ('m * 'm -> 'm) -> 'm ztactic * ('m -> 'm ztactic) -> 'm ztactic
  val zTHEN : ('m * 'm -> 'm) -> 'm ztactic * 'm ztactic -> 'm ztactic

  val depzTHEN_ELSE : ('m * 'm -> 'm) -> 'm ztactic * ('m -> 'm ztactic) * 'm ztactic -> 'm ztactic
  val zTHEN_ELSE : ('m * 'm -> 'm) -> 'm ztactic * 'm ztactic * 'm ztactic -> 'm ztactic

  val zEVERY : 'm ztactic -> ('m * 'm -> 'm) -> 'm ztactic list -> 'm ztactic
  val zALL_GOALS : 'm ztactic -> ('m * 'm -> 'm) -> (GPU.GCS.goal_pos -> 'm ztactic) -> 'm ztactic
  val zEVERY_GOAL : 'm ztactic -> ('m * 'm -> 'm) -> (GPU.GCS.goal_pos -> 'm ztactic) ->
    GPU.GCS.goal_pos list -> 'm ztactic
  val zEVERY_FOCUS : 'm ztactic -> ('m * 'm -> 'm) -> (GPU.GCS.goal_pos -> 'm ztactic) ->
    GPU.F.focus -> 'm ztactic

  (*EVERY where each tactic may fail but at least one must succeed*)
  val zTRY_EVERY1 : ('m * 'm -> 'm) -> 'm ztactic list -> 'm ztactic
  val zTRY_ALL_GOALS1 : ('m * 'm -> 'm) -> (GPU.GCS.goal_pos -> 'm ztactic) -> 'm ztactic
  val zTRY_EVERY_GOAL1 : ('m * 'm -> 'm) -> (GPU.GCS.goal_pos -> 'm ztactic) ->
    GPU.GCS.goal_pos list -> 'm ztactic
  val zTRY_EVERY_FOCUS1 : ('m * 'm -> 'm) -> (GPU.GCS.goal_pos -> 'm ztactic) -> GPU.F.focus ->
    'm ztactic

  val zIFIRST_GOAL : ('a -> 'm ztactic) -> 'a list -> 'm ztactic
  val zFIRST_GOAL : (GPU.GCS.goal_pos -> 'm ztactic) -> 'm ztactic
  val zFIRST_GOAL_FOCUS : (GPU.GCS.goal_pos -> 'm ztactic) -> GPU.F.focus -> 'm ztactic

  (*like FIRST_GOAL but with backtracking to non-first applicable goals*)
  val zISOME_GOAL : ('a -> 'm ztactic) -> 'a list -> 'm ztactic
  val zSOME_GOAL : (GPU.GCS.goal_pos -> 'm ztactic) -> 'm ztactic
  val zSOME_GOAL_FOCUS : (GPU.GCS.goal_pos -> 'm ztactic) -> GPU.F.focus -> 'm ztactic
end

functor Zippy_ZTactic(
    structure R : ZIPPY_ZTACTIC_RESULT
    structure RTac : ZIPPY_RTACTIC
  ) : ZIPPY_ZTACTIC =
struct

open R
structure RTac = RTac

type 'm ztactic = state -> 'm result Seq.seq

structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(\<^eval>\<open>sfx_ParaT_nargs "Seq_Monad"\<close>)
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A); open M A SC GPU
  structure TU = Tactic_Util
in
fun no_ztac _ = Seq.empty
fun all_ztac m state = pure (result m state GPU.id)

fun lift_rtac_single_goal tac i state = tac i state
  >>= arr (fn {state = state', more} =>
    Zippy_Thm_State.nprems_of state' - Zippy_Thm_State.nprems_of state + 1
    |> single_goal_gpos_update i
    |> result more state')

fun gen_lift_tac_focus f_goals tac (F.Goals is) = f_goals tac is

fun zTRY m tac = TU.ORELSE (tac, all_ztac m)
fun zTRY' m tac = TU.ORELSE' (tac, Library.K (all_ztac m))

fun then_update madd tac {state, more, gpos_update} =
  let
    val update_ud = map_gpos_update (General_Util.flip GPU.comp gpos_update)
    val update_m = map_more (curry madd more)
  in tac more state >>= arr (update_ud #> update_m) end
fun depzTHEN madd (tac1, tac2) = tac1 >>> then_update madd tac2
fun zTHEN madd (tac1, tac2) = depzTHEN madd (tac1, Library.K tac2)

fun depzTHEN_ELSE madd (tac, tac_true, tac_false) state = case Seq.pull (tac state) of
    NONE => tac_false state
  | some => Seq.maps (then_update madd tac_true) (Seq.make (fn _ => some))
fun zTHEN_ELSE madd (tac1, tac2, tac3) = depzTHEN_ELSE madd (tac1, Library.K tac2, tac3)

fun gen_every_arg _ empty_tac _ [] = empty_tac
  | gen_every_arg comb _ tac (i :: is) = fold (fn i => fn acc => comb (acc, tac i)) is (tac i)

(*invariant: position list is sorted*)
fun with_rev_ngoals f tac st = f (List.map tac (Zippy_Thm_State.nprems_of st downto 1)) st
fun with_rev_goals f tac goals = fold (tac #> cons) goals [] |> f

fun zEVERY empty_tac madd = gen_every_arg (zTHEN madd) empty_tac I
fun zALL_GOALS no_goals_tac madd = with_rev_ngoals (zEVERY no_goals_tac madd)
fun zEVERY_GOAL empty_tac madd tac = with_rev_goals (zEVERY empty_tac madd) tac
fun zEVERY_FOCUS empty_tac madd = gen_lift_tac_focus (zEVERY_GOAL empty_tac madd)

fun zTRY_EVERY1 madd = gen_every_arg
  (fn (acc, tac) => TU.ORELSE (
    depzTHEN snd (acc, fn m => depzTHEN_ELSE snd (tac, pair m #> madd #> all_ztac, all_ztac m)),
    tac)) no_ztac I
fun zTRY_ALL_GOALS1 madd = with_rev_ngoals (zTRY_EVERY1 madd)
fun zTRY_EVERY_GOAL1 madd = with_rev_goals (zTRY_EVERY1 madd)
fun zTRY_EVERY_FOCUS1 madd = gen_lift_tac_focus (zTRY_EVERY_GOAL1 madd)

fun zIFIRST_GOAL tac = gen_every_arg TU.ORELSE no_ztac tac
fun zFIRST_GOAL tac st = zIFIRST_GOAL tac (1 upto Zippy_Thm_State.nprems_of st) st
fun zFIRST_GOAL_FOCUS x = gen_lift_tac_focus zIFIRST_GOAL x

fun zISOME_GOAL tac = gen_every_arg TU.APPEND no_ztac tac
fun zSOME_GOAL tac st = zISOME_GOAL tac (1 upto Zippy_Thm_State.nprems_of st) st
fun zSOME_GOAL_FOCUS x = gen_lift_tac_focus zISOME_GOAL x
end
end

structure Standard_Zippy_ZTactic = Zippy_ZTactic(
  structure R = Standard_Zippy_ZTactic_Result; structure RTac = Standard_Zippy_RTactic)
