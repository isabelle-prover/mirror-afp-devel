(*  Title:      Zippy/zippy_goal_results_top_meta_vars_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_RESULTS_TOP_META_VARS_MIXIN =
sig
  include ZIPPY_GOAL_RESULTS_TOP_META_VARS_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure Path : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_PATH"\<close>

  val may_take_more_results : @{AllT_args} Results.L.container -> bool

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zipper{i}
  val move_path_if_may_take_more_results{i} : Path.path{i} ->
    (@{ParaT_args} @{AllT_args} zipper1, @{AllT_args} zipper{i} option) morph\<close>\<close>
end

functor Zippy_Goal_Results_Top_Meta_Vars_Mixin(
    structure Z : ZIPPY_BASE_BASE
    structure Goal_Results_Top_Meta_Vars : ZIPPY_GOAL_RESULTS_TOP_META_VARS_MIXIN_BASE
    sharing type Goal_Results_Top_Meta_Vars.Results.L.container = Z.Z2.zipper
  ) : ZIPPY_GOAL_RESULTS_TOP_META_VARS_MIXIN =
struct

open Z Goal_Results_Top_Meta_Vars
structure MU = Zippy_Monad_Util(M); open MU

structure Results = Zippy_Goal_Results_Mixin(Goal_Results_Top_Meta_Vars.Results)
structure Top_Meta_Vars = Zippy_Top_Meta_Vars_Mixin(Goal_Results_Top_Meta_Vars.Top_Meta_Vars)
structure PosU = \<^eval>\<open>sfx_ParaT_nargs "Zipper_Position_Util"\<close>(M)
structure Path = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Path_Util"\<close>(Z)

fun may_take_more_results z = not (Results.has_results z) orelse not (Top_Meta_Vars.is_empty z)

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} zipper{i} = @{AllT_args} Z{i}.zipper\<close>\<close>

local open SC
in
fun move_path_if_may_take_more_results1 (Path.Pos pos) =
    PosU.move_pos Z1.ZM.Left.morph Z1.ZM.Right.morph Z1.ZM.Down.morph pos >>> K.arr SOME
  | move_path_if_may_take_more_results1 (Path.Path1 (pos, p)) =
    \<^eval>\<open>"move_path_if_may_take_more_results" ^ pred_mod_nzippers 1\<close> p
    >>> AC.opt (A.K NONE) (\<^eval>\<open>"Down" ^ pred_mod_nzippers 1 ^ ".morph"\<close>
      >>> move_path_if_may_take_more_results1 (Path.Pos pos))
and move_path_if_may_take_more_results2 (Path.Path2 (pos, p)) =
  move_path_if_may_take_more_results1 p
  >>> AC.opt (A.K NONE) (Down1.morph
    >>> PosU.move_pos Z2.ZM.Left.morph Z2.ZM.Right.morph Z2.ZM.Down.morph pos
    >>> K.arr (Option.filter may_take_more_results))
\<^imap>\<open>\<open>{i}\<close> => \<open>
and move_path_if_may_take_more_results{i} (Path.Path{i} (pos, p)) =
  move_path_if_may_take_more_results\<^eval>\<open>pred_mod_nzippers {i}\<close> p
  >>> AC.opt (A.K NONE) (Down\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>morph
    >>> PosU.move_pos Z{i}.ZM.Left.morph Z{i}.ZM.Right.morph Z{i}.ZM.Down.morph pos >>> K.arr SOME)
\<close> start: 3\<close>
end

end
