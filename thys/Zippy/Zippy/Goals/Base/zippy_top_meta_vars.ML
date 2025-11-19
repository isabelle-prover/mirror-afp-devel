(*  Title:      Zippy/zippy_top_meta_vars.ML
    Author:     Kevin Kappelmann

Meta variables shared with top-level goal.
*)
signature ZIPPY_TOP_META_VARS =
sig
  type top_meta_vars = Vars.set
  val pretty : Proof.context -> top_meta_vars SpecCheck_Show.show
  (*initialise a state's top-level meta variables given its parent's top-level meta variables*)
  val init : top_meta_vars -> Zippy_Thm_State.state -> top_meta_vars
  val is_empty : top_meta_vars -> bool
end

structure Zippy_Top_Meta_Vars : ZIPPY_TOP_META_VARS =
struct

structure Show = SpecCheck_Show

type top_meta_vars = Vars.set
fun pretty ctxt = Vars.list_set #> Show.list (Var #> Show.term ctxt)
fun init parent_top_meta_vars state =
  if Vars.is_empty parent_top_meta_vars orelse not (Zippy_Thm_State.has_meta_vars state)
  then Vars.empty
  else
    let
      val state_meta_vars = Zippy_Thm_State.meta_vars state
      fun remove_if_not_in_state_meta_vars k = not (Vars.defined state_meta_vars k) ? Vars.remove k
    in
      Vars.fold (fst #> remove_if_not_in_state_meta_vars) parent_top_meta_vars parent_top_meta_vars
    end
val is_empty = Vars.is_empty

end
