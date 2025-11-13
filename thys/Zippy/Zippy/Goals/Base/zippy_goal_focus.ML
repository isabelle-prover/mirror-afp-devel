(*  Title:      Zippy/zippy_goal_focus.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_FOCUS =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS
  datatype focus = Goals of GCS.goal_pos list
  val goals : GCS.goal_pos list -> focus
  val sort_goals : GCS.goal_pos list -> focus
  val all_upto : int -> focus
  val single : GCS.goal_pos -> focus
  val pretty : focus SpecCheck_Show.show

  val focused_data : focus -> 'a list -> (GCS.goal_pos * 'a) list
end

functor Zippy_Goal_Focus(GCS : ZIPPY_GOAL_CLUSTERS) : ZIPPY_GOAL_FOCUS =
struct
structure Show = SpecCheck_Show_Base

structure GCS = GCS

datatype focus = Goals of GCS.goal_pos list

val goals = Goals
val sort_goals = sort int_ord #> Goals
fun all_upto n = goals (1 upto n)
fun single x = Goals [x]
fun pretty (Goals xs) = Pretty.block [Pretty.str "Goals ", Pretty.block [Show.list Show.int xs]]

fun get_indices _ [] _ = []
  | get_indices i (j :: js) (x :: xs) = if i = j
      then (i, x) :: get_indices (i + 1) js xs
      else get_indices (i + 1) (j :: js) xs
  | get_indices i js xs = error (Pretty.breaks [
        Pretty.block [Pretty.str "Bad remaining arguments for get_indices."],
        Pretty.block [Pretty.str "Counter: ", SpecCheck_Show.int i],
        Pretty.block [Pretty.str "Indices: ", SpecCheck_Show.list SpecCheck_Show.int js],
        Pretty.block [Pretty.str "Remaining data: ", SpecCheck_Show.int (length xs)]
      ] |> Pretty.block |> Pretty.string_of)

fun focused_data (Goals gposs) = get_indices 1 gposs
end

structure Standard_Zippy_Goal_Focus = Zippy_Goal_Focus(Standard_Zippy_Goal_Clusters)