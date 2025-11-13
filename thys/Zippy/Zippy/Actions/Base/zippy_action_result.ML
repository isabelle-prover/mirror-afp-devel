(*  Title:      Zippy/zippy_action_result.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_RESULT =
sig
  datatype ('u, 'e, 'c) result = Unchanged of 'u (*stay at node without structural changes*)
    | Expanded of 'e (*expand node without changing existing node paths*)
    | Changed of 'c (*other structural or relevant content changes*)
  val merge : ('u -> 'a) -> ('e -> 'a) -> ('c -> 'a) -> ('u, 'e, 'c) result -> 'a
end

structure Zippy_Action_Result : ZIPPY_ACTION_RESULT =
struct
datatype ('u, 'e, 'c) result = Unchanged of 'u | Expanded of 'e | Changed of 'c
fun merge f _ _ (Unchanged s) = f s
  | merge _ f _ (Expanded e) = f e
  | merge _ _ f (Changed t) = f t
end
