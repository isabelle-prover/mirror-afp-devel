(*  Title:      Zippy/zippy_paction_queue_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_QUEUE_MIXIN_BASE =
sig
  structure PAction : ZIPPY_PACTION_MIXIN
  structure Queue : PRIORITY_QUEUE

  type @{AllT_args} entry = {prio : PAction.prio,
    action : @{AllT_args} PAction.action,
    zipper : @{AllT_args} PAction.zipper}
  type @{AllT_args} queue = @{AllT_args} entry Queue.t
end

functor Zippy_PAction_Queue_Mixin_Base(A :
  sig
    structure PAction : ZIPPY_PACTION_MIXIN
    structure Queue : PRIORITY_QUEUE
  end
  ) : ZIPPY_PACTION_QUEUE_MIXIN_BASE
  =
struct
open A

type @{AllT_args} entry = {prio : PAction.prio,
  action : @{AllT_args} PAction.action,
  zipper : @{AllT_args} PAction.zipper}
type @{AllT_args} queue = @{AllT_args} entry Queue.t
end
