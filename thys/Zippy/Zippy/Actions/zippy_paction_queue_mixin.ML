(*  Title:      Zippy/zippy_paction_queue_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PACTION_QUEUE_MIXIN =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  include ZIPPY_PACTION_QUEUE_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  sharing type M.t = PAction.M.t
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  val mk_entry : (@{ParaT_args} @{AllT_args} PAction.zipper, @{AllT_args} entry) morph
  val run_entry : @{AllT_args} entry -> (@{ParaT_args} @{AllT_args} PAction.zipper,
    @{AllT_args} PAction.action_result) morph

  val fold_pactions :
    (*update result*)
    (@{ParaT_args} @{AllT_args} entry * 'r, 'r Co.Co.res) morph ->
    (*initialise result*)
    (@{ParaT_args} @{AllT_args} PAction.zipper, 'r Co.Co.res) morph ->
    (*zipper enumeration*)
    (@{ParaT_args} @{AllT_args} PAction.zipper, @{AllT_args} PAction.zipper) Co.Co.coroutine ->
    (*zipper to start the enumeration*)
    (@{ParaT_args} @{AllT_args} PAction.zipper, (@{AllT_args} PAction.zipper * 'r) Co.Co.res) morph

  val insert : Queue.prio * @{AllT_args} entry -> (@{ParaT_args} @{AllT_args} queue) emorph
  val mk_entry_insert : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    @{AllT_args} PAction.zipper -> (@{ParaT_args} @{AllT_args} queue) emorph

  val insert_pactions_queue : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    (@{ParaT_args} @{AllT_args} PAction.zipper, @{AllT_args} PAction.zipper) Co.Co.coroutine ->
    @{AllT_args} PAction.zipper -> (@{ParaT_args} @{AllT_args} queue) emorph

  type @{AllT_args} container1
  val insert_descendant_pactions_queue : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    @{AllT_args} container1 -> (@{ParaT_args} @{AllT_args} queue) emorph
  val init_pactions_queue : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    (@{ParaT_args} @{AllT_args} container1, @{AllT_args} queue) morph

  val update_unchanged : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    @{AllT_args} PAction.zipper -> (@{ParaT_args} @{AllT_args} queue) emorph
  val update_expanded : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    (@{AllT_args} PAction.zipper_expanded -> (@{ParaT_args} @{AllT_args} queue) emorph) ->
    @{AllT_args} PAction.zipper_expanded -> (@{ParaT_args} @{AllT_args} queue) emorph
  val update_changed : (@{ParaT_args} @{AllT_args} entry, Queue.prio) morph ->
    @{AllT_args} PAction.zipper_changed -> (@{ParaT_args} @{AllT_args} queue) emorph
end

functor Zippy_PAction_Queue_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure PAction_Queue : ZIPPY_PACTION_QUEUE_MIXIN_BASE
    sharing type PAction_Queue.PAction.zipper_changed = Z.Z1.zipper
    sharing type PAction_Queue.PAction.zipper = Z.Z4.zipper
    sharing type PAction_Queue.PAction.zipper_expanded = Z.Z5.zipper
    sharing type PAction_Queue.PAction.M.t = Z.M.t
    val mk_exn : (unit -> @{ParaT_args encl: "(" ")"} Z.Co.ME.exn)
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t =Z.M.t
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure Show_Container1 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show_Container1.t = Z.Z1.ZM.container
    structure Show4 : ZIPPY_SHOW_MIXIN_BASE
    sharing type Show4.t = Z.Z4.zipper
    structure Show_Queue_Entry : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = @{AllT_args} PAction_Queue.entry
    structure Show_Prio : ZIPPY_SHOW_MIXIN_BASE
    where type @{AllT_args} t = PAction_Queue.Queue.prio
  ) : ZIPPY_PACTION_QUEUE_MIXIN =
struct

open Z PAction_Queue Log
structure MU = Zippy_Monad_Util(PAction.M); open MU

local open SC Mo A Co PAction.Exn
in
fun mk_entry zipper = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Creating entry for",
      Show4.pretty ctxt zipper
    ] |> Pretty.block |> Pretty.string_of);
  PAction.get_run_paction zipper))
  >>= arr (fn (prio, action) => {prio = prio, action = action, zipper = zipper})
fun run_entry entry = PAction.run_action (#prio entry, #action entry)

fun fold_pactions update = Co.repeat_step_res_init (arr fst)
  (AE.catch' (first mk_entry >>> update) (arr (snd #> Co.continue))) (AE.id ())

fun insert (prio, entry) = Ctxt.with_ctxt (fn ctxt => arr (fn queue =>
  (@{log Logger.TRACE} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Inserting entry",
      Show_Queue_Entry.pretty ctxt entry,
      Pretty.block [Pretty.str "with priority ", Show_Prio.pretty ctxt prio],
      Pretty.str "to queue."
    ] |> Pretty.block |> Pretty.string_of);
  Queue.insert (prio, entry) queue)))

fun mk_entry_insert mk_prio z queue =
  mk_entry z >>= (fn entry => mk_prio entry >>= (fn prio => insert (prio, entry) queue))

fun insert_pactions_queue mk_prio co z = AE.try (fn queue =>
  fold_pactions
    (fn (entry, queue) => mk_prio entry >>= (fn prio => insert (prio, entry) queue >>= arr Co.continue))
    (fn z => mk_entry_insert mk_prio z queue >>= arr Co.continue) co z
  >>= arr (Co.dest_res #> snd))

type @{AllT_args} container1 = @{AllT_args} Z1.ZM.container
(*FIXME: could be made more efficient: only add pactions of goals that may take more results*)
fun insert_descendant_pactions_queue mk_prio c queue = Ctxt.get_ctxt () >>= (fn ctxt =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Inserting descendant pactions of",
      Show_Container1.pretty ctxt c,
      Pretty.str "to queue."
    ] |> Pretty.block |> Pretty.string_of);
  AE.catch'
    (Z1.ZM.Zip.morph >>> ADF_Post4.enum_zipper3 mk_exn
      >>> (fn (z, co) => insert_pactions_queue mk_prio (Co.cons (id ()) co) z queue))
    (A.K queue) c))
fun init_pactions_queue mk_prio c = insert_descendant_pactions_queue mk_prio c Queue.empty

local fun mk_entry_insert_safe mk_prio z = AE.try (mk_entry_insert mk_prio z)
in
fun update_unchanged mk_prio z = Ctxt.with_ctxt (fn ctxt => fn queue =>
  (@{log Logger.DEBUG} ctxt (fn _ => Pretty.breaks [
      Pretty.str "Inserting paction of unchanged action's zipper",
      Show4.pretty ctxt z,
      Pretty.str "to queue."
    ] |> Pretty.block |> Pretty.string_of);
  mk_entry_insert_safe mk_prio z queue))
fun update_expanded mk_prio insert_descendant_pactions_queue z = insert_descendant_pactions_queue z
  >>> (fn queue => Z.Up5.morph z >>= (fn z => mk_entry_insert_safe mk_prio z queue))
end
(*paths of entries in the queue might have changed; we hence re-initialise the queue*)
fun update_changed mk_prio z _ = Z1.ZM.Unzip.morph z >>= init_pactions_queue mk_prio
end

end
