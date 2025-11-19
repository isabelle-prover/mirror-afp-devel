(*  Title:      Zippy/zippy_enum_action_app_metadata_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ENUM_ACTION_APP_METADATA_MIXIN =
sig
  include ZIPPY_ACTION_APP_METADATA_MIXIN_BASE
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure Co : ZIPPY_COROUTINE_MIXIN_BASE
  sharing type Co.M.t = M.t

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zipper{i}\<close>\<close>
  (*depth-first postorder enumeration of promising zipper1 children*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val enum_df_post_promising_children{i} : (unit -> @{ParaT_args encl: "(" ")"} Co.ME.exn) ->
    (@{ParaT_args} @{AllT_args} zipper{i},
      (@{ParaT_args} unit, @{AllT_args} zipper1) Co.Co.coroutine) morph\<close> start: 2\<close>
end

functor Zippy_Enum_Action_App_Metadata_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure Meta : ZIPPY_ACTION_APP_METADATA_MIXIN
    sharing type Meta.L.container = Z.Z5.zipper
  ) : ZIPPY_ENUM_ACTION_APP_METADATA_MIXIN =
struct

open Z Meta
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Zippy_Exception_Mixin(Co)

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} zipper{i} = @{AllT_args} Z{i}.zipper\<close>\<close>

local open SC Mo A Co Exn
  fun gen_enum_promising_zippers mk_exn down enum_children enum_promising_child = down
    >>> (fn z => Co.repeat_step_res (arr fst)
      (fn (z, co) => AE.catch' (enum_promising_child mk_exn >>> arr (Co.append_co co #> Co.continue))
        (K (Co.continue co)) z)
      (enum_children mk_exn) (z, Co.throw (mk_exn ())))
    >>> arr (Co.dest_res #> snd)
in
fun \<^imap>\<open>\<open>{i}\<close> => \<open>
enum_df_post_promising_children{i} mk_exn = gen_enum_promising_zippers mk_exn Down{i}.morph
  DF_Post\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>enum_zipper
  enum_df_post_promising_children\<^eval>\<open>succ_mod_nzippers {i}\<close>\<close>
sep: "and" start: 2 stop: 4\<close>
and enum_df_post_promising_children5 mk_exn z = z |>
  (if Progress.getter z = Meta.P.promising
  then Down5.morph >>> arr (Co.enum_co (DF_Post1.enum_zipper mk_exn))
  else K (Co.throw (mk_exn ())))
end

end
