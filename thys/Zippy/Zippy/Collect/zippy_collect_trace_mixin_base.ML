(*  Title:      Zippy/ZIPPY_COLLECT_TRACE_MIXIN_BASE.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COLLECT_TRACE_MIXIN_BASE =
sig
  include ZIPPY_BASE_BASE
  type @{AllT_args} data
  type @{AllT_args} trace = (@{AllT_args} data * @{AllT_args} data list) option

  structure SZCollect : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_DEP_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} trace
  where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} trace
  where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} trace
  where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = unit\<close>\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZCollect.SZ{i}.Zipper.container = Z{i}.zipper
  sharing type SZCollect.SZ{i}.Container.container = Z{i}.ZM.container
  sharing type SZCollect.SZ{i}.Content.container = Z{i}.ZD.content
  sharing type SZCollect.SZ{i}.ZCtxt.container = Z{i}.ZD.zcontext\<close>\<close>
  sharing type SZCollect.ZSub.M.t = M.t
end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Zippy_Collect_Trace_Mixin_Base{j}(A :
  sig
    structure Z : ZIPPY_BASE_BASE
    type @{AllT_args} data
    val update : @{AllT_args} Z.Z{j}.zipper -> (@{AllT_args} data * @{AllT_args} data list) option ->
      @{AllT_args} data
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
  end) :
  sig
    include ZIPPY_COLLECT_TRACE_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} A.Z.Z{i}.ZM.container *
      (@{AllT_args} A.data * @{AllT_args} A.data list) option
    where type @{AllT_args} Z{i}.zipper = @{AllT_args} A.Z.Z{i}.zipper *
      (@{AllT_args} A.data * @{AllT_args} A.data list) option
    where type @{AllT_args} Z{i}.ZD.content = @{AllT_args} A.Z.Z{i}.ZD.content *
      (@{AllT_args} A.data * @{AllT_args} A.data list) option
    where type @{AllT_args} Z{i}.ZD.zcontext = @{AllT_args} A.Z.Z{i}.ZD.zcontext * unit
    \<close>\<close>
    structure SZ : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZSub.Z{i}.ZM.container = @{AllT_args} A.Z.Z{i}.ZM.container
    where type @{AllT_args} ZSub.Z{i}.zipper = @{AllT_args} A.Z.Z{i}.zipper
    where type @{AllT_args} ZSub.Z{i}.ZD.content = @{AllT_args} A.Z.Z{i}.ZD.content
    where type @{AllT_args} ZSub.Z{i}.ZD.zcontext = @{AllT_args} A.Z.Z{i}.ZD.zcontext
    where type @{AllT_args} SZ{i}.Container.container = @{AllT_args} Z{i}.ZM.container
    where type @{AllT_args} SZ{i}.Zipper.container = @{AllT_args} Z{i}.zipper
    where type @{AllT_args} SZ{i}.Content.container = @{AllT_args} Z{i}.ZD.content
    where type @{AllT_args} SZ{i}.ZCtxt.container = @{AllT_args} Z{i}.ZD.zcontext\<close>\<close>
    sharing type SZ.ZSub.M.t = M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val container{i} : @{AllT_args} trace -> @{AllT_args} A.Z.Z{i}.ZM.container ->
      @{AllT_args} Z{i}.ZM.container
    val init_container{i} : @{AllT_args} A.Z.Z{i}.ZM.container -> @{AllT_args} Z{i}.ZM.container\<close>\<close>
  end
  =
struct
open A
type @{AllT_args} data = @{AllT_args} data
type @{AllT_args} trace = (@{AllT_args} data * @{AllT_args} data list) option

structure MB : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = Z

structure ZD = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Data"\<close>(
  type @{AllT_args} content = @{AllT_args} trace)
local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z.K); open SC Z.K Z.M
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Base{i} =
struct
  structure M = MB
  type @{AllT_args} dep_zip = @{AllT_args} Z.Z{i}.ZM.container * @{AllT_args} Z.Z{i}.zipper
  type @{AllT_args} dep_unzip = @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z{i}.ZM.container
  type @{AllT_args} dep_up = @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z{i}.zipper
  type @{AllT_args} dep_down = @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z{i}.zipper
  type @{AllT_args} dep_left = @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z{i}.zipper
  type @{AllT_args} dep_right = @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z{i}.zipper
  type @{AllT_args} container = @{AllT_args} ZD.zipper
  type @{AllT_args} zipper = @{AllT_args} ZD.zipper
  fun move _ = id ()
  val zip = move
  val unzip = move
  val up = move
  val down = move
  val left = move
  val right = move
end
structure DZM{i} = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs"\<close>(open Base{i})\<close>\<close>
fun pop trace = Option.mapPartial (snd #> List.getItem) trace
fun push z trace = let val data = update z trace
  in Option.map (op ::) trace |> the_default [] |> pair data |> SOME end
structure DZM{j} = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Morphs"\<close>(open Base{j}
  fun zip (_, z) = arr (push z)
  fun unzip _ = arr pop
  fun update (_, z) = arr (pop #> push z)
  val up = update
  val down = update
  val left = update
  val right = update)
structure ZCollect = \<^eval>\<open>pfx_sfx_nargs "Alternating_Dep_Zipper"\<close>(
  structure Z =
  struct
    open MB
    \<^imap>\<open>\<open>{i}\<close> => \<open>structure Z{i} = DZM{i}\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Base{i} =
    struct open MB; type @{AllT_args} from = @{AllT_args} Z{i}.zipper; fun morph _ = id () end
    structure Down{i} =
    struct open Base{i}
      type @{AllT_args} dep =
        @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
      type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
    end
    structure Up{i} =
    struct open Base{i}
      type @{AllT_args} dep =
        @{AllT_args} Z.Z{i}.zipper * @{AllT_args} Z.Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
      type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
    end\<close>\<close>
    structure Down\<^eval>\<open>pred_mod_nzippers {j}\<close> =
    struct open Down\<^eval>\<open>pred_mod_nzippers {j}\<close>; fun morph (_, z) = arr (push z) end
    structure Up{j} = struct open Up{j}; fun morph _ = arr pop end
  end
  \<^imap>\<open>\<open>{i}\<close> => \<open>structure ZD{i} = ZD\<close>\<close>)
end

structure Z = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper_Alternating_Dep_Zipper"]\<close>(
  structure AZ1 = Z; structure AZ2 = ZCollect)
structure ZB = Zippy_Base_Base(\<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Util"\<close>(
  structure Z = Z
  structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Repeat"\<close>(Exn.AE)))
open ZB

structure SZ = Z.SZ1
structure SZCollect = Z.SZ2

fun container cs c = (c, cs)
fun init_container c = container NONE c
\<^imap>\<open>\<open>{i}\<close> => \<open>
val container{i} = container
val init_container{i} = init_container\<close>\<close>

end\<close>\<close>
