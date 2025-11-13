(*  Title:      Zippy/extend_zipper_context.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "EXTEND_ZIPPER_CONTEXT"\<close> =
sig
  structure Zbase : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  type @{AllT_args} new_zcontext

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} Zbase.ZM.container * @{AllT_args} new_zcontext
  sharing type ZD.content = Zbase.ZD.content
  sharing type M.t = Zbase.M.t

  val mk_zcontext : @{AllT_args} Zbase.ZD.zcontext * @{AllT_args} new_zcontext ->
    @{AllT_args} ZD.zcontext

  val get_base_zcontext : @{AllT_args} ZD.zcontext -> @{AllT_args} Zbase.ZD.zcontext
  val get_new_zcontext : @{AllT_args} ZD.zcontext -> @{AllT_args} new_zcontext

  val zipper_from_base_zipper : @{AllT_args} Zbase.zipper * @{AllT_args} new_zcontext ->
    @{AllT_args} zipper
  val base_zipper_from_zipper : @{AllT_args} zipper -> @{AllT_args} Zbase.zipper
end

functor \<^eval>\<open>sfx_T_nargs "Extend_Zipper_Context"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD.content = Z.ZD.content
    type @{AllT_args} new_zcontext
    val mk_zcontext : @{AllT_args} Z.ZD.zcontext * @{AllT_args} new_zcontext ->
      @{AllT_args} ZD.zcontext
    val get_base_zcontext : @{AllT_args} ZD.zcontext -> @{AllT_args} Z.ZD.zcontext
    val get_new_zcontext : @{AllT_args} ZD.zcontext -> @{AllT_args} new_zcontext
  ) :
    \<^eval>\<open>sfx_T_nargs "EXTEND_ZIPPER_CONTEXT"\<close>
    where type @{AllT_args} zipper = @{AllT_args} ZD.zipper
  =
struct

structure Zbase = Z
type @{AllT_args} new_zcontext = @{AllT_args} new_zcontext
val mk_zcontext = mk_zcontext
val get_base_zcontext = get_base_zcontext
val get_new_zcontext = get_new_zcontext

fun zipper_from_base_zipper (x, new_zctxt) =
  let
    val content = Z.ZD.Co.getter x
    val base_zctxt = Z.ZD.ZCtxt.getter x
  in ZD.zipper (content, mk_zcontext (base_zctxt, new_zctxt)) end

fun base_zipper_from_zipper x =
  Z.ZD.zipper (ZD.Co.getter x, ZD.ZCtxt.getter x |> get_base_zcontext)

local
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open SC A
in
structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZD = ZD
  structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
    type @{AllT_args} content = @{AllT_args} Z.ZD.content
    type @{AllT_args} zcontext = @{AllT_args} ZD.zcontext
    type @{AllT_args} zipper = @{AllT_args} ZD.zipper
    structure ZM = Z.ZM
    structure M = ZM
    type @{AllT_args} container = @{AllT_args} ZM.container * @{AllT_args} new_zcontext
    fun zip x = x |> (first ZM.Zip.morph >>> arr zipper_from_base_zipper)
    fun unzip x = x |>
      ((arr base_zipper_from_zipper >>> ZM.Unzip.morph) &&& (arr (ZD.ZCtxt.getter #> get_new_zcontext)))
    fun lift_morph move =
      (arr base_zipper_from_zipper >>> move) &&& (arr (ZD.ZCtxt.getter #> get_new_zcontext))
      >>> arr zipper_from_base_zipper
    fun up x = x |> lift_morph ZM.Up.morph
    fun down x = x |> lift_morph ZM.Down.morph
    fun left x = x |> lift_morph ZM.Left.morph
    fun right x = x |> lift_morph ZM.Right.morph)
)
open Z
end

end
