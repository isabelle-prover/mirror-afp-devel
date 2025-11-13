(*  Title:      Zippy/content_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Content_Zipper_Data"\<close>(
    type @{AllT_args} content
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    where type @{AllT_args} content = @{AllT_args} content
    where type @{AllT_args} zcontext = unit
    where type @{AllT_args} zipper = @{AllT_args} content
  =
struct
structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} zcontext = unit
type @{AllT_args} zipper = @{AllT_args} content

local
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(L.K.M)
  open A
in
fun zipper x = fst x

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} zipper end
structure Co =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} content
  fun getter x = x
  val modifier = AA.app
  fun lens _ = L.mk_lens getter modifier
end
structure ZCtxt =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} zcontext
  fun getter _ = ()
  fun modifier x = snd x
  fun lens _ = L.mk_lens getter modifier
end
end
end

functor \<^eval>\<open>sfx_T_nargs "Content_Zipper_Morphs"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} container
    type @{AllT_args} content
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} content) M.morph
    val unzip : (@{ParaT_args} @{AllT_args} content, @{AllT_args} container) M.morph
    val up : (@{ParaT_args} @{AllT_args} content) M.emorph
    val down : (@{ParaT_args} @{AllT_args} content) M.emorph
    val left : (@{ParaT_args} @{AllT_args} content) M.emorph
    val right : (@{ParaT_args} @{AllT_args} content) M.emorph
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close>
    where type @{AllT_args} container = @{AllT_args} container
    where type @{AllT_args} zipper = @{AllT_args} content
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
  structure M = M
  type @{AllT_args} container = @{AllT_args} container
  type @{AllT_args} zipper = @{AllT_args} content
  val zip = zip
  val unzip = unzip
  val up = up
  val down = down
  val left = left
  val right = right)

signature \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close> =
sig
  type @{AllT_args} container
  type @{AllT_args} content
  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} container
  where type @{AllT_args} ZD.content = @{AllT_args} content
  where type @{AllT_args} ZD.zcontext = unit
  where type @{AllT_args} zipper = @{AllT_args} content
end

functor \<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} container
    type @{AllT_args} content
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} content) M.morph
    val unzip : (@{ParaT_args} @{AllT_args} content, @{AllT_args} container) M.morph
    val up : (@{ParaT_args} @{AllT_args} content) M.emorph
    val down : (@{ParaT_args} @{AllT_args} content) M.emorph
    val left : (@{ParaT_args} @{AllT_args} content) M.emorph
    val right : (@{ParaT_args} @{AllT_args} content) M.emorph
  ) : \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close> =
struct

type @{AllT_args} container = @{AllT_args} container
type @{AllT_args} content = @{AllT_args} content
structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZD = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Data"\<close>(
    type @{AllT_args} content = @{AllT_args} content)
  structure ZM = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Morphs"\<close>(
    structure M = M
    type @{AllT_args} container = @{AllT_args} container
    type @{AllT_args} content = @{AllT_args} content
    val zip = zip
    val unzip = unzip
    val up = up
    val down = down
    val left = left
    val right = right)
)
open Z

end

signature \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close> = \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close>

functor \<^eval>\<open>sfx_T_nargs "Single_Content_Zipper"\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
    where type @{ParaT_args encl: "(" ")"} exn = unit
    type @{AllT_args} container
    type @{AllT_args} content
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} content) AE.morph
    val unzip : (@{ParaT_args} @{AllT_args} content, @{AllT_args} container) AE.morph
  ) : \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close> =
\<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(AE.K.M)
  type @{AllT_args} container = @{AllT_args} container
  type @{AllT_args} content = @{AllT_args} content
  open AE
  val zip = zip
  val unzip = unzip
  fun left x = x |> throw' ()
  fun right x = x |> throw' ()
  fun up x = x |> throw' ()
  fun down x = x |> throw' ()
)
