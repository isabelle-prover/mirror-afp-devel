(*  Title:      Zippy/list_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  type @{AllT_args} content
  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZD.content = @{AllT_args} content
  where type @{AllT_args} ZD.zcontext = @{AllT_args} content L.t * @{AllT_args} content L.t
  where type @{AllT_args} ZM.container = @{AllT_args} content L.t
  sharing type M.t = L.M.t
end

functor \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
    where type 'a t = 'a list
    val mk_exn_horizontal : unit -> (@{ParaT_args} @{ParaT_args encl: "(" ")"} L.M.exn) L.M.t
    type @{AllT_args} content
  ) :
    \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
    where type @{AllT_args} content = @{AllT_args} content
   =
struct

type @{AllT_args} content = @{AllT_args} content

structure L = L
structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
struct
  type @{AllT_args} content = @{AllT_args} content
  type @{AllT_args} zcontext = @{AllT_args} content L.t * @{AllT_args} content L.t
end)
structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(L.M)
  type @{AllT_args} container = @{AllT_args} content L.t
  open ZD
  local
    structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(M.K)
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M.M)
    open SC A
  in
  fun zip x = x |> (L.dest >>> second (arr (pair L.empty)) >>> arr zipper)
  fun get_co_zctxt x = (Co.getter x, ZCtxt.getter x)
  fun unzip x =
    let val (c, (rev_pref, suff)) = get_co_zctxt x
    in M.M.pure (rev rev_pref @ [c] @ suff) end
  fun dest_zipper x =
    let val (c, (hs, ts)) = get_co_zctxt x
    in M.M.pure (hs, (c, ts)) end
  fun up x = x |> (dest_zipper
    >>> first L.dest
    >>> arr (fn ((h, hs), (c, ts)) => zipper (h, (hs, L.cons c ts))))
  fun down x = x |> (dest_zipper
    >>> second (second L.dest)
    >>> arr (fn (hs, (c, (t, ts))) => zipper (t, (L.cons c hs, ts))))
  fun left x = x |> (K () >>> mk_exn_horizontal >>> L.M.throw)
  fun right x = x |> (K () >>> mk_exn_horizontal >>> L.M.throw)
  end)

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(structure ZD = ZD; structure ZM = ZM)
open Z
end
