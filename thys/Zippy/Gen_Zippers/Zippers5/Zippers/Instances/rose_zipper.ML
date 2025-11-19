(*  Title:      Zippy/rose_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ROSE_ZIPPER"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  type 'a rose
  val dest_rose : 'a rose -> ('a * 'a rose) L.t
  val rose : ('a * 'a rose) L.t -> 'a rose
  val cons : 'a * 'a rose -> 'a rose -> 'a rose
  type @{AllT_args} content
  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZD.content = @{AllT_args} content
  where type @{AllT_args} ZD.zcontext = @{AllT_args} content rose *
    (((@{AllT_args} content * @{AllT_args} content rose) L.t *
    (@{AllT_args} content * @{AllT_args} content rose) L.t * @{AllT_args} content option) L.t)
  where type @{AllT_args} ZM.container = @{AllT_args} content rose
  sharing type M.t = L.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Rose_Zipper"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
    where type 'a t = 'a list
    where type @{ParaT_args encl: "(" ")"} M.exn = unit
    type @{AllT_args} content
  ) :
    \<^eval>\<open>sfx_T_nargs "ROSE_ZIPPER"\<close>
    where type @{AllT_args} content = @{AllT_args} content
  =
struct

structure L = L
type @{AllT_args} content = @{AllT_args} content

datatype 'a rose = Rose of ('a * 'a rose) L.t
fun dest_rose (Rose xs) = xs
fun rose xs = Rose xs
fun cons x (Rose xs) = Rose (L.cons x xs)

structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
  type @{AllT_args} content = @{AllT_args} content
  type @{AllT_args} zcontext = @{AllT_args} content rose *
    (((@{AllT_args} content * @{AllT_args} content rose) L.t *
    (@{AllT_args} content * @{AllT_args} content rose) L.t * @{AllT_args} content option) L.t))

structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(L.M)
  type @{AllT_args} container = @{AllT_args} content rose
  open ZD
  local
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M.M)
    structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
    structure AC = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice"\<close>(M.M)
    open SC A
  in
  fun zip x = x |> (arr dest_rose
    >>> L.dest
    >>> arr (fn ((x, cs), xs) => zipper (x, (cs, [([], xs, NONE)]))))
  fun get_co_zctxt x = (Co.getter x, ZCtxt.getter x)
  fun unzip x =
    let
      fun mk [(rev_pref, suff, _)] children v = Rose (rev rev_pref @ [(v, children)] @ suff)
        | mk ((rev_pref, suff, SOME c) :: xs) children v =
            mk xs (Rose (rev rev_pref @ [(v, children)] @ suff)) c
      val (c, (children, xs)) = get_co_zctxt x
    in M.M.pure (mk xs children c) end
  fun dest_zipper x =
    let val (c, (ch, xs)) = get_co_zctxt x
    in (ch, (c, xs)) end
  fun dest_zipper_flip x = x |> (dest_zipper #> (fn (ch, (c, xs)) => (xs, (c, ch))))
  fun up x = x |> (arr dest_zipper_flip
    >>> first L.dest
    >>> arr (fn (((rev_pref, suff, p), xs), (c, ch)) =>
      Option.map (rpair (rose (rev rev_pref @ [(c, ch)] @ suff), xs)) p)
    >>> AC.opt L.M.throw (arr zipper))
  fun down x = x |> (arr dest_zipper
    >>> first (arr dest_rose >>> L.dest)
    >>> arr (fn (((c, ch), cs), (p, xs)) => zipper (c, (ch, (L.cons (L.empty, cs, SOME p) xs)))))
  fun left x = x |> (arr dest_zipper_flip
    >>> first L.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (rev_pref, (suff, p, xs))))
    >>> first (first L.dest)
    >>> arr (fn ((((r, rch), rs), (suff, p, xs)), (c, ch)) =>
      zipper (r,  (rch, L.cons (rs, L.cons (c, ch) suff , p) xs))))
  fun right x = x |> (arr dest_zipper_flip
    >>> first L.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (suff, (rev_pref, p, xs))))
    >>> first (first L.dest)
    >>> arr (fn ((((s, sch), ss), (rev_pref, p, xs)), (c, ch)) =>
      zipper (s, (sch, L.cons (L.cons (c, ch) rev_pref, ss, p) xs))))
  end)

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(structure ZD = ZD; structure ZM = ZM)
open Z

end
