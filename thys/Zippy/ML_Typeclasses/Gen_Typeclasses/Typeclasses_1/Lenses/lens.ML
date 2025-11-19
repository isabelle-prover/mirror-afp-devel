(*  Title:  lens.ML
    Author: Kevin Kappelmann

Lenses adopted from Haskell's fclables https://hackage.haskell.org/package/fclabels
Unlike fclabels, which uses GADTs and categories, we register lenses as indexed categories.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "LENS_BASE"\<close> =
sig
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>

  type (@{ParaT_args} 's, 'i) getter = (@{ParaT_args} 's, 'i) C.morph
  type (@{ParaT_args} 't, 'o, 's, 'i) modifier =
    (@{ParaT_args} (@{ParaT_args} 'i, 'o) C.morph * 's, 't) C.morph
  type (@{ParaT_args} 's, 'i) smodifier = (@{ParaT_args} 's, 'i, 's, 'i) modifier

  (*Abstract lens datatype. The getter and modifier work in some category.
  The type of the value pointed to might change, thereby changing the type of the outer structure.*)
  type (@{ParaT_args} 't, 'o, 's, 'i) lens
  (*simple lens*)
  type (@{ParaT_args} 's, 'i) slens = (@{ParaT_args} 's, 'i, 's, 'i) lens

  val mk_lens : (@{ParaT_args} 's, 'i) getter -> (@{ParaT_args} 't, 'o, 's, 'i) modifier ->
    (@{ParaT_args} 't, 'o, 's, 'i) lens

  val get : (@{ParaT_args} 't, 'o, 's, 'i) lens -> (@{ParaT_args} 's, 'i) getter
  val modify : (@{ParaT_args} 't, 'o, 's, 'i) lens -> (@{ParaT_args} 't, 'o, 's, 'i) modifier

  val comp_modify : (@{ParaT_args} 'o, 'u, 'i, 'j) modifier ->
    (@{ParaT_args} 't, 'o, 's, 'i) modifier -> (@{ParaT_args} 't, 'u, 's, 'j) modifier
  include \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close>
  sharing type morph = lens
end

functor \<^eval>\<open>sfx_ParaT_nargs "Lens_Base"\<close>(AA : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "LENS_BASE"\<close> =
struct

structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(AA)
structure C = AA

type (@{ParaT_args} 's, 'i) getter = (@{ParaT_args} 's, 'i) C.morph
type (@{ParaT_args} 't, 'o, 's, 'i) modifier =
  (@{ParaT_args} (@{ParaT_args} 'i, 'o) C.morph * 's, 't) C.morph
type (@{ParaT_args} 's, 'i) smodifier = (@{ParaT_args} 's, 'i, 's, 'i) modifier

datatype (@{ParaT_args} 't, 'o, 's, 'i) lens = Lens of {
  get : (@{ParaT_args} 's, 'i) getter,
  modify : (@{ParaT_args} 't, 'o, 's, 'i) modifier
}
type (@{ParaT_args} 's, 'i) slens = (@{ParaT_args} 's, 'i, 's, 'i) lens

fun mk_lens get modify = Lens {get = get, modify = modify}

fun get (Lens {get, ...}) = get
fun modify (Lens {modify, ...}) = modify

type (@{ParaT_args} 'i, 'j, 'a, 'b) morph = (@{ParaT_args} 'i, 'j, 'a, 'b) lens
type (@{ParaT_args} 'i, 'j, 'a) emorph = (@{ParaT_args} 'i, 'j, 'a, 'a) morph

fun id _ = mk_lens (A.id ()) AA.app

fun comp_modify m1 m2 = AA.uncurry (A.curry m2 o A.curry m1)

fun comp l1 l2 =
  let
    val g1 = get l1
    val m1 = modify l1
    val g2 = get l2
    val m2 = modify l2
  in mk_lens (A.comp g1 g2) (comp_modify m1 m2) end

end

signature \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "LENS_BASE"\<close>

  type (@{ParaT_args} 't, 'o, 's) setter = (@{ParaT_args} ('o * 's), 't) C.morph
  type (@{ParaT_args} 's, 'o) ssetter = (@{ParaT_args} ('o * 's), 's) C.morph

  val set_modify : (@{ParaT_args} 't, 'o, 's, 'i) modifier -> (@{ParaT_args} 't, 'o, 's) setter
  val set : (@{ParaT_args} 't, 'o, 's, 'i) lens -> (@{ParaT_args} 't, 'o, 's) setter

  val lens_get : (@{ParaT_args} 's, 'i) C.morph -> (@{ParaT_args} 'o, 'o, 's, 'i) lens
  val lens_mk : (@{ParaT_args} 'o, 't) C.morph -> (@{ParaT_args} 't, 'o, 'i, 'i) lens
  val lens_get_mk : (@{ParaT_args} 's, 'i) C.morph -> (@{ParaT_args} 'u, 'o) C.morph ->
    (@{ParaT_args} 'o, 'u, 's, 'i) lens

  (*pairs*)
  val get_fst : (@{ParaT_args} 's, 'i1 * 'i2) getter -> (@{ParaT_args} 's, 'i1) getter
  val get_snd : (@{ParaT_args} 's, 'i1 * 'i2) getter -> (@{ParaT_args} 's, 'i2) getter
  val modify_fst : (@{ParaT_args} 't, 'o1 * 'i2, 's, 'i1 * 'i2) modifier ->
    (@{ParaT_args} 't, 'o1, 's, 'i1) modifier
  val modify_snd : (@{ParaT_args} 't, 'i1 * 'o2, 's, 'i1 * 'i2) modifier ->
    (@{ParaT_args} 't, 'o2, 's, 'i2) modifier
  val lens_fst : (@{ParaT_args} 't, 'o1 * 'i2, 's, 'i1 * 'i2) lens ->
    (@{ParaT_args} 't, 'o1, 's, 'i1) lens
  val lens_snd : (@{ParaT_args} 't, 'i1 * 'o2, 's, 'i1 * 'i2) lens ->
    (@{ParaT_args} 't, 'o2, 's, 'i2) lens

  val modify_K : (@{ParaT_args} 't, ((@{ParaT_args} 'a, 'o) C.morph), 's, 'i) modifier ->
    (@{ParaT_args} 't, 'o, 's, 'i) modifier
  val lens_K : (@{ParaT_args} 't, ((@{ParaT_args} 'a, 'o) C.morph), 's, 'i) lens ->
    (@{ParaT_args} 't, 'o, 's, 'i) lens
end

functor \<^eval>\<open>sfx_ParaT_nargs "Lens"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_BASE"\<close>
    sharing type L.C.morph = A.morph
  ) : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close> =
struct

open L

type (@{ParaT_args} 't, 'o, 's) setter = (@{ParaT_args} ('o * 's), 't) C.morph
type (@{ParaT_args} 's, 'o) ssetter = (@{ParaT_args} ('o * 's), 's) C.morph

fun set_modify m = C.comp m (A.first (A.arr A.K))
fun set l = set_modify (modify l)

fun lens_get f =
  L.mk_lens (L.id () |> L.get |> L.C.comp f) (A.second f |> L.C.comp (L.modify (L.id ())))

fun lens_mk f =
  let val id = L.id ()
  in L.mk_lens (L.get id) (L.C.comp f (L.modify id)) end

fun lens_get_mk get modify = lens_get get |> comp (lens_mk modify)

(*pairs*)
fun get_fst f = C.comp (A.arr fst) f
fun get_snd f = C.comp (A.arr snd) f
fun modify_fst f = C.comp f (A.first (A.arr A.first))
fun modify_snd f = C.comp f (A.first (A.arr A.second))

fun lens_fst l = mk_lens (get_fst (get l)) (modify_fst (modify l))
fun lens_snd l = mk_lens (get_snd (get l)) (modify_snd (modify l))

local open A in
fun modify_K m = C.comp m (first (arr (C.comp (arr K))))
fun lens_K l = mk_lens (get l) (modify_K (modify l))
end

end

signature \<^eval>\<open>sfx_ParaT_nargs "PAIR_LENS"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "LENS_BASE"\<close>
  val get_pair :
    (@{ParaT_args} 's1, 'i1) getter -> (@{ParaT_args} 's2, 'i2) getter ->
      (@{ParaT_args} 's1 * 's2, 'i1 * 'i2) getter
  val modify_pair : (@{ParaT_args} 's1 * 's2, 'i1 * 'i2) getter ->
    (@{ParaT_args} 't1, 'o1, 's1, 'i1) modifier -> (@{ParaT_args} 't2, 'o2, 's2, 'i2) modifier ->
    (@{ParaT_args} 't1 * 't2, 'o1 * 'o2, 's1 * 's2, 'i1 * 'i2) modifier
  val lens_pair : (@{ParaT_args} 't1, 'o1, 's1, 'i1) lens -> (@{ParaT_args} 't2, 'o2, 's2, 'i2) lens ->
    (@{ParaT_args} 't1 * 't2, 'o1 * 'o2, 's1 * 's2, 'i1 * 'i2) lens
end

functor \<^eval>\<open>sfx_ParaT_nargs "Pair_Lens"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
    structure AA : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close>
    sharing type AA.morph = A.morph
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_BASE"\<close>
    sharing type L.C.morph = A.morph
  ) : \<^eval>\<open>sfx_ParaT_nargs "PAIR_LENS"\<close> =
struct

open L

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC A
in
fun get_pair g1 g2 = g1 *** g2

structure SArrow_Apply = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Apply"\<close>

fun modify_pair g m1 m2 =
  arr (fn (f, x) => ((f, x), x))
  >>> first (second g >>> AA.app >>> arr (SArrow_Apply.*** (K #> pair, K #> pair)))
  >>> arr (uncurry SArrow_Apply.***)
  >>> (m1 *** m2)

fun lens_pair l1 l2 =
  let val g = get_pair (L.get l1) (L.get l2)
  in L.mk_lens g (modify_pair g (L.modify l1) (L.modify l2)) end
end

end

signature \<^eval>\<open>sfx_ParaT_nargs "LENS_APP"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  val get_app : 'a -> (@{ParaT_args} 's, ((@{ParaT_args} 'a, 'i) C.morph)) getter ->
    (@{ParaT_args} 's, 'i) getter
  val modify_app : 'a -> (@{ParaT_args} 't, 'o, 's, ((@{ParaT_args} 'a, 'i) C.morph)) modifier ->
    (@{ParaT_args} 't, 'o, 's, 'i) modifier
  val lens_app : 'a -> (@{ParaT_args} 't, 'o, 's, ((@{ParaT_args} 'a, 'i) C.morph)) lens ->
    (@{ParaT_args} 't, 'o, 's, 'i) lens

  val modify_app_K : 'a -> (@{ParaT_args} 't, ((@{ParaT_args} 'b, 'o) C.morph), 's,
    ((@{ParaT_args} 'a, 'i) C.morph)) modifier ->
    (@{ParaT_args} 't, 'o, 's, 'i) modifier
  val lens_app_K : 'a -> (@{ParaT_args} 't, ((@{ParaT_args} 'b, 'o) C.morph), 's,
    ((@{ParaT_args} 'a, 'i) C.morph)) lens -> (@{ParaT_args} 't, 'o, 's, 'i) lens
end

functor \<^eval>\<open>sfx_ParaT_nargs "Lens_App"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
    structure AA : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close>
    sharing type AA.morph = A.morph
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    sharing type L.C.morph = A.morph
  ) : \<^eval>\<open>sfx_ParaT_nargs "LENS_APP"\<close> =
struct

open L

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC A
in
fun get_app x = C.comp (AA.app' x)
fun modify_app x m = first (arr (fn m' => AA.app' x >>> m')) >>> m
fun lens_app x l = mk_lens (get_app x (get l)) (modify_app x (modify l))

fun modify_app_K x m = modify_K (modify_app x m)
fun lens_app_K x l = lens_K (lens_app x l)
end

end

signature \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) K.kleisli
  val get_monad : (@{ParaT_args} 's, (@{ParaT_args} 'i) K.M.t) getter -> (@{ParaT_args} 's, 'i) getter
  val modify_monad :
    (@{ParaT_args} 't, (@{ParaT_args} 'o) K.M.t, 's, (@{ParaT_args} 'i) K.M.t) modifier ->
    (@{ParaT_args} 't, 'o, 's, 'i) modifier
  val lens_monad :
    (@{ParaT_args} 't, (@{ParaT_args} 'o) K.M.t, 's, (@{ParaT_args} 'i) K.M.t) lens ->
    (@{ParaT_args} 't, 'o, 's, 'i) lens
end

functor \<^eval>\<open>sfx_ParaT_nargs "Lens_Kleisli"\<close>(
    structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.morph = (@{ParaT_args} 'a, 'b) K.kleisli
  ) : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close> =
struct

open L
structure K = K

fun get_monad f = (fn x => K.M.bind (f x) I)
fun modify_monad f = apfst K.M.map #> f
fun lens_monad l = L.mk_lens (get_monad (L.get l)) (modify_monad (L.modify l))

end
