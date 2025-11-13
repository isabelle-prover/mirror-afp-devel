(*  Title:  bi_typeclass.ML
    Author: Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR_FIRST"\<close> =
sig
  type (@{ParaT_args} 'a, 'b) t
  val first : ('a -> 'c) -> (@{ParaT_args} 'a, 'b) t -> (@{ParaT_args} 'c, 'b) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR_SECOND"\<close> =
sig
  type (@{ParaT_args} 'a, 'b) t
  val second : ('b -> 'c) -> (@{ParaT_args} 'a, 'b) t -> (@{ParaT_args} 'a, 'c) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR_BASE"\<close> =
sig
  type (@{ParaT_args} 'a, 'b) t
  val bimap : ('a -> 'c) -> ('b -> 'd) -> (@{ParaT_args} 'a, 'b) t -> (@{ParaT_args} 'c, 'd) t
end

signature \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR_BASE"\<close>
  val first : ('a -> 'c) -> (@{ParaT_args} 'a, 'b) t -> (@{ParaT_args} 'c, 'b) t
  val second : ('b -> 'd) -> (@{ParaT_args} 'a, 'b) t -> (@{ParaT_args} 'a, 'd) t
end

functor \<^eval>\<open>sfx_ParaT_nargs "Bi_Functor"\<close>(B : \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "BI_FUNCTOR"\<close> =
struct
open B
fun first f = B.bimap f I
fun second f = B.bimap I f
end