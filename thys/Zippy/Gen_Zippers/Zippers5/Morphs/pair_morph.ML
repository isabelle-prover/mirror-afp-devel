(*  Title:      Zippy/pair_morph.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "PAIR_MORPH_DEP_MORPH"\<close> =
sig
  structure M1 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  structure M2 : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  where type @{AllT_args} dep = @{AllT_args} M1.from * @{AllT_args} M1.to
  sharing type M1.M.t = M2.M.t

  include \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  where type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
  where type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to
  sharing type M.t = M1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
    structure M1 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    structure M2 : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
    where type @{AllT_args} dep = @{AllT_args} M1.from * @{AllT_args} M1.to
    sharing type M2.M.t = M1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_MORPH_DEP_MORPH"\<close>
  =
struct
structure M1 = M1
structure M2 = M2

structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = M1
open M

type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to

local
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(K); open A
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M); open M
in
fun morph (x, y) = M1.morph x >>= (fn r => M2.morph (x, r) y >>= (fn s => pure (r, s)))
end
end

signature \<^eval>\<open>sfx_T_nargs "PAIR_MORPH"\<close> =
sig
  structure M1 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  structure M2 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type M1.M.t = M2.M.t

  include \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  where type @{AllT_args} from = @{AllT_args} M1.from * @{AllT_args} M2.from
  where type @{AllT_args} to = @{AllT_args} M1.to * @{AllT_args} M2.to
  sharing type M.t = M1.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Pair_Morph"\<close>(
    structure M1 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    structure M2 : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
    sharing type M2.M.t = M1.M.t
  ) : \<^eval>\<open>sfx_T_nargs "PAIR_MORPH"\<close>
  =
struct
structure M2In = M2
structure PM = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
  structure M1 = M1
  structure M2 = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
    structure M = M2; type @{AllT_args} dep = @{AllT_args} M1.from * @{AllT_args} M1.to))
open PM
structure M2 = M2In
end