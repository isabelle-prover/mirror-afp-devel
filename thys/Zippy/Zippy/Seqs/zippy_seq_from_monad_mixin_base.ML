(*  Title:      Zippy/zippy_seq_from_monad_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_SEQ_FROM_MONAD_MIXIN_BASE =
sig
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
  type @{AllT_args} state
  val seq_from_monad : @{AllT_args} state -> (@{ParaT_args} 'a Seq.seq) M.t -> 'a Seq.seq
end

functor Zippy_Seq_From_Monad_Mixin_Base(A :
  sig
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>
    type @{AllT_args} state
    val seq_from_monad : @{AllT_args} state -> (@{ParaT_args} 'a Seq.seq) M.t -> 'a Seq.seq
  end) : ZIPPY_SEQ_FROM_MONAD_MIXIN_BASE
  = A
