(*  Title:      Zippy/zippy_collect_trace_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COLLECT_TRACE_MIXIN =
sig
  include ZIPPY_COLLECT_TRACE_MIXIN_BASE

  val pretty_trace : @{AllT_args} data SpecCheck_Show.show  ->
    @{AllT_args} trace SpecCheck_Show.show
  val get_current : @{AllT_args} trace -> @{AllT_args} data option
  val get_prev : @{AllT_args} trace -> @{AllT_args} data list option

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZZCollect_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} SZCollect.SZ{i}.Content.data
  sharing type ZZCollect_Co{i}.container = Z{i}.zipper\<close>\<close>
end

functor Zippy_Collect_Trace_Mixin(Z : ZIPPY_COLLECT_TRACE_MIXIN_BASE) : ZIPPY_COLLECT_TRACE_MIXIN =
struct
open Z
structure MU = Zippy_Monad_Util(Z.M); open MU
structure Show = SpecCheck_Show

fun pretty_trace pretty_data = Show.option (Show.zip pretty_data (Show.list pretty_data))
fun get_current trace = Option.map fst trace
fun get_prev trace = Option.map snd trace

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZZCollect_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = SZCollect.SZ{i}.Content)\<close>\<close>
end
