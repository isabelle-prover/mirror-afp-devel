(*  Title:      Zippy/zippy_lists_positions_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_POSITIONS_MIXIN =
sig
  include ZIPPY_LISTS_POSITIONS_MIXIN_BASE

  val compact_path : ZP.ZGPos.path -> int list
  val pretty_path : ZP.ZGPos.path SpecCheck_Show.show
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val pretty_position_zipper{i} : @{AllT_args} Z{i}.zipper SpecCheck_Show.show
  val pretty_position_container{i} : @{AllT_args} Z{i}.ZM.container SpecCheck_Show.show\<close>\<close>
end

functor Zippy_Lists_Positions_Mixin(
    structure Z : ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
  ) : ZIPPY_LISTS_POSITIONS_MIXIN
  =
struct
open Z
structure ZP = Zippy_Positions_Mixin(structure Z = Z.ZP; structure Exn = Exn)
structure Show = SpecCheck_Show

val compact_path = List.map (List.length #> General_Util.pred)
val pretty_path = compact_path #> List.rev #> chop_groups \<^eval>\<open>ML_Gen.nzippers' ()\<close>
  #> Show.list (Show.list Show.int)

fun pretty_position depth path = Show.record [("Depth", Show.int depth), ("Path", pretty_path path)]

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun pretty_position_zipper{i} z = pretty_position
  (ZP.ZZDepth_Co{i}.getter z) (ZP.ZZGPos_Co{i}.getter z)
fun pretty_position_container{i} c = pretty_position
  (ZP.SZDepth.SZ{i}.Container.getter c) (ZP.SZGPos.SZ{i}.Container.getter c)
\<close>\<close>

end
