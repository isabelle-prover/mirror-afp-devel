(*  Title:      Zippy/alternating_global_position_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close> =
sig
  type path = Zipper_Position.pos list
  val init_path : path
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container = path
  where type @{AllT_args} Z{i}.ZD.zcontext = unit
  where type @{AllT_args} Z{i}.ZD.content = path
  where type @{AllT_args} Z{i}.zipper = path\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Global_Position_Zipper"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_GLOBAL_POSITION_ZIPPER"\<close> =
struct

structure Pos = Zipper_Position
type path = Pos.pos list
val init_path = []

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
structure MB = M
structure M = MB
open M

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure M = MB
  open M.M
  type @{AllT_args} container = path
  type @{AllT_args} content = path
  type @{AllT_args} zipper = path
  fun zip pss = pure (Pos.init :: pss)
  fun unzip (_ :: pss) = pure pss
  fun down (ps :: pss) = pure ((Pos.init_x :: ps) :: pss)
  (*FIXME: use monad with exception instead of throwing option exception?*)
  fun up (ps :: pss) = pure (the (Pos.up ps) :: pss
    handle Option.Option => error "Cannot go further up in alternating global position zipper.")
  fun left (ps :: pss) = pure (Pos.left ps :: pss)
  fun right (ps :: pss) = pure (Pos.right ps :: pss))\<close>\<close>

structure Base =
struct open MB
  type @{AllT_args} from = path
  type @{AllT_args} to = path
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = struct open Base; fun morph pss = M.pure (Pos.init :: pss) end\<close>\<close>
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = struct open Base; fun morph (_ :: pss) = M.pure pss end\<close>\<close>

end
