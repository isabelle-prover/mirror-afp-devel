(*  Title:      Zippy/alternating_depth_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close> =
sig
  val init_depth : int
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container = int
  where type @{AllT_args} Z{i}.ZD.content = int\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Depth_Zipper"\<close>(
    M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close> =
struct

val init_depth = 0

structure Z = \<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  open M.K
  structure M = M
  type @{AllT_args} container = int
  type @{AllT_args} content = int
  fun zip x = x |> id ()
  fun unzip x = x |> id ()
  fun left x = x |> id ()
  fun right x = x |> id ()
  fun up x = x |> id ()
  fun down x = x |> id ())

structure AZ : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
struct
  open Z
  structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
  structure Base = struct open Z; type @{AllT_args} from = int; type @{AllT_args} to = int end
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} = Z
  structure Down{i} =
  struct
    open Base
    fun morph x = x |> Z.K.id ()
  end
  structure Up{i} =
  struct
    open Base
    fun morph x = x |> Z.K.id ()
  end\<close>\<close>
  structure \<^eval>\<open>"Down" ^ ML_Gen.nzippers' ()\<close> =
  struct
    open Base
    fun morph x = x + 1 |> Z.K.id ()
  end
  structure Up1 =
  struct
    open Base
    fun morph x = x - 1 |> Z.K.id ()
  end
end
open AZ
end