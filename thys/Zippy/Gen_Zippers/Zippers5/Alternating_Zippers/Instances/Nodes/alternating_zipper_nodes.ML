(*  Title:      Zippy/alternating_zipper_nodes.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close> =
sig
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{i}.M.t = Z1.M.t\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} next = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t
  sharing type N{i}.node = Z{i}.ZD.content\<close>\<close>
end

signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close> =
sig
  structure A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} next = @{AllT_args} A.N{i}.next
  sharing type N{i}.content = A.N{i}.content
  sharing type N{i}.node = A.N{i}.node\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zcontext{i}
  type @{AllT_args} pzipper{i}
  type @{AllT_args} parent{i} = (@{ParaT_args} @{AllT_args} pzipper{i}) A.Z{i}.M.t

  val zcontext{i} : @{AllT_args} A.Z{i}.ZD.zcontext * @{AllT_args} parent{i} ->
    @{AllT_args} zcontext{i}

  structure LZCtxt{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type LZCtxt{i}.container = zcontext{i}
  sharing type LZCtxt{i}.data = A.Z{i}.ZD.zcontext

  structure Parent{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} parent{i}
  sharing type Parent{i}.container = zcontext{i}\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure PZD{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  sharing type PZD{i}.content = N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content
  sharing type PZD{i}.zcontext = zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
  sharing type PZD{i}.zipper = pzipper{i}\<close>\<close>

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZD.content = @{AllT_args} A.Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext = @{AllT_args} zcontext{i}
  where type @{AllT_args} Z{i}.ZM.container =
    @{AllT_args} A.Z{i}.ZM.container * @{AllT_args} parent{i}\<close>\<close>
  sharing type M.t = A.Z1.M.t
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
    A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close> =
struct

structure A = A
open A
structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = Z1
open M
structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

local
  structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
    type @{AllT_args} content = @{ZipperT_arg 0}
    type @{AllT_args} zcontext = @{ZipperT_arg 1})
in

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} zcontext{i} = ZContext{i} of (
    @{AllT_args} Z{i}.ZD.zcontext,
    (@{ParaT_args} @{AllT_args} pzipper{i}) M.t) lzcontext_parent\<close>
sep: \<open>and\<close>\<close>
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} pzipper{i} = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg: "," "" sep: "" start: 2}) ZD.zipper\<close>
sep: \<open>and\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} parent{i} = (@{ParaT_args} @{AllT_args} pzipper{i}) A.Z{i}.M.t\<close>\<close>

(*create parent zipper data by simultaneous instantiation*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure PZD{i} :
  \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  where type @{AllT_args} content = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg: "," "" sep: "" start: 2}) ZD.content
  where type @{AllT_args} zcontext = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg: "," "" sep: "" start: 2}) ZD.zcontext
  where type @{AllT_args} zipper = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg: "," "" sep: "" start: 2}) ZD.zipper
  = ZD\<close>\<close>
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun zcontext{i} x = Library.uncurry lzcontext_parent x |> ZContext{i}\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Base = struct open L; type @{AllT_args} container = @{AllT_args} zcontext{i} end
structure LZCtxt{i} =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} Z{i}.ZD.zcontext
  fun getter (ZContext{i} {lzcontext,...}) = lzcontext
  fun modifier (f, ZContext{i} {lzcontext, parent}) = zcontext{i} (f lzcontext, parent)
  fun lens _ = L.mk_lens getter modifier
end
structure Parent{i} =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} parent{i}
  fun getter (ZContext{i} {parent,...}) = parent
  fun modifier (f, ZContext{i} {lzcontext, parent}) = zcontext{i} (lzcontext, f parent)
  fun lens _ = L.mk_lens getter modifier
end\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Extend_Zipper_Context"\<close>(
  structure Z = Z{i}
  structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
    type @{AllT_args} content = @{AllT_args} Z{i}.ZD.content
    type @{AllT_args} zcontext = @{AllT_args} zcontext{i})
  type @{AllT_args} new_zcontext = @{AllT_args} parent{i}
  val mk_zcontext = zcontext{i}
  val get_base_zcontext = LZCtxt{i}.getter
  val get_new_zcontext = Parent{i}.getter
)\<close>\<close>

structure Base =
struct
  structure MB = \<^eval>\<open>sfx_ParaT_nargs "Morph_Base"\<close>(M)
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M)
  open MB M
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close> =
struct
  open Base
  type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  fun morph x =
    let
      val zcontent = Z{i}.ZD.Co.getter x
      val content = N{i}.Co.getter zcontent
      val next = N{i}.Next.getter zcontent
      val zctxt = Z{i}.ZD.ZCtxt.getter x
      val pzd = PZD\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper (content, zctxt)
    in next >>= (fn next => Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Zip.morph (next, pure pzd)) end
end\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close> =
struct
  open Base
  type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  fun morph x =
    Z{i}.ZM.Unzip.morph x
    >>= (fn (next, parent) => parent
    >>= K.arr (fn parent =>
      let
        val content = PZD{i}.Co.getter parent
        val zctxt = PZD{i}.ZCtxt.getter parent
        val node = N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>node (content, pure next)
      in Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>ZD.zipper (node, zctxt) end))
end\<close>\<close>

end
