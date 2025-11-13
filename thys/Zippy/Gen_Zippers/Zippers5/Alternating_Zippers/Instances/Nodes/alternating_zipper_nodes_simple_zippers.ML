(*  Title:      Zippy/alternating_zipper_nodes_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZD.content = @{ZipperT_arg 0}
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>
  ) :
  sig
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} node{i}\<close>\<close>

    include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      @{AllT_args} node{i},
      @{ZipperT_args start: 1}) Z{i}.ZM.container
    where type @{AllT_args} N{i}.node = @{AllT_args} node{i}
    where type @{AllT_args} N{i}.content = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
    (* where @{AllT_args} Zi.ZD.zcontext = (@{ParaT_args} @{AllT_args} Ni.node, 'a2, ...) Zi.ZD.zcontext *)
    where type (@{ParaT_args} 'a) Z1.M.t = (@{ParaT_args} 'a) Z1.M.t
  end
  =
struct

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>succ_node_functor\<close>(
  type (@{AllT_args encl: "" ","} 'n) next = 'n
  type (@{AllT_args encl: "" ","} 'n) content = @{ZipperT_arg \<open>{i} - 1\<close>})\<close>\<close>

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} next{i} = Next{i} of (@{ParaT_args}
  (@{ParaT_args}
    (@{AllT_args encl: "" ","} @{AllT_args} next\<^eval>\<open>succ_mod_nzippers {i}\<close>)
      N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>node,
    @{ZipperT_args start: 1}) Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container)
  Z{i}.ZM.Zip.M.t\<close>
sep: "and"\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun next{i} x = Next{i} x
fun dest_next{i} (Next{i} x) = x\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} =
\<^eval>\<open>sfx_inst_T_nargs "Instantiate_Node_Succ" (ML_Gen.nzippers () + 1)\<close>(
  type @{AllT_args} inst = @{AllT_args} next{i}
  structure N = N{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Zipper" 1\<close>(
  type @{AllT_args} inst = @{AllT_args} N{i}.node
  structure Z = Z{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>sfx_T_nargs "Modify_Node_Next"\<close>(
  structure N = N{i}
  type @{AllT_args} nnext = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Zip.M.t
  val nnext = dest_next{i}
  val dest_nnext = next{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} node{i} = @{AllT_args} N{i}.node\<close>\<close>

end