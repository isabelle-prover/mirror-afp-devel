(*  Title:      Zippy/alternating_zipper_nodes_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} ncontent{i} (*content for node{i}*)
    val ncontent{i} : @{AllT_args} Z{i}.ZD.content -> @{AllT_args} ncontent{i}

    val next{i} : @{AllT_args} Z{i}.ZD.content ->
      (@{ParaT_args} @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t

    val content{i} : @{AllT_args} ncontent{i} ->
      (@{ParaT_args} @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t ->
      @{AllT_args} Z{i}.ZD.content\<close>\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZD.zcontext = @{AllT_args} Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} Z{i}.ZM.container
    where type @{AllT_args} Z{i}.zipper = @{AllT_args} Z{i}.zipper\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} N{i}.content = @{AllT_args} ncontent{i}\<close>\<close>
    where type (@{ParaT_args} 'a) Z1.M.t = (@{ParaT_args} 'a) Z1.M.t
  =
struct

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>sfx_T_nargs "Node"\<close>(
  type @{AllT_args} content = @{AllT_args} ncontent{i}
  type @{AllT_args} next = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t
)\<close>\<close>

local structure A = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close>; open A A.A
in
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Content"\<close>(
  structure Z = Z{i}
  type @{AllT_args} ncontent = @{AllT_args} N{i}.node
  fun ncontent x = x |> comp N{i}.node (ncontent{i} &&& next{i})
  fun dest_ncontent x = x |> comp (AA.uncurry content{i}) (N{i}.Co.getter &&& N{i}.Next.getter)
)\<close>\<close>
end

end
