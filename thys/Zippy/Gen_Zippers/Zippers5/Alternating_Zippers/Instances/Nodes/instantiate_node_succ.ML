(*  Title:      Zippy/instantiate_node_succ.ML
    Author:     Kevin Kappelmann

Instantiate_Node_Succ_k_j_i creates a Node_j_i from a Node_j_{i+1} by instantiation
of the zipper types 'a1,...,'a{i+1} as follows:
for n<k, use 'an.
for n=k, use @{AllT_args} inst.
for n>k, use 'a{n-1}.

In other words: one polymorphic type parameter of the node is instantiated and all other ones
are kept the same or shifted to the left by one.
*)
\<^imap>\<open>\<open>{k}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Node_Succ" {k}\<close>(
    structure N : \<^eval>\<open>succ_node_sig\<close>
    type @{AllT_args} inst
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      @{ZipperT_args stop: \<open>{k} - 2\<close> sep: "" encl_arg: "" ","}
      @{AllT_args} inst
      @{ZipperT_args start: \<open>{k} - 1\<close> sep: "" encl_arg: "," ""}) N.content
    where type @{AllT_args} next = (@{ParaT_args}
      @{ZipperT_args stop: \<open>{k} - 2\<close> sep: "" encl_arg: "" ","}
      @{AllT_args} inst
      @{ZipperT_args start: \<open>{k} - 1\<close> sep: "" encl_arg: "," ""}) N.next
    where type @{AllT_args} node = (@{ParaT_args}
      @{ZipperT_args stop: \<open>{k} - 2\<close> sep: "" encl_arg: "" ","}
      @{AllT_args} inst
      @{ZipperT_args start: \<open>{k} - 1\<close> sep: "" encl_arg: "," ""}) N.node
  =
struct
open N
type @{AllT_args} content = (@{ParaT_args}
  @{ZipperT_args stop: \<open>{k} - 2\<close> sep: "" encl_arg: "" ","}
  @{AllT_args} inst
  @{ZipperT_args start: \<open>{k} - 1\<close> sep: "" encl_arg: "," ""}) N.content
type @{AllT_args} next = (@{ParaT_args}
  @{ZipperT_args stop: \<open>{k} - 2\<close> sep: "" encl_arg: "" ","}
  @{AllT_args} inst
  @{ZipperT_args start: \<open>{k} - 1\<close> sep: "" encl_arg: "," ""}) N.next
type @{AllT_args} node = (@{ParaT_args}
  @{ZipperT_args stop: \<open>{k} - 2\<close> sep: "" encl_arg: "" ","}
  @{AllT_args} inst
  @{ZipperT_args start: \<open>{k} - 1\<close> sep: "" encl_arg: "," ""}) N.node

structure Base = struct type @{AllT_args} container = @{AllT_args} node end
structure Co =
struct
  open Co Base
  type @{AllT_args} data = @{AllT_args} content
end
structure Next =
struct
  open Next Base
  type @{AllT_args} data = @{AllT_args} next
end
end\<close>\<close>
