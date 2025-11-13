(*  Title:      Zippy/modify_node_next.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Node_Next"\<close>(
    structure N : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    type @{AllT_args} nnext
    val nnext : @{AllT_args} N.next -> @{AllT_args} nnext
    val dest_nnext : @{AllT_args} nnext -> @{AllT_args} N.next
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = @{AllT_args} N.content
    where type @{AllT_args} next = @{AllT_args} nnext
    where type @{AllT_args} node = @{AllT_args} N.node
  =
struct

open N

type @{AllT_args} next = @{AllT_args} nnext
local structure A = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close> open A.A
in
fun node x = x |> (comp N.node (second dest_nnext))
end

structure Next = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Data"\<close>(
  type @{AllT_args} ndata = @{AllT_args} nnext
  val ndata = nnext
  val dest_ndata = dest_nnext
  structure L = Next)

end
