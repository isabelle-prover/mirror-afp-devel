(*  Title:      Zippy/modify_node_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Node_Content"\<close>(
    structure N : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    type @{AllT_args} ncontent
    val ncontent : @{AllT_args} N.content -> @{AllT_args} ncontent
    val dest_ncontent : @{AllT_args} ncontent -> @{AllT_args} N.content
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = @{AllT_args} ncontent
    where type @{AllT_args} next = @{AllT_args} N.next
    where type @{AllT_args} node = @{AllT_args} N.node
  =
struct

open N

type @{AllT_args} content = @{AllT_args} ncontent
local structure A = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply"\<close> open A.A
in
fun node x = x |> (comp N.node (first dest_ncontent))
end

structure Co = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Data"\<close>(
  type @{AllT_args} ndata = @{AllT_args} ncontent
  val ndata = ncontent
  val dest_ndata = dest_ncontent
  structure L = Co)

end
