(*  Title:      Zippy/zippy_node.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE =
sig
  include ZIPPY_NODE_BASE
  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  (* misc *)
  val no_parent : (@{ParaT_args} @{ParaT_args encl: "(" ")"} Exn.AE.exn, 'p) morph
  val no_next : (@{ParaT_args} @{ParaT_args encl: "(" ")"} Exn.AE.exn, 'n) morph

  (* constructors *)
  val container_no_parent : @{ParaT_args encl: "(" ")"} Exn.AE.exn -> 'c ->
    'c * (@{ParaT_args} 'p) M.t
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val node_no_next{i} : @{ParaT_args encl: "(" ")"} Exn.AE.exn -> @{AllT_args} ZN.N{i}.content ->
    @{AllT_args} ZN.N{i}.node\<close>\<close>

  (* lenses *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Node{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Node{i}.container = Z{i}.zipper
  sharing type Node{i}.data = ZN.N{i}.node

  structure Node_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Node_Co{i}.container = Z{i}.zipper
  sharing type Node_Co{i}.data = ZN.N{i}.content

  structure Node_Next{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZN.N{i}.next
  sharing type Node_Next{i}.container = Z{i}.zipper\<close>\<close>

  val set_no_next : @{ParaT_args encl: "(" ")"} Exn.AE.exn ->
    (@{ParaT_args} 's, (@{ParaT_args} 'i) M.t) L.smodifier -> 's -> 's
end

functor Zippy_Node(
    structure Z : ZIPPY_NODE_BASE
    structure Exn : ZIPPY_EXCEPTION_MIXIN
    sharing type Exn.M.t = Z.M.t
  ) : ZIPPY_NODE =
struct

open Z
structure Exn = Exn; open Exn

(* misc *)
val no_parent = AE.throw
val no_next = AE.throw

(* constructors *)
fun container_no_parent e c = (c, no_parent e)
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun node_no_next{i} e c = ZN.N{i}.node (c, no_next e)\<close>\<close>

(* lenses *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Node{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = SZN.SZ{i}.Content)

structure Node_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Node{i}
  structure L2 = ZN.N{i}.Co)

structure Node_Next{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Node{i}
  structure L2 = ZN.N{i}.Next)\<close>\<close>

fun set_no_next exn nextl z = L.set_modify nextl (no_next exn, z)

end