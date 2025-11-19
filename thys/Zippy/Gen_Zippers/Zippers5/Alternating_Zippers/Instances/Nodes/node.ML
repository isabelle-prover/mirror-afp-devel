(*  Title:      Zippy/node.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "NODE"\<close> =
sig
  type @{AllT_args} node
  type @{AllT_args} content
  type @{AllT_args} next

  val node : @{AllT_args} content * @{AllT_args} next -> @{AllT_args} node

  structure Co : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} node
  where type @{AllT_args} data = @{AllT_args} content

  structure Next : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} node
  where type @{AllT_args} data = @{AllT_args} next
end

functor \<^eval>\<open>sfx_T_nargs "Node"\<close>(
    type @{AllT_args} content
    type @{AllT_args} next
  ) : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} next = @{AllT_args} next
datatype @{AllT_args} node = Node of {content : @{AllT_args} content, next : @{AllT_args} next}

fun node (content, next) = Node {content = content, next = next}

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} node end
structure Co =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} content
  fun getter (Node {content,...}) = content
  fun modifier (f, Node {content, next}) = node (f content, next)
  fun lens _ = L.mk_lens getter modifier
end

structure Next =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} next
  fun getter (Node {next,...}) = next
  fun modifier (f, Node {content, next}) = node (content, f next)
  fun lens _ = L.mk_lens getter modifier
end

end
