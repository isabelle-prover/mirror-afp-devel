section \<open>Export\<close>

theory Export
  imports Prover
begin

text \<open>In this theory, we make the prover executable using the code interpretation of the abstract
completeness framework and the Isabelle to Haskell code generator.\<close>

text \<open>To actually execute the prover, we need to lazily evaluate the stream of rules to apply.
Otherwise, we will never actually get to a result.\<close>
code_lazy_type stream

text \<open>We would also like to make the evaluation of streams a bit more efficient.\<close>
declare Stream.smember_code [code del]
lemma [code]: "Stream.smember x (y ## s) = (x = y \<or> Stream.smember x s)"
  unfolding Stream.smember_def by auto

text \<open>To export code to Haskell, we need to specify that functions on the option type should be
  exported into the equivalent functions on the Maybe monad.\<close>
code_printing
  constant the \<rightharpoonup> (Haskell) "MaybeExt.fromJust"
| constant Option.is_none \<rightharpoonup> (Haskell) "MaybeExt.isNothing"

text \<open>To use the Maybe monad, we need to import it, so we add a shim to do so in every module.\<close>
code_printing code_module MaybeExt \<rightharpoonup> (Haskell)
  \<open>module MaybeExt(fromJust, isNothing) where
     import Data.Maybe(fromJust, isNothing);\<close>

text \<open>The default export setup will create a cycle of module imports, so we roll most of the
  theories into one module when exporting to Haskell to prevent this.\<close>
code_identifier
  code_module Stream \<rightharpoonup> (Haskell) Prover
| code_module Prover \<rightharpoonup> (Haskell) Prover
| code_module Export \<rightharpoonup> (Haskell) Prover
| code_module Option \<rightharpoonup> (Haskell) Prover
| code_module MaybeExt \<rightharpoonup> (Haskell) Prover
| code_module Abstract_Completeness \<rightharpoonup> (Haskell) Prover

text \<open>Finally, we define an executable version of the prover using the code interpretation from the
  framework, and a version where the list of terms is initially empty.\<close>
definition \<open>secavTreeCode \<equiv> i.mkTree (\<lambda>r s. Some (effect r s)) rules\<close>
definition \<open>secavProverCode \<equiv> \<lambda>z . secavTreeCode ([], z)\<close>

text \<open>We then export this version of the prover into Haskell.\<close>
export_code open secavProverCode in Haskell

end