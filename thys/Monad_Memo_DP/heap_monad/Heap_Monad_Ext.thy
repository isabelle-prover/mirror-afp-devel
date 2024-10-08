subsection \<open>Heap Monad\<close>

theory Heap_Monad_Ext
  imports "HOL-Imperative_HOL.Imperative_HOL"
begin

definition fun_app_lifted :: "('a \<Rightarrow> 'b Heap) Heap \<Rightarrow> 'a Heap \<Rightarrow> 'b Heap" where
  "fun_app_lifted f\<^sub>T x\<^sub>T \<equiv> do { f \<leftarrow> f\<^sub>T; x \<leftarrow> x\<^sub>T; f x }"

bundle heap_monad_syntax begin

notation fun_app_lifted (infixl \<open>.\<close> 999)
type_synonym ('a, 'b) fun_lifted = "'a \<Rightarrow> 'b Heap" (\<open>_ ==H\<Longrightarrow> _\<close> [3,2] 2)
type_notation Heap (\<open>[_]\<close>)

notation Heap_Monad.return (\<open>\<langle>_\<rangle>\<close>)
notation (ASCII) Heap_Monad.return (\<open>(#_#)\<close>)
notation Transfer.Rel (\<open>Rel\<close>)

end

context includes heap_monad_syntax begin

qualified lemma return_app_return:
  "\<langle>f\<rangle> . \<langle>x\<rangle> = f x"
  unfolding fun_app_lifted_def return_bind ..

qualified lemma return_app_return_meta:
  "\<langle>f\<rangle> . \<langle>x\<rangle> \<equiv> f x"
  unfolding return_app_return .

qualified definition if\<^sub>T :: "bool Heap \<Rightarrow> 'a Heap \<Rightarrow> 'a Heap \<Rightarrow> 'a Heap" where
  "if\<^sub>T b\<^sub>T x\<^sub>T y\<^sub>T \<equiv> do {b \<leftarrow> b\<^sub>T; if b then x\<^sub>T else y\<^sub>T}"
end

end
