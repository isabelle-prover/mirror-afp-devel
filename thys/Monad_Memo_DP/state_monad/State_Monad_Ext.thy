subsection \<open>State Monad\<close>

theory State_Monad_Ext
  imports "HOL-Library.State_Monad"
begin

definition fun_app_lifted :: "('M,'a \<Rightarrow> ('M, 'b) state) state \<Rightarrow> ('M,'a) state \<Rightarrow> ('M,'b) state" where
  "fun_app_lifted f\<^sub>T x\<^sub>T \<equiv> do { f \<leftarrow> f\<^sub>T; x \<leftarrow> x\<^sub>T; f x }"

bundle state_monad_syntax begin

notation fun_app_lifted (infixl \<open>.\<close> 999)
type_synonym ('a,'M,'b) fun_lifted = "'a \<Rightarrow> ('M,'b) state" (\<open>_ ==_\<Longrightarrow> _\<close> [3,1000,2] 2)
type_synonym ('a,'b) dpfun = "'a ==('a\<rightharpoonup>'b)\<Longrightarrow> 'b" (infixr \<open>\<Rightarrow>\<^sub>T\<close> 2)
type_notation state (\<open>[_| _]\<close>)

notation State_Monad.return (\<open>\<langle>_\<rangle>\<close>)
notation (ASCII) State_Monad.return (\<open>(#_#)\<close>)
notation Transfer.Rel (\<open>Rel\<close>)

end

context includes state_monad_syntax begin

qualified lemma return_app_return:
  "\<langle>f\<rangle> . \<langle>x\<rangle> = f x"
  unfolding fun_app_lifted_def bind_left_identity ..

qualified lemma return_app_return_meta:
  "\<langle>f\<rangle> . \<langle>x\<rangle> \<equiv> f x"
  unfolding return_app_return .

qualified definition if\<^sub>T :: "('M, bool) state \<Rightarrow> ('M, 'a) state \<Rightarrow> ('M, 'a) state \<Rightarrow> ('M, 'a) state" where
  "if\<^sub>T b\<^sub>T x\<^sub>T y\<^sub>T \<equiv> do {b \<leftarrow> b\<^sub>T; if b then x\<^sub>T else y\<^sub>T}"
end

end
