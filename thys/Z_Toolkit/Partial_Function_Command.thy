section \<open> Partial Function Command \<close>

theory Partial_Function_Command
  imports Function_Toolkit
  keywords "zfun" :: "thy_decl_block" and "precondition" "postcondition"
begin

definition pfun_spec :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Zpfun> 'b" where
"pfun_spec P Q = (\<lambda> x | P x \<and> (\<exists> y. Q x y) \<bullet> SOME y. Q x y)"

lemma pfun_spec_app_eqI [intro]: "\<lbrakk> P x; \<And> y. Q x y \<longleftrightarrow> y = f x \<rbrakk> \<Longrightarrow> (pfun_spec P Q)(x)\<^sub>p = f x"
  by (simp add: pfun_spec_def, subst pabs_apply, auto)

ML_file \<open>Partial_Function_Command.ML\<close>

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword zfun} "define Z-like partial functions" 
    (Zfun_Command.zfun_parser >> (Toplevel.theory o Zfun_Command.compile_zfun));
\<close>

end