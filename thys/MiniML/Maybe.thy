(* Title:     MiniML/Maybe.thy
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Universal error monad"

theory Maybe
imports Main
begin

definition
  option_bind :: "['a option, 'a => 'b option] => 'b option" where
  "option_bind m f = (case m of None => None | Some r => f r)"

syntax "_option_bind" :: "[pttrns,'a option,'b] => 'c" (\<open>(_ := _;//_)\<close> 0)
syntax_consts "_option_bind" == option_bind
translations "P := E; F" == "CONST option_bind E (\<lambda>P. F)"


\<comment> \<open>constructor laws for @{text option_bind}\<close>
lemma option_bind_Some: "option_bind (Some s) f = (f s)"
  by (simp add: option_bind_def)

lemma option_bind_None: "option_bind None f = None"
  by (simp add: option_bind_def)

declare option_bind_Some [simp] option_bind_None [simp]

\<comment> \<open>expansion of @{text option_bind}\<close>
lemma split_option_bind: "P(option_bind res f) =  
          ((res = None \<longrightarrow> P None) \<and> (\<forall>s. res = Some s \<longrightarrow> P(f s)))"
  unfolding option_bind_def
  by (rule option.split)

lemma split_option_bind_asm: "P(option_bind res f) =  
          (~ ((res = None \<and> \<not> P None) \<or> (\<exists>s. res = Some s \<and> \<not> P(f s))))"
  unfolding option_bind_def
  by (rule option.split_asm)

lemma option_bind_eq_None [simp]:
    "((option_bind m f) = None) = ((m=None) | (\<exists>p. m = Some p \<and> f p = None))"
  by (simp split: split_option_bind)

end
