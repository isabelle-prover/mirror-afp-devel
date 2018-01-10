theory Refine_String
imports
  Autoref_Misc
begin

subsection \<open>Setup for literals\<close>
context begin interpretation autoref_syn .
lemma [autoref_itype]: "STR x ::\<^sub>i I"
  and [autoref_op_pat_def]: "STR x \<equiv> OP (STR x) :::\<^sub>i I"
  and [autoref_rules]: "(STR x, OP (STR x) ::: Id) \<in> Id"
  by simp_all
end

subsection \<open>Setup for characters\<close>
context begin interpretation autoref_syn .
lemma [autoref_itype]: "Char x ::\<^sub>i I"
  and [autoref_op_pat_def]: "Char x \<equiv> OP (Char x) :::\<^sub>i I"
  and [autoref_rules]: "(Char x, OP (Char x) ::: Id) \<in> Id"
  by simp_all
end

subsection \<open>setup for strings\<close>

consts i_string :: interface
consts i_char :: interface

abbreviation "char_rel \<equiv> Id::(char\<times>_) set"
definition "string_rel \<equiv> \<langle>char_rel\<rangle>list_rel::(string\<times>_) set"
lemmas [autoref_rel_intf] = REL_INTFI[of string_rel i_string]
lemmas [autoref_rel_intf] = REL_INTFI[of char_rel i_char]

definition op_str_Nil::"string" where [simp]: "op_str_Nil = Nil"
definition op_str_Cons::"char \<Rightarrow> string \<Rightarrow> string" where [simp]: "op_str_Cons = Cons"
definition op_str_append::"string \<Rightarrow> string \<Rightarrow> string" where [simp]: "op_str_append = (@)"

context begin interpretation autoref_syn .
lemma
  shows [autoref_itype]:
    "op_str_Nil ::\<^sub>i i_string"
    "op_str_Cons ::\<^sub>i i_char \<rightarrow>\<^sub>i i_string \<rightarrow>\<^sub>i i_string"
    "op_str_append ::\<^sub>i i_string \<rightarrow>\<^sub>i i_string \<rightarrow>\<^sub>i i_string"
  and [autoref_rules]:
    "(Nil, op_str_Nil::string) \<in> string_rel"
    "(Cons, op_str_Cons) \<in> char_rel \<rightarrow> string_rel \<rightarrow> string_rel"
    "((@), op_str_append) \<in> string_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  and [autoref_op_pat_def]:
    "Nil \<equiv> op_str_Nil"
    "Cons \<equiv> op_str_Cons"
    "(@) \<equiv> op_str_append"
  by (simp_all add: string_rel_def)
end

end
