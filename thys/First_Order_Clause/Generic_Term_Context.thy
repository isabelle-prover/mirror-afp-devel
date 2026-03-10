theory Generic_Term_Context
  imports 
    Generic_Term
    Generic_Context
begin

locale term_context_interpretation = 
  term_interpretation where Fun = Fun +
  context_interpretation where More = More and fun_sym = fun_sym\<^sub>c and extra = extra\<^sub>c
for
  Fun :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 't" and
  More :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 'c \<Rightarrow> 't list \<Rightarrow> 'c" and
  fun_sym\<^sub>c extra\<^sub>c +
assumes apply_context [simp]: "\<And>f e ls c rs t. (More f e ls c rs)\<langle>t\<rangle> = Fun f e (ls @ c\<langle>t\<rangle> # rs)"
begin

lemma is_subterm_obtain_context [elim]:
  assumes "t' \<unlhd> t"
  obtains c where "t = c\<langle>t'\<rangle>"
  using assms 
proof (induction t' t arbitrary: thesis rule: is_subterm_eq.induct)
  case (subterm_refl t)

  then show ?case 
    by (metis apply_hole)
next
  case (subterm t' t t'')
 
  then obtain c where t': "t' = c\<langle>t''\<rangle>" 
    by auto

  obtain ts1 ts2 where "subterms t = ts1 @ t' # ts2"
    by (meson split_list_first subterm.hyps(1))

  show ?case
    by (metis t' append_is_Nil_conv apply_context interpret_term is_var_subterms split_list_first
        subterm.hyps(1) subterm.prems)
qed

end

locale hole_position =
  smaller_subterms where subterms = subterms +
  "context" where apply_context = apply_context
for 
  subterms :: "'t \<Rightarrow> 't list" and
  apply_context :: "'c \<Rightarrow> 't \<Rightarrow> 't" +
fixes hole_position :: "'c \<Rightarrow> position"
assumes 
  subterm_at_hole_position [simp]: "\<And>c t. c\<langle>t\<rangle> !\<^sub>t hole_position c = t" and
  hole_position_in_positions [intro]: "\<And>c t. hole_position c \<in> positions (c\<langle>t\<rangle>)"

locale context_at = hole_position where apply_context = apply_context 
  for apply_context :: "'c \<Rightarrow> 't \<Rightarrow> 't" +
  fixes context_at :: "'t \<Rightarrow> position \<Rightarrow> 'c" (infixl \<open>!\<^sub>c\<close> 64)
  assumes
    context_at_root [simp]: "t !\<^sub>c [] = \<box>" and
    context_at_hole [simp]: "\<And>c t. c\<langle>t\<rangle> !\<^sub>c (hole_position c) = c" and
    context_at_subterm_at [simp]: "\<And>p t. p \<in> positions t \<Longrightarrow> (t !\<^sub>c p)\<langle>t !\<^sub>t p\<rangle> = t"
begin

abbreviation replace_at (\<open>_\<lbrakk>_ := _\<rbrakk>\<close> [70, 0, 50] 70) where
  "replace_at t p s \<equiv> (t !\<^sub>c p)\<langle>s\<rangle>"

lemma replace_at_hole [simp]: "c\<langle>t\<rangle>\<lbrakk>hole_position c := t'\<rbrakk> = c\<langle>t'\<rangle>"
  by simp

lemma replace_at_id [simp]: "t\<lbrakk>[] := t\<rbrakk> = t"
  by simp

end

locale replace_at_subterm =
  context_at + 
  term_interpretation +
  assumes
    replace_at_subterm [simp]: 
      "\<And>f e ts i p t. Fun f e ts\<lbrakk>i # p := t\<rbrakk> =
        Fun f e (take i ts @ ts ! i\<lbrakk>p := t\<rbrakk> # drop (Suc i) ts)"

end
