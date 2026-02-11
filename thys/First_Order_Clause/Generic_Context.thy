theory Generic_Context
  imports Context_Notation
begin

locale "context" =
  context_notation +
  assumes
    compose_context_iff [simp]: "\<And>(c :: 'c) c' (t :: 't). (c \<circ>\<^sub>c c')\<langle>t\<rangle> = c\<langle>c'\<langle>t\<rangle>\<rangle>" and
    compose_hole [simp]: "\<And>c. \<box> \<circ>\<^sub>c c = c" "\<And>c. c \<circ>\<^sub>c \<box> = c" and
    apply_hole [simp]: "\<And>t. \<box>\<langle>t\<rangle> = t" and
    apply_context_eq: "\<And>c t t'. c\<langle>t\<rangle> = c\<langle>t'\<rangle> \<Longrightarrow> t = t'"

locale context_interpretation = "context" where apply_context = apply_context 
  for apply_context :: "'c \<Rightarrow> 't \<Rightarrow> 't" +
fixes 
  More :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 'c \<Rightarrow> 't list \<Rightarrow> 'c" and
  fun_sym :: "'c \<Rightarrow> 'f" and 
  extra :: "'c \<Rightarrow> 'e" and
  subterms\<^sub>l :: "'c \<Rightarrow> 't list" and
  subcontext :: "'c \<Rightarrow> 'c" and
  subterms\<^sub>r :: "'c \<Rightarrow> 't list"
assumes
  context_fun_sym [simp]: "\<And>f e ls c rs. fun_sym (More f e ls c rs) = f" and
  context_extra [simp]: "\<And>f e ls c rs. extra (More f e ls c rs) = e" and
  subterms\<^sub>l [simp]: "\<And>f e ls c rs. subterms\<^sub>l (More f e ls c rs) = ls" and
  subcontext [simp]: "\<And>f e ls c rs. subcontext (More f e ls c rs) = c" and
  subterms\<^sub>r [simp]: "\<And>f e ls c rs. subterms\<^sub>r (More f e ls c rs) = rs" and
  context_destruct: "\<And>c. c \<noteq> \<box> \<longleftrightarrow> (\<exists>f e ls c' rs. c = More f e ls c' rs)" and
  context_inject [intro]: 
    "More f\<^sub>1 e\<^sub>1 ls\<^sub>1 c\<^sub>1' rs\<^sub>1 = More f\<^sub>2 e\<^sub>2 ls\<^sub>2 c\<^sub>2' rs\<^sub>2 \<Longrightarrow> 
      f\<^sub>1 = f\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2 \<and> ls\<^sub>1 = ls\<^sub>2 \<and> c\<^sub>1' = c\<^sub>2' \<and> rs\<^sub>1 = rs\<^sub>2" and
  compose_context [simp]: "More f e ls c rs \<circ>\<^sub>c c' = More f e ls (c \<circ>\<^sub>c c') rs"
begin

lemma interpretation_not_hole [intro]: "More f e ls c' rs \<noteq> \<box>"
  using context_destruct
  by fast

end

locale smaller_subcontext =
  fixes hole :: 'c and size :: "'c \<Rightarrow> nat" and subcontext :: "'c \<Rightarrow> 'c"
  assumes subcontext_smaller: "\<And>c. c \<noteq> hole \<Longrightarrow> size (subcontext c) < size c"

end
