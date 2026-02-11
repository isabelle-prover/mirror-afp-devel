theory IsaFoR_Ground_Context
  imports
    Generic_Term_Context
    IsaFoR_Abstract_Context
    IsaFoR_Ground_Term
begin

type_synonym 'f gcontext = "('f, 'f gterm) actxt"

abbreviation apply_ground_context (\<open>_\<langle>_\<rangle>\<^sub>G\<close> [1000, 0] 1000) where
  "c\<langle>t\<rangle>\<^sub>G \<equiv> GFun\<langle>c;t\<rangle>"

fun context_at\<^sub>G :: "'f gterm \<Rightarrow> pos \<Rightarrow> 'f gcontext" where
  "context_at\<^sub>G t [] = \<box>" |
  "context_at\<^sub>G (GFun f ts) (i # ps) = More f (take i ts) (context_at\<^sub>G (ts!i) ps) (drop (Suc i) ts)"

interpretation gcontext: term_context_interpretation where
  subterms = gargs and fun_sym = groot_sym and extra = "\<lambda>_. ()" and is_var = is_var and
  Fun = "\<lambda>f _. GFun f" and
  hole = \<box> and apply_context = apply_ground_context and compose_context = "(\<circ>\<^sub>c)" and
  More = "\<lambda>f _. More f" and fun_sym\<^sub>c = fun_sym\<^sub>c and extra\<^sub>c = "\<lambda>_. ()" and subterms\<^sub>l = subterms\<^sub>l and
  subcontext = subcontext and subterms\<^sub>r = subterms\<^sub>r
proof unfold_locales
  fix c :: "'f gcontext" and t t' 
  assume "c\<langle>t\<rangle>\<^sub>G = c\<langle>t'\<rangle>\<^sub>G" 

  then show "t = t'"
    by (induction c) auto
next
  fix c :: "'f gcontext"

  show "c \<noteq> \<box> \<longleftrightarrow> (\<exists>f e ls c' rs. c = More f ls c' rs)"
    by (metis actxt.distinct(1) actxt.exhaust)
qed (simp_all add: intp_actxt_compose)

interpretation gcontext: replace_at_subterm where  
  subterms = gargs and fun_sym = groot_sym and extra = "\<lambda>_. ()" and is_var = is_var and
  Fun = "\<lambda>f _. GFun f" and size = size and
  hole = \<box> and apply_context = apply_ground_context and compose_context = "(\<circ>\<^sub>c)" and
  hole_position = hole_pos and context_at = context_at\<^sub>G
proof unfold_locales
  fix c :: "'f gcontext" and t

  show "gterm.subterm_at c\<langle>t\<rangle>\<^sub>G (hole_pos c) = t"
    by (induction c) auto

  show "hole_pos c \<in> gterm.positions c\<langle>t\<rangle>\<^sub>G"
    by (induction c) auto

  show "context_at\<^sub>G c\<langle>t\<rangle>\<^sub>G (hole_pos c) = c"
    by (induction c) auto
next
  fix p and t :: "'f gterm"
  assume "p \<in> gterm.positions t"

  then show "(context_at\<^sub>G t p)\<langle>gterm.subterm_at t p\<rangle>\<^sub>G = t"
    by (induction t p rule: context_at\<^sub>G.induct) (auto simp: Cons_nth_drop_Suc)
qed auto

end
