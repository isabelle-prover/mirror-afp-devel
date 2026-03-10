theory IsaFoR_Abstract_Context
  imports 
    First_Order_Terms.Subterm_and_Context
    Generic_Context
begin

fun fun_sym\<^sub>c :: "('f, 't) actxt \<Rightarrow> 'f" where
  "fun_sym\<^sub>c (More f _ _ _) = f"

fun subterms\<^sub>l :: "('f, 't) actxt \<Rightarrow> 't list" where
  "subterms\<^sub>l (More _ ls _ _) = ls"

fun subcontext :: "('f, 't) actxt \<Rightarrow> ('f, 't) actxt" where
  "subcontext (More _ _ c _) = c"

fun subterms\<^sub>r :: "('f, 't) actxt \<Rightarrow> 't list" where
  "subterms\<^sub>r (More _ _ _ rs) = rs"

interpretation abstract_context: smaller_subcontext where
  hole = \<box> and subcontext = subcontext and size = size
proof unfold_locales
  fix c :: "('f, 't) actxt"
  assume "c \<noteq> \<box>"

  then show "size (subcontext c) < size c"
    by (cases c) auto
qed

end
