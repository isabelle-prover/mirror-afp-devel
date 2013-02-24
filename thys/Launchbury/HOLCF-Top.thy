theory "HOLCF-Top"
imports 
  "~~/src/HOL/HOLCF/HOLCF"
begin

default_sort type

class Top_cpo = cpo +
  assumes most: "\<exists>x. \<forall>y. y \<sqsubseteq> x"
begin
  
  definition top :: "'a"
    where "top = (THE x. \<forall>y. y \<sqsubseteq> x)"
  
  notation (xsymbols)
    top ("\<top>")
  
  lemma maximal [iff]: "x \<sqsubseteq> \<top>"
  unfolding top_def
  apply (rule the1I2)
  apply (rule ex_ex1I)
  apply (rule most)
  apply (blast intro: below_antisym)
  apply simp
  done
end

default_sort cpo

lemma above_top_iff [simp]: "(\<top> \<sqsubseteq> x) = (x = \<top>)"
by (simp add: po_eq_conv)

lemma eq_top_iff: "(x = \<top>) = (\<top> \<sqsubseteq> x)"
by simp

lemma topI: "\<top> \<sqsubseteq> x ==> x = \<top>"
by (subst eq_top_iff)

end
