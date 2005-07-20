
header {* The Formalization of JML Operators *}

theory JML = StoreProperties :

text {* JML operators that are to be used in Hoare formulae can be formalized here.
*}

constdefs
  instanceof :: "Value \<Rightarrow> Javatype \<Rightarrow> bool"  ("_ @instanceof _")
  "instanceof v t \<equiv> typeof v \<le> t"

end
