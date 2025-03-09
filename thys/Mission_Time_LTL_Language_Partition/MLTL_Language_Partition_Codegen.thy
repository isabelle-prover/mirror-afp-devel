theory MLTL_Language_Partition_Codegen

imports MLTL_Language_Partition_Algorithm Show.Shows_Literal

begin

section \<open>Pretty Parsing\<close>

fun nat_to_string:: "nat \<Rightarrow> string" where 
"nat_to_string n = String.explode (Shows_Literal.showl n)"

fun mltl_to_literal_aux:: "nat mltl \<Rightarrow> string" where 
  "mltl_to_literal_aux True\<^sub>m = ''true''"
| "mltl_to_literal_aux False\<^sub>m = ''false''"
| "mltl_to_literal_aux (Prop\<^sub>m (p)) = ''p''@(nat_to_string p)"
| "mltl_to_literal_aux (Not\<^sub>m \<phi>) = ''(!''@(mltl_to_literal_aux \<phi>)@'')''"
| "mltl_to_literal_aux (\<phi> And\<^sub>m \<psi>) = ''('' @ (mltl_to_literal_aux \<phi>) @ '' & '' @ (mltl_to_literal_aux \<psi>) @ '')''"
| "mltl_to_literal_aux (\<phi> Or\<^sub>m \<psi>) = ''('' @ (mltl_to_literal_aux \<phi>) @ '' | '' @ (mltl_to_literal_aux \<psi>) @ '')''"
| "mltl_to_literal_aux (G\<^sub>m [a,b] \<phi>) = ''(G['' @ (nat_to_string a) @ '','' @ (nat_to_string b) @ ''] '' @ (mltl_to_literal_aux \<phi>) @ '')''"
| "mltl_to_literal_aux (F\<^sub>m [a,b] \<phi>) = ''(F['' @ (nat_to_string a) @ '','' @ (nat_to_string b) @ ''] '' @ (mltl_to_literal_aux \<phi>) @ '')''"
| "mltl_to_literal_aux (\<phi> R\<^sub>m [a,b] \<psi>) = ''('' @ (mltl_to_literal_aux \<phi>) @ '' R['' @ (nat_to_string a) @ '','' @ (nat_to_string b) @ ''] '' @ (mltl_to_literal_aux \<psi>) @ '')''"
| "mltl_to_literal_aux (\<phi> U\<^sub>m [a,b] \<psi>) = ''('' @ (mltl_to_literal_aux \<phi>) @ '' U['' @ (nat_to_string a) @ '','' @ (nat_to_string b) @ ''] '' @ (mltl_to_literal_aux \<psi>) @ '')''"

fun mltl_to_literal:: "nat mltl \<Rightarrow> String.literal"
  where "mltl_to_literal \<phi> = String.implode (mltl_to_literal_aux \<phi>)"

value "mltl_to_literal ((Prop\<^sub>m (3) And\<^sub>m True\<^sub>m) U\<^sub>m[3,4] False\<^sub>m) = 
       STR ''((p3 & true) U[3,4] false)''"

section "Code Export"

export_code LP_mltl mltl_to_literal in Haskell module_name LP_mltl

end
