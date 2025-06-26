theory Babai_Algorithm_Updated
  imports
    LLL_Basis_Reduction.LLL_Impl
    "HOL.Archimedean_Field"
    "HOL-Analysis.Inner_Product"

begin

fun calculate_c:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> nat => int" where
  "calculate_c s L1 n  = round ((s \<bullet> (L1!((dim_vec s) - n))) / (sq_norm_vec (L1!((dim_vec s) - n))))"

fun update_s:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> rat vec list \<Rightarrow> nat \<Rightarrow> rat vec" where
  "update_s sn M Mt n = ((rat_of_int (calculate_c sn Mt n)) \<cdot>\<^sub>v M!((dim_vec sn) - n)) "

fun babai_help:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> rat vec list \<Rightarrow> nat \<Rightarrow> rat vec" where
	"babai_help s M Mt 0 = s" |
	"babai_help s M Mt (Suc n) = (let B = (babai_help s M Mt n) in B - (update_s B M Mt (Suc n)))"

text \<open>This assumes an LLL-reduced input and outputs a short vector of the form $v+t$, with $v \in L$ \<close>
fun babai_of_LLL :: "rat vec \<Rightarrow> rat vec list \<Rightarrow> rat vec" where
	"babai_of_LLL s M = babai_help s M (gram_schmidt (dim_vec s) M) (dim_vec s)" 

text \<open>This begins with a non-reduced basis and outputs a vector $v$ in $L$ which is close to $t$\<close>
fun full_babai :: "int vec list \<Rightarrow> rat vec \<Rightarrow> rat \<Rightarrow> int vec" 
  where "full_babai fs target \<alpha> = 
        map_vec int_of_rat
          (babai_of_LLL
            (uminus target)
            (LLL.RAT (LLL_Impl.reduce_basis \<alpha> fs))
          + target)"

end


