theory Babai_Algorithm

imports LLL_Basis_Reduction.LLL
	"HOL.Archimedean_Field"
  "HOL-Analysis.Inner_Product"

begin
fun calculate_c:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> nat => int" where
  "calculate_c s L1 n  = round ((s \<bullet> (L1!( (dim_vec s) - n ) ) ) / (sq_norm_vec (L1!( (dim_vec s) - n ) ) ) )"

fun update_s:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> rat vec list \<Rightarrow> nat \<Rightarrow> rat vec" where
  "update_s sn M Mt n = ( (rat_of_int (calculate_c sn Mt n)) \<cdot>\<^sub>v M!((dim_vec sn)-n)) "


fun Babai_Help:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> rat vec list \<Rightarrow> nat \<Rightarrow> rat vec" where
	"Babai_Help s M Mt 0 = s" |
	"Babai_Help s M Mt (Suc n) = (let B= (Babai_Help s M Mt n) in B- (update_s B M Mt (Suc n)) )"

definition Babai:: "rat vec \<Rightarrow> rat vec list \<Rightarrow> rat vec" where
	"Babai s M = Babai_Help s M (gram_schmidt (dim_vec s) M) (dim_vec s)" 
(*Pretty sure from looking at the original code that this is unnormalized, rather than normalized Gram-Schmidt*)


(*
value "gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]"

value "update_s (vec_of_list [1::rat,2])  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 2"

value "update_s (vec_of_list [1::rat,2])  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 1"

value "update_s (update_s (vec_of_list [1::rat,2])  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 1) [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 1"

value "Babai_Help (vec_of_list [1::rat,2])  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 0"

value "Babai_Help (vec_of_list [1::rat,2])  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 1"

value "Babai_Help (update_s (vec_of_list [1::rat,2])  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 1)  [(vec_of_list [2::rat,3]),(vec_of_list [3,4])] (gram_schmidt 2 [(vec_of_list [2::rat,3]),(vec_of_list [3,4])]) 0"

*)
end


