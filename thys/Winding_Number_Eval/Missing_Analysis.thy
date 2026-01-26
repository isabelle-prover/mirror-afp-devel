(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in analysis\<close>

theory Missing_Analysis
  imports "HOL-Analysis.Analysis"
begin  

subsection \<open>More about paths\<close>
   
lemma pathfinish_offset[simp]:
  "pathfinish (\<lambda>t. g t - z) = pathfinish g - z"
  unfolding pathfinish_def by simp 
    
lemma pathstart_offset[simp]:
  "pathstart (\<lambda>t. g t - z) = pathstart g - z"
  unfolding pathstart_def by simp
    
lemma pathimage_offset[simp]:
  fixes g :: "_ \<Rightarrow> 'b::topological_group_add"
  shows "p \<in> path_image (\<lambda>t. g t - z) \<longleftrightarrow> p+z \<in> path_image g " 
unfolding path_image_def by (auto simp:algebra_simps)
  
lemma path_offset[simp]:
 fixes g :: "_ \<Rightarrow> 'b::topological_group_add"
 shows "path (\<lambda>t. g t - z) \<longleftrightarrow> path g"
unfolding path_def
proof 
  assume "continuous_on {0..1} (\<lambda>t. g t - z)" 
  hence "continuous_on {0..1} (\<lambda>t. (g t - z) + z)"
    using continuous_on_add continuous_on_const by blast 
  then show "continuous_on {0..1} g" by auto
qed (auto intro:continuous_intros)   
   
end
