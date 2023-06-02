theory infnorm

imports 
  Main
  "Jordan_Normal_Form.Matrix"
  "LLL_Basis_Reduction.Norms"
begin

section \<open>Maximum Norm\<close>
text \<open>The $\ell_\infty$ norm on vectors is exactly the maximum of the absolute value 
  of all entries.\<close>

lemma linf_norm_vec_Max:
  "\<parallel>v\<parallel>\<^sub>\<infinity> = Max (insert 0 {\<bar>v$i\<bar> | i. i< dim_vec v})"
proof (induct v)
  case (vCons a v)
  have "Missing_Lemmas.max_list (map abs (list_of_vec (vCons a v)) @ [0]) =
    Missing_Lemmas.max_list ((\<bar>a\<bar>) # (map abs (list_of_vec v) @ [0]))" by auto
  also have "\<dots> = max (\<bar>a\<bar>) (\<parallel>v\<parallel>\<^sub>\<infinity>)" unfolding linf_norm_vec_def by (cases v, auto)
  also have "\<dots> = max (\<bar>a\<bar>) (Max (insert 0 {\<bar>v$i\<bar> | i. i< dim_vec v}))" using vCons by auto
  also have "\<dots> = Max (insert (\<bar>a\<bar>) (insert 0 {\<bar>v$i\<bar> | i. i< dim_vec v}))" by auto
  also have "\<dots> = Max (insert 0 (insert (\<bar>a\<bar>) {\<bar>v$i\<bar> | i. i< dim_vec v}))"
    by (simp add: insert_commute)
  also have "insert (\<bar>a\<bar>){\<bar>v$i\<bar> | i. i< dim_vec v} = 
    {\<bar>(vCons a v)$i\<bar> | i. i< dim_vec (vCons a v)}"
  proof (safe, goal_cases)
    case (1 x)
    show ?case by (subst exI[of _ "0"], auto)
  next
    case (2 x i)
    then show ?case by (subst exI[of _ "Suc i"]) 
      (use vec_index_vCons_Suc[of a v i, symmetric] in \<open>auto\<close>)
  next
    case (3 x i)
    then show ?case by (subst vec_index_vCons) (subst exI[of _ "i-1"], auto)
  qed
  finally show ?case unfolding linf_norm_vec_def by auto
qed auto


end