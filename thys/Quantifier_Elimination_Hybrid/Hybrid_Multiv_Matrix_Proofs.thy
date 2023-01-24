(* This file includes proofs for the multivariate 
  matrix equation construction from Hybrid_Multiv_Matrix.thy.
*)


theory Hybrid_Multiv_Matrix_Proofs
  imports
    "BenOr_Kozen_Reif.Matrix_Equation_Construction"
    Multiv_Tarski_Query
    "BenOr_Kozen_Reif.Renegar_Proofs"
    Hybrid_Multiv_Matrix
    Hybrid_Multiv_Algorithm
    Renegar_Modified

begin

hide_const "BKR_Decision.And"
hide_const "BKR_Decision.Or"

hide_const "UnivPoly.eval"

subsection "Connect multivariate Tarski queries to univariate"
lemma pull_out_pairs_length:
  shows "length (pull_out_pairs qs Is) = length Is"
  using pull_out_pairs.simps by force

lemma construct_NofI_M_subset_prop:
  assumes "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"
  shows "set init_assumps \<subseteq> set assumps"
proof -
  have "(assumps, tq) \<in> set (map construct_NofI_single_M (construct_NofI_R_spmods p init_assumps qs1 qs2))"
    using assms
    by auto 
  then obtain mid_assumps tq_list where tuple_prop2: "(assumps, tq) = construct_NofI_single_M (mid_assumps, tq_list)"
    "(mid_assumps, tq_list) \<in> set (construct_NofI_R_spmods p init_assumps qs1 qs2)"
    by force
  have s1: "mid_assumps = assumps"
    using tuple_prop2(1)
    by simp 
  have s2: "set init_assumps \<subseteq> set mid_assumps"
    using tuple_prop2(2) spmods_multiv_assum_acc
    by (metis construct_NofI_R_spmods_def)
  then show "set init_assumps \<subseteq> set assumps"
    using s1 s2
    by blast 
qed

subsection "Connect multivariate RHS vector to univariate"

lemma construct_rhs_vector_rec_M_subset_prop_len1:
  assumes "(assumps, rhs_list) \<in> set (construct_rhs_vector_rec_M p init_assumps [a])"
  shows "set init_assumps \<subseteq> set assumps"
proof -
  obtain qs1 qs2 where a_prop: "a = (qs1, qs2)"
    using prod.exhaust by blast 
  have tuple_prop: "(assumps, rhs_list) \<in> set (map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) (construct_NofI_M p init_assumps qs1 qs2))"
    using a_prop assms by auto
  then obtain tq where tq_prop: "rhs_list = [tq]"
    by auto
  let ?ell = "( map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) (construct_NofI_M p init_assumps qs1 qs2))"
  have tuple_in_list: "(assumps, rhs_list) \<in> set ?ell"
    using tuple_prop 
    by auto
  then have "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"  
    using tq_prop
    by (smt (verit, best) imageE list.inject list.set_map old.prod.case old.prod.simps(1) prod.collapse) 
  then have "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"
    using tq_prop
    by metis 
  then have "(assumps, tq) \<in> set(map construct_NofI_single_M 
      (construct_NofI_R_spmods p init_assumps qs1 qs2))"
    by force
  then have "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"
    using \<open>(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)\<close> by force
  then show ?thesis using construct_NofI_M_subset_prop
    by blast
qed

lemma construct_rhs_vector_rec_M_subset_prop:
  assumes "(assumps, rhs_list) \<in> set (construct_rhs_vector_rec_M p init_assumps qs_list)"
  shows "set init_assumps \<subseteq> set assumps"
  using assms
proof (induct qs_list  arbitrary: assumps rhs_list init_assumps)
  case Nil
  then show ?case
    using construct_rhs_vector_rec_M.simps by auto
next
  case (Cons a qs_list)
  obtain qs1 qs2 where a_prop: "a = (qs1, qs2)"
    using Cons.prems Cons.hyps prod.exhaust
    by fastforce 
  { assume *: "qs_list = []"
    then have "set init_assumps \<subseteq> set assumps" using construct_rhs_vector_rec_M_subset_prop_len1 
        Cons.prems
      by blast 
  }
  moreover   { assume *: "length qs_list \<ge> 1"
    then obtain v va where qs_list_prop: "qs_list = v # va"
      by (metis One_nat_def Suc_le_length_iff)
    let ?TQ_list = "construct_NofI_M p init_assumps qs1 qs2"
    have "(assumps, rhs_list) \<in> set (construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#qs_list))"
      using Cons.prems(1) * a_prop by auto
    then have "(assumps, rhs_list) \<in> set (concat ((map (\<lambda>(new_assumps, tq). 
    (let rec = construct_rhs_vector_rec_M p new_assumps qs_list in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)) ?TQ_list)))"
      using * a_prop qs_list_prop
      by (simp add: split_def) 
    then obtain new_assumps tq where tq_prop: "(new_assumps,tq) \<in> set (?TQ_list)"
      "(assumps, rhs_list) \<in> set (let rec = construct_rhs_vector_rec_M p new_assumps qs_list in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)"
      by auto
    then obtain rhs_rest where rhs_list_prop: "rhs_list = tq#rhs_rest"
      "(assumps, rhs_rest) \<in> set (construct_rhs_vector_rec_M p new_assumps qs_list)"
      by auto
    then have s1: "set new_assumps \<subseteq> set assumps"
      using Cons.hyps
      by auto 
    have s2: "set init_assumps \<subseteq> set new_assumps"
      using construct_NofI_M_subset_prop tq_prop(1) 
      by auto
    have "set init_assumps \<subseteq> set assumps"
      using s1 s2 
      by auto
  }
  ultimately  show ?case
    using Cons.prems
    by (metis length_0_conv less_one linorder_neqE_nat nat_less_le rel_simps(47)) 
qed

lemma construct_rhs_vector_rec_M_univariate:
  (* Intuitively, assumps really contains all of the assumptions that we care about *)
  assumes rhs_list_is: "(assumps, rhs_list) \<in> set(construct_rhs_vector_rec_M p init_assumps qs_list)"
  assumes val: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  shows "rhs_list = map (\<lambda>(qs1,qs2).
    (construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1) (eval_mpoly_poly_list val qs2))) qs_list"
  using assms
proof (induct qs_list arbitrary: assumps rhs_list init_assumps)
  case Nil
  then show ?case 
    using construct_rhs_vector_rec_M.simps
    by auto
next
  case (Cons a qs_list)
  obtain qs1 qs2 where a_prop: "a = (qs1, qs2)"
    using Cons.prems Cons.hyps
    using prod.exhaust by blast 
  { assume *: "qs_list = []"
    let ?tq = "construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1) (eval_mpoly_poly_list val qs2)"
    have " (assumps, rhs_list) \<in> set (construct_rhs_vector_rec_M p init_assumps [(qs1, qs2)])"
      using Cons.prems(1) * a_prop by auto
    then have 
      "(assumps, rhs_list) \<in> set (let TQ_list = construct_NofI_M p init_assumps qs1 qs2 in
    map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) TQ_list)"
      by (metis construct_rhs_vector_rec_M.simps(2))
    then have tuple_prop:
      "(assumps, rhs_list) \<in> set ( map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) (construct_NofI_M p init_assumps qs1 qs2))"
      by auto
    then obtain tq where tq_prop: "rhs_list = [tq]"
      by auto
    let ?ell = "( map (\<lambda>(new_assumps, tq). (new_assumps, [tq])) (construct_NofI_M p init_assumps qs1 qs2))"
    have tuple_in_list: "(assumps, rhs_list) \<in> set ?ell"
      using tuple_prop
      by auto
    then have "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"  
      using tq_prop
      by (smt (verit, best) imageE list.inject list.set_map old.prod.case old.prod.simps(1) prod.collapse) 
    then have "(assumps, tq) \<in> set (construct_NofI_M p init_assumps qs1 qs2)"
      using tq_prop
      by metis 
    then have "rhs_list = [construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1) (eval_mpoly_poly_list val qs2)]"
      using construct_NofI_M_univariate_tarski_query[of assumps tq p init_assumps qs1 qs2 val]
        Cons.prems(2) tq_prop
      by auto
    then have "rhs_list =
       map (\<lambda>(qs1, qs2).
               construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1)
                (eval_mpoly_poly_list val qs2))
        [(qs1, qs2)]"
      by auto
    then have "rhs_list =
       map (\<lambda>(qs1, qs2).
               construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1)
                (eval_mpoly_poly_list val qs2))
        (a # qs_list)"
      using * a_prop by auto
  }
  moreover {
    assume *: "qs_list \<noteq> []"
    then obtain v va where qs_list_prop: "qs_list = v # va"
      by (meson neq_Nil_conv)
    let ?tq = "construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1) (eval_mpoly_poly_list val qs2)"
    let ?TQ_list = "construct_NofI_M p init_assumps qs1 qs2"
    have "(assumps, rhs_list) \<in> set (construct_rhs_vector_rec_M p init_assumps ((qs1, qs2)#qs_list))"
      using Cons.prems(1) * a_prop by auto
    then have "(assumps, rhs_list) \<in> set (concat ((map (\<lambda>(new_assumps, tq). 
    (let rec = construct_rhs_vector_rec_M p new_assumps qs_list in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)) ?TQ_list)))"
      using * a_prop qs_list_prop
      by (simp add: split_def) 
    then obtain new_assumps tq where tq_prop: "(new_assumps,tq) \<in> set (?TQ_list)"
      "(assumps, rhs_list) \<in> set (let rec = construct_rhs_vector_rec_M p new_assumps qs_list in
     map (\<lambda>r. (fst r,  tq#snd r)) rec)"
      by auto
    then obtain rhs_rest where rhs_list_prop: "rhs_list = tq#rhs_rest"
      "(assumps, rhs_rest) \<in> set (construct_rhs_vector_rec_M p new_assumps qs_list)"
      by auto
    then have subset: "set new_assumps \<subseteq> set assumps" using
        construct_rhs_vector_rec_M_subset_prop[of assumps rhs_rest p new_assumps qs_list]
      by auto 
    then have val_2: "\<And> p n. (p, n) \<in> set new_assumps \<Longrightarrow> satisfies_evaluation val p n"
      using val
      by (meson Set.basic_monos(7) local.Cons(3)) 
    have tq_is: "tq = ?tq"
      using construct_NofI_M_univariate_tarski_query[of new_assumps tq p init_assumps qs1 qs2 val]
        tq_prop(1) Cons.prems(2) subset
      by blast
    have ih: "rhs_rest =
           map (\<lambda>(qs1, qs2).
                   construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1)
                    (eval_mpoly_poly_list val qs2))
            qs_list"
      using rhs_list_prop Cons.prems(2) val_2
      by (simp add: local.Cons(1))  
    then have "rhs_list =
       map (\<lambda>(qs1, qs2).
               construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1)
                (eval_mpoly_poly_list val qs2))
        (a # qs_list)"
      using a_prop tq_is ih rhs_list_prop
      by simp 
  }
  ultimately have "rhs_list =
       map (\<lambda>(qs1, qs2).
               construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1)
                (eval_mpoly_poly_list val qs2))
        (a # qs_list)"
    by blast
  then show ?case
    by blast 
qed

lemma retrieve_polys_prop:
  assumes "\<And>x. x \<in> set ns \<Longrightarrow> x < length qs"
  shows "(eval_mpoly_poly_list val (retrieve_polys qs ns)) = (retrieve_polys (map (eval_mpoly_poly val) qs) ns)"
  using assms unfolding eval_mpoly_poly_list_def retrieve_polys_def by auto

(* Intuitively, with the assumptions we have, we'll get a unique RHS vector
 i.e. the output of construct_NofI_M gives uniqueness (and matches the univariate
 case) *)
lemma construct_rhs_vector_M_univariate:
  (* Intuitively, assumps really contains all of the assumptions that we care about *)
  assumes rhs_vec_is: "(assumps, rhs_vec) \<in> set(construct_rhs_vector_M p init_assumps qs Is)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes well_def_subsets:  "\<And> Is1 Is2 n. (Is1, Is2) \<in> set Is \<Longrightarrow> 
    (n \<in> set Is1 \<or> n \<in> set Is2) \<Longrightarrow> n < length qs"
  shows "rhs_vec = construct_rhs_vector_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) Is"
proof  - 
  have "(assumps, rhs_vec) \<in> set (map (\<lambda>res. (fst res, vec_of_list (snd res))) (construct_rhs_vector_rec_M p init_assumps (pull_out_pairs qs Is)))"
    using rhs_vec_is unfolding construct_rhs_vector_M_def by auto 
  then have "\<exists>rhs_list. rhs_vec = vec_of_list rhs_list \<and> (assumps, rhs_list) \<in> set (map (\<lambda>res. (fst res, snd res)) (construct_rhs_vector_rec_M p init_assumps (pull_out_pairs qs Is)))"
    by auto
  then obtain rhs_list where rhs_list_prop: "rhs_vec = vec_of_list rhs_list \<and> (assumps, rhs_list) \<in> set (map (\<lambda>res. (fst res, snd res)) (construct_rhs_vector_rec_M p init_assumps (pull_out_pairs qs Is)))"
    by auto
  then have rhs_list_char: "rhs_list = map (\<lambda>(qs1,qs2).
    (construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val qs1) (eval_mpoly_poly_list val qs2))) (pull_out_pairs qs Is)"
    using assms construct_rhs_vector_rec_M_univariate
      (* Takes a couple seconds to load*)
    by (smt (verit, del_insts) case_prod_beta map_eq_conv map_idI prod.exhaust_sel)
  have lov_1: "list_of_vec (map_vec
     (\<lambda>(I1, I2).
         construct_NofI_R (eval_mpoly_poly val p) (retrieve_polys (map (eval_mpoly_poly val) qs) I1)
          (retrieve_polys (map (eval_mpoly_poly val) qs) I2))
     (vec_of_list Is)) = map (\<lambda>(I1, I2).
         construct_NofI_R (eval_mpoly_poly val p) (retrieve_polys (map (eval_mpoly_poly val) qs) I1)
          (retrieve_polys (map (eval_mpoly_poly val) qs) I2)) Is"
    by (metis list_vec vec_of_list_map)
  have lov_2: "list_of_vec rhs_vec = rhs_list"
    using rhs_list_prop
    using list_vec by blast 
  let ?rhs_list_var = "map (\<lambda>(I1, I2).
         construct_NofI_R (eval_mpoly_poly val p) (retrieve_polys (map (eval_mpoly_poly val) qs) I1)
          (retrieve_polys (map (eval_mpoly_poly val) qs) I2)) Is"
  have rhs_list_is: "rhs_list = ?rhs_list_var"
  proof - 
    have len_is1: "length (pull_out_pairs qs Is) = length Is"
      by simp
    then have "length rhs_list = length Is"
      using rhs_list_char
      by auto
    have len_is2: "length ?rhs_list_var = length Is"
      by auto
    have "\<And>n. n  < length Is \<Longrightarrow> rhs_list ! n = ?rhs_list_var ! n"
    proof - 
      fix n
      assume *: "n  < length Is"
      then obtain Is1 Is2 where Is_prop: "Is ! n = (Is1, Is2)"
        by fastforce
      then have "(pull_out_pairs qs Is) ! n = ((retrieve_polys qs Is1), (retrieve_polys qs Is2))"
        using "*" by force
      then have nth_1: "rhs_list ! n =  construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val (retrieve_polys qs Is1)) (eval_mpoly_poly_list val (retrieve_polys qs Is2))"     
        using rhs_list_char
        by (simp add: "*" len_is1) 
      have nth_2: "map (\<lambda>(I1, I2).
            construct_NofI_R (eval_mpoly_poly val p) (retrieve_polys (map (eval_mpoly_poly val) qs) I1)
             (retrieve_polys (map (eval_mpoly_poly val) qs) I2)) Is ! n
      = construct_NofI_R (eval_mpoly_poly val p) (retrieve_polys (map (eval_mpoly_poly val) qs) Is1)
             (retrieve_polys (map (eval_mpoly_poly val) qs) Is2)"
        using Is_prop
        by (simp add: "*")
      have ret_poly1: "(eval_mpoly_poly_list val (retrieve_polys qs Is1)) = (retrieve_polys (map (eval_mpoly_poly val) qs) Is1)"
        unfolding retrieve_polys_def eval_mpoly_poly_list_def 
        using well_def_subsets retrieve_polys_prop Is_prop       
        by (metis "*" eval_mpoly_poly_list_def in_set_conv_nth retrieve_polys_def)
      have ret_poly2: "(eval_mpoly_poly_list val (retrieve_polys qs Is2)) = (retrieve_polys (map (eval_mpoly_poly val) qs) Is2)"
        unfolding retrieve_polys_def eval_mpoly_poly_list_def 
        using well_def_subsets retrieve_polys_prop Is_prop
        by (metis "*" eval_mpoly_poly_list_def in_set_conv_nth retrieve_polys_def)
      have "construct_NofI_R (eval_mpoly_poly val p) (eval_mpoly_poly_list val (retrieve_polys qs Is1)) (eval_mpoly_poly_list val (retrieve_polys qs Is2))
        = construct_NofI_R (eval_mpoly_poly val p) (retrieve_polys (map (eval_mpoly_poly val) qs) Is1)
             (retrieve_polys (map (eval_mpoly_poly val) qs) Is2)"
        using ret_poly1 ret_poly2 
        by auto
      then show "rhs_list ! n = ?rhs_list_var ! n"
        using nth_1 nth_2 by auto 
    qed
    then show ?thesis
      using len_is1 len_is2
      by (metis \<open>length rhs_list = length Is\<close> nth_equalityI)
  qed
  then show ?thesis
    using rhs_list_is lov_2 lov_1
    unfolding construct_rhs_vector_R_def
    using rhs_list_prop by force 
qed

subsection "Connect multivariate LHS vector to univariate"

lemma solve_for_lhs_vector_M_univariate:
  assumes lhs_in: "(assumps, lhs_vec) \<in> set (solve_for_lhs_M p init_assumps qs subsets matr)"
  assumes val: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes well_def_subsets:  "\<And> Is1 Is2 n. (Is1, Is2) \<in> set subsets \<Longrightarrow> 
    (n \<in> set Is1 \<or> n \<in> set Is2) \<Longrightarrow> n < length qs"
  shows "lhs_vec = solve_for_lhs_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) subsets matr"
proof - 
  let ?lhs_univ = "solve_for_lhs_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) subsets matr"
  have "(assumps, lhs_vec) \<in> set(map (\<lambda>rhs. (fst rhs, solve_for_lhs_single_M p qs subsets matr (snd rhs))) (construct_rhs_vector_M p init_assumps qs subsets))"
    using lhs_in
    using solve_for_lhs_M_def by auto 
  then obtain rhs where rhs_prop: "rhs \<in> set(construct_rhs_vector_M p init_assumps qs subsets)"
    "(assumps, lhs_vec) = (fst rhs, solve_for_lhs_single_M p qs subsets matr (snd rhs))"
    by auto
  then have snd_is: "snd rhs = construct_rhs_vector_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) subsets"
    using construct_rhs_vector_M_univariate
    by (metis assms(2) fst_conv prod.collapse well_def_subsets)  
  have "fst rhs = assumps" using rhs_prop
    by force 
  have "?lhs_univ = mult_mat_vec (matr_option (dim_row matr) (mat_inverse_var matr)) (snd rhs)"
    using snd_is
    by (simp add: solve_for_lhs_R_def) 
  then show ?thesis
    using rhs_prop(2) unfolding solve_for_lhs_single_M_def 
    by auto
qed

subsection "Connect multivariate reduction step to univariate"

lemma reduce_system_single_M_univariate:
  assumes inset: "(assumps, mat_eq) \<in> set(reduce_system_single_M p qs (init_assumps, init_mat_eq))"
  assumes val: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes init: "init_mat_eq = (m, (subs, signs))"
  assumes well_def_subsets:  "\<And> Is1 Is2 n. (Is1, Is2) \<in> set subs \<Longrightarrow> 
    (n \<in> set Is1 \<or> n \<in> set Is2) \<Longrightarrow> n < length qs"
  shows "mat_eq = reduce_system_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) qs), init_mat_eq)"
proof - 
  have "(assumps, mat_eq) \<in> set (map (\<lambda>lhs. (fst lhs, reduction_step_R m signs subs (snd lhs))) (solve_for_lhs_M p init_assumps qs subs m))"
    using inset
    using assms(3)
    by force
  then obtain lhs where lhs_prop: "lhs \<in> set (solve_for_lhs_M p init_assumps qs subs m)"
    "(assumps, mat_eq) = (fst lhs, reduction_step_R m signs subs (snd lhs))"
    by auto
  then have "snd lhs = solve_for_lhs_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) subs m"
    using solve_for_lhs_vector_M_univariate assms
    by (smt (verit, best) prod.exhaust_sel prod.simps(1))
  then have "mat_eq = reduction_step_R m signs subs (solve_for_lhs_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) subs m)"
    using lhs_prop
    by force 
  then show ?thesis 
    using init
    using reduce_system_R.simps by presburger 
qed

lemma reduce_system_M_univariate:
  assumes "(assumps, mat_eq) \<in> set(reduce_system_M p qs input_list)"
  assumes val: "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes val_qs: "val_qs = (map (eval_mpoly_poly val) qs)"
  assumes all_subsets_well_def:  "\<And> init_assumps init_mat_eq Is1 Is2 n subs m signs. 
   (init_assumps, (m, (subs, signs))) \<in> set input_list \<Longrightarrow>
   (Is1, Is2) \<in> set subs \<Longrightarrow> (n \<in> set Is1 \<or> n \<in> set Is2) \<Longrightarrow> n < length qs"
  obtains acc mss where
    "(acc,mss) \<in> set (input_list)" 
    "mat_eq = reduce_system_R (eval_mpoly_poly val p) (val_qs,mss)"
proof -
  have "(assumps, mat_eq) \<in> set(concat (map (reduce_system_single_M p qs) input_list))"
    by (metis assms(1) reduce_system_M.simps)
  then obtain init_assumps init_m init_subs init_signs where
    mat_eq_prop: 
    "(init_assumps, (init_m, (init_subs, init_signs))) \<in> set input_list"
    "(assumps, mat_eq) \<in> set (reduce_system_single_M p qs (init_assumps, (init_m, (init_subs, init_signs))))"
    by auto
  then have well_def_subsets:  "\<And> Is1 Is2 n. (Is1, Is2) \<in> set init_subs \<Longrightarrow> 
    (n \<in> set Is1 \<or> n \<in> set Is2) \<Longrightarrow> n < length qs"
    using all_subsets_well_def
    by blast
  then have mat_eq_is: "mat_eq = reduce_system_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) qs), (init_m, (init_subs, init_signs)))"
    using reduce_system_single_M_univariate mat_eq_prop assms(2) by blast 
  then show ?thesis using mat_eq_prop
    using assms(3) that by blast
qed

lemma base_case_info_M_well_def:
  assumes "(init_assumps, (m, (subs, signs))) \<in> set base_case_info_M"
  assumes "(Is1, Is2) \<in> set subs"
  assumes "n \<in> set Is1 \<or> n \<in> set Is2"
  shows "n < 1"
proof -
  have "(m, (subs, signs)) = base_case_info_R" using assms(1)
    unfolding base_case_info_M_def using Renegar_Algorithm.base_case_info_R_def Renegar_Algorithm.base_case_info_R_def
    by simp
  then have s: "subs = [([], []),([0], []),([], [0])]" unfolding base_case_info_R_def
    by auto
  have "(n \<in> set Is1 \<or> n \<in> set Is2)" using assms(3)
    by (simp add: in_set_member)
  thus ?thesis using assms(2) unfolding s by auto
qed

subsection "Connect multivariate combining systems to univariate"

(* Well-definedness property to satisfy induction hypothesis *)
lemma base_case_with_assumps_info_M_well_def:
  assumes "(init_assumps, (m, (subs, signs))) \<in> set (base_case_info_M_assumps a)"
  assumes "(Is1, Is2) \<in> set subs"
  assumes "n \<in> set Is1 \<or> n \<in> set Is2"
  shows "n < 1"
proof -
  have "(m, (subs, signs)) = base_case_info_R" using assms(1)
    unfolding base_case_info_M_assumps_def 
    using Renegar_Algorithm.base_case_info_R_def Renegar_Algorithm.base_case_info_R_def
    by auto
  then have s: "subs = [([], []),([0], []),([], [0])]" unfolding base_case_info_R_def
    by auto
  have "(n \<in> set Is1 \<or> n \<in> set Is2)" using assms(3)
    by (simp add: in_set_member)
  thus ?thesis using assms(2) unfolding s by auto
qed

lemma concat_map_in_set:
  assumes "x \<in> set (concat (map f ls))"
  shows "\<exists>i < length ls. x \<in> set (f (ls ! i))"
  using assms
  by (smt (verit, best) in_set_conv_nth length_map map_nth_eq_conv nth_concat_split) 

lemma combine_systems_R_snd:
  assumes "length qs1 = length new_qs1"
  shows "snd (combine_systems_R p (qs1, sys1) (qs2, sys2)) = 
    snd (combine_systems_R new_p (new_qs1, sys1) (new_qs2, sys2))"
proof - 
  obtain  m1 sub1 sgn1 where sys1: "sys1 = (m1, sub1, sgn1)"
    using prod_cases3 by blast
  obtain  m2 sub2 sgn2 where sys2: "sys2 = (m2, sub2, sgn2)"
    using prod_cases3 by blast 
  have h1: "snd (combine_systems_R p (qs1, sys1) (qs2, sys2)) = 
    snd (smash_systems_R p qs1 qs2 sub1 sub2 sgn1 sgn2 m1 m2)"
    using sys1 sys2 by auto 
  have h2: "snd (combine_systems_R new_p (new_qs1, sys1) (new_qs2, sys2)) = 
    snd (smash_systems_R new_p new_qs1 new_qs2 sub1 sub2 sgn1 sgn2 m1 m2)"
    using sys1 sys2 by auto 
  show ?thesis
    using h1 h2 assms unfolding smash_systems_R_def by auto
qed

subsection "Subset Properties"

lemma construct_rhs_vector_M_subset_prop:
  assumes "(assumps, rhs_vec) \<in> set (construct_rhs_vector_M p init_assumps qs subsets)"
  shows "set init_assumps \<subseteq> set assumps"
proof - 
  obtain rhs_list where "(assumps, rhs_list) \<in> set  (construct_rhs_vector_rec_M p init_assumps (pull_out_pairs qs subsets))" 
    "rhs_vec = vec_of_list rhs_list"
    using assms unfolding construct_rhs_vector_M_def by auto
  then show ?thesis
    using construct_rhs_vector_rec_M_subset_prop by auto
qed

lemma construct_lhs_vector_rec_M_subset_prop:
  assumes "(assumps, lhs_list) \<in> set (solve_for_lhs_M p init_assumps qs subsets matr)"
  shows "set init_assumps \<subseteq> set assumps"
proof - 
  obtain rhs_vec where "(assumps, rhs_vec) \<in> set (construct_rhs_vector_M p init_assumps qs subsets)" 
    "lhs_list = matr_option (dim_row matr) (mat_inverse_var matr) *\<^sub>v rhs_vec "
    using assms unfolding solve_for_lhs_M_def solve_for_lhs_single_M_def 
    by auto 
  then show ?thesis
    using construct_rhs_vector_M_subset_prop[of assumps] by auto
qed

lemma reduce_system_single_M_subset_prop:
  assumes "(assumps, mat_eq) \<in> set (reduce_system_single_M p qs (init_assumps, (m,subs,signs)))"
  shows "set init_assumps \<subseteq> set assumps"
proof - 
  obtain lhs_vec where "(assumps, lhs_vec) \<in> set (solve_for_lhs_M p init_assumps qs subs m)" 
    "mat_eq = reduction_step_R m signs subs lhs_vec"
    using assms 
    by (auto) 
  then show ?thesis
    using construct_lhs_vector_rec_M_subset_prop[of assumps] 
    by auto
qed


lemma calculate_data_assumps_M_subset:
  assumes "(assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps)"
  shows "set init_assumps \<subseteq> set assumps"
  using assms
proof (induction "length qs" arbitrary: qs assumps mat_eq rule: less_induct)
  case less
  {assume *: "length qs = 0"
    then have "(assumps, mat_eq) \<in> set (map (\<lambda>(assumps,(a,(b,c))). (assumps, (a,b,map (drop 1) c))) (reduce_system_M p [1] (base_case_info_M_assumps init_assumps)))"
      using less.prems by auto 
    then obtain a b c where "(assumps, (a, (b, c))) \<in> set (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))"
      by auto 
    then have "(assumps, (a, (b, c))) \<in> set (concat (map (reduce_system_single_M p [1]) [(init_assumps, base_case_info_R)]))"
      unfolding base_case_info_M_assumps_def
      using Renegar_Algorithm.base_case_info_R_def Renegar_Algorithm.base_case_info_R_def 
      by (auto) 
    then have "(assumps, (a, (b, c))) \<in> set( reduce_system_single_M p [1] (init_assumps, base_case_info_R))"
      by auto
    then have "set init_assumps \<subseteq> set assumps"
      unfolding base_case_info_R_def
      using reduce_system_single_M_subset_prop[of assumps "(a, (b, c))" p "[1]" init_assumps]
      by auto
  }
  moreover {assume *: "length qs = 1"
    then have "(assumps, mat_eq) \<in> set (reduce_system_M p qs (base_case_info_M_assumps init_assumps))"
      using less.prems by auto 
    then obtain a b c where "(assumps, (a, (b, c))) \<in> set (reduce_system_M p qs (base_case_info_M_assumps init_assumps))"
      by (smt (verit) prod.sel(2) prod_cases4)
    then have "(assumps, (a, (b, c))) \<in> set (concat (map (reduce_system_single_M p qs) [(init_assumps, base_case_info_R)]))"
      unfolding base_case_info_M_assumps_def 
      using Renegar_Algorithm.base_case_info_R_def Renegar_Algorithm.base_case_info_R_def 
      by (auto)
    then have "(assumps, (a, (b, c))) \<in> set( reduce_system_single_M p qs (init_assumps, base_case_info_R))"
      by auto
    then have "set init_assumps \<subseteq> set assumps"
      unfolding base_case_info_R_def
      using reduce_system_single_M_subset_prop[of assumps "(a, (b, c))" p qs init_assumps]
      by auto
  }
  moreover {assume *: "length qs > 1"
    let ?len = "length qs"
    let ?q1 = "take (?len div 2) qs"
    let ?left = "calculate_data_assumps_M p ?q1 init_assumps"
    let ?q2 = "drop (?len div 2) qs"
    let ?right = "calculate_data_assumps_M p ?q2 init_assumps"
    let ?comb = "combine_systems_M p ?q1 ?left ?q2 ?right"
    have len_q1_less: "length ?q1 < length qs"
      using * by auto
    have inset_red: "(assumps, mat_eq) \<in> set(reduce_system_M p (fst ?comb) (snd ?comb))"
      using * less.prems
      by (smt (verit, best) calculate_data_assumps_M.simps less_one nat_less_le not_one_less_zero)
    have "fst ?comb = qs"
      by auto
    then have "(assumps, mat_eq) \<in> set(reduce_system_M p qs (snd ?comb))"
      using inset_red 
      by auto
    then obtain assm_pre m_pre subs_pre signs_pre where assumps_reduce:
      "(assm_pre, (m_pre, subs_pre, signs_pre)) \<in> set (snd ?comb)"
      "(assumps, mat_eq) \<in> set(reduce_system_single_M p qs (assm_pre, (m_pre, subs_pre, signs_pre)))"
      by (metis concat_map_in_set find_consistent_signs_at_roots_single_M.cases nth_mem reduce_system_M.simps)
    then obtain meq1 meq2 assm1 assm2 where subsystems:
      "(assm1, meq1) \<in> set (calculate_data_assumps_M p ?q1 init_assumps)"
      "(assm2, meq2) \<in> set (calculate_data_assumps_M p ?q2 init_assumps)"
      "(assm_pre, (m_pre, subs_pre, signs_pre)) = combine_systems_single_M p ?q1 (assm1, meq1) ?q2 (assm2, meq2)"
      by auto (* Takes a second to load *)
    then have assm_pre: "assm_pre = assm1@assm2" 
      by auto
    have "set init_assumps \<subseteq> set assm1"
      using less.hyps[of ?q1] less.prems subsystems(1) len_q1_less
      by auto (* Takes a second to load *)
    then have "set init_assumps \<subseteq> set assm_pre" 
      using assm_pre by auto 
    then have "set init_assumps \<subseteq> set assumps"
      using assumps_reduce(2) reduce_system_single_M_subset_prop[of assumps mat_eq p qs assm_pre m_pre subs_pre signs_pre]
      by auto
  }
  ultimately show ?case
    by (meson less_one linorder_neqE_nat)
qed

lemma extract_signs_M_subset:
  assumes "(assumps, signs) \<in> set (extract_signs (calculate_data_assumps_M p qs init_assumps))"
  shows "set init_assumps \<subseteq> set assumps"
proof - 
  obtain mat_eq where 
    "(assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps)"
    "signs = snd (snd mat_eq)"
    using assms by auto
  then show ?thesis 
    using calculate_data_assumps_M_subset[of assumps mat_eq p qs init_assumps]
    by auto
qed

subsection "Top-level Results: Connect calculate data methods to univariate"

(* Well-definedness property to satisfy induction hypothesis *)
lemma all_list_constr_R_matches_well_def:
  assumes welldef: "all_list_constr_R subs (length q)"
  shows "(Is1, Is2) \<in> set (subs) \<Longrightarrow> n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow> n < length q"
proof -
  assume inset: "(Is1, Is2) \<in> set (subs)"
  assume inlist: "n \<in> set Is1 \<or> n \<in> set Is2"
  have welldef_var: "\<forall>x. x \<in> set subs \<longrightarrow>
        list_constr (fst x) (length q) \<and> list_constr (snd x) (length q)"
    using welldef  unfolding all_list_constr_R_def
    by (simp add: in_set_member)
  have "(Is1, Is2) \<in> set subs"
    using inset by auto 
  then have "(\<forall>x\<in>set Is1. x < length q) \<and> (\<forall>x\<in>set Is2. x < length q)"
    using welldef_var
    by (simp add: Ball_set list_constr_def)
  then show "n < length q"
    using inlist
    by metis
qed

lemma calculate_data_M_univariate:
  assumes mat_eq: "(assumps, mat_eq) \<in> set (calculate_data_M p qs)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes p_nonzero: "eval_mpoly_poly val p \<noteq> 0"
  shows "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = mat_eq"
  using assms
proof (induct "length qs" arbitrary: val p mat_eq assumps qs rule: less_induct)
  case (less qs val p mat_eq assumps) 
  have "length qs = 0 \<or> length qs = 1 \<or> length qs > 1"
    by (meson less_one nat_neq_iff)
  moreover {assume *: "length qs = 0"
    let ?m = "(mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]])"
    let ?subs = "[([], []),([0], []),([], [0])]"
    let ?signs = "[[1],[0],[-1]]"
    let ?eval_p = "eval_mpoly_poly val p"
    have mat_eq_in: "(assumps, mat_eq) \<in> set (calculate_data_M p [])"
      using * less.prems(1) by auto 
    let ?map_base = "map (\<lambda>(assumps,(a,(b,c))). (assumps, (a,b,map (drop 1) c))) (reduce_system_M p [1] base_case_info_M)"
    have "(assumps, mat_eq) \<in> set ?map_base"
      using mat_eq_in 
      by auto
    then obtain a1 b1 c1 where a1b1c1_prop:
      "(assumps, (a1, (b1, c1))) \<in> set (reduce_system_M p [1] base_case_info_M)"
      "mat_eq = (a1, (b1, map (drop 1) c1))"
      by auto
    have base_case_well_def: "\<And>init_assumps init_mat_eq Is1 Is2 n subs m signs.
        (init_assumps, m, subs, signs) \<in> set base_case_info_M \<Longrightarrow>
        (Is1, Is2) \<in> set subs \<Longrightarrow> n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow> n < length [1]"
      using base_case_info_M_well_def by auto
    have map_is: "[1] = map (eval_mpoly_poly val) [1] "
      unfolding eval_mpoly_poly_def eval_mpoly_def 
      by auto
   then have "\<exists>acc mss. (acc,mss) \<in> set (base_case_info_M) \<and> (a1, (b1, c1)) = reduce_system_R (eval_mpoly_poly val p) ([1],mss)"
      using reduce_system_M_univariate[of "assumps" "(a1, b1, c1)" p "[1]" base_case_info_M val "[1]"]
        a1b1c1_prop less(3) base_case_well_def
      apply (auto) 
      by metis
    then obtain acc mss where a1b1c1_connect:
      "(acc,mss) \<in> set (base_case_info_M)" 
      "(a1, (b1, c1)) = reduce_system_R (eval_mpoly_poly val p) ([1],mss)"
      by auto
    then have mss_is: "mss = base_case_info_R"
      unfolding base_case_info_M_def 
      by auto
    obtain a b c where abc_prop: "(a, b, c) = reduction_step_R ?m ?signs ?subs (solve_for_lhs_R ?eval_p [1] ?subs ?m)"
      by (metis reduction_step_R.simps)
    then have "(a, b, c) = (a1, b1, c1)"
      using abc_prop a1b1c1_prop
      by (metis a1b1c1_connect(2) base_case_info_R_def mss_is reduce_system_R.simps) 
    then have mat_eq_is: "(a, b, map (drop (Suc 0)) c) = mat_eq"
      using a1b1c1_prop(2) by (auto) 
    have "qs = [] \<Longrightarrow> mat_eq = (a, b, map (drop (Suc 0)) c) \<Longrightarrow>
      (case reduce_system_R (eval_mpoly_poly val p) ([1], base_case_info_R) of
      (a, b, c) \<Rightarrow> (a, b, map (drop (Suc 0)) c)) = (a, b, map (drop (Suc 0)) c) "
      using abc_prop unfolding base_case_info_R_def
      using  old.prod.case reduce_system_R.simps
      by (smt (verit, ccfv_SIG))
    then have "calculate_data_R ?eval_p (map (eval_mpoly_poly val) qs)= mat_eq"
      using * mat_eq_is
      by simp 
  }
  moreover {assume *: "length qs = 1"
    have meq: "(assumps, mat_eq) \<in> set (reduce_system_M p qs base_case_info_M)"
      using "*" le_eq_less_or_eq less(2) one_neq_zero by auto
    have **: "\<And>init_assumps init_mat_eq Is1 Is2 n subs m signs.
      (init_assumps, m, subs, signs) \<in> set base_case_info_M \<Longrightarrow>
      (Is1, Is2) \<in> set subs \<Longrightarrow>
      n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow>
      n < length qs" unfolding *
      using base_case_info_M_well_def
      by meson
    from reduce_system_M_univariate[OF meq less(3), of " map (eval_mpoly_poly val)
   qs"]
    obtain acc mss where ams: "(acc,mss) \<in> set base_case_info_M" 
      "mat_eq = reduce_system_R (eval_mpoly_poly val p)
      (map (eval_mpoly_poly val) qs, mss)"
      using "**" by blast
    then have "mss = base_case_info_R" unfolding base_case_info_M_def 
      by auto
    then have "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = mat_eq"
      using ams * by simp
  }
    (* Inductive case: progress by breaking down, using IH, then piecing back together.
      It's the reduction of a combination of two smaller matrix equation pieces. *)
  moreover {assume *: "length qs  > 1"
    have inset: "(assumps, mat_eq) \<in> set (calculate_data_M p qs)"
      using less.prems(1) by auto 
    let ?len = "length qs"
    let ?q1 = "take (?len div 2) qs"
    let ?q2 = "drop (?len div 2) qs"
    let ?left = "calculate_data_M p ?q1"
    let ?right = "calculate_data_M p ?q2"
    let ?comb = "combine_systems_M p ?q1 ?left ?q2 ?right"
    let ?eval_p = "(eval_mpoly_poly val p)"
    let ?eval_q1 = "(map (eval_mpoly_poly val) ?q1)"
    let ?eval_q2 = "(map (eval_mpoly_poly val) ?q2)"
    have map_q1: "map (eval_mpoly_poly val) ?q1 = 
      (take (length (map (eval_mpoly_poly val) qs) div 2) (map (eval_mpoly_poly val) qs))"
      by (auto simp add: take_map) 
    have map_q2: "map (eval_mpoly_poly val) ?q2 = 
      (drop (length (map (eval_mpoly_poly val) qs) div 2) (map (eval_mpoly_poly val) qs))"
      by (auto simp add: drop_map) 
    have "fst ?comb = qs" 
      by auto
    then have "(assumps, mat_eq) \<in> set (reduce_system_M p qs (snd ?comb))"
      using inset *
      by (smt (verit) calculate_data_M.simps less_numeral_extra(2) less_one nat_less_le)
    then have "(assumps, mat_eq) \<in> set (concat (map (reduce_system_single_M p qs) (snd ?comb)))"
      by (metis reduce_system_M.simps)
    then have "\<exists>sys. sys \<in> set (snd ?comb) \<and> (assumps, mat_eq) \<in> set(reduce_system_single_M p qs sys)"
      using concat_map_in_set in_set_member
      by (metis nth_mem) 
    then obtain a_pre me_pre  where reduce_prop: "(a_pre, me_pre) \<in> set (snd ?comb)"
      "(assumps, mat_eq) \<in> set(reduce_system_single_M p qs (a_pre, me_pre))"
      by fastforce 
    then obtain a1 me1 a2 me2 where mes_prop: "(a1, me1) \<in> set ?left"
      "(a2, me2) \<in> set ?right"
      "(a_pre, me_pre) = combine_systems_single_M p ?q1 (a1, me1) ?q2 (a2, me2)"
      by auto
    then have a_pre: "a_pre = a1@a2" 
      by auto 
    have lengt: "length qs div 2 \<ge> 1"
      using * by auto
    then have len_q1: "length ?q1 < length qs"
      by auto
    have len_q2: "length ?q2 < length qs"
      using lengt by auto
    obtain mat_pre subs_pre signs_pre where me_decomp:
      "me_pre = (mat_pre,subs_pre,signs_pre)"
      using mes_prop
      using prod_cases3 by blast 
    then have "assumps \<in> set (map fst (solve_for_lhs_M p a_pre qs subs_pre mat_pre))"
      using reduce_prop(2) by auto
    then have "assumps \<in> set (map fst (construct_rhs_vector_M p a_pre qs subs_pre))"
      unfolding solve_for_lhs_M_def by auto
    then obtain a_rhs_list where "(assumps, a_rhs_list)
    \<in> set (construct_rhs_vector_rec_M p a_pre (pull_out_pairs qs subs_pre))"
      unfolding construct_rhs_vector_M_def by auto
    then have a_pre_subset: "set a_pre \<subseteq> set assumps"
      using construct_rhs_vector_rec_M_subset_prop[of assumps _ p a_pre "(pull_out_pairs qs subs_pre)"]
      by auto
    have set_a1: "set a1 \<subseteq> set assumps"
      using a_pre_subset a_pre by auto 
    then have a1_satisfies: "(\<And>p n. (p, n) \<in> set a1 \<Longrightarrow> satisfies_evaluation val p n)"
      using less(3) by blast
    from less.hyps[of ?q1 a1 me1, OF len_q1 mes_prop(1) a1_satisfies]
    have me1_ind: "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q1) = me1"
      using less(4) by blast
    have set_a2: "set a2 \<subseteq> set assumps"
      using a_pre_subset a_pre by auto 
    then have a2_satisfies: "(\<And>p n. (p, n) \<in> set a2 \<Longrightarrow> satisfies_evaluation val p n)"
      using less(3) by blast
    from less.hyps[of ?q2 a2 me2, OF len_q2 mes_prop(2) a2_satisfies]
    have me2_ind: "calculate_data_R ?eval_p (map (eval_mpoly_poly val) ?q2) = me2"
      using less(4) by blast
    have "a_pre = a1 @ a2 \<Longrightarrow> me_pre =
      snd (combine_systems_R p (take (length qs div 2) qs, me1)
            (drop (length qs div 2) qs, me2)) \<Longrightarrow>
      snd (combine_systems_R p (take (length qs div 2) qs, me1)
            (drop (length qs div 2) qs, me2)) =
      snd (combine_systems_R (eval_mpoly_poly val p)
            (map (eval_mpoly_poly val) (take (length qs div 2) qs), me1)
            (map (eval_mpoly_poly val) (drop (length qs div 2) qs), me2))"
      using combine_systems_R_snd
      by (metis length_map)
    then have me_pre: "me_pre = snd (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2))"
      using mes_prop(3)
      by (auto)
    obtain mat_pre1 subs_pre1 signs_pre1 where me1_decomp:
      "me1 = (mat_pre1,subs_pre1,signs_pre1)"
      using prod_cases3 by blast
    obtain mat_pre2 subs_pre2 signs_pre2 where me2_decomp:
      "me2 = (mat_pre2,subs_pre2,signs_pre2)"
      using prod_cases3 by blast
    have fst_comb: "fst (combine_systems_R ?eval_p ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2)) = (map (eval_mpoly_poly val) ?q1) @ (map (eval_mpoly_poly val) ?q2)"
    proof -   
      have "fst (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2)) =
        fst (smash_systems_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q1) (map (eval_mpoly_poly val) ?q2) subs_pre1 subs_pre2 signs_pre1 signs_pre2 mat_pre1 mat_pre2)"
        using combining_to_smash_R me1_decomp me2_decomp by force
      then show ?thesis
        unfolding smash_systems_R_def by auto 
    qed
    then have "map (eval_mpoly_poly val) qs = fst (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2))"
      by (metis append_take_drop_id map_append)
    then have me_pre_var:  "(map (eval_mpoly_poly val) qs, me_pre) = (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2))"
      using me_pre by auto 
    have len_hyp: "length (map (eval_mpoly_poly val) qs) > 1"
      using * by auto
    have len_eq: "length (map (eval_mpoly_poly val) qs) = length qs"
      by simp 
    have len_q1_gt0: "length (map (eval_mpoly_poly val) ?q1) > 0"
      using len_hyp len_eq by auto
    have len_q2_gt0: "length (map (eval_mpoly_poly val) ?q2) > 0"
      using len_hyp len_eq by auto
    let ?uni_sys_q1 = "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q1)"
    have sat_props_q1_univ: "satisfies_properties_R ?eval_p (map (eval_mpoly_poly val) ?q1) (get_subsets_R ?uni_sys_q1) (get_signs_R ?uni_sys_q1) (get_matrix_R ?uni_sys_q1)"
      using calculate_data_satisfies_properties_R[of "?eval_p" "(map (eval_mpoly_poly val) (take (length qs div 2) qs))"]
        len_q1_gt0  using less.prems(3) by auto
    let ?uni_sys_q2 = "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q2)"
    have sat_props_q2_univ: "satisfies_properties_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q2) (get_subsets_R ?uni_sys_q2) (get_signs_R ?uni_sys_q2) (get_matrix_R ?uni_sys_q2)"
      using calculate_data_satisfies_properties_R[of "(eval_mpoly_poly val p)" "(map (eval_mpoly_poly val) (drop (length qs div 2) qs))"]
        len_q2_gt0  using less.prems(3)  by auto
    have comb_satisfies: "satisfies_properties_R ?eval_p (?eval_q1@(map (eval_mpoly_poly val) ?q2)) 
  (get_subsets_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) 
  (get_signs_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) 
  (get_matrix_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2)))))"
      using combining_sys_satisfies_properties_R[of ?eval_p ?eval_q1 ?eval_q2] len_q1_gt0 len_q2_gt0 less.prems(3)
        sat_props_q2_univ sat_props_q1_univ
      by auto (* takes a second to load *)
    then have well_def_subs_pre: "all_list_constr_R (get_subsets_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) (length (?eval_q1@?eval_q2))"
      unfolding satisfies_properties_R_def by auto
    have get_subs_pre: "(get_subsets_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) = subs_pre"
      using me_decomp unfolding get_subsets_R_def
      by (metis fst_conv me1_ind me2_ind me_pre_var snd_conv) 
    have well_def: "(\<And>Is1 Is2 n. (Is1, Is2) \<in> set (fst (snd me_pre)) \<Longrightarrow> n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow> n < length qs)"
      using well_def_subs_pre get_subs_pre 
        all_list_constr_R_matches_well_def[of subs_pre]
      by (smt (verit, ccfv_SIG) fst_comb fst_conv get_subsets_R_def length_map me1_ind me2_ind me_pre_var snd_conv) 
    then have reduce_mat_eq: "mat_eq = reduce_system_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) qs), me_pre)"
      using reduce_system_single_M_univariate[OF reduce_prop(2) less.prems(2)]
      by (metis prod.exhaust_sel) 
    let ?eval_qs = "(map (eval_mpoly_poly val) qs)"
    have "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = 
     (let q1 = take ((length ?eval_qs) div 2) ?eval_qs; left = calculate_data_R ?eval_p q1;
         q2 = drop ((length ?eval_qs) div 2) ?eval_qs; right = calculate_data_R ?eval_p q2;
         comb = combine_systems_R ?eval_p (q1,left) (q2,right) in
         reduce_system_R ?eval_p comb)"
      using len_hyp
      by (smt (z3) calculate_data_R.simps less_one nat_less_le semiring_norm(136)) 
    moreover have "... = (let q1 =(map (eval_mpoly_poly val) ?q1);
         left = calculate_data_R (eval_mpoly_poly val p) q1;
         q2 = (map (eval_mpoly_poly val) ?q2);
         right = calculate_data_R (eval_mpoly_poly val p) q2
     in Let (combine_systems_R (eval_mpoly_poly val p) (q1, left) (q2, right))
         (reduce_system_R (eval_mpoly_poly val p))) "
      using map_q1 map_q2 by auto 
    moreover have "... = (let q1 =(map (eval_mpoly_poly val) ?q1); left = me1; 
      q2 = (map (eval_mpoly_poly val) ?q2); right = me2 in
      Let (combine_systems_R (eval_mpoly_poly val p) (q1, left) (q2, right))
         (reduce_system_R (eval_mpoly_poly val p)))"
      unfolding Let_def me1_ind me2_ind by auto
    moreover have "... = mat_eq"
      unfolding Let_def reduce_mat_eq me_pre_var by auto  
    ultimately have "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = mat_eq"
      by auto (* Can take a second to load *)
  }
  ultimately show ?case by blast
qed

lemma calculate_data_M_assumps_univariate:
  assumes mat_eq: "(assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps)"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes p_nonzero: "eval_mpoly_poly val p \<noteq> 0"
  shows "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = mat_eq"
  using assms
proof (induct "length qs" arbitrary: val p mat_eq assumps qs rule: less_induct)
  case (less qs val p mat_eq assumps) 
  have "length qs = 0 \<or> length qs = 1 \<or> length qs > 1"
    by (meson less_one nat_neq_iff)
  moreover {assume *: "length qs = 0"
    let ?m = "(mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]])"
    let ?subs = "[([], []),([0], []),([], [0])]"
    let ?signs = "[[1],[0],[-1]]"
    let ?eval_p = "eval_mpoly_poly val p"
    have mat_eq_in: "(assumps, mat_eq) \<in> set (calculate_data_assumps_M p [] init_assumps)"
      using * less.prems(1) by auto 
    let ?map_base = "map (\<lambda>(assumps,(a,(b,c))). (assumps, (a,b,map (drop 1) c))) (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))"
    have "(assumps, mat_eq) \<in> set ?map_base"
      using mat_eq_in 
      by auto
    then obtain a1 b1 c1 where a1b1c1_prop:
      "(assumps, (a1, (b1, c1))) \<in> set (reduce_system_M p [1] (base_case_info_M_assumps init_assumps))"
      "mat_eq = (a1, (b1, map (drop 1) c1))"
      by auto
    have base_case_well_def: "\<And>in_a init_mat_eq Is1 Is2 n subs m signs.
        (in_a, m, subs, signs) \<in> set (base_case_info_M_assumps init_assumps) \<Longrightarrow>
        (Is1, Is2) \<in> set subs \<Longrightarrow> n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow> n < length [1]"
      using base_case_with_assumps_info_M_well_def  
      by auto
    have " [1] = map (eval_mpoly_poly val) [1] "
      unfolding eval_mpoly_poly_def eval_mpoly_def 
      by auto
    then have "\<exists>acc mss. (acc,mss) \<in> set ((base_case_info_M_assumps init_assumps)) \<and> (a1, (b1, c1)) = reduce_system_R (eval_mpoly_poly val p) ([1],mss)"
      using reduce_system_M_univariate[of "assumps" "(a1, b1, c1)" p "[1]" "(base_case_info_M_assumps init_assumps)" val "[1]"]
        a1b1c1_prop less(3) base_case_well_def apply (auto)
      by metis
    then obtain acc mss where a1b1c1_connect:
      "(acc,mss) \<in>  set ((base_case_info_M_assumps init_assumps))" 
      "(a1, (b1, c1)) = reduce_system_R (eval_mpoly_poly val p) ([1],mss)"
      by auto
    then have mss_is: "mss = base_case_info_R"
      unfolding base_case_info_M_assumps_def 
      using Renegar_Algorithm.base_case_info_R_def Renegar_Algorithm.base_case_info_R_def
      by auto
    obtain a b c where abc_prop: "(a, b, c) = reduction_step_R ?m ?signs ?subs (solve_for_lhs_R ?eval_p [1] ?subs ?m)"
      by (metis reduction_step_R.simps)
    then have "(a, b, c) = (a1, b1, c1)"
      using abc_prop a1b1c1_prop
      by (metis a1b1c1_connect(2) base_case_info_R_def mss_is reduce_system_R.simps) 
    then have mat_eq_is: "(a, b, map (drop (Suc 0)) c) = mat_eq"
      using a1b1c1_prop(2) by (auto) 
    have "(a, b, c) =
  reduction_step_R (mat_of_rows_list 3 [[1, 1, 1], [0, 1, 0], [1, 0, - 1]])
   [[1], [0], [- 1]] [([], []), ([0], []), ([], [0])]
   (solve_for_lhs_R (eval_mpoly_poly val p) [1]
     [([], []), ([0], []), ([], [0])]
     (mat_of_rows_list 3 [[1, 1, 1], [0, 1, 0], [1, 0, - 1]]))"
      using abc_prop
      unfolding base_case_info_R_def
      by (smt (verit) old.prod.case reduce_system_R.simps)
    then have "calculate_data_R ?eval_p (map (eval_mpoly_poly val) qs)= mat_eq"
      using mat_eq_is *
      by (smt (z3) a1b1c1_connect(2) a1b1c1_prop(2) calculate_data_R.simps length_map mss_is split_conv) 
  }
  moreover {assume *: "length qs = 1"
    have meq: "(assumps, mat_eq) \<in> set (reduce_system_M p qs (base_case_info_M_assumps init_assumps))"
      using "*" le_eq_less_or_eq less(2) one_neq_zero by auto
    have **: "\<And>init_assumps init_mat_eq Is1 Is2 n subs m signs.
      (init_assumps, m, subs, signs) \<in> set (base_case_info_M_assumps init_assumps) \<Longrightarrow>
      (Is1, Is2) \<in> set subs \<Longrightarrow>
      n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow>
      n < length qs" unfolding *
      using base_case_with_assumps_info_M_well_def
      by meson
    from reduce_system_M_univariate[OF meq less(3), of " map (eval_mpoly_poly val)
   qs"]
    obtain acc mss where ams: "(acc,mss) \<in> set (base_case_info_M_assumps init_assumps)" 
      "mat_eq = reduce_system_R (eval_mpoly_poly val p)
      (map (eval_mpoly_poly val) qs, mss)"
      using "**"
      apply (auto) 
      by (smt (z3) "*" base_case_with_assumps_info_M_well_def) 
    then have "mss = base_case_info_R" unfolding base_case_info_M_assumps_def 
      using Renegar_Algorithm.base_case_info_R_def Renegar_Algorithm.base_case_info_R_def
      by auto
    then have "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = mat_eq"
      using ams * by simp
  }
    (* Inductive case: progress by breaking down, using IH, then piecing back together.
      It's the reduction of a combination of two smaller matrix equation pieces. *)
  moreover {assume *: "length qs  > 1"
    have inset: "(assumps, mat_eq) \<in> set (calculate_data_assumps_M p qs init_assumps)"
      using less.prems(1) 
      by auto 
    let ?len = "length qs"
    let ?q1 = "take (?len div 2) qs"
    let ?q2 = "drop (?len div 2) qs"
    let ?left = "calculate_data_assumps_M p ?q1 init_assumps"
    let ?right = "calculate_data_assumps_M p ?q2 init_assumps"
    let ?comb = "combine_systems_M p ?q1 ?left ?q2 ?right"
    let ?eval_p = "(eval_mpoly_poly val p)"
    let ?eval_q1 = "(map (eval_mpoly_poly val) ?q1)"
    let ?eval_q2 = "(map (eval_mpoly_poly val) ?q2)"
    have map_q1: "map (eval_mpoly_poly val) ?q1 = 
      (take (length (map (eval_mpoly_poly val) qs) div 2) (map (eval_mpoly_poly val) qs))"
      by (auto simp add: take_map) 
    have map_q2: "map (eval_mpoly_poly val) ?q2 = 
      (drop (length (map (eval_mpoly_poly val) qs) div 2) (map (eval_mpoly_poly val) qs))"
      by (auto simp add: drop_map) 
    have "fst ?comb = qs" 
      by auto
    then have "(assumps, mat_eq) \<in> set (reduce_system_M p qs (snd ?comb))"
      using inset *
      by (smt (z3) calculate_data_assumps_M.simps gr_implies_not0 less_one nat_less_le) 
    then have "(assumps, mat_eq) \<in> set (concat (map (reduce_system_single_M p qs) (snd ?comb)))"
      by (metis reduce_system_M.simps)
    then have "\<exists>sys. sys \<in> set (snd ?comb) \<and> (assumps, mat_eq) \<in> set(reduce_system_single_M p qs sys)"
      using concat_map_in_set in_set_member
      by (metis nth_mem) 
    then obtain a_pre me_pre  where reduce_prop: "(a_pre, me_pre) \<in> set (snd ?comb)"
      "(assumps, mat_eq) \<in> set(reduce_system_single_M p qs (a_pre, me_pre))"
      by fastforce 
    then obtain a1 me1 a2 me2 where mes_prop: "(a1, me1) \<in> set ?left"
      "(a2, me2) \<in> set ?right"
      "(a_pre, me_pre) = combine_systems_single_M p ?q1 (a1, me1) ?q2 (a2, me2)"
      by auto
    then have a_pre: "a_pre = a1@a2" 
      by auto 
    have lengt: "length qs div 2 \<ge> 1"
      using * by auto
    then have len_q1: "length ?q1 < length qs"
      by auto
    have len_q2: "length ?q2 < length qs"
      using lengt by auto
    obtain mat_pre subs_pre signs_pre where me_decomp:
      "me_pre = (mat_pre,subs_pre,signs_pre)"
      using mes_prop
      using prod_cases3 by blast 
    then have "assumps \<in> set (map fst (solve_for_lhs_M p a_pre qs subs_pre mat_pre))"
      using reduce_prop(2) by auto
    then have "assumps \<in> set (map fst (construct_rhs_vector_M p a_pre qs subs_pre))"
      unfolding solve_for_lhs_M_def by auto
    then obtain a_rhs_list where "(assumps, a_rhs_list)
    \<in> set (construct_rhs_vector_rec_M p a_pre (pull_out_pairs qs subs_pre))"
      unfolding construct_rhs_vector_M_def by auto
    then have a_pre_subset: "set a_pre \<subseteq> set assumps"
      using construct_rhs_vector_rec_M_subset_prop[of assumps _ p a_pre "(pull_out_pairs qs subs_pre)"]
      by auto
    have set_a1: "set a1 \<subseteq> set assumps"
      using a_pre_subset a_pre by auto 
    then have a1_satisfies: "(\<And>p n. (p, n) \<in> set a1 \<Longrightarrow> satisfies_evaluation val p n)"
      using less(3) by blast
    from less.hyps[of ?q1 a1 me1, OF len_q1 mes_prop(1) a1_satisfies]
    have me1_ind: "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q1) = me1"
      using less(4) by blast
    have set_a2: "set a2 \<subseteq> set assumps"
      using a_pre_subset a_pre by auto 
    then have a2_satisfies: "(\<And>p n. (p, n) \<in> set a2 \<Longrightarrow> satisfies_evaluation val p n)"
      using less(3) by blast
    from less.hyps[of ?q2 a2 me2, OF len_q2 mes_prop(2) a2_satisfies]
    have me2_ind: "calculate_data_R ?eval_p (map (eval_mpoly_poly val) ?q2) = me2"
      using less(4) by blast
    have me_pre: "me_pre = snd (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2))"
      using mes_prop(3) combine_systems_R_snd length_map
      by (metis combine_systems_single_M.simps snd_conv) 
    obtain mat_pre1 subs_pre1 signs_pre1 where me1_decomp:
      "me1 = (mat_pre1,subs_pre1,signs_pre1)"
      using prod_cases3 by blast
    obtain mat_pre2 subs_pre2 signs_pre2 where me2_decomp:
      "me2 = (mat_pre2,subs_pre2,signs_pre2)"
      using prod_cases3 by blast
    have fst_comb: "fst (combine_systems_R ?eval_p ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2)) = (map (eval_mpoly_poly val) ?q1) @ (map (eval_mpoly_poly val) ?q2)"
    proof -   
      have "fst (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2)) =
        fst (smash_systems_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q1) (map (eval_mpoly_poly val) ?q2) subs_pre1 subs_pre2 signs_pre1 signs_pre2 mat_pre1 mat_pre2)"
        using combining_to_smash_R me1_decomp me2_decomp by force
      then show ?thesis
        unfolding smash_systems_R_def by auto 
    qed
    then have "map (eval_mpoly_poly val) qs = fst (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2))"
      by (metis append_take_drop_id map_append)
    then have me_pre_var:  "(map (eval_mpoly_poly val) qs, me_pre) = (combine_systems_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) ?q1), me1) ((map (eval_mpoly_poly val) ?q2), me2))"
      using me_pre by auto 
    have len_hyp: "length (map (eval_mpoly_poly val) qs) > 1"
      using * by auto
    have len_eq: "length (map (eval_mpoly_poly val) qs) = length qs"
      by simp 
    have len_q1_gt0: "length (map (eval_mpoly_poly val) ?q1) > 0"
      using len_hyp len_eq by auto
    have len_q2_gt0: "length (map (eval_mpoly_poly val) ?q2) > 0"
      using len_hyp len_eq by auto
    let ?uni_sys_q1 = "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q1)"
    have sat_props_q1_univ: "satisfies_properties_R ?eval_p (map (eval_mpoly_poly val) ?q1) (get_subsets_R ?uni_sys_q1) (get_signs_R ?uni_sys_q1) (get_matrix_R ?uni_sys_q1)"
      using calculate_data_satisfies_properties_R[of "?eval_p" "(map (eval_mpoly_poly val) (take (length qs div 2) qs))"]
        len_q1_gt0  using less.prems(3) by auto
    let ?uni_sys_q2 = "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q2)"
    have sat_props_q2_univ: "satisfies_properties_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) ?q2) (get_subsets_R ?uni_sys_q2) (get_signs_R ?uni_sys_q2) (get_matrix_R ?uni_sys_q2)"
      using calculate_data_satisfies_properties_R[of "(eval_mpoly_poly val p)" "(map (eval_mpoly_poly val) (drop (length qs div 2) qs))"]
        len_q2_gt0  using less.prems(3)  by auto
    have comb_satisfies: "satisfies_properties_R ?eval_p (?eval_q1@(map (eval_mpoly_poly val) ?q2)) 
  (get_subsets_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) 
  (get_signs_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) 
  (get_matrix_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2)))))"
      using combining_sys_satisfies_properties_R[of ?eval_p ?eval_q1 ?eval_q2] len_q1_gt0 len_q2_gt0 less.prems(3)
        sat_props_q2_univ sat_props_q1_univ 
      by auto  (* takes a second to load *)
    then have well_def_subs_pre: "all_list_constr_R (get_subsets_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) (length (?eval_q1@?eval_q2))"
      unfolding satisfies_properties_R_def by auto
    have get_subs_pre: "(get_subsets_R (snd ((combine_systems_R ?eval_p (?eval_q1,?uni_sys_q1) (?eval_q2,?uni_sys_q2))))) = subs_pre"
      using me_decomp unfolding get_subsets_R_def
      by (metis fst_conv me1_ind me2_ind me_pre_var snd_conv) 
    have well_def: "(\<And>Is1 Is2 n. (Is1, Is2) \<in> set (fst (snd me_pre)) \<Longrightarrow> n \<in> set Is1 \<or> n \<in> set Is2 \<Longrightarrow> n < length qs)"
      using well_def_subs_pre get_subs_pre 
        all_list_constr_R_matches_well_def[of subs_pre]
      by (smt (verit, ccfv_SIG) fst_comb fst_conv get_subsets_R_def length_map me1_ind me2_ind me_pre_var snd_conv) 
    then have reduce_mat_eq: "mat_eq =  reduce_system_R (eval_mpoly_poly val p) ((map (eval_mpoly_poly val) qs), me_pre)"
      using reduce_system_single_M_univariate[OF reduce_prop(2) less.prems(2)]
      by (metis prod.exhaust_sel) 
    let ?eval_qs = "(map (eval_mpoly_poly val) qs)"
    have "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = 
     (let q1 = take ((length ?eval_qs) div 2) ?eval_qs; left = calculate_data_R ?eval_p q1;
         q2 = drop ((length ?eval_qs) div 2) ?eval_qs; right = calculate_data_R ?eval_p q2;
         comb = combine_systems_R ?eval_p (q1,left) (q2,right) in
         reduce_system_R ?eval_p comb)"
      using len_hyp
      by (smt (z3) calculate_data_R.simps less_one nat_less_le semiring_norm(136)) 
    moreover have "... = (let q1 =(map (eval_mpoly_poly val) ?q1);
         left = calculate_data_R (eval_mpoly_poly val p) q1;
         q2 = (map (eval_mpoly_poly val) ?q2);
         right = calculate_data_R (eval_mpoly_poly val p) q2
     in Let (combine_systems_R (eval_mpoly_poly val p) (q1, left) (q2, right))
         (reduce_system_R (eval_mpoly_poly val p))) "
      using map_q1 map_q2 by auto 
    moreover have "... = (let q1 =(map (eval_mpoly_poly val) ?q1); left = me1; 
      q2 = (map (eval_mpoly_poly val) ?q2); right = me2 in
      Let (combine_systems_R (eval_mpoly_poly val p) (q1, left) (q2, right))
         (reduce_system_R (eval_mpoly_poly val p)))"
      unfolding Let_def me1_ind me2_ind by auto
    moreover have "... = mat_eq"
      unfolding Let_def reduce_mat_eq me_pre_var by auto  
    ultimately have "calculate_data_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs) = mat_eq"
      by auto
  }
  ultimately show ?case by blast
qed

lemma calculate_data_gives_signs_at_roots:
  assumes "(assumps, signs) \<in> set (calculate_data_to_signs (calculate_data_M p qs))"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes "eval_mpoly_poly val p \<noteq> 0"
  shows "signs = find_consistent_signs_at_roots_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs)"
  using assms calculate_data_M_univariate 
  unfolding find_consistent_signs_at_roots_R_def by auto

lemma calculate_data_gives_noncomp_signs_at_roots:
  assumes "(assumps, signs) \<in> set (calculate_data_to_signs (calculate_data_M p qs))"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes "eval_mpoly_poly val p \<noteq> 0"
  shows "set signs = set (characterize_consistent_signs_at_roots (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs))"
  using assms find_consistent_signs_at_roots_R calculate_data_gives_signs_at_roots
  by metis

lemma calculate_data_assumps_gives_signs_at_roots:
  assumes "(assumps, signs) \<in> set (calculate_data_to_signs (calculate_data_assumps_M p qs init_assumps))"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes "eval_mpoly_poly val p \<noteq> 0"
  shows "signs = find_consistent_signs_at_roots_R (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs)"
  using assms calculate_data_M_assumps_univariate 
  unfolding find_consistent_signs_at_roots_R_def 
  by auto

lemma calculate_data_assumps_gives_noncomp_signs_at_roots:
  assumes "(assumps, signs) \<in> set (calculate_data_to_signs (calculate_data_assumps_M p qs init_assumps))"
  assumes "\<And>p n. (p,n) \<in> set assumps \<Longrightarrow> satisfies_evaluation val p n"
  assumes "eval_mpoly_poly val p \<noteq> 0"
  shows "set signs = set (characterize_consistent_signs_at_roots (eval_mpoly_poly val p) (map (eval_mpoly_poly val) qs))"
  using assms find_consistent_signs_at_roots_R calculate_data_assumps_gives_signs_at_roots
  by metis 

end