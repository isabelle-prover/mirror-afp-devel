subsubsection \<open>Register Equations\<close>

theory Register_Equations imports "../Register_Machine/MultipleStepRegister"
                                  Equation_Setup "../Diophantine/Register_Machine_Sums" 
                                  "../Diophantine/Binary_And" "HOL-Library.Rewrite"

begin

context rm_eq_fixes
begin

  text \<open>Equation 4.22\<close>
  definition register_0 :: "bool" where
    "register_0 \<equiv> r 0 = a + b*r 0 + b*\<Sum>R+ p 0 s - b*\<Sum>R- p 0 (\<lambda>k. s k && z 0)"

  text \<open>Equation 4.23\<close>
  definition register_l :: "bool" where
    "register_l \<equiv> \<forall>l>0. l < n \<longrightarrow> r l = b*r l + b*\<Sum>R+ p l s - b*\<Sum>R- p l (\<lambda>k. s k && z l)"

  text \<open>Extra equation not in Matiyasevich's book\<close>
  definition register_bound :: "bool" where
    "register_bound \<equiv> \<forall>l < n. r l < b ^ q"

  definition register_equations :: "bool" where
    "register_equations \<equiv> register_0 \<and> register_l \<and> register_bound"

end

context register_machine 
begin

definition sum_rsub_of_bit_and  :: "polynomial \<Rightarrow> nat \<Rightarrow> polynomial list \<Rightarrow> polynomial
                              \<Rightarrow> relation" 
  ("[_ = \<Sum>R- _ '(_ && _')]") where
  "[x = \<Sum>R- d (s && zl)] \<equiv> let x' = push_param x (length p);
                               s' = push_param_list s (length p); 
                               zl' = push_param zl (length p)
                            in [\<exists>length p] [\<forall><length p] (\<lambda>i. [Param i = s'!i && zl'])
                                                        [\<and>] x' [=] [\<Sum>R-] p d Param"

lemma sum_rsub_of_bit_and_dioph[dioph]:
  fixes s :: "polynomial list" and d :: nat and x zl :: polynomial
  shows "is_dioph_rel [x = \<Sum>R- d (s && zl)]"
  unfolding sum_rsub_of_bit_and_def by (auto simp add: dioph)

lemma sum_rsub_of_bit_and_eval:
  fixes z s :: "polynomial list" and d :: nat and x :: polynomial
  assumes "length s = Suc m" "length p > 0"
  shows "eval [x = \<Sum>R- d (s && zl)] a
         \<longleftrightarrow> peval x a = \<Sum>R- p d (\<lambda>k. peval (s!k) a && peval zl a)" (is "?P \<longleftrightarrow> ?Q")
proof -
  have invariance: "\<forall>k<length p. y1 k = y2 k \<Longrightarrow> \<Sum>R- p d y1 = \<Sum>R- p d y2" for y1 y2
    unfolding sum_rsub.simps apply (intro sum.cong, simp)
    using \<open>length p > 0\<close> by auto (metis Suc_pred le_imp_less_Suc length_greater_0_conv)

  have len_ps: "length s = length p"
    using m_def \<open>length s = Suc m\<close> \<open>length p > 0\<close> by auto

  have aux1: "peval ([\<Sum>R-] p l f) a = \<Sum>R- p l (\<lambda>x. peval (f x) a) " for l f
    using defs \<open>length p > 0\<close> by auto

  show ?thesis
  proof (rule)
    assume ?P
    thus ?Q
      unfolding sum_rsub_of_bit_and_def 
      using aux1 apply simp
      apply (auto simp add: aux1 push_push defs)
      using push_push_map_i apply (simp add: push_param_list_def len_ps)
      unfolding list_eval_def apply (simp add: assms len_ps invariance) 
      using assms(2) invariance len_ps sum_rsub_polynomial_eval by force
  next
    assume ?Q
    thus ?P
      unfolding sum_rsub_of_bit_and_def apply (auto simp add: aux1 defs push_push)
      apply (rule exI[of _ "map (\<lambda>k. peval (s ! k) a && peval zl a) [0..<length p]"], simp)
      using push_push push_push_map_i apply (simp add: push_param_list_def len_ps)
      using invariance len_ps push_list_eval \<open>length p > 0\<close> defs by simp
  qed
qed


lemma register_0_dioph[dioph]:
  fixes A b :: polynomial
  fixes r z s :: "polynomial list"
  assumes "length r = n" "length z = n" "length s = Suc m" 
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.register_0 p (ll!0!0) (ll!0!1)
                            (nth (ll!1)) (nth (ll!2)) (nth (ll!3))) [[A, b], r, z, s]"
  shows "is_dioph_rel DR"
proof -
  let ?N = "1"
  define A' b' r' z' s' where pushed_def: "A' = push_param A ?N" "b' = push_param b ?N"
                               "r' = map (\<lambda>x. push_param x ?N) r" "z' = map (\<lambda>x. push_param x ?N) z"
                               "s' = map (\<lambda>x. push_param x ?N) s"

  define DS where "DS \<equiv> [\<exists>] ([Param 0 = \<Sum>R- 0 (s' && (z'!0))] [\<and>]
                              r'!0 [=] A' [+] b' [*] r'!0 [+] b' [*] ([\<Sum>R+] p 0 (nth s')) 
                                                          [-] b' [*] (Param 0))"

  have "length p > 0" using p_nonempty by auto
  have "n > 0" using n_gt_0 by auto

  have "length p = length s"
    using \<open>length s = Suc m\<close> m_def \<open>length p > 0\<close> by auto
  have "length s' = length s"
    unfolding pushed_def by auto
  have "length z > 0"
    using \<open>length z = n\<close> \<open>n > 0\<close> by simp
  have "length r > 0"
    using \<open>length r = n\<close> \<open>n > 0\<close> by simp

  have "eval DS a = eval DR a" for a
  proof -
    (* the key to this proof is to write these intermediate steps with list_eval on the RHS
        because that is needed in the final proof; otherwise showing the equivalence again
        re-requires unfolding the sum definitions *) 
    have sum_radd_push: "\<Sum>R+ p 0 (\<lambda>x. peval (s' ! x) (push a k)) = \<Sum>R+ p 0 (list_eval s a)" for k
      unfolding sum_radd.simps pushed_def apply (intro sum.cong, simp)
      using push_push_map1 \<open>length p = length s\<close> \<open>length s = Suc m\<close> by simp

    have sum_rsub_push: "\<Sum>R- p 0 (\<lambda>x. peval (s' ! x) (push a k) && peval (z' ! 0) (push a k))
                           = \<Sum>R- p 0 (\<lambda>x. list_eval s a x && peval (z ! 0) a)" for k
      unfolding sum_rsub.simps pushed_def apply (intro sum.cong, simp)
      using push_push_map1 \<open>length p = length s\<close> \<open>length s = Suc m\<close> \<open>length z > 0\<close>
      by (simp add: list_eval_def)

    have 1: "peval ([\<Sum>R-] p l f) a = \<Sum>R- p l (\<lambda>x. peval (f x) a) " for f l
      using defs \<open>length p > 0\<close> by auto

    show ?thesis
      unfolding DS_def rm_eq_fixes.register_0_def 
      register_machine_axioms rm_eq_fixes_def apply (simp add: defs)
      using \<open>length p > 0\<close> apply (simp add: sum_rsub_of_bit_and_eval \<open>length s' = length s\<close>
                                            \<open>length s = Suc m\<close>) 
      apply (simp add: sum_radd_push sum_rsub_push)
      unfolding pushed_def using push_push1 push_push_map1 \<open>length r > 0\<close> apply simp
      unfolding DR_def assms defs \<open>length p > 0\<close> 
      using rm_eq_fixes_def rm_eq_fixes.register_0_def register_machine_axioms apply (simp)
      using \<open>length z > 0\<close> push_def list_eval_def 1 apply (simp add: 1 defs \<open>length p > 0\<close>)
      using One_nat_def sum_radd_push unfolding pushed_def(5) list_eval_def by presburger
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (simp add: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

lemma register_l_dioph[dioph]:
  fixes b :: polynomial
  fixes r z s :: "polynomial list"
  assumes "length r = n" "length z = n" "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.register_l p n (ll!0!0)
                            (nth (ll!1)) (nth (ll!2)) (nth (ll!3))) [[b], r, z, s]"
  shows "is_dioph_rel DR"
proof -
  define indices where "indices \<equiv> [Suc 0..<n]" (* for now *)
  
  let ?N = "length indices + 1"
  define b' r' z' s' where pushed_def: "b' = push_param b ?N"
                                       "r' = map (\<lambda>x. push_param x ?N) r" 
                                       "z' = map (\<lambda>x. push_param x ?N) z"
                                       "s' = map (\<lambda>x. push_param x ?N) s"
                                            
  define param_l_is_sum_rsub_of_bitand where
    "param_l_is_sum_rsub_of_bitand \<equiv> \<lambda>l. [Param l = \<Sum>R- l (s' && (z'!l))]"
  define params_are_sum_rsub_of_bitand where 
    "params_are_sum_rsub_of_bitand \<equiv> [\<forall> in indices] param_l_is_sum_rsub_of_bitand"
  define single_register where
    "single_register \<equiv> \<lambda>l. r'!l [=] b' [*] r'!l [+] b' [*] ([\<Sum>R+] p l (nth s')) [-] b' [*] (Param l)"

  define DS where "DS \<equiv> [\<exists>n] params_are_sum_rsub_of_bitand [\<and>] [\<forall> in indices] single_register"

  have "length p > 0" using p_nonempty by auto
  have "n > 0" using n_gt_0 by auto
  have "length p = length s"
    using \<open>length s = Suc m\<close> m_def \<open>length p > 0\<close> by auto
  have "length s' = length s"
    unfolding pushed_def by auto
  have "length z > 0"
    using \<open>length z = n\<close> \<open>n > 0\<close> by simp
  have "length r > 0"
    using \<open>length r = n\<close> \<open>n > 0\<close> by simp
  have "length indices + 1 = n"
    unfolding indices_def \<open>n>0\<close> 
    using Suc_pred' \<open>n > 0\<close> length_upt by presburger
  have "length s' = Suc m"
    using \<open>length s' = length s\<close> \<open>length s = Suc m\<close> by auto

  have "eval DS a = eval DR a" for a
  proof -

    have eval_to_peval:
          "eval [polynomial.Param (indices ! k) 
          = \<Sum>R- indices ! k (s' && z' ! (indices ! k))] y 
      \<longleftrightarrow>(peval (polynomial.Param (indices ! k)) y 
          = \<Sum>R- p (indices ! k) (\<lambda>ka. peval (s' ! ka) y && peval (z' ! (indices ! k)) y) )" for k y  
      using sum_rsub_of_bit_and_eval \<open>length p > 0\<close> \<open>length s' = Suc m\<close> by auto

    have b'_unfold: "peval b' (push_list a ks) = peval b a" if "length ks = n" for ks
      unfolding pushed_def using indices_def push_push that \<open>length indices + 1 = n\<close> by auto

    have r'_unfold: "peval (r' ! (indices ! k)) (push_list a ks) = peval (r!(indices!k)) a"
      if "k < length indices" and "length ks = n" for k ks 
      using indices_def push_push pushed_def that(1) that(2) \<open>length r = n\<close> by auto

    have Param_unfold: "peval (Param (indices ! k)) (push_list a ks) = ks!(indices!k)" 
      if "k < length indices" and "length ks = n" for k ks
      using One_nat_def Suc_pred indices_def length_upt nat_add_left_cancel_less 
          nth_upt peval.simps(2) plus_1_eq_Suc push_list_eval that(1) that(2) by (metis \<open>0 < n\<close>)

    have unfold_4: "push_list a ks (indices ! k) = ks!(indices!k)" 
      if "k < length indices" and "length ks = n" for k ks
      using Param_unfold that(1) that(2) by force

    have unfold_sum_radd: "\<Sum>R+ p (indices ! k) (\<lambda>x. peval (s' ! x) (push_list a ks))
                         = \<Sum>R+ p (indices ! k) (list_eval s a)"
      if "length ks = n" for k ks 
      apply (rule sum_radd_cong) unfolding pushed_def 
      using push_push_map_i[of ks n _ s a] \<open>length indices + 1 = n\<close> that 
      using \<open>length p = length s\<close> 
      by (metis \<open>0 < length p\<close> add.left_neutral add_lessD1 le_neq_implies_less less_add_one 
          less_diff_conv less_diff_conv2 nat_le_linear not_add_less1)
      
    have unfold_sum_rsub: "\<Sum>R- p (indices ! k) (\<lambda>ka. peval (s' ! ka) (push_list a ks) 
                                        && peval (z' ! (indices ! k)) (push_list a ks))
                         = \<Sum>R- p (indices ! k) (\<lambda>ka. list_eval s a ka
                                        && peval (z ! (indices ! k)) a)"
      if "length ks = n" for k ks 
      apply (rule sum_rsub_cong) unfolding pushed_def 
      using push_push_map_i[of ks n _ s a] unfolding \<open>length indices + 1 = n\<close> 
      using \<open>length p = length s\<close> assms apply simp
      using nth_map[of _ z "\<lambda>x. push_param x (Suc (length indices))"]
      using modifies_yields_valid_register \<open>length z = n\<close>
      by (smt assms le_imp_less_Suc nth_map push_push_simp that)

    have indices_unfold: "(\<forall>k < length indices. P (indices!k)) \<longleftrightarrow> (\<forall>l>0. l<n \<longrightarrow> P l)" for P
      unfolding indices_def apply auto
      using \<open>n>0\<close> by (metis Suc_diff_Suc diff_zero not_less_eq)

    have alternative_sum_rsub:
          "(\<Sum>R- p l (\<lambda>ka. list_eval s a ka && peval (z ! l) a)) 
         =(\<Sum>R- p l (\<lambda>k. map (\<lambda>P. peval P a) s ! k && map (\<lambda>P. peval P a) z ! l))" for l
      apply (rule sum_rsub_cong) unfolding list_eval_def apply simp 
      using modifies_yields_valid_register 
      One_nat_def assms(3) nth_map \<open>length z = n\<close> \<open>length s = Suc m\<close>
      by (metis \<open>length p = length s\<close> le_imp_less_Suc m_def)

    (* Start of chain of equalities *)
    have "(eval DS a) = (\<exists>ks. n = length ks \<and> 
           (\<forall>k<length indices. eval [Param (indices ! k) 
                               = \<Sum>R- (indices ! k) (s' && z' ! (indices ! k))] (push_list a ks)) \<and>
           (\<forall>k<length indices. eval (single_register (indices ! k)) (push_list a ks)))"
      unfolding DS_def params_are_sum_rsub_of_bitand_def param_l_is_sum_rsub_of_bitand_def
      by (simp add: defs)

    also have "... = (\<exists>ks. n = length ks \<and>
           (\<forall>k<length indices. 
              peval (Param (indices ! k)) (push_list a ks) 
              = \<Sum>R- p (indices ! k) (\<lambda>ka. peval (s' ! ka) (push_list a ks) 
                                        && peval (z' ! (indices ! k)) (push_list a ks)) \<and>
              peval (r' ! (indices ! k)) (push_list a ks) 
              = peval b' (push_list a ks) * peval (r' ! (indices ! k)) (push_list a ks) 
              + peval b' (push_list a ks) * \<Sum>R+ p (indices ! k) 
                                                   (\<lambda>x. peval (s' ! x) (push_list a ks)) 
              - peval b' (push_list a ks) * (push_list a ks (indices ! k))))"      
      using eval_to_peval unfolding single_register_def 
      using sum_radd_polynomial_eval \<open>length p > 0\<close> by (simp add: defs) (blast) 

    also have "... = (\<exists>ks. n = length ks \<and>
           (\<forall>k<length indices. 
              ks!(indices!k)
              = \<Sum>R- p (indices ! k) (\<lambda>ka. peval (s' ! ka) (push_list a ks) 
                                        && peval (z' ! (indices ! k)) (push_list a ks)) \<and>
              peval (r!(indices!k)) a
              = peval b a * peval (r!(indices!k)) a
              + peval b a * \<Sum>R+ p (indices ! k) (\<lambda>x. peval (s' ! x) (push_list a ks)) 
              - peval b a * (ks!(indices!k))))"
      using b'_unfold r'_unfold Param_unfold unfold_4 by (smt (z3))

    also have "... = (\<exists>ks. n = length ks \<and>
           (\<forall>k<length indices. 
              ks!(indices!k)
              = (\<Sum>R- p (indices ! k) (\<lambda>ka. peval (s' ! ka) (push_list a ks) 
                                        && peval (z' ! (indices ! k)) (push_list a ks))) \<and>
              peval (r!(indices!k)) a
              = peval b a * peval (r!(indices!k)) a
              + peval b a * (\<Sum>R+ p (indices ! k) (list_eval s a))
              - peval b a * (ks!(indices!k))))"
      using unfold_sum_radd by (smt (z3))

    also have "... = (\<exists>ks. n = length ks \<and>
           (\<forall>k<length indices. 
              ks!(indices!k)
                = \<Sum>R- p (indices ! k) (\<lambda>ka. list_eval s a ka && peval (z ! (indices ! k)) a) 
            \<and> peval (r!(indices!k)) a
                = peval b a * peval (r!(indices!k)) a
                + peval b a * (\<Sum>R+ p (indices ! k) (list_eval s a))
                - peval b a * (ks!(indices!k))))"
      using unfold_sum_rsub by auto

    also have "... = (\<exists>ks. n = length ks \<and>
           (\<forall>k<length indices. 
              ks!(indices!k)
                = \<Sum>R- p (indices ! k) (\<lambda>ka. list_eval s a ka && peval (z ! (indices ! k)) a) 
            \<and> peval (r!(indices!k)) a
                = peval b a * peval (r!(indices!k)) a
                + peval b a * (\<Sum>R+ p (indices ! k) (list_eval s a))
                - peval b a *  
                (\<Sum>R- p (indices ! k) (\<lambda>ka. list_eval s a ka && peval (z ! (indices ! k)) a))))"
      by smt

    also have "... = (\<forall>k<length indices. 
              peval (r!(indices!k)) a
                = peval b a * peval (r!(indices!k)) a
                + peval b a * (\<Sum>R+ p (indices ! k) (list_eval s a))
                - peval b a *  
                (\<Sum>R- p (indices ! k) (\<lambda>ka. list_eval s a ka && peval (z ! (indices ! k)) a)))"
      unfolding indices_def apply auto 
      apply (rule exI[of _ 
             "map (\<lambda>k. \<Sum>R- p k (\<lambda>ka. list_eval s a ka && peval (z ! k) a)) [0..<n]"])
      by auto

    also have "... = (\<forall>l>0. l < n \<longrightarrow> 
                  peval (r!l) a
                    = peval b a * peval (r!l) a
                    + peval b a * (\<Sum>R+ p l (list_eval s a))
                    - peval b a *  
                    (\<Sum>R- p l (\<lambda>ka. list_eval s a ka && peval (z ! l) a)))"
      using indices_unfold[of "\<lambda>x. peval (r ! x) a =
        peval b a * peval (r ! x) a + peval b a * (\<Sum>R+ p x (list_eval s a)) -
        peval b a * (\<Sum>R- p x (\<lambda>ka. (list_eval s a ka) && peval (z ! x) a))"]
      by auto

    also have "... =  (\<forall>l>0. l < n \<longrightarrow>
           peval (r!l) a =
           peval b a * map (\<lambda>P. peval P a) r ! l
         + peval b a * (\<Sum>R+ p l ((!) (map (\<lambda>P. peval P a) s)))
         - peval b a * (\<Sum>R- p l (\<lambda>k. map (\<lambda>P. peval P a) s ! k && map (\<lambda>P. peval P a) z ! l)))"
      using nth_map[of _ r "(\<lambda>P. peval P a)"] unfolding \<open>length r = n\<close> 
      using alternative_sum_rsub list_eval_def by auto

    also have "... = (eval DR a)"      
      apply (simp add: DR_def defs) using rm_eq_fixes_def rm_eq_fixes.register_l_def
      local.register_machine_axioms
      using nth_map[of _ r "\<lambda>P. peval P a"] unfolding \<open>length r = n\<close> by auto

    finally show "eval DS a = eval DR a" by auto
  qed

  moreover have "is_dioph_rel DS"
  proof - 
    have "list_all (is_dioph_rel \<circ> param_l_is_sum_rsub_of_bitand) indices" 
      unfolding param_l_is_sum_rsub_of_bitand_def indices_def list_all_def by (auto simp:dioph)
    hence "is_dioph_rel params_are_sum_rsub_of_bitand"
      unfolding params_are_sum_rsub_of_bitand_def by (auto simp: dioph)
  
    have "list_all (is_dioph_rel \<circ> single_register) indices"
      unfolding single_register_def list_all_def indices_def by (auto simp: dioph)
    thus ?thesis 
    unfolding DS_def using \<open>is_dioph_rel params_are_sum_rsub_of_bitand\<close> by (auto simp: dioph)
  qed

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

lemma register_bound_dioph:
  fixes b q :: polynomial
  fixes r :: "polynomial list"
  assumes "length r = n"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.register_bound n (ll!0!0) (ll!0!1) (nth (ll!1))) 
                     [[b, q], r]"
  shows "is_dioph_rel DR"
proof - 

  define indices where "indices \<equiv> [0..<n]" (* for now *)
  hence "length indices = n" by auto

  let ?N = "length indices"
  define b' q' r' where pushed_def: "b' = push_param b ?N"
                                    "q' = push_param q ?N"
                                    "r' = map (\<lambda>x. push_param x ?N) r" 
                
  define bound where
    "bound \<equiv> \<lambda>l. (r'!l [<] (Param l) [\<and>] [Param l = b' ^ q'])"

  define DS where "DS \<equiv> [\<exists>n] [\<forall> in indices] bound"

  have "eval DS a = eval DR a" for a 
  proof -       

    have r'_unfold: "peval (r' ! k) (push_list a ks) = peval (r ! k) a" 
      if "length ks = n" and "k < length ks" for k ks
      unfolding pushed_def \<open>length indices = n\<close> 
      using push_push_map_i[of ks n k r] that \<open>length r = n\<close> list_eval_def by auto

    have b'_unfold: "peval b' (push_list a ks) = peval b a" 
     and q'_unfold: "peval q' (push_list a ks) = peval q a"
      if "length ks = n" and "k < length ks" for k ks
      unfolding pushed_def \<open>length indices = n\<close>   
      using push_push_simp that \<open>length r = n\<close> list_eval_def by auto      

    have "eval DS a = (\<exists>ks. n = length ks \<and>
          (\<forall>k<n. peval (r' ! k) (push_list a ks) < push_list a ks k \<and>
                 push_list a ks k = peval b' (push_list a ks) ^ peval q' (push_list a ks)))"
      unfolding DS_def indices_def bound_def by (simp add: defs)
    
    also have "... = (\<exists>ks. n = length ks \<and>
          (\<forall>k<n. peval (r ! k) a < peval b a ^ peval q a \<and>
                 push_list a ks k = peval b a ^ peval q a))"
      using r'_unfold b'_unfold q'_unfold by (metis (full_types))

    also have "... = (\<forall>k<n. peval (r ! k) a < peval b a ^ peval q a)"
      apply auto apply (rule exI[of _ "map (\<lambda>k. peval b a ^ peval q a) [0..<n]"])
      unfolding indices_def push_list_def by auto

    also have "... = (\<forall>l<n. map (\<lambda>P. peval P a) r ! l < peval b a ^ peval q a)"
      using nth_map[of _ r "\<lambda>P. peval P a"] \<open>length r = n\<close> by force

    finally show ?thesis unfolding DR_def
      using rm_eq_fixes.register_bound_def rm_eq_fixes_def register_machine_def 
      p_nonempty n_gt_0 valid_program by (auto simp add: defs) 

  qed

  moreover have "is_dioph_rel DS"
  proof -
    have "list_all (is_dioph_rel \<circ> bound) indices"
      unfolding bound_def indices_def list_all_def by (auto simp:dioph)
    thus ?thesis unfolding DS_def indices_def bound_def by (auto simp: dioph)
  qed

  ultimately show ?thesis     
    by (auto simp: is_dioph_rel_def)
qed



definition register_equations_relation :: "polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial
   \<Rightarrow> polynomial list \<Rightarrow> polynomial list \<Rightarrow> polynomial list \<Rightarrow> relation" ("[REG] _ _ _ _ _ _") where
  "[REG] a b q r z s \<equiv> LARY (\<lambda>ll. rm_eq_fixes.register_equations p n (ll!0!0) (ll!0!1) (ll!0!2)
                          (nth (ll!1)) (nth (ll!2)) (nth (ll!3))) [[a, b, q], r, z, s]"

lemma reg_dioph:
  fixes A b q r z s
  assumes "length r = n" "length z = n" "length s = Suc m" 
  defines "DR \<equiv> [REG] A b q r z s"
  shows "is_dioph_rel DR"
proof -

  define DS where "DS \<equiv> (LARY (\<lambda>ll. rm_eq_fixes.register_0 p (ll!0!0) (ll!0!1)
                        (nth (ll!1)) (nth (ll!2)) (nth (ll!3))) [[A, b], r, z, s])
                    [\<and>] (LARY (\<lambda>ll. rm_eq_fixes.register_l p n (ll!0!0)
                        (nth (ll!1)) (nth (ll!2)) (nth (ll!3))) [[b], r, z, s])
                    [\<and>] (LARY (\<lambda>ll. rm_eq_fixes.register_bound n (ll!0!0) (ll!0!1) (nth (ll!1))) 
                        [[b, q], r])"

  have "eval DS a = eval DR a" for a 
    unfolding DS_def DR_def register_equations_relation_def rm_eq_fixes.register_equations_def 
    apply (simp add: defs) 
    by (simp add: register_machine_axioms rm_eq_fixes.intro rm_eq_fixes.register_equations_def)

  moreover have "is_dioph_rel DS"
    unfolding DS_def using assms register_0_dioph[of r z s] register_l_dioph[of r z s] 
    register_bound_dioph by (auto simp: dioph)

  ultimately show ?thesis by (auto simp: is_dioph_rel_def)
qed

end

end