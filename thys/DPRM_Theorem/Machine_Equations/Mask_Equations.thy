subsubsection \<open>Equations for masking relations\<close>

theory Mask_Equations
  imports "../Register_Machine/MachineMasking" Equation_Setup "../Diophantine/Binary_And"

abbrevs mb = "\<preceq>"

begin

context rm_eq_fixes
begin

  text \<open>Equation 4.15\<close>  
  definition register_mask :: "bool" where
    "register_mask \<equiv> \<forall>l < n. r l \<preceq> d"
  
  text \<open>Equation 4.17\<close>
  definition zero_indicator_mask :: "bool" where
    "zero_indicator_mask \<equiv> \<forall>l < n. z l \<preceq> e"

  text \<open>Equation 4.20\<close>
  definition zero_indicator_0_or_1 :: "bool" where
    "zero_indicator_0_or_1 \<equiv> \<forall>l<n. 2^c * z l = (r l + d) && f"
  
  definition mask_equations :: "bool" where 
    "mask_equations \<equiv> register_mask \<and> zero_indicator_mask \<and> zero_indicator_0_or_1"

end

context register_machine
begin

lemma register_mask_dioph:
  fixes d r
  assumes "n = length r"
  defines "DR \<equiv> (NARY (\<lambda>l. rm_eq_fixes.register_mask n (l!0) (shift l 1)) ([d] @ r))"
  shows "is_dioph_rel DR"
proof -
  define DS where "DS \<equiv> [\<forall><n] (\<lambda>i. ((r!i) [\<preceq>] d))"

  have "eval DS a = eval DR a" for a
  proof -
    have "eval DR a = rm_eq_fixes.register_mask n (peval d a) (list_eval r a)"
      unfolding DR_def by (auto simp add: shift_def list_eval_def)
    also have "... = (\<forall>l < n. (peval (r!l) a) \<preceq> peval d a)"
      using rm_eq_fixes.register_mask_def \<open>n = length r\<close> rm_eq_fixes_def 
            local.register_machine_axioms by (auto simp: list_eval_def)
    finally show ?thesis
      unfolding DS_def defs by simp
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp add: dioph)

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed

lemma zero_indicator_mask_dioph:
  fixes e z
  assumes "n = length z"
  defines "DR \<equiv> (NARY (\<lambda>l. rm_eq_fixes.zero_indicator_mask n (l!0) (shift l 1)) ([e] @ z))"
  shows "is_dioph_rel DR"
proof -
  define DS where "DS \<equiv> [\<forall><n] (\<lambda>i. ((z!i) [\<preceq>] e))"

  have "eval DS a = eval DR a" for a
  proof -
    have "eval DR a = rm_eq_fixes.zero_indicator_mask n (peval e a) (list_eval z a)"
      unfolding DR_def by (auto simp add: shift_def list_eval_def)
    also have "... = (\<forall>l < n. (peval (z!l) a) \<preceq> peval e a)"
      using rm_eq_fixes.zero_indicator_mask_def \<open>n = length z\<close> 
      rm_eq_fixes_def local.register_machine_axioms by (auto simp: list_eval_def)
    finally show ?thesis
      unfolding DS_def defs by simp
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp add: dioph)

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed

lemma zero_indicator_0_or_1_dioph:
  fixes c d f r z
  assumes "n = length r" and "n = length z"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.zero_indicator_0_or_1 n (ll!0!0) (ll!0!1) (ll!0!2)
                             (nth (ll!1)) (nth (ll!2))) [[c, d, f], r, z]"
  shows "is_dioph_rel DR"
proof -
  let ?N = 2
  define c' d' f' r' z' where pushed_def: "c' = push_param c ?N" "d' = push_param d ?N"
                                "f' = push_param f ?N" "r' = map (\<lambda>x. push_param x ?N) r"
                                "z' = map (\<lambda>x. push_param x ?N) z"
  define DS where "DS \<equiv> [\<forall><n] (\<lambda>i. ([\<exists>2] [Param 0 = (Const 2) ^ c'] 
                                        [\<and>] [Param 1 = (r'!i) [+] d' && f']
                                        [\<and>] Param 0 [*] (z'!i) [=] Param 1))"

  have "eval DS a = eval DR a" for a
  proof -
    have "eval DR a = rm_eq_fixes.zero_indicator_0_or_1 n (peval c a) (peval d a) (peval f a)
                        (list_eval r a) (list_eval z a)"
      unfolding DR_def defs by (auto simp add: assms shift_def list_eval_def)
    also have "... = (\<forall>l < n. 2^(peval c a) * (peval (z!l) a)
                              = (peval (r!l) a + peval d a) && peval f a)"
      using rm_eq_fixes.zero_indicator_0_or_1_def \<open>n = length r\<close> using assms
      rm_eq_fixes_def local.register_machine_axioms by (auto simp: list_eval_def)
    finally show ?thesis
      unfolding DS_def defs pushed_def using push_push apply (auto)
      subgoal for k
        apply (rule exI[of _ "[2^peval c a, peval (r!k) a + peval d a && peval f a]"])
        apply (auto simp: push_list_def assms(1-2))
        by (metis assms(1) assms(2) length_Cons list.size(3) nth_map numeral_2_eq_2)
      subgoal
        using assms by auto
      done
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (auto simp add: dioph)

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed


definition mask_equations_relation ("[MASK] _ _ _ _ _ _") where
  "[MASK] c d e f r z \<equiv> LARY (\<lambda>ll. rm_eq_fixes.mask_equations n 
                              (ll!0!0) (ll!0!1) (ll!0!2) (ll!0!3) (nth (ll!1)) (nth (ll!2)))
                              [[c, d, e, f], r, z]"

lemma mask_equations_relation_dioph:
  fixes c d e f r z
  assumes "n = length r" and "n = length z"
  defines "DR \<equiv> [MASK] c d e f r z"
  shows "is_dioph_rel DR"
proof -
  define DS where "DS \<equiv> NARY (\<lambda>l. rm_eq_fixes.register_mask n (l!0) (shift l 1)) ([d] @ r)
  [\<and>] NARY (\<lambda>l. rm_eq_fixes.zero_indicator_mask n (l!0) (shift l 1)) ([e] @ z)
  [\<and>] LARY (\<lambda>ll. rm_eq_fixes.zero_indicator_0_or_1 n (ll!0!0) (ll!0!1) (ll!0!2)
                             (nth (ll!1)) (nth (ll!2))) [[c, d, f], r, z]"

  have "eval DS a = eval DR a" for a
    using DS_def DR_def mask_equations_relation_def rm_eq_fixes.mask_equations_def
    rm_eq_fixes_def local.register_machine_axioms by (simp add: defs shift_def)
    
  moreover have "is_dioph_rel DS"
    unfolding DS_def using assms dioph
    using register_mask_dioph zero_indicator_mask_dioph zero_indicator_0_or_1_dioph
    by (metis (no_types, lifting))

  ultimately show ?thesis
    by (simp add: is_dioph_rel_def)
qed

end

end