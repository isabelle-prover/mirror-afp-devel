subsubsection \<open>State unique equations\<close>

theory State_Unique_Equations imports "../Register_Machine/MultipleStepState"
                                      Equation_Setup "../Diophantine/Register_Machine_Sums" 
                                      "../Diophantine/Binary_And"

begin

context rm_eq_fixes 
begin

  text \<open>Equations not in the book: \<close>
  definition state_mask :: "bool" where
      "state_mask \<equiv> \<forall>k\<le>m. s k \<preceq> e"

  definition state_bound :: "bool" where
    "state_bound \<equiv> \<forall>k<m. s k < b ^ q" 
(* This means s k,q = 0 for all k < m. *)
(* Reminder: s m = b^q \<^bold>— s m,t = 1 at t = q and nowhere else*)
  
  definition state_unique_equations :: "bool" where
    "state_unique_equations \<equiv> state_mask \<and> state_bound"

end

context register_machine
begin

lemma state_mask_dioph:
  fixes e :: polynomial
  fixes s :: "polynomial list"
  assumes "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_mask p (ll!0!0) (nth (ll!1))) [[e], s]"
  shows "is_dioph_rel DR"
proof - 
  define mask where "mask \<equiv> (\<lambda>l. (s!l [\<preceq>] e))"
  define DS where "DS \<equiv> [\<forall><Suc m] mask"

  have "eval DS a = eval DR a" for a 
  proof -
    have "eval DS a = (\<forall>k\<le>m. peval (s ! k) a \<preceq> peval e a)" 
      unfolding DS_def mask_def by (simp add: less_Suc_eq_le defs)

    also have "... = (\<forall>k\<le>m. map (\<lambda>P. peval P a) s ! k \<preceq> peval e a)"
      using nth_map[of _ s "(\<lambda>P. peval P a)"] \<open>length s = Suc m\<close> by auto

    finally show ?thesis
      unfolding DR_def using rm_eq_fixes_def local.register_machine_axioms 
                             rm_eq_fixes.state_mask_def by (simp add: defs)
  qed

  moreover have "is_dioph_rel DS"
  proof -
    have "list_all (is_dioph_rel \<circ> mask) [0..<Suc m]"
      unfolding mask_def list_all_def by (auto simp: dioph)
    thus ?thesis unfolding DS_def mask_def by (auto simp: dioph)
  qed

  ultimately show ?thesis     
    by (auto simp: is_dioph_rel_def)
qed

lemma state_bound_dioph:
  fixes b q :: polynomial
  fixes s :: "polynomial list"
  assumes "length s = Suc m"
  defines "DR \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_bound p (ll!0!0) (ll!0!1) (nth (ll!1))) [[b, q], s]"
  shows "is_dioph_rel DR"
proof - 
  let ?N = "m"
  define b' q' s' where pushed_def: "b' = push_param b ?N"
                                    "q' = push_param q ?N"
                                    "s' = map (\<lambda>x. push_param x ?N) s" 
                
  define bound where
    "bound \<equiv> \<lambda>l. s'!l [<] (Param l) [\<and>] [Param l = b' ^ q']"

  define DS where "DS \<equiv> [\<exists>m] [\<forall><m] bound"

  have "eval DS a = eval DR a" for a 
  proof -       

    have s'_unfold: "peval (s' ! k) (push_list a ks) = peval (s ! k) a" 
      if "length ks = m" and "k < length ks" for k ks
      unfolding pushed_def  
      using push_push_map_i[of ks n k s] that \<open>length s = Suc m\<close> list_eval_def 
      by (metis less_SucI nth_map push_push)

    have b'_unfold: "peval b' (push_list a ks) = peval b a" 
     and q'_unfold: "peval q' (push_list a ks) = peval q a"
      if "length ks = m" and "k < length ks" for k ks
      unfolding pushed_def    
      using push_push_simp that \<open>length s = Suc m\<close> list_eval_def by metis+      

    have "eval DS a = (\<exists>ks. m = length ks \<and>
          (\<forall>k<m. peval (s' ! k) (push_list a ks) < push_list a ks k \<and>
                 push_list a ks k = peval b' (push_list a ks) ^ peval q' (push_list a ks)))"
      unfolding DS_def bound_def by (simp add: defs)
    
    also have "... = (\<exists>ks. m = length ks \<and>
          (\<forall>k<m. peval (s ! k) a < peval b a ^ peval q a \<and>
                 push_list a ks k = peval b a ^ peval q a))"
      using s'_unfold b'_unfold q'_unfold by metis

    also have "... = (\<forall>k<m. peval (s ! k) a < peval b a ^ peval q a)"
      apply auto apply (rule exI[of _ "map (\<lambda>k. peval b a ^ peval q a) [0..<m]"])
      unfolding push_list_def by auto

    also have "... = (\<forall>l<m. map (\<lambda>P. peval P a) s ! l < peval b a ^ peval q a)"
      using nth_map[of _ s "\<lambda>P. peval P a"] \<open>length s = Suc m\<close> by force

    finally show ?thesis unfolding DR_def  
      using rm_eq_fixes_def local.register_machine_axioms rm_eq_fixes.state_bound_def 
      by (simp add: defs) 

  qed

  moreover have "is_dioph_rel DS"
  proof -
    have "list_all (is_dioph_rel \<circ> bound) [0..<Suc m]"
      unfolding bound_def list_all_def by (auto simp:dioph)
    thus ?thesis unfolding DS_def bound_def by (auto simp: dioph)
  qed

  ultimately show ?thesis     
    by (auto simp: is_dioph_rel_def)
qed

lemma state_unique_equations_dioph:
  fixes b q e :: polynomial
  fixes s :: "polynomial list"
  assumes "length s = Suc m"
  defines "DR \<equiv> LARY 
                (\<lambda>ll. rm_eq_fixes.state_unique_equations p (ll!0!0) (ll!0!1) (ll!0!2) (nth (ll!1))) 
                [[b, e, q], s]"
  shows "is_dioph_rel DR"
proof - 

  define DS where "DS \<equiv> LARY (\<lambda>ll. rm_eq_fixes.state_mask p (ll!0!0) (nth (ll!1))) [[e], s]
                    [\<and>] LARY (\<lambda>ll. rm_eq_fixes.state_bound p (ll!0!0) (ll!0!1) (nth (ll!1))) 
                              [[b, q], s]"

  have "eval DS a = eval DR a" for a
    unfolding DR_def DS_def using rm_eq_fixes.state_unique_equations_def rm_eq_fixes_def
    local.register_machine_axioms
    by (auto simp: defs)

  moreover have "is_dioph_rel DS" 
    unfolding DS_def using state_bound_dioph state_mask_dioph assms dioph by auto

  ultimately show ?thesis using is_dioph_rel_def by auto
qed

end

end