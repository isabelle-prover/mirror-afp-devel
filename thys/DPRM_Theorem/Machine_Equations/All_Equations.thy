subsubsection \<open>Wrap-Up: Combining all equations\<close>

theory All_Equations
  imports All_Equations_Invariance
 
begin

context register_machine
begin

definition all_equations_relation :: "polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial
  \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial \<Rightarrow> polynomial list \<Rightarrow> polynomial list \<Rightarrow> polynomial list
  \<Rightarrow> relation" ("[ALLEQ] _ _ _ _ _ _ _ _ _ _") where
  "[ALLEQ] a q b c d e f r z s 
         \<equiv> LARY (\<lambda>ll. all_equations (ll!0!0) (ll!0!1) (ll!0!2) (ll!0!3) (ll!0!4) (ll!0!5) (ll!0!6)
                                     (nth (ll!1)) (nth (ll!2)) (nth (ll!3)))
                                     [[a, q, b, c, d, e, f], r, z, s]"

lemma all_equations_dioph: 
  fixes A f e d c b q :: polynomial
  fixes r z s :: "polynomial list"
  assumes "length r = n" "length z = n" "length s = Suc m"
  defines "DR \<equiv> [ALLEQ] A q b c d e f r z s"
  shows "is_dioph_rel DR"
proof - 
  define DS where "DS \<equiv> ([REG] A b q r z s) 
                     [\<and>] ([STATE] b e q z s)
                     [\<and>] ([MASK] c d e f r z)
                     [\<and>] ([CONST] b c d e f q)
                     [\<and>] [MISC] A c q"

  have "eval DS a = eval DR a" for a 
    unfolding DR_def DS_def all_equations_relation_def all_equations_def 
    unfolding register_equations_relation_def state_equations_relation_def 
      mask_equations_relation_def rm_constant_equations_def rm_miscellaneous_equations_def
    by (simp add: defs)

  moreover have "is_dioph_rel DS"
    unfolding DS_def apply (rule and_dioph)+
    apply (simp_all add: rm_constant_equations_dioph rm_miscellaneous_equations_dioph)
    using assms reg_dioph[of r z s A b q] state_equations_dioph[of s z b e q] 
          mask_equations_relation_dioph[of r z c d e f] by metis+

  ultimately show ?thesis using is_dioph_rel_def by auto
qed

definition rm_equations :: "nat \<Rightarrow> bool" where
  "rm_equations a \<equiv> \<exists> q :: nat.
                      \<exists> b c d e f :: nat. 
                      \<exists> r z :: register \<Rightarrow> nat. 
                      \<exists> s :: state \<Rightarrow> nat.
                      all_equations a q b c d e f r z s"

definition rm_equations_relation :: "polynomial \<Rightarrow> relation" ("[RM] _") where
  "[RM] A \<equiv> UNARY (rm_equations) A"

(* Correct assumptions: Need validity of p *)

lemma rm_dioph:
  fixes A
  fixes ic :: configuration
  defines "DR \<equiv> [RM] A"
  shows "is_dioph_rel DR"
proof - 
  define q b c d e f where "q \<equiv> Param 0" and
                           "b \<equiv> Param 1" and
                           "c \<equiv> Param 2" and
                           "d \<equiv> Param 3" and
                           "e \<equiv> Param 4" and
                           "f \<equiv> Param 5" 

  define r where "r \<equiv> map Param [6..<n + 6]"
  define z where "z \<equiv> map Param [n+6..<2*n + 6]"
  define s where "s \<equiv> map Param [2*n + 6..<2*n + 6 + m + 1]"

  define number_of_ex_vars where "number_of_ex_vars \<equiv> 2*n + 6 + m + 1" 

  define A' where "A' \<equiv> push_param A number_of_ex_vars"

  define DS where "DS \<equiv> [\<exists>number_of_ex_vars] [ALLEQ] A' q b c d e f r z s"

  have "length r = n" and "length z = n" and "length s = Suc m"
    unfolding r_def z_def s_def by auto

  have "eval DS a = eval DR a" for a
  proof (rule)
    assume "eval DS a"
    then obtain ks where 
      ks_length: "number_of_ex_vars = length ks" and
      ALLEQ: "eval ([ALLEQ] A' q b c d e f r z s) (push_list a ks)" 
      unfolding DS_def by (auto simp add: defs)

    define q' b' c' d' e' f' where "q' \<equiv> ks!0" and
                                   "b' \<equiv> ks!1" and
                                   "c' \<equiv> ks!2" and
                                   "d' \<equiv> ks!3" and
                                   "e' \<equiv> ks!4" and
                                   "f' \<equiv> ks!5" 

    define r_list where "r_list \<equiv> (take n (drop 6 ks))"
    define z_list where "z_list \<equiv> (take n (drop (6+n) ks))"
    define s_list where "s_list \<equiv> (drop (6 + 2*n) ks)"
    
    define r' where "r' \<equiv> (!) r_list"
    define z' where "z' \<equiv> (!) z_list"
    define s' where "s' \<equiv> (!) s_list"

    have A: "peval A' (push_list a ks) = peval A a" for a 
      using ks_length push_push_simp unfolding A'_def by auto

    have q: "peval q (push_list a ks) = q'"
      unfolding q_def q'_def push_list_def using ks_length unfolding number_of_ex_vars_def by auto
    have b: "peval b (push_list a ks) = b'"
      unfolding b_def b'_def push_list_def using ks_length unfolding number_of_ex_vars_def by auto
    have c: "peval c (push_list a ks) = c'"
      unfolding c_def c'_def push_list_def using ks_length unfolding number_of_ex_vars_def by auto
    have d: "peval d (push_list a ks) = d'"
      unfolding d_def d'_def push_list_def using ks_length unfolding number_of_ex_vars_def by auto
    have e: "peval e (push_list a ks) = e'"
      unfolding e_def e'_def push_list_def using ks_length unfolding number_of_ex_vars_def by auto
    have f: "peval f (push_list a ks) = f'"
      unfolding f_def f'_def push_list_def using ks_length unfolding number_of_ex_vars_def by auto

    have r: "(!) (map (\<lambda>P. peval P (push_list a ks)) r) x = (!) r_list x" if "x < n" for x 
      unfolding r_def r_list_def using that unfolding push_list_def 
      using ks_length unfolding number_of_ex_vars_def by auto

    have z: "(map (\<lambda>P. peval P (push_list a ks)) z) ! x = z_list ! x" if "x < n" for x 
      unfolding z_def z_list_def using that unfolding push_list_def 
      using ks_length unfolding number_of_ex_vars_def by (auto simp add: add.commute)

    have s: "(map (\<lambda>P. peval P (push_list a ks)) s) ! x = s_list ! x" if "x < Suc m" for x 
      unfolding s_def s_list_def using that unfolding push_list_def 
      using ks_length unfolding number_of_ex_vars_def by (auto simp add: add.commute)

    have "all_equations (peval A a) q' b' c' d' e' f' r' z' s'"
      using ALLEQ unfolding all_equations_relation_def apply (simp add: defs)
      unfolding A q b c d e f 
      using all_equations_invariance[of 
                                     "(!) (map (\<lambda>P. peval P (push_list a ks)) r)" r' 
                                     "(!) (map (\<lambda>P. peval P (push_list a ks)) z)" z' 
                                     "(!) (map (\<lambda>P. peval P (push_list a ks)) s)" s' 
                                     "peval A a" q' b' c' d' e' f'] r z s
      using r'_def s'_def z'_def by fastforce 

    thus "eval DR a" 
      unfolding DR_def rm_equations_def rm_equations_relation_def by (auto simp: defs) (blast) 
  next
    assume "eval DR a"
    then obtain q' b' c' d' e' f' r' z' s' where 
         all_eq: "all_equations (peval A a) q' b' c' d' e' f' r' z' s'"
    unfolding DR_def rm_equations_def rm_equations_relation_def by (auto simp: defs)

    define r_list where "r_list \<equiv> map r' [0..<n]"
    define z_list where "z_list \<equiv> map z' [0..<n]"
    define s_list where "s_list \<equiv> map s' [0..<Suc m]"

    define ks where "ks \<equiv> [q', b', c', d', e', f'] @ r_list @ z_list @ s_list"

    have "number_of_ex_vars = length ks"
      unfolding number_of_ex_vars_def ks_def r_list_def z_list_def s_list_def by auto

    have A: "peval A' (push_list a ks) = peval A a" for a 
      unfolding A'_def  
      using push_push_simp[of A ks a] unfolding \<open>number_of_ex_vars = length ks\<close> by auto
        

    have q: "peval q (push_list a ks) = q'"
      unfolding q_def ks_def push_list_def by auto
    have b: "peval b (push_list a ks) = b'"
      unfolding b_def ks_def push_list_def by auto
    have c: "peval c (push_list a ks) = c'"
      unfolding c_def ks_def push_list_def by auto
    have d: "peval d (push_list a ks) = d'"
      unfolding d_def ks_def push_list_def by auto
    have e: "peval e (push_list a ks) = e'"
      unfolding e_def ks_def push_list_def by auto
    have f: "peval f (push_list a ks) = f'"
      unfolding f_def ks_def push_list_def by auto

    have r: "(map (\<lambda>P. peval P (push_list a ks)) r) ! x = r' x" if "x < n" for x
      using that unfolding ks_def r_list_def r_def push_list_def 
      using nth_append[of "map r' [0..<n]" "z_list @ s_list"] by auto 

    have z: "(map (\<lambda>P. peval P (push_list a ks)) z) ! x = z' x" if "x < n" for x
      using that unfolding ks_def z_list_def r_list_def z_def push_list_def apply simp
      using nth_append[of "map r' [0..<n] @ map z' [0..<n]" "s_list"]
      by (metis add_diff_cancel_left' gen_length_def length_code length_map length_upt 
          not_add_less1 nth_append nth_map_upt) 

    have s: "(map (\<lambda>P. peval P (push_list a ks)) s) ! x = s' x" if "x < Suc m" for x
      using that unfolding ks_def r_list_def z_list_def s_list_def s_def push_list_def apply simp 
      using nth_append[of "map r' [0..<n] @ map z' [0..<n]" "map s' [0..<m] @ [s' m]" "(2 * n + x)"]
      by (auto) (metis (mono_tags, lifting) add_cancel_left_left diff_zero length_map length_upt 
          less_antisym nth_append nth_append_length nth_map_upt)

    have "eval ([ALLEQ] A' q b c d e f r z s) (push_list a ks)" 
      using all_eq unfolding all_equations_relation_def apply (simp add: defs)
      unfolding A q b c d e f
      using all_equations_invariance[of "(!) (map (\<lambda>P. peval P (push_list a ks)) r)" r' 
                                        "(!) (map (\<lambda>P. peval P (push_list a ks)) z)" z' 
                                        "(!) (map (\<lambda>P. peval P (push_list a ks)) s)" s' 
                                        "peval A a" q' b' c' d' e' f'] r z s
      using r_list_def s_list_def z_list_def by auto

    thus "eval DS a"
      unfolding DS_def using \<open>number_of_ex_vars = length ks\<close> by (auto) 
  qed

  moreover have "is_dioph_rel DS"
    unfolding DS_def
    using all_equations_dioph \<open>length r = n\<close> \<open>length z = n\<close> \<open>length s = Suc m\<close> assms  
    by (auto simp: dioph)
    
  ultimately show ?thesis 
    using is_dioph_rel_def by auto

qed

end

end