(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary $\omega$-Word Facts\<close>

theory Words2
imports Main "~~/src/HOL/Library/Omega_Words_Fun"
begin 

subsection \<open>Suffixes\<close>
-- \<open>Compute non empty suffixes of finite words\<close>

fun suffixes
where
  "suffixes [] = []"
| "suffixes (x#xs) = (suffixes xs) @ [x#xs]"

lemma suffixes_append:
  "suffixes (xs @ ys) = (suffixes ys) @ (map (\<lambda>xss. xss @ ys) (suffixes xs))"
  by (induction xs) simp_all

lemma suffixes_alt_def:
  "suffixes xs = rev (map (\<lambda>i. drop i xs) [0..<length xs])"  
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    have "suffixes (xs @ [x]) = [x] # (map (\<lambda>xss. xss @ [x]) (suffixes xs))"
      unfolding suffixes_append by simp
    also
    have "\<dots> = rev ([[x]]) @ rev (map (\<lambda>xss. xss @ [x]) (map (\<lambda>i. drop i xs) [0..<length xs]))"
      using rev.simps(2) rev_map rev_rev_ident rev_append snoc.IH by metis
    also
    have "\<dots> = rev (map (\<lambda>xss. xss @ [x]) (map (\<lambda>i. drop i xs) [0..<length xs]) @ [[x]])"
      using rev_append by fastforce
    also
    have "\<dots> = rev (map (\<lambda>i. drop i (xs @ [x])) [0..<length xs] @ [[x]])"
      unfolding map_map comp_def using drop_append by simp
    also
    have "\<dots> = rev (map (\<lambda>i. drop i (xs @ [x])) [0..<length (xs @ [x])])"
      unfolding length_append_singleton upt_Suc_append[OF le0] by simp
    finally
    show ?case .
qed simp

subsection \<open>Limit\<close>

lemma limit_range_suffix:
  assumes "limit r = range (suffix i r)"
  shows "limit r = range (suffix (i + j) r)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = range (suffix i r)"
    using assms .
  moreover
  have "\<dots> \<supseteq> ?rhs"
    by (metis (mono_tags, hide_lams) calculation imageI image_subsetI iso_tuple_UNIV_I suffix_nth suffix_suffix)
  moreover
  have "\<dots> \<supseteq> ?lhs" 
    using limit_in_range_suffix .
  ultimately
  show "?lhs = ?rhs"
    by (metis antisym_conv limit_in_range_suffix)
qed

end
