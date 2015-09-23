(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary $\omega$-Word Facts\<close>

theory Words2
  imports "Main" "~~/src/HOL/Library/Omega_Words_Fun" 
begin 

subsection \<open>Suffixes\<close>

-- \<open>Non empty suffixes of finite words - specialised!\<close>

fun suffixes
where
  "suffixes [] = []"
| "suffixes (x#xs) = (suffixes xs) @ [x#xs]"

lemma suffixes_append:
  "suffixes (xs @ ys) = (suffixes ys) @ (map (\<lambda>zs. zs @ ys) (suffixes xs))"
  by (induction xs) simp_all

lemma suffixes_alt_def:
  "suffixes xs = rev (prefix (length xs) (\<lambda>i. drop i xs))"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    show ?case
      by (simp add: subsequence_def suffixes_append snoc rev_map)
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
