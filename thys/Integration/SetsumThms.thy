header{*Setsum theorems*}

theory SetsumThms = SEQ:

text{*This theory is but a collection of simple properties of the @{text
  setsum} operator. They should be rather obvious.*}

(* in future: finite_setsum_diff1 *)
lemma setsum_diff_real: "finite A \<Longrightarrow> (setsum f (A - {a}) :: real) =
    (if a:A then setsum f A - f a else setsum f A)"
  by (erule finite_induct) (auto simp add: insert_Diff_if)

(* in future: setsum_mult *)
lemma setsum_times_real: "(a::real) * (\<Sum>i\<in>R. f i) = (\<Sum>i\<in>R. a*f i)" (*<*)
proof (cases "finite R")
  case True
  thus ?thesis 
  proof (induct)
    case empty
    thus ?case by simp
  next
    case insert
    thus ?case
      by (simp add: right_distrib) 
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def)
qed(*>*)

(* in future: setsum_mono *)
lemma setsum_mono_real: 
  assumes le: "\<And>i. i\<in>K \<Longrightarrow> f i \<le> (g i::real)"
  shows "(\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"(*<*)
proof (cases "finite K")
  case True
  thus ?thesis using le
  proof (induct)
    case empty
    thus ?case by simp
  next
    case insert
    thus ?case
      by force
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def)
qed(*>*)

end
