header{*Setsum theorems*}

theory SetsumThms = SEQ:

text{*This theory is but a collection of simple properties of the @{text
  setsum} operator. They should be rather obvious.*}

lemma setsum_diff_real: "finite A \<Longrightarrow> (setsum f (A - {a}) :: real) =
    (if a:A then setsum f A - f a else setsum f A)"
  by (erule finite_induct) (auto simp add: insert_Diff_if)

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


lemma assumes fin: "finite X" and inj: "inj s"
  shows setsum_image: "setsum f (s ` X) = setsum (f \<circ> s) X" (*<*)using fin
proof (induct) 
  case empty
  thus ?case by simp
next
  case insert
  with inj show ?case
    by (simp, subst setsum_insert) (auto simp add: inj_on_def)
qed(*>*)

  
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

     
lemma limseq_setsum:
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Sum>n\<in>S. X n m) ----> (\<Sum>n\<in>S. L n)"(*<*)
proof (cases "finite S")
  case True
  thus ?thesis using n
  proof (induct)
    case empty
    show ?case
      by (simp add: LIMSEQ_const)
  next
    case insert
    thus ?case
      by (simp add: LIMSEQ_add)
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def LIMSEQ_const)
qed(*>*)

lemma setsum_le0_real:
  assumes f: "\<forall>i \<in> S. f i \<le> 0"
  shows "(\<Sum>i\<in>S. f i) \<le> (0::real)" (*<*)
proof -
  from f have "(\<Sum>i\<in>S. f i) \<le> (\<Sum>i\<in>S. 0)" 
    by (simp add: setsum_mono_real) 
  thus ?thesis 
    by (simp add: setsum_0)
qed(*>*)


end
