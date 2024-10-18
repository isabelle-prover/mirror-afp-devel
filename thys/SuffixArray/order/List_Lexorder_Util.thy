theory List_Lexorder_Util
  imports
    "HOL-Library.List_Lexorder"
begin

lemma same_equiv_def:
  "(\<forall>j<n. s ! (i + j) = s ! Suc (i + j)) = (\<forall>j\<le>n. s ! (i + j) = s ! i)"
proof safe
  fix j
  assume "\<forall>j<n. s ! (i + j) = s ! Suc (i + j)" "j \<le> n"
  then show "s ! (i + j) = s ! i"
  proof (induct n arbitrary: j)
    case 0
    then show ?case
      by simp
  next
    case (Suc n j)
    note IH = this
    show ?case
    proof (cases j)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc m)
      with IH(1)[of m] IH(2,3)
      have "s ! (i + m) = s ! i"
        by (meson Suc_le_mono less_Suc_eq)
      then show ?thesis
        using Suc Suc.prems(1) Suc.prems(2) by force
    qed
  qed
next
  fix j
  assume "\<forall>j\<le>n. s ! (i + j) = s ! i" "j < n"
  then show "s ! (i + j) = s ! Suc (i + j)"
    using less_eq_Suc_le by fastforce
qed

lemma list_less_ex:
  "xs < ys \<longleftrightarrow>
   (\<exists>b c as bs cs. xs = as @ b # bs \<and> ys = as @ c # cs \<and> b < c) \<or>
   (\<exists>c cs. ys = xs @ c # cs)"
  by (clarsimp simp: List_Lexorder.list_less_def lexord_def; blast)

end