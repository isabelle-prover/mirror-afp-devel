theory Horn_Fset
  imports Horn_Inference FSet_Utils
begin

locale horn_fset_impl = horn +
  fixes infer0_impl :: "'a list" and infer1_impl :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a list"
begin

lemma saturate_fold_simp [simp]:
  "fold (\<lambda>xa. case_option None (f xa)) xs None = None"
  by (induct xs) auto

lemma saturate_fold_mono [partial_function_mono]:
  "option.mono_body (\<lambda>f. fold (\<lambda>x. case_option None (\<lambda>y. f (x, y))) xs b)"
  unfolding monotone_def fun_ord_def flat_ord_def
proof (intro allI impI, induct xs arbitrary: b)
  case (Cons a xs)
  show ?case
    using Cons(1)[OF Cons(2), of "x (a, the b)"] Cons(2)[rule_format, of "(a, the b)"]
    by (cases b) auto
qed auto

partial_function (option) saturate_rec :: "'a \<Rightarrow> 'a fset \<Rightarrow> ('a fset) option" where
  "saturate_rec x bs = (if x |\<in>| bs then Some bs else
     fold (\<lambda>x. case_option None (saturate_rec x)) (infer1_impl x bs) (Some (finsert x bs)))"

definition saturate_impl where
  "saturate_impl = fold (\<lambda>x. case_option None (saturate_rec x)) infer0_impl (Some {||})"

end

locale horn_fset = horn_fset_impl +
  assumes infer0: "infer0 = set infer0_impl"
    and infer1: "\<And>x bs. infer1 x (fset bs) = set (infer1_impl x bs)"
begin

lemma saturate_rec_sound:
  "saturate_rec x bs = Some bs' \<Longrightarrow> ({x}, fset bs) \<turnstile> ({}, fset bs')"
proof (induct arbitrary: x bs bs' rule: saturate_rec.fixp_induct)
  case 1 show ?case using option_admissible[of "\<lambda>(x, y) z. _ x y z"]
    by fastforce
next
  case (3 rec)
  have [dest!]: "(set xs, fset ys) \<turnstile> ({}, fset bs')"
    if "fold (\<lambda>x a. case a of None \<Rightarrow> None | Some a \<Rightarrow> rec x a) xs (Some ys) = Some bs'"
    for xs ys using that
  proof (induct xs arbitrary: ys)
    case (Cons a xs)
    show ?case using trans[OF step_mono[OF 3(1)], of a ys _ "set xs" "{}" "fset bs'"] Cons
      by (cases "rec a ys") auto
  qed (auto intro: refl)
  show ?case using propagate[of x "{}" "fset bs", unfolded infer1 Un_empty_left] 3(2)
    by (auto simp: delete split: if_splits intro: trans delete)
qed auto

lemma saturate_impl_sound:
  assumes "saturate_impl = Some B'"
  shows "fset B' = saturate"
proof -
  have "(set xs, fset ys) \<turnstile> ({}, fset bs')"
    if "fold (\<lambda>x a. case a of None \<Rightarrow> None | Some a \<Rightarrow> saturate_rec x a) xs (Some ys) = Some bs'"
    for xs ys bs' using that
  proof (induct xs arbitrary: ys)
    case (Cons a xs)
    show ?case
      using trans[OF step_mono[OF saturate_rec_sound], of a ys _ "set xs" "{}" "fset bs'"] Cons
      by (cases "saturate_rec a ys") auto
  qed (auto intro: refl)
  from this[of infer0_impl "{||}" B'] assms step_sound show ?thesis
    by (auto simp: saturate_impl_def infer0)
qed

lemma saturate_impl_complete:
  assumes "finite saturate"
  shows "saturate_impl \<noteq> None"
proof -
  have *: "fold (\<lambda>x. case_option None (saturate_rec x)) ds (Some bs) \<noteq> None"
    if "fset bs \<subseteq> saturate" "set ds \<subseteq> saturate" for bs ds
    using that
  proof (induct "card (saturate - fset bs)" arbitrary: bs ds rule: less_induct)
    case less
    show ?case using less(3)
    proof (induct ds)
      case (Cons d ds)
      have "infer1 d (fset bs) \<subseteq> saturate" using less(2) Cons(2)
        unfolding infer1_def by (auto intro: saturate.infer)
      moreover have "card (saturate - fset (finsert d bs)) < card (saturate - fset bs)" if "d \<notin> fset bs"
        using Cons(2) assms that
        by (metis DiffI Diff_insert card_Diff1_less finite_Diff finsert.rep_eq in_mono insertCI list.simps(15))
      ultimately show ?case using less(1)[of "finsert d bs" "infer1_impl d bs @ ds"] less(2) Cons assms
        unfolding fold.simps comp_def option.simps
        apply (subst saturate_rec.simps)
        apply (auto simp flip: saturate_rec.simps split!: if_splits simp: infer1)
        apply (simp add: saturate_rec.simps)
        done
    qed simp
  qed
  show ?thesis using *[of "{||}" "infer0_impl"] inv_start by (simp add: saturate_impl_def infer0)
qed

end

lemmas [code] = horn_fset_impl.saturate_rec.simps horn_fset_impl.saturate_impl_def

end