theory Bucket_Insert_Verification
  imports 
    "../abs-proof/Abs_Bucket_Insert_Verification"
    "../def/Bucket_Insert"
begin
section "Bucket Insert"

lemma abs_bucket_insert_step_cons:
  assumes "bucket_insert_step (B, SA, Suc i) (\<alpha>, T, a # xs) = (B1, SA1, j1)"
  and     "bucket_insert_step (B, SA, i) (\<alpha>, T, xs) = (B2, SA2, j2)"
shows "B1 = B2 \<and> SA1 = SA2"
  by (metis assms(1) assms(2) bucket_insert_step.simps nth_Cons_Suc prod.sel(1) prod.sel(2))

lemma abs_bucket_insert_base_cons':
  assumes  "repeat n bucket_insert_step (B, SA, Suc i) (\<alpha>, T, x # xs) = (B1, SA1, j1)"
  and      "repeat n bucket_insert_step (B, SA, i) (\<alpha>, T, xs) = (B2, SA2, j2)"
shows "B1 = B2 \<and> SA1 = SA2"
  using assms
proof (induct n arbitrary: B SA i)
  case 0
  then show ?case 
    by (simp add: repeat_0)
next
  case (Suc n)
  note IH = this

  let ?b = "\<alpha> (T ! (xs ! i))"
  let ?k = "B ! ?b - Suc 0"

  have "bucket_insert_step (B, SA, Suc i) (\<alpha>, T, x # xs)
          = (B[?b := ?k], SA[?k := xs ! i], Suc (Suc i))"
    by (metis bucket_insert_step.simps nth_Cons_Suc)
  with IH(2) repeat_step_forward[of n bucket_insert_step "(B, SA, Suc i)" "(\<alpha>, T, x # xs)"]
  have "repeat n bucket_insert_step (B[?b := ?k], SA[?k := xs ! i], Suc (Suc i)) (\<alpha>, T, x # xs)
          = (B1, SA1, j1)"
    by simp
  moreover
  have "bucket_insert_step (B, SA, i) (\<alpha>, T, xs) = (B[?b := ?k], SA[?k := xs ! i], Suc i)"
    by (metis bucket_insert_step.simps)
  with IH(3) repeat_step_forward[of n bucket_insert_step "(B, SA, i)" "(\<alpha>, T, xs)"]
  have "repeat n bucket_insert_step (B[?b := ?k], SA[?k := xs ! i], Suc i) (\<alpha>, T, xs)
          = (B2, SA2, j2)"
    by simp
  ultimately show ?case
    using IH(1)[of "B[?b := ?k]" "SA[?k := xs ! i]" "Suc i"]
    by blast
qed

lemma bucket_insert_base_cons:
  assumes "b = \<alpha> (T ! a)"
  and     "k = B ! b - Suc 0"
  and     "bucket_insert_base \<alpha> T B SA (a # xs) = (B1, SA1, j1)"
  and     "bucket_insert_base \<alpha> T (B[b := k]) (SA[k := a]) xs = (B2, SA2, j2)"
shows "B1 = B2 \<and> SA1 = SA2"
proof -
  from assms(1,2)
  have "bucket_insert_step (B, SA, 0) (\<alpha>, T, a # xs) = (B[b := k], SA[k := a], Suc 0)"
    by (metis bucket_insert_step.simps nth_Cons_0)
  with assms(3)[simplified bucket_insert_base_def, simplified]
       repeat_step_forward[of "length xs" bucket_insert_step "(B, SA, 0)" "(\<alpha>, T, a # xs)"]
  have A: "repeat (length xs) bucket_insert_step (B[b := k], SA[k := a], Suc 0) (\<alpha>, T, a # xs)
            = (B1, SA1, j1)"
    by simp
  with abs_bucket_insert_base_cons'[of "length xs" "B[b := k]" "SA[k := a]" 0 \<alpha> T a xs B1 SA1 j1 B2 SA2 j2]
       assms(4)[simplified bucket_insert_base_def]
  show ?thesis
    by simp
qed
  
lemma bucket_insert_cons:
  assumes "b = \<alpha> (T ! a)"
  and     "k = B ! b - Suc 0"
shows "bucket_insert \<alpha> T B SA (a # xs) = bucket_insert \<alpha> T (B[b := k]) (SA[k := a]) xs"
  by (clarsimp simp: bucket_insert_def Let_def bucket_insert_base_cons[of _ \<alpha>, OF assms]
               split: prod.splits)

lemma abs_bucket_insert_eq:
  "abs_bucket_insert \<alpha> T B SA xs = bucket_insert \<alpha> T B SA xs"
proof (induct xs arbitrary: B SA)
  case Nil
  then show ?case
    unfolding bucket_insert_def bucket_insert_base_def
    by (simp add: repeat_0)
next
  case (Cons a xs)
  note IH = this

  let ?b = "\<alpha> (T ! a)"
  let ?k = "B ! ?b - Suc 0"

  have "abs_bucket_insert \<alpha> T B SA (a # xs) = abs_bucket_insert \<alpha> T (B[?b := ?k]) (SA[?k := a]) xs"
    by (meson abs_bucket_insert.simps(2))
  moreover
  from bucket_insert_cons[of ?b \<alpha> T a ?k B SA xs, simplified]
  have "bucket_insert \<alpha> T B SA (a # xs) = bucket_insert \<alpha> T (B[?b := ?k]) (SA[?k := a]) xs" .
  ultimately show ?case
    using IH[of "B[?b := ?k]" "SA[?k := a]"]
    by simp
qed

end