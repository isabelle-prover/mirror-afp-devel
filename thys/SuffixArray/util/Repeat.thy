theory Repeat
  imports Main
begin

section "Repeat Function At Most N Times"

fun repeatatm :: "nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a"
  where
"repeatatm 0 _ _ acc _ = acc" |
"repeatatm (Suc n) f g acc obsv = (if f acc obsv then acc else repeatatm n f g (g acc obsv) obsv)"

declare repeatatm.simps[simp del]

subsection "Step and early termination lemmas"

lemma repeatatm_step_stop_Suc:
  "f (repeatatm n f g a b) b
    \<Longrightarrow> repeatatm (Suc n) f g a b = repeatatm n f g a b"
proof (induct n arbitrary: a)
  case 0
  then show ?case
    by (simp add: repeatatm.simps)
next
  case (Suc n a)
  note IH = this
  show ?case
  proof (cases "f a b")
    assume "f a b"
    then show ?case
      by (simp add: repeatatm.simps)
  next
    assume "\<not> f a b"
    with IH(2)
    have "f (repeatatm n f g (g a b) b) b"
      by (simp add: repeatatm.simps)
    with IH(1)
    have "repeatatm (Suc n) f g (g a b) b = repeatatm n f g (g a b) b"
      by blast
    then show ?case
      by (simp add: repeatatm.simps)
  qed
qed

lemma repeatatm_step:
  "\<not>f (repeatatm n f g a b) b
    \<Longrightarrow> repeatatm (Suc n) f g a b = g (repeatatm n f g a b) b"
proof (induct n arbitrary: a)
  case 0
  then show ?case
    by (simp add: repeatatm.simps)
next
  case (Suc n a)
  note IH = this
  show ?case
  proof (cases "f a b")
    assume "f a b"
    with IH(2)
    show ?case
      by (simp add: repeatatm.simps)
  next
    assume "\<not> f a b"
    with IH(2)
    have "\<not> f (repeatatm n f g (g a b) b) b"
      by (simp add: repeatatm.simps)
    with IH(1)
    have "repeatatm (Suc n) f g (g a b) b = g (repeatatm n f g (g a b) b) b"
      by blast
    then show ?case
      by (simp add: repeatatm.simps \<open>\<not> f a b\<close>)
  qed
qed

lemma repeatatm_step_forward:
  "\<not>f a b \<Longrightarrow> repeatatm (Suc n) f g a b = repeatatm n f g (g a b) b"
  by (induct n arbitrary: a; simp add: repeatatm.simps)

lemma repeatatm_stop_Suc:
  "\<lbrakk>f (repeatatm n f g a b) b\<rbrakk> \<Longrightarrow> f (repeatatm (Suc n) f g a b) b"
proof (induct n arbitrary: a)
  case 0
  then show ?case
    by (simp add: repeatatm.simps)
next
  case (Suc n a)
  note IH = this
  show ?case
  proof (cases "f a b")
    assume "f a b"
    then show ?case
      by (simp add: repeatatm.simps)
  next
    assume "\<not> f a b"
    with IH(2)
    have "f (repeatatm n f g (g a b) b) b"
      by (simp add: repeatatm.simps)
    with IH(1)
    have "f (repeatatm (Suc n) f g (g a b) b) b"
      by blast
    then show ?case
      by (simp add: repeatatm.simps)
  qed
qed

lemma repeatatm_stop:
  "\<lbrakk>f (repeatatm n f g a b) b; n \<le> m\<rbrakk> \<Longrightarrow> f (repeatatm m f g a b) b"
proof (induct m arbitrary: a n)
  case 0
  then show ?case
    by simp
next
  case (Suc m a n)
  note IH = this
  show ?case
  proof (cases "n \<le> m")
    assume "n \<le> m"
    with repeatatm_stop_Suc[of f m g a b] IH(1)[OF IH(2)]
    show ?case
      by simp
  next
    assume "\<not> n \<le> m"
    with IH(2,3)
    show ?case
      using le_Suc_eq by blast
  qed
qed


lemma repeatatm_step_stop:
  "\<lbrakk>f (repeatatm n f g a b) b; n \<le> m\<rbrakk> \<Longrightarrow> repeatatm m f g a b = repeatatm n f g a b"
proof (induct m arbitrary: a n)
  case 0
  then show ?case
    by simp
next
  case (Suc m a n)
  note IH = this
  show ?case
  proof (cases "n \<le> m")
    assume "n \<le> m"
    with repeatatm_step_stop_Suc[of f m g a b] IH(2) IH(1)[OF IH(2)]
    show ?case
      by simp
  next
    assume "\<not> n \<le> m"
    then show ?case
      using Suc.prems(2) le_SucE by blast
  qed
qed

lemma repeatatm_not_stop_Suc:
  "\<not>f (repeatatm (Suc n) f g a b) b \<Longrightarrow> \<not>f (repeatatm n f g a b) b"
  apply (rule contrapos_nn[where Q = "f (repeatatm (Suc n) f g a b) b"]; simp)
  using repeatatm_stop_Suc[of f n g a b] by simp

lemma repeatatm_maintain_inv:
  assumes "\<And>a. P a \<Longrightarrow> P (g a b)"
  shows "P a \<Longrightarrow> P (repeatatm n f g a b)"
proof (induct n arbitrary: a)
  case 0
  then show ?case
    by (simp add: repeatatm.simps)
next
  case (Suc n a)
  note IH = this

  from IH(1)[OF IH(2)]
  have "P (repeatatm n f g a b)"
    by assumption

  with `\<And>a. P a \<Longrightarrow> P (g a b)`
  show ?case
    by (metis repeatatm_step repeatatm_step_stop_Suc)
qed

section "Repeat Function N Times"

definition repeat :: "nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a"
  where
"repeat n f a b = repeatatm n (\<lambda>x y. False) f a b"

lemma repeat_0:
  "repeat 0 f a b = a"
  by (simp add: repeat_def repeatatm.simps(1))

lemma repeat_step:
  "repeat (Suc n) f a b = f (repeat n f a b) b"
  unfolding repeat_def
  by (simp add: repeatatm_step)

lemma repeat_step_forward:
  "repeat (Suc n) f a b = repeat n f (f a b) b"
  unfolding repeat_def
  by (simp add: repeatatm_step_forward)

lemma repeat_maintain_inv:
  assumes "\<And>a. P a \<Longrightarrow> P (f a b)"
  shows "P a \<Longrightarrow> P (repeat n f a b)"
  by (simp add: assms repeat_def repeatatm_maintain_inv)

lemma repeat_eq_fold:
  "repeat n f a b = fold (\<lambda>_ a. f a b) [0..<n] a"
  apply (induct n)
   apply (simp add: repeat_def repeatatm.simps)
  apply (subst repeat_step)
  apply simp
  done

end