theory List_Aux
imports
  "List-Index.List_Index"
begin

section \<open>Auxiliary List Lemmas\<close>

lemma nth_rotate_conv_nth1_conv_nth:
  assumes "m < length xs"
  shows "rotate1 xs ! m = xs ! (Suc m mod length xs)"
  using assms
proof (induction xs arbitrary: m)
  case (Cons x xs)
  show ?case
  proof (cases "m < length xs")
    case False
    with Cons.prems have "m = length xs" by force
    then show ?thesis by (auto simp: nth_append)
  qed (auto simp: nth_append)
qed simp

lemma nth_rotate_conv_nth:
  assumes "m < length xs"
  shows "rotate n xs ! m = xs ! ((m + n) mod length xs)"
  using assms
proof (induction n arbitrary: m)
  case 0 then show ?case by simp
next
  case (Suc n)
  show ?case
  proof cases
    assume "m + 1 < length xs"
    with Suc show ?thesis using Suc by (auto simp: nth_rotate_conv_nth1_conv_nth)
  next
    assume "\<not>(m + 1 < length xs)"
    with Suc have "m + 1 = length xs" "0 < length xs" by auto
    moreover
    { have "Suc (m + n) mod length xs = (Suc m + n) mod length xs"
        by auto
      also have "\<dots> = n mod length xs" using \<open>m + 1 = _\<close> by simp
      finally have "Suc (m + n) mod length xs = n mod length xs" .}
    ultimately
    show ?thesis by (auto simp: nth_rotate_conv_nth1_conv_nth Suc.IH)
  qed
qed

end
