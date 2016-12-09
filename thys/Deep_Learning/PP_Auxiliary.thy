(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Material to be moved to HOL finally\<close>

theory PP_Auxiliary
imports
  Main
begin

subsection \<open>Already taken over into Isabelle repository\<close>

subsection \<open>Not yet taken over into Isabelle repository\<close>

(*context cancel_comm_monoid_add
begin

lemma add_left_left_cancel [simp]:
  "a + b = a \<longleftrightarrow> b = 0"
proof (rule iffI)
  assume "a + b = a"
  then have "a + b = a + 0" by simp
  then show "b = 0" by (rule add_left_imp_eq)
qed simp

lemma add_left_right_cancel [simp]:
  "b + a = a \<longleftrightarrow> b = 0"
  by (simp add: ac_simps)

lemma add_right_left_cancel [simp]:
  "a = a + b \<longleftrightarrow> b = 0"
  using add_left_left_cancel [of a b] by (auto simp only: ac_simps)

lemma add_right_right_cancel [simp]:
  "a = b + a \<longleftrightarrow> b = 0"
  by (simp add: ac_simps)

end*)

lemma (in comm_monoid_set) mono_neutral_cong:
  assumes [simp]: "finite T" "finite S"
  and * [rule_format]: "\<forall>i \<in> T - S. h i = z" "\<forall>i \<in> S - T. g i = z"
  and gh: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x = h x" shows "F g S = F h T"
proof-
  have "F g S = F g (S \<inter> T)"
    by(rule mono_neutral_right)(auto intro: *)
  also have "\<dots> = F h (S \<inter> T)" using refl gh by(rule cong)
  also have "\<dots> = F h T"
    by(rule mono_neutral_left)(auto intro: *)
  finally show ?thesis .
qed

end
