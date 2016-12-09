(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Material to be moved to HOL\<close>

theory PP_Auxiliary
imports
  Main
begin

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
