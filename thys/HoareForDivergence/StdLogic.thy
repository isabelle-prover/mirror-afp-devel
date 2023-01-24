section "A standard total correctness Hoare logic"

theory StdLogic imports WhileLang begin

(* -- inference rules for a standard total-correctness Hoare logic -- *)

inductive hoare :: "(state \<Rightarrow> bool) \<Rightarrow> prog \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool" where
  h_skip[simp,intro!]: "hoare P Skip P"
| h_assign[simp,intro!]: "hoare (\<lambda>s. Q (subst n x s)) (Assign n x) Q"
| h_print[simp,intro!]: "hoare (\<lambda>s. Q (print x s)) (Print x) Q"
| h_seq[intro]: "hoare P p M \<Longrightarrow> hoare M q Q \<Longrightarrow> hoare P (Seq p q) Q"
| h_if[intro!]    : "hoare (\<lambda>s. P s \<and>  guard x s) p Q
        \<Longrightarrow> hoare (\<lambda>s. P s \<and> ~guard x s) q Q \<Longrightarrow> hoare P (If x p q) Q"
| h_while : "(\<And>s0. hoare (\<lambda>s. P s \<and> guard x s \<and> s = s0) p (\<lambda>s. P s \<and> R s s0))
        \<Longrightarrow> wfP R \<Longrightarrow> hoare P (While x p) (\<lambda>s. P s \<and> ~guard x s)"
| h_weaken: "(\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> hoare P' p Q' \<Longrightarrow> (\<And>s. Q' s \<Longrightarrow> Q s) \<Longrightarrow> hoare P p Q"

(* -- semantics -- *)

definition hoare_sem :: "(state \<Rightarrow> bool) \<Rightarrow> prog \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare_sem P p Q \<equiv>
    (\<forall>s. P s \<longrightarrow> (\<exists>t. terminates s p t \<and> Q t))"

end