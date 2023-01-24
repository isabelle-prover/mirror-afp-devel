section "A Hoare logic for diverging programs"

theory DivLogic
  imports WhileLang StdLogic CoinductiveLemmas
begin

definition ignores_output :: "(val \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> bool" where
  "ignores_output H \<equiv> \<forall>i s out1 out2. H i (s,out1) = H i (s,out2)"

inductive pohjola where
  p_seq_d: "pohjola P p (D::val llist \<Rightarrow> bool) \<Longrightarrow> pohjola P (Seq p q) D"
| p_seq_h: "hoare P p M \<Longrightarrow> pohjola M q D \<Longrightarrow> pohjola P (Seq p q) D"
| p_if: "pohjola (\<lambda>s. P s \<and>  guard x s) p D \<Longrightarrow>
   pohjola (\<lambda>s. P s \<and> ~guard x s) q D \<Longrightarrow> pohjola P (If x p q) D"
| (* proving that a non-terminating loop diverges *)
  p_while1: "(\<And>s. P s \<Longrightarrow>
         (\<exists>H ev.
           guard x s \<and> H 0 s \<and> ignores_output H \<and>
           D (flat (LCons (output_of s) (inf_llist ev))) \<and>
           (\<forall>i. hoare (\<lambda>s. H i s \<and> output_of s = []) p
                     (\<lambda>s. H (i+1) s \<and> output_of s = ev i \<and> guard x s)))) \<Longrightarrow>
    pohjola P (While x p) D"
| (* proving that the ith execution of the body of a loop causes
     something within the body to diverge *)
  p_while2: "(\<forall>s. P s \<longrightarrow> guard x s) \<Longrightarrow> wfP R \<Longrightarrow>
   (\<forall>s0. hoare (\<lambda>s. P s \<and> b s \<and> s = s0) p (\<lambda>s. P s \<and> R s s0)) \<Longrightarrow>
    pohjola (\<lambda>s. P s \<and> ~b s) p D \<Longrightarrow> pohjola P (While x p) D"
| p_const: "pohjola (\<lambda>s. False) p D"
| p_case: "pohjola (\<lambda>s. P s \<and> b s) p D \<Longrightarrow> pohjola (\<lambda>s. P s \<and> ~b s) p D \<Longrightarrow> pohjola P p D"
| p_weaken: "(\<forall>s. P s \<longrightarrow> P' s) \<Longrightarrow> pohjola P' p D' \<Longrightarrow> (\<forall>s. D' s \<longrightarrow> D s) \<Longrightarrow> pohjola P p D"
print_theorems

(* -- semantics -- *)

definition pohjola_sem where
  "pohjola_sem P p D \<equiv>
    \<forall>s. P s \<longrightarrow> (\<exists>l. diverges s p l \<and> D l)"

end