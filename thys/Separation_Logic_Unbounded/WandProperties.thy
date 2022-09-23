section \<open>Properties of Magic Wands\<close>

theory WandProperties
  imports Distributivity
begin

context logic
begin

lemma modus_ponens:
  "Star P (Wand P Q), \<Delta> \<turnstile> Q"
proof (rule entailsI)
  fix \<sigma> s
  assume "\<sigma>, s, \<Delta> \<Turnstile> Star P (Wand P Q)"
  show "\<sigma>, s, \<Delta> \<Turnstile> Q"
    using \<open>\<sigma>, s, \<Delta> \<Turnstile> Star P (Wand P Q)\<close> commutative by force
qed

lemma transitivity:
  "Star (Wand A B) (Wand B C), \<Delta> \<turnstile> Wand A C"
proof (rule entailsI)
  fix \<sigma> s
  assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Star (Wand A B) (Wand B C)"
  then obtain ab bc where "Some \<sigma> = ab \<oplus> bc" "ab, s, \<Delta> \<Turnstile> Wand A B" "bc, s, \<Delta> \<Turnstile> Wand B C"
    by auto
  show "\<sigma>, s, \<Delta> \<Turnstile> Wand A C"
  proof (rule sat_wand)
    fix a \<sigma>'
    assume asm1: "a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a"
    then obtain aab where "Some aab = ab \<oplus> a"
      by (metis \<open>Some \<sigma> = ab \<oplus> bc\<close> asso3 commutative compatible_def option.exhaust_sel)
    then have "Some \<sigma>' = aab \<oplus> bc"
      by (metis \<open>Some \<sigma> = ab \<oplus> bc\<close> asm1 asso1 commutative)
    moreover have "aab, s, \<Delta> \<Turnstile> B"
      using \<open>Some aab = ab \<oplus> a\<close> \<open>ab, s, \<Delta> \<Turnstile> Wand A B\<close> asm1 by auto
    ultimately show "\<sigma>', s, \<Delta> \<Turnstile> C"
      using \<open>bc, s, \<Delta> \<Turnstile> Wand B C\<close> commutative by auto
  qed
qed

lemma currying1:
  "Wand (Star A B) C, \<Delta> \<turnstile> Wand A (Wand B C)"
proof (rule entailsI)
  fix \<sigma> s
  assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Wand (Star A B) C"
  show "\<sigma>, s, \<Delta> \<Turnstile> Wand A (Wand B C)"
  proof (rule sat_wand)
    fix a \<sigma>'
    assume asm1: "a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a"
    show "\<sigma>', s, \<Delta> \<Turnstile> Wand B C"
    proof (rule sat_wand)
      fix b \<sigma>''
      assume asm2: "b, s, \<Delta> \<Turnstile> B \<and> Some \<sigma>'' = \<sigma>' \<oplus> b"
      then obtain ab where "Some ab = a \<oplus> b"
        by (metis asm1 asso2 compatible_def option.collapse)
      then have "ab, s, \<Delta> \<Turnstile> Star A B"
        using asm1 asm2 by auto
      moreover have "Some \<sigma>'' = \<sigma> \<oplus> ab"
        by (metis \<open>Some ab = a \<oplus> b\<close> asm1 asm2 asso1)
      ultimately show "\<sigma>'', s, \<Delta> \<Turnstile> C"
        using asm0 sat.simps(3) by blast
    qed
  qed
qed

lemma currying2:
  "Wand A (Wand B C), \<Delta> \<turnstile> Wand (Star A B) C"
proof (rule entailsI)
  fix \<sigma> s
  assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Wand A (Wand B C)"
  show "\<sigma>, s, \<Delta> \<Turnstile> Wand (Star A B) C"
  proof (rule sat_wand)
    fix ab \<sigma>'
    assume asm1: "ab, s, \<Delta> \<Turnstile> Star A B \<and> Some \<sigma>' = \<sigma> \<oplus> ab"
    then obtain a b where "Some ab = a \<oplus> b" "a, s, \<Delta> \<Turnstile> A" "b, s, \<Delta> \<Turnstile> B"
      by auto
    then obtain bc where "Some bc = \<sigma> \<oplus> a"
      by (metis asm1 asso3 compatible_def option.exhaust_sel)
    then have "bc, s, \<Delta> \<Turnstile> Wand B C"
      using \<open>a, s, \<Delta> \<Turnstile> A\<close> asm0 by auto
    moreover have "Some \<sigma>' = bc \<oplus> b"
      by (metis \<open>Some ab = a \<oplus> b\<close> \<open>Some bc = \<sigma> \<oplus> a\<close> asm1 asso1)
    ultimately show "\<sigma>', s, \<Delta> \<Turnstile> C"
      using \<open>b, s, \<Delta> \<Turnstile> B\<close> sat.simps(3) by blast
  qed
qed

lemma distribution:
  "Star (Wand A B) C, \<Delta> \<turnstile> Wand A (Star B C)"
proof (rule entailsI)
  fix \<sigma> s
  assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Star (Wand A B) C"
  then obtain ab c where "Some \<sigma> = ab \<oplus> c" "ab, s, \<Delta> \<Turnstile> Wand A B" "c, s, \<Delta> \<Turnstile> C"
    by auto
  show "\<sigma>, s, \<Delta> \<Turnstile> Wand A (Star B C)"
  proof (rule sat_wand)
    fix a \<sigma>'
    assume asm1: "a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a"
    then obtain b where "Some b = ab \<oplus> a"
      by (metis \<open>Some \<sigma> = ab \<oplus> c\<close> asso3 commutative compatible_def option.exhaust_sel)
    then have "b, s, \<Delta> \<Turnstile> B"
      using \<open>ab, s, \<Delta> \<Turnstile> Wand A B\<close> asm1 by force
    moreover have "Some \<sigma>' = b \<oplus> c"
      by (metis \<open>Some \<sigma> = ab \<oplus> c\<close> \<open>Some b = ab \<oplus> a\<close> asm1 asso1 commutative)
    ultimately show "\<sigma>', s, \<Delta> \<Turnstile> Star B C"
      using \<open>c, s, \<Delta> \<Turnstile> C\<close> sat.simps(2) by blast
  qed
qed

lemma adjunct1:
  assumes "A, \<Delta> \<turnstile> Wand B C"
  shows "Star A B, \<Delta> \<turnstile> C"
proof (rule entailsI)
  fix \<sigma> s
  assume "\<sigma>, s, \<Delta> \<Turnstile> Star A B"
  then show "\<sigma>, s, \<Delta> \<Turnstile> C"
    using assms entails_def by force
qed

lemma adjunct2:
  assumes "Star A B, \<Delta> \<turnstile> C"
  shows "A, \<Delta> \<turnstile> Wand B C"
proof (rule entailsI)
  fix \<sigma> s
  assume "\<sigma>, s, \<Delta> \<Turnstile> A"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Wand B C"
    by (meson assms entails_def sat.simps(2) sat_wand)
qed


end

end
