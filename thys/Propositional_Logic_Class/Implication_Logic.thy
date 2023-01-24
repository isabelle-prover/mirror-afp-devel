chapter \<open> Implication Logic \label{sec:implicational-intuitionistic-logic} \<close>

theory Implication_Logic
  imports Main
begin

text \<open> This theory presents the pure implicational fragment of
       intuitionistic logic. That is to say, this is the fragment of
       intuitionistic logic containing \<^emph>\<open>implication only\<close>, and no other
       connectives nor \<^emph>\<open>falsum\<close> (i.e., \<open>\<bottom>\<close>). We shall refer to this logic as
       \<^emph>\<open>implication logic\<close> in future discussion. \<close>

text \<open> For further reference see @{cite urquhartImplicationalFormulasIntuitionistic1974}.\<close>

section \<open> Axiomatization \<close>

text \<open> Implication logic can be given by the a Hilbert-style  axiom system,
       following Troelstra and Schwichtenberg
       @{cite \<open>\S 1.3.9, pg. 33\<close> troelstraBasicProofTheory2000}. \<close>

class implication_logic =
  fixes deduction :: "'a \<Rightarrow> bool" ("\<turnstile> _" [60] 55)
  fixes implication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 70)
  assumes axiom_k: "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  assumes axiom_s: "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  assumes modus_ponens: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<psi>"

section \<open> Common Rules \<close>

lemma (in implication_logic) trivial_implication:
  "\<turnstile> \<phi> \<rightarrow> \<phi>"
  by (meson axiom_k axiom_s modus_ponens)

lemma (in implication_logic) flip_implication:
  "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> \<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>"
  by (meson axiom_k axiom_s modus_ponens)

lemma (in implication_logic) hypothetical_syllogism:
  "\<turnstile> (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
  by (meson axiom_k axiom_s modus_ponens)

lemma (in implication_logic) flip_hypothetical_syllogism:
  "\<turnstile> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>)"
  using modus_ponens flip_implication hypothetical_syllogism by blast

lemma (in implication_logic) implication_absorption:
  "\<turnstile> (\<phi> \<rightarrow> \<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>"
  by (meson axiom_k axiom_s modus_ponens)

section \<open> Lists of Assumptions \<close>

subsection \<open> List Implication \<close>

text \<open> Implication given a list of assumptions can be expressed recursively \<close>

primrec (in implication_logic)
  list_implication :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<rightarrow>" 80) where
    "[] :\<rightarrow> \<phi> = \<phi>"
  | "(\<psi> # \<Psi>) :\<rightarrow> \<phi> = \<psi> \<rightarrow> \<Psi> :\<rightarrow> \<phi>"

subsection \<open> Deduction From a List of Assumptions \label{sec:list-deduction}\<close>

text \<open> Deduction from a list of assumptions can be expressed in terms of
       @{term "(:\<rightarrow>)"}. \<close>

definition (in implication_logic) list_deduction :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" (infix ":\<turnstile>" 60)
  where
    "\<Gamma> :\<turnstile> \<phi> \<equiv> \<turnstile> \<Gamma> :\<rightarrow> \<phi>"

subsection \<open> List Deduction as Implication Logic \<close>

text \<open> The relation @{term "(:\<turnstile>)"} may naturally be interpreted as a
       @{term "deduction"} predicate for an instance of implication logic
       for a fixed list of assumptions @{term "\<Gamma>"}. \<close>

text \<open> Analogues of the two axioms of implication logic can be
       naturally stated using list implication. \<close>

lemma (in implication_logic) list_implication_axiom_k:
  "\<turnstile> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
  by (induct \<Gamma>, (simp, meson axiom_k axiom_s modus_ponens)+)

lemma (in implication_logic) list_implication_axiom_s:
  "\<turnstile> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<Gamma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<psi>"
  by (induct \<Gamma>,
      (simp, meson axiom_k axiom_s modus_ponens hypothetical_syllogism)+)

text \<open> The lemmas @{thm list_implication_axiom_k [no_vars]} and
       @{thm list_implication_axiom_s [no_vars]} jointly give rise to an
       interpretation of implication logic, where a list of assumptions
       @{term "\<Gamma>"} play the role of a \<^emph>\<open>background theory\<close> of @{term "(:\<turnstile>)"}. \<close>

context implication_logic begin
interpretation list_deduction_logic:
   implication_logic "\<lambda> \<phi>. \<Gamma> :\<turnstile> \<phi>" "(\<rightarrow>)"
proof qed
  (meson
     list_deduction_def
     axiom_k
     axiom_s
     modus_ponens
     list_implication_axiom_k
     list_implication_axiom_s)+
end

text \<open> The following \<^emph>\<open>weakening\<close> rule can also be derived. \<close>

lemma (in implication_logic) list_deduction_weaken:
  "\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  unfolding list_deduction_def
  using modus_ponens list_implication_axiom_k
  by blast

text \<open> In the case of the empty list, the converse may be established. \<close>

lemma (in implication_logic) list_deduction_base_theory [simp]:
  "[] :\<turnstile> \<phi> \<equiv> \<turnstile> \<phi>"
  unfolding list_deduction_def
  by simp

lemma (in implication_logic) list_deduction_modus_ponens:
  "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<psi>"
  unfolding list_deduction_def
  using modus_ponens list_implication_axiom_s
  by blast

section \<open> The Deduction Theorem \<close>

text \<open> One result in the meta-theory of implication logic
       is the \<^emph>\<open>deduction theorem\<close>, which is a mechanism for moving
       antecedents back and forth from collections of assumptions. \<close>

text \<open> To develop the deduction theorem, the following two lemmas generalize
       @{thm "flip_implication" [no_vars]}. \<close>

lemma (in implication_logic) list_flip_implication1:
  "\<turnstile> (\<phi> # \<Gamma>) :\<rightarrow> \<chi> \<rightarrow> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<chi>)"
  by (induct \<Gamma>,
      (simp,
         meson
           axiom_k
           axiom_s
           modus_ponens
           flip_implication
           hypothetical_syllogism)+)

lemma (in implication_logic) list_flip_implication2:
  "\<turnstile> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> # \<Gamma>) :\<rightarrow> \<chi>"
  by (induct \<Gamma>,
      (simp,
         meson
           axiom_k
           axiom_s
           modus_ponens
           flip_implication
           hypothetical_syllogism)+)

text \<open> Together the two lemmas above suffice to prove a form of
       the deduction theorem: \<close>

theorem (in implication_logic) list_deduction_theorem:
  "(\<phi> # \<Gamma>) :\<turnstile> \<psi> = \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi>"
  unfolding list_deduction_def
  by (metis modus_ponens list_flip_implication1 list_flip_implication2)

section \<open> Monotonic Growth in Deductive Power \<close>

text \<open> In logic, for two sets of assumptions @{term "\<Phi>"} and @{term "\<Psi>"},
        if @{term "\<Psi> \<subseteq> \<Phi>"} then the latter theory @{term "\<Phi>"} is
        said to be \<^emph>\<open>stronger\<close> than former theory @{term "\<Psi>"}.
        In principle, anything a weaker theory can prove a
        stronger theory can prove. One way of saying this is
        that deductive power increases monotonically with as the set of
        underlying assumptions grow. \<close>

text \<open> The monotonic growth of deductive power can be expressed as a
       meta-theorem in implication logic. \<close>

text \<open> The lemma @{thm "list_flip_implication2" [no_vars]} presents a means
       of \<^emph>\<open>introducing\<close> assumptions into a list of assumptions when
       those assumptions have been arrived at by an implication. The next
       lemma presents a means of \<^emph>\<open>discharging\<close> those assumptions, which can
       be used in the monotonic growth theorem to be proved. \<close>

lemma (in implication_logic) list_implication_removeAll:
  "\<turnstile> \<Gamma> :\<rightarrow> \<psi> \<rightarrow> (removeAll \<phi> \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
proof -
  have "\<forall> \<psi>. \<turnstile> \<Gamma> :\<rightarrow> \<psi> \<rightarrow> (removeAll \<phi> \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
  proof(induct \<Gamma>)
    case Nil
    then show ?case by (simp, meson axiom_k)
  next
    case (Cons \<chi> \<Gamma>)
    assume
      inductive_hypothesis: "\<forall> \<psi>. \<turnstile> \<Gamma> :\<rightarrow> \<psi> \<rightarrow> removeAll \<phi> \<Gamma> :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
    moreover {
      assume "\<phi> \<noteq> \<chi>"
      with inductive_hypothesis
      have "\<forall> \<psi>. \<turnstile> (\<chi> # \<Gamma>) :\<rightarrow> \<psi> \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
        by (simp, meson modus_ponens hypothetical_syllogism)
    }
    moreover {
      fix \<psi>
      assume \<phi>_equals_\<chi>: "\<phi> = \<chi>"
      moreover with inductive_hypothesis
      have "\<turnstile> \<Gamma> :\<rightarrow> (\<chi> \<rightarrow> \<psi>) \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<chi> \<rightarrow> \<psi>)" by simp
      hence "\<turnstile> \<Gamma> :\<rightarrow> (\<chi> \<rightarrow> \<psi>) \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
        by (metis
              calculation
              modus_ponens
              implication_absorption
              list_flip_implication1
              list_flip_implication2
              list_implication.simps(2))
      ultimately have "\<turnstile> (\<chi> # \<Gamma>) :\<rightarrow> \<psi> \<rightarrow> removeAll \<phi> (\<chi> # \<Gamma>) :\<rightarrow> (\<phi> \<rightarrow> \<psi>)"
        by (simp,
              metis
                modus_ponens
                hypothetical_syllogism
                list_flip_implication1
                list_implication.simps(2))
    }
    ultimately show ?case by simp
  qed
  thus ?thesis by blast
qed

text \<open> From lemma above presents what is needed to prove that deductive power
       for lists is monotonic. \<close>

theorem (in implication_logic) list_implication_monotonic:
  "set \<Sigma> \<subseteq> set \<Gamma> \<Longrightarrow> \<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
proof -
  assume "set \<Sigma> \<subseteq> set \<Gamma>"
  moreover have "\<forall> \<Sigma> \<phi>. set \<Sigma> \<subseteq> set \<Gamma> \<longrightarrow> \<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
  proof(induct \<Gamma>)
    case Nil
    then show ?case
      by (metis
            list_implication.simps(1)
            list_implication_axiom_k
            set_empty
            subset_empty)
  next
    case (Cons \<psi> \<Gamma>)
    assume
      inductive_hypothesis: "\<forall>\<Sigma> \<phi>. set \<Sigma> \<subseteq> set \<Gamma> \<longrightarrow> \<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> \<Gamma> :\<rightarrow> \<phi>"
    {
      fix \<Sigma>
      fix \<phi>
      assume \<Sigma>_subset_relation: "set \<Sigma> \<subseteq> set (\<psi> # \<Gamma>)"
      have "\<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> (\<psi> # \<Gamma>) :\<rightarrow> \<phi>"
      proof -
        {
          assume "set \<Sigma> \<subseteq> set \<Gamma>"
          hence ?thesis
            by (metis
                    inductive_hypothesis
                    axiom_k modus_ponens
                    flip_implication
                    list_implication.simps(2))
        }
        moreover {
          let ?\<Delta> = "removeAll \<psi> \<Sigma>"
          assume "\<not> (set \<Sigma> \<subseteq> set \<Gamma>)"
          hence "set ?\<Delta> \<subseteq> set \<Gamma>"
            using \<Sigma>_subset_relation by auto
          hence "\<turnstile> ?\<Delta> :\<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> \<Gamma> :\<rightarrow> (\<psi> \<rightarrow> \<phi>)"
            using inductive_hypothesis by auto
          hence "\<turnstile> ?\<Delta> :\<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<psi> # \<Gamma>) :\<rightarrow> \<phi>"
            by (metis
                    modus_ponens
                    flip_implication
                    list_flip_implication2
                    list_implication.simps(2))
          moreover have "\<turnstile> \<Sigma> :\<rightarrow> \<phi> \<rightarrow> ?\<Delta> :\<rightarrow> (\<psi> \<rightarrow> \<phi>)"
            by (simp add: local.list_implication_removeAll)
          ultimately have ?thesis
            using modus_ponens hypothetical_syllogism by blast
        }
        ultimately show ?thesis by blast
     qed
    }
    thus ?case by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open> A direct consequence is that deduction from lists of assumptions
       is monotonic as well: \<close>

theorem (in implication_logic) list_deduction_monotonic:
  "set \<Sigma> \<subseteq> set \<Gamma> \<Longrightarrow> \<Sigma> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  unfolding list_deduction_def
  using modus_ponens list_implication_monotonic
  by blast

section \<open> The Deduction Theorem Revisited \<close>

text \<open> The monotonic nature of deduction allows us to prove another form of
       the deduction theorem, where the assumption being discharged is
       completely removed from the list of assumptions. \<close>

theorem (in implication_logic) alternate_list_deduction_theorem:
    "(\<phi> # \<Gamma>) :\<turnstile> \<psi> = (removeAll \<phi> \<Gamma>) :\<turnstile> \<phi> \<rightarrow> \<psi>"
  by (metis
        list_deduction_def
        modus_ponens
        filter_is_subset
        list_deduction_monotonic
        list_deduction_theorem
        list_implication_removeAll
        removeAll.simps(2)
        removeAll_filter_not_eq)

section \<open> Reflection \<close>

text \<open> In logic the \<^emph>\<open>reflection\<close> principle sometimes refers to when
       a collection of assumptions can deduce any of its members. It is
       automatically derivable from @{thm "list_deduction_monotonic" [no_vars]} among
       the other rules provided. \<close>

lemma (in implication_logic) list_deduction_reflection:
  "\<phi> \<in> set \<Gamma> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  by (metis
        list_deduction_def
        insert_subset
        list.simps(15)
        list_deduction_monotonic
        list_implication.simps(2)
        list_implication_axiom_k
        order_refl)

section \<open> The Cut Rule \<close>

text \<open> \<^emph>\<open>Cut\<close> is a rule commonly presented in sequent calculi, dating
       back to Gerhard Gentzen's \<^emph>\<open>Investigations in Logical Deduction\<close> (1935)
       @{cite gentzenUntersuchungenUeberLogische1935}\<close>

text \<open> The cut rule is not generally necessary in sequent calculi. It can
       often be shown that the rule can be eliminated without reducing the
       power of the underlying logic. However, as demonstrated by George
       Boolos' \<^emph>\<open>Don't Eliminate Cut\<close> (1984) @{cite boolosDonEliminateCut1984},
       removing the rule can often lead to very inefficient proof systems. \<close>

text \<open> Here the rule is presented just as a meta theorem. \<close>

theorem (in implication_logic) list_deduction_cut_rule:
  "(\<phi> # \<Gamma>) :\<turnstile> \<psi> \<Longrightarrow> \<Delta> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>"
  by (metis
        (no_types, lifting)
        Un_upper1
        Un_upper2
        list_deduction_modus_ponens
        list_deduction_monotonic
        list_deduction_theorem
        set_append)

text \<open> The cut rule can also be strengthened to entire lists of propositions. \<close>

theorem (in implication_logic) strong_list_deduction_cut_rule:
    "(\<Phi> @ \<Gamma>) :\<turnstile> \<psi> \<Longrightarrow> \<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>"
proof -
  have "\<forall> \<psi>. (\<Phi> @ \<Gamma> :\<turnstile> \<psi> \<longrightarrow> (\<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi>) \<longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>)"
    proof(induct \<Phi>)
      case Nil
      then show ?case
        by (metis
                Un_iff
                append.left_neutral
                list_deduction_monotonic
                set_append
                subsetI)
    next
      case (Cons \<chi> \<Phi>) assume inductive_hypothesis:
         "\<forall> \<psi>. \<Phi> @ \<Gamma> :\<turnstile> \<psi> \<longrightarrow> (\<forall>\<phi>\<in>set \<Phi>. \<Delta> :\<turnstile> \<phi>) \<longrightarrow> \<Gamma> @ \<Delta> :\<turnstile> \<psi>"
      {
        fix \<psi> \<chi>
        assume "(\<chi> # \<Phi>) @ \<Gamma> :\<turnstile> \<psi>"
        hence A: "\<Phi> @ \<Gamma> :\<turnstile> \<chi> \<rightarrow> \<psi>" using list_deduction_theorem by auto
        assume "\<forall>\<phi> \<in> set (\<chi> # \<Phi>). \<Delta> :\<turnstile> \<phi>"
        hence B: "\<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi>"
          and C: "\<Delta> :\<turnstile> \<chi>" by auto
        from A B have "\<Gamma> @ \<Delta> :\<turnstile> \<chi> \<rightarrow> \<psi>" using inductive_hypothesis by blast
        with C have "\<Gamma> @ \<Delta> :\<turnstile> \<psi>"
          by (meson
                list.set_intros(1)
                list_deduction_cut_rule
                list_deduction_modus_ponens
                list_deduction_reflection)
      }
      thus ?case by simp
    qed
    moreover assume "(\<Phi> @ \<Gamma>) :\<turnstile> \<psi>"
  moreover assume "\<forall> \<phi> \<in> set \<Phi>. \<Delta> :\<turnstile> \<phi>"
  ultimately show ?thesis by blast
qed

section \<open> Sets of Assumptions \<close>

text \<open> While deduction in terms of lists of assumptions is straight-forward
       to define, deduction (and the \<^emph>\<open>deduction theorem\<close>) is commonly given in
       terms of \<^emph>\<open>sets\<close> of propositions.  This formulation is suited to
       establishing strong completeness theorems and compactness theorems. \<close>

text \<open> The presentation of deduction from a set follows the presentation of
       list deduction given for \<^term>\<open>(:\<turnstile>)\<close>. \<close>

section \<open> Definition of Deduction \<close>

text \<open> Just as deduction from a list \<^term>\<open>(:\<turnstile>)\<close> can be defined in
       terms of \<^term>\<open>(:\<rightarrow>)\<close>, deduction from a \<^emph>\<open>set\<close> of assumptions
       can be expressed in terms of \<^term>\<open>(:\<turnstile>)\<close>. \<close>

definition (in implication_logic) set_deduction :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<tturnstile>" 60)
  where
    "\<Gamma> \<tturnstile> \<phi> \<equiv> \<exists> \<Psi>. set \<Psi>  \<subseteq> \<Gamma> \<and> \<Psi> :\<turnstile> \<phi>"

subsection \<open> Interpretation as Implication Logic \<close>

text \<open> As in the case of @{term "(:\<turnstile>)"}, the relation @{term "(\<tturnstile>)"} may be
       interpreted as @{term "deduction"} predicate for a fixed set of
       assumptions @{term "\<Gamma>"}. \<close>

text \<open> The following lemma is given in order to establish this, which asserts
       that every implication logic tautology @{term "\<turnstile> \<phi>"}
       is also a tautology for @{term "\<Gamma> \<tturnstile> \<phi>"}. \<close>

lemma (in implication_logic) set_deduction_weaken:
  "\<turnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  using list_deduction_base_theory set_deduction_def by fastforce

text \<open> In the case of the empty set, the converse may be established. \<close>

lemma (in implication_logic) set_deduction_base_theory:
  "{} \<tturnstile> \<phi> \<equiv> \<turnstile> \<phi>"
  using list_deduction_base_theory set_deduction_def by auto

text \<open> Next, a form of \<^emph>\<open>modus ponens\<close> is provided for @{term "(\<tturnstile>)"}. \<close>

lemma (in implication_logic) set_deduction_modus_ponens:
   "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<psi>"
proof -
  assume "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>"
  then obtain \<Phi> where A: "set \<Phi> \<subseteq> \<Gamma>" and B: "\<Phi> :\<turnstile> \<phi> \<rightarrow> \<psi>"
    using set_deduction_def by blast
  assume "\<Gamma> \<tturnstile> \<phi>"
  then obtain \<Psi> where C: "set \<Psi> \<subseteq> \<Gamma>" and D: "\<Psi> :\<turnstile> \<phi>"
    using set_deduction_def by blast
  from B D have "\<Phi> @ \<Psi> :\<turnstile> \<psi>"
    using list_deduction_cut_rule list_deduction_theorem by blast
  moreover from A C have "set (\<Phi> @ \<Psi>) \<subseteq> \<Gamma>" by simp
  ultimately show ?thesis
    using set_deduction_def by blast
qed

context implication_logic begin
interpretation set_deduction_logic:
  implication_logic "\<lambda> \<phi>. \<Gamma> \<tturnstile> \<phi>" "(\<rightarrow>)"
proof
   fix \<phi> \<psi>
   show "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"  by (metis axiom_k set_deduction_weaken)
next
    fix \<phi> \<psi> \<chi>
    show "\<Gamma> \<tturnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<chi>"
      by (metis axiom_s set_deduction_weaken)
next
    fix \<phi> \<psi>
    show "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<psi>"
      using set_deduction_modus_ponens by metis
qed
end

section \<open> The Deduction Theorem \<close>

text \<open> The next result gives the deduction theorem for @{term "(\<tturnstile>)"}. \<close>

theorem (in implication_logic) set_deduction_theorem:
  "insert \<phi> \<Gamma> \<tturnstile> \<psi> = \<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>"
proof -
  have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> insert \<phi> \<Gamma> \<tturnstile> \<psi>"
    by (metis
            set_deduction_def
            insert_mono
            list.simps(15)
            list_deduction_theorem)
  moreover {
    assume "insert \<phi> \<Gamma> \<tturnstile> \<psi>"
    then obtain \<Phi> where "set \<Phi> \<subseteq> insert \<phi> \<Gamma>" and "\<Phi> :\<turnstile> \<psi>"
      using set_deduction_def by auto
    hence "set (removeAll \<phi> \<Phi>) \<subseteq> \<Gamma>" by auto
    moreover from \<open>\<Phi> :\<turnstile> \<psi>\<close> have "removeAll \<phi> \<Phi> :\<turnstile> \<phi> \<rightarrow> \<psi>"
      using modus_ponens list_implication_removeAll list_deduction_def
      by blast
    ultimately have "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>"
      using set_deduction_def by blast
  }
  ultimately show "insert \<phi> \<Gamma> \<tturnstile> \<psi> = \<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>" by metis
qed

section \<open> Monotonic Growth in Deductive Power \<close>

text \<open> In contrast to the @{term "(:\<turnstile>)"} relation, the proof that the
       deductive power of @{term "(\<tturnstile>)"} grows monotonically with its
       assumptions may be fully automated. \<close>

theorem set_deduction_monotonic:
  "\<Sigma> \<subseteq> \<Gamma> \<Longrightarrow> \<Sigma> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  by (meson dual_order.trans set_deduction_def)

section \<open> The Deduction Theorem Revisited \<close>

text \<open> As a consequence of the fact that @{thm "set_deduction_monotonic" [no_vars]}
       is automatically provable, an alternate \<^emph>\<open>deduction theorem\<close> where the
       discharged assumption is completely removed from the set of assumptions
       is just a consequence of the more conventional
       @{thm "set_deduction_theorem" [no_vars]} rule and some basic set identities. \<close>

theorem (in implication_logic) alternate_set_deduction_theorem:
  "insert \<phi> \<Gamma> \<tturnstile> \<psi> = \<Gamma> - {\<phi>} \<tturnstile> \<phi> \<rightarrow> \<psi>"
  by (metis insert_Diff_single set_deduction_theorem)

section \<open> Reflection \<close>

text \<open> Just as in the case of @{term "(:\<turnstile>)"}, deduction from sets of
       assumptions makes true the \<^emph>\<open>reflection principle\<close> and is
       automatically provable. \<close>

theorem (in implication_logic) set_deduction_reflection:
  "\<phi> \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  by (metis
          Set.set_insert
          list_implication.simps(1)
          list_implication_axiom_k
          set_deduction_theorem
          set_deduction_weaken)

section \<open> The Cut Rule \<close>

text \<open> The final principle of @{term "(\<tturnstile>)"} presented is the \<^emph>\<open>cut rule\<close>. \<close>

text \<open> First, the weak form of the rule is established. \<close>

theorem (in implication_logic) set_deduction_cut_rule:
  "insert \<phi> \<Gamma> \<tturnstile> \<psi> \<Longrightarrow> \<Delta> \<tturnstile> \<phi> \<Longrightarrow> \<Gamma> \<union> \<Delta> \<tturnstile> \<psi>"
proof -
  assume "insert \<phi> \<Gamma> \<tturnstile> \<psi>"
  hence "\<Gamma> \<tturnstile> \<phi> \<rightarrow> \<psi>" using set_deduction_theorem by auto
  hence "\<Gamma> \<union> \<Delta> \<tturnstile> \<phi> \<rightarrow> \<psi>" using set_deduction_def by auto
  moreover assume "\<Delta> \<tturnstile> \<phi>"
  hence "\<Gamma> \<union> \<Delta> \<tturnstile> \<phi>" using set_deduction_def by auto
  ultimately show ?thesis using set_deduction_modus_ponens by metis
qed

text \<open> Another lemma is shown next in order to establish the strong form
       of the cut rule. The lemma shows the existence of a \<^emph>\<open>covering list\<close> of
       assumptions \<^term>\<open>\<Psi>\<close> in the event some set of assumptions
       \<^term>\<open>\<Delta>\<close> proves everything in a finite set of assumptions
       \<^term>\<open>\<Phi>\<close>. \<close>

lemma (in implication_logic) finite_set_deduction_list_deduction:
  assumes "finite \<Phi>"
  and "\<forall> \<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi>"
  shows "\<exists>\<Psi>. set \<Psi> \<subseteq> \<Delta> \<and> (\<forall>\<phi> \<in> \<Phi>. \<Psi> :\<turnstile> \<phi>)"
  using assms
proof(induct \<Phi> rule: finite_induct)
  case empty thus ?case by (metis all_not_in_conv empty_subsetI set_empty)
next
  case (insert \<chi> \<Phi>)
  assume "\<forall>\<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi> \<Longrightarrow> \<exists>\<Psi>. set \<Psi> \<subseteq> \<Delta> \<and> (\<forall>\<phi> \<in> \<Phi>. \<Psi> :\<turnstile> \<phi>)"
     and "\<forall>\<phi> \<in> insert \<chi> \<Phi>. \<Delta> \<tturnstile> \<phi>"
  hence "\<exists>\<Psi>. set \<Psi> \<subseteq> \<Delta> \<and> (\<forall>\<phi>\<in>\<Phi>. \<Psi> :\<turnstile> \<phi>)" and "\<Delta> \<tturnstile> \<chi>" by simp+
  then obtain \<Psi>\<^sub>1 \<Psi>\<^sub>2 where
    "set (\<Psi>\<^sub>1 @ \<Psi>\<^sub>2) \<subseteq> \<Delta>"
    "\<forall>\<phi> \<in> \<Phi>. \<Psi>\<^sub>1 :\<turnstile> \<phi>"
    "\<Psi>\<^sub>2 :\<turnstile> \<chi>"
    using set_deduction_def by auto
  moreover from this have "\<forall>\<phi> \<in> (insert \<chi> \<Phi>). \<Psi>\<^sub>1 @ \<Psi>\<^sub>2 :\<turnstile> \<phi>"
    by (metis
            insert_iff
            le_sup_iff
            list_deduction_monotonic
            order_refl set_append)
  ultimately show ?case by blast
qed

text \<open> With @{thm finite_set_deduction_list_deduction [no_vars]} the strengthened
       form of the cut rule can be given. \<close>

theorem (in implication_logic) strong_set_deduction_cut_rule:
  assumes "\<Phi> \<union> \<Gamma> \<tturnstile> \<psi>"
  and "\<forall> \<phi> \<in> \<Phi>. \<Delta> \<tturnstile> \<phi>"
  shows "\<Gamma> \<union> \<Delta> \<tturnstile> \<psi>"
proof -
  obtain \<Sigma> where
    A: "set \<Sigma>  \<subseteq> \<Phi> \<union> \<Gamma>" and
    B: "\<Sigma> :\<turnstile> \<psi>"
    using assms(1) set_deduction_def
    by auto+
  obtain \<Phi>' \<Gamma>' where
    C: "set \<Phi>' = set \<Sigma> \<inter> \<Phi>" and
    D: "set \<Gamma>' = set \<Sigma> \<inter> \<Gamma>"
    by (metis inf_sup_aci(1) inter_set_filter)+
  then have "set (\<Phi>' @ \<Gamma>') = set \<Sigma>" using A by auto
  hence E: "\<Phi>' @ \<Gamma>' :\<turnstile> \<psi>" using B list_deduction_monotonic by blast
  hence "\<forall> \<phi> \<in> set \<Phi>'. \<Delta> \<tturnstile> \<phi>" using assms(2) C by auto
  from this obtain \<Delta>' where "set \<Delta>' \<subseteq> \<Delta>" and "\<forall> \<phi> \<in> set \<Phi>'. \<Delta>' :\<turnstile> \<phi>"
    using finite_set_deduction_list_deduction by blast
  with strong_list_deduction_cut_rule D E
  have "set (\<Gamma>' @ \<Delta>') \<subseteq> \<Gamma> \<union> \<Delta>" and "\<Gamma>' @ \<Delta>' :\<turnstile> \<psi>" by auto
  thus ?thesis using set_deduction_def by blast
qed

section \<open>Maximally Consistent Sets For Implication Logic \label{sec:implicational-maximally-consistent-sets}\<close>

text \<open> \<^emph>\<open>Maximally Consistent Sets\<close> are a common construction for proving
       completeness of logical calculi.  For a classic presentation, see
       Dirk van Dalen's \<^emph>\<open>Logic and Structure\<close> (2013, \S1.5, pgs. 42--45)
       @{cite vandalenLogicStructure2013}. \<close>

text \<open> Maximally consistent sets will form the foundation of all of the
       model theory we will employ in this text. In fact, apart from
       classical logic semantics, conventional model theory will not be
       used at all. \<close>

text \<open> The models we are centrally concerned are derived from maximally
       consistent sets. These include probability measures used in completeness
       theorems of probability logic found in \S\ref{sec:probability-logic-completeness},
       as well as arbitrage protection and trading strategies stipulated by
       our formulation of the \<^emph>\<open>Dutch Book Theorem\<close> we present in
       \S\ref{chap:dutch-book-theorem}. \<close>

text \<open> Since implication logic does not have \<^emph>\<open>falsum\<close>, consistency is
       defined relative to a formula \<^term>\<open>\<phi>\<close>. \<close>

definition (in implication_logic)
  formula_consistent :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_-consistent _" [100] 100)
  where
    [simp]: "\<phi>-consistent \<Gamma> \<equiv> \<not> (\<Gamma> \<tturnstile> \<phi>)"

text \<open> Since consistency is defined relative to some \<^term>\<open>\<phi>\<close>,
       \<^emph>\<open>maximal consistency\<close> is presented as asserting that either
       \<^term>\<open>\<psi>\<close> or \<^term>\<open>\<psi> \<rightarrow> \<phi>\<close> is in the consistent set \<^term>\<open>\<Gamma>\<close>,
       for all \<^term>\<open>\<psi>\<close>.  This coincides with the traditional definition in
       classical logic when \<^term>\<open>\<phi>\<close> is \<^emph>\<open>falsum\<close>. \<close>

definition (in implication_logic)
  formula_maximally_consistent_set_def :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_-MCS _" [100] 100)
  where
    [simp]: "\<phi>-MCS \<Gamma> \<equiv> (\<phi>-consistent \<Gamma>) \<and> (\<forall> \<psi>. \<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>)"

text \<open> Every consistent set \<^term>\<open>\<Gamma>\<close> may be extended to a maximally
       consistent set. \<close>

text \<open> However, no assumption is made regarding the cardinality of the types
       of an instance of @{class implication_logic}. \<close>

text \<open> As a result, typical proofs that assume a countable domain are not
       suitable.  Our proof leverages \<^emph>\<open>Zorn's lemma\<close>. \<close>

lemma (in implication_logic) formula_consistent_extension:
  assumes "\<phi>-consistent \<Gamma>"
  shows "(\<phi>-consistent (insert \<psi> \<Gamma>)) \<or> (\<phi>-consistent (insert (\<psi> \<rightarrow> \<phi>) \<Gamma>))"
proof -
  {
    assume "\<not> \<phi>-consistent insert \<psi> \<Gamma>"
    hence "\<Gamma> \<tturnstile> \<psi> \<rightarrow> \<phi>"
      using set_deduction_theorem
      unfolding formula_consistent_def
      by simp
    hence "\<phi>-consistent insert (\<psi> \<rightarrow> \<phi>) \<Gamma>"
     by (metis Un_absorb assms formula_consistent_def set_deduction_cut_rule)
  }
  thus ?thesis by blast
qed

theorem (in implication_logic) formula_maximally_consistent_extension:
  assumes "\<phi>-consistent \<Gamma>"
  shows "\<exists> \<Omega>. (\<phi>-MCS \<Omega>) \<and> \<Gamma> \<subseteq> \<Omega>"
proof -
  let ?\<Gamma>_extensions = "{\<Sigma>. (\<phi>-consistent \<Sigma>) \<and> \<Gamma> \<subseteq> \<Sigma>}"
  have "\<exists> \<Omega> \<in> ?\<Gamma>_extensions. \<forall>\<Sigma> \<in> ?\<Gamma>_extensions. \<Omega> \<subseteq> \<Sigma> \<longrightarrow> \<Sigma> = \<Omega>"
  proof (rule subset_Zorn)
    fix \<C> :: "'a set set"
    assume subset_chain_\<C>: "subset.chain ?\<Gamma>_extensions \<C>"
    hence \<C>:  "\<forall> \<Sigma> \<in> \<C>. \<Gamma> \<subseteq> \<Sigma>" "\<forall> \<Sigma> \<in> \<C>. \<phi>-consistent \<Sigma>"
      unfolding subset.chain_def
      by blast+
    show "\<exists> \<Omega> \<in> ?\<Gamma>_extensions. \<forall> \<Sigma> \<in> \<C>. \<Sigma> \<subseteq> \<Omega>"
    proof cases
      assume "\<C> = {}" thus ?thesis using assms by blast
    next
      let ?\<Omega> = "\<Union> \<C>"
      assume "\<C> \<noteq> {}"
      hence "\<Gamma> \<subseteq> ?\<Omega>" by (simp add: \<C>(1) less_eq_Sup)
      moreover have "\<phi>-consistent ?\<Omega>"
      proof -
        {
          assume "\<not> \<phi>-consistent ?\<Omega>"
          then obtain \<omega> where \<omega>:
            "finite \<omega>"
            "\<omega> \<subseteq> ?\<Omega>"
            "\<not> \<phi>-consistent \<omega>"
            unfolding
              formula_consistent_def
              set_deduction_def
            by auto
          from \<omega>(1) \<omega>(2) have "\<exists> \<Sigma> \<in> \<C>. \<omega> \<subseteq> \<Sigma>"
          proof (induct \<omega> rule: finite_induct)
            case empty thus ?case using \<open>\<C> \<noteq> {}\<close> by blast
          next
            case (insert \<psi> \<omega>)
            from this obtain \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 where
              \<Sigma>\<^sub>1:
                  "\<omega> \<subseteq> \<Sigma>\<^sub>1"
                  "\<Sigma>\<^sub>1 \<in> \<C>"
              and \<Sigma>\<^sub>2:
                  "\<psi> \<in> \<Sigma>\<^sub>2"
                  "\<Sigma>\<^sub>2 \<in> \<C>"
              by auto
            hence "\<Sigma>\<^sub>1 \<subseteq> \<Sigma>\<^sub>2 \<or> \<Sigma>\<^sub>2 \<subseteq> \<Sigma>\<^sub>1"
              using subset_chain_\<C>
              unfolding subset.chain_def
              by blast
            hence "(insert \<psi> \<omega>) \<subseteq> \<Sigma>\<^sub>1 \<or> (insert \<psi> \<omega>) \<subseteq> \<Sigma>\<^sub>2"
              using \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 by blast
            thus ?case using \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 by blast
          qed
          hence "\<exists> \<Sigma> \<in> \<C>. (\<phi>-consistent \<Sigma>) \<and> \<not> (\<phi>-consistent \<Sigma>)"
            using \<C>(2) \<omega>(3)
            unfolding
              formula_consistent_def
              set_deduction_def
            by auto
          hence "False" by auto
        }
        thus ?thesis by blast
      qed
      ultimately show ?thesis by blast
    qed
  qed
  then obtain \<Omega> where \<Omega>:
    "\<Omega> \<in> ?\<Gamma>_extensions"
    "\<forall>\<Sigma> \<in> ?\<Gamma>_extensions. \<Omega> \<subseteq> \<Sigma> \<longrightarrow> \<Sigma> = \<Omega>"
    by auto+
  {
    fix \<psi>
    have "(\<phi>-consistent insert \<psi> \<Omega>) \<or> (\<phi>-consistent insert (\<psi> \<rightarrow> \<phi>) \<Omega>)"
         "\<Gamma> \<subseteq> insert \<psi> \<Omega>"
         "\<Gamma> \<subseteq> insert (\<psi> \<rightarrow> \<phi>) \<Omega>"
      using \<Omega>(1) formula_consistent_extension formula_consistent_def
      by auto
    hence "insert \<psi> \<Omega> \<in> ?\<Gamma>_extensions
             \<or> insert (\<psi> \<rightarrow> \<phi>) \<Omega> \<in> ?\<Gamma>_extensions"
      by blast
    hence "\<psi> \<in> \<Omega> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Omega>" using \<Omega>(2) by blast
  }
  thus ?thesis
    using \<Omega>(1)
    unfolding formula_maximally_consistent_set_def_def
    by blast
qed

text \<open> Finally, maximally consistent sets contain anything that can be deduced
       from them, and model a form of \<^emph>\<open>modus ponens\<close>. \<close>

lemma (in implication_logic) formula_maximally_consistent_set_def_reflection:
  "\<phi>-MCS \<Gamma> \<Longrightarrow> \<psi> \<in> \<Gamma> = \<Gamma> \<tturnstile> \<psi>"
proof -
  assume "\<phi>-MCS \<Gamma>"
  {
    assume "\<Gamma> \<tturnstile> \<psi>"
    moreover from \<open>\<phi>-MCS \<Gamma>\<close> have "\<psi> \<in> \<Gamma> \<or> (\<psi> \<rightarrow> \<phi>) \<in> \<Gamma>" "\<not> \<Gamma> \<tturnstile> \<phi>"
      unfolding
        formula_maximally_consistent_set_def_def
        formula_consistent_def
      by auto
    ultimately have "\<psi> \<in> \<Gamma>"
      using set_deduction_reflection set_deduction_modus_ponens
      by metis
  }
  thus "\<psi> \<in> \<Gamma> = \<Gamma> \<tturnstile> \<psi>"
    using set_deduction_reflection
    by metis
qed

theorem (in implication_logic) formula_maximally_consistent_set_def_implication_elimination:
  assumes "\<phi>-MCS \<Omega>"
  shows "(\<psi> \<rightarrow> \<chi>) \<in> \<Omega> \<Longrightarrow> \<psi> \<in> \<Omega> \<Longrightarrow> \<chi> \<in> \<Omega>"
  using
    assms
    formula_maximally_consistent_set_def_reflection
    set_deduction_modus_ponens
  by blast

text \<open> This concludes our introduction to implication logic. \<close>

end
