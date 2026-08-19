(* Kirstin Peters, TU Berlin, 2015 *)

theory ProcessCalculi
  imports Relations
begin

section \<open>Process Calculi\<close>

text \<open>A process calculus is given by a set of process terms (syntax) and a relation on terms
      (semantics). We consider reduction as well as labelled variants of the semantics.\<close>

subsection \<open>Reduction Semantics\<close>

text \<open>A set of process terms and a relation on pairs of terms (called reduction semantics) define
      a process calculus.\<close>

record 'proc processCalculus =
  Reductions :: "'proc \<Rightarrow> 'proc \<Rightarrow> bool"

text \<open>A pair of the reduction relation is called a (reduction) step.\<close>

abbreviation step :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<longmapsto>_ _\<close> [70, 70, 70] 80) where
  "P \<longmapsto>Cal Q \<equiv> Reductions Cal P Q"

text \<open>We use * to indicate the reflexive and transitive closure of the reduction relation.\<close>

primrec nSteps :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> nat \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<longmapsto>_\<^bsup>_\<^esup> _\<close> [70, 70, 70, 70] 80) where
  "P \<longmapsto>Cal\<^bsup>0\<^esup> Q     = (P = Q)"
| "P \<longmapsto>Cal\<^bsup>Suc n\<^esup> Q = (\<exists>P'. P \<longmapsto>Cal\<^bsup>n\<^esup> P' \<and> P' \<longmapsto>Cal Q)"

definition steps :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<longmapsto>_* _\<close> [70, 70, 70] 80) where
  "P \<longmapsto>Cal* Q \<equiv> \<exists>n. P \<longmapsto>Cal\<^bsup>n\<^esup> Q"

text \<open>A process is divergent, if it can perform an infinite sequence of steps.\<close>

definition divergent :: "'proc \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"  (\<open>_ \<longmapsto>_\<omega>\<close> [70, 70] 80) where
  "P \<longmapsto>(Cal)\<omega> \<equiv> \<forall>P'. P \<longmapsto>Cal* P' \<longrightarrow> (\<exists>P''. P' \<longmapsto>Cal P'')"

text \<open>Each term can perform an (empty) sequence of steps to itself.\<close>

lemma steps_refl:
  fixes Cal :: "'proc processCalculus"
    and P   :: "'proc"
  shows "P \<longmapsto>Cal* P"
proof -
  have "P \<longmapsto>Cal\<^bsup>0\<^esup> P"
    by simp
  hence "\<exists>n. P \<longmapsto>Cal\<^bsup>n\<^esup> P"
    by blast
  thus "P \<longmapsto>Cal* P"
    by (simp add: steps_def)
qed

text \<open>A single step is a sequence of steps of length one.\<close>

lemma step_to_steps:
  fixes Cal  :: "'proc processCalculus"
    and P P' :: "'proc"
  assumes step: "P \<longmapsto>Cal P'"
  shows "P \<longmapsto>Cal* P'"
proof -
  from step have "P \<longmapsto>Cal\<^bsup>1\<^esup> P'"
    by simp
  thus ?thesis
    unfolding steps_def
    by blast
qed

text \<open>If there is a sequence of steps from P to Q and from Q to R, then there is also a sequence
      of steps from P to R.\<close>

lemma nSteps_add:
  fixes Cal   :: "'proc processCalculus"
    and n1 n2 :: "nat"
  shows "\<forall>P Q R. P \<longmapsto>Cal\<^bsup>n1\<^esup> Q \<and> Q \<longmapsto>Cal\<^bsup>n2\<^esup> R \<longrightarrow> P \<longmapsto>Cal\<^bsup>(n1 + n2)\<^esup> R"
proof (induct n2, simp)
  case (Suc n)
  assume IH: "\<forall>P Q R. P \<longmapsto>Cal\<^bsup>n1\<^esup> Q \<and> Q \<longmapsto>Cal\<^bsup>n\<^esup> R \<longrightarrow> P \<longmapsto>Cal\<^bsup>(n1 + n)\<^esup> R"
  show ?case
  proof clarify
    fix P Q R
    assume "Q \<longmapsto>Cal\<^bsup>Suc n\<^esup> R"
    from this obtain Q' where A1: "Q \<longmapsto>Cal\<^bsup>n\<^esup> Q'" and A2: "Q' \<longmapsto>Cal R"
      by auto
    assume "P \<longmapsto>Cal\<^bsup>n1\<^esup> Q"
    with A1 IH have "P \<longmapsto>Cal\<^bsup>(n1 + n)\<^esup> Q'"
      by blast
    with A2 show "P \<longmapsto>Cal\<^bsup>(n1 + Suc n)\<^esup> R"
      by auto
  qed
qed

lemma steps_add:
  fixes Cal   :: "'proc processCalculus"
    and P Q R :: "'proc"
  assumes A1: "P \<longmapsto>Cal* Q"
      and A2: "Q \<longmapsto>Cal* R"
  shows "P \<longmapsto>Cal* R"
proof -
  from A1 obtain n1 where "P \<longmapsto>Cal\<^bsup>n1\<^esup> Q"
    by (auto simp add: steps_def)
  moreover from A2 obtain n2 where "Q \<longmapsto>Cal\<^bsup>n2\<^esup> R"
    by (auto simp add: steps_def)
  ultimately have "P \<longmapsto>Cal\<^bsup>(n1 + n2)\<^esup> R"
    using nSteps_add[where Cal="Cal"]
    by blast
  thus "P \<longmapsto>Cal* R"
    by (simp add: steps_def, blast)
qed

subsubsection \<open>Observables or Barbs\<close>

text \<open>We assume a predicate that tests terms for some kind of observables. At this point we do not
      limit or restrict the kind of observables used for a calculus nor the method to check them.\<close>

record ('proc, 'barbs) calculusWithBarbs =
  Calculus :: "'proc processCalculus"
  HasBarb  :: "'proc \<Rightarrow> 'barbs \<Rightarrow> bool" (\<open>_\<down>_\<close> [70, 70] 80)

abbreviation hasBarb :: "'proc \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs \<Rightarrow> bool"
  (\<open>_\<down><_>_\<close> [70, 70, 70] 80) where
  "P\<down><CWB>a \<equiv> HasBarb CWB P a"

text \<open>A term reaches a barb if it can evolve to a term that has this barb.\<close>

abbreviation reachesBarb :: "'proc \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs \<Rightarrow> bool"
  (\<open>_\<Down><_>_\<close> [70, 70, 70] 80) where
  "P\<Down><CWB>a \<equiv> \<exists>P'. P \<longmapsto>(Calculus CWB)* P' \<and> P'\<down><CWB>a"

text \<open>A relation R preserves barbs if whenever (P, Q) in R and P has a barb then also Q has this
      barb.\<close>

abbreviation rel_preserves_barb_set
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool" where
  "rel_preserves_barb_set Rel CWB Barbs \<equiv>
   rel_preserves_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<down><CWB>a)"

abbreviation rel_preserves_barbs
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "rel_preserves_barbs Rel CWB \<equiv> rel_preserves_binary_pred Rel (HasBarb CWB)"

lemma preservation_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_preserves_barbs Rel CWB = (\<forall>Barbs. rel_preserves_barb_set Rel CWB Barbs)"
  by blast

text \<open>A relation R reflects barbs if whenever (P, Q) in R and Q has a barb then also P has this
      barb.\<close>

abbreviation rel_reflects_barb_set
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool" where
  "rel_reflects_barb_set Rel CWB Barbs \<equiv>
   rel_reflects_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<down><CWB>a)"

abbreviation rel_reflects_barbs
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "rel_reflects_barbs Rel CWB \<equiv> rel_reflects_binary_pred Rel (HasBarb CWB)"

lemma reflection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_reflects_barbs Rel CWB = (\<forall>Barbs. rel_reflects_barb_set Rel CWB Barbs)"
  by blast

text \<open>A relation respects barbs if it preserves and reflects barbs.\<close>

abbreviation rel_respects_barb_set
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool" where
  "rel_respects_barb_set Rel CWB Barbs \<equiv>
   rel_preserves_barb_set Rel CWB Barbs \<and> rel_reflects_barb_set Rel CWB Barbs"

abbreviation rel_respects_barbs
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "rel_respects_barbs Rel CWB \<equiv> rel_preserves_barbs Rel CWB \<and> rel_reflects_barbs Rel CWB"

lemma respection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_respects_barbs Rel CWB = (\<forall>Barbs. rel_respects_barb_set Rel CWB Barbs)"
  by blast

text \<open>If a relation preserves barbs then so does its reflexive or/and transitive closure.\<close>

lemma preservation_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes preservation: "rel_preserves_barbs Rel CWB"
  shows "rel_preserves_barbs (Rel\<^sup>=) CWB"
    and "rel_preserves_barbs (Rel\<^sup>+) CWB"
    and "rel_preserves_barbs (Rel\<^sup>*) CWB"
  using preservation
        preservation_of_binary_predicates_and_closures[where Rel="Rel" and Pred="HasBarb CWB"]
  by blast+

text \<open>If a relation reflects barbs then so does its reflexive or/and transitive closure.\<close>

lemma reflection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes reflection: "rel_reflects_barbs Rel CWB"
  shows "rel_reflects_barbs (Rel\<^sup>=) CWB"
    and "rel_reflects_barbs (Rel\<^sup>+) CWB"
    and "rel_reflects_barbs (Rel\<^sup>*) CWB"
  using reflection
        reflection_of_binary_predicates_and_closures[where Rel="Rel" and Pred="HasBarb CWB"]
  by blast+

text \<open>If a relation respects barbs then so does its reflexive, symmetric, or/and transitive
      closure.\<close>

lemma respection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes respection: "rel_respects_barbs Rel CWB"
  shows "rel_respects_barbs (Rel\<^sup>=) CWB"
    and "rel_respects_barbs (symcl Rel) CWB"
    and "rel_respects_barbs (Rel\<^sup>+) CWB"
    and "rel_respects_barbs (symcl (Rel\<^sup>=)) CWB"
    and "rel_respects_barbs (Rel\<^sup>*) CWB"
    and "rel_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
proof -
  from respection show "rel_respects_barbs (Rel\<^sup>=) CWB"
    using respection_of_binary_predicates_and_closures(1)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (symcl Rel) CWB"
    using respection_of_binary_predicates_and_closures(2)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (Rel\<^sup>+) CWB"
    using respection_of_binary_predicates_and_closures(3)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (symcl (Rel\<^sup>=)) CWB"
    using respection_of_binary_predicates_and_closures(4)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs (Rel\<^sup>*) CWB"
    using respection_of_binary_predicates_and_closures(5)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
next
  from respection show "rel_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
    using respection_of_binary_predicates_and_closures(6)[where Rel="Rel" and Pred="HasBarb CWB"]
    by blast
qed

text \<open>A relation R weakly preserves barbs if it preserves reachability of barbs, i.e., if (P, Q)
      in R and P reaches a barb then also Q has to reach this barb.\<close>

abbreviation rel_weakly_preserves_barb_set
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool" where
  "rel_weakly_preserves_barb_set Rel CWB Barbs \<equiv>
   rel_preserves_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<Down><CWB>a)"

abbreviation rel_weakly_preserves_barbs
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "rel_weakly_preserves_barbs Rel CWB \<equiv> rel_preserves_binary_pred Rel (\<lambda>P a. P\<Down><CWB>a)"

lemma weak_preservation_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_weakly_preserves_barbs Rel CWB =
         (\<forall>Barbs. rel_weakly_preserves_barb_set Rel CWB Barbs)"
  by blast

text \<open>A relation R weakly reflects barbs if it reflects reachability of barbs, i.e., if (P, Q) in
      R and Q reaches a barb then also P has to reach this barb.\<close>

abbreviation rel_weakly_reflects_barb_set
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool" where
  "rel_weakly_reflects_barb_set Rel CWB Barbs \<equiv>
   rel_reflects_binary_pred Rel (\<lambda>P a. a \<in> Barbs \<and> P\<Down><CWB>a)"

abbreviation rel_weakly_reflects_barbs
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "rel_weakly_reflects_barbs Rel CWB \<equiv> rel_reflects_binary_pred Rel (\<lambda>P a. P\<Down><CWB>a)"

lemma weak_reflection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_weakly_reflects_barbs Rel CWB = (\<forall>Barbs. rel_weakly_reflects_barb_set Rel CWB Barbs)"
  by blast

text \<open>A relation weakly respects barbs if it weakly preserves and weakly reflects barbs.\<close>

abbreviation rel_weakly_respects_barb_set
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> 'barbs set \<Rightarrow> bool" where
  "rel_weakly_respects_barb_set Rel CWB Barbs \<equiv>
   rel_weakly_preserves_barb_set Rel CWB Barbs \<and> rel_weakly_reflects_barb_set Rel CWB Barbs"

abbreviation rel_weakly_respects_barbs
  :: "('proc \<times> 'proc) set \<Rightarrow> ('proc, 'barbs) calculusWithBarbs \<Rightarrow> bool" where
  "rel_weakly_respects_barbs Rel CWB \<equiv>
   rel_weakly_preserves_barbs Rel CWB \<and> rel_weakly_reflects_barbs Rel CWB"

lemma weak_respection_of_barbs_and_set_of_barbs:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  shows "rel_weakly_respects_barbs Rel CWB = (\<forall>Barbs. rel_weakly_respects_barb_set Rel CWB Barbs)"
  by blast

text \<open>If a relation weakly preserves barbs then so does its reflexive or/and transitive closure.\<close>

lemma weak_preservation_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes preservation: "rel_weakly_preserves_barbs Rel CWB"
  shows "rel_weakly_preserves_barbs (Rel\<^sup>=) CWB"
    and "rel_weakly_preserves_barbs (Rel\<^sup>+) CWB"
    and "rel_weakly_preserves_barbs (Rel\<^sup>*) CWB"
  using preservation preservation_of_binary_predicates_and_closures[where Rel="Rel"
        and Pred="\<lambda>P a. P\<Down><CWB>a"]
  by blast+

text \<open>If a relation weakly reflects barbs then so does its reflexive or/and transitive closure.\<close>

lemma weak_reflection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes reflection: "rel_weakly_reflects_barbs Rel CWB"
  shows "rel_weakly_reflects_barbs (Rel\<^sup>=) CWB"
    and "rel_weakly_reflects_barbs (Rel\<^sup>+) CWB"
    and "rel_weakly_reflects_barbs (Rel\<^sup>*) CWB"
  using reflection reflection_of_binary_predicates_and_closures[where Rel="Rel"
        and Pred="\<lambda>P a. P\<Down><CWB>a"]
  by blast+

text \<open>If a relation weakly respects barbs then so does its reflexive, symmetric, or/and
      transitive closure.\<close>

lemma weak_respection_of_barbs_and_closures:
  fixes Rel :: "('proc \<times> 'proc) set"
    and CWB :: "('proc, 'barbs) calculusWithBarbs"
  assumes respection: "rel_weakly_respects_barbs Rel CWB"
  shows "rel_weakly_respects_barbs (Rel\<^sup>=) CWB"
    and "rel_weakly_respects_barbs (symcl Rel) CWB"
    and "rel_weakly_respects_barbs (Rel\<^sup>+) CWB"
    and "rel_weakly_respects_barbs (symcl (Rel\<^sup>=)) CWB"
    and "rel_weakly_respects_barbs (Rel\<^sup>*) CWB"
    and "rel_weakly_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
proof -
  from respection show "rel_weakly_respects_barbs (Rel\<^sup>=) CWB"
    using respection_of_binary_predicates_and_closures(1)[where Rel="Rel"
          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (symcl Rel) CWB"
    using respection_of_binary_predicates_and_closures(2)[where Rel="Rel"
          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (Rel\<^sup>+) CWB"
    using respection_of_binary_predicates_and_closures(3)[where Rel="Rel"
          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (symcl (Rel\<^sup>=)) CWB"
    using respection_of_binary_predicates_and_closures(4)[where Rel="Rel"
          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs (Rel\<^sup>*) CWB"
    using respection_of_binary_predicates_and_closures(5)[where Rel="Rel"
          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
next
  from respection show "rel_weakly_respects_barbs ((symcl (Rel\<^sup>=))\<^sup>+) CWB"
    using respection_of_binary_predicates_and_closures(6)[where Rel="Rel"
          and Pred="\<lambda>P a. P\<Down><CWB>a"]
    by blast
qed

(* Kirstin Peters, University of Augsburg, 2026 *)

subsection \<open>Labelled Semantics\<close>

text \<open>Alternatively, a process calculus is defined by a set of process terms and a relation on a
      term, a label, and a term (called labelled semantics). Moreover, we assume that in this case
      there exists a special label to denote an internal action.\<close>

record ('proc, 'lab) labelledProcessCalculus =
  LabelledSemantics :: "'proc \<Rightarrow> 'lab \<Rightarrow> 'proc \<Rightarrow> bool"
  InternalAction    :: "'lab"

text \<open>A triple of the labelled semantics is called a labelled step. To avoid confusion we disable
      some syntactic sugar for Limes in Topological Spaces.\<close>

no_notation Topological_Spaces.LIM (\<open>(\<open>notation=\<open>infix LIM\<close>\<close>(_)/ \<midarrow>(_)/\<rightarrow> (_))\<close> [60, 0, 60] 60)

abbreviation labelledStep
  :: "'proc \<Rightarrow> 'lab \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>_\<rightarrow>_ _\<close> [70, 70, 70, 70] 80) where
  "P \<midarrow>\<alpha>\<rightarrow>Cal Q \<equiv> LabelledSemantics Cal P \<alpha> Q"

text \<open>The internal action is denoted by tau, where we add the respective calculus, since different
      calculi may have a different internal action label.\<close>

abbreviation internal :: "('proc, 'lab) labelledProcessCalculus \<Rightarrow> 'lab"  (\<open>\<tau>-_\<close> [70] 90) where
  "\<tau>-Cal \<equiv> InternalAction Cal"

text \<open>A weak internal step is the reflexive and transitive closure of a labelled step on the
      internal action label.\<close>

inductive weakTauStep :: "'proc \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<rightarrow>_* _\<close> [70, 70, 70] 80) where
  WTS_refl:  "P \<rightarrow>Cal* P"
| WTS_trans: "\<lbrakk>P \<rightarrow>Cal* Q; Q \<midarrow>\<tau>-Cal\<rightarrow>Cal R\<rbrakk> \<Longrightarrow> P \<rightarrow>Cal* R"

lemma weakTauStep_decompose:
  fixes P Q :: "'proc"
    and Cal :: "('proc, 'lab) labelledProcessCalculus"
  assumes "P \<rightarrow>Cal* Q"
  shows "P = Q \<or> (\<exists>R. P \<rightarrow>Cal* R \<and> R \<midarrow>\<tau>-Cal\<rightarrow>Cal Q)"
  using assms
  by (induct, auto)

lemma weakTauSteps_trans:
  fixes P Q R :: "'proc"
    and Cal   :: "('proc, 'lab) labelledProcessCalculus"
  assumes "P \<rightarrow>Cal* Q"
      and "Q \<rightarrow>Cal* R"
    shows "P \<rightarrow>Cal* R"
  using assms(2) assms(1)
proof induct
  case (WTS_refl Q Cal)
  assume "P \<rightarrow>Cal* Q"
  thus "P \<rightarrow>Cal* Q" .
next
  case (WTS_trans Q Cal S R)
  assume "P \<rightarrow>Cal* Q \<Longrightarrow> P \<rightarrow>Cal* S" and "P \<rightarrow>Cal* Q"
  hence "P \<rightarrow>Cal* S"
    by simp
  moreover assume "S \<midarrow>\<tau>-Cal\<rightarrow>Cal R"
  ultimately show "P \<rightarrow>Cal* R"
    using weakTauStep.WTS_trans[of P Cal S R]
    by simp
qed

text \<open>A weak labelled step is a labelled step surrounded by an arbitrary number of steps on the
      internal action.\<close>

definition weakLabelledActionStep
  :: "'proc \<Rightarrow> 'lab \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>_\<rightarrow>_* _\<close> [70, 70, 70, 70] 80) where
  "P \<midarrow>\<alpha>\<rightarrow>Cal* Q \<equiv> \<alpha> \<noteq> \<tau>-Cal \<and> (\<exists>R S. P \<rightarrow>Cal* R \<and> R \<midarrow>\<alpha>\<rightarrow>Cal S \<and> S \<rightarrow>Cal* Q)"

definition weakLabelledStep
  :: "'proc \<Rightarrow> 'lab \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>\<Zcat>_\<rightarrow>_* _\<close> [70, 70, 70, 70] 80) where
  "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* Q \<equiv> if \<alpha> = \<tau>-Cal then P \<rightarrow>Cal* Q else P \<midarrow>\<alpha>\<rightarrow>Cal* Q"

text \<open>A weak labelled step can be extended by any number of internal steps.\<close>

lemma weakLabelledActionStep_extend_by_internal:
  fixes P P' P'' :: "'proc"
    and \<alpha>        :: "'lab"
    and Cal      :: "('proc, 'lab) labelledProcessCalculus"
  assumes action:   "P \<midarrow>\<alpha>\<rightarrow>Cal* P'"
      and internal: "P' \<rightarrow>Cal* P''"
    shows "P \<midarrow>\<alpha>\<rightarrow>Cal* P''"
proof -
  from action obtain R S where A1: "\<alpha> \<noteq> \<tau>-Cal" and A2: "P \<rightarrow>Cal* R" and A3: "R \<midarrow>\<alpha>\<rightarrow>Cal S"
                           and A4: "S \<rightarrow>Cal* P'"
    unfolding weakLabelledActionStep_def
    by blast
  from internal A4 have "S \<rightarrow>Cal* P''"
    using weakTauSteps_trans[of S Cal P' P'']
    by simp
  with A1 A2 A3 show "P \<midarrow>\<alpha>\<rightarrow>Cal* P''"
    unfolding weakLabelledActionStep_def
    by blast
qed

lemma weakLabelledActionStep_preceeded_by_internal:
  fixes P P' P'' :: "'proc"
    and \<alpha>        :: "'lab"
    and Cal      :: "('proc, 'lab) labelledProcessCalculus"
  assumes internal: "P \<rightarrow>Cal* P'"
      and action:   "P' \<midarrow>\<alpha>\<rightarrow>Cal* P''"
    shows "P \<midarrow>\<alpha>\<rightarrow>Cal* P''"
proof -
  from action obtain R S where A1: "\<alpha> \<noteq> \<tau>-Cal" and A2: "P' \<rightarrow>Cal* R" and A3: "R \<midarrow>\<alpha>\<rightarrow>Cal S"
                           and A4: "S \<rightarrow>Cal* P''"
    unfolding weakLabelledActionStep_def
    by blast
  from internal A2 have "P \<rightarrow>Cal* R"
    using weakTauSteps_trans[of P Cal P' R]
    by simp
  with A1 A3 A4 show "P \<midarrow>\<alpha>\<rightarrow>Cal* P''"
    unfolding weakLabelledActionStep_def
    by blast
qed

lemma weakLabelledStep_extend_by_internal:
  fixes P P' P'' :: "'proc"
    and \<alpha>        :: "'lab"
    and Cal      :: "('proc, 'lab) labelledProcessCalculus"
  assumes action:   "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
      and internal: "P' \<rightarrow>Cal* P''"
    shows "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
  unfolding weakLabelledStep_def
proof auto
  assume "\<alpha> = \<tau>-Cal"
  with action have "P \<rightarrow>Cal* P'"
    unfolding weakLabelledStep_def
    by simp
  with internal show "P \<rightarrow>Cal* P''"
    using weakTauSteps_trans[of P Cal P' P'']
    by simp
next
  assume "\<alpha> \<noteq> \<tau>-Cal"
  with action have "P \<midarrow>\<alpha>\<rightarrow>Cal* P'"
    unfolding weakLabelledStep_def
    by simp
  with internal show "P \<midarrow>\<alpha>\<rightarrow>Cal* P''"
    using weakLabelledActionStep_extend_by_internal[of P \<alpha> Cal P' P'']
    by simp
qed

lemma weakLabelledStep_preceeded_by_internal:
  fixes P P' P'' :: "'proc"
    and \<alpha>        :: "'lab"
    and Cal      :: "('proc, 'lab) labelledProcessCalculus"
  assumes internal: "P \<rightarrow>Cal* P'"
      and action:   "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    shows "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
  unfolding weakLabelledStep_def
proof auto
  assume "\<alpha> = \<tau>-Cal"
  with action have "P' \<rightarrow>Cal* P''"
    unfolding weakLabelledStep_def
    by simp
  with internal show "P \<rightarrow>Cal* P''"
    using weakTauSteps_trans[of P Cal P' P'']
    by simp
next
  assume "\<alpha> \<noteq> \<tau>-Cal"
  with action have "P' \<midarrow>\<alpha>\<rightarrow>Cal* P''"
    unfolding weakLabelledStep_def
    by simp
  with internal show "P \<midarrow>\<alpha>\<rightarrow>Cal* P''"
    using weakLabelledActionStep_preceeded_by_internal[of P Cal P' \<alpha> P'']
    by simp
qed

text \<open>A sequence of weak labelled steps is called a weak labelled sequence. Note that for each
      internal action in the sequence an arbitrary number of internal steps can be performed even 0
      and similarly for each other label. Also note that we deliberately do not forbid internal
      labels in the considered word.\<close>

inductive weakLabelledSequence
  :: "'proc \<Rightarrow> 'lab list \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> 'proc \<Rightarrow> bool"
  (\<open>_ \<midarrow>\<frown>_\<rightarrow>_* _\<close> [70, 70, 70, 70] 80) where
  WLS_Nil:  "P \<rightarrow>Cal* P' \<Longrightarrow> P \<midarrow>\<frown>[]\<rightarrow>Cal* P'"
| WLS_Cons: "\<lbrakk>P \<midarrow>\<frown>w\<rightarrow>Cal* P'; P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''\<rbrakk> \<Longrightarrow> P \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* P''"

lemma internal_weakLabelledSequence:
  fixes P P' :: "'proc"
    and Cal  :: "('proc, 'lab) labelledProcessCalculus"
  assumes "P \<midarrow>\<frown>[]\<rightarrow>Cal* P'"
  shows "P \<rightarrow>Cal * P'"
proof -
  define w where def_w: "w = ([]::'lab list)"
  with assms have "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
    by simp
  from this def_w show "P \<rightarrow>Cal * P'"
    by (induct, simp_all)
qed

text \<open>A weak labelled sequence can be extended by any number of internal steps.\<close>

lemma weakLabelledSequence_extend_by_internal:
  fixes P P' P'' :: "'proc"
    and w        :: "'lab list"
    and Cal      :: "('proc, 'lab) labelledProcessCalculus"
  assumes word:     "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
      and internal: "P' \<rightarrow>Cal* P''"
    shows "P \<midarrow>\<frown>w\<rightarrow>Cal* P''"
  using assms
proof (induct arbitrary: P'')
  case (WLS_Nil P Cal P')
  assume "P \<rightarrow>Cal* P'" and "P' \<rightarrow>Cal* P''"
  hence "P \<rightarrow>Cal* P''"
    using weakTauSteps_trans[of P Cal P' P'']
    by simp
  thus "P \<midarrow>\<frown>[]\<rightarrow>Cal* P''"
    using weakLabelledSequence.WLS_Nil[of P Cal P'']
    by simp
next
  case (WLS_Cons P w Cal P' \<alpha> R)
  assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
  moreover assume "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* R" and "R \<rightarrow>Cal* P''"
  hence "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    using weakLabelledStep_extend_by_internal[of P' \<alpha> Cal R P'']
    by simp
  ultimately show "P \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* P''"
    using weakLabelledSequence.WLS_Cons[of P w Cal P' \<alpha> P'']
    by simp
qed

lemma weakLabelledSequence_preceeded_by_internal:
  fixes P P' P'' :: "'proc"
    and w        :: "'lab list"
    and Cal      :: "('proc, 'lab) labelledProcessCalculus"
  assumes internal: "P \<rightarrow>Cal* P'"
      and word:     "P' \<midarrow>\<frown>w\<rightarrow>Cal* P''"
    shows "P \<midarrow>\<frown>w\<rightarrow>Cal* P''"
  using word internal
proof (induct)
  case (WLS_Nil P' Cal P'')
  assume "P \<rightarrow>Cal* P'" and "P' \<rightarrow>Cal* P''"
  hence "P \<rightarrow>Cal* P''"
    using weakTauSteps_trans[of P Cal P' P'']
    by simp
  thus "P \<midarrow>\<frown>[]\<rightarrow>Cal* P''"
    using weakLabelledSequence.WLS_Nil[of P Cal P'']
    by simp
next
  case (WLS_Cons P' w Cal P'' \<alpha> P''')
  assume "P \<rightarrow>Cal* P' \<Longrightarrow> P \<midarrow>\<frown>w\<rightarrow>Cal* P''" and "P \<rightarrow>Cal* P'"
  hence "P \<midarrow>\<frown>w\<rightarrow>Cal* P''"
    by simp
  moreover assume "P'' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'''"
  ultimately show "P \<midarrow>\<frown>(w@[\<alpha>])\<rightarrow>Cal* P'''"
    using weakLabelledSequence.WLS_Cons[of P w Cal P'' \<alpha> P''']
    by simp
qed

lemma weakLabelledSequence_single:
  fixes P P' :: "'proc"
    and \<alpha>    :: "'lab"
    and Cal  :: "('proc, 'lab) labelledProcessCalculus"
  assumes step: "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
  shows "P \<midarrow>\<frown>[\<alpha>]\<rightarrow>Cal* P'"
proof -
  have "P \<rightarrow>Cal* P"
    using WTS_refl[of P Cal]
    by simp
  hence "P \<midarrow>\<frown>[]\<rightarrow>Cal* P"
    using WLS_Nil[of P Cal P]
    by simp
  with step show "P \<midarrow>\<frown>[\<alpha>]\<rightarrow>Cal* P'"
    using WLS_Cons[of P "[]" Cal P \<alpha> P']
    by simp
qed

lemma weakLabelledSequence_decompose:
  fixes P P' :: "'proc"
    and w    :: "'lab list"
    and Cal  :: "('proc, 'lab) labelledProcessCalculus"
  assumes step: "P \<midarrow>\<frown>w\<rightarrow>Cal* P'"
  shows "w = [] \<Longrightarrow> P \<rightarrow>Cal* P'"
    and "w \<noteq> [] \<Longrightarrow> \<exists>w' \<alpha> P''. w = w'@[\<alpha>] \<and> P \<midarrow>\<frown>w'\<rightarrow>Cal* P'' \<and> P'' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
  using step
proof induct
  case (WLS_Nil P Cal P')
  {
    assume "P \<rightarrow>Cal* P'"
    thus "P \<rightarrow>Cal* P'" .
  next
    assume "[] \<noteq> []"
    hence False
      by simp
    thus "\<exists>w' \<alpha> P''. [] = w'@[\<alpha>] \<and> P \<midarrow>\<frown>w'\<rightarrow>Cal* P'' \<and> P'' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
      by simp
  }
next
  case (WLS_Cons P w Cal P' \<alpha> P'')
  {
    assume "w@[\<alpha>] = []"
    hence False
      by simp
    thus "P \<rightarrow>Cal* P''"
      by simp
  next
    assume "P \<midarrow>\<frown>w\<rightarrow>Cal* P'" and "P' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P''"
    thus "\<exists>w' \<alpha>' P'''. w@[\<alpha>] = w'@[\<alpha>'] \<and> P \<midarrow>\<frown>w'\<rightarrow>Cal* P''' \<and> P''' \<midarrow>\<Zcat>\<alpha>'\<rightarrow>Cal* P''"
      by blast
  }
qed

lemma weakLabelledSequence_single_rev:
  fixes P P' :: "'proc"
    and \<alpha>    :: "'lab"
    and Cal  :: "('proc, 'lab) labelledProcessCalculus"
  assumes step: "P \<midarrow>\<frown>[\<alpha>]\<rightarrow>Cal* P'"
  shows "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
proof -
  from step obtain P'' where A1: "P \<midarrow>\<frown>[]\<rightarrow>Cal* P''" and A2: "P'' \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
    using weakLabelledSequence_decompose(2)[of P "[\<alpha>]" Cal P']
    by auto
  from A1 have "P \<rightarrow>Cal* P''"
    using weakLabelledSequence_decompose(1)[of P "[]" Cal P'']
    by simp
  with A2 show "P \<midarrow>\<Zcat>\<alpha>\<rightarrow>Cal* P'"
    using weakLabelledStep_preceeded_by_internal[of P Cal P'' \<alpha> P']
    by simp
qed

text \<open>A process is divergent, if it can perform an infinite sequence of internal steps.\<close>

definition divergentLS
  :: "'proc \<Rightarrow> ('proc, 'lab) labelledProcessCalculus \<Rightarrow> bool" (\<open>_ \<rightarrow>_\<omega>\<close> [70, 70] 80) where
  "P \<rightarrow>(Cal)\<omega> \<equiv> \<forall>P'. P \<rightarrow>Cal* P' \<longrightarrow> (\<exists>P''. P' \<midarrow>\<tau>-Cal\<rightarrow>Cal P'')"

end