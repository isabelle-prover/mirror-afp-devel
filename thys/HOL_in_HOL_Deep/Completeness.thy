theory Completeness
  imports Soundness "HOL-Library.Countable_Set"
begin

section \<open>Completeness\<close>

text \<open>Henkin completeness for \<open>NK\<close>, with the term model realised as a term evaluation
  (BKK Definition 3.35).  The result is then strengthened to arbitrary infinite value
  carriers, signatures with infinitely many parameters, and open formulas, and extended to
  derivation from hypotheses --- up to arbitrary parameter-rich contexts of open formulas
  at @{emph \<open>any\<close>} signature cardinality; the carrier need only be at least as large as
  the signature.  For the hypothesis relation \<open>\<tturnstile>\<close> of \<open>Calculus\<close> even the
  parameter-rich proviso disappears (\<open>completeness_fprov\<close>).\<close>

subsection \<open>Model existence and completeness (BKK Section 6, Corollary 7.7)\<close>

text \<open>We build a Henkin term model from a maximal consistent, saturated set of sentences, following
  BKK's model-existence route (BKK Section 6).  \<open>NK\<close>-consistency and its closure properties
  (BKK Definition 7.4, Lemma 7.5) live in \<open>Calculus\<close>; here we develop the witnessing step,
  the maximal saturated extension (BKK Lemma 6.32), the term
  model with its truth lemma (BKK Theorem 6.33), and the completeness theorem itself
  (BKK Corollary 7.7).\<close>

subsubsection \<open>Witnessing a false universal
  (BKK property \<open>\<nabla>\<^sub>\<exists>\<close>, Definition 6.5; the \<open>\<nabla>\<^sub>\<exists>\<close> case of Lemma 7.5)\<close>

text \<open>If \<open>\<not>\<Pi>\<^bsub>\<alpha>\<^esub> G\<close> is consistent with \<open>\<Phi>\<close>, then it stays consistent when we add a witness
  \<open>\<not> (G c)\<close> for a fresh parameter \<open>c\<close>.  This is the key step for making the extension saturated.\<close>

lemma con_witness:
  assumes con: "con (insert (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)) \<Phi>)"
      and wG: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(G)" and fp: "freep \<Phi>"
      and c: "c \<notin> usedp \<Phi>" "c \<notin> pars G"
    shows "con (insert (\<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>))) (insert (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)) \<Phi>))"
proof (rule con_I)
  define \<Gamma> where "\<Gamma> = \<Phi> \<union> {\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)}"
  have fpG: "freep \<Gamma>" unfolding \<Gamma>_def by (rule freep_un[OF fp])
  assume "insert (\<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>))) (insert (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)) \<Phi>) \<turnstile> \<^bold>\<bottom>"
  hence "\<Gamma> \<union> {\<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>))} \<turnstile> \<^bold>\<bottom>" by (simp add: \<Gamma>_def insert_commute)
  hence "\<Gamma> \<turnstile> \<^bold>\<not> (Neg \<^bold>\<cdot> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>)))"
    using wff_Not[OF wff_App[OF wG wff_Par]] by (rule bprov.NegI)
  hence "\<Gamma> \<turnstile> G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>)"
    using wff_App[OF wG wff_Par] fpG by (rule dneg)
  moreover have "c \<notin> pars G" and "\<forall>D \<in> \<Gamma>. c \<notin> pars D" using c
    by (auto simp: \<Gamma>_def usedp_def)
  ultimately have piG: "\<Gamma> \<turnstile> (Pi \<alpha>) \<^bold>\<cdot> G" using wG
    by (blast intro: bprov.PiI)
  have "\<Gamma> \<turnstile> \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)" by (auto simp: \<Gamma>_def intro: bprov.Hyp)
  from this piG have "\<Gamma> \<turnstile> \<^bold>\<bottom>" using wff_FalseB by (rule bprov.NegE)
  thus False using con by (simp add: con_def \<Gamma>_def)
qed

subsubsection \<open>Signatures of arbitrary cardinality: the parameter reserve\<close>

text \<open>BKK run their extension lemma at any infinite signature cardinality \<open>\<aleph>\<^sub>s\<close> (BKK
  Remark 3.16).  To follow them beyond countable signatures, the enumeration of sentences
  below walks a well-order of the @{emph \<open>term type\<close>} instead of \<open>\<nat>\<close>, and the freshness
  argument becomes quantitative: the reserve of unused parameters must be as large as the
  @{emph \<open>signature\<close>}, not merely infinite.  The predicate \<open>richp\<close> ("parameter-rich")
  captures this, in the cardinal order \<open>\<le>o\<close> of the Isabelle/HOL library; over a countable
  signature it collapses to \<open>freep\<close> (@{emph \<open>infinite\<close>} reserve, BKK Definition 6.3).\<close>

unbundle cardinal_syntax

definition richp :: "'p tm set \<Rightarrow> bool" where "richp \<Phi> \<equiv> |UNIV :: 'p set| \<le>o |- usedp \<Phi>|"

lemma richp_freep:
  assumes "richp (\<Phi> :: 'p::infinite tm set)" shows "freep \<Phi>"
proof -
  have "|UNIV :: nat set| \<le>o |UNIV :: 'p set|"
    using infinite_iff_card_of_nat infinite_UNIV by blast
  from ordLeq_transitive[OF this assms[unfolded richp_def]]
  show ?thesis unfolding freep_def using infinite_iff_card_of_nat by blast
qed

lemma richp_iff_freep:
  fixes \<Phi> :: "'p::{countable,infinite} tm set"
  shows "richp \<Phi> \<longleftrightarrow> freep \<Phi>"
proof
  assume "richp \<Phi>" thus "freep \<Phi>" by (rule richp_freep)
next
  assume "freep \<Phi>"
  hence n: "|UNIV :: nat set| \<le>o |- usedp \<Phi>|"
    unfolding freep_def using infinite_iff_card_of_nat by blast
  have "|UNIV :: 'p set| \<le>o |UNIV :: nat set|"
    using card_of_ordLeq by fastforce
  thus "richp \<Phi>" unfolding richp_def using n ordLeq_transitive by blast
qed

lemma infinite_tm_UNIV: "infinite (UNIV :: 'p tm set)"
proof -
  have "inj (Bnd :: nat \<Rightarrow> 'p tm)" by (simp add: inj_on_def)
  thus ?thesis by (metis finite_imageD infinite_UNIV_nat infinite_super top_greatest)
qed

text \<open>Over an infinite signature there are at most as many terms as parameters: an infinite
  type absorbs pairing (\<open>|'p \<times> 'p| =o |'p|\<close>), so the whole term algebra encodes injectively
  into \<open>'p\<close> itself --- the nontrivial half of the identity \<open>|'p tm| = max(\<aleph>\<^sub>0, |'p|)\<close>, and
  the only half needed here.
  The encoder \<open>tmenc\<close> tags each constructor and recurses through an injective pairing.\<close>

primrec tmenc :: "('u \<times> 'u \<Rightarrow> 'u) \<Rightarrow> (nat \<Rightarrow> 'u) \<Rightarrow> ('p \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" where
  "tmenc pr2 nt pt (Bnd n) = pr2 (nt 0, nt n)"
| "tmenc pr2 nt pt (Fre n \<sigma>) = pr2 (nt 1, pr2 (nt n, nt (to_nat \<sigma>)))"
| "tmenc pr2 nt pt (Par p \<sigma>) = pr2 (nt 2, pr2 (pt p, nt (to_nat \<sigma>)))"
| "tmenc pr2 nt pt Neg = pr2 (nt 3, nt 0)"
| "tmenc pr2 nt pt Dis = pr2 (nt 4, nt 0)"
| "tmenc pr2 nt pt (Pi \<sigma>) = pr2 (nt 5, nt (to_nat \<sigma>))"
| "tmenc pr2 nt pt (Iota \<sigma>) = pr2 (nt 6, nt (to_nat \<sigma>))"
| "tmenc pr2 nt pt (Eq \<sigma>) = pr2 (nt 7, nt (to_nat \<sigma>))"
| "tmenc pr2 nt pt (App s t) = pr2 (nt 8, pr2 (tmenc pr2 nt pt s, tmenc pr2 nt pt t))"
| "tmenc pr2 nt pt (Abs \<sigma> b) = pr2 (nt 9, pr2 (nt (to_nat \<sigma>), tmenc pr2 nt pt b))"

lemma tmenc_inj:
  assumes p2: "inj pr2" and nt: "inj nt" and pt: "inj pt"
  shows "tmenc pr2 nt pt s = tmenc pr2 nt pt t \<Longrightarrow> s = t"
  by (induction s arbitrary: t)
     (case_tac t; force dest!: injD[OF p2] injD[OF nt] injD[OF pt])+

lemma card_of_tm: "|UNIV :: 'p tm set| \<le>o |UNIV :: 'p::infinite set|"
proof -
  have "|UNIV :: ('p \<times> 'p) set| =o |UNIV :: 'p set|"
    using card_of_Times_same_infinite[OF infinite_UNIV] by simp
  hence "|UNIV :: ('p \<times> 'p) set| \<le>o |UNIV :: 'p set|"
    by (rule ordIso_imp_ordLeq)
  then obtain pr2 :: "'p \<times> 'p \<Rightarrow> 'p" where p2: "inj pr2"
    by (meson card_of_ordLeq)
  obtain nt :: "nat \<Rightarrow> 'p" where nt: "inj nt"
    using infinite_UNIV infinite_countable_subset by blast
  have idp: "inj (id :: 'p \<Rightarrow> 'p)" by (simp add: inj_on_def)
  have "inj (tmenc pr2 nt id)"
    using tmenc_inj[OF p2 nt idp] by (auto intro: injI)
  thus ?thesis by (simp add: card_of_ordLeqI)
qed

lemma richp_reserve:
  assumes "richp (\<Phi> :: 'p::infinite tm set)"
  shows "|UNIV :: 'p tm set| \<le>o |- usedp \<Phi>|"
  by (rule ordLeq_transitive[OF card_of_tm assms[unfolded richp_def]])

text \<open>Two small counting facts: a finite set is strictly smaller than any infinite type, and
  a union of fewer-than-\<open>|'k|\<close> finite sets stays strictly smaller than \<open>|'k|\<close> --- no
  regularity of the cardinal is needed, because the members are finite.\<close>

lemma card_of_finite_infinite:
  assumes "finite (A :: 'a set)" and "infinite (B :: 'b set)"
  shows "|A| <o |B|"
  using assms
  by (intro finite_ordLess_infinite) (auto simp: Field_card_of card_of_well_order_on)

lemma card_of_UNION_finite_small:
  fixes F :: "'i \<Rightarrow> 'a set"
  assumes small: "|I| <o |UNIV :: 'k set|" and inf: "infinite (UNIV :: 'k set)"
      and fin: "\<And>i. i \<in> I \<Longrightarrow> finite (F i)"
  shows "|\<Union>i\<in>I. F i| <o |UNIV :: 'k set|"
proof (cases "finite I")
  case True
  hence "finite (\<Union>i\<in>I. F i)" using fin by blast
  thus ?thesis using inf by (rule card_of_finite_infinite)
next
  case False
  have "|\<Union>i\<in>I. F i| \<le>o |I|"
  proof (rule card_of_UNION_ordLeq_infinite[OF False])
    show "|I| \<le>o |I|" by (rule ordLeq_reflexive[OF card_of_Well_order])
    show "\<forall>i\<in>I. |F i| \<le>o |I|"
      using fin False by (blast intro: ordLess_imp_ordLeq card_of_finite_infinite)
  qed
  thus ?thesis using small by (rule ordLeq_ordLess_trans)
qed

text \<open>A full-size reserve survives removing finitely many elements --- the workhorse
  behind the closure properties of \<open>richp\<close>.\<close>

lemma card_of_diff_finite:
  assumes rich: "|UNIV :: 'a::infinite set| \<le>o |R :: 'a set|" and fin: "finite F"
  shows "|UNIV :: 'a set| \<le>o |R - F|"
proof (rule ccontr)
  assume "\<not> |UNIV :: 'a set| \<le>o |R - F|"
  hence l: "|R - F| <o |UNIV :: 'a set|"
    by (metis card_of_Well_order not_ordLeq_iff_ordLess)
  have "R \<subseteq> (R - F) \<union> F" by blast
  hence "|R| \<le>o |(R - F) \<union> F|" by (rule card_of_mono1)
  moreover have "|(R - F) \<union> F| <o |UNIV :: 'a set|"
    by (rule card_of_Un_ordLess_infinite[OF infinite_UNIV l
          card_of_finite_infinite[OF fin infinite_UNIV]])
  ultimately show False
    using rich by (meson ordLeq_ordLess_trans ordLeq_transitive ordLess_irreflexive)
qed

text \<open>Like \<open>freep\<close>, richness survives adding one formula: only finitely many parameters
  are lost.\<close>

lemma richp_add:
  assumes "richp (\<Phi> :: 'p::infinite tm set)" shows "richp (insert B \<Phi>)"
proof -
  have "- usedp \<Phi> - pars B \<subseteq> - usedp (insert B \<Phi>)"
    by (auto simp: usedp_def)
  hence "|- usedp \<Phi> - pars B| \<le>o |- usedp (insert B \<Phi>)|"
    by (rule card_of_mono1)
  thus ?thesis
    unfolding richp_def
    using card_of_diff_finite[OF assms[unfolded richp_def] finite_pars]
          ordLeq_transitive by blast
qed

subsubsection \<open>Maximal consistent, saturated extension (BKK's abstract extension lemma 6.32)\<close>

text \<open>We enumerate the sentences along a well-order of the term type and, step by step,
  decide each one or its negation (\<open>con_split\<close>), immediately adding a Henkin witness for a
  decided negated universal (\<open>con_witness\<close>).  The union of the chain is a maximal
  consistent, saturated set.\<close>

definition freshc :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p" where
 "freshc S G \<equiv> SOME c. c \<notin> usedp S \<and> c \<notin> pars G"

lemma freshc_fresh: "freep S \<Longrightarrow> freshc S G \<notin> usedp S \<and> freshc S G \<notin> pars G"
  by (metis (lifting) finite_pars freep_fresh freshc_def someI_ex)

fun wit :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" where
  \<open>wit S (\<^bold>\<not>App (Pi \<alpha>) G) = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}\<close>
| \<open>wit _ _ = {}\<close>

lemma wit_cases: "wit S A = {} \<or> (\<exists>\<alpha> G. A = \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G) \<and>
   wit S A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))})"
  by (induct S A rule: wit.induct) auto
lemma finite_wit: "finite (wit S A)"
  by (induct S A rule: wit.induct) auto
definition step :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" where
  "step S A \<equiv> if cwff \<o> A
   then (if con (insert A S) then insert A S \<union> wit S A else insert (\<^bold>\<not> A) S)
   else S"

text \<open>The enumeration order: a well-order of the term type of @{emph \<open>minimal\<close>} order type,
  the cardinal \<open>|UNIV|\<close> of \<open>'p tm\<close> as provided by the library.  Strictly below any stage lie
  @{emph \<open>fewer\<close>} terms than there are terms in total (@{thm [source] card_of_underS}).\<close>

definition tmord :: "('p tm \<times> 'p tm) set" where
  "tmord = |UNIV :: 'p tm set|"

lemma tmord_wo: "wo_rel (tmord :: ('p tm \<times> 'p tm) set)"
  by (simp add: wo_rel_def tmord_def card_of_Well_order)

lemma tmord_wf: "wf (tmord - Id :: ('p tm \<times> 'p tm) set)"
  using card_of_well_order_on[of "UNIV :: 'p tm set"]
  unfolding well_order_on_def tmord_def by blast

lemma tmord_lin: "linear_order_on UNIV (tmord :: ('p tm \<times> 'p tm) set)"
  using card_of_well_order_on[of "UNIV :: 'p tm set"]
  unfolding well_order_on_def tmord_def by blast

lemma tmord_total: "a \<noteq> b \<Longrightarrow> (a, b) \<in> tmord \<or> (b, a) \<in> tmord"
  using tmord_lin unfolding linear_order_on_def total_on_def by blast

lemma tmord_trans: "(a, b) \<in> tmord \<Longrightarrow> (b, c) \<in> tmord \<Longrightarrow> (a, c) \<in> tmord"
  using tmord_lin
  unfolding linear_order_on_def partial_order_on_def preorder_on_def
  by (blast dest: transD)

lemma tmord_refl: "(a, a) \<in> tmord"
  using tmord_lin
  unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def by blast

lemma tmord_induct [case_names below]:
  assumes "\<And>a. (\<And>b. b \<in> underS tmord a \<Longrightarrow> P b) \<Longrightarrow> P a"
  shows "P (a :: 'p tm)"
proof (rule wf_induct_rule[OF tmord_wf])
  fix a :: "'p tm" assume IH: "\<And>b. (b, a) \<in> tmord - Id \<Longrightarrow> P b"
  show "P a"
  proof (rule assms)
    fix b assume "b \<in> underS tmord a"
    hence "(b, a) \<in> tmord - Id" by (auto simp: underS_def)
    thus "P b" by (rule IH)
  qed
qed

lemma tmord_underS_small: "|underS tmord (a :: 'p tm)| <o |UNIV :: 'p tm set|"
proof -
  have co: "Card_order (tmord :: ('p tm \<times> 'p tm) set)"
    unfolding tmord_def by (rule card_of_Card_order)
  have fld: "(a :: 'p tm) \<in> Field tmord"
    by (simp add: tmord_def Field_card_of)
  from card_of_underS[OF co fld] show ?thesis
    by (simp add: tmord_def)
qed

lemma tmord_under: "under tmord a = insert a (underS tmord a)"
  by (auto simp: under_def underS_def tmord_refl)

text \<open>The extension, by well-order recursion: at stage \<open>a\<close> the term \<open>a\<close> itself is decided
  over the union of all earlier stages (a no-op unless \<open>a\<close> is a sentence) --- each term is
  its own index, so no enumeration function is needed.\<close>

definition ext :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" where
  "ext \<Phi> = wo_rel.worec tmord (\<lambda>f a. step (\<Phi> \<union> (\<Union>b \<in> underS tmord a. f b)) a)"

lemma ext_unfold:
  fixes \<Phi> :: "'p tm set"
  shows "ext \<Phi> a = step (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b)) a"
proof -
  have adm: "wo_rel.adm_wo tmord (\<lambda>f a. step (\<Phi> \<union> (\<Union>b \<in> underS tmord a. f b)) a)"
  proof -
    { fix f g :: "'p tm \<Rightarrow> 'p tm set" and x :: "'p tm"
      assume "\<forall>y \<in> underS tmord x. f y = g y"
      hence "(\<Union>b \<in> underS tmord x. f b) = (\<Union>b \<in> underS tmord x. g b)" by auto
      hence "step (\<Phi> \<union> (\<Union>b \<in> underS tmord x. f b)) x
           = step (\<Phi> \<union> (\<Union>b \<in> underS tmord x. g b)) x" by simp }
    thus ?thesis unfolding wo_rel.adm_wo_def[OF tmord_wo] by blast
  qed
  show ?thesis
    using fun_cong[OF wo_rel.worec_fixpoint[OF tmord_wo adm], of a]
    unfolding ext_def by simp
qed

definition Hset :: "'p tm set \<Rightarrow> 'p tm set" where
  "Hset \<Phi> = (\<Union>a. ext \<Phi> a)"

text \<open>The chain is directed, each stage extends \<open>\<Phi>\<close>, and each stage stays \<open>freep\<close> and consistent.\<close>

lemma step_expand: "S \<subseteq> step S A"
  by (auto simp: step_def)

text \<open>Statement preserved verbatim from the published version of this entry (compatibility
  export); the transfinite chain below tracks parameter usage by counting instead.\<close>

lemma freep_step: "freep S \<Longrightarrow> freep (step S A)"
  by (simp add: finite_wit freep_add freep_un_finite step_def)

lemma ext_stage_sub: "\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b) \<subseteq> ext \<Phi> a"
  by (subst ext_unfold) (rule step_expand)

lemma Phi_sub_ext: "\<Phi> \<subseteq> ext \<Phi> a"
  using ext_stage_sub by blast

lemma ext_mono: "b \<in> underS tmord a \<Longrightarrow> ext \<Phi> b \<subseteq> ext \<Phi> a"
  using ext_stage_sub by blast

lemma ext_finite_ub:
  assumes "finite B" and "B \<noteq> {}"
  shows "\<exists>b \<in> B. \<forall>c \<in> B. ext \<Phi> c \<subseteq> ext \<Phi> b"
  using assms
proof (induction B rule: finite_ne_induct)
  case (singleton x) show ?case by blast
next
  case (insert x B)
  then obtain b where b: "b \<in> B" "\<forall>c\<in>B. ext \<Phi> c \<subseteq> ext \<Phi> b" by blast
  consider "x = b" | "x \<in> underS tmord b" | "b \<in> underS tmord x"
    using tmord_total by (auto simp: underS_def)
  thus ?case
  proof cases
    case 1 thus ?thesis using b by blast
  next
    case 2 thus ?thesis using b ext_mono by blast
  next
    case 3
    hence bx: "ext \<Phi> b \<subseteq> ext \<Phi> x" by (rule ext_mono)
    thus ?thesis using b by blast
  qed
qed

lemma ext_directed: "\<exists>c. ext \<Phi> a \<subseteq> ext \<Phi> c \<and> ext \<Phi> b \<subseteq> ext \<Phi> c"
proof -
  have "\<exists>d \<in> {a, b}. \<forall>c \<in> {a, b}. ext \<Phi> c \<subseteq> ext \<Phi> d"
    by (rule ext_finite_ub) auto
  thus ?thesis by blast
qed
lemma con_step: assumes "con S" and "freep S" shows "con (step S A)"
proof (cases "cwff \<o> A")
  case False
  with assms(1) show ?thesis by (auto simp: step_def)
next case True
  show ?thesis 
  proof (cases "con (insert A S)")
    case False
    hence "con (insert (\<^bold>\<not> A) S)"
      using con_split[OF assms(1)] cwff_wff[OF True] by blast
    thus ?thesis using False True by (simp add: step_def)
  next
    case True
    have "con (insert A S \<union> wit S A)" using wit_cases[of S A]  
    proof
      assume "wit S A = {}" thus ?thesis using True by simp
    next
      assume "\<exists>\<alpha> G. A = \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G) \<and> wit S A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}"
      then obtain \<alpha> G where AG: "A = \<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)"
        and w: "wit S A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}" by blast
      have wG: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(G)" using cwff_wff[OF \<open>cwff \<o> A\<close>] AG
        by (auto dest: wff_unique)
      have fr: "freshc S G \<notin> usedp S" "freshc S G \<notin> pars G"
        using freshc_fresh[OF assms(2)] by auto
      have "con (insert (\<^bold>\<not> (G \<^bold>\<cdot> ((freshc S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))) (insert A S))"
        by (metis AG True assms(2) con_witness fr(1,2) wG)
      thus ?thesis using w by simp
    qed
    thus ?thesis using True \<open>cwff \<o> A\<close> by (simp add: step_def)
  qed
qed
text \<open>Bookkeeping for freshness: each stage consumes only finitely many parameters (the
  sentence decided, plus at most one witness), and below any stage there are fewer stages
  than terms --- while the \<open>richp\<close> reserve holds at least \<open>|'p tm|\<close>-many parameters
  (@{thm [source] richp_reserve}).  So every stage stays \<open>freep\<close> --- which is all
  that \<open>con_step\<close> asks for.\<close>

definition stagep :: "'p tm set \<Rightarrow> 'p tm \<Rightarrow> 'p set" where
  "stagep \<Phi> b = pars b \<union> usedp (wit (\<Phi> \<union> (\<Union>c \<in> underS tmord b. ext \<Phi> c)) b)"

lemma finite_stagep: "finite (stagep \<Phi> b)"
  by (simp add: stagep_def finite_wit usedp_def)

lemma usedp_step_sub: "usedp (step S A) \<subseteq> usedp S \<union> pars A \<union> usedp (wit S A)"
  by (auto simp: step_def usedp_def)

lemma usedp_ext_bound:
  "usedp (ext \<Phi> a) \<subseteq> usedp \<Phi> \<union> (\<Union>b \<in> under tmord a. stagep \<Phi> b)"
proof (induction a rule: tmord_induct)
  case (below a)
  have su: "c \<in> under tmord a" if "b \<in> underS tmord a" "c \<in> under tmord b" for b c
    using that by (auto simp: under_def underS_def intro: tmord_trans)
  have "usedp (ext \<Phi> a)
        \<subseteq> usedp (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b)) \<union> stagep \<Phi> a"
    using usedp_step_sub[of "\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b)" a]
    by (subst ext_unfold) (auto simp: stagep_def)
  moreover have "usedp (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b))
        = usedp \<Phi> \<union> (\<Union>b \<in> underS tmord a. usedp (ext \<Phi> b))"
    by (auto simp: usedp_def)
  moreover have "usedp (ext \<Phi> b) \<subseteq> usedp \<Phi> \<union> (\<Union>c \<in> under tmord a. stagep \<Phi> c)"
    if b: "b \<in> underS tmord a" for b
    using below.IH[OF b] su[OF b] by blast
  moreover have "a \<in> under tmord a" by (simp add: tmord_under)
  ultimately show ?case by blast
qed

lemma ext_reserve:
  assumes rp: "richp (\<Phi> :: 'p::infinite tm set)"
  shows "freep (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b))" and "freep (ext \<Phi> a)"
proof -
  define X where "X = (\<Union>b \<in> under tmord a. stagep \<Phi> b)"
  have "under tmord (a :: 'p tm) = {a} \<union> underS tmord a"
    by (auto simp: tmord_under)
  hence "|under tmord (a :: 'p tm)| <o |UNIV :: 'p tm set|"
    using card_of_Un_ordLess_infinite[OF infinite_tm_UNIV
          card_of_finite_infinite[OF _ infinite_tm_UNIV] tmord_underS_small,
          of "{a}"] by simp
  hence Xsmall: "|X| <o |UNIV :: 'p tm set|"
    unfolding X_def
    by (rule card_of_UNION_finite_small[OF _ infinite_tm_UNIV]) (rule finite_stagep)
  have su: "c \<in> under tmord a" if "b \<in> underS tmord a" "c \<in> under tmord b" for b c
    using that by (auto simp: under_def underS_def intro: tmord_trans)
  have bound': "usedp (ext \<Phi> b) \<subseteq> usedp \<Phi> \<union> X" if b: "b \<in> under tmord a" for b
  proof (cases "b = a")
    case True
    thus ?thesis using usedp_ext_bound[of \<Phi> b] unfolding X_def by simp
  next
    case False
    hence bS: "b \<in> underS tmord a" using b by (auto simp: under_def underS_def)
    have "(\<Union>c \<in> under tmord b. stagep \<Phi> c) \<subseteq> X"
      unfolding X_def using su[OF bS] by blast
    thus ?thesis using usedp_ext_bound[of \<Phi> b] by blast
  qed
  have bound: "usedp (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b)) \<subseteq> usedp \<Phi> \<union> X"
  proof -
    have "usedp (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b))
        = usedp \<Phi> \<union> (\<Union>b \<in> underS tmord a. usedp (ext \<Phi> b))"
      by (auto simp: usedp_def)
    moreover have "usedp (ext \<Phi> b) \<subseteq> usedp \<Phi> \<union> X" if "b \<in> underS tmord a" for b
      using bound' that by (auto simp: under_def underS_def)
    ultimately show ?thesis by blast
  qed
  have inf: "infinite (- (usedp \<Phi> \<union> X))"
  proof
    assume fin: "finite (- (usedp \<Phi> \<union> X))"
    have "- usedp \<Phi> \<subseteq> X \<union> (- (usedp \<Phi> \<union> X))" by blast
    hence "|- usedp \<Phi>| \<le>o |X \<union> (- (usedp \<Phi> \<union> X))|" by (rule card_of_mono1)
    moreover have "|X \<union> (- (usedp \<Phi> \<union> X))| <o |UNIV :: 'p tm set|"
      by (rule card_of_Un_ordLess_infinite[OF infinite_tm_UNIV Xsmall
            card_of_finite_infinite[OF fin infinite_tm_UNIV]])
    ultimately have "|UNIV :: 'p tm set| <o |UNIV :: 'p tm set|"
      using richp_reserve[OF rp] by (meson ordLeq_ordLess_trans ordLeq_transitive)
    thus False using ordLess_irreflexive by blast
  qed
  show "freep (\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b))"
    unfolding freep_def by (rule infinite_super[OF _ inf]) (use bound in blast)
  have aa: "a \<in> under tmord a" by (simp add: under_def tmord_refl)
  show "freep (ext \<Phi> a)"
    unfolding freep_def
    by (rule infinite_super[OF _ inf]) (use bound'[OF aa] in blast)
qed

lemma con_ext:
  assumes con\<Phi>: "con \<Phi>" and rp: "richp (\<Phi> :: 'p::infinite tm set)"
  shows "con (ext \<Phi> a)"
proof (induction a rule: tmord_induct)
  case (below a)
  let ?S = "\<Phi> \<union> (\<Union>b \<in> underS tmord a. ext \<Phi> b)"
  have conS: "con ?S"
  proof (rule con_compact)
    fix F :: "'p tm set" assume finF: "finite F" and subF: "F \<subseteq> ?S"
    show "con F"
    proof (cases "F \<subseteq> \<Phi>")
      case True
      show ?thesis by (rule con_mono[OF con\<Phi> True richp_freep[OF rp]])
    next
      case False
      have "\<forall>x \<in> F - \<Phi>. \<exists>b. b \<in> underS tmord a \<and> x \<in> ext \<Phi> b"
        using subF by blast
      then obtain f where f: "\<And>x. x \<in> F - \<Phi> \<Longrightarrow> f x \<in> underS tmord a \<and> x \<in> ext \<Phi> (f x)"
        by (metis bchoice)
      have finB: "finite (f ` (F - \<Phi>))" and neB: "f ` (F - \<Phi>) \<noteq> {}"
        and subB: "f ` (F - \<Phi>) \<subseteq> underS tmord a"
        using finF False f by auto
      obtain b where b: "b \<in> f ` (F - \<Phi>)" "\<And>c. c \<in> f ` (F - \<Phi>) \<Longrightarrow> ext \<Phi> c \<subseteq> ext \<Phi> b"
        using ext_finite_ub[where \<Phi> = \<Phi>, OF finB neB] by blast
      have FbF: "F \<subseteq> ext \<Phi> b"
      proof
        fix x assume x: "x \<in> F"
        show "x \<in> ext \<Phi> b"
        proof (cases "x \<in> \<Phi>")
          case True thus ?thesis using Phi_sub_ext by blast
        next
          case False
          hence "x \<in> ext \<Phi> (f x)" and "f x \<in> f ` (F - \<Phi>)" using f x by auto
          thus ?thesis using b(2) by blast
        qed
      qed
      have conb: "con (ext \<Phi> b)" using below.IH b(1) subB by blast
      show ?thesis by (rule con_mono[OF conb FbF ext_reserve(2)[OF rp]])
    qed
  qed
  show ?case by (subst ext_unfold) (rule con_step[OF conS ext_reserve(1)[OF rp]])
qed

text \<open>\<open>Hset \<Phi>\<close> extends \<open>\<Phi>\<close> and, by compactness, is consistent.\<close>

lemma Phi_sub_Hset: "\<Phi> \<subseteq> Hset \<Phi>"
  unfolding Hset_def using Phi_sub_ext by blast

lemma finite_sub_ext: "finite F \<Longrightarrow> F \<subseteq> Hset \<Phi> \<Longrightarrow> \<exists>a. F \<subseteq> ext \<Phi> a"
proof (induction F rule: finite_induct)
  case empty thus ?case by blast
next
  case (insert x F)
  then obtain a where a: "F \<subseteq> ext \<Phi> a" by auto
  from insert.prems obtain b where b: "x \<in> ext \<Phi> b" by (auto simp: Hset_def)
  obtain c where "ext \<Phi> a \<subseteq> ext \<Phi> c" and "ext \<Phi> b \<subseteq> ext \<Phi> c"
    using ext_directed by blast
  thus ?case using a b by blast
qed

lemma con_Hset: fixes \<Phi> :: "'p::infinite tm set"
  assumes "con \<Phi>" and "richp \<Phi>"
  shows "con (Hset \<Phi>)"
  by (meson assms con_compact con_ext con_mono ext_reserve(2) finite_sub_ext)

text \<open>Crucially, \<open>freep (Hset \<Phi>)\<close> fails (a maximal set uses every parameter), so we never weaken
  @{emph \<open>to\<close>} \<open>Hset\<close>.  Instead we use that every @{emph \<open>finite\<close>} subset of \<open>Hset\<close> is
  consistent --- finite contexts are always \<open>freep\<close>, which is all the proof rules need.\<close>

lemma Hset_finite_con: fixes \<Phi> :: "'p::infinite tm set"
  assumes "con \<Phi>" and "richp \<Phi>" and "finite F" and "F \<subseteq> Hset \<Phi>"
  shows "con F"
  by (meson assms con_ext con_mono ext_reserve(2) finite_sub_ext)

text \<open>\<open>Hset\<close> decides every sentence --- BKK call this @{emph \<open>saturated\<close>}, property \<open>\<^sub>~\<nabla>\<^sub>s\<^sub>a\<^sub>t\<close>
  (BKK Definition 6.24) --- and has the Henkin witness property \<open>\<^sub>~\<nabla>\<^sub>\<exists>\<close> (BKK Definition 6.19).
  We call the former @{emph \<open>maximality\<close>} and reserve @{emph \<open>saturation\<close>} for the witness
  property; the lemma names below follow this convention.\<close>

lemma Hset_maximal:
  assumes c: "cwff \<o> A" shows "A \<in> Hset \<Phi> \<or> \<^bold>\<not> A \<in> Hset \<Phi>"
proof -
  have "A \<in> ext \<Phi> A \<or> \<^bold>\<not> A \<in> ext \<Phi> A"
    using c by (subst (1 2) ext_unfold) (simp add: step_def)
  thus ?thesis unfolding Hset_def by blast
qed
lemma Hset_saturated: fixes \<Phi> :: "'p::infinite tm set"
  assumes con\<Phi>: "con \<Phi>" and fp: "richp \<Phi>"
  and cA: "cwff \<o> (\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G))" and inH: "\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G) \<in> Hset \<Phi>"
shows "\<exists>c. \<^bold>\<not> (G \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<alpha>\<^esub>)) \<in> Hset \<Phi>"
proof -
  note wA = cwff_wff[OF cA]
  let ?A = "\<^bold>\<not> ((Pi \<alpha>) \<^bold>\<cdot> G)"
  let ?S = "\<Phi> \<union> (\<Union>b \<in> underS tmord ?A. ext \<Phi> b)"
  have step: "ext \<Phi> ?A = step ?S ?A"
    by (rule ext_unfold)
  have "con (insert ?A ?S)"
  proof (rule ccontr)
    assume "\<not> con (insert ?A ?S)"
    hence "\<^bold>\<not> ?A \<in> ext \<Phi> ?A" using cA step
        by (auto simp: step_def)
    hence "\<^bold>\<not> ?A \<in> Hset \<Phi>" unfolding Hset_def by blast
    thus False using con_not_both[OF con_Hset[OF con\<Phi> fp] inH _ wA]
        by blast
  qed
  hence "wit ?S ?A \<subseteq> ext \<Phi> ?A" using cA step
    by (auto simp: step_def)
  moreover have "wit ?S ?A = {\<^bold>\<not> (G \<^bold>\<cdot> ((freshc ?S G)\<^sup>p\<^bsub>\<alpha>\<^esub>))}"
    by simp
  ultimately have "\<^bold>\<not> (G \<^bold>\<cdot> ((freshc ?S G)\<^sup>p\<^bsub>\<alpha>\<^esub>)) \<in> Hset \<Phi>"
    unfolding Hset_def by blast
  thus ?thesis by blast
qed

subsubsection \<open>Deductive closure of the Hintikka set\<close>

text \<open>Since \<open>Hset\<close> is maximal and each of its finite subsets is consistent, every sentence
    provable from a finite subset already belongs to \<open>Hset\<close> (deductive closure --- a consequence
    of the maximality of the extension, BKK Lemma 6.32).\<close>

lemma Hset_deduct: fixes \<Phi> :: "'p::infinite tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "richp \<Phi>"
      and finF: "finite F" and subF: "F \<subseteq> Hset \<Phi>" and FS: "F \<turnstile> S"
      and cS: "cwff \<o> S" shows "S \<in> Hset \<Phi>"
proof (rule ccontr)
  assume "S \<notin> Hset \<Phi>"
  hence negS: "\<^bold>\<not> S \<in> Hset \<Phi>" using Hset_maximal[OF cS] by blast
  have fin': "finite (insert (\<^bold>\<not> S) F)" using finF by simp
  have sub': "insert (\<^bold>\<not> S) F \<subseteq> Hset \<Phi>" using negS subF by auto
  have "insert (\<^bold>\<not> S) F \<turnstile> \<^bold>\<bottom>"
    by (meson FS Hyp NegE bprov_weaken fin' freep_finite insertCI subset_insertI wff_FalseB)
  moreover have "con (insert (\<^bold>\<not> S) F)"
      by (rule Hset_finite_con[OF con\<Phi> fp\<Phi> fin' sub'])
  ultimately show False by (simp add: con_def)
qed

subsection \<open>The term model (BKK Section 6, the Hintikka lemma)\<close>

text \<open>Fix a consistent, parameter-rich set \<open>\<Phi>\<close>; its Hintikka extension \<open>H\<close> is maximal, consistent
  and saturated.  The @{emph \<open>term model\<close>} has as its domain the closed well-formed terms quotiented
  by provable Leibniz equality \<open>A \<sim> B \<equiv> (A \<^bold>\<doteq> B) \<in> H\<close>; this quotient is what forces property q.\<close>

locale hintikka_model = fixes \<Phi> :: "'p::infinite tm set"
  assumes con\<Phi>: "con \<Phi>" and fp\<Phi>: "richp \<Phi>"
begin

text \<open>Leibniz equality is reflexive on \<open>Hset\<close> --- BKK's property \<open>\<nabla>\<^sub>r\<close> for saturated
  Hintikka sets (Lemma 6.25; Lemma 6.23 gives the negative form \<open>\<^sub>~\<nabla>\<^sub>=\<^sub>r\<close>); symmetry,
  transitivity, congruence and truth-transfer follow, all by @{thm [source] Hset_deduct}
  over the corresponding derived rules of the calculus.\<close>

lemma Hset_leib_refl: assumes ca: "cwff \<alpha> A" shows "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{}"])
  show "finite {}" by simp
  show "{} \<subseteq> Hset \<Phi>" by simp
  show "{} \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A" by (rule leib_refl[OF cwff_wff[OF ca]])
  show "cwff \<o> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A)" by (rule cwff_LeibE[OF ca ca])
qed

lemma Hset_leib_sym:
  assumes ca: "cwff \<alpha> A" and cb: "cwff \<alpha> B" and AB: "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B) \<in> Hset \<Phi>"
  shows "(B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>])
  note wa = cwff_wff[OF ca] and wb = cwff_wff[OF cb]
  show "finite {A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B}" by simp
  show "{A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B} \<subseteq> Hset \<Phi>" using AB by simp
  show "{A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B} \<turnstile> B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A"
    by (simp add: Hyp freep_finite leib_sym wa wb)
  show "cwff \<o> (B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A)" by (rule cwff_LeibE[OF cb ca])
qed

lemma Hset_leib_trans:
  assumes ca: "cwff \<alpha> A" and wb: "wff\<^bsub>\<alpha>\<^esub>(B)" and cc: "cwff \<alpha> C"
  and AB: "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B) \<in> Hset \<Phi>" and BC: "(B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C) \<in> Hset \<Phi>"
  shows "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>])
  note wa = cwff_wff[OF ca] and wc = cwff_wff[OF cc]
  let ?F = "{A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B, B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C}"
  show "finite ?F" by simp
  show "?F \<subseteq> Hset \<Phi>" using AB BC by simp
  show "?F \<turnstile> A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C"
    by (meson Hyp \<open>finite {A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B, B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C}\<close> freep_finite insertCI
        leib_trans wa wb wc)
  show "cwff \<o> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> C)" by (rule cwff_LeibE[OF ca cc])
qed

lemma Hset_leib_cong:
  assumes cc: "cwff (\<alpha>\<^bold>\<Rightarrow>\<beta>) C" and cc': "cwff (\<alpha>\<^bold>\<Rightarrow>\<beta>) C'" and ca: "cwff \<alpha> A"
      and ca': "cwff \<alpha> A'"
      and CC: "(C \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> C') \<in> Hset \<Phi>" and AA: "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A') \<in> Hset \<Phi>"
    shows "((C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A')) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>])
  note wC = cwff_wff[OF cc] and wC' = cwff_wff[OF cc'] and
       wA = cwff_wff[OF ca] and wA' = cwff_wff[OF ca']
  let ?F = "{C \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> C', A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> A'}"
  have fp: "freep ?F" using freep_finite[of ?F] by simp
  show "finite ?F" by simp
  show "?F \<subseteq> Hset \<Phi>" using CC AA by simp
  show "?F \<turnstile> (C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A')"
    by (meson Hyp fp insertCI leib_cong1 leib_cong2 leib_trans wA wA' wC wC'
              wff_App[OF wC' wA] wff_App[OF wC' wA'] wff_App[OF wC wA])
  show "cwff \<o> ((C \<^bold>\<cdot> A) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> (C' \<^bold>\<cdot> A'))"
    by (rule cwff_LeibE[OF cwff_App[OF cc ca] cwff_App[OF cc' ca']])
qed

text \<open>Leibniz-equal propositions have the same truth (membership transfers along \<open>\<sim>\<close> at
  type \<open>\<o>\<close>); by Leibniz transport with the identity predicate.\<close>

lemma Hset_leib_mp:
  assumes ca: "cwff \<o> A" and cb: "cwff \<o> B" and AB: "(A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B) \<in> Hset \<Phi>"
      and A: "A \<in> Hset \<Phi>"
    shows "B \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi> _ _ _ cb])
  note wA = cwff_wff[OF ca] and wB = cwff_wff[OF cb]
  let ?F = "{A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B, A}"
  let ?P = "\<^bold>\<Lambda>\<^bsub>\<o>\<^esub> (Bnd 0)"   \<comment> \<open>the identity predicate\<close>
  have wP: "wff\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub>(?P)" by (rule wff_AbsI) (simp add: wff_Fre)
  have fp: "freep ?F" using freep_finite[of ?F] by simp
  have PA: "?P \<^bold>\<cdot> A \<approx>\<^bsub>\<o>\<^esub> A" using beq.beta[OF wP wA] by simp
  have PB: "?P \<^bold>\<cdot> B \<approx>\<^bsub>\<o>\<^esub> B" using beq.beta[OF wP wB] by simp
  show "finite ?F" by simp
  show "?F \<subseteq> Hset \<Phi>" using AB A by simp
  have s1: "?F \<turnstile> A \<^bold>\<doteq>\<^bsub>\<o>\<^esub> B" by (auto intro: bprov.Hyp)
  show "?F \<turnstile> B"
    by (rule leib_transport[OF s1 fp wA wB wP PA PB]) (auto intro: bprov.Hyp)
qed

text \<open>The \<open>\<sim>\<close>-equivalence classes of closed well-formed terms (@{const cwff} from
  Section 1): \<open>A \<sim> B \<equiv> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> H\<close> --- the Leibniz quotient of BKK's model-existence proof
  (BKK Theorem 6.33); the \<open>\<^sub>~\<nabla>\<close>-properties of Leibniz equality in \<open>H\<close> are BKK Lemma 6.23.\<close>

definition cls :: "'p tm \<Rightarrow> 'p tm set" where
  "cls A \<equiv> {B. \<exists>\<sigma>. cwff \<sigma> A \<and> cwff \<sigma> B \<and> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> Hset \<Phi>}"
lemma cls_self: "cwff \<sigma> A \<Longrightarrow> A \<in> cls A"
  using Hset_leib_refl by (auto simp: cls_def)

text \<open>The quotient is faithful: two classes coincide exactly when the terms are Leibniz-equal in
  \<open>H\<close>.  This is what will give property q in the model.\<close>

lemma cls_eq_iff:
  assumes wA: "cwff \<sigma> A" and wB: "cwff \<sigma> B"
    shows "(cls A = cls B) \<longleftrightarrow> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> B) \<in> Hset \<Phi>" 
  by (smt (verit, best) Collect_cong cls_def cls_self cwff_unique cwff_wff
      Hset_leib_sym Hset_leib_trans mem_Collect_eq wA wB)

lemma cls_rep:
  assumes "cwff \<sigma> A"
  shows "cwff \<sigma> (SOME B. B \<in> cls A) \<and> (A \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> (SOME B. B \<in> cls A)) \<in> Hset \<Phi>"
proof -
  have "(SOME B. B \<in> cls A) \<in> cls A" using cls_self[OF assms]
    by (metis someI)
  then obtain \<tau> where t: "cwff \<tau> A" "cwff \<tau> (SOME B. B \<in> cls A)"
    "(A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> (SOME B. B \<in> cls A)) \<in> Hset \<Phi>" by (auto simp: cls_def)
  have "\<tau> = \<sigma>" using cwff_unique[OF t(1) assms].
  thus ?thesis using t(2,3) by simp
qed

text \<open>The applicative structure of the term model (BKK Definition 3.1): the domain of type \<open>\<sigma>\<close>
  consists of the classes of closed terms of type \<open>\<sigma>\<close>, and application is term application.\<close>

definition Dm :: "ty \<Rightarrow> 'p tm set \<Rightarrow> bool" where "Dm \<sigma> X \<equiv> \<exists>A. cwff \<sigma> A \<and> X = cls A"
definition Ap :: "'p tm set \<Rightarrow> 'p tm set \<Rightarrow> 'p tm set" where
  "Ap X Y \<equiv> cls ((SOME A. A \<in> X) \<^bold>\<cdot> (SOME B. B \<in> Y))"
lemma Ap_cls:
  assumes wA: "cwff (\<alpha> \<^bold>\<Rightarrow> \<beta>) A" and wB: "cwff \<alpha> B"
    shows "Ap (cls A) (cls B) = cls (A \<^bold>\<cdot> B)"
proof -
  have a: "cwff (\<alpha> \<^bold>\<Rightarrow> \<beta>) (SOME A'. A' \<in> cls A)" "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub> (SOME A'. A' \<in> cls A)) \<in> Hset \<Phi>" 
    using cls_rep[OF wA] by auto
  have b: "cwff \<alpha> (SOME B'. B' \<in> cls B)" "(B \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> (SOME B'. B' \<in> cls B)) \<in> Hset \<Phi>"
    using cls_rep[OF wB] by auto
  have wAB: "cwff \<beta> (A \<^bold>\<cdot> B)" using wA wB
    by (auto simp: cwff_def intro: wff_App)
  have "((A \<^bold>\<cdot> B) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> ((SOME A'. A' \<in> cls A) \<^bold>\<cdot> (SOME B'. B' \<in> cls B))) \<in> Hset \<Phi>"
    using Hset_leib_cong wA a(1) wB b(1) a(2) b(2) by (auto simp: cwff_def)
  moreover have "cwff \<beta> ((SOME A'. A' \<in> cls A) \<^bold>\<cdot> (SOME B'. B' \<in> cls B))" 
    using a(1) b(1) cwff_App by blast 
  ultimately have "cls (A \<^bold>\<cdot> B) = cls ((SOME A'. A' \<in> cls A) \<^bold>\<cdot> (SOME B'. B' \<in> cls B))"
    using cls_eq_iff wAB by blast
  thus ?thesis by (simp add: Ap_def)
qed
lemma Dm_cls: "cwff \<sigma> A \<Longrightarrow> Dm \<sigma> (cls A)" by (auto simp: Dm_def)

text \<open>Truth and falsity behave (the analogue of BKK Lemma 3.43 / property b): \<open>\<^bold>\<top> \<in> H\<close>, \<open>\<^bold>\<bottom> \<notin> H\<close>,
  so \<open>cls \<^bold>\<top> \<noteq> cls \<^bold>\<bottom>\<close>.\<close>

lemma Hset_TrueB: "\<^bold>\<top> \<in> Hset \<Phi>"
  using Hset_deduct bprov_TrueB con\<Phi> cwff_TrueB fp\<Phi> by blast 
lemma Hset_not_FalseB: "\<^bold>\<bottom> \<notin> Hset \<Phi>"
  by (metis hintikka_model_axioms Hyp con_def con_Hset hintikka_model_def)
lemma TF: "cls \<^bold>\<top> \<noteq> cls \<^bold>\<bottom>"
  using Hset_TrueB Hset_leib_mp Hset_not_FalseB cls_eq_iff con\<Phi>
        cwff_FalseB cwff_TrueB fp\<Phi> by blast

subsubsection \<open>Satisfaction bridges: membership in \<open>H\<close> as truth
  (BKK Lemma 6.21, Lemmas 6.25--6.26)\<close>

text \<open>\<open>H\<close> never contains both \<open>\<phi>\<close> and \<open>\<^bold>\<not>\<phi>\<close> (BKK's property \<open>\<^sub>~\<nabla>\<^sub>c\<close>, Definition 6.19,
  here for arbitrary sentences via Lemma 6.10).\<close>

lemma Hset_notboth: "wff\<^bsub>\<o>\<^esub>(\<phi>) \<Longrightarrow> \<phi> \<in> Hset \<Phi> \<Longrightarrow> \<^bold>\<not> \<phi> \<notin> Hset \<Phi>"
    using con\<Phi> con_Hset con_not_both fp\<Phi> by auto

text \<open>Boolean extensionality inside \<open>H\<close> (via the rule \<open>NK(b)\<close>; the saturated-sets lemma for
  property b, BKK Lemma 6.26): a member of \<open>H\<close> is Leibniz-equal to \<open>\<^bold>\<top>\<close>, a non-member
  to \<open>\<^bold>\<bottom>\<close>.\<close>

lemma Hset_eq_TrueB:
  assumes p: "\<phi> \<in> Hset \<Phi>" and w: "cwff \<o> \<phi>"
  shows "(\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<top>) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{\<phi>}"])
  show "finite {\<phi>}" by simp
  show "{\<phi>} \<subseteq> Hset \<Phi>" using p by simp
  show "{\<phi>} \<turnstile> \<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<top>"
    by (metis BoolE Hyp bprov_TrueB cwff_def insertCI insert_is_Un w wff_TrueB)
  show "cwff \<o> (\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<top>)"
    by (metis cwff_App cwff_TrueB cwff_def fvs_defs(5) w wff_Leib)   
qed

lemma Hset_eq_FalseB: assumes np: "\<^bold>\<not> \<phi> \<in> Hset \<Phi>" and w: "cwff \<o> \<phi>"
  shows "(\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<bottom>) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{\<^bold>\<not> \<phi>}"])
  show "finite {\<^bold>\<not> \<phi>}" by simp
  show "{\<^bold>\<not> \<phi>} \<subseteq> Hset \<Phi>" using np by simp
  show "{\<^bold>\<not> \<phi>} \<turnstile> \<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<bottom>" 
    by (metis BoolE Hyp NegE TrueB_def Un_empty_right
        Un_insert_right bprov_TrueB cwff_wff insertCI w wff_FalseB)
  show "cwff \<o> (\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<^bold>\<bottom>)" 
    by (metis w cwff_def cwff_FalseB cwff_App wff_Leib fvs_defs(5)) 
qed

text \<open>Sentences with the same truth value in \<open>H\<close> are Leibniz-equal in \<open>H\<close> (the general form
  of the \<open>NK(b)\<close> bridge, cf.\ BKK Lemma 6.26).\<close>

lemma Hset_iff_eq:
  assumes wp: "cwff \<o> \<phi>" and wq: "cwff \<o> \<psi>"
      and iff: "\<phi> \<in> Hset \<Phi> \<longleftrightarrow> \<psi> \<in> Hset \<Phi>" 
  shows "(\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> \<psi>) \<in> Hset \<Phi>" 
  by (metis Hset_eq_FalseB Hset_eq_TrueB Hset_maximal cls_eq_iff
      cwff_FalseB cwff_TrueB iff wp wq)

text \<open>THE satisfaction bridge: a sentence's class is the class of \<open>\<^bold>\<top>\<close> exactly when it is
  in \<open>H\<close> (the \<open>\<upsilon>\<close>-valuation of the term model in the proof of BKK Theorem 6.33).\<close>

lemma cls_TrueB_iff: "cwff \<o> \<phi> \<Longrightarrow> cls \<phi> = cls \<^bold>\<top> \<longleftrightarrow> \<phi> \<in> Hset \<Phi>" 
  by (metis Hset_eq_FalseB Hset_eq_TrueB Hset_maximal TF cls_eq_iff cwff_FalseB cwff_TrueB)

text \<open>Property b at the class level: the boolean domain has exactly the classes of \<open>\<^bold>\<top>\<close>
  and \<open>\<^bold>\<bottom>\<close> (BKK Definition 3.46).\<close>

lemma cls_bool: "cwff \<o> \<phi> \<Longrightarrow> cls \<phi> = cls \<^bold>\<top> \<or> cls \<phi> = cls \<^bold>\<bottom>" 
  by (metis TF cls_eq_iff cwff_FalseB cls_TrueB_iff Hset_iff_eq)
lemma cls_FalseB_iff: "cwff \<o> \<phi> \<Longrightarrow> cls \<phi> = cls \<^bold>\<bottom> \<longleftrightarrow> \<phi> \<notin> Hset \<Phi>" 
  by (metis cls_eq_iff cwff_FalseB TF Hset_iff_eq cls_TrueB_iff)

subsubsection \<open>The evaluation and logical conditions of the term model\<close>

text \<open>The \<open>\<beta>\<close>-condition (BKK Definition 3.18(4)) inside \<open>H\<close>: a \<open>\<beta>\<close>-redex is Leibniz-equal to
  its reduct, via the rule \<open>NK(\<beta>)\<close> applied to reflexivity.\<close>

lemma Hset_beta:
  assumes wAbs: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and wa: "cwff \<sigma> a"
    shows "((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> b\<^bold>\<langle>a\<^bold>\<rangle>) \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{}"])
  let ?A = "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a"  let ?B = "b\<^bold>\<langle>a\<^bold>\<rangle>"
  have wA: "wff\<^bsub>\<tau>\<^esub>(?A)"
    using cwff_wff[OF wAbs] cwff_wff[OF wa] by (auto intro: wff_App)
  have step: "(?B \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B) \<approx>\<^bsub>\<o>\<^esub> (?A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B)" 
    by (meson appL appR beq.sym beta cwff_wff wAbs wa wff_Leib wff_opn)
  show "{} \<turnstile> ?A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B"
    by (meson Beta cwff_def finite.emptyI freep_finite leib_refl local.step wAbs wa wff_opn) 
  show "finite {}" by simp
  show "{} \<subseteq> Hset \<Phi>" by simp
  show "cwff \<o> (?A \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> ?B)"
    by (meson cwff_App cwff_def cwff_opn fvs_defs(5) wAbs wa wff_Leib)
qed

text \<open>The \<open>L\<^bsub>\<not>\<^esub>\<close> condition (BKK Figure 2) at the class level, from maximality
  and consistency of \<open>H\<close>.\<close>

lemma cls_neg: "cwff \<o> \<phi> \<Longrightarrow> cls (\<^bold>\<not> \<phi>) = (if cls \<phi> = cls \<^bold>\<top> then cls \<^bold>\<bottom> else cls \<^bold>\<top>)"
  by (meson Hset_maximal Hset_notboth cwff_App cwff_Neg cwff_def
            cls_FalseB_iff cls_TrueB_iff)

text \<open>The \<open>L\<^bsub>\<or>\<^esub>\<close> condition: \<open>H\<close> treats disjunction disjunctively (BKK \<open>\<nabla>\<^sub>\<or>\<close>, Definition 6.19).\<close>

lemma Hset_dis_iff:
  assumes wp: "cwff \<o> \<phi>" and wq: "cwff \<o> \<psi>"
    shows "\<phi> \<^bold>\<or> \<psi> \<in> Hset \<Phi> \<longleftrightarrow> \<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi>" 
proof
  assume d: "\<phi> \<^bold>\<or> \<psi> \<in> Hset \<Phi>"
  show "\<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi>"
  proof (rule ccontr)
    assume "\<not> (\<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi>)"
    hence np: "\<^bold>\<not> \<phi> \<in> Hset \<Phi>" and nq: "\<^bold>\<not> \<psi> \<in> Hset \<Phi>"
      using Hset_maximal[OF wp] Hset_maximal[OF wq] by blast+
    let ?F = "{\<phi> \<^bold>\<or> \<psi>, \<^bold>\<not> \<phi>, \<^bold>\<not> \<psi>}"
    have "?F \<turnstile> \<phi> \<^bold>\<or> \<psi>" by (auto intro: bprov.Hyp)
    moreover have "?F \<union> {\<phi>} \<turnstile> \<^bold>\<bottom>"
      by (metis Hyp NegE insertCI insert_is_Un sup.commute wff_FalseB)   
    moreover have "?F \<union> {\<psi>} \<turnstile> \<^bold>\<bottom>"
      by (metis Hyp NegE Un_insert_right insertCI insert_subset sup_ge1 wff_FalseB)
    ultimately have "?F \<turnstile> \<^bold>\<bottom>"
      using cwff_wff[OF wp] cwff_wff[OF wq] by (metis bprov.DisE)
    moreover have "con ?F"
      by (meson Hset_finite_con con\<Phi> d empty_subsetI finite.emptyI finite.insertI
                fp\<Phi> insert_subsetI np nq)
    ultimately show False by (simp add: con_def)
  qed
next
  show "\<phi> \<in> Hset \<Phi> \<or> \<psi> \<in> Hset \<Phi> \<Longrightarrow> \<phi> \<^bold>\<or> \<psi> \<in> Hset \<Phi>" 
    by (meson DisIL DisIR Hset_deduct Hyp bprov_finite con\<Phi> cwff_App
        cwff_Dis cwff_def fp\<Phi> wp wq)
qed

lemma cls_dis:
  assumes wp: "cwff \<o> \<phi>" and wq: "cwff \<o> \<psi>"
  shows "cls (\<phi> \<^bold>\<or> \<psi>) = (if cls \<phi> = cls \<^bold>\<top> \<or> cls \<psi> = cls \<^bold>\<top> then cls \<^bold>\<top> else cls \<^bold>\<bottom>)"
proof -
  have wd: "cwff \<o> (\<phi> \<^bold>\<or> \<psi>)" using wp wq by (auto simp: cwff_def)
  show ?thesis by (simp add: Hset_dis_iff cls_FalseB_iff cls_TrueB_iff wd wp wq)
qed

text \<open>The \<open>L\<^sup>\<sigma>\<^bsub>\<forall>\<^esub>\<close> condition: \<open>H\<close> treats the quantifier universally --- \<open>NK(\<Pi>E)\<close> gives one
  direction, the witness property \<open>\<^sub>~\<nabla>\<^sub>\<exists>\<close> (BKK Definition 6.19) together with maximality the
  other.\<close>

lemma Hset_pi_iff:
  assumes wf: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f"
    shows "(Pi \<sigma>) \<^bold>\<cdot> f \<in> Hset \<Phi> \<longleftrightarrow> (\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>)"
proof
  assume pf: "(Pi \<sigma>) \<^bold>\<cdot> f \<in> Hset \<Phi>"
  have step: "f \<^bold>\<cdot> a \<in> Hset \<Phi>" if wa: "cwff \<sigma> a" for a
    by (meson Hset_maximal Hyp NegE PiE con\<Phi> con_Hset con_def
              cwff_App cwff_def fp\<Phi> local.wf pf wa wff_FalseB)
  thus "\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>" by blast
next
  assume all: "\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>"
  show "(Pi \<sigma>) \<^bold>\<cdot> f \<in> Hset \<Phi>"
  proof (rule ccontr)
    assume npf: "(Pi \<sigma>) \<^bold>\<cdot> f \<notin> Hset \<Phi>"
    have wPf: "wff\<^bsub>\<o>\<^esub>((Pi \<sigma>) \<^bold>\<cdot> f)"
      using cwff_wff[OF wf] by (auto intro: wff_App wff_Pi)
    have cPf: "fvs ((Pi \<sigma>) \<^bold>\<cdot> f) = {}"
      using cwff_closed[OF wf] by simp
    have n: "\<^bold>\<not> ((Pi \<sigma>) \<^bold>\<cdot> f) \<in> Hset \<Phi>"
      using Hset_maximal[OF cwffI[OF wPf cPf]] npf by blast
    have wn: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<not> ((Pi \<sigma>) \<^bold>\<cdot> f))" using wPf by (rule wff_Not)
    have cn: "fvs (\<^bold>\<not> ((Pi \<sigma>) \<^bold>\<cdot> f)) = {}" using cPf by simp
    obtain c where nc: "\<^bold>\<not> (f \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<sigma>\<^esub>)) \<in> Hset \<Phi>"
      using Hset_saturated[OF con\<Phi> fp\<Phi> cwffI[OF wn cn] n] by blast
    have inc: "f \<^bold>\<cdot> (c\<^sup>p\<^bsub>\<sigma>\<^esub>) \<in> Hset \<Phi>"
      using all[rule_format, of "c\<^sup>p\<^bsub>\<sigma>\<^esub>"] cwff_Par[of \<sigma> c] by simp
    show False
      using Hset_notboth[OF wff_App[OF cwff_wff[OF wf] wff_Par] inc] nc by simp
  qed
qed

lemma cls_pi:
  assumes wf: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f"
  shows "cls ((Pi \<sigma>) \<^bold>\<cdot> f) = (if (\<forall>a. cwff \<sigma> a \<longrightarrow> Ap (cls f) (cls a) = cls \<^bold>\<top>)
                             then cls \<^bold>\<top> else cls \<^bold>\<bottom>)"
proof -
  have wPf: "cwff \<o> ((Pi \<sigma>) \<^bold>\<cdot> f)"
    using wf by (auto simp: cwff_def intro: wff_App wff_Pi)
  have e: "(Ap (cls f) (cls a) = cls \<^bold>\<top>) = (f \<^bold>\<cdot> a \<in> Hset \<Phi>)" if a: "cwff \<sigma> a" for a
    using Ap_cls[OF wf a] cls_TrueB_iff[OF cwff_App[OF wf a]] by simp
  have inner: "(\<forall>a. cwff \<sigma> a \<longrightarrow> Ap (cls f) (cls a) = cls \<^bold>\<top>)
      = (\<forall>a. cwff \<sigma> a \<longrightarrow> App f a \<in> Hset \<Phi>)" using e by blast
  show ?thesis
    using cls_TrueB_iff[OF wPf] cls_FalseB_iff[OF wPf] Hset_pi_iff[OF wf] inner
    by (cases "\<forall>a. cwff \<sigma> a \<longrightarrow> f \<^bold>\<cdot> a \<in> Hset \<Phi>") auto
qed

text \<open>The \<open>\<beta>\<close>-condition transfers membership: a redex of type \<open>\<o>\<close> is in \<open>H\<close> exactly when its
  reduct is (via the Leibniz bridge).\<close>

lemma Hset_beta_iff:
  assumes "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and "cwff \<sigma> a"
  shows "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a \<in> Hset \<Phi> \<longleftrightarrow> b\<^bold>\<langle>a\<^bold>\<rangle> \<in> Hset \<Phi>"
  by (meson Hset_beta Hset_leib_mp Hset_leib_sym con\<Phi> cwff_App cwff_opn fp\<Phi> assms)

text \<open>Type uniqueness of the classes (BKK: the domains are disjoint by type).\<close>

lemma cls_type:
  "cwff \<sigma> s \<Longrightarrow> cwff \<tau> t \<Longrightarrow> cls s = cls t \<Longrightarrow> \<sigma> = \<tau>" 
  by (smt (verit, ccfv_SIG) cls_def cls_self cwff_unique mem_Collect_eq)

text \<open>Property q (BKK Definition 3.46): the Leibniz combinator itself is the identity
  relation of the term model, by @{thm cls_eq_iff}.\<close>

text \<open>The one step behind functionality and description: if every instance of an abstracted
  body lies in \<open>H\<close>, the \<open>\<Pi>\<close>-sentence lies in \<open>H\<close> by saturation (@{thm [source] Hset_pi_iff}),
  and anything derivable from it is in \<open>H\<close> by @{thm [source] Hset_deduct}.\<close>

lemma Hset_forall_intro:
  assumes wB: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> body)"
      and inst: "\<And>a. cwff \<sigma> a \<Longrightarrow> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> body) \<^bold>\<cdot> a \<in> Hset \<Phi>"
      and drv: "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> body} \<turnstile> S"
      and cS: "cwff \<o> S"
    shows "S \<in> Hset \<Phi>"
proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> body}"])
  show "finite {\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> body}" by simp
  show "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> body} \<subseteq> Hset \<Phi>"
    unfolding Forall_def using Hset_pi_iff[OF wB] inst by blast
  show "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> body} \<turnstile> S" by (rule drv)
  show "cwff \<o> S" by (rule cS)
qed

text \<open>Property f (functionality, BKK Definition 3.46) via the rule \<open>NK(f)\<close>: two functions
  that agree on every class are Leibniz-equal in \<open>H\<close>.\<close>

lemma cls_ext:
  assumes wg: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) g" and wh: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) h"
      and ag: "\<And>a. cwff \<sigma> a \<Longrightarrow> Ap (cls g) (cls a) = Ap (cls h) (cls a)"
    shows "cls g = cls h"
proof -
  have lcg: "lc g" and lch: "lc h" using wg wh
    by (auto intro: cwff_lc)
  let ?body = "g \<^bold>\<cdot> (Bnd 0) \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> h \<^bold>\<cdot> (Bnd 0)"
  have opnb: "?body\<^bold>\<langle>u\<^bold>\<rangle> = (g \<^bold>\<cdot> u \<^bold>\<doteq>\<^bsub>\<tau>\<^esub> h \<^bold>\<cdot> u)" for u using lcg lch
    by simp
  \<comment> \<open>the abstracted body is a closed well-formed predicate\<close>
  have wB: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)"
  proof -
    have "wff\<^bsub>\<o>\<^esub>(?body\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" for x unfolding opnb
      using cwff_wff[OF wg] cwff_wff[OF wh]
      by (auto intro: wff_App wff_Fre)
    hence "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)" by (rule wff_AbsI)
    moreover have "fvs (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) = {}"
      using cwff_closed[OF wg] cwff_closed[OF wh]
      by (simp add: Leib_def)
    ultimately show ?thesis by (simp add: cwff_def)
  qed
  \<comment> \<open>pointwise agreement puts every instance of the body in \<open>H\<close>\<close>
  have inst: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) \<^bold>\<cdot> a \<in> Hset \<Phi>" if a: "cwff \<sigma> a" for a
    by (smt (verit, ccfv_threshold) Ap_cls Hset_beta_iff ag
        cls_eq_iff cwff_App opnb that wB wg wh)
  \<comment> \<open>hence the \<open>\<Pi>\<close>-sentence is in \<open>H\<close>, and \<open>NK(f)\<close> yields the equation\<close>
  have "(g \<^bold>\<doteq>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> h) \<in> Hset \<Phi>"
  proof (rule Hset_forall_intro[OF wB inst])
    have "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body} \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body" by (auto intro: bprov.Hyp)
    thus "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body} \<turnstile> g \<^bold>\<doteq>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> h"
      using FuncE cwff_wff wg wh by blast
    show "cwff \<o> (g \<^bold>\<doteq>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> h)" by (rule cwff_LeibE[OF wg wh])
  qed
  thus ?thesis using cls_eq_iff[OF wg wh] by simp
qed

text \<open>The description condition of the term model (beyond BKK; cf.\ Andrews 1972): a class
that provably behaves as the singleton of \<open>a\<close> is mapped by \<open>Iota \<sigma>\<close> to the class of \<open>a\<close>.
Functional extensionality \<open>NK(f)\<close> reduces the pointwise hypothesis to a Leibniz equation
with the literal singleton \<open>(Leib \<sigma>) \<^bold>\<cdot> a\<close>, which the axiom \<open>NK(\<iota>)\<close> describes.\<close>

lemma cls_desc:
  assumes wf: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f" and wa: "cwff \<sigma> a"
      and sing: "\<And>b. cwff \<sigma> b \<Longrightarrow> (Ap (cls f) (cls b) = cls \<^bold>\<top>) = (cls b = cls a)"
    shows "cls ((Iota \<sigma>) \<^bold>\<cdot> f) = cls a"
proof -
  have lcf: "lc f" and lca: "lc a" using wf wa
    by (auto intro: cwff_lc)
  let ?body = "f \<^bold>\<cdot> (Bnd 0) \<^bold>\<doteq>\<^bsub>\<o>\<^esub> ((Leib \<sigma>) \<^bold>\<cdot> a) \<^bold>\<cdot> (Bnd 0)"
  have opnb: "?body\<^bold>\<langle>u\<^bold>\<rangle> = (f \<^bold>\<cdot> u \<^bold>\<doteq>\<^bsub>\<o>\<^esub> ((Leib \<sigma>) \<^bold>\<cdot> a) \<^bold>\<cdot> u)" for u
    using lcf lca by simp
  have wB: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)"
  proof -
    have "wff\<^bsub>\<o>\<^esub>(?body\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" for x unfolding opnb
      using cwff_wff[OF wf] cwff_wff[OF wa]
      by (auto intro: wff_App wff_Fre)
    hence "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body)" by (rule wff_AbsI)
    moreover have "fvs (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) = {}" using cwff_def local.wf wa
      by auto
    ultimately show ?thesis by (simp add: cwff_def)
  qed
  \<comment> \<open>the pointwise singleton facts land in \<open>H\<close>\<close>
  have inst: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?body) \<^bold>\<cdot> b \<in> Hset \<Phi>" if b: "cwff \<sigma> b" for b
    by (metis (no_types, opaque_lifting) Ap_cls Hset_beta_iff Hset_iff_eq cls_TrueB_iff
              cls_eq_iff cwff_App cwff_Leib local.wf opnb sing that wB wa)
  \<comment> \<open>\<open>NK(f)\<close> reduces to the literal singleton, \<open>NK(\<iota>)\<close> describes it\<close>
  have "(((Iota \<sigma>) \<^bold>\<cdot> f) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> a) \<in> Hset \<Phi>"
  proof (rule Hset_forall_intro[OF wB inst])
    let ?F = "{\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body}"
    have fpF: "freep ?F" by (rule freep_finite) simp
    have PiD: "?F \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ?body"
      by (auto intro: bprov.Hyp)
    show "?F \<turnstile> (Iota \<sigma>) \<^bold>\<cdot> f \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> a"
      by (rule leib_trans[OF
        leib_cong2[OF bprov.FuncE[OF PiD cwff_wff[OF wf] 
                cwff_wff[OF cwff_App[OF cwff_Leib wa]]] fpF
                    cwff_wff[OF wf] cwff_wff[OF cwff_App[OF
                    cwff_Leib wa]] 
              wff_Iota] bprov.Desc[OF cwff_wff[OF wa]] fpF
                  wff_App[OF wff_Iota cwff_wff[OF wf]] 
            wff_App[OF wff_Iota cwff_wff[OF cwff_App[OF cwff_Leib
                wa]]] cwff_wff[OF wa]])
    show "cwff \<o> ((Iota \<sigma>) \<^bold>\<cdot> f \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> a)" 
      by (metis wa cwff_App local.wf cwff_Leib cwff_Iota)
  qed
  thus ?thesis
    using cls_eq_iff[OF cwff_App[OF cwff_Iota wf] wa] by simp
qed

text \<open>Primitive equality in \<open>H\<close> (BKK Remark 7.9): reflexivity is \<open>\<nabla>\<^bsub>=\<^sub>r\<^esub>\<close> via \<open>NK(=\<^sub>r)\<close>, and
primitive and Leibniz equality coincide in \<open>H\<close> --- \<open>\<rightarrow>\<close> via \<open>NK(=\<^sub>l)\<close> (\<open>\<nabla>\<^bsub>=\<^sub>\<doteq>\<^esub>\<close>), \<open>\<leftarrow>\<close> by
Leibniz substitution into \<open>\<lambda>x. a \<^bold>=\<^bsub>\<sigma>\<^esub> x\<close> from reflexivity.\<close>

lemma Hset_peq_iff:
  assumes wa: "cwff \<sigma> a" and wb: "cwff \<sigma> b"
    shows "(a \<^bold>=\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi> \<longleftrightarrow> (a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>"
proof
  assume p: "(a \<^bold>=\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>" show "(a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>"
  proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{a \<^bold>=\<^bsub>\<sigma>\<^esub> b}"])
    show "finite {a \<^bold>=\<^bsub>\<sigma>\<^esub> b}" by simp
    show "{a \<^bold>=\<^bsub>\<sigma>\<^esub> b} \<subseteq> Hset \<Phi>" using p by simp
    show "{a \<^bold>=\<^bsub>\<sigma>\<^esub> b} \<turnstile> a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b"
      by (auto intro: bprov.EqL bprov.Hyp)
    show "cwff \<o> (a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b)" by (rule cwff_LeibE[OF wa wb])
  qed
next
  assume l: "(a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>" show "(a \<^bold>=\<^bsub>\<sigma>\<^esub> b) \<in> Hset \<Phi>"
  proof (rule Hset_deduct[OF con\<Phi> fp\<Phi>, of "{a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b}"])
    show "finite {a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b}" by simp
    show "{a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b} \<subseteq> Hset \<Phi>" using l by simp
    show "{a \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> b} \<turnstile> a \<^bold>=\<^bsub>\<sigma>\<^esub> b"
      by (rule leib_to_peq[OF _ _ cwff_wff[OF wa] cwff_wff[OF wb]])
         (auto intro: bprov.Hyp freep_finite)
    show "cwff \<o> (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using cwff_wff[OF wa] cwff_wff[OF wb] cwff_closed[OF wa] cwff_closed[OF wb]
      by (auto simp: cwff_def)
  qed
qed

end

subsubsection \<open>Model existence (BKK Lemma 7.5 / Theorem 7.6)\<close>

text \<open>The Hintikka set induces a term evaluation: the class map \<open>cls\<close> together with the term-model
  domains and application satisfies every @{locale valuation} condition.  Via the bridge
  \<open>valuation \<subseteq> bkk_model\<close> of Section 2, every \<open>NK\<close>-consistent set of sentences therefore
  has a model in the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> --- BKK's model-existence theorem.\<close>

sublocale hintikka_model \<subseteq> V: valuation Dm Ap cls
proof
  show "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> cwff \<sigma> a \<Longrightarrow> Ap (cls (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) (cls a) = cls (b\<^bold>\<langle>a\<^bold>\<rangle>)"
    for \<sigma> \<tau> b a by (metis (no_types, lifting) Ap_cls Hset_beta cls_eq_iff cwff_App cwff_opn)
  show "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) g \<Longrightarrow> cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) h \<Longrightarrow> (\<And>a. cwff \<sigma> a
      \<Longrightarrow> Ap (cls g) (cls a) = Ap (cls h) (cls a)) \<Longrightarrow> cls g = cls h"
    for \<sigma> \<tau> g h by (rule cls_ext)
  show "cwff \<sigma> a \<Longrightarrow> cwff \<sigma> b \<Longrightarrow> (Ap (Ap (cls (Eq \<sigma>)) (cls a)) (cls b)
      = cls \<^bold>\<top>) = (cls a = cls b)" for \<sigma> a b
  proof -
    assume wa: "cwff \<sigma> a" and wb: "cwff \<sigma> b"
    have 2: "Ap (cls ((Eq \<sigma>) \<^bold>\<cdot> a)) (cls b) = cls (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using Ap_cls[OF cwff_App[OF cwff_Eq wa] wb] by simp
    have wab: "cwff \<o> (a \<^bold>=\<^bsub>\<sigma>\<^esub> b)"
      using cwff_App[OF cwff_App[OF cwff_Eq wa] wb] by simp
    show "(Ap (Ap (cls (Eq \<sigma>)) (cls a)) (cls b) = cls \<^bold>\<top>) = (cls a = cls b)"
      using Ap_cls[OF cwff_Eq wa] 2 cls_TrueB_iff[OF wab]
            Hset_peq_iff[OF wa wb] cls_eq_iff[OF wa wb] by simp
  qed
qed(auto simp: Ap_cls Dm_def cls_type TF cls_desc cls_pi cls_dis cls_neg cls_bool)

subsubsection \<open>The truth lemma\<close>

context hintikka_model
begin

text \<open>THE TRUTH LEMMA: the satisfaction claim of BKK Theorem 6.33 (the underlying Hintikka
  properties are BKK Lemma 6.21).  A sentence denotes its own class --- under @{emph \<open>any\<close>}
  assignment, since a closed formula ignores it.  It denotes the truth value \<open>cls \<^bold>\<top>\<close> of the
  term model exactly when it belongs to \<open>H\<close>.\<close>

theorem truth_lemma:
  "cwff \<o> \<phi> \<Longrightarrow> V.Ev \<xi> \<phi> = cls \<^bold>\<top> \<longleftrightarrow> \<phi> \<in> Hset \<Phi>"
  using cls_TrueB_iff msub_closed cwff_closed V.Ev_def by metis

end

subsubsection \<open>Model existence, packaged: the term model\<close>

text \<open>The construction, packaged once: every consistent parameter-rich set \<open>\<Phi>\<close> of sentences
  has a \<open>\<Sigma>\<close>-Henkin model --- the Hintikka term model, whose domains are \<open>\<sim>\<close>-classes of
  closed wffs --- satisfying every member of \<open>\<Phi>\<close> (the model-existence theorem, BKK
  Theorem 7.6).  The total domain injects into the term type, so over a countable signature
  it is countable.  The refuting countermodel, the completeness theorem and the
  single-sentence model-existence form are all instances.\<close>

theorem term_model_sat:
  fixes \<Phi> :: "'p::infinite tm set"
  assumes con: "con \<Phi>" and fp: "richp \<Phi>" and sen: "\<And>B. B \<in> \<Phi> \<Longrightarrow> cwff \<o> B"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
  where "bkk_model Dm Ap Ee vl" "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "\<forall>B\<in>\<Phi>. vl (Ee \<xi> B)"
proof -
  interpret H: hintikka_model \<Phi> by unfold_locales (rule con fp)+
  define \<xi> :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm set" where
    "\<xi> \<equiv> \<lambda>n \<tau>. H.cls (undefined\<^sup>p\<^bsub>\<tau>\<^esub>)"
  have r: "H.V.vresp \<xi>"
    by (auto simp: \<xi>_def H.V.vresp_def intro: H.Dm_cls cwff_Par)
  have ra: "app_struct.asg H.Dm \<xi>" using r
    by (simp add: H.V.bkkA.asg_def H.V.vresp_def)
  have bm: "bkk_model H.Dm H.Ap H.V.Ev (\<lambda>a. a = H.cls \<^bold>\<top>)"
    by intro_locales
  \<comment> \<open>the term model satisfies every member of \<open>\<Phi>\<close> by the truth lemma\<close>
  have sat: "\<forall>B\<in>\<Phi>. H.V.Ev \<xi> B = H.cls \<^bold>\<top>"
    using H.truth_lemma sen Phi_sub_Hset[of \<Phi>]
    by (auto simp: cwff_def)
  \<comment> \<open>the total domain injects into the term type: choose a representative of each class\<close>
  have "{x. \<exists>\<tau>. H.Dm \<tau> x} \<subseteq> H.cls ` UNIV" by (auto simp: H.Dm_def)
  hence inj: "inj_on (inv_into UNIV H.cls) {x. \<exists>\<tau>. H.Dm \<tau> x}"
    by (rule inj_on_inv_into)
  show ?thesis by (rule that[OF bm inj ra]) (use sat in auto)
qed

text \<open>The refuting instance: if \<open>A\<close> is not derivable @{emph \<open>from\<close>} a parameter-rich set \<open>\<Phi>\<close>
  of closed sentences, the term model of \<open>{\<^bold>\<not>A} \<union> \<Phi>\<close> satisfies every hypothesis yet refutes \<open>A\<close> ---
  the abstract negation law @{thm [source] sigma_model.sat_Neg} turns satisfaction of
  \<open>\<^bold>\<not>A\<close> into refutation of \<open>A\<close>.\<close>

lemma refuting_term_model_hyps:
  fixes \<Phi> :: "'p::infinite tm set" and A :: "'p tm"
  assumes c: "cwff \<o> A" and fp: "richp \<Phi>" and sen: "\<And>B. B \<in> \<Phi> \<Longrightarrow> cwff \<o> B"
      and nd: "\<not> \<Phi> \<turnstile> A"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
  where "bkk_model Dm Ap Ee vl" "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "\<forall>B\<in>\<Phi>. vl (Ee \<xi> B)" "\<not> vl (Ee \<xi> A)"
proof -
  note wA = cwff_wff[OF c]
  let ?\<Psi> = "insert (\<^bold>\<not> A) \<Phi>"
  have con\<Psi>: "con ?\<Psi>" using bprov.simps con_def nd wA by fastforce
  have fp\<Psi>: "richp ?\<Psi>" by (rule richp_add[OF fp])
  have cN: "cwff \<o> (\<^bold>\<not> A)" using c by (auto simp: cwff_def intro!: wff_Not)
  have sen\<Psi>: "\<And>B. B \<in> ?\<Psi> \<Longrightarrow> cwff \<o> B" using sen cN by auto
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where bm: "bkk_model Dm Ap Ee vl" and inj: "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>" and sat: "\<forall>B\<in>?\<Psi>. vl (Ee \<xi> B)"
    using term_model_sat[OF con\<Psi> fp\<Psi> sen\<Psi>] .
  interpret M: bkk_model Dm Ap Ee vl by (rule bm)
  have ref: "\<not> vl (Ee \<xi> A)" using sat M.sat_Neg[OF wA xi] by auto
  show ?thesis by (rule that[OF bm inj xi]) (use sat ref in auto)
qed

text \<open>The positive counterpart: the model-existence half of Henkin completeness.  From the
  @{emph \<open>consistency\<close>} of a single sentence \<open>A\<close> one obtains a @{emph \<open>countable\<close>} \<open>\<Sigma>\<close>-Henkin
  model (the term model) that @{emph \<open>satisfies\<close>} \<open>A\<close>.  This holds for @{emph \<open>any\<close>} consistent
  sentence --- an axiom of infinity included --- and stays entirely within plain HOL: the
  carrier is the type \<^typ>\<open>'p tm set\<close> of term classes, with the total domain --- the
  \<open>\<sim>\<close>-classes of closed wffs --- countable, and with no set-theoretic
  universe.  A stronger meta-theory can thus be needed only to establish the consistency
  premise (for an axiom without finite models), never for the model construction.\<close>

theorem countable_henkin_sat:
  fixes A :: "'p::{countable,infinite} tm"
  assumes cA: "cwff \<o> A" and con: "con {A}"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" and vl \<xi>
  where "bkk_model Dm Ap Ee vl" "countable {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "vl (Ee \<xi> A)"
proof -
  have fp: "richp {A}"
    unfolding richp_iff_freep by (intro freep_finite) simp
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where M: "bkk_model Dm Ap Ee vl" and inj: "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>" and sat: "\<forall>B\<in>{A}. vl (Ee \<xi> B)"
    by (rule term_model_sat[OF con fp]) (use cA in auto)
  have "inj_on (to_nat \<circ> rep) {x. \<exists>\<tau>. Dm \<tau> x}"
  proof (rule comp_inj_on[OF inj])
    show "inj_on to_nat (rep ` {x. \<exists>\<tau>. Dm \<tau> x})"
      by (rule inj_on_subset[OF inj_to_nat]) simp
  qed
  hence cnt: "countable {x. \<exists>\<tau>. Dm \<tau> x}"
    unfolding countable_def by blast
  show ?thesis by (rule that[OF M cnt xi]) (use sat in auto)
qed

subsubsection \<open>Completeness (BKK Corollary 7.7)\<close>

text \<open>\<open>NK\<^sub>\<beta>\<^sub>f\<^sub>b\<close> with \<open>NK(\<iota>)\<close> is complete for the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> of \<open>\<Sigma>\<close>-models with
  description (the description-enriched \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close>, cf.\ Andrews 1972): a sentence that is
  valid in every such model of a sufficiently \<open>\<Sigma>\<close>-pure set of
  sentences \<open>\<Phi>\<close> (it suffices to assume validity over the models carried by \<open>'p tm set\<close> --- in
  particular the term model) is derivable from \<open>\<Phi>\<close>.  Like BKK, who allow signatures of any
  infinite cardinality \<open>\<aleph>\<^sub>s\<close> (BKK Remark 3.16), we admit an arbitrary infinite type of
  parameter names; purity is then the parameter-rich \<open>richp\<close>, which over a countable
  signature is the familiar \<open>freep\<close> (BKK Definition 6.3).  The proof
  is by contraposition, BKK's argument: if \<open>\<Phi> \<turnstile> A\<close> fails, the refuting term model
  satisfies \<open>\<Phi>\<close> but refutes \<open>A\<close>, contradicting validity.\<close>

lemma fp0: "freep ({} :: 'p::{countable,infinite} tm set)"
  by (rule freep_finite[OF finite.emptyI])

theorem completeness:
  fixes \<Phi> :: "'p::infinite tm set" and A :: "'p tm"
  assumes c: "cwff \<o> A" and fp: "richp \<Phi>"
      and valid: "\<Phi> \<Turnstile>('p tm set) A"
      and sen: "\<And>B. B \<in> \<Phi> \<Longrightarrow> cwff \<o> B"
  shows "\<Phi> \<turnstile> A"
proof (rule ccontr)
  assume nd: "\<not> \<Phi> \<turnstile> A"
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where M: "bkk_model Dm Ap Ee vl" and "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>"
      and sat: "\<forall>B\<in>\<Phi>. vl (Ee \<xi> B)" and nA: "\<not> vl (Ee \<xi> A)"
    by (rule refuting_term_model_hyps[OF c fp sen nd])
  have satw: "\<forall>B\<in>\<Phi>. wff \<o> B \<and> vl (Ee \<xi> B)" using sat sen cwff_wff by blast
  have "vl (Ee \<xi> A)"
    using valid M xi satw unfolding bkk_consequence_def rel_truth_def by blast
  thus False using nA by simp
qed

text \<open>Soundness (BKK Theorem 7.3) and completeness (BKK Corollary 7.7) speak about the
  @{emph \<open>same\<close>} class of models, so together they characterise derivability @{emph \<open>from
  hypotheses\<close>} semantically: for a parameter-rich (\<open>richp\<close>; over a countable signature
  equivalently \<open>freep\<close>) set \<open>\<Phi>\<close> of closed sentences,
  \<open>\<Phi> \<turnstile> A\<close> holds exactly when \<open>\<Phi> \<Turnstile> A\<close> in the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> over the term carrier ---
  @{thm [source] completeness} gives \<open>\<Longleftarrow>\<close> (the model-existence direction) and
  @{thm [source] soundness_sat} gives \<open>\<Longrightarrow>\<close>; the packaged equivalences are stated in
  \<open>Main_Results\<close>.\<close>

subsection \<open>Completeness at every signature and carrier\<close>

text \<open>This part strengthens the completeness theorem from the term-model carrier to
  @{emph \<open>arbitrary\<close>} infinite value carriers, by an explicit model-embedding
  construction: every \<open>\<Sigma>\<close>-model of the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> whose total domain embeds
  injectively into a carrier \<open>'u\<close> has a satisfaction-equivalent copy on \<open>'u\<close>.  The
  term model's total domain injects into the term
  type, and \<open>|'p tm| \<le> |'p|\<close> over an infinite signature, so the term model embeds into
  every carrier at least as large as the signature --- over a countable signature, into
  every infinite carrier --- and validity there suffices for derivability.  Completeness is then
  extended further, to open formulas, to signatures with infinitely many parameters, and to
  derivation from hypotheses, and the development closes with the main theorems stated in
  self-contained notation.\<close>

subsubsection \<open>Model embedding: satisfaction is carrier-independent\<close>

text \<open>A \<open>\<Sigma>\<close>-model over a carrier \<open>'v\<close> whose total domain maps injectively into a
  carrier \<open>'u\<close> has a satisfaction-equivalent copy over \<open>'u\<close>; every refutation transfers.
  All model conditions are pointwise, so the transfer needs no induction on terms.\<close>

lemma bkk_model_embed:
  fixes Dm :: "ty \<Rightarrow> 'v \<Rightarrow> bool" and i :: "'v \<Rightarrow> 'u"
    and A :: "'p tm"
  assumes M: "bkk_model Dm Ap Ee vl"
     and inj: "inj_on i {x. \<exists>\<tau>. Dm \<tau> x}"
     and wA: "wff\<^bsub>\<o>\<^esub>(A)"
     and xi: "app_struct.asg Dm \<xi>" and nA: "\<not> vl (Ee \<xi> A)"
  obtains Dm' Ap' and Ee' :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl' \<xi>'
  where "bkk_model Dm' Ap' Ee' vl'" "app_struct.asg Dm' \<xi>'" "\<not> vl' (Ee' \<xi>' A)"
        "\<And>B. wff\<^bsub>\<o>\<^esub>(B) \<Longrightarrow> vl' (Ee' \<xi>' B) = vl (Ee \<xi> B)"
proof -
  interpret M: bkk_model Dm Ap Ee vl by (rule M)
  define D where "D = {x. \<exists>\<tau>. Dm \<tau> x}"
  have DmD: "Dm \<tau> x \<Longrightarrow> x \<in> D" for \<tau> x by (auto simp: D_def)
  have iinj: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> i x = i y \<Longrightarrow> x = y" for x y
    using inj by (auto simp: D_def inj_on_def)
  define bk where "bk = (\<lambda>u. SOME x. x \<in> D \<and> i x = u)"
  have cancel: "x \<in> D \<Longrightarrow> bk (i x) = x" for x
    unfolding bk_def by (rule some_equality) (auto intro: iinj)
  define Dm' where "Dm' = (\<lambda>\<tau> u. \<exists>x. Dm \<tau> x \<and> u = i x)"
  have Dm'I: "Dm \<tau> x \<Longrightarrow> Dm' \<tau> (i x)" for \<tau> x by (auto simp: Dm'_def)
  define pull :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 'v" where
    "pull \<equiv> \<lambda>\<xi>' n \<tau>. if \<exists>x. Dm \<tau> x \<and> i x = \<xi>' n \<tau>
                     then SOME x. Dm \<tau> x \<and> i x = \<xi>' n \<tau>
                     else SOME x. Dm \<tau> x"
  have pull_asg: "M.asg (pull \<xi>')" for \<xi>'
    unfolding M.asg_def pull_def
    by (auto intro: someI_ex M.as_nonempty someI2_ex)
  have pull_agree: "Dm' \<tau> (\<xi>' n \<tau>) \<Longrightarrow> i (pull \<xi>' n \<tau>) = \<xi>' n \<tau>"
    for \<xi>' n \<tau>
    unfolding pull_def Dm'_def by (auto intro: someI2_ex)
  have pull_push: "pull (\<lambda>n \<tau>. i (\<xi> n \<tau>)) = \<xi>"
  proof (intro ext)
    fix n \<tau>
    have d: "Dm \<tau> (\<xi> n \<tau>)" using xi by (simp add: M.asg_def)
    have "\<exists>x. Dm \<tau> x \<and> i x = i (\<xi> n \<tau>)" using d by blast
    moreover have "\<And>x. Dm \<tau> x \<Longrightarrow> i x = i (\<xi> n \<tau>) \<Longrightarrow> x = \<xi> n \<tau>"
      by (auto intro: iinj DmD d)
    ultimately show "pull (\<lambda>n \<tau>. i (\<xi> n \<tau>)) n \<tau> = \<xi> n \<tau>"
      unfolding pull_def by auto
  qed
  define Ap' where "Ap' \<equiv> \<lambda>u v. i (Ap (bk u) (bk v))"
  define Ee' where "Ee' \<equiv> \<lambda>\<xi>' B. i (Ee (pull \<xi>') B)"
  define vl' where "vl' \<equiv> \<lambda>u. vl (bk u)"
  have Ap'I: "x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> Ap' (i x) (i y) = i (Ap x y)" for x y
    by (simp add: Ap'_def cancel)
  have vl'I: "x \<in> D \<Longrightarrow> vl' (i x) \<longleftrightarrow> vl x" for x
    by (simp add: vl'_def cancel)
  have EeD: "wff\<^bsub>\<tau>\<^esub>(B) \<Longrightarrow> Ee (pull \<xi>') B \<in> D" for \<tau> B \<xi>'
    by (auto intro: DmD M.ev_type[OF _ pull_asg])
  have ApD: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f \<Longrightarrow> Dm \<alpha> a \<Longrightarrow> Ap f a \<in> D" for \<alpha> \<beta> f a
    by (auto intro: DmD M.as_appTy)
\<comment> \<open>the image is an applicative structure; interpreting it makes the specialised \<open>asg\<close> equation
    available\<close>
  have AS': "app_struct Dm' Ap'"
  proof (unfold_locales, goal_cases)
    case (1 \<alpha>) show ?case using M.as_nonempty Dm'I by (metis Dm'_def)
  next
    case (2 \<alpha> \<beta> f a) thus ?case
      by (auto simp: Dm'_def Ap'I DmD intro: M.as_appTy)
  qed
  interpret A': app_struct Dm' Ap' by (rule AS')
  \<comment> \<open>the image is a model: every condition transfers pointwise\<close>
  have BM: "bkk_model Dm' Ap' Ee' vl'"
  proof (unfold_locales, goal_cases)
    case 1 thus ?case
      by (auto simp: Ee'_def intro: Dm'I M.ev_type[OF _ pull_asg])
  next
    case (2 \<xi>' n \<sigma>)
    hence "Dm' \<sigma> (\<xi>' n \<sigma>)" by (simp add: A'.asg_def)
    thus ?case by (simp add: Ee'_def M.ev_var[OF pull_asg] pull_agree)
  next
    case 3 thus ?case
      by (simp add: Ee'_def M.ev_app[OF _ _ pull_asg]
          Ap'I[OF EeD EeD])
  next
    case (4 \<tau> B \<xi>' \<xi>'')
    have "pull \<xi>' n \<sigma> = pull \<xi>'' n \<sigma>" if "(n, \<sigma>) \<in> occ B" for n \<sigma>
      using 4(4)[OF that] by (auto simp: pull_def)
    thus ?case unfolding Ee'_def
      by (intro arg_cong[of _ _ i] M.ev_coin[OF 4(1) pull_asg pull_asg])
  next
    case 5 thus ?case
      by (simp add: Ee'_def M.ev_beta[OF _ pull_asg])
  next
    case (6 \<xi>' a')
    then obtain a where a: "Dm \<o> a" "a' = i a" by (auto simp: Dm'_def)
    have "vl' (Ap' (Ee' \<xi>' Neg) a') = vl (Ap (Ee (pull \<xi>') Neg) a)"
      by (simp add: a Ee'_def Ap'I[OF EeD[OF wff_Neg] DmD[OF a(1)]]
          vl'I[OF ApD[OF M.ev_type[OF wff_Neg pull_asg] a(1)]])
    thus ?case
      by (simp add: a M.vl_neg[OF pull_asg a(1)] vl'I[OF DmD[OF a(1)]])
  next
    case (7 \<xi>' a' b')
    then obtain a b where ab: "Dm \<o> a" "a' = i a" "Dm \<o> b" "b' = i b"
      by (auto simp: Dm'_def)
    have dsD: "Ap (Ee (pull \<xi>') Dis) a \<in> D"
      by (rule ApD[OF M.ev_type[OF wff_Dis pull_asg] ab(1)])
    have ds2: "Dm (\<o> \<^bold>\<Rightarrow> \<o>) (Ap (Ee (pull \<xi>') Dis) a)"
      by (rule M.as_appTy[OF M.ev_type[OF wff_Dis pull_asg] ab(1)])
    have "vl' (Ap' (Ap' (Ee' \<xi>' Dis) a') b')
            = vl (Ap (Ap (Ee (pull \<xi>') Dis) a) b)"
      by (simp add: ab Ee'_def Ap'I[OF EeD[OF wff_Dis] DmD[OF ab(1)]]
          Ap'I[OF dsD DmD[OF ab(3)]] vl'I[OF ApD[OF ds2 ab(3)]])
    thus ?case
      by (simp add: ab M.vl_dis[OF pull_asg ab(1) ab(3)]
          vl'I[OF DmD[OF ab(1)]] vl'I[OF DmD[OF ab(3)]])
  next
    case (8 \<xi>' \<sigma> f')
    then obtain f where f: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f" "f' = i f"
        by (auto simp: Dm'_def)
    have piD: "Dm ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>) (Ee (pull \<xi>') (Pi \<sigma>))"
      by (rule M.ev_type[OF wff_Pi pull_asg])
    have l: "vl' (Ap' (Ee' \<xi>' (Pi \<sigma>)) f')
               = vl (Ap (Ee (pull \<xi>') (Pi \<sigma>)) f)"
      by (simp add: f Ee'_def Ap'I[OF EeD[OF wff_Pi] DmD[OF f(1)]]
          vl'I[OF ApD[OF piD f(1)]])
    have r: "(\<forall>d'. Dm' \<sigma> d' \<longrightarrow> vl' (Ap' f' d'))
               = (\<forall>d. Dm \<sigma> d \<longrightarrow> vl (Ap f d))"
      by (auto simp: Dm'_def f Ap'I[OF DmD[OF f(1)] DmD]
          vl'I[OF ApD[OF f(1)]])
    show ?case using l r M.vl_pi[OF pull_asg f(1)] by simp
  next
    case (9 \<xi>' \<sigma> a' b')
    then obtain a b where ab: "Dm \<sigma> a" "a' = i a" "Dm \<sigma> b" "b' = i b"
      by (auto simp: Dm'_def)
    have eqD: "Ap (Ee (pull \<xi>') (Eq \<sigma>)) a \<in> D"
      by (rule ApD[OF M.ev_type[OF wff_Eq pull_asg] ab(1)])
    have eq2: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) (Ap (Ee (pull \<xi>') (Eq \<sigma>)) a)"
      by (rule M.as_appTy[OF M.ev_type[OF wff_Eq pull_asg] ab(1)])
    have "vl' (Ap' (Ap' (Ee' \<xi>' (Eq \<sigma>)) a') b')
            = vl (Ap (Ap (Ee (pull \<xi>') (Eq \<sigma>)) a) b)"
      by (simp add: ab Ee'_def Ap'I[OF EeD[OF wff_Eq] DmD[OF ab(1)]]
          Ap'I[OF eqD DmD[OF ab(3)]] vl'I[OF ApD[OF eq2 ab(3)]])
    thus ?case
      using M.vl_eq[OF pull_asg ab(1) ab(3)] iinj[OF DmD DmD] ab
      by (auto simp: DmD)
  next
    case (10 \<xi>' \<sigma> f' a')
    then obtain f a where fa: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f" "f' = i f" "Dm \<sigma> a" "a' = i a"
      by (auto simp: Dm'_def)
    have sing: "vl (Ap f b) \<longleftrightarrow> b = a" if b: "Dm \<sigma> b" for b
    proof -
      have "vl' (Ap' f' (i b)) \<longleftrightarrow> i b = a'"
        using 10(4)[OF Dm'I[OF b]] by simp
      thus ?thesis
        using b fa iinj[OF DmD DmD]
        by (auto simp: Ap'I[OF DmD[OF fa(1)] DmD[OF b]]
            vl'I[OF ApD[OF fa(1) b]] DmD)
    qed
    have "Ap (Ee (pull \<xi>') (Iota \<sigma>)) f = a"
      by (rule M.vl_iota[OF pull_asg fa(1) fa(3)]) (rule sing)
    thus ?case
      by (simp add: fa Ee'_def Ap'I[OF EeD[OF wff_Iota] DmD[OF fa(1)]])
  next
    case 11
    show ?case
      unfolding A'.functional_def
    proof (intro allI impI)
      fix \<alpha> \<beta> f' g'
      assume f': "Dm' (\<alpha> \<^bold>\<Rightarrow> \<beta>) f'" and g': "Dm' (\<alpha> \<^bold>\<Rightarrow> \<beta>) g'"
        and agree: "\<forall>a'. Dm' \<alpha> a' \<longrightarrow> Ap' f' a' = Ap' g' a'"
      obtain f g where fg: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f" "f' = i f" "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) g" "g' = i g"
        using f' g' by (auto simp: Dm'_def)
      have "Ap f a = Ap g a" if a: "Dm \<alpha> a" for a
      proof -
        have "i (Ap f a) = i (Ap g a)"
          using agree[THEN spec, of "i a"] Dm'I[OF a]
          by (simp add: fg Ap'I[OF DmD[OF fg(1)] DmD[OF a]]
              Ap'I[OF DmD[OF fg(3)] DmD[OF a]])
        thus ?thesis by (rule iinj[OF ApD ApD, OF fg(1) a fg(3) a])
      qed
      hence "f = g"
        using M.prop_f fg unfolding M.functional_def by blast
      thus "f' = g'" by (simp add: fg)
    qed
  next
    case (12 a' b')
    then obtain a b where ab: "Dm \<o> a" "a' = i a" "Dm \<o> b" "b' = i b"
      by (auto simp: Dm'_def)
    thus ?case
      using 12(3) M.prop_b[OF ab(1) ab(3)] vl'I[OF DmD[OF ab(1)]]
        vl'I[OF DmD[OF ab(3)]] by simp
  qed
  \<comment> \<open>the pushed assignment agrees with the original on every formula, so satisfaction
     (and the refutation of \<open>A\<close>) transfers\<close>
  define \<xi>' where "\<xi>' \<equiv> \<lambda>n \<tau>. i (\<xi> n \<tau>)"
  have asg': "app_struct.asg Dm' \<xi>'"
    using xi unfolding M.asg_def \<xi>'_def A'.asg_def
    by (auto intro: Dm'I)
  have push: "Ee' \<xi>' B = i (Ee \<xi> B)" for B by (simp add: Ee'_def \<xi>'_def pull_push)
  have agree: "vl' (Ee' \<xi>' B) = vl (Ee \<xi> B)" if "wff\<^bsub>\<o>\<^esub>(B)" for B
    by (simp add: push vl'I[OF DmD[OF M.ev_type[OF that xi]]])
  have nA': "\<not> vl' (Ee' \<xi>' A)" using nA agree[OF wA] by simp
  show ?thesis by (rule that[OF BM asg' nA' agree])
qed

subsubsection \<open>Completeness at every infinite carrier\<close>

text \<open>The strengthened form of BKK Corollary 7.7: consequence over the models of
  \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> at a value carrier @{emph \<open>at least as large as the signature\<close>} implies
  derivability.  The term carrier plays no special role: it only needs to embed into the
  given carrier --- its total domain injects into \<open>'p tm\<close>, and \<open>|'p tm| \<le> |'p| \<le> |'u|\<close> ---
  and the embedding preserves the satisfaction of \<open>\<Phi>\<close> and the refutation of \<open>A\<close>.  The
  cardinality link is stated as an injection \<open>emb :: 'p \<Rightarrow> 'u\<close>; over a countable signature
  every infinite carrier qualifies, which recovers the every-carrier form below.\<close>

theorem completeness_hyps_rich:
  fixes \<Phi> :: "'p::infinite tm set" and A :: "'p tm" and emb :: "'p \<Rightarrow> 'u"
  assumes emb: "inj emb" and c: "cwff \<o> A" and fp: "richp \<Phi>"
      and sen: "\<And>B. B \<in> \<Phi> \<Longrightarrow> cwff \<o> B"
      and valid: "\<Phi> \<Turnstile>('u) A"
  shows "\<Phi> \<turnstile> A"
proof (rule ccontr)
  assume nd: "\<not> \<Phi> \<turnstile> A"
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where M: "bkk_model Dm Ap Ee vl" and injr: "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>" and sat: "\<forall>B\<in>\<Phi>. vl (Ee \<xi> B)"
      and nA: "\<not> vl (Ee \<xi> A)"
    by (rule refuting_term_model_hyps[OF c fp sen nd])
  \<comment> \<open>embed the total domain into the carrier \<open>'u\<close>, via \<open>|'p tm| \<le> |'p| \<le> |'u|\<close>\<close>
  have "|UNIV :: 'p set| \<le>o |UNIV :: 'u set|"
    using card_of_ordLeq emb by auto
  hence "|UNIV :: 'p tm set| \<le>o |UNIV :: 'u set|"
    using card_of_tm ordLeq_transitive by blast
  then obtain g :: "'p tm \<Rightarrow> 'u" where g: "inj g"
    by (meson card_of_ordLeq)
  have inj: "inj_on (g \<circ> rep) {x. \<exists>\<tau>. Dm \<tau> x}"
    using injr g by (rule comp_inj_on[OF _ inj_on_subset]) auto
  obtain Dm' Ap' and Ee' :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl' \<xi>'
    where M': "bkk_model Dm' Ap' Ee' vl'" and asg': "app_struct.asg Dm' \<xi>'"
      and nA': "\<not> vl' (Ee' \<xi>' A)"
      and agree: "\<And>B. wff\<^bsub>\<o>\<^esub>(B) \<Longrightarrow> vl' (Ee' \<xi>' B) = vl (Ee \<xi> B)"
    by (rule bkk_model_embed[OF M inj cwff_wff[OF c] xi nA]) (rule that)
  \<comment> \<open>the image model still satisfies every hypothesis\<close>
  have satw': "\<forall>B\<in>\<Phi>. wff \<o> B \<and> vl' (Ee' \<xi>' B)"
  proof
    fix B assume B: "B \<in> \<Phi>"
    have wB: "wff \<o> B" using cwff_wff[OF sen[OF B]] .
    have "vl' (Ee' \<xi>' B) = vl (Ee \<xi> B)" by (rule agree[OF wB])
    moreover have "vl (Ee \<xi> B)" using sat B by blast
    ultimately show "wff \<o> B \<and> vl' (Ee' \<xi>' B)" using wB by simp
  qed
  \<comment> \<open>so validity of \<open>A\<close> forces it to hold, contradicting the refutation\<close>
  have "vl' (Ee' \<xi>' A)"
    using valid M' asg' satw'
    unfolding bkk_consequence_def rel_truth_def by blast
  thus False using nA' by simp
qed

subsubsection \<open>Signature transport\<close>

text \<open>On the semantic side, maps of parameter names need @{emph \<open>no\<close>} injectivity:
  any \<open>h :: 'p \<Rightarrow> 'q\<close> turns a model for \<open>'q\<close> into a model for \<open>'p\<close> by
  evaluating through \<open>prn h\<close> --- the value conditions \<open>vl\<^sub>\<not>, \<dots>, vl\<^sub>\<iota>\<close> only
  inspect \<open>Ee\<close> at the logical constants, which \<open>prn\<close> fixes.\<close>

text \<open>On the syntactic side, transport is by @{emph \<open>retraction\<close>}: any finite parameter
  support relocates injectively into \<open>\<nat>\<close> and back, \<open>g \<circ> h\<close> being the identity on the
  support, so \<open>prn g \<circ> prn h\<close> fixes the terms and contexts concerned.  This single
  construction drives every signature-transport argument below.\<close>

lemma nat_retract:
  fixes P :: "'p::infinite set"
  assumes fin: "finite P"
  shows "\<exists>(g :: nat \<Rightarrow> 'p) h. inj g \<and> (\<forall>p \<in> P. g (h p) = p)"
proof -
  obtain g0 :: "nat \<Rightarrow> 'p" where g0: "inj g0"
    using infinite_UNIV infinite_countable_subset by blast
  define S where "S = P \<union> range g0"
  have "inj_on (inv g0) (range g0)" by (rule inj_on_inv_into) simp
  hence rc: "countable (range g0)" by (rule countableI)
  have ri: "infinite (range g0)"
    using finite_imageD[of g0 UNIV] g0 infinite_UNIV_nat by auto
  have cS: "countable S" and iS: "infinite S"
    unfolding S_def using rc ri fin by (auto intro: countable_finite)
  define g where "g = from_nat_into S"
  have g: "inj g" and cover: "P \<subseteq> range g"
    using bij_betw_from_nat_into[OF cS iS]
    unfolding g_def bij_betw_def S_def by auto
  define h :: "'p \<Rightarrow> nat" where "h = (\<lambda>p. SOME n. g n = p)"
  have gh: "g (h p) = p" if "p \<in> P" for p
  proof -
    from cover that obtain n where n: "g n = p" by auto
    from someI[of "\<lambda>n. g n = p", OF n] show ?thesis by (simp add: h_def)
  qed
  show ?thesis using g gh by blast
qed

lemma prn_retract:
  assumes "\<And>p. p \<in> pars A \<Longrightarrow> g (h p) = p"
  shows "prn g (prn h A) = A"
  by (simp add: assms prn_cong prn_prn)

lemma prn_retract_set:
  assumes "\<And>p. p \<in> usedp \<Phi> \<Longrightarrow> g (h p) = p"
  shows "prn g ` prn h ` \<Phi> = \<Phi>"
proof -
  have "prn g (prn h B) = B" if "B \<in> \<Phi>" for B
    by (rule prn_retract) (use assms that in \<open>auto simp: usedp_def\<close>)
  thus ?thesis by (force simp: image_image)
qed

text \<open>Retraction along an @{emph \<open>arbitrary\<close>} injection into the same signature: an
  injective renaming \<open>g\<close> that undoes a given injection \<open>h\<close> on any finite support.  On the
  support, \<open>g\<close> inverts \<open>h\<close>; away from it, the two cofinite remainders have full
  cardinality, so they inject into each other without touching the support's values.\<close>

lemma inj_finite_retract:
  fixes h :: "'p::infinite \<Rightarrow> 'p"
  assumes injh: "inj h" and fin: "finite P"
  shows "\<exists>g :: 'p \<Rightarrow> 'p. inj g \<and> (\<forall>p \<in> P. g (h p) = p)"
proof -
  define Q where "Q = h ` P"
  have finQ: "finite Q" using fin by (simp add: Q_def)
  have "|UNIV :: 'p set| \<le>o |UNIV :: 'p set|"
    by (rule ordLeq_reflexive[OF card_of_Well_order])
  hence "|UNIV :: 'p set| \<le>o |UNIV - P :: 'p set|"
    using card_of_diff_finite[OF _ fin] by fastforce
  hence "|UNIV - Q :: 'p set| \<le>o |UNIV - P :: 'p set|"
    using card_of_mono1[of "UNIV - Q" UNIV] ordLeq_transitive by blast
  then obtain k :: "'p \<Rightarrow> 'p"
    where k: "inj_on k (UNIV - Q)" and rk: "k ` (UNIV - Q) \<subseteq> UNIV - P"
    using card_of_ordLeq[THEN iffD2] by blast
  define g where "g = (\<lambda>x. if x \<in> Q then inv_into P h x else k x)"
  have gh: "g (h p) = p" if "p \<in> P" for p
    using that inv_into_f_f[OF inj_on_subset[OF injh subset_UNIV]]
    by (auto simp: g_def Q_def)
  have "inj g"
  proof (rule injI)
    fix x y assume e: "g x = g y"
    have inP: "g z \<in> P" if "z \<in> Q" for z
      using that inv_into_into[of z h P] by (auto simp: g_def Q_def)
    have notP: "g z \<notin> P" if "z \<notin> Q" for z
      using that rk by (auto simp: g_def)
    consider "x \<in> Q" "y \<in> Q" | "x \<notin> Q" "y \<notin> Q" | "x \<in> Q" "y \<notin> Q" | "x \<notin> Q" "y \<in> Q"
      by blast
    thus "x = y"
    proof cases
      case 1 thus ?thesis
        using e inj_on_inv_into[of Q h P] by (auto simp: g_def Q_def inj_on_def)
    next
      case 2 thus ?thesis using e k by (auto simp: g_def inj_on_def)
    next
      case 3 thus ?thesis using e inP notP by metis
    next
      case 4 thus ?thesis using e inP notP by metis
    qed
  qed
  thus ?thesis using gh by blast
qed

lemma bkk_model_reduct:
  fixes Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'q tm \<Rightarrow> 'u" and h :: "'p \<Rightarrow> 'q"
  assumes "bkk_model Dm Ap Ee vl"
  shows "bkk_model Dm Ap (\<lambda>\<xi> t. Ee \<xi> (prn h t)) vl"
proof -
  interpret bkk_model Dm Ap Ee vl by (rule assms)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 3 thus ?case using ev_app by fastforce
    next case 4 thus ?case by (metis ev_coin prn_occ wff_prn)
    next case 5 thus ?case using ev_beta by blast
  qed(auto simp: vl_eq vl_pi vl_dis vl_neg vl_iota ev_var ev_type wff_prn prop_f prop_b)
qed

text \<open>Statement preserved verbatim from the published version of this entry (compatibility
  export); validity is the empty-context face of \<open>bkk_consequence_map\<close> below.\<close>

lemma bkk_valid_map:
  fixes h :: "'p \<Rightarrow> 'q"
  assumes v: "\<Turnstile>('u) (A :: 'p tm)"
    shows "\<Turnstile>('u) (prn h A :: 'q tm)"
  unfolding bkk_valid_def rel_truth_def
  by (metis bkk_model_reduct bkk_valid_def rel_truth_def v)

text \<open>Semantic consequence transports along an @{emph \<open>arbitrary\<close>} map of parameter names:
  the reduct of a \<open>'q\<close>-model is a \<open>'p\<close>-model, and it satisfies a hypothesis iff the original
  satisfies its renaming.  Validity is the empty-context face of the same fact.\<close>

lemma bkk_consequence_map:
  fixes h :: "'p \<Rightarrow> 'q"
  assumes v: "\<Phi> \<Turnstile>('u) (A :: 'p tm)"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
    shows "prn h ` \<Phi> \<Turnstile>('u) (prn h A :: 'q tm)"
  unfolding bkk_consequence_def rel_truth_def
proof (intro allI impI)
  fix Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'q tm \<Rightarrow> 'u" and vl :: "'u \<Rightarrow> bool" and \<xi>
  assume bm: "bkk_model Dm Ap Ee vl" and xi: "app_struct.asg Dm \<xi>"
     and sat: "\<forall>B'\<in>prn h ` \<Phi>. wff \<o> B' \<and> vl (Ee \<xi> B')"
  have bm': "bkk_model Dm Ap (\<lambda>\<xi> t. Ee \<xi> (prn h t)) vl" by (rule bkk_model_reduct[OF bm])
  have "\<forall>B\<in>\<Phi>. wff \<o> B \<and> vl (Ee \<xi> (prn h B))" using sat w\<Phi> by blast
  thus "vl (Ee \<xi> (prn h A))"
    using v bm' xi unfolding bkk_consequence_def rel_truth_def by blast
qed


subsubsection \<open>Arbitrary parameter-rich contexts: discharging the free-variable stock\<close>

text \<open>Finally the restriction to a @{emph \<open>finite\<close>} context is lifted altogether: an arbitrary
  parameter-rich context of open formulas is admissible.  With infinitely many typed free
  variables a per-variable induction cannot terminate, so the trade is made
  @{emph \<open>simultaneously\<close>}, by
  the closure \<open>vpar S \<pi>\<close> (Section 1, the parameter-valued instance of the simultaneous
  substitution @{const msub}) and its substitution-value law
  @{thm [source] sigma_eval.ev_vpar} (Section 2).  An injective \<open>\<pi>\<close> with pairwise distinct
  fresh parameters exists because the variables form a countable stock while \<open>richp \<Phi>\<close>
  supplies a reservoir as large as the signature: an injection of \<open>'p + \<nat>\<close> into it splits
  it, the \<open>\<nat>\<close>-half feeding \<open>\<pi>\<close> and the untouched \<open>'p\<close>-half keeping the closed image
  parameter-rich.  The law transports the
  consequence to the closed image, where
  @{thm [source] completeness_hyps_rich} applies.  Since every \<open>NK\<close>-derivation is
  finite (@{thm [source] bprov_finite}), the resulting derivation mentions only finitely many
  of the substituted parameters, and @{thm [source] bprov_pvar} inverts them one at a time
  (@{thm [source] pvar_vpar}); weakening restores the full context.\<close>

text \<open>Semantic consequence transports along the simultaneous closure, exactly as it does
  along parameter renamings (@{thm [source] bkk_consequence_map}): every assignment for the
  closed image induces, via the parameter values, an assignment for the originals.\<close>

lemma bkk_consequence_vpar:
  assumes v: "\<Phi> \<Turnstile>('u) (A :: 'p tm)"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)" and wA: "wff\<^bsub>\<o>\<^esub>(A)"
    shows "vpar UNIV \<pi> ` \<Phi> \<Turnstile>('u) vpar UNIV \<pi> A"
  unfolding bkk_consequence_def rel_truth_def
proof (intro allI impI)
  fix Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl :: "'u \<Rightarrow> bool" and \<xi>
  assume bm: "bkk_model Dm Ap Ee vl" and xi: "app_struct.asg Dm \<xi>"
     and sat: "\<forall>B'\<in>vpar UNIV \<pi> ` \<Phi>. wff \<o> B' \<and> vl (Ee \<xi> B')"
  interpret M: bkk_model Dm Ap Ee vl by (rule bm)
  have asg': "app_struct.asg Dm (\<lambda>n \<sigma>. Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>))"
    using M.ev_type[OF wff_Par xi] by (simp add: M.asg_def)
  have evA: "Ee \<xi> (vpar UNIV \<pi> A) = Ee (\<lambda>n \<sigma>. Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>)) A"
    using M.ev_vpar[where S = UNIV, OF wA xi] by simp
  have sat': "\<forall>B\<in>\<Phi>. wff \<o> B \<and> vl (Ee (\<lambda>n \<sigma>. Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>)) B)"
  proof
    fix B assume B: "B \<in> \<Phi>"
    have wB: "wff\<^bsub>\<o>\<^esub>(B)" using w\<Phi> B by blast
    have "Ee \<xi> (vpar UNIV \<pi> B) = Ee (\<lambda>n \<sigma>. Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>)) B"
      using M.ev_vpar[where S = UNIV, OF wB xi] by simp
    moreover have "vpar UNIV \<pi> B \<in> vpar UNIV \<pi> ` \<Phi>" using B by blast
    ultimately show "wff \<o> B \<and> vl (Ee (\<lambda>n \<sigma>. Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>)) B)"
      using sat wB by auto
  qed
  have "vl (Ee (\<lambda>n \<sigma>. Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>)) A)"
    by (rule v[unfolded bkk_consequence_def rel_truth_def, rule_format,
               OF bm asg' sat'[rule_format]])
  thus "vl (Ee \<xi> (vpar UNIV \<pi> A))" by (simp add: evA)
qed

text \<open>Syntactic inversion: a derivation of the closed image over a @{emph \<open>finite\<close>} stock of
  substituted variables is undone by @{thm [source] bprov_pvar}, one parameter at a time.\<close>

lemma bprov_vpar_invert:
  assumes inj: "\<And>n \<tau> x \<sigma>. \<pi> n \<tau> = \<pi> x \<sigma> \<Longrightarrow> n = x \<and> \<tau> = \<sigma>"
      and fr: "\<And>B n \<sigma>. B \<in> insert A \<Psi> \<Longrightarrow> \<pi> n \<sigma> \<notin> pars B"
  shows "finite W \<Longrightarrow> vpar W \<pi> ` \<Psi> \<turnstile> vpar W \<pi> A \<Longrightarrow> \<Psi> \<turnstile> A"
proof (induction rule: finite_induct)
  case empty
  have e: "vpar {} \<pi> t = t" for t by (simp add: vpar_id)
  show ?case using empty.prems unfolding e by (simp add: image_ident)
next
  case (insert p W)
  obtain x \<sigma> where p: "p = (x, \<sigma>)" by (cases p) auto
  have injx: "\<And>n \<tau>. \<pi> n \<tau> = \<pi> x \<sigma> \<Longrightarrow> n = x \<and> \<tau> = \<sigma>" using inj by blast
  have inv: "pvar (\<pi> x \<sigma>) \<sigma> x (vpar (insert p W) \<pi> B) = vpar W \<pi> B"
    if B: "B \<in> insert A \<Psi>" for B
  proof -
    have W: "insert p W - {(x, \<sigma>)} = W" using insert.hyps(2) p by auto
    have "pvar (\<pi> x \<sigma>) \<sigma> x (vpar (insert p W) \<pi> B) = vpar (insert p W - {(x, \<sigma>)}) \<pi> B"
      by (rule pvar_vpar[OF injx fr[OF B]])
    thus ?thesis unfolding W .
  qed
  have "pvar (\<pi> x \<sigma>) \<sigma> x ` (vpar (insert p W) \<pi> ` \<Psi>)
      \<turnstile> pvar (\<pi> x \<sigma>) \<sigma> x (vpar (insert p W) \<pi> A)"
    by (rule bprov_pvar[OF insert.prems])
  moreover have "pvar (\<pi> x \<sigma>) \<sigma> x ` (vpar (insert p W) \<pi> ` \<Psi>) = vpar W \<pi> ` \<Psi>"
    unfolding image_image by (rule image_cong[OF HOL.refl]) (rule inv, blast)
  moreover have "pvar (\<pi> x \<sigma>) \<sigma> x (vpar (insert p W) \<pi> A) = vpar W \<pi> A"
    by (rule inv) blast
  ultimately have "vpar W \<pi> ` \<Psi> \<turnstile> vpar W \<pi> A" by simp
  thus ?case by (rule insert.IH)
qed

text \<open>Hypothesis-relative completeness in full generality: an arbitrary parameter-rich
  context of open formulas, with no finiteness condition of any kind, at @{emph \<open>any\<close>}
  signature --- the carrier need only be at least as large as the signature.  The reserve
  is split in two by an injection \<open>j\<close> of \<open>'p + \<nat>\<close> into it: the \<open>\<nat>\<close>-half supplies the
  pairwise distinct fresh parameters that close the free variables, the \<open>'p\<close>-half is
  untouched by the closure and keeps the closed image parameter-rich.\<close>

theorem completeness_hyps_open_rich:
  fixes \<Phi> :: "'p::infinite tm set" and A :: "'p tm" and emb :: "'p \<Rightarrow> 'u"
  assumes emb: "inj emb" and wA: "wff\<^bsub>\<o>\<^esub>(A)" and fp: "richp \<Phi>"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and valid: "\<Phi> \<Turnstile>('u) A"
    shows "\<Phi> \<turnstile> A"
proof -
  \<comment> \<open>the reserve stays full-size after removing the parameters of \<open>A\<close>\<close>
  have rA: "|UNIV :: 'p set| \<le>o |- usedp \<Phi> - pars A|"
    by (rule card_of_diff_finite[OF fp[unfolded richp_def] finite_pars])
  \<comment> \<open>split it: an injection of \<open>'p + \<nat>\<close> into the reserve\<close>
  have "|(UNIV :: 'p set) <+> (UNIV :: nat set)| =o |UNIV :: 'p set|"
    using card_of_Plus_infinite[OF infinite_UNIV]
          infinite_iff_card_of_nat[of "UNIV :: 'p set"] infinite_UNIV by blast
  hence "|UNIV :: ('p + nat) set| \<le>o |- usedp \<Phi> - pars A|"
    using rA unfolding UNIV_Plus_UNIV
    by (meson ordIso_imp_ordLeq ordLeq_transitive)
  from card_of_ordLeq[THEN iffD2, OF this]
  obtain j :: "'p + nat \<Rightarrow> 'p" where injj: "inj j"
      and rj: "range j \<subseteq> - usedp \<Phi> - pars A"
    by blast
  define f :: "nat \<Rightarrow> 'p" where "f = (\<lambda>n. j (Inr n))"
  have injf: "inj f" using injj by (auto simp: f_def inj_on_def)
  have rf: "range f \<subseteq> - usedp \<Phi> - pars A" using rj by (auto simp: f_def)
  define \<pi> :: "nat \<Rightarrow> ty \<Rightarrow> 'p" where "\<pi> = (\<lambda>n \<sigma>. f (to_nat (n, \<sigma>)))"
  have inj\<pi>: "n = x \<and> \<tau> = \<sigma>" if "\<pi> n \<tau> = \<pi> x \<sigma>" for n \<tau> x \<sigma>
    using injD[OF injf that[unfolded \<pi>_def]] by simp
  have fresh\<Phi>: "\<pi> n \<sigma> \<notin> usedp \<Phi>" and freshA: "\<pi> n \<sigma> \<notin> pars A" for n \<sigma>
    using rf unfolding \<pi>_def by auto
  \<comment> \<open>the closed image is a parameter-rich context of sentences\<close>
  define \<Phi>c where "\<Phi>c = vpar UNIV \<pi> ` \<Phi>"
  have cA: "cwff \<o> (vpar UNIV \<pi> A)" by (rule cwff_vpar[OF wA])
  have cB: "cwff \<o> B'" if B': "B' \<in> \<Phi>c" for B'
  proof -
    obtain B where B: "B \<in> \<Phi>" and eq: "B' = vpar UNIV \<pi> B"
      using B' unfolding \<Phi>c_def by auto
    show ?thesis unfolding eq by (rule cwff_vpar[OF w\<Phi>[OF B]])
  qed
  have fpc: "richp \<Phi>c"
  proof -
    have sub: "range (\<lambda>p. j (Inl p)) \<subseteq> - usedp \<Phi>c"
    proof
      fix q assume "q \<in> range (\<lambda>p. j (Inl p))"
      then obtain p where q: "q = j (Inl p)" by auto
      have "q \<notin> pars B'" if B': "B' \<in> \<Phi>c" for B'
      proof
        assume qp: "q \<in> pars B'"
        obtain B where B: "B \<in> \<Phi>" and B'B: "B' = vpar UNIV \<pi> B"
          using B' unfolding \<Phi>c_def by auto
        have dis: "q \<in> pars B \<or> (\<exists>n \<sigma>'. q = \<pi> n \<sigma>')"
          using qp unfolding B'B by (rule pars_vpar)
        have nB: "q \<notin> pars B" using rj q B by (auto simp: usedp_def)
        have n\<pi>: "q \<noteq> \<pi> n \<sigma>'" for n \<sigma>'
          using injD[OF injj] q by (auto simp: \<pi>_def f_def)
        show False using dis nB n\<pi> by blast
      qed
      thus "q \<in> - usedp \<Phi>c" by (auto simp: usedp_def)
    qed
    have inj1: "inj (\<lambda>p. j (Inl p))" using injj by (auto simp: inj_on_def)
    have "|UNIV :: 'p set| \<le>o |- usedp \<Phi>c|"
      by (rule card_of_ordLeq[THEN iffD1]) (use sub inj1 in blast)
    thus ?thesis by (simp add: richp_def)
  qed
  \<comment> \<open>transport the consequence and apply the closed parameter-rich completeness\<close>
  have vc: "\<Phi>c \<Turnstile>('u) vpar UNIV \<pi> A"
    unfolding \<Phi>c_def by (rule bkk_consequence_vpar[OF valid w\<Phi> wA])
  have dc: "\<Phi>c \<turnstile> vpar UNIV \<pi> A"
    by (rule completeness_hyps_rich[OF emb cA fpc cB vc])
  \<comment> \<open>the derivation is finite, so it lives over a finite subcontext\<close>
  obtain \<Phi>\<^sub>0 where fin0: "finite \<Phi>\<^sub>0" and sub0: "\<Phi>\<^sub>0 \<subseteq> \<Phi>c" and d0: "\<Phi>\<^sub>0 \<turnstile> vpar UNIV \<pi> A"
    using bprov_finite[OF dc] by blast
  obtain \<Psi> where sub\<Psi>: "\<Psi> \<subseteq> \<Phi>" and fin\<Psi>: "finite \<Psi>" and im: "\<Phi>\<^sub>0 = vpar UNIV \<pi> ` \<Psi>"
    using finite_subset_image[OF fin0 sub0[unfolded \<Phi>c_def]] by blast
  \<comment> \<open>restrict the closure to the finitely many occurring variables and invert them\<close>
  define W where "W = occ A \<union> (\<Union>B\<in>\<Psi>. occ B)"
  have finW: "finite W" unfolding W_def using fin\<Psi> finite_occ by auto
  have "occ A \<subseteq> W" unfolding W_def by blast
  hence eqA: "vpar UNIV \<pi> A = vpar W \<pi> A" by (rule vpar_cong[symmetric])
  have eqB: "vpar UNIV \<pi> B = vpar W \<pi> B" if B: "B \<in> \<Psi>" for B
  proof -
    have "occ B \<subseteq> W" unfolding W_def using B by blast
    thus ?thesis by (rule vpar_cong[symmetric])
  qed
  have im\<Psi>: "vpar UNIV \<pi> ` \<Psi> = vpar W \<pi> ` \<Psi>" by (rule image_cong[OF HOL.refl eqB])
  have dW: "vpar W \<pi> ` \<Psi> \<turnstile> vpar W \<pi> A" using d0 unfolding im im\<Psi> eqA .
  have fr: "\<pi> n \<sigma> \<notin> pars B" if "B \<in> insert A \<Psi>" for B n \<sigma>
    using fresh\<Phi> freshA sub\<Psi> that by (auto simp: usedp_def)
  have "\<Psi> \<turnstile> A" by (rule bprov_vpar_invert[OF inj\<pi> fr finW dW])
  thus ?thesis by (rule bprov_weaken[OF _ sub\<Psi> richp_freep[OF fp]])
qed

text \<open>Over a countable signature every infinite carrier is admissible and \<open>richp\<close> is
  \<open>freep\<close>, so the classical statement follows; its closed, empty-context and
  finite-context faces are exported as one-line instances in the corollary ladder
  below.\<close>

theorem completeness_hyps_open_full:
  fixes \<Phi> :: "'p::{countable,infinite} tm set" and A :: "'p tm"
  assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" and fp: "freep \<Phi>"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and valid: "\<Phi> \<Turnstile>('u::infinite) A"
    shows "\<Phi> \<turnstile> A"
proof -
  obtain g :: "nat \<Rightarrow> 'u" where g: "inj g"
    using infinite_UNIV infinite_countable_subset by blast
  have emb: "inj (\<lambda>p :: 'p. g (to_nat p))"
    by (auto simp: inj_on_def dest!: injD[OF g])
  show ?thesis
    by (rule completeness_hyps_open_rich[OF emb wA iffD2[OF richp_iff_freep fp] w\<Phi> valid])
qed

subsubsection \<open>Hypothesis-relative completeness without purity\<close>

text \<open>For the hypothesis relation \<open>\<tturnstile>\<close> even the parameter reserve disappears: an
  @{emph \<open>arbitrary\<close>} context of open formulas is admitted, over any carrier at least as
  large as the signature.  The reserve is created rather than assumed --- the signature
  folds injectively into one half of itself (\<open>|'p + 'p| = |'p|\<close>), the untouched half makes
  the image context parameter-rich, and @{thm [source] completeness_hyps_open_rich}
  applies.  The resulting derivation is finite, so it retracts along the fold
  (@{thm [source] inj_finite_retract}) to a derivation from a finite part of the original
  context --- which is exactly \<open>\<Phi> \<tturnstile> A\<close>.  Semantic compactness of the Henkin consequence
  thus needs no ultraproducts: it falls out of this theorem together with soundness
  (\<open>Main_Results\<close>).\<close>

theorem completeness_fprov:
  fixes \<Phi> :: "'p::infinite tm set" and A :: "'p tm" and emb :: "'p \<Rightarrow> 'u"
  assumes emb: "inj emb" and wA: "wff\<^bsub>\<o>\<^esub>(A)"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and valid: "\<Phi> \<Turnstile>('u) A"
    shows "\<Phi> \<tturnstile> A"
proof -
  \<comment> \<open>fold the signature into one half of itself; the other half is an untouched reserve\<close>
  have "|(UNIV :: 'p set) <+> (UNIV :: 'p set)| =o |UNIV :: 'p set|"
    using card_of_Plus_infinite[OF infinite_UNIV
          ordLeq_reflexive[OF card_of_Well_order]] by blast
  hence "|UNIV :: ('p + 'p) set| \<le>o |UNIV :: 'p set|"
    by (metis UNIV_Plus_UNIV ordIso_imp_ordLeq)
  then obtain j :: "'p + 'p \<Rightarrow> 'p" where injj: "inj j"
    by (meson card_of_ordLeq)
  define h where "h = (\<lambda>p. j (Inl p))"
  have injh: "inj h" using injj by (auto simp: h_def inj_on_def)
  \<comment> \<open>the image context is parameter-rich: the \<open>Inr\<close>-half avoids every \<open>h\<close>-image\<close>
  define \<Phi>' where "\<Phi>' = prn h ` \<Phi>"
  have rich': "richp \<Phi>'"
  proof -
    have sub: "range (\<lambda>q. j (Inr q)) \<subseteq> - usedp \<Phi>'"
    proof
      fix x assume "x \<in> range (\<lambda>q. j (Inr q))"
      then obtain q where x: "x = j (Inr q)" by blast
      have "x \<notin> pars B'" if "B' \<in> \<Phi>'" for B'
      proof -
        have "B' \<in> prn h ` \<Phi>" using that by (simp add: \<Phi>'_def)
        then obtain B where "B' = prn h B" by blast
        hence "pars B' = h ` pars B" by (simp add: tm.set_map)
        thus ?thesis using x injD[OF injj] by (auto simp: h_def)
      qed
      thus "x \<in> - usedp \<Phi>'" by (auto simp: usedp_def)
    qed
    have inj1: "inj (\<lambda>q. j (Inr q))" using injj by (auto simp: inj_on_def)
    have "|UNIV :: 'p set| \<le>o |- usedp \<Phi>'|"
      by (rule card_of_ordLeq[THEN iffD1]) (use sub inj1 in blast)
    thus ?thesis by (simp add: richp_def)
  qed
  \<comment> \<open>transport validity and well-formedness along the fold\<close>
  have valid': "\<Phi>' \<Turnstile>('u) prn h A"
    unfolding \<Phi>'_def by (rule bkk_consequence_map[OF valid w\<Phi>])
  have wA': "wff\<^bsub>\<o>\<^esub>(prn h A)" by (rule wff_prn[OF wA])
  have w\<Phi>': "\<And>B'. B' \<in> \<Phi>' \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B')"
    by (auto simp: \<Phi>'_def intro: wff_prn w\<Phi>)
  \<comment> \<open>complete over the image and extract the finite kernel of the derivation\<close>
  have "\<Phi>' \<turnstile> prn h A"
    by (rule completeness_hyps_open_rich[OF emb wA' rich' w\<Phi>' valid'])
  then obtain \<Psi>0 where fin\<Psi>: "finite \<Psi>0" and sub\<Psi>: "\<Psi>0 \<subseteq> \<Phi>'"
      and d\<Psi>: "\<Psi>0 \<turnstile> prn h A"
    using bprov_finite by blast
  obtain \<Phi>\<^sub>0 where sub\<Phi>: "\<Phi>\<^sub>0 \<subseteq> \<Phi>" and fin\<Phi>: "finite \<Phi>\<^sub>0" and im: "\<Psi>0 = prn h ` \<Phi>\<^sub>0"
    using finite_subset_image[OF fin\<Psi> sub\<Psi>[unfolded \<Phi>'_def]] by blast
  \<comment> \<open>retract the finite derivation back along the fold\<close>
  define P where "P = pars A \<union> usedp \<Phi>\<^sub>0"
  have finP: "finite P"
    unfolding P_def usedp_def using fin\<Phi> finite_pars by auto
  obtain g :: "'p \<Rightarrow> 'p" where injg: "inj g" and gh: "\<forall>p \<in> P. g (h p) = p"
    using inj_finite_retract[OF injh finP] by blast
  have "prn g ` \<Psi>0 \<turnstile> prn g (prn h A)" by (rule bprov_rename[OF injg d\<Psi>])
  moreover have "prn g (prn h A) = A"
    by (rule prn_retract) (use gh in \<open>auto simp: P_def\<close>)
  moreover have "prn g ` \<Psi>0 = \<Phi>\<^sub>0"
    unfolding im by (rule prn_retract_set) (use gh in \<open>auto simp: P_def\<close>)
  ultimately have "\<Phi>\<^sub>0 \<turnstile> A" by simp
  thus ?thesis using fin\<Phi> sub\<Phi> by (rule fprovI[rotated 2])
qed

subsubsection \<open>The exported corollary ladder\<close>

text \<open>The completeness forms of the published version of this entry, each a one-line
  instance of the theorems above: over a countable signature every infinite carrier is
  admissible, open formulas need no closure --- the simultaneous variable-for-parameter
  trade subsumes the published version's per-occurrence induction --- and a finite context is
  automatically pure.\<close>

theorem completeness_open_at_any_carrier:
  fixes A :: "'p::{countable,infinite} tm"
  assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" and valid: "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
proof -
  have v0: "{} \<Turnstile>('u) A" using valid by (simp add: bkk_valid_def bkk_consequence_def)
  show ?thesis
    by (rule completeness_hyps_open_full[OF wA fp0 _ v0]) simp
qed

theorem completeness_open:
  fixes A :: "'p::{countable,infinite} tm"
  assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" and valid: "\<Turnstile>('p tm set) A"
  shows "\<turnstile> A"
proof -
  have emb: "inj (\<lambda>p :: 'p. {p\<^sup>p\<^bsub>\<iota>\<^esub>} :: 'p tm set)" by (simp add: inj_on_def)
  have v0: "{} \<Turnstile>('p tm set) A"
    using valid by (simp add: bkk_valid_def bkk_consequence_def)
  have "({} :: 'p tm set) \<tturnstile> A"
    by (rule completeness_fprov[OF emb wA _ v0]) simp
  thus ?thesis using fprov_finite_eq_bprov[of "{}" A] by simp
qed

text \<open>The published closed-formula equivalence, its statement verbatim; the open-formula
  strengthening is \<open>completeness_open\<close> above together with \<open>soundness_valid\<close>.\<close>

theorem derivable_iff_valid:
  fixes A :: "'p::{countable,infinite} tm"
  assumes "cwff \<o> A"
  shows "\<turnstile> A \<longleftrightarrow> \<Turnstile>('p tm set) A"
  using completeness_open[OF cwff_wff[OF assms]] soundness_valid by blast

lemma refuting_term_model:
  fixes A :: "'p::{countable,infinite} tm"
  assumes c: "cwff \<o> A" and nd: "\<not>\<turnstile> A"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set" and vl \<xi>
  where "bkk_model Dm Ap Ee vl" "countable {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "\<not> vl (Ee \<xi> A)"
proof -
  have fp: "richp ({} :: 'p tm set)"
    by (simp add: richp_iff_freep freep_finite)
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
      and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where M: "bkk_model Dm Ap Ee vl" and inj: "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>" and "\<forall>B\<in>({} :: 'p tm set). vl (Ee \<xi> B)"
      and nA: "\<not> vl (Ee \<xi> A)"
    by (rule refuting_term_model_hyps[OF c fp _ nd]) simp_all
  have "inj_on (to_nat \<circ> rep) {x. \<exists>\<tau>. Dm \<tau> x}"
  proof (rule comp_inj_on[OF inj])
    show "inj_on to_nat (rep ` {x. \<exists>\<tau>. Dm \<tau> x})"
      by (rule inj_on_subset[OF inj_to_nat]) simp
  qed
  hence cnt: "countable {x. \<exists>\<tau>. Dm \<tau> x}"
    unfolding countable_def by blast
  show ?thesis by (rule that[OF M cnt xi nA])
qed

theorem completeness_at_any_carrier:
  fixes A :: "'p::{countable,infinite} tm"
  assumes c: "cwff \<o> A" and valid: "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
  by (rule completeness_open_at_any_carrier[OF cwff_wff[OF c] valid])

theorem completeness_hyps_open_finite_countable:
  fixes \<Phi> :: "'p::{countable,infinite} tm set" and A :: "'p tm"
  assumes fin: "finite \<Phi>"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and wA: "wff\<^bsub>\<o>\<^esub>(A)"
      and valid: "\<Phi> \<Turnstile>('u::infinite) A"
    shows "\<Phi> \<turnstile> A"
  by (rule completeness_hyps_open_full[OF wA freep_finite[OF fin] w\<Phi> valid])

text \<open>The same at @{emph \<open>every\<close>} signature.  A finite context and its conclusion mention
  only finitely many parameters, so the problem relocates into a copy of \<open>\<nat>\<close> inside \<open>'p\<close>
  and \<open>bprov_rename\<close> transports the derivation back.  Countability of \<open>'p\<close> thus drops out,
  and only \<open>'p\<close> infinite remains.\<close>

theorem completeness_hyps_open_finite:
  fixes \<Phi> :: "'p::infinite tm set" and A :: "'p tm"
  assumes fin: "finite \<Phi>"
      and w\<Phi>: "\<And>B. B \<in> \<Phi> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)"
      and wA: "wff\<^bsub>\<o>\<^esub>(A)"
      and v: "\<Phi> \<Turnstile>('u::infinite) A"
    shows "\<Phi> \<turnstile> A"
proof -
  have finP: "finite (pars A \<union> usedp \<Phi>)" using fin by (simp add: usedp_def)
  obtain g :: "nat \<Rightarrow> 'p" and h where g: "inj g"
      and gh: "\<forall>p \<in> pars A \<union> usedp \<Phi>. g (h p) = p"
    using nat_retract[OF finP] by blast
  \<comment> \<open>into the countable subsignature\<close>
  have finN: "finite (prn h ` \<Phi>)" using fin by simp
  have wN\<Phi>: "wff\<^bsub>\<o>\<^esub>(B')" if "B' \<in> prn h ` \<Phi>" for B' :: "nat tm"
    using that w\<Phi> by (auto intro: wff_prn)
  have wN: "wff\<^bsub>\<o>\<^esub>(prn h A)" by (rule wff_prn[OF wA])
  have vN: "prn h ` \<Phi> \<Turnstile>('u) (prn h A :: nat tm)"
    by (rule bkk_consequence_map[OF v w\<Phi>])
  have dN: "prn h ` \<Phi> \<turnstile> (prn h A :: nat tm)"
    by (rule completeness_hyps_open_finite_countable[OF finN wN\<Phi> wN vN])
  \<comment> \<open>and back along \<open>g\<close>\<close>
  have "prn g ` (prn h ` \<Phi>) \<turnstile> prn g (prn h A)"
    by (rule bprov_rename[OF g dN])
  moreover have "prn g (prn h A) = A"
    by (rule prn_retract) (use gh in auto)
  moreover have "prn g ` prn h ` \<Phi> = \<Phi>"
    by (rule prn_retract_set) (use gh in auto)
  ultimately show ?thesis by simp
qed

text \<open>The empty-context instance: completeness for every signature with infinitely many
  parameters.  (With only finitely many parameters this route is barred: \<open>NK(\<Pi>I)\<close> consumes
  fresh eigen-parameters, and an injection \<open>\<nat> \<Rightarrow> 'p\<close> is exactly what supplies them.)\<close>

theorem completeness_at_any_signature:
  fixes A :: "'p::infinite tm"
  assumes wA: "wff\<^bsub>\<o>\<^esub>(A)" and v: "\<Turnstile>('u::infinite) A"
  shows "\<turnstile> A"
proof -
  have v0: "{} \<Turnstile>('u) A" using v by (simp add: bkk_valid_def bkk_consequence_def)
  show ?thesis
    by (rule completeness_hyps_open_finite[OF _ _ wA v0]) auto
qed

text \<open>The cardinality link between signature and carrier reflects a real boundary, not an
  artefact of the proof.  Over an uncountable signature, take as \<open>\<Phi>\<close> the diagram
  \<open>{c\<^sub>a \<noteq> c\<^sub>b}\<close> of uncountably many parameter constants, indexed so that a reserve of full
  size \<open>|'p|\<close> stays unused --- then \<open>\<Phi>\<close> is even parameter-rich.  \<open>\<Phi>\<close> is consistent: every
  finite part has a finite model, and derivability is finitary (this argument is informal
  here; its countable analogue is mechanised as \<open>con_Diag\<close> in \<open>NK_Infinity\<close>).  Yet over a
  @{emph \<open>countable\<close>} carrier \<open>'u\<close> no model satisfies \<open>\<Phi>\<close> --- the domains are subsets of
  \<open>'u\<close> and cannot keep uncountably many constants apart --- so \<open>\<Phi> \<Turnstile>('u) \<^bold>\<bottom>\<close> holds
  vacuously while \<open>\<Phi> \<turnstile> \<^bold>\<bottom>\<close> fails --- and since every finite part of \<open>\<Phi>\<close> is consistent,
  \<open>\<Phi> \<tturnstile> \<^bold>\<bottom>\<close> fails as well, so the counterexample applies to both hypothesis relations.
  For contexts of unbounded size the every-carrier
  form thus does not survive beyond countable signatures (for @{emph \<open>finite\<close>} contexts it
  does, @{thm [source] completeness_hyps_open_finite}): the carrier has to grow with the
  signature, as in the premise of @{thm [source] completeness_fprov} and
  @{thm [source] completeness_hyps_open_rich}; over a
  countable signature every infinite carrier qualifies, and the every-carrier statement
  (@{thm [source] completeness_hyps_open_full}) is recovered.  Whether the
  @{emph \<open>parameter-rich\<close>} reserve of the \<open>\<turnstile>\<close>-level forms could be weakened to the merely
  infinite reserve \<open>freep\<close> is not settled here; the two coincide over countable
  signatures, and for the hypothesis relation \<open>\<tturnstile>\<close> the question dissolves ---
  @{thm [source] completeness_fprov} assumes no purity at all.\<close>

end
