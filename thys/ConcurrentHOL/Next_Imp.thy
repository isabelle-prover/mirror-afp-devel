(*<*)
theory Next_Imp
imports
  Safety_Logic
begin

(*>*)
section\<open> ``Next step'' implication ala Abadi and Merz (and Lamport)\label{sec:abadi_merz} \<close>

text\<open>

As was apparently well-known in the mid-1990s (see, e.g.,
\<^citet>\<open>\<open>\S4\<close> in "XuCauCollette:1994"\<close> and
the references therein), Heyting implication is inadequate for a
general refinement story. (We show it is strong enough for a
relational assume/guarantee program logic; see
\S\ref{sec:abadi_plotkin}, \S\ref{sec:refinement-ag} and
\S\ref{sec:abadi_plotkin-parallel}. In our setting it fails to
generalize (at least) because the composition theorem for Heyting
implication (\S\ref{sec:abadi_plotkin}) is not termination sensitive.)

We therefore follow \<^citet>\<open>"AbadiLamport:1995"\<close> by developing a stronger implication
\<open>P \<^bold>\<longrightarrow>\<^sub>+ Q\<close> with the intuitive semantics that the consequent \<open>Q\<close> holds for at least one
step beyond the antecedent \<open>P\<close>. This is some kind of step indexing.

Here we sketch the relevant parts of \<^citet>\<open>"AbadiMerz:1995"
and "AbadiMerz:1996"\<close>, the latter of which has a fuller story,
including a formal account of the logical core of TLA and the
(implicit) observation that infinitary parallel composition poses no
problem for safety properties (see the comments under Theorem~5.2 and \S5.5).
\<^citet>\<open>"AbadiLamport:1995" and "XuCauCollette:1994" and
"CauCollette:1996"\<close> provide further background;
\<^citet>\<open>\<open>Appendix~B\<close> in
"JonssonTsay:1996"\<close> provide a more syntactic account.

Observations:
 \<^item> The hypothesis \<open>P\<close> is always a safety property here
 \<^item> TLA does not label transitions or have termination markers
 \<^item> Abadi/Cau/Collette/Lamport/Merz/Xu/... avoid naming this operator

Further references:
 \<^item> \<^citet>\<open>"Maier:2001"\<close>

\<close>

definition "next_imp" :: "'a::preorder set \<Rightarrow> 'a set \<Rightarrow> 'a set" where \<comment>\<open> \<^citet>\<open>\<open>\S2\<close> in "AbadiMerz:1995"\<close> \<close>
  "next_imp P Q = {\<sigma>. \<forall>\<sigma>'\<le>\<sigma>. (\<forall>\<sigma>''<\<sigma>'. \<sigma>'' \<in> P) \<longrightarrow> \<sigma>' \<in> Q}"

setup \<open>Sign.mandatory_path "next_imp"\<close>

lemma downwards_closed:
  assumes "P \<in> downwards.closed"
  shows "next_imp P Q \<in> downwards.closed"
unfolding next_imp_def by (blast elim: downwards.clE intro: order_trans)

lemma mono:
  assumes "x' \<le> x"
  assumes "y \<le> y'"
  shows "next_imp x y \<le> next_imp x' y'"
unfolding next_imp_def using assms by fast

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) X X'"
  assumes "st_ord F Y Y'"
  shows "st_ord F (next_imp X Y) (next_imp X' Y')"
using assms by (cases F) (auto simp: next_imp.mono)

lemma minimal:
  assumes "trace.T s xs v \<in> next_imp P Q"
  shows "trace.T s [] None \<in> Q"
using assms by (simp add: next_imp_def trace.less trace.less_eq_None)

lemma alt_def: \<comment>\<open> This definition coincides with \<^citet>\<open>"CauCollette:1996"\<close>, \<^citet>\<open>\<open>\S3.5.3\<close> in "AbadiLamport:1995"\<close> \<close>
  assumes "P \<in> downwards.closed"
  shows "next_imp P Q
      = {\<sigma>. trace.T (trace.init \<sigma>) [] None \<in> Q
          \<and> (\<forall>i. trace.take i \<sigma> \<in> P \<longrightarrow> trace.take (Suc i) \<sigma> \<in> Q)}" (is "?lhs = ?rhs")
proof(rule antisym)
  have "trace.take (Suc i) (trace.T s xs v) \<in> Q"
    if "trace.T s xs v \<in> ?lhs" and "trace.take i (trace.T s xs v) \<in> P"
   for s xs v i
    using that \<open>P \<in> downwards.closed\<close>
    by (force simp: next_imp_def trace.less_take_less_eq
              dest: spec[where x="trace.take (Suc i) (trace.T s xs v)"]
              elim: downwards.closed_in)
  then show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: trace.split_all next_imp.minimal)
next
  have "trace.T s xs v \<in> ?lhs"
    if minimal: "trace.T s [] None \<in> Q"
   and imp: "\<forall>i. trace.take i (trace.T s xs v) \<in> P \<longrightarrow> trace.take (Suc i) (trace.T s xs v) \<in> Q"
   for s xs v
  proof -
    have "trace.take i (trace.T s xs v) \<in> Q"
      if "\<forall>\<sigma>''<trace.take i (trace.T s xs v). \<sigma>'' \<in> P"
     for i
      using that
    proof(induct i)
      case (Suc i) with imp show ?case
        by (metis le_add2 order_le_less plus_1_eq_Suc trace.take.mono)
    qed (simp add: minimal)
    then show "trace.T s xs v \<in> ?lhs"
      by (clarsimp simp: next_imp_def trace.less_eq_take_def)
  qed
  then show "?rhs \<subseteq> ?lhs"
    by (clarsimp simp: trace.split_all next_imp.minimal)
qed

text\<open>

\<^citet>\<open>\<open>\S3.5.3\<close> in "AbadiLamport:1995"\<close> assert but do not prove the following connection with
Heyting implication. \<^citet>\<open>"AbadiMerz:1995"\<close> do. See also
\<^citet>\<open>\<open>\S5.3 and \S5.5\<close> in "AbadiMerz:1996"\<close>.

\<close>

lemma Abadi_Merz_Prop_1_subseteq: \<comment>\<open> First half of \<^citet>\<open>\<open>Proposition~1\<close> in "AbadiMerz:1995"\<close> \<close>
  fixes P :: "'a::preorder set"
  assumes "P \<in> downwards.closed"
  assumes wf: "wfP ((<) :: 'a relp)"
  shows "next_imp P Q \<subseteq> downwards.imp (downwards.imp Q P) Q" (is "?lhs \<subseteq> ?rhs")
proof(rule subsetI)
  fix \<sigma> assume "\<sigma> \<in> ?lhs" with wf show "\<sigma> \<in> ?rhs"
  proof(induct rule: wfp_induct_rule)
    case (less \<sigma>)
    have "\<tau> \<in> Q" if "\<tau> \<le> \<sigma>" and YYY: "\<forall>\<sigma>'\<le>\<tau>. \<sigma>' \<in> Q \<longrightarrow> \<sigma>' \<in> P" for \<tau>
    proof -
      have "\<rho> \<in> P" if "\<rho> < \<tau>" for \<rho>
      proof -
        from \<open>\<rho> < \<tau>\<close> \<open>\<tau> \<le> \<sigma>\<close> \<open>P \<in> downwards.closed\<close> have "\<rho> \<in> next_imp P Q"
          by (meson downwards.closed_in next_imp.downwards_closed less.prems less_imp_le)
        with \<open>\<rho> < \<tau>\<close> \<open>\<tau> \<le> \<sigma>\<close> have "\<rho> \<in> downwards.imp (downwards.imp Q P) Q"
          using less.hyps less_le_trans by blast
        moreover from \<open>\<rho> < \<tau>\<close>  YYY have "\<rho> \<in> downwards.imp Q P"
          by (simp add: downwards.imp_def) (meson order.trans order_less_imp_le)
        ultimately show ?thesis by (meson downwards.imp_mp')
      qed
      with that less.prems show ?thesis
        unfolding next_imp_def by blast
    qed
    then show ?case
      unfolding downwards.imp_def by blast
  qed
qed

text\<open>

The converse holds if either \<open>Q\<close> is a safety property or the order is partial.

\<close>

lemma Abadi_Merz_Prop1: \<comment>\<open> \<^citet>\<open>\<open>Proposition~1\<close> in "AbadiMerz:1995"\<close> and \<^citet>\<open>\<open>Proposition~5.2\<close> in "AbadiMerz:1996"\<close> \<close>
  fixes P :: "'a::preorder set"
  assumes "P \<in> downwards.closed"
  assumes "Q \<in> downwards.closed"
  assumes wf: "wfP ((<) :: 'a relp)"
  shows "next_imp P Q = downwards.imp (downwards.imp Q P) Q" (is "?lhs = ?rhs")
proof(rule antisym[OF next_imp.Abadi_Merz_Prop_1_subseteq[OF assms(1,3)]])
  from \<open>Q \<in> downwards.closed\<close> show "?rhs \<subseteq> ?lhs"
    by (auto simp: next_imp_def downwards.imp_def order.strict_iff_not dest: downwards.closed_in)
qed

lemma Abadi_Lamport_Lemma6: \<comment>\<open> \<^citet>\<open>\<open>Lemma~6\<close> in "AbadiLamport:1995"\<close> (no proof given there) \<close>
  fixes P :: "'a::order set"
  assumes "P \<in> downwards.closed"
  assumes wf: "wfP ((<) :: 'a relp)"
  shows "next_imp P Q = downwards.imp (downwards.imp Q P) Q" (is "?lhs = ?rhs")
proof(rule Set.equalityI[OF next_imp.Abadi_Merz_Prop_1_subseteq[OF assms]])
  show "?rhs \<subseteq> ?lhs"
    unfolding next_imp_def downwards.imp_def by (fastforce simp: le_less elim: downwards.closed_in)
qed

lemmas downwards_imp = next_imp.Abadi_Lamport_Lemma6[OF _ trace.wfP_less]

lemma boolean_implication_le:
  assumes "P \<in> downwards.closed"
  shows "next_imp P Q \<subseteq> P \<^bold>\<longrightarrow>\<^sub>B Q"
using downwards.closed_conv[OF assms]
by (fastforce simp: next_imp_def boolean_implication.member
             intro: order_less_imp_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lift_definition "next_imp" :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" (infixr "\<^bold>\<longrightarrow>\<^sub>+" 61) is
  "Next_Imp.next_imp"
by (simp add: next_imp.downwards_imp raw.spec.closed.downwards_closed raw.spec.closed.downwards_imp)

setup \<open>Sign.mandatory_path "next_imp"\<close>

lemma heyting: \<comment>\<open> fundamental \<close>
  shows "P \<^bold>\<longrightarrow>\<^sub>+ Q = (Q \<^bold>\<longrightarrow>\<^sub>H P) \<^bold>\<longrightarrow>\<^sub>H Q"
by transfer (simp add: next_imp.downwards_imp raw.spec.closed.downwards_closed)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma next_imp_le_conv:
  fixes P :: "('a, 's, 'v) spec"
  shows "\<lblot>\<sigma>\<rblot> \<le> P \<^bold>\<longrightarrow>\<^sub>+ Q \<longleftrightarrow> (\<forall>\<sigma>'\<le>\<sigma>. (\<forall>\<sigma>''<\<sigma>'. \<lblot>\<sigma>''\<rblot> \<le> P) \<longrightarrow> \<lblot>\<sigma>'\<rblot> \<le> Q)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (force simp: spec.next_imp.heyting spec.singleton.heyting_le_conv)
  note spec.singleton.transfer[transfer_rule]
  show "?rhs \<Longrightarrow> ?lhs"
  proof(transfer, unfold raw.singleton_def, rule raw.spec.least)
    show "{\<sigma>} \<subseteq> next_imp P Q"
      if "P \<in> raw.spec.closed"
     and "\<forall>\<sigma>'\<le>\<sigma>. (\<forall>\<sigma>''<\<sigma>'. raw.spec.cl {\<sigma>''} \<subseteq> P) \<longrightarrow> raw.spec.cl {\<sigma>'} \<subseteq> Q"
     for P Q :: "('a, 's, 'v) trace.t set" and \<sigma>
      using that by (auto simp: next_imp_def raw.spec.least_conv
                          dest: order.trans[OF raw.spec.expansive])
    show "next_imp P Q \<in> raw.spec.closed"
      if "P \<in> raw.spec.closed"
     and "Q \<in> raw.spec.closed"
     for P Q :: "('a, 's, 'v) trace.t set"
      using that
      by (simp add: next_imp.downwards_imp raw.spec.closed.downwards_closed raw.spec.closed.downwards_imp)
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "next_imp"\<close>

lemma mono:
  assumes "x' \<le> x"
  assumes "y \<le> y'"
  shows "x \<^bold>\<longrightarrow>\<^sub>+ y \<le> x' \<^bold>\<longrightarrow>\<^sub>+ y'"
by (simp add: assms heyting.mono spec.next_imp.heyting)

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) X X'"
  assumes "st_ord F Y Y'"
  shows "st_ord F (X \<^bold>\<longrightarrow>\<^sub>+ Y) (X' \<^bold>\<longrightarrow>\<^sub>+ Y')"
using assms by (cases F) (auto simp: spec.next_imp.mono)

lemma idempotentR:
  shows "P \<^bold>\<longrightarrow>\<^sub>+ (P \<^bold>\<longrightarrow>\<^sub>+ Q) = P \<^bold>\<longrightarrow>\<^sub>+ Q"
by (simp add: spec.next_imp.heyting heyting heyting.detachment(1) heyting.discharge(2) inf.absorb2
        flip: heyting.curry_conv)

lemma contains:
  assumes "X \<le> Q"
  shows "X \<le> P \<^bold>\<longrightarrow>\<^sub>+ Q"
by (simp add: assms spec.next_imp.heyting heyting.curry le_infI1)

interpretation closure: closure_complete_lattice_class "(\<^bold>\<longrightarrow>\<^sub>+) P" for P
by standard
   (metis (no_types, lifting) order.refl order.trans
                              spec.next_imp.idempotentR spec.next_imp.contains spec.next_imp.mono)

lemma InfR:
  shows "x \<^bold>\<longrightarrow>\<^sub>+ \<Sqinter>X = \<Sqinter> ((\<^bold>\<longrightarrow>\<^sub>+) x ` X)"
by transfer (auto simp: next_imp_def)

lemma SupR_not_empty:
  fixes P :: "(_, _, _) spec"
  assumes "X \<noteq> {}"
  shows "P \<^bold>\<longrightarrow>\<^sub>+ (\<Squnion>x\<in>X. Q x) = (\<Squnion>x\<in>X. P \<^bold>\<longrightarrow>\<^sub>+ Q x)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.singleton_le_extI
                      spec.next_imp.closure.Sup_cl_le[where X="Q ` X", simplified image_image]])
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
  proof(cases "\<lblot>\<sigma>\<rblot> \<le> P")
    case True with \<open>\<lblot>\<sigma>\<rblot> \<le> ?lhs\<close> show ?thesis
      by (fastforce simp: spec.singleton.next_imp_le_conv
                   intro: order.trans[OF spec.singleton.mono]
                   elim!: order_less_imp_le
                    dest: spec[where x=\<sigma>])
  next
    case False show ?thesis
    proof(cases "\<lblot>trace.init \<sigma>, [], None\<rblot> \<le> P")
      case True with \<open>\<not> \<lblot>\<sigma>\<rblot> \<le> P\<close>
      obtain j where *: "\<forall>\<sigma>''<trace.take (Suc j) \<sigma>. \<lblot>\<sigma>''\<rblot> \<le> P"
                 and **: "\<not> \<lblot>trace.take (Suc j) \<sigma>\<rblot> \<le> P"
        using ex_least_nat_less[where P="\<lambda>i. \<not>\<lblot>trace.take i \<sigma>\<rblot> \<le> P" and n="Suc (length (trace.rest \<sigma>))"]
        by (force dest: trace.less_take_less_eq
                  simp: less_Suc_eq_le order.trans[OF spec.singleton.mono]
             simp flip: trace.take.Ex_all)
      from \<open>\<lblot>\<sigma>\<rblot> \<le> ?lhs\<close> ** show ?thesis
      by (clarsimp simp: spec.singleton.next_imp_le_conv
                  dest!: spec[where x="trace.take (Suc j) \<sigma>"] rev_mp[OF *]
                  elim!: rev_bexI)
          (meson order.trans less_le_not_le spec.singleton.mono trace.less_eq_same_cases trace.less_eq_take)
    next
      case False with \<open>X \<noteq> {}\<close> \<open>\<lblot>\<sigma>\<rblot> \<le> ?lhs\<close> show ?thesis
        by (clarsimp simp: spec.singleton.next_imp_le_conv simp flip: ex_in_conv)
           (metis "trace.take.0" trace.less_eq_take_def trace.less_t_def trace.take.sel(1))
    qed
  qed
qed

lemma cont:
  shows "cont Sup (\<le>) Sup (\<le>) ((\<^bold>\<longrightarrow>\<^sub>+) P)"
by (rule contI) (simp add: spec.next_imp.SupR_not_empty[where Q=id, simplified])

lemma mcont:
  shows "mcont Sup (\<le>) Sup (\<le>) ((\<^bold>\<longrightarrow>\<^sub>+) P)"
by (simp add: monotoneI mcontI[OF _ spec.next_imp.cont])

lemmas mcont2mcont[cont_intro] = mcont2mcont[OF spec.next_imp.mcont, of luba orda Q P] for luba orda Q P

lemma botL:
  assumes "spec.idle \<le> P"
  shows "\<bottom> \<^bold>\<longrightarrow>\<^sub>+ P = \<top>"
by (simp add: assms spec.next_imp.heyting spec.eq_iff Heyting.heyting spec.heyting.non_triv)

lemma topL[simp]:
  shows "\<top> \<^bold>\<longrightarrow>\<^sub>+ P = P"
by (simp add: spec.next_imp.heyting)

lemmas topR[simp] = spec.next_imp.closure.cl_top

lemma refl:
  shows "P \<^bold>\<longrightarrow>\<^sub>+ P \<le> P"
by (simp add: spec.next_imp.heyting)

lemma heyting_le:
  shows "P \<^bold>\<longrightarrow>\<^sub>+ Q \<le> P \<^bold>\<longrightarrow>\<^sub>H Q"
by (simp add: spec.next_imp.heyting heyting.discard heyting.mono)

lemma discharge:
  shows "P \<sqinter> (P \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>+ R) = P \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>+ R)" (is "?thesis1 P Q")
    and "(P \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>+ R) \<sqinter> P = P \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>+ R)" (is ?thesis2)
    and "Q \<sqinter> (P \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>+ R) = Q \<sqinter> (P \<^bold>\<longrightarrow>\<^sub>+ R)" (is ?thesis3)
    and "(P \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>+ R) \<sqinter> Q = Q \<sqinter> (P \<^bold>\<longrightarrow>\<^sub>+ R)" (is ?thesis4)
proof -
  show "?thesis1 P Q" for P Q
    by (simp add: spec.next_imp.heyting heyting.infR heyting.curry_conv heyting.discard heyting.discharge)
  then show ?thesis2 by (rule inf_commute_conv)
  from \<open>?thesis1 Q P\<close> show ?thesis3 by (simp add: ac_simps)
  then show ?thesis4 by (rule inf_commute_conv)
qed

lemma detachment:
  shows "x \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>+ y) \<le> y"
    and "(x \<^bold>\<longrightarrow>\<^sub>+ y) \<sqinter> x \<le> y"
by (simp_all add: spec.next_imp.heyting heyting.discard heyting.discharge)

lemma infR:
  shows "P \<^bold>\<longrightarrow>\<^sub>+ Q \<sqinter> R = (P \<^bold>\<longrightarrow>\<^sub>+ Q) \<sqinter> (P \<^bold>\<longrightarrow>\<^sub>+ R)"
by (rule antisym[OF spec.next_imp.closure.cl_inf_le])
   (rule spec.singleton_le_extI; clarsimp simp: spec.singleton.next_imp_le_conv)

lemma supL_le:
  shows "x \<squnion> y \<^bold>\<longrightarrow>\<^sub>+ z \<le> (x \<^bold>\<longrightarrow>\<^sub>+ z) \<squnion> (y \<^bold>\<longrightarrow>\<^sub>+ z)"
by (simp add: le_supI1 spec.next_imp.mono)

lemma heytingL:
  shows "(P \<^bold>\<longrightarrow>\<^sub>H Q) \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>+ R) \<le> P \<^bold>\<longrightarrow>\<^sub>+ R"
by (simp add: spec.next_imp.heyting heyting ac_simps)
   (simp add: heyting.rev_trans heyting.discharge flip: inf.assoc)

lemma heytingR:
  shows "(P \<^bold>\<longrightarrow>\<^sub>+ Q) \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>H R) \<le> P \<^bold>\<longrightarrow>\<^sub>+ R"
by (simp add: spec.next_imp.heyting heyting ac_simps)
   (simp add: heyting.discharge heyting.trans heyting.uncurry flip: inf.assoc)

lemma heytingL_distrib:
  shows "P \<^bold>\<longrightarrow>\<^sub>H (Q \<^bold>\<longrightarrow>\<^sub>+ R) = (P \<sqinter> Q) \<^bold>\<longrightarrow>\<^sub>+ (P \<^bold>\<longrightarrow>\<^sub>H R)"
by (metis (no_types, opaque_lifting) heyting.curry_conv heyting.detachment(2) heyting.infR
                                     heyting.refl heyting.swap inf_top_left spec.next_imp.heyting)

lemma trans:
  shows "(P \<^bold>\<longrightarrow>\<^sub>+ Q) \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>+ R) \<le> P \<^bold>\<longrightarrow>\<^sub>+ R"
by (meson order.trans Heyting.heyting spec.next_imp.heytingL spec.next_imp.heyting_le)

lemma rev_trans:
  shows "(Q \<^bold>\<longrightarrow>\<^sub>+ R) \<sqinter> (P \<^bold>\<longrightarrow>\<^sub>+ Q) \<le> P \<^bold>\<longrightarrow>\<^sub>+ R"
by (simp add: inf.commute spec.next_imp.trans)

lemma
  assumes "x' \<le> x"
  shows discharge_leL: "x' \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>+ y) = x' \<sqinter> y" (is ?thesis1)
    and discharge_leR: "(x \<^bold>\<longrightarrow>\<^sub>+ y) \<sqinter> x' = y \<sqinter> x'" (is ?thesis2)
proof -
  from assms show ?thesis1
    by (metis inf.absorb_iff2 inf_top.right_neutral spec.next_imp.discharge(4) spec.next_imp.topL)
  then show ?thesis2 by (simp add: ac_simps)
qed

lemma invmap:
  shows "spec.invmap af sf vf (P \<^bold>\<longrightarrow>\<^sub>+ Q) = spec.invmap af sf vf P \<^bold>\<longrightarrow>\<^sub>+ spec.invmap af sf vf Q"
by (simp add: spec.next_imp.heyting spec.invmap.heyting)

lemma Abadi_Lamport_Lemma7:
  assumes "Q \<sqinter> R \<le> P"
  shows "P \<^bold>\<longrightarrow>\<^sub>+ Q \<le> R \<^bold>\<longrightarrow>\<^sub>+ Q"
by (simp add: assms spec.next_imp.heyting Heyting.heyting heyting.detachment(2) heyting.discharge(2))

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma "next_imp":
  shows "spec.term.none (P \<^bold>\<longrightarrow>\<^sub>+ Q) \<le> spec.term.all P \<^bold>\<longrightarrow>\<^sub>+ spec.term.none Q"
by (simp add: spec.next_imp.heyting order.trans[OF spec.term.none.heyting_le] spec.term.all.heyting)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma "next_imp":
  shows "spec.term.all (P \<^bold>\<longrightarrow>\<^sub>+ Q) = spec.term.all P \<^bold>\<longrightarrow>\<^sub>+ spec.term.all Q"
by (simp add: spec.next_imp.heyting)
   (metis spec.term.all.heyting spec.term.all_none spec.term.heyting_noneL_allR_mono spec.term.none_all)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma "next_imp":
  assumes "Q \<in> spec.term.closed _"
  shows "P \<^bold>\<longrightarrow>\<^sub>+ Q \<in> spec.term.closed _"
using assms
by (simp add: spec.next_imp.heyting spec.term.closed.heyting)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "pre"\<close>

lemma next_imp_eq_heyting:
  assumes "spec.idle \<le> R"
  shows "Q \<sqinter> spec.pre P \<^bold>\<longrightarrow>\<^sub>+ R = spec.pre P \<^bold>\<longrightarrow>\<^sub>H (Q \<^bold>\<longrightarrow>\<^sub>+ R)" (is "?lhs = ?rhs")
    and "spec.pre P \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>+ R = spec.pre P \<^bold>\<longrightarrow>\<^sub>H (Q \<^bold>\<longrightarrow>\<^sub>+ R)" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule antisym[OF _ spec.singleton_le_extI])
    show "?lhs \<le> ?rhs"
      by (simp add: heyting spec.next_imp.discharge)
    show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
      using assms that
      by (clarsimp simp: spec.singleton.next_imp_le_conv spec.singleton.heyting_le_conv
                         spec.singleton.le_conv)
         (metis order.refl append_self_conv2 spec.singleton.idle_le_conv spec.singleton_le_ext_conv
                trace.less(1) trace.less_eqE trace.steps'.simps(1) trace.t.sel(1))
  qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Compositionality ala Abadi and Merz (and Lamport) \label{sec:abadi_merz-compositionality} \<close>

text\<open>

The main theorem for this implication (\<^citet>\<open>\<open>Theorem~4\<close> in "AbadiMerz:1995"\<close> and
\<^citet>\<open>\<open>Corollary~5.1\<close> in "AbadiMerz:1996"\<close>)
shows how to do assumption/commitment proofs for TLA considered as an
algebraic logic. See also \<^citet>\<open>"CauCollette:1996"\<close>.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

lemma Abadi_Lamport_Lemma5:
  shows "(\<Sqinter>i\<in>I. P i \<^bold>\<longrightarrow>\<^sub>+ Q i) \<le> (\<Sqinter>i\<in>I. P i) \<^bold>\<longrightarrow>\<^sub>+ (\<Sqinter>i\<in>I. Q i)"
by (simp add: spec.next_imp.InfR INF_lower INF_superset_mono image_image spec.next_imp.mono)

lemma Abadi_Merz_Prop2_1:
  shows "(P \<^bold>\<longrightarrow>\<^sub>+ Q) \<sqinter> (P \<^bold>\<longrightarrow>\<^sub>+ (Q \<^bold>\<longrightarrow>\<^sub>H R)) \<le> P \<^bold>\<longrightarrow>\<^sub>+ R"
by (metis heyting.detachment(1) inf_sup_ord(2) spec.next_imp.infR)

lemma Abadi_Merz_Theorem3_5:
  shows "P \<^bold>\<longrightarrow>\<^sub>H (Q \<^bold>\<longrightarrow>\<^sub>H R) \<le> (R \<^bold>\<longrightarrow>\<^sub>+ Q) \<^bold>\<longrightarrow>\<^sub>H (P \<^bold>\<longrightarrow>\<^sub>+ Q)"
by (simp add: heyting order.trans[OF spec.next_imp.heytingL] spec.next_imp.Abadi_Lamport_Lemma7
        flip: heyting.curry_conv)

theorem Abadi_Merz_Theorem4:
  shows "(A \<sqinter> (\<Sqinter>i\<in>I. Cs i) \<^bold>\<longrightarrow>\<^sub>H (\<Sqinter>i\<in>I. As i))
       \<sqinter> (A \<^bold>\<longrightarrow>\<^sub>+ ((\<Sqinter>i\<in>I. Cs i) \<^bold>\<longrightarrow>\<^sub>H C))
       \<sqinter> (\<Sqinter>i\<in>I. As i \<^bold>\<longrightarrow>\<^sub>+ Cs i)
        \<le> A \<^bold>\<longrightarrow>\<^sub>+ C" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs \<le> A \<^bold>\<longrightarrow>\<^sub>H (\<Sqinter>i\<in>I. Cs i) \<^bold>\<longrightarrow>\<^sub>H (\<Sqinter>i\<in>I. As i)"
    by (simp add: heyting.curry_conv inf.coboundedI1)
  then have 2: "?lhs \<le> ((\<Sqinter>i\<in>I. As i) \<^bold>\<longrightarrow>\<^sub>+ (\<Sqinter>i\<in>I. Cs i)) \<^bold>\<longrightarrow>\<^sub>H (A \<^bold>\<longrightarrow>\<^sub>+ (\<Sqinter>i\<in>I. Cs i))"
    by (simp add: heyting.curry_conv inf.coboundedI1 spec.Abadi_Merz_Theorem3_5)
  have 3: "?lhs \<le> (\<Sqinter>i\<in>I. As i) \<^bold>\<longrightarrow>\<^sub>+ (\<Sqinter>i\<in>I. Cs i)"
    using spec.Abadi_Lamport_Lemma5 le_infI2 by blast
  from 2 3 have "?lhs \<le> A \<^bold>\<longrightarrow>\<^sub>+ (\<Sqinter>i\<in>I. Cs i)"
    using heyting.mp by blast
  then show ?thesis
    by - (rule order.trans[OF _ spec.Abadi_Merz_Prop2_1[where Q="\<Sqinter> (Cs ` I)"]]; simp add: inf.coboundedI1)
qed

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
