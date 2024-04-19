(*<*)
theory Heyting
imports
  Closures
begin

(*>*)
section\<open> Heyting algebras \label{sec:heyting_algebras} \<close>

text\<open>

Our (complete) lattices are Heyting algebras. The following development is oriented towards
using the derived Heyting implication in a logical fashion. As there are no standard classes for
semi-(complete-)lattices we simply work with complete lattices.

References:
 \<^item> \<^citet>\<open>"Esakia:2019"\<close> -- fundamental theory
 \<^item> \<^citet>\<open>\<open>Lemma 5.2.1\<close> in "vanDalen:2004"\<close> -- some equivalences
 \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Pseudocomplement\<close> -- properties

\<close>

class heyting_algebra = complete_lattice +
  assumes inf_Sup_distrib1: "\<And>Y::'a set. \<And>x::'a. x \<sqinter> (\<Squnion>Y) = (\<Squnion>y\<in>Y. x \<sqinter> y)"
begin

definition heyting :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<^bold>\<longrightarrow>\<^sub>H" 53) where
  "x \<^bold>\<longrightarrow>\<^sub>H y = \<Squnion>{z. x \<sqinter> z \<le> y}"

lemma heyting: \<comment>\<open> The Galois property for \<open>(\<sqinter>)\<close> and \<open>\<^bold>\<longrightarrow>\<^sub>H\<close> \<close>
  shows "z \<le> x \<^bold>\<longrightarrow>\<^sub>H y \<longleftrightarrow> z \<sqinter> x \<le> y" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  from inf_Sup_distrib1 have "\<Squnion>{a. x \<sqinter> a \<le> y} \<sqinter> x \<le> y" by (simp add: SUP_le_iff inf_commute)
  then show "?lhs \<Longrightarrow> ?rhs" unfolding heyting_def by (meson inf_mono order.trans order_refl)
  show "?rhs \<Longrightarrow> ?lhs" by (simp add: heyting_def Sup_upper inf.commute)
qed

end

setup \<open>Sign.mandatory_path "heyting"\<close>

context heyting_algebra
begin

lemma commute:
  shows "x \<sqinter> z \<le> y \<longleftrightarrow> z \<le> (x \<^bold>\<longrightarrow>\<^sub>H y)"
by (simp add: heyting inf.commute)

lemmas uncurry = iffD1[OF heyting]
lemmas curry = iffD2[OF heyting]

lemma curry_conv:
  shows "(x \<sqinter> y \<^bold>\<longrightarrow>\<^sub>H z) = (x \<^bold>\<longrightarrow>\<^sub>H y \<^bold>\<longrightarrow>\<^sub>H z)"
by (simp add: order_eq_iff) (metis heyting eq_refl inf.assoc)

lemma swap:
  shows "P \<^bold>\<longrightarrow>\<^sub>H Q \<^bold>\<longrightarrow>\<^sub>H R = Q \<^bold>\<longrightarrow>\<^sub>H P \<^bold>\<longrightarrow>\<^sub>H R"
by (metis curry_conv inf.commute)

lemma absorb:
  shows "y \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>H y) = y"
    and "(x \<^bold>\<longrightarrow>\<^sub>H y) \<sqinter> y = y"
by (simp_all add: curry inf_absorb1 ac_simps)

lemma detachment:
  shows "x \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>H y) = x \<sqinter> y" (is ?thesis1)
    and "(x \<^bold>\<longrightarrow>\<^sub>H y) \<sqinter> x = x \<sqinter> y" (is ?thesis2)
proof -
  show ?thesis1 by (metis absorb(1) uncurry inf.assoc inf.commute inf.idem inf_iff_le(2))
  then show ?thesis2 by (simp add: ac_simps)
qed

lemma discharge:
  assumes "x' \<le> x"
  shows "x' \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>H y) = x' \<sqinter> y" (is ?thesis1)
    and "(x \<^bold>\<longrightarrow>\<^sub>H y) \<sqinter> x' = y \<sqinter> x'" (is ?thesis2)
proof -
  from assms show ?thesis1 by (metis curry_conv detachment(2) inf.absorb1)
  then show ?thesis2 by (simp add: ac_simps)
qed

lemma trans:
  shows "(x \<^bold>\<longrightarrow>\<^sub>H y) \<sqinter> (y \<^bold>\<longrightarrow>\<^sub>H z) \<le> x \<^bold>\<longrightarrow>\<^sub>H z"
by (metis curry detachment(2) swap uncurry inf_le2)

lemma rev_trans:
  shows "(y \<^bold>\<longrightarrow>\<^sub>H z) \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>H y) \<le> x \<^bold>\<longrightarrow>\<^sub>H z"
by (simp add: inf.commute trans)

lemma discard:
  shows "Q \<le> P \<^bold>\<longrightarrow>\<^sub>H Q"
by (simp add: curry)

lemma infR:
  shows "x \<^bold>\<longrightarrow>\<^sub>H y \<sqinter> z = (x \<^bold>\<longrightarrow>\<^sub>H y) \<sqinter> (x \<^bold>\<longrightarrow>\<^sub>H z)"
by (simp add: order_eq_iff curry uncurry detachment le_infI2)

lemma mono:
  assumes "x' \<le> x"
  assumes "y \<le> y'"
  shows "x \<^bold>\<longrightarrow>\<^sub>H y \<le> x' \<^bold>\<longrightarrow>\<^sub>H y'"
using assms by (metis curry detachment(1) uncurry inf_commute inf_absorb2 le_infI1)

lemma strengthen[strg]:
  assumes "st_ord (\<not> F) X X'"
  assumes "st_ord F Y Y'"
  shows "st_ord F (X \<^bold>\<longrightarrow>\<^sub>H Y) (X' \<^bold>\<longrightarrow>\<^sub>H Y')"
using assms by (cases F; simp add: heyting.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<ge>) F"
  assumes "monotone orda (\<le>) G"
  shows "monotone orda (\<le>) (\<lambda>x. F x \<^bold>\<longrightarrow>\<^sub>H G x)"
by (simp add: monotoneI curry discharge le_infI1 monotoneD[OF assms(1)] monotoneD[OF assms(2)])

lemma mp:
  assumes "x \<le> y \<^bold>\<longrightarrow>\<^sub>H z"
  assumes "x \<le> y"
  shows "x \<le> z"
by (meson assms uncurry inf_greatest order.refl order_trans)

lemma botL:
  shows "\<bottom> \<^bold>\<longrightarrow>\<^sub>H x = \<top>"
by (simp add: heyting top_le)

lemma top_conv:
  shows "x \<^bold>\<longrightarrow>\<^sub>H y = \<top> \<longleftrightarrow> x \<le> y"
by (metis curry detachment(2) inf_iff_le(1) inf_top.left_neutral)

lemma refl[simp]:
  shows "x \<^bold>\<longrightarrow>\<^sub>H x = \<top>"
by (simp add: top_conv)

lemma topL[simp]:
  shows "\<top> \<^bold>\<longrightarrow>\<^sub>H x = x"
by (metis detachment(1) inf_top_left)

lemma topR[simp]:
  shows "x \<^bold>\<longrightarrow>\<^sub>H \<top> = \<top>"
by (simp add: top_conv)

lemma K[simp]:
  shows "x \<^bold>\<longrightarrow>\<^sub>H (y \<^bold>\<longrightarrow>\<^sub>H x) = \<top>"
by (simp add: discard top_conv)

subclass distrib_lattice
proof \<comment>\<open> \<^citet>\<open>\<open>Proposition~1.5.3\<close> in "Esakia:2019"\<close> \<close>
  have "x \<sqinter> (y \<squnion> z) \<le> x \<sqinter> y \<squnion> x \<sqinter> z" for x y z :: 'a
    using commute by fastforce
  then have "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" for x y z :: 'a
    by (simp add: order.eq_iff le_infI2)
  then show "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)" for x y z :: 'a
    by (rule distrib_imp1)
qed

lemma supL:
  shows "(x \<squnion> y) \<^bold>\<longrightarrow>\<^sub>H z = (x \<^bold>\<longrightarrow>\<^sub>H z) \<sqinter> (y \<^bold>\<longrightarrow>\<^sub>H z)"
by (simp add: order_eq_iff mono curry uncurry inf_sup_distrib1)

subclass (in complete_distrib_lattice) heyting_algebra by standard (rule inf_Sup)

lemma inf_Sup_distrib:
  shows "x \<sqinter> \<Squnion>Y = (\<Squnion>y\<in>Y. x \<sqinter> y)"
    and "\<Squnion>Y \<sqinter> x = (\<Squnion>y\<in>Y. x \<sqinter> y)"
by (simp_all add: inf_Sup_distrib1 inf_commute)

lemma inf_SUP_distrib:
  shows "x \<sqinter> (\<Squnion>i\<in>I. Y i) = (\<Squnion>i\<in>I. x \<sqinter> Y i)"
    and "(\<Squnion>i\<in>I. Y i) \<sqinter> x = (\<Squnion>i\<in>I. Y i \<sqinter> x)"
by (simp_all add: inf_Sup_distrib image_image ac_simps)

end

lemma eq_boolean_implication: \<comment>\<open> the implications coincide in \<^class>\<open>boolean_algebra\<close>s  \<close>
  fixes x :: "_::boolean_algebra"
  shows "x \<^bold>\<longrightarrow>\<^sub>H y = x \<^bold>\<longrightarrow>\<^sub>B y"
by (simp add: order.eq_iff boolean_implication_def heyting.detachment heyting.curry flip: shunt1)

lemmas simp_thms =
  heyting.botL
  heyting.topL
  heyting.topR
  heyting.refl

lemma Sup_prime_Sup_irreducible_iff:
  fixes x :: "_::heyting_algebra"
  shows "Sup_prime x \<longleftrightarrow> Sup_irreducible x"
by (fastforce simp: Sup_prime_on_def Sup_irreducible_on_def inf.order_iff heyting.inf_Sup_distrib
             intro: Sup_prime_on_imp_Sup_irreducible_on)

paragraph\<open> Logical rules ala HOL \<close>

lemma bspec:
  fixes P :: "_ \<Rightarrow> (_::heyting_algebra)"
  shows "x \<in> X \<Longrightarrow> (\<Sqinter>x\<in>X. P x \<^bold>\<longrightarrow>\<^sub>H Q x) \<sqinter> P x \<le> Q x" (is "?X \<Longrightarrow> ?thesis1")
    and "x \<in> X \<Longrightarrow> P x \<sqinter> (\<Sqinter>x\<in>X. P x \<^bold>\<longrightarrow>\<^sub>H Q x) \<le> Q x" (is "_ \<Longrightarrow> ?thesis2")
    and "(\<Sqinter>x. P x \<^bold>\<longrightarrow>\<^sub>H Q x) \<sqinter> P x \<le> Q x" (is ?thesis3)
    and "P x \<sqinter> (\<Sqinter>x. P x \<^bold>\<longrightarrow>\<^sub>H Q x) \<le> Q x" (is ?thesis4)
proof -
  show "?X \<Longrightarrow> ?thesis1" by (meson INF_lower heyting.uncurry)
  then show "?X \<Longrightarrow> ?thesis2" by (simp add: inf_commute)
  show ?thesis3 by (simp add: Inf_lower heyting.commute inf_commute)
  then show ?thesis4 by (simp add: inf_commute)
qed

lemma INFL:
  fixes Q :: "_::heyting_algebra"
  shows "(\<Sqinter>x\<in>X. P x \<^bold>\<longrightarrow>\<^sub>H Q) = (\<Squnion>x\<in>X. P x) \<^bold>\<longrightarrow>\<^sub>H Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by (meson INFE SUPE order.refl heyting.commute heyting.uncurry)
  show "?rhs \<le> ?lhs" by (simp add: INFI SupI heyting.mono)
qed

lemmas SUPL = heyting.INFL[symmetric]

lemma INFR:
  fixes P :: "_::heyting_algebra"
  shows "(\<Sqinter>x\<in>X. P \<^bold>\<longrightarrow>\<^sub>H Q x) = (P \<^bold>\<longrightarrow>\<^sub>H (\<Sqinter>x\<in>X. Q x))" (is "?lhs = ?rhs")
by (simp add: order_eq_iff INFI INF_lower heyting.mono)
   (meson INFI INF_lower heyting.curry heyting.uncurry)

lemmas Inf_simps = \<comment>\<open> "Miniscoping: pushing in universal quantifiers." \<close>
  Inf_inf
  inf_Inf
  INF_inf_const1
  INF_inf_const2
  heyting.INFL
  heyting.INFR

lemma SUPL_le:
  fixes Q :: "_::heyting_algebra"
  shows "(\<Squnion>x\<in>X. P x \<^bold>\<longrightarrow>\<^sub>H Q) \<le> (\<Sqinter>x\<in>X. P x) \<^bold>\<longrightarrow>\<^sub>H Q"
by (simp add: INF_lower SUPE heyting.mono)

lemma SUPR_le:
  fixes P :: "_::heyting_algebra"
  shows "(\<Squnion>x\<in>X. P \<^bold>\<longrightarrow>\<^sub>H Q x) \<le> P \<^bold>\<longrightarrow>\<^sub>H (\<Squnion>x\<in>X. Q x)"
by (simp add: SUPE SUP_upper heyting.mono)

lemma SUP_inf:
  fixes Q :: "_::heyting_algebra"
  shows "(\<Squnion>x\<in>X. P x \<sqinter> Q) = (\<Squnion>x\<in>X. P x) \<sqinter> Q"
by (simp add: heyting.inf_SUP_distrib(2))

lemma inf_SUP:
  fixes P :: "_::heyting_algebra"
  shows "(\<Squnion>x\<in>X. P \<sqinter> Q x) =  P \<sqinter> (\<Squnion>x\<in>X. Q x)"
by (simp add: heyting.inf_SUP_distrib(1))

lemmas Sup_simps = \<comment>\<open> "Miniscoping: pushing in universal quantifiers." \<close>
  sup_SUP
  SUP_sup
  heyting.inf_SUP
  heyting.SUP_inf

lemma mcont2mcont_inf[cont_intro]:
  fixes F :: "_ \<Rightarrow> 'a::heyting_algebra"
  fixes G :: "_ \<Rightarrow> 'a::heyting_algebra"
  assumes "mcont luba orda Sup (\<le>) F"
  assumes "mcont luba orda Sup (\<le>) G"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. F x \<sqinter> G x)"
proof -
  have mcont_inf1: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. x \<sqinter> y)" for x :: "'a::heyting_algebra"
    by (auto intro!: contI mcontI monotoneI intro: le_infI2 simp flip: heyting.inf_SUP_distrib)
  then have mcont_inf2: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>x. x \<sqinter> y)" for y :: "'a::heyting_algebra"
    by (subst inf.commute) (rule mcont_inf1)
  from assms mcont_inf1 mcont_inf2 show ?thesis
    by (best intro: ccpo.mcont2mcont'[OF complete_lattice_ccpo] ccpo.mcont_const[OF complete_lattice_ccpo])
qed

lemma closure_imp_distrib_le: \<comment>\<open> \<^citet>\<open>\<open>Lemma~3.3\<close> in "AbadiPlotkin:1993"\<close>, generalized \<close>
  fixes P Q :: "_ :: heyting_algebra"
  assumes cl: "closure_axioms (\<le>) cl"
  assumes cl_inf: "\<And>x y. cl x \<sqinter> cl y \<le> cl (x \<sqinter> y)"
  shows "P \<^bold>\<longrightarrow>\<^sub>H Q \<le> cl P \<^bold>\<longrightarrow>\<^sub>H cl Q"
proof -
  from cl have "(P \<^bold>\<longrightarrow>\<^sub>H Q) \<sqinter> cl P \<le> cl (P \<^bold>\<longrightarrow>\<^sub>H Q) \<sqinter> cl P"
    by (metis (mono_tags) closure_axioms_def inf_mono order.refl)
  also have "\<dots> \<le> cl ((P \<^bold>\<longrightarrow>\<^sub>H Q) \<sqinter> P)"
    by (simp add: cl_inf)
  also from cl have "\<dots> \<le> cl Q"
    by (metis (mono_tags) closure_axioms_def order.refl heyting.mono heyting.uncurry)
  finally show ?thesis
    by (simp add: heyting)
qed

setup \<open>Sign.parent_path\<close>


paragraph\<open> Pseudocomplements \<close>

definition pseudocomplement :: "'a::heyting_algebra \<Rightarrow> 'a" ("\<^bold>\<not>\<^sub>H _" [75] 75) where
  "\<^bold>\<not>\<^sub>Hx = x \<^bold>\<longrightarrow>\<^sub>H \<bottom>"

lemma pseudocomplementI:
  shows "x \<le> \<^bold>\<not>\<^sub>Hy \<longleftrightarrow> x \<sqinter> y \<le> \<bottom>"
by (simp add: pseudocomplement_def heyting)

setup \<open>Sign.mandatory_path "pseudocomplement"\<close>

lemma monotone:
  shows "antimono pseudocomplement"
by (simp add: antimonoI heyting.mono pseudocomplement_def)

lemmas strengthen[strg] = st_monotone[OF pseudocomplement.monotone]
lemmas mono = monotoneD[OF pseudocomplement.monotone]
lemmas mono2mono[cont_intro, partial_function_mono]
   = monotone2monotone[OF pseudocomplement.monotone, simplified, of orda P for orda P]

lemma eq_boolean_negation: \<comment>\<open> the negations coincide in \<^class>\<open>boolean_algebra\<close>s  \<close>
  fixes x :: "_::{boolean_algebra,heyting_algebra}"
  shows "\<^bold>\<not>\<^sub>Hx = -x"
by (simp add: pseudocomplement_def heyting.eq_boolean_implication)

lemma heyting:
  shows "x \<^bold>\<longrightarrow>\<^sub>H \<^bold>\<not>\<^sub>Hx = \<^bold>\<not>\<^sub>Hx"
by (simp add: pseudocomplement_def order_eq_iff heyting heyting.detachment)

lemma Inf:
  shows "x \<sqinter> \<^bold>\<not>\<^sub>Hx = \<bottom>"
    and "\<^bold>\<not>\<^sub>Hx \<sqinter> x = \<bottom>"
by (simp_all add: pseudocomplement_def heyting.detachment)

lemma double_le:
  shows "x \<le> \<^bold>\<not>\<^sub>H\<^bold>\<not>\<^sub>Hx"
by (simp add: pseudocomplement_def heyting.detachment heyting.curry)

interpretation double: closure_complete_lattice_class "pseudocomplement \<circ> pseudocomplement"
by standard (simp; meson order.trans pseudocomplement.double_le pseudocomplement.mono)

lemma triple:
  shows "\<^bold>\<not>\<^sub>H\<^bold>\<not>\<^sub>H\<^bold>\<not>\<^sub>Hx = \<^bold>\<not>\<^sub>Hx"
by (simp add: order_eq_iff pseudocomplement.double_le pseudocomplement.mono)

lemma contrapos_le:
  shows "x \<^bold>\<longrightarrow>\<^sub>H y \<le> \<^bold>\<not>\<^sub>Hy \<^bold>\<longrightarrow>\<^sub>H \<^bold>\<not>\<^sub>Hx"
by (simp add: heyting.curry heyting.trans pseudocomplement_def)

lemma sup_inf: \<comment>\<open> half of de Morgan \<close>
  shows "\<^bold>\<not>\<^sub>H(x \<squnion> y) = \<^bold>\<not>\<^sub>Hx \<sqinter> \<^bold>\<not>\<^sub>Hy"
by (simp add: pseudocomplement_def heyting.supL)

lemma inf_sup_weak: \<comment>\<open> the weakened other half of de Morgan \<close>
  shows "\<^bold>\<not>\<^sub>H(x \<sqinter> y) = \<^bold>\<not>\<^sub>H\<^bold>\<not>\<^sub>H(\<^bold>\<not>\<^sub>Hx \<squnion> \<^bold>\<not>\<^sub>Hy)"
by (metis (no_types, opaque_lifting) pseudocomplement_def heyting.curry_conv heyting.supL inf_commute pseudocomplement.triple)                   

lemma fix_triv:
  assumes "x = \<^bold>\<not>\<^sub>Hx"
  shows "x = y"
using assms by (metis antisym bot.extremum inf.idem inf_le2 pseudocomplementI)

lemma double_top:
  shows "\<^bold>\<not>\<^sub>H\<^bold>\<not>\<^sub>H(x \<squnion> \<^bold>\<not>\<^sub>Hx) = \<top>"
by (metis pseudocomplement_def heyting.refl pseudocomplement.Inf(1) pseudocomplement.sup_inf)

lemma Inf_inf:
  fixes P :: "_ \<Rightarrow> (_::heyting_algebra)"
  shows "(\<Sqinter>x. P x) \<sqinter> \<^bold>\<not>\<^sub>HP x = \<bottom>"
by (simp add: pseudocomplement_def Inf_lower heyting.discharge(1))

lemma SUP_le: \<comment>\<open> half of de Morgan \<close>
  fixes P :: "_ \<Rightarrow> (_::heyting_algebra)"
  shows "(\<Squnion>x\<in>X. P x) \<le> \<^bold>\<not>\<^sub>H(\<Sqinter>x\<in>X. \<^bold>\<not>\<^sub>HP x)"
by (rule SUP_least) (meson INF_lower order.trans pseudocomplement.double_le pseudocomplement.mono)

lemma SUP_INF_le:
  fixes P :: "_ \<Rightarrow> (_::heyting_algebra)"
  shows "(\<Squnion>x\<in>X. \<^bold>\<not>\<^sub>HP x) \<le> \<^bold>\<not>\<^sub>H(\<Sqinter>x\<in>X. P x)"
by (simp add: INF_lower SUPE pseudocomplement.mono)

lemma SUP:
  fixes P :: "_ \<Rightarrow> (_::heyting_algebra)"
  shows "\<^bold>\<not>\<^sub>H(\<Squnion>x\<in>X. P x) = (\<Sqinter>x\<in>X. \<^bold>\<not>\<^sub>HP x)"
by (simp add: order.eq_iff SUP_upper le_INF_iff pseudocomplement.mono)
   (metis inf_commute pseudocomplement.SUP_le pseudocomplementI)

setup \<open>Sign.parent_path\<close>


subsection\<open> Downwards closure of preorders (downsets) \label{sec:closures-downwards} \<close>

text\<open>

A \<^emph>\<open>downset\<close> (also \<^emph>\<open>lower set\<close> and \<^emph>\<open>order ideal\<close>) is a subset of a preorder that is closed under
the order relation. (An \<^emph>\<open>ideal\<close> is a downset that is \<^const>\<open>directed\<close>.) Some results require
antisymmetry (a partial order).

References:
 \<^item> \<^citet>\<open>"Vickers:1989"\<close>, early chapters.
 \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Alexandrov_topology\<close>
 \<^item> \<^citet>\<open>\<open>\S3\<close> in "AbadiPlotkin:1991"\<close>

\<close>

setup \<open>Sign.mandatory_path "downwards"\<close>

definition cl :: "'a::preorder set \<Rightarrow> 'a set" where
  "cl P = {x |x y. y \<in> P \<and> x \<le> y}"

setup \<open>Sign.parent_path\<close>

interpretation downwards: closure_powerset_distributive downwards.cl \<comment>\<open> On preorders \<close>
proof standard
  show "(P \<subseteq> downwards.cl Q) \<longleftrightarrow> (downwards.cl P \<subseteq> downwards.cl Q)" for P Q :: "'a set"
    unfolding downwards.cl_def by (auto dest: order_trans)
  show "downwards.cl (\<Union>X) \<subseteq> \<Union> (downwards.cl ` X) \<union> downwards.cl {}" for X :: "'a set set"
    unfolding downwards.cl_def by auto
qed

interpretation downwards: closure_powerset_distributive_anti_exchange "(downwards.cl::_::order set \<Rightarrow> _)"
  \<comment>\<open> On partial orders; see \<^citet>\<open>"PfaltzSlapal:2013"\<close> \<close>
by standard (unfold downwards.cl_def; blast intro: anti_exchangeI antisym)

setup \<open>Sign.mandatory_path "downwards"\<close>

lemma cl_empty:
  shows "downwards.cl {} = {}"
unfolding downwards.cl_def by simp

lemma closed_empty[iff]:
  shows "{} \<in> downwards.closed"
using downwards.cl_def by fastforce

lemma clI[intro]:
  assumes "y \<in> P"
  assumes "x \<le> y"
  shows "x \<in> downwards.cl P"
unfolding closure.closed_def downwards.cl_def using assms by blast

lemma clE:
  assumes "x \<in> downwards.cl P"
  obtains y where "y \<in> P" and "x \<le> y"
using assms unfolding downwards.cl_def by fast

lemma closed_in:
  assumes "x \<in> P"
  assumes "y \<le> x"
  assumes "P \<in> downwards.closed"
  shows "y \<in> P"
using assms unfolding downwards.cl_def downwards.closed_def by blast

lemma order_embedding: \<comment>\<open> On preorders; see \<^citet>\<open>\<open>\S1.35\<close> in "DaveyPriestley:2002"\<close> \<close>
  fixes x :: "_::preorder"
  shows "downwards.cl {x} \<subseteq> downwards.cl {y} \<longleftrightarrow> x \<le> y"
using downwards.cl by (blast elim: downwards.clE)

text\<open>

The lattice of downsets of a set \<open>X\<close> is always a \<^class>\<open>heyting_algebra\<close>.

References:
 \<^item> \<^citet>\<open>\<open>\S7.5\<close> in "Ono:2019"\<close>; uses upsets, points to \<^citet>\<open>"Stone:1938"\<close> as the origin
 \<^item> \<^citet>\<open>\<open>\S2.2\<close> in "Esakia:2019"\<close>
 \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Intuitionistic_logic#Heyting_algebra_semantics\<close>

\<close>

definition imp :: "'a::preorder set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "imp P Q = {\<sigma>. \<forall>\<sigma>'\<le>\<sigma>. \<sigma>' \<in> P \<longrightarrow> \<sigma>' \<in> Q}"

lemma imp_refl:
  shows "downwards.imp P P = UNIV"
by (simp add: downwards.imp_def)

lemma imp_contained:
  assumes "P \<subseteq> Q"
  shows "downwards.imp P Q = UNIV"
unfolding downwards.imp_def using assms by fast

lemma heyting_imp:
  assumes "P \<in> downwards.closed"
  shows "P \<subseteq> downwards.imp Q R \<longleftrightarrow> P \<inter> Q \<subseteq> R"
using assms unfolding downwards.imp_def downwards.closed_def by blast

lemma imp_mp':
  assumes "\<sigma> \<in> downwards.imp P Q"
  assumes "\<sigma> \<in> P"
  shows "\<sigma> \<in> Q"
using assms by (simp add: downwards.imp_def)

lemma imp_mp:
  shows "P \<inter> downwards.imp P Q \<subseteq> Q"
    and "downwards.imp P Q \<inter> P \<subseteq> Q"
by (meson IntD1 IntD2 downwards.imp_mp' subsetI)+

lemma imp_contains:
  assumes "X \<subseteq> Q"
  assumes "X \<in> downwards.closed"
  shows "X \<subseteq> downwards.imp P Q"
using assms by (auto simp: downwards.imp_def elim: downwards.closed_in)

lemma imp_downwards:
  assumes "y \<in> downwards.imp P Q"
  assumes "x \<le> y"
  shows "x \<in> downwards.imp P Q"
using assms order_trans by (force simp: downwards.imp_def)

lemma closed_imp:
  shows "downwards.imp P Q \<in> downwards.closed"
by (meson downwards.clE downwards.closedI downwards.imp_downwards)

text\<open>

The set \<open>downwards.imp P Q\<close> is the greatest downset contained in the Boolean implication
\<open>P \<^bold>\<longrightarrow>\<^sub>B Q\<close>, i.e., \<open>downwards.imp\<close> is the \<^emph>\<open>kernel\<close> of \<open>(\<^bold>\<longrightarrow>\<^sub>B)\<close> \<^citep>\<open>"Zwiers:1989"\<close>.
Note that ``kernel'' is a choice or interior function.

\<close>

lemma imp_boolean_implication_subseteq:
  shows "downwards.imp P Q \<subseteq> P \<^bold>\<longrightarrow>\<^sub>B Q"
unfolding downwards.imp_def boolean_implication.set_alt_def by blast

lemma downwards_closed_imp_greatest:
  assumes "R \<subseteq> P \<^bold>\<longrightarrow>\<^sub>B Q"
  assumes "R \<in> downwards.closed"
  shows "R \<subseteq> downwards.imp P Q"
using assms unfolding boolean_implication.set_alt_def downwards.imp_def downwards.closed_def by blast

definition kernel :: "'a::order set \<Rightarrow> 'a set" where
  "kernel X = \<Squnion>{Q \<in> downwards.closed. Q \<subseteq> X}"

lemma kernel_def2:
  shows "downwards.kernel X = {\<sigma>. \<forall>\<sigma>'\<le>\<sigma>. \<sigma>' \<in> X}" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs"
    unfolding downwards.kernel_def using downwards.closed_conv by blast
next
  have "x \<in> ?lhs" if "x \<in> ?rhs" for x
    unfolding downwards.kernel_def using that
    by (auto elim: downwards.clE intro: exI[where x="downwards.cl {x}"])
  then show "?rhs \<subseteq> ?lhs" by blast
qed

lemma kernel_contractive:
  shows "downwards.kernel X \<subseteq> X"
unfolding downwards.kernel_def by blast

lemma kernel_idempotent:
  shows "downwards.kernel (downwards.kernel X) = downwards.kernel X"
unfolding downwards.kernel_def by blast

lemma kernel_monotone:
  shows "mono downwards.kernel"
unfolding downwards.kernel_def by (rule monotoneI) blast

lemma closed_kernel_conv:
  shows "X \<in> downwards.closed \<longleftrightarrow> downwards.kernel X = X"
unfolding downwards.kernel_def2 downwards.closed_def by (blast elim: downwards.clE)

lemma closed_kernel:
  shows "downwards.kernel X \<in> downwards.closed"
by (simp add: downwards.closed_kernel_conv downwards.kernel_idempotent)

lemma kernel_cl:
  shows "downwards.kernel (downwards.cl X) = downwards.cl X"
using downwards.closed_kernel_conv by blast

lemma cl_kernel:
  shows "downwards.cl (downwards.kernel X) = downwards.kernel X"
by (simp flip: downwards.closed_conv add: downwards.closed_kernel)

lemma kernel_boolean_implication:
  fixes P :: "_::order"
  shows "downwards.kernel (P \<^bold>\<longrightarrow>\<^sub>B Q) = downwards.imp P Q"
unfolding downwards.kernel_def2 boolean_implication.set_alt_def downwards.imp_def by blast

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
