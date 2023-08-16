(*
Title: Quantales with converse
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Quantales with converse\<close>

theory Quantale_Converse
  imports Modal_Quantale Modal_Kleene_Algebra_Converse

begin

subsection \<open>Properties of unital quantales\<close>

text \<open>These properties should eventually added to the quantales AFP entry.\<close>

lemma (in quantale) bres_bot_top [simp]: "\<bottom> \<rightarrow> \<top> = \<top>"
  by (simp add: local.bres_galois_imp local.order.antisym)

lemma (in quantale) fres_top_bot [simp]: "\<top> \<leftarrow> \<bottom> = \<top>"
  by (meson local.fres_galois local.order_antisym local.top_greatest)

lemma (in unital_quantale) bres_top_top2 [simp]: "(x \<rightarrow> y \<cdot> \<top>) \<cdot> \<top> = x \<rightarrow> y \<cdot> \<top>"
proof-
  have "(x \<rightarrow> y \<cdot> \<top>) \<cdot> \<top> \<le> x \<rightarrow> y \<cdot> \<top> \<cdot> \<top>"
    by (simp add: local.bres_interchange)
  hence "(x \<rightarrow> y \<cdot> \<top>) \<cdot> \<top> \<le> x \<rightarrow> y \<cdot> \<top>"
    by (simp add: mult_assoc)
  thus ?thesis
    by (metis local.mult_1_right local.order_eq_iff local.psrpq.subdistl local.sup_top_right)
qed

lemma (in unital_quantale) fres_top_top2 [simp]: "\<top> \<cdot> (\<top> \<cdot> y \<leftarrow> x) =  \<top> \<cdot> y \<leftarrow> x"
  by (metis local.dual_order.antisym local.fres_interchange local.le_top local.top_greatest mult_assoc)

lemma (in unital_quantale) bres_top_bot [simp]: "\<top> \<rightarrow> \<bottom> = \<bottom>"
  by (metis local.bot_least local.bres_canc1 local.le_top local.order.antisym)

lemma (in unital_quantale) fres_bot_top [simp]: "\<bottom> \<leftarrow> \<top> = \<bottom>"
  by (metis local.bot_unique local.fres_canc1 local.top_le local.uqka.independence2 local.uwqlka.star_ext)

lemma (in unital_quantale) top_bot_iff: "(x \<cdot> \<top> = \<bottom>) = (x = \<bottom>)"
  by (metis local.fres_bot_top local.fres_canc2 local.le_bot local.mult_botl)


subsection \<open>Involutive quantales\<close>

text \<open>The following axioms for involutive quantales are standard.\<close>

class involutive_quantale = unital_quantale + invol_op +
  assumes inv_invol [simp]: "(x\<^sup>\<circ>)\<^sup>\<circ> = x"
  and inv_contrav: "(x \<cdot> y)\<^sup>\<circ> = y\<^sup>\<circ> \<cdot> x\<^sup>\<circ>"
  and inv_sup [simp]: "(\<Squnion>X)\<^sup>\<circ> = (\<Squnion>x \<in> X. x\<^sup>\<circ>)"

context involutive_quantale
begin

lemma inv_binsup [simp]: "(x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> \<squnion> y\<^sup>\<circ>"
proof-
  have "(x \<squnion> y)\<^sup>\<circ> = (\<Squnion>z \<in> {x,y}. z\<^sup>\<circ>)"
    using local.inv_sup local.sup_Sup by presburger
  also have "\<dots> = (\<Squnion>z \<in> {x\<^sup>\<circ>,y\<^sup>\<circ>}. z)"
    by simp
  also have "\<dots> = x\<^sup>\<circ> \<squnion> y\<^sup>\<circ>"
    by fastforce
  finally show ?thesis.
qed

lemma inv_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<circ> \<le> y\<^sup>\<circ>"
  by (metis inv_binsup local.sup.absorb_iff1)

lemma inv_galois: "(x\<^sup>\<circ> \<le> y) = (x \<le> y\<^sup>\<circ>)"
  using local.inv_iso by fastforce

lemma bres_fres_conv: "(y\<^sup>\<circ> \<leftarrow> x\<^sup>\<circ>)\<^sup>\<circ> = x \<rightarrow> y"
proof-
  have "(y\<^sup>\<circ> \<leftarrow> x\<^sup>\<circ>)\<^sup>\<circ> = (\<Squnion>{z. z \<cdot> x\<^sup>\<circ> \<le> y\<^sup>\<circ>})\<^sup>\<circ>"
    by (simp add: local.fres_def)
  also have "\<dots> = \<Squnion>{z\<^sup>\<circ> |z. z \<cdot> x\<^sup>\<circ> \<le> y\<^sup>\<circ>}"
    by (simp add: image_Collect)
  also have "\<dots> = \<Squnion>{z. z\<^sup>\<circ> \<cdot> x\<^sup>\<circ> \<le> y\<^sup>\<circ>}"
    by (metis local.inv_invol)
  also have "\<dots> = \<Squnion>{z. (x \<cdot> z)\<^sup>\<circ> \<le> y\<^sup>\<circ>}"
    by (simp add: local.inv_contrav)
  also have "\<dots> = \<Squnion>{z. x \<cdot> z \<le> y}"
    by (metis local.inv_invol local.inv_iso)
  also have "\<dots> = x \<rightarrow> y"
    by (simp add: local.bres_def)
  finally show ?thesis.
qed

lemma fres_bres_conv: "(y\<^sup>\<circ> \<rightarrow> x\<^sup>\<circ>)\<^sup>\<circ> = x \<leftarrow> y"
  by (metis bres_fres_conv local.inv_invol)

sublocale invqka: involutive_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar invol
  by unfold_locales (simp_all add: local.inv_contrav)

lemma inv_binf [simp]: "(x \<sqinter> y)\<^sup>\<circ> = x\<^sup>\<circ> \<sqinter> y\<^sup>\<circ>"
proof-
  {fix z
  have "(z \<le> (x \<sqinter> y)\<^sup>\<circ>) = (z\<^sup>\<circ> \<le> x \<sqinter> y)"
    using invqka.inv_adj by blast
  also have "\<dots> = (z\<^sup>\<circ> \<le> x \<and> z\<^sup>\<circ> \<le> y)"
    by simp
  also have "\<dots> = (z \<le> x\<^sup>\<circ> \<and> z \<le> y\<^sup>\<circ>)"
    by (simp add: invqka.inv_adj)
  also have "\<dots> = (z \<le> x\<^sup>\<circ> \<sqinter> y\<^sup>\<circ>)"
    by simp
  finally have "(z \<le> (x \<sqinter> y)\<^sup>\<circ>) = (z \<le> x\<^sup>\<circ> \<sqinter> y\<^sup>\<circ>)".}
  thus ?thesis
    using local.dual_order.antisym by blast
qed

lemma inv_inf [simp]: "(\<Sqinter>X)\<^sup>\<circ> = (\<Sqinter>x \<in> X. x\<^sup>\<circ>)"
  by (metis invqka.inv_adj local.INF_eqI local.Inf_greatest local.Inf_lower local.inv_invol)

lemma inv_top [simp]: "\<top>\<^sup>\<circ> = \<top>"
proof-
  have a: "\<top>\<^sup>\<circ> \<le> \<top>"
    by simp
  hence "(\<top>\<^sup>\<circ>)\<^sup>\<circ> \<le> \<top>\<^sup>\<circ>"
    using local.inv_iso by blast
  hence "\<top> \<le> \<top>\<^sup>\<circ>"
    by simp
  thus ?thesis
    by (simp add: local.top_le)
qed

lemma inv_qstar_aux [simp]: "(x ^ i)\<^sup>\<circ> = (x\<^sup>\<circ>) ^ i"
  by (induct i, simp_all add: local.power_commutes)

lemma inv_conjugate: "(x\<^sup>\<circ> \<sqinter> y = \<bottom>) = (x \<sqinter> y\<^sup>\<circ> = \<bottom>)"
  using inv_binf invqka.inv_zero by fastforce

text \<open>We define domain and codomain as in relation algebra and compare with the domain
and codomain axioms above.\<close>

definition do :: "'a \<Rightarrow> 'a" where
  "do x = 1 \<sqinter> (x \<cdot> x\<^sup>\<circ>)"

definition cd :: "'a \<Rightarrow> 'a" where
  "cd x = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> x)"

lemma do_inv: "do (x\<^sup>\<circ>) = cd x"
proof-
  have "do (x\<^sup>\<circ>) = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> (x\<^sup>\<circ>)\<^sup>\<circ>)"
    by (simp add: do_def)
  also have "\<dots> = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> x)"
    by simp
  also have "\<dots> = cd x"
    by (simp add: cd_def)
  finally show ?thesis.
qed

lemma cd_inv: "cd (x\<^sup>\<circ>) = do x"
  by (simp add: cd_def do_def)

lemma do_le_top: "do x \<le> 1 \<sqinter> (x \<cdot> \<top>)"
  by (simp add: do_def local.inf.coboundedI2 local.mult_isol)

lemma do_subid: "do x \<le> 1"
  by (simp add: do_def)

lemma cd_subid: "cd x \<le> 1"
  by (simp add: cd_def)

lemma do_bot [simp]: "do \<bottom> = \<bottom>"
  by (simp add: do_def)

lemma cd_bot [simp]: "cd \<bottom> = \<bottom>"
  by (simp add: cd_def)

lemma do_iso: "x \<le> y \<Longrightarrow> do x \<le> do y"
  by (simp add: do_def local.inf.coboundedI2 local.inv_iso local.psrpq.mult_isol_var)

lemma cd_iso: "x \<le> y \<Longrightarrow> cd x \<le> cd y"
  using cd_def local.eq_refl local.inf_mono local.inv_iso local.psrpq.mult_isol_var by presburger

lemma do_subdist: "do x \<squnion> do y \<le> do (x \<squnion> y)"
proof-
  have "do x \<le> do (x \<squnion> y)" and "do y \<le> do (x \<squnion> y)"
    by (simp_all add: do_iso)
  thus ?thesis
    by simp
qed

lemma cd_subdist: "cd x \<squnion> cd y \<le> cd (x \<squnion> y)"
  by (simp add: cd_iso)

lemma inv_do [simp]: "(do x)\<^sup>\<circ> = do x"
  by (simp add: do_def)

lemma inv_cd [simp]: "(cd x)\<^sup>\<circ> = cd x"
  by (metis do_inv inv_do)

lemma dedekind_modular:
  assumes "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  shows "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  using assms local.inf.cobounded1 local.mult_isol local.order_trans by blast

lemma modular_eq1:
  assumes "\<forall>x y z w. (y \<sqinter> (z \<cdot> x\<^sup>\<circ>) \<le> w \<longrightarrow> (y \<cdot> x) \<sqinter> z \<le> w \<cdot> x)"
  shows "\<forall>x y z. (x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
  using assms by blast

lemma "do x \<cdot> do y = do x \<sqinter> do y" (* nitpick[expect=genuine]*)
  oops

lemma "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<cdot> q = p \<sqinter> q" (* nitpick[expect=genuine]*)
  oops

end

sublocale ab_unital_quantale \<subseteq> ciq: involutive_quantale id _ _ _ _ _ _ _ _ _ _
  by unfold_locales (simp_all add: mult_commute)

class distributive_involutive_quantale = involutive_quantale + distrib_unital_quantale

class boolean_involutive_quantale = involutive_quantale + bool_unital_quantale

begin

lemma res_peirce:
  assumes "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows  "((x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>) = ((y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>)"
proof
  assume "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>"
  hence "z\<^sup>\<circ> \<le> -(x \<cdot> y)"
    by (simp add: local.inf.commute local.inf_shunt)
  thus "(y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
    by (metis assms local.inf_shunt local.inv_conjugate local.inv_contrav local.inv_invol local.mult_isol local.order.trans)
next
  assume "(y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
  hence "x\<^sup>\<circ> \<le> -(y \<cdot> z)"
    using local.compl_le_swap1 local.inf_shunt by blast
  thus "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>"
    by (metis assms local.dual_order.trans local.inf_shunt local.inv_conjugate local.inv_contrav local.mult_isol)
qed

lemma res_schroeder1:
  assumes "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows "((x \<cdot> y) \<sqinter> z = \<bottom>) = (y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>)"
proof
  assume h: "(x \<cdot> y) \<sqinter> z = \<bottom>"
  hence "z \<le> -(x \<cdot> y)"
    by (simp add: local.inf.commute local.inf_shunt)
  thus "y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>"
    by (metis assms local.dual_order.trans local.inf.commute local.inf_shunt local.mult_isol)
next
  assume "y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>"
  hence "y \<le> -(x\<^sup>\<circ> \<cdot> z)"
    by (simp add: local.inf_shunt)
  thus "(x \<cdot> y) \<sqinter> z = \<bottom>"
    by (metis assms local.inf_shunt local.inv_invol local.order_trans mult_isol)
qed

lemma res_schroeder2:
  assumes "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows "((x \<cdot> y) \<sqinter> z = \<bottom>) = (x \<sqinter> (z \<cdot> y\<^sup>\<circ>) = \<bottom>)"
  by (metis assms local.inv_invol local.res_peirce local.res_schroeder1)

lemma res_mod:
  assumes  "\<forall>x y. x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  shows "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"
proof-
  have "(x \<cdot> y) \<sqinter> z = ((x \<sqinter> ((z \<cdot> y\<^sup>\<circ>) \<squnion> -(z \<cdot> y\<^sup>\<circ>))) \<cdot> y) \<sqinter> z"
    by simp
  also have "\<dots> = (((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<sqinter> z) \<squnion> (((x \<sqinter> -(z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<sqinter> z)"
    using local.chaq.wswq.distrib_left local.inf.commute local.sup_distr by presburger
  also have "\<dots> \<le> ((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<squnion> ((x \<cdot> y) \<sqinter> (-(z \<cdot> y\<^sup>\<circ>)) \<cdot> y \<sqinter> z)"
    by (metis assms local.inf.commute local.inf_compl_bot_right local.sup.orderI local.sup_inf_absorb res_schroeder2)
  also have "\<dots> \<le> ((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<squnion> ((x \<cdot> y) \<sqinter> -z  \<sqinter> z)"
    by (metis assms local.dual_order.eq_iff local.inf.commute local.inf_compl_bot_right res_schroeder2)
  also have "\<dots> \<le> ((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y)"
    by (simp add: local.inf.commute)
  finally show ?thesis.
qed

end

text \<open>The strong Gelfand property (name by Palmigiano and Re) is important for dioids and Kleene algebras.
The modular law is a convenient axiom for relational quantales, in a setting where the underlying
lattice is not boolean.\<close>

class quantale_converse = involutive_quantale +
  assumes strong_gelfand: "x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"

begin

lemma do_gelfand [simp]: "do x \<cdot> do x \<cdot> do x = do x"
  apply (rule order.antisym)
  using local.do_subid local.h_seq local.mult_isol apply fastforce
  by (metis local.inv_do local.strong_gelfand)

lemma cd_gelfand [simp]: "cd x \<cdot> cd x \<cdot> cd x = cd x"
  by (metis do_gelfand local.do_inv)

lemma do_idem [simp]: "do x \<cdot> do x  = do x"
  apply (rule order.antisym)
  using local.do_subid local.mult_isol apply fastforce
  by (metis do_gelfand local.do_subid local.eq_refl local.nsrnqo.mult_oner local.psrpq.mult_isol_var)

lemma cd_idem [simp]: "cd x \<cdot> cd x  = cd x"
  by (metis do_idem local.do_inv)

lemma dodo [simp]: "do (do x) = do x"
proof-
  have "do (do x) = 1 \<sqinter> (do x \<cdot> do x)"
    using local.do_def local.inv_do by force
  also have "\<dots> = 1 \<sqinter> do x"
    by simp
  also have "\<dots> = do x"
    by (simp add: local.do_def)
  finally show ?thesis.
qed

lemma cdcd [simp]: "cd (cd x) = cd x"
  using cd_idem local.cd_def local.inv_cd by force

lemma docd_compat [simp]: "do (cd x) = cd x"
proof-
  have "do (cd x) = do (do (x\<^sup>\<circ>))"
    by (simp add: local.do_inv)
  also have "\<dots> = do (x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cd x"
    by (simp add: local.do_inv)
  finally show ?thesis.
qed

lemma cddo_compat [simp]: "cd (do x) = do x"
  by (metis docd_compat local.cd_inv local.inv_do)

end

sublocale quantale_converse \<subseteq> convqka: kleene_algebra_converse "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" invol qstar
  by unfold_locales (simp add: local.strong_gelfand)


subsection \<open>Dedekind quantales\<close>

class dedekind_quantale = involutive_quantale +
  assumes modular_law: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y"

begin

sublocale convdqka: kleene_algebra_converse  "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" invol qstar
  by unfold_locales (metis local.inf.absorb2 local.le_top local.modular_law local.top_greatest)

subclass quantale_converse
  by unfold_locales (simp add: local.convdqka.strong_gelfand)

lemma modular_2 [simp]: "((x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> y) \<sqinter> z = (x \<cdot> y) \<sqinter> z"
  apply (rule order.antisym)
  using local.inf.cobounded1 local.inf_mono local.mult_isor local.order_refl apply presburger
  by (simp add: local.modular_law)

lemma modular_1 [simp]: "(x \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))) \<sqinter> z = (x \<cdot> y) \<sqinter> z"
  by (metis local.inv_binf local.inv_contrav local.inv_invol modular_2)

lemma modular3: "(x \<cdot> y) \<sqinter> z \<le> x \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
  by (metis local.inf.cobounded1 modular_1)

text \<open>The name Dedekind quantale owes to the following formula, which is equivalent to the modular law. Dedekind quantales
are called modular quantales in Rosenthal's book on quantaloids (to be precise: he discusses modular quantaloids, but the
notion of modular quantale is then obvious).\<close>

lemma dedekind: "(x \<cdot> y) \<sqinter> z \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
proof-
  have  "(x \<cdot> y) \<sqinter> z = (x \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))) \<sqinter> z"
    by simp
  also have "\<dots> \<le> (x \<sqinter> (z \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
    using local.modular_law by presburger
  also have "\<dots> = (x \<sqinter> (z \<cdot> (y\<^sup>\<circ> \<sqinter> (z\<^sup>\<circ> \<cdot> x)))) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
    by simp
  also have "\<dots> \<le> (x \<sqinter> (z \<cdot> y\<^sup>\<circ>)) \<cdot> (y \<sqinter> (x\<^sup>\<circ> \<cdot> z))"
    using local.inf.commute modular_1 by fastforce
  finally show ?thesis.
qed

lemma peirce: "((x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>) = ((y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>)"
proof
  assume "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>"
  hence "((x \<cdot> y) \<sqinter> z\<^sup>\<circ>) \<cdot> y\<^sup>\<circ> = \<bottom>"
    by simp
  hence "(z\<^sup>\<circ> \<cdot> y\<^sup>\<circ>) \<sqinter> x = \<bottom>"
    by (metis local.inf.commute local.inv_invol local.le_bot local.modular_law)
  hence "((y \<cdot> z) \<sqinter> x\<^sup>\<circ>)\<^sup>\<circ> = \<bottom>\<^sup>\<circ>"
    by simp
  thus "(y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
    by (metis local.inv_invol)
next
  assume h: "(y \<cdot> z) \<sqinter> x\<^sup>\<circ> = \<bottom>"
  hence "z\<^sup>\<circ> \<cdot> ((y \<cdot> z) \<sqinter> x\<^sup>\<circ>) = \<bottom>"
    by simp
  hence "(y\<^sup>\<circ> \<cdot> x\<^sup>\<circ>) \<sqinter> z = \<bottom>"
    by (metis h local.inf.commute local.inv_invol local.le_bot local.mult_botr modular3)
   hence "((x \<cdot> y) \<sqinter> z\<^sup>\<circ>)\<^sup>\<circ> = \<bottom>\<^sup>\<circ>"
    by simp
  thus "(x \<cdot> y) \<sqinter> z\<^sup>\<circ> = \<bottom>"
    by (metis local.inv_invol)
qed

lemma schroeder_1: "((x \<cdot> y) \<sqinter> z = \<bottom>) = (y \<sqinter> (x\<^sup>\<circ> \<cdot> z) = \<bottom>)"
  by (metis local.inf.commute local.inf_bot_right local.inv_invol local.mult_botr modular_1)

lemma schroeder_2: "((x \<cdot> y) \<sqinter> z = \<bottom>) = (x \<sqinter> (z \<cdot> y\<^sup>\<circ>) = \<bottom>)"
  by (metis local.inv_invol peirce schroeder_1)

lemma modular_eq2: "y \<sqinter> (z \<cdot> x\<^sup>\<circ>) \<le> w \<Longrightarrow> (y \<cdot> x) \<sqinter> z \<le> w \<cdot> x"
  by (meson local.dual_order.trans local.eq_refl local.h_w1 local.modular_law)

lemma lla_top_aux: "p \<le> 1 \<Longrightarrow> ((x \<le> p \<cdot> x) = (x \<le> p \<cdot> \<top>))"
proof
  assume h: "p \<le> 1"
  and h1: "x \<le> p \<cdot> x"
  thus "x \<le> p \<cdot> \<top>"
    by (meson local.mult_isol local.order_trans local.top_greatest)
next
  assume h: "p \<le> 1"
  and "x \<le> p \<cdot> \<top>"
  hence "x = (p \<cdot> \<top>) \<sqinter> x"
    using local.inf.absorb_iff2 by auto
  also have "\<dots> \<le> p \<cdot> (\<top> \<sqinter> (p\<^sup>\<circ> \<cdot> x))"
    using modular3 by blast
  also have "\<dots> = p \<cdot> p \<cdot> x"
    by (simp add: h local.convdqka.subid_conv mult_assoc)
  finally show "x \<le> p \<cdot> x"
    by (metis h local.dual_order.trans local.mult_isor local.nsrnqo.mult_onel)
qed

text \<open>Next we turn to properties of domain and codomain in Dedekind quantales.\<close>

lemma lra_top_aux: "p \<le> 1 \<Longrightarrow> ((x \<le> x \<cdot> p ) = (x \<le> \<top> \<cdot> p))"
  by (metis convdqka.subid_conv local.inf.absorb_iff2 local.mult_1_right local.psrpq.subdistl local.sup.absorb_iff2 local.top_greatest modular_eq2)

lemma lla: "p \<le> 1 \<Longrightarrow> ((do x \<le> p) = (x \<le> p \<cdot> \<top>))"
proof
  assume a1: "x \<le> p \<cdot> \<top>"
  assume a2: "p \<le> 1"
  have f3: "x \<cdot> \<top> \<le> p \<cdot> \<top> \<cdot> \<top>"
    by (simp add: a1 local.mult_isor)
  have f4: "p \<cdot> do x \<le> p"
    by (simp add: local.do_subid local.uqka.star_inductr_var_equiv local.uwqlka.star_subid)
  have "x \<cdot> \<top> \<le> p \<cdot> \<top>"
    using f3 by (simp add: local.mult.semigroup_axioms semigroup.assoc)
  thus "do x \<le> p"
    using f4 a2 lla_top_aux local.do_le_top local.inf.bounded_iff local.order_trans by blast
next
  assume a1: "do x \<le> p"
  assume a2: "p \<le> 1"
  hence  "do x \<cdot> x \<le> p \<cdot> x"
    by (simp add: a1 local.mult_isor)
  hence "x \<le> p \<cdot> x"
    using a1 local.do_def modular_eq2 by fastforce
  thus "x \<le> p \<cdot> \<top>"
    by (simp add: a2 lla_top_aux)
qed

lemma lla_Inf: "do x = \<Sqinter>{p. x \<le> p \<cdot> \<top> \<and> p \<le> 1}"
  apply (rule order.antisym)
  using lla local.Inf_greatest apply fastforce
  by (metis CollectI lla local.Inf_lower local.do_subid local.order.refl)

lemma lra: "p \<le> 1 \<Longrightarrow> ((cd x \<le> p) = (x \<le> \<top> \<cdot> p))"
  by (metis invqka.inv_adj lla local.convdqka.subid_conv local.do_inv local.inv_contrav local.inv_top)

lemma lra_Inf: "cd x = \<Sqinter>{p. x \<le> \<top> \<cdot> p \<and> p \<le> 1}"
  apply (rule order.antisym)
  using local.Inf_greatest lra apply fastforce
  by (metis CollectI local.Inf_lower local.cd_subid local.order.refl lra)

lemma lla_var: "p \<le> 1 \<Longrightarrow> ((do x \<le> p) = (x \<le> p \<cdot> x))"
  by (simp add: lla lla_top_aux)

lemma lla_Inf_var: "do x = \<Sqinter>{p. x \<le> p \<cdot> x \<and> p \<le> 1}"
  apply (rule order.antisym)
  using lla_var local.Inf_greatest apply fastforce
  by (metis CollectI lla_var local.Inf_lower local.do_subid local.order.refl)

lemma lra_var: "p \<le> 1 \<Longrightarrow> ((cd x \<le> p) = (x \<le> x \<cdot> p))"
  by (simp add: lra lra_top_aux)

lemma lra_Inf_var: "cd x = \<Sqinter>{p. x \<le> x \<cdot> p \<and> p \<le> 1}"
  apply (rule order.antisym)
  using local.Inf_greatest lra_var apply fastforce
  by (metis CollectI local.Inf_lower local.cd_subid local.order.refl lra_var)

lemma do_top: "do x = 1 \<sqinter> (x \<cdot> \<top>)"
proof-
  have "1 \<sqinter> (x \<cdot> \<top>) = 1 \<sqinter> (x \<cdot> (\<top> \<sqinter> x\<^sup>\<circ> \<cdot> 1))"
    by (metis local.inf.commute local.inf_top.left_neutral modular_1)
  also have "\<dots> = do x"
    by (simp add: local.do_def)
  finally show ?thesis..
qed

lemma cd_top: "cd x = 1 \<sqinter> (\<top> \<cdot> x)"
  by (metis do_top invqka.inv_one local.do_inv local.inv_binf local.inv_cd local.inv_contrav local.inv_invol local.inv_top)

text \<open>We start deriving the axioms of modal semirings and modal quantales.\<close>

lemma do_absorp: "x \<le> do x \<cdot> x"
  using lla_var local.do_subid by blast

lemma cd_absorp: "x \<le> x \<cdot> cd x"
  using local.cd_subid lra_var by blast

lemma do_absorp_eq [simp]: "do x \<cdot> x = x"
  using do_absorp local.do_subid local.dual_order.antisym local.h_w1 by fastforce

lemma cd_absorp_eq [simp]: "x \<cdot> cd x = x"
  by (metis do_top local.do_inv local.inf_top.right_neutral local.nsrnqo.mult_oner modular_1)

lemma do_top2: "x \<cdot> \<top> = do x \<cdot> \<top>"
proof (rule order.antisym)
  have "x \<cdot> \<top> = do x \<cdot> x \<cdot> \<top>"
    by simp
  also have "\<dots> \<le> do x \<cdot> \<top> \<cdot> \<top>"
    using local.psrpq.mult_double_iso local.top_greatest by presburger
  also have "\<dots> = do x \<cdot> \<top>"
    by (simp add: local.mult.semigroup_axioms semigroup.assoc)
  finally show "x \<cdot> \<top> \<le> do x \<cdot> \<top>".
  have "do x \<cdot> \<top> = (1 \<sqinter> (x \<cdot> \<top>)) \<cdot> \<top>"
    by (simp add: do_top)
  also have "\<dots> \<le> (1 \<cdot> \<top>) \<sqinter> (x \<cdot> \<top> \<cdot> \<top>)"
    by (simp add: local.mult_isor)
  also have "\<dots> = x \<cdot> \<top>"
    by (simp add: mult_assoc)
  finally show "do x \<cdot> \<top> \<le> x \<cdot> \<top>".
qed

lemma cd_top2: "\<top> \<cdot> x  = \<top> \<cdot> cd x"
  by (metis do_top2 local.do_inv local.inv_cd local.inv_contrav local.inv_invol local.inv_top)

lemma do_local [simp]: "do (x \<cdot> do y) = do (x \<cdot> y)"
proof-
  have "do (x \<cdot> do y) = 1 \<sqinter> (x \<cdot> do y \<cdot> \<top>)"
    using do_top by force
  also have "\<dots> = 1 \<sqinter> (x \<cdot> y \<cdot> \<top>)"
    using do_top2 mult_assoc by force
  also have "\<dots> = do (x \<cdot> y)"
    by (simp add: do_top)
  finally show ?thesis
    by force
qed

lemma cd_local [simp]: "cd (cd x \<cdot> y) = cd (x \<cdot> y)"
  by (metis cd_top cd_top2 mult_assoc)

lemma do_fix_subid: "(do x = x) = (x \<le> 1)"
proof
  assume "do x = x"
  thus "x \<le> 1"
    by (metis local.do_subid)
next
  assume a: "x \<le> 1"
  hence "x = do x \<cdot> x"
    by simp
  hence b: "x \<le> do x"
    by (metis a local.mult_isol local.nsrnqo.mult_oner)
  have "x \<cdot> x \<le> x"
    using a local.mult_isor by fastforce
  hence  "do x \<le> x"
    by (simp add: a lla_var local.le_top lra_top_aux)
  thus "do x = x"
    by (simp add: b local.dual_order.antisym)
qed

lemma cd_fix_subid: "(cd x = x) = (x \<le> 1)"
  by (metis local.convdqka.subid_conv local.do_inv local.do_fix_subid local.docd_compat)

lemma do_inf2: "do (do x \<sqinter> do y) = do x \<sqinter> do y"
  using do_top local.do_fix_subid local.inf.assoc by auto

lemma do_inf_comp: "do x \<cdot> do y = do x \<sqinter> do y"
  by (smt (verit, best) local.do_def local.do_idem local.do_fix_subid local.dodo local.dual_order.trans local.inf_commute local.inf_idem local.inv_contrav local.inv_do local.mult_1_right local.mult_isol modular_1 mult_assoc)

lemma cd_inf_comp: "cd x \<cdot> cd y = cd x \<sqinter> cd y"
  by (metis do_inf_comp local.docd_compat)

lemma subid_mult_meet: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<cdot> q = p \<sqinter> q"
  by (metis do_inf_comp local.do_fix_subid)

lemma dodo_sup: "do (do x \<squnion> do y) = do x \<squnion> do y"
proof-
  have "do (do x \<squnion> do y) = 1 \<sqinter> ((do x \<squnion> do y) \<cdot> (do x \<squnion> do y)\<^sup>\<circ>)"
    using local.do_def by blast
  also have "\<dots> = 1 \<sqinter> ((do x \<squnion> do y) \<cdot> (do x \<squnion> do y))"
    by simp
  also have "\<dots> = 1 \<sqinter> (do x \<squnion> do y)"
    using local.do_subid local.dodo local.inf.idem local.le_supI subid_mult_meet by presburger
  also have "\<dots> = do x \<squnion> do y"
    by (simp add: local.do_def local.inf_absorb2)
  finally show ?thesis.
qed

lemma do_sup [simp]: "do (x \<squnion> y) = do x \<squnion> do y"
proof-
  have "do (x \<squnion> y) = 1 \<sqinter> ((x \<squnion> y) \<cdot> \<top>)"
    by (simp add: do_top)
  also have "\<dots> = 1 \<sqinter> (x \<cdot> \<top> \<squnion> y \<cdot> \<top>)"
    by simp
  also have "\<dots> = 1 \<sqinter> (do x \<cdot> \<top> \<squnion> do y \<cdot> \<top>)"
    using do_top2 by force
  also have "\<dots> = 1 \<sqinter> ((do x \<squnion> do y) \<cdot> \<top>)"
    by simp
  also have "\<dots> = do (do x \<squnion> do y)"
    by (simp add: do_top)
  finally show ?thesis
    by (simp add: dodo_sup)
qed

lemma cdcd_sup: "cd (cd x \<squnion> cd y) = cd x \<squnion> cd y"
  using local.cd_fix_subid by fastforce

lemma cd_sup [simp]: "cd (x \<squnion> y) = cd x \<squnion> cd y"
  by (metis do_sup local.do_inv local.inv_binsup)

text \<open>Next we show that Dedekind quantales are modal quantales, hence also modal semirings.\<close>

sublocale dmq: dc_modal_quantale 1 "(\<cdot>)" Inf Sup "(\<sqinter>)" "(\<le>)" "(<)" "(\<squnion>)" "\<bottom>" "\<top>" cd do
proof
  show "\<And>x. cd x \<le> 1"
    by (simp add: cd_top)
  show "\<And>x. do x \<le> 1"
    by (simp add: do_top)
qed simp_all

lemma do_top3 [simp]: "do (x \<cdot> \<top>) = do x"
  using dmq.coddual.le_top dmq.dqmsr.domain_1'' local.do_iso local.order.antisym by presburger

lemma cd_top3 [simp]: "cd (\<top> \<cdot> x) = cd x"
  by (simp add: cd_top dmq.coddual.mult_assoc)

lemma dodo_Sup_pres: "do (\<Squnion>x \<in> X. do x) = (\<Squnion>x \<in> X. do x)"
  by (simp add: local.SUP_least local.do_fix_subid)

text \<open>The domain elements form a complete Heyting algebra.\<close>

lemma do_complete_heyting: "do x \<sqinter> (\<Squnion>y \<in> Y. do y) = (\<Squnion>y \<in> Y. do x \<sqinter> do y)"
proof-
  have "do x \<sqinter> (\<Squnion>y \<in> Y. do y) = do x \<cdot> (\<Squnion>y \<in> Y. do y)"
    by (metis do_inf_comp dodo_Sup_pres)
  also have "\<dots> = (\<Squnion>y \<in> Y. do x \<cdot> do y)"
    by (simp add: dmq.coddual.Sup_distr image_image)
  also have "\<dots> = (\<Squnion>y \<in> Y. do x \<sqinter> do y)"
    using do_inf_comp by force
  finally show ?thesis.
qed

lemma cdcd_Sup_pres: "cd (\<Squnion>x \<in> X. cd x) = (\<Squnion>x \<in> X. cd x)"
  by (simp add: local.SUP_least local.cd_fix_subid)

lemma cd_complete_heyting: "cd x \<sqinter> (\<Squnion>y \<in> Y. cd y) = (\<Squnion>y \<in> Y. cd x \<sqinter> cd y)"
proof-
  have "cd x \<sqinter> (\<Squnion>y \<in> Y. cd y) = cd x \<cdot> (\<Squnion>y \<in> Y. cd y)"
    by (metis cd_inf_comp cdcd_Sup_pres)
  also have "\<dots> = (\<Squnion>y \<in> Y. cd x \<cdot> cd y)"
    by (simp add: dmq.coddual.Sup_distr image_image)
  also have "\<dots> = (\<Squnion>y \<in> Y. cd x \<sqinter> cd y)"
    using cd_inf_comp by force
  finally show ?thesis.
qed

lemma subid_complete_heyting:
  assumes "p \<le> 1"
  and "\<forall>q \<in> Q. q \<le> 1"
  shows "p \<sqinter> (\<Squnion>Q) = (\<Squnion>q \<in> Q. p \<sqinter> q)"
proof-
  have a: "do p = p"
    by (simp add: assms(1) local.do_fix_subid)
  have b: "\<forall>q \<in> Q. do q = q"
    using assms(2) local.do_fix_subid by presburger
  hence "p \<sqinter> (\<Squnion>Q) = do p \<sqinter> (\<Squnion>q \<in> Q. do q)"
    by (simp add: a)
  also have "\<dots> = (\<Squnion>q \<in> Q. do p \<sqinter> do q)"
    using do_complete_heyting by blast
  also have "\<dots> = (\<Squnion>q \<in> Q. p \<sqinter> q)"
    using a b by force
  finally show ?thesis.
qed

text \<open>Next we show that domain and codomain preserve arbitrary Sups.\<close>

lemma do_Sup_pres_aux: "(\<Squnion>x \<in> X. do x \<cdot> \<top>) = (\<Squnion>x \<in> do ` X. x \<cdot> \<top>)"
  by (smt (verit, best) Sup.SUP_cong image_image)

lemma do_Sup_pres: "do (\<Squnion>x \<in> X. x) = (\<Squnion>x \<in> X. do x)"
proof-
  have "do (\<Squnion>x \<in> X. x) = 1 \<sqinter> ((\<Squnion>x \<in> X. x) \<cdot> \<top>)"
    by (simp add: do_top)
  also have "\<dots> = 1 \<sqinter> (\<Squnion>x \<in> X. x \<cdot> \<top>)"
    by (simp add: dmq.coddual.Sup_distl)
  also have "\<dots> = 1 \<sqinter> (\<Squnion>x \<in> X. do x \<cdot> \<top>)"
    using do_top2 by force
  also have "\<dots> = 1 \<sqinter> (\<Squnion>x \<in> do ` X. x \<cdot> \<top>)"
    using do_Sup_pres_aux by presburger
  also have "\<dots> = 1 \<sqinter> ((\<Squnion>x \<in> X. do x) \<cdot> \<top>)"
    using dmq.coddual.Sup_distl by presburger
  also have "\<dots> = do (\<Squnion>x \<in> X. do x)"
    by (simp add: do_top)
  finally show ?thesis
    using dodo_Sup_pres by presburger
qed

lemma cd_Sup_pres: "cd (\<Squnion>x \<in> X. x) = (\<Squnion>x \<in> X. cd x)"
proof-
  have "cd (\<Squnion>x \<in> X. x) = do ((\<Squnion>x \<in> X. x)\<^sup>\<circ>)"
    using local.do_inv by presburger
  also have "\<dots> = do (\<Squnion>x \<in> X. x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = (\<Squnion>x \<in> X. do (x\<^sup>\<circ>))"
    by (metis do_Sup_pres image_ident image_image)
  also have "\<dots> = (\<Squnion>x \<in> X. cd x)"
    using local.do_inv by presburger
  finally show ?thesis.
qed

lemma do_inf: "do (x \<sqinter> y) = 1 \<sqinter> (y \<cdot> x\<^sup>\<circ>)"
  by (smt (z3) do_absorp_eq invqka.inv_one local.do_def local.inf_commute local.inv_binf local.inv_contrav local.inv_invol local.mult_1_right modular_1 modular_2 mult_assoc)

lemma cd_inf: "cd (x \<sqinter> y) = 1 \<sqinter> (y\<^sup>\<circ> \<cdot> x)"
  by (metis do_inf local.do_inv local.inv_binf local.inv_invol)

lemma do_bres_prop: "p \<le> 1 \<Longrightarrow> do (x \<rightarrow> p \<cdot> \<top>) = 1 \<sqinter> (x \<rightarrow> p \<cdot> \<top>)"
  by (simp add: do_top)

lemma cd_fres_prop: "p \<le> 1 \<Longrightarrow> cd (\<top> \<cdot> p \<leftarrow> x) = 1 \<sqinter> (\<top> \<cdot> p \<leftarrow> x)"
  by (simp add: cd_top)

lemma do_meet_prop: "(do p \<cdot> x) \<sqinter> (x \<cdot> do q) = do p \<cdot> x \<cdot> do q"
proof (rule order.antisym)
  have "x \<sqinter> (do p \<cdot> x \<cdot> do q) \<le> do p \<cdot> x"
    by (simp add: dmq.dqmsr.dom_subid_aux2'' local.inf.coboundedI2)
  thus  "(do p \<cdot> x) \<sqinter> (x \<cdot> do q) \<le> do p \<cdot> x \<cdot> do q"
    by (simp add: local.inf.commute modular_eq2)
next
  have "do p \<cdot> x \<cdot> do q = (do p \<cdot> x \<cdot> do q) \<sqinter> (do p \<cdot> x \<cdot> do q)"
    by simp
  also have "\<dots> \<le> (do p \<cdot> x) \<sqinter> (x \<cdot> do q)"
    using dmq.dqmsr.dom_subid_aux2 dmq.dqmsr.dom_subid_aux2'' local.psrpq.mult_isol_var by auto
  finally show "do p \<cdot> x \<cdot> do q \<le> (do p \<cdot> x) \<sqinter> (x \<cdot> do q)".
qed

lemma subid_meet_prop: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> (p \<cdot> x) \<sqinter> (x \<cdot> q) = p \<cdot> x \<cdot> q"
  by (metis do_fix_subid do_meet_prop)

text \<open>Next we consider box and diamond operators like in modal semirings and modal quantales.
These are inherited from domain quantales. Diamonds are defined with respect to domain and codomain.
The box operators are defined as Sups and hence right adjoints of diamonds.\<close>

abbreviation "do_dia \<equiv> dmq.fd'"

abbreviation "cd_dia \<equiv> dmq.bd'"

abbreviation "do_box \<equiv> dmq.bb"

abbreviation "cd_box \<equiv> dmq.fb"

text \<open>In the sense of modal logic, the domain-based diamond is a backward operator, the codomain-based
one a forward operator. These are related by opposition/converse.\<close>

lemma do_dia_cd_dia_conv: "p \<le> 1 \<Longrightarrow> do_dia (x\<^sup>\<circ>) p = cd_dia x p"
  by (simp add: convdqka.subid_conv dmq.coddual.dqmsr.fd_def dmq.dqmsr.fd_def local.cd_def local.do_def)

lemma cd_dia_do_dia_conv: "p \<le> 1 \<Longrightarrow> cd_dia (x\<^sup>\<circ>) p = do_dia x p"
  by (metis do_dia_cd_dia_conv local.inv_invol)

text \<open>Diamonds preserve sups in both arguments.\<close>

lemma do_dia_Sup: "do_dia (\<Squnion>X) p = (\<Squnion>x \<in> X. do_dia x p)"
proof-
  have "do_dia (\<Squnion>X) p = do ((\<Squnion>X) \<cdot> p)"
    by (simp add: dmq.dqmsr.fd_def)
  also have "\<dots> = do (\<Squnion>x \<in> X. x \<cdot> p)"
    using local.Sup_distr by fastforce
 also have "\<dots> = (\<Squnion>x \<in> X. do (x \<cdot> p))"
   by (metis do_Sup_pres image_ident image_image)
  also have "\<dots> = (\<Squnion>x \<in> X. do_dia x p)"
    using dmq.dqmsr.fd_def by fastforce
  finally show ?thesis.
qed

lemma do_dia_Sup2: "do_dia x (\<Squnion>P) = (\<Squnion>p \<in> P. do_dia x p)"
proof-
  have  "do_dia x (\<Squnion>P) = do (x \<cdot> (\<Squnion>P))"
    by (simp add: dmq.dqmsr.fd_def)
  also have "\<dots> = (\<Squnion>p \<in> P. do (x \<cdot> p))"
    by (metis dmq.coddual.Sup_distr do_Sup_pres image_ident image_image)
  also have "\<dots> = (\<Squnion>p \<in> P. do_dia x p)"
    using dmq.dqmsr.fd_def by auto
  finally show ?thesis.
qed

lemma cd_dia_Sup: "cd_dia (\<Squnion>X) p = (\<Squnion>x \<in> X. cd_dia x p)"
proof-
  have "cd_dia (\<Squnion>X) p = cd (p \<cdot> (\<Squnion>X))"
    by (simp add: dmq.coddual.dqmsr.fd_def)
  also have "\<dots> = cd (\<Squnion>x \<in> X. p \<cdot> x)"
    using dmq.coddual.Sup_distr by auto
 also have "\<dots> = (\<Squnion>x \<in> X. cd (p \<cdot> x))"
   by (metis cd_Sup_pres image_ident image_image)
  also have "\<dots> = (\<Squnion>x \<in> X. cd_dia x p)"
    using dmq.coddual.dqmsr.fd_def by force
  finally show ?thesis.
qed

lemma cd_dia_Sup2: "cd_dia x (\<Squnion>P) = (\<Squnion>p \<in> P. cd_dia x p)"
proof-
  have  "cd_dia x (\<Squnion>P) = cd ((\<Squnion>P) \<cdot> x)"
    by (simp add: dmq.coddual.dqmsr.fd_def)
  also have "\<dots> = (\<Squnion>p \<in> P. cd (p \<cdot> x))"
    by (metis cd_Sup_pres dmq.coddual.Sup_distl image_ident image_image)
  also have "\<dots> = (\<Squnion>p \<in> P. cd_dia x p)"
    using dmq.coddual.dqmsr.fd_def by auto
  finally show ?thesis.
qed

text \<open>The domain-based box is a forward operator, the codomain-based on a backward one. These interact
again with respect to converse.\<close>

lemma do_box_var: "p \<le> 1 \<Longrightarrow> do_box x p = \<Squnion>{q. do_dia x q \<le> p \<and> q \<le> 1}"
  by (smt (verit, best) Collect_cong dmq.bb_def dmq.dqmsr.fdia_d_simp local.do_fix_subid local.dodo)

lemma cd_box_var: "p \<le> 1 \<Longrightarrow> cd_box x p = \<Squnion>{q. cd_dia x q \<le> p \<and> q \<le> 1}"
  by (smt (verit, best) Collect_cong dmq.coddual.dqmsr.fdia_d_simp dmq.fb_def local.cd_fix_subid local.cdcd)

lemma do_box_cd_box_conv: "p \<le> 1 \<Longrightarrow> do_box (x\<^sup>\<circ>) p = cd_box x p"
proof-
  assume a: "p \<le> 1"
  hence "do_box (x\<^sup>\<circ>) p = \<Squnion>{q. do_dia (x\<^sup>\<circ>) q \<le> p \<and> q \<le> 1}"
    by (simp add: do_box_var)
  also have "\<dots> =  \<Squnion>{q. cd_dia x q \<le> p \<and> q \<le> 1}"
    by (metis do_dia_cd_dia_conv)
  also have "\<dots> = cd_box x p"
    using a cd_box_var by auto
  finally show ?thesis.
qed

lemma cd_box_do_box_conv: "p \<le> 1 \<Longrightarrow> cd_box (x\<^sup>\<circ>) p = do_box x p"
  by (metis do_box_cd_box_conv local.inv_invol)

lemma do_box_subid: "do_box x p \<le> 1"
  using dmq.bb_def local.Sup_le_iff by force

lemma cd_box_subid: "p \<le> 1 \<Longrightarrow> cd_box x p \<le> 1"
  by (metis do_box_subid local.do_box_cd_box_conv)

text \<open>Next we prove that boxes and diamonds are adjoints, and then demodalisation laws known
from modal semirings.\<close>

lemma do_dia_do_box_galois:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(do_dia x p \<le> q) = (p \<le> do_box x q)"
proof
  show "do_dia x p \<le> q \<Longrightarrow> p \<le> do_box x q"
    by (simp add: assms do_box_var local.Sup_upper)
next
  assume "p \<le> do_box x q"
  hence "do_dia x p \<le> do (x \<cdot> \<Squnion>{t. do_dia x t \<le> q \<and> t \<le> 1})"
    by (simp add: assms(2) local.dmq.dqmsr.fd_def local.do_box_var local.do_iso local.mult_isol)
  also have "\<dots> = \<Squnion>{do (x \<cdot> t) |t. do_dia x t \<le> q \<and> t \<le> 1}"
    by (metis do_Sup_pres image_ident image_image local.Sup_distl setcompr_eq_image)
  also have "\<dots> = \<Squnion>{do_dia x t |t. do_dia x t \<le> q \<and> t \<le> 1}"
    using local.dmq.dqmsr.fd_def by fastforce
  also have "\<dots> \<le> q"
    using local.Sup_le_iff by blast
  finally have "do_dia x p \<le> q".
  thus "p \<le> do_box x q \<Longrightarrow> do_dia x p \<le> q".
qed

lemma cd_dia_cd_box_galois:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(cd_dia x p \<le> q) = (p \<le> cd_box x q)"
  by (metis assms do_box_cd_box_conv do_dia_cd_dia_conv do_dia_do_box_galois)

lemma do_dia_demod_subid:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(do_dia x p \<le> q) = (x \<cdot> p \<le> q \<cdot> x)"
  by (metis assms dmq.dqmsr.fdemodalisation2 local.do_fix_subid)

text \<open>The demodalisation laws have variants based on residuals.\<close>

lemma do_dia_demod_subid_fres:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(do_dia x p \<le> q) = (p \<le> x \<rightarrow> q \<cdot> x)"
  by (simp add: assms do_dia_demod_subid local.bres_galois)

lemma do_dia_demod_subid_var:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(do_dia x p \<le> q) = (x \<cdot> p \<le> q \<cdot> \<top>)"
  by (simp add: assms(2) dmq.dqmsr.fd_def lla)

lemma do_dia_demod_subid_var_fres:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(do_dia x p \<le> q) = (p \<le> x \<rightarrow> q \<cdot> \<top>)"
  by (simp add: assms do_dia_demod_subid_var local.bres_galois)

lemma cd_dia_demod_subid:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(cd_dia x p \<le> q) = (p \<cdot> x \<le> x \<cdot> q)"
  by (metis assms dmq.coddual.dqmsr.fdemodalisation2 local.cd_fix_subid)

lemma cd_dia_demod_subid_fres:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(cd_dia x p \<le> q) = (p \<le> x \<cdot> q \<leftarrow> x)"
  by (simp add: assms cd_dia_demod_subid local.fres_galois)

lemma cd_dia_demod_subid_var:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(cd_dia x p \<le> q) = (p \<cdot> x \<le> \<top> \<cdot> q)"
  by (simp add: assms(2) dmq.coddual.dqmsr.fd_def lra)

lemma cd_dia_demod_subid_var_fres:
  assumes "p \<le> 1"
  and "q \<le> 1"
shows "(cd_dia x p \<le> q) = (p \<le> \<top> \<cdot> q \<leftarrow> x)"
  by (simp add: assms cd_dia_demod_subid_var local.fres_galois)

lemma do_box_iso:
  assumes "p \<le> 1"
  and "q \<le> 1"
  and "p \<le> q"
shows "do_box x p \<le> do_box x q"
  by (meson assms do_box_subid do_dia_do_box_galois local.order.refl local.order.trans)

lemma cd_box_iso:
  assumes "p \<le> 1"
  and "q \<le> 1"
  and "p \<le> q"
shows "cd_box x p \<le> cd_box x q"
  by (metis assms do_box_cd_box_conv do_box_iso)

lemma do_box_demod_subid:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> do_box x q) = (x \<cdot> p \<le> q \<cdot> x)"
  using assms do_dia_do_box_galois local.do_dia_demod_subid by force

lemma do_box_demod_subid_bres:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> do_box x q) = (p \<le> x \<rightarrow> q \<cdot> x)"
  by (simp add: assms do_box_demod_subid local.bres_galois)

lemma do_box_demod_subid_var:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> do_box x q) = (x \<cdot> p \<le> q \<cdot> \<top>)"
  using assms do_dia_demod_subid_var do_dia_do_box_galois by auto

lemma do_box_demod_subid_var_bres:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> do_box x q) = (p \<le> x \<rightarrow> q \<cdot> \<top>)"
  by (simp add: assms do_box_demod_subid_var local.bres_galois)

lemma do_box_demod_subid_var_bres_do:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> do_box x q) = (p \<le> do (x \<rightarrow> q \<cdot> \<top>))"
  by (simp add: assms do_box_demod_subid_var_bres do_top)

lemma cd_box_demod_subid:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> cd_box x q) = (p \<cdot> x \<le> x \<cdot> q)"
  using assms local.cd_dia_cd_box_galois local.cd_dia_demod_subid by force

lemma cd_box_demod_subid_fres:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> cd_box x q) = (p \<le> x \<cdot> q \<leftarrow> x)"
  by (simp add: assms cd_box_demod_subid local.fres_galois)

lemma cd_box_demod_subid_var:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> cd_box x q) = (p \<cdot> x \<le> \<top> \<cdot> q)"
  using assms cd_dia_cd_box_galois cd_dia_demod_subid_var by force

lemma cd_box_demod_subid_var_fres:
  assumes "p \<le> 1"
  and "q \<le> 1"
  shows "(p \<le> cd_box x q) = (p \<le> \<top> \<cdot> q \<leftarrow> x)"
  by (simp add: assms cd_box_demod_subid_var local.fres_galois)

text \<open>We substitute demodalisation inequalities for diamonds in the definitions of boxes.\<close>

lemma do_box_var2: "p \<le> 1 \<Longrightarrow> do_box x p = \<Squnion>{q. x \<cdot> q \<le> p \<cdot> x \<and> q \<le> 1}"
  unfolding do_box_var by (meson do_dia_demod_subid)

lemma do_box_bres1: "p \<le> 1 \<Longrightarrow> do_box x p = \<Squnion>{q. q \<le> x \<rightarrow> p \<cdot> x \<and> q \<le> 1}"
  unfolding do_box_var by (meson do_dia_demod_subid_fres)

lemma do_box_bres2: "p \<le> 1 \<Longrightarrow> do_box x p = \<Squnion>{q. q \<le> x \<rightarrow> p \<cdot> \<top> \<and> q \<le> 1}"
  unfolding do_box_var by (simp add: dmq.dqmsr.fd_def lla local.bres_galois)

lemma do_box_var3: "p \<le> 1 \<Longrightarrow> do_box x p = \<Squnion>{q. x \<cdot> q \<le> p \<cdot> \<top> \<and> q \<le> 1}"
  unfolding do_box_var using dmq.dqmsr.fd_def lla by force

lemma cd_box_var2: "p \<le> 1 \<Longrightarrow> cd_box x p = \<Squnion>{q. q \<cdot> x \<le> x \<cdot> p \<and> q \<le> 1}"
  unfolding cd_box_var by (metis cd_dia_demod_subid)

lemma cd_box_var3: "p \<le> 1 \<Longrightarrow> cd_box x p = \<Squnion>{q. q \<cdot> x \<le> \<top> \<cdot> p \<and> q \<le> 1}"
  unfolding cd_box_var by (simp add: dmq.coddual.dqmsr.fd_def lra)

text \<open>Using these results we get a simple characterisation of boxes via domain and codomain.
Similar laws can be found implicitly in Doornbos, Backhouse and van der Woude's paper on a calculational
approach to mathematical induction, which speaks about wlp operators instead  modal operators.\<close>

lemma bres_do_box: "p \<le> 1 \<Longrightarrow> do_box x p = do (x \<rightarrow> p \<cdot> \<top>)"
  by (meson do_box_demod_subid_var_bres_do do_box_subid local.cd_fix_subid local.cddo_compat local.dual_order.antisym local.eq_refl)

lemma bres_do_box_var: "p \<le> 1 \<Longrightarrow> do_box x p = 1 \<sqinter> (x \<rightarrow> p \<cdot> \<top>)"
  using bres_do_box do_bres_prop by force

lemma bres_do_box_top: "p \<le> 1 \<Longrightarrow> (do_box x p) \<cdot> \<top> = x \<rightarrow> p \<cdot> \<top>"
  using bres_do_box do_top2 by auto

lemma fres_cd_box: "p \<le> 1 \<Longrightarrow> cd_box x p = cd (\<top> \<cdot> p \<leftarrow> x)"
proof-
  assume h0: "p \<le> 1"
  {fix q
  assume h1: "q \<le> 1"
  have "(q \<le> cd_box x p) = (q \<cdot> x \<le> \<top> \<cdot> p)"
    by (simp add: cd_box_demod_subid_var h0 h1)
  also have "\<dots> = (q \<le> \<top> \<cdot> p \<leftarrow> x)"
    by (simp add: local.fres_galois)
  also have "\<dots> = (q \<le> 1 \<sqinter> (\<top> \<cdot> p \<leftarrow> x))"
    by (simp add: h1)
  also have "\<dots> = (q \<le> cd (\<top> \<cdot> p \<leftarrow> x))"
    by (simp add: cd_fres_prop h0)
  finally have "(q \<le> cd_box x p) = (q \<le> cd (\<top> \<cdot> p \<leftarrow> x))".}
  hence "\<forall>y. y \<le> cd_box x p \<longleftrightarrow> y \<le> cd (\<top> \<cdot> p \<leftarrow> x)"
    by (meson cd_box_subid dmq.coddual.dqmsr.dpd3 h0 local.dual_order.trans)
  thus ?thesis
    using local.dual_order.antisym by blast
qed

lemma fres_cd_box_var: "p \<le> 1 \<Longrightarrow> cd_box x p = 1 \<sqinter> (\<top> \<cdot> p \<leftarrow> x)"
  by (simp add: cd_fres_prop fres_cd_box)

lemma fres_cd_box_top: "p \<le> 1 \<Longrightarrow> \<top> \<cdot> cd_box x p = \<top> \<cdot> p \<leftarrow> x"
  using cd_top2 fres_cd_box by auto


text \<open>Next we show that the box operators act on the complete Heyting algebra of subidentities.\<close>

lemma cd_box_act:
  assumes "p \<le> 1"
  shows "cd_box (x \<cdot> y) p = cd_box x (cd_box y p)"
proof-
  {fix q
    assume a: "q \<le> 1"
    hence "(q \<le> cd_box (x \<cdot> y) p) = (cd_dia (x \<cdot> y) q \<le> p)"
      by (simp add: assms cd_dia_cd_box_galois)
    also have "\<dots> = (cd_dia y (cd_dia x q) \<le> p)"
      by (simp add: local.dmq.coddual.dqmsr.fdia_mult)
    also have "\<dots> = (cd_dia x q \<le> cd_box y p)"
      using assms cd_dia_cd_box_galois cd_top dmq.coddual.dqmsr.fd_def by force
    also have "\<dots> = (q \<le> cd_box x (cd_box y p))"
      by (simp add: a assms cd_dia_cd_box_galois local.cd_box_subid)
    finally have "(q \<le> cd_box (x \<cdot> y) p) = (q \<le> cd_box x (cd_box y p))".}
  thus ?thesis
    by (meson assms local.cd_box_subid local.dual_order.eq_iff)
qed

lemma do_box_act:
  assumes "p \<le> 1"
  shows "do_box (x \<cdot> y) p = do_box y (do_box x p)"
  by (smt (verit) assms cd_box_act local.cd_box_do_box_conv local.do_box_subid local.inv_contrav)

text \<open>Next we show that the box operators are Sup reversing in the first and Inf preserving
in the second argument.\<close>

lemma do_box_sup_inf: "p \<le> 1 \<Longrightarrow> do_box (x \<squnion> y) p = do_box x p \<cdot> do_box y p"
proof-
  assume h1: "p \<le> 1"
  {fix q
  assume h2: "q \<le> 1"
  hence "(q \<le> do_box (x \<squnion> y) p) = (do_dia (x \<squnion> y) q \<le> p)"
    by (simp add: do_dia_do_box_galois h1)
  also have "\<dots> = (do_dia x q \<le> p \<and> do_dia y q \<le> p)"
    by (simp add: dmq.dqmsr.fdia_add2)
  also have "\<dots> = (q \<le> do_box x p \<and> q \<le> do_box y p)"
    by (simp add: do_dia_do_box_galois h1 h2)
  also have "\<dots> = (q \<le> do_box x p \<cdot> do_box y p)"
    by (simp add: do_box_subid subid_mult_meet)
  finally have "(q \<le> do_box (x \<squnion> y) p) = (q \<le> do_box x p \<cdot> do_box y p)".}
  hence "\<forall>z. z \<le> do_box (x \<squnion> y) p \<longleftrightarrow> z \<le> do_box x p \<cdot> do_box y p"
    by (metis do_box_subid local.dual_order.trans local.inf.boundedE subid_mult_meet)
  thus ?thesis
    using local.dual_order.antisym by blast
qed

lemma do_box_sup_inf_var: "p \<le> 1 \<Longrightarrow> do_box (x \<squnion> y) p = do_box x p \<sqinter> do_box y p"
  by (simp add: do_box_subid do_box_sup_inf subid_mult_meet)

lemma do_box_Sup_Inf:
  assumes "X \<noteq> {}"
  and "p \<le> 1"
  shows "do_box (\<Squnion>X) p = (\<Sqinter>x \<in> X. do_box x p)"
proof-
  {fix q
    assume h: "q \<le> 1"
    hence "(q \<le> do_box (\<Squnion>X) p) = (do_dia (\<Squnion>X) q \<le> p)"
    by (simp add: do_dia_do_box_galois assms(2))
  also have "\<dots> = ((\<Squnion>x \<in> X. do_dia x q) \<le> p)"
    using do_dia_Sup by force
  also have "\<dots> = (\<forall>x \<in> X. do_dia x q \<le> p)"
    by (simp add: local.SUP_le_iff)
  also have "\<dots> = (\<forall>x \<in> X. q \<le> do_box x p)"
    using do_dia_do_box_galois assms(2) h by blast
  also have "\<dots> = (q \<le> (\<Sqinter>x \<in> X. do_box x p))"
    by (simp add: local.le_INF_iff)
  finally have "(q \<le> do_box (\<Squnion>X) p) = (q \<le> (\<Sqinter>x \<in> X. do_box x p))".}
  hence "\<forall>y. y \<le> do_box (\<Squnion>X) p \<longleftrightarrow> y \<le> (\<Sqinter>x \<in> X. do_box x p)"
    by (smt (verit, ccfv_threshold) assms(1) do_box_subid local.INF_le_SUP local.SUP_least local.order_trans)
  thus ?thesis
    using local.dual_order.antisym by blast
qed

lemma do_box_Sup_Inf2:
  assumes "P \<noteq> {}"
  and "\<forall>p \<in> P. p \<le> 1"
  shows "do_box x (\<Sqinter>P) = (\<Sqinter>p \<in> P. do_box x p)"
proof-
  have h0: "(\<Sqinter>p \<in> P. do_box x p) \<le> 1"
  by (meson all_not_in_conv assms(1) do_box_subid local.INF_lower2)
  {fix q
    assume h1: "q \<le> 1"
    hence "(q \<le> do_box x (\<Sqinter>P)) = (do_dia x q \<le> \<Sqinter>P)"
      by (simp add: assms do_dia_do_box_galois local.Inf_less_eq)
    also have "\<dots> = (\<forall>p \<in> P. do_dia x q \<le> p)"
      using local.le_Inf_iff by blast
    also have "\<dots> = (\<forall>p \<in> P. q \<le> do_box x p)"
      using assms(2) do_dia_do_box_galois h1 by auto
    also have "\<dots> = (q \<le> (\<Sqinter>p \<in> P. do_box x p))"
      by (simp add: local.le_INF_iff)
    finally have "(q \<le> do_box x (\<Sqinter>P)) = (q \<le> (\<Sqinter>p \<in> P. do_box x p))".}
  thus ?thesis
    using do_box_subid h0 local.dual_order.antisym by blast
qed

lemma cd_box_sup_inf: "p \<le> 1 \<Longrightarrow> cd_box (x \<squnion> y) p = cd_box x p \<cdot> cd_box y p"
  by (metis do_box_cd_box_conv do_box_sup_inf local.inv_binsup)

lemma cd_box_sup_inf_var: "p \<le> 1 \<Longrightarrow> cd_box (x \<squnion> y) p = cd_box x p \<sqinter> cd_box y p"
  by (simp add: cd_box_subid cd_box_sup_inf subid_mult_meet)

lemma cd_box_Sup_Inf:
  assumes "X \<noteq> {}"
  and "p \<le> 1"
shows "cd_box (\<Squnion>X) p = (\<Sqinter>x \<in> X. cd_box x p)"
proof-
  have "cd_box (\<Squnion>X) p = do_box ((\<Squnion>X)\<^sup>\<circ>) p"
    using assms(2) do_box_cd_box_conv by presburger
  also have "\<dots> = (\<Sqinter>y \<in> {x\<^sup>\<circ>|x. x \<in> X}. do_box y p)"
    by (simp add: Setcompr_eq_image assms do_box_Sup_Inf)
  also have "\<dots> = (\<Sqinter>x \<in> X. do_box (x\<^sup>\<circ>) p)"
    by (simp add: Setcompr_eq_image image_image)
  also have "\<dots> = (\<Sqinter>x \<in> X. cd_box x p)"
    using assms(2) do_box_cd_box_conv by force
  finally show ?thesis.
qed

lemma cd_box_Sup_Inf2:
  assumes "P \<noteq> {}"
  and "\<forall>p \<in> P. p \<le> 1"
shows "cd_box x (\<Sqinter>P) = (\<Sqinter>p \<in> P. cd_box x p)"
proof-
  have "cd_box x (\<Sqinter>P) = do_box (x\<^sup>\<circ>) (\<Sqinter>P)"
    by (simp add: assms do_box_cd_box_conv local.Inf_less_eq)
  also have "\<dots> = (\<Sqinter>p \<in> P. do_box (x\<^sup>\<circ>) p)"
    using assms do_box_Sup_Inf2 by presburger
  also have "\<dots> = (\<Sqinter>p \<in> P. cd_box x p)"
    using assms(2) do_box_cd_box_conv by force
  finally show ?thesis.
qed

text \<open>Next we define an antidomain operation in the style of modal semirings. A natural condition is
that the antidomain of an element is the greatest test that cannot be left-composed with that elements,
and hence a greatest left annihilator. The definition of anticodomain is similar. As we are not in a
boolean domain algebra, we cannot expect that the antidomain of the antidomain yields the domain or
that the union of a domain element with the corresponding antidomain element equals one.\<close>

definition "ado x = \<Squnion>{p. p \<cdot> x = \<bottom> \<and> p \<le> 1}"

definition "acd x = \<Squnion>{p. x \<cdot> p = \<bottom> \<and> p \<le> 1}"

lemma ado_acd: "ado (x\<^sup>\<circ>) = acd x"
  unfolding ado_def acd_def
  by (metis convdqka.subid_conv invqka.inv_zero local.inv_contrav local.inv_invol)

lemma acd_ado: "acd (x\<^sup>\<circ>) = ado x"
  unfolding ado_def acd_def
  by (metis acd_def ado_acd ado_def local.inv_invol)

lemma ado_left_zero [simp]: "ado x \<cdot> x = \<bottom>"
  unfolding ado_def
  using dmq.coddual.Sup_distl by auto

lemma acd_right_zero [simp]: "x \<cdot> acd x = \<bottom>"
  unfolding acd_def
  by (simp add: dmq.coddual.h_Sup local.dual_order.antisym)

lemma ado_greatest: "p \<le> 1 \<Longrightarrow> p \<cdot> x = \<bottom> \<Longrightarrow> p \<le> ado x"
  by (simp add: ado_def local.Sup_upper)

lemma acd_greatest: "p \<le> 1 \<Longrightarrow> x \<cdot> p = \<bottom> \<Longrightarrow> p \<le> acd x"
  by (simp add: acd_def local.Sup_upper)

lemma ado_subid: "ado x \<le> 1"
  using ado_def local.Sup_le_iff by force

lemma acd_subid: "acd x \<le> 1"
  by (simp add: acd_def local.Sup_le_iff)

lemma ado_left_zero_iff: "p \<le> 1 \<Longrightarrow> (p \<le> ado x) = (p \<cdot> x = \<bottom>)"
  by (metis ado_greatest ado_left_zero local.bot_unique local.mult_isor)

lemma acd_right_zero_iff: "p \<le> 1 \<Longrightarrow> (p \<le> acd x) = (x \<cdot> p = \<bottom>)"
  by (metis acd_greatest acd_right_zero local.bot_unique local.mult_isol)

text \<open>This gives an eqational characterisation of antidomain and anticodomain.\<close>

lemma ado_cd_bot: "ado x = cd (\<bottom> \<leftarrow> x)"
proof-
  {fix p
  assume  h: "p \<le> 1"
  hence "(p \<le> ado x) = (p \<cdot> x = \<bottom>)"
    by (simp add: ado_left_zero_iff)
  also have "\<dots> = (p \<le> \<bottom> \<leftarrow> x)"
    using local.bot_unique local.fres_galois by blast
  also have "\<dots> = (p \<le> 1 \<sqinter> (\<bottom> \<leftarrow> x))"
    by (simp add: h)
  also have "\<dots> = (p \<le> cd (\<bottom> \<leftarrow> x))"
    by (metis cd_fres_prop local.bot_least local.mult_botr)
  finally have "(p \<le> ado x) = (p \<le> cd (\<bottom> \<leftarrow> x))".}
  hence "\<forall>y. y \<le> ado x \<longleftrightarrow> y \<le> cd (\<bottom> \<leftarrow> x)"
    using ado_subid local.cd_subid local.dual_order.trans by blast
  thus ?thesis
    using local.dual_order.antisym by blast
qed

lemma acd_do_bot: "acd x = do (x \<rightarrow> \<bottom>)"
  by (metis ado_acd ado_cd_bot invqka.inv_zero local.bres_fres_conv local.cd_inv local.inv_invol)

lemma ado_cd_bot_id: "ado x = 1 \<sqinter> (\<bottom> \<leftarrow> x)"
  by (metis ado_cd_bot cd_fres_prop local.cd_bot local.cd_subid local.mult_botr)

lemma acd_do_bot_id: "acd x = 1 \<sqinter> (x \<rightarrow> \<bottom>)"
  by (metis acd_do_bot do_bres_prop local.bot_least local.mult_botl)

lemma ado_cd_bot_var: "ado x = cd (\<bottom> \<leftarrow> do x)"
  by (metis ado_cd_bot do_top2 local.fres_bot_top local.fres_curry)

lemma acd_do_bot_var: "acd x = do (cd x \<rightarrow> \<bottom>)"
  by (metis acd_do_bot cd_top2 local.bres_curry local.bres_top_bot)

lemma ado_do_bot: "ado x = do (do x \<rightarrow> \<bottom>)"
  using acd_ado acd_do_bot_var local.cd_inv by auto

lemma "do x = ado (ado x)" (* nitpick[expect=genuine]*)
  oops

lemma acd_cd_bot: "acd x = cd (\<bottom> \<leftarrow> cd x)"
  by (metis ado_acd ado_cd_bot_var local.cd_inv local.inv_invol)

lemma ado_do_bot_var: "ado x = 1 \<sqinter> (do x \<rightarrow> \<bottom>)"
  by (metis ado_do_bot do_bres_prop local.bot_unique local.bres_bot_bot local.bres_canc1 local.do_bot local.do_subid)

 lemma acd_cd_bot_var: "acd x = 1 \<sqinter> (\<bottom> \<leftarrow> cd x)"
   by (metis acd_cd_bot acd_right_zero cd_top local.fres_top_top2)


text \<open>Domain and codomain are compatible with the boxes.\<close>

lemma cd_box_ado: "cd_box x \<bottom> = ado x"
  by (simp add: ado_cd_bot fres_cd_box)

lemma do_box_acd: "do_box x \<bottom> = acd x"
  by (simp add: acd_do_bot bres_do_box)

lemma ado_subid_prop: "p \<le> 1 \<Longrightarrow> ado p = 1 \<sqinter> (p \<rightarrow> \<bottom>)"
  by (metis ado_do_bot_var do_fix_subid)

lemma ado_do: "p \<le> 1 \<Longrightarrow> ado p = do (p \<rightarrow> \<bottom>)"
  using ado_do_bot do_fix_subid by force

lemma ado_do_compl: "ado x \<cdot> do x = \<bottom>"
  using dmq.dqmsr.dom_weakly_local by force

lemma "ado x \<squnion> do x = \<top>" (* nitpick[expect = genuine]*)
  oops

lemma "\<forall>x p. \<exists>f. 1 \<sqinter> (\<top> \<cdot> p \<leftarrow> x) = 1 \<sqinter> (\<bottom> \<leftarrow> (x \<rightarrow> p \<cdot> \<top>))" (* nitpick[expect=genuine]*)
  oops

lemma "cd_box x p = ado (x \<cdot> ado p)" (* nitpick[expect=genuine]*)
  oops

lemma ad_do_bot [simp]: "(1 \<sqinter> (do x \<rightarrow> \<bottom>)) \<cdot> do x = \<bottom>"
  using ado_do_bot_var ado_left_zero dmq.dqmsr.dom_weakly_local by presburger

lemma do_heyting_galois: "(do x \<cdot> do y \<le> do z) = (do x \<le> 1 \<sqinter> (do y \<rightarrow> do z))"
  by (metis dmq.dqmsr.dsg4 dmq.mqdual.cod_subid local.bres_galois local.le_inf_iff)

lemma do_heyting_galois_var: "(do x \<cdot> do y \<le> do z) = (do x \<le> cd_box (do y) (do z))"
  by (metis cd_dia_cd_box_galois cd_fix_subid dmq.coddual.dqmsr.fd_def dmq.dqmsr.dom_mult_closed local.do_subid)

text \<open>Antidomain is therefore Heyting negation.\<close>

lemma ado_heyting_negation: "ado (do x) = cd_box (do x) \<bottom>"
  by (simp add: cd_box_ado)

lemma ad_ax1 [simp]: "(1 \<sqinter> (do x \<rightarrow> \<bottom>)) \<cdot> x = \<bottom>"
  by (simp add: local.dmq.dqmsr.dom_weakly_local)

lemma "1 \<sqinter> (do (1 \<sqinter> (do x \<rightarrow> \<bottom>)) \<rightarrow> \<bottom>) = do x" (* nitpick[expect=genuine]*)
  oops

lemma "p \<le> 1 \<Longrightarrow> do_dia x p = 1 \<sqinter> (cd_box x (1 \<sqinter> (p \<rightarrow> \<bottom>)) \<rightarrow> \<bottom>)" (* nitpick[expect=genuine]*)
  oops

lemma  "p \<le> 1 \<Longrightarrow> cd_box x p = 1 \<sqinter> (do_dia x (1 \<sqinter> (p \<rightarrow> \<bottom>)) \<rightarrow> \<bottom>)" (* nitpick[expect=genuine]*)
  oops

lemma "p \<le> 1 \<Longrightarrow> cd_dia x p = 1 \<sqinter> (do_box x (1 \<sqinter> (p \<rightarrow> \<bottom>)) \<rightarrow> \<bottom>)" (* nitpick[expect=genuine]*)
  oops

lemma "p \<le> 1 \<Longrightarrow> do_box x p = 1 \<sqinter> (cd_dia x (1 \<sqinter> (p \<rightarrow> \<bottom>)) \<rightarrow> \<bottom>)" (* nitpick[expect=genuine]*)
  oops

end

subsection \<open>Boolean Dedekind quantales\<close>

class distributive_dedekind_quantale = distrib_unital_quantale + dedekind_quantale

class boolean_dedekind_quantale = bool_unital_quantale + distributive_dedekind_quantale

begin

lemma ad_do_bot [simp]: "(1 - do x) \<cdot> do x = \<bottom>"
  by (simp add: local.diff_eq local.inf_shunt local.subid_mult_meet)

lemma ad_ax1 [simp]: "(1 - do x) \<cdot> x = \<bottom>"
  by (simp add: local.dmq.dqmsr.dom_weakly_local)

lemma ad_do [simp]: "1 - do (1 - do x) = do x"
proof-
  have "1 - do (1 - do x) = 1 - (1 - do x)"
    by (metis local.diff_eq local.do_fix_subid local.inf.cobounded1)
  also have "\<dots> = 1 \<sqinter> -(1 \<sqinter> - do x)"
    by (simp add: local.diff_eq)
  also have "\<dots> = do x"
    by (simp add: local.chaq.wswq.distrib_left local.do_top)
  finally show ?thesis.
qed

lemma ad_ax2: "1 - do (x \<cdot> y) \<squnion> (1 - do (x \<cdot> (1 - do (1 - do y)))) = 1 - do (x \<cdot> (1 - do (1 - do y)))"
  by simp

lemma ad_ax3 [simp]: "do x \<squnion> (1 - do x) = 1"
proof-
  have "do x \<squnion> (1 - do x) = do x \<squnion> (1 \<sqinter> -do x)"
    using local.diff_eq by force
  also have "\<dots> = 1 \<sqinter> (do x \<squnion> -do x)"
    by (simp add: local.chaq.wswq.distrib_left local.do_top)
  also have "\<dots> = 1"
    by simp
  finally show ?thesis.
qed

sublocale bdad: antidomain_semiring "\<lambda>x. 1 - do x" "(\<squnion>)" "(\<cdot>)" 1 \<bottom> _ _
  by unfold_locales simp_all

sublocale bdadka: antidomain_kleene_algebra "\<lambda>x. 1 - do x" "(\<squnion>)" "(\<cdot>)" 1 \<bottom> _ _ qstar..

sublocale bdar: antirange_semiring "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "\<lambda>x. 1 - cd x" _ _
  apply unfold_locales
    apply (metis ad_ax1 ad_do dmq.mqs.local_var local.docd_compat)
   apply (metis ad_do local.cddo_compat local.dmq.coddual.dqmsr.dsr2 local.docd_compat local.sup.idem)
  by (metis bdad.a_subid' bdad.as3 local.convdqka.subid_conv local.do_inv)

sublocale bdaka: antirange_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> _ _ qstar "\<lambda>x. 1 - cd x"..

sublocale bmod: modal_semiring_simp "\<lambda>x. 1 - do x" "(\<squnion>)" "(\<cdot>)" 1 \<bottom> _ _ "\<lambda>x. 1 - cd x"..

sublocale bmod: modal_kleene_algebra_simp "(\<squnion>)" "(\<cdot>)" 1 \<bottom> _ _ qstar "\<lambda>x. 1 - do x" "\<lambda>x. 1 - cd x"..

lemma inv_neg: "(-x)\<^sup>\<circ> = -(x\<^sup>\<circ>)"
  by (metis local.diff_eq local.diff_shunt_var local.dual_order.eq_iff local.inf.commute local.inv_conjugate local.inv_galois)

lemma residuation: "x\<^sup>\<circ> \<cdot> -(x \<cdot> y) \<le> -y"
  by (metis local.inf.commute local.inf_compl_bot local.inf_shunt local.schroeder_1)

lemma bres_prop: "x \<rightarrow> y = -(x\<^sup>\<circ> \<cdot> -y)"
  by (metis local.ba_dual.dual_iff local.bres_canc1 local.bres_galois_imp local.compl_le_swap1 local.dmq.coddual.h_w1 local.dual_order.antisym local.inv_invol residuation)

lemma fres_prop: "x \<leftarrow> y = -(-x \<cdot> y\<^sup>\<circ>)"
  using bres_prop inv_neg local.fres_bres_conv by auto

lemma do_dia_fdia: "do_dia x p = bdad.fdia x p"
  by (simp add: local.bdad.fdia_def local.dmq.dqmsr.fd_def)

lemma cd_dia_bdia: "cd_dia x p = bdar.bdia x p"
  by (metis ad_do bdar.ardual.a_subid' bdar.bdia_def local.cd_fix_subid local.dmq.coddual.dqmsr.fd_def local.docd_compat)

lemma do_dia_fbox_de_morgan: "p \<le> 1 \<Longrightarrow> do_dia x p = 1 - bdad.fbox x (1 - p)"
  by (smt (verit, ccfv_SIG) ad_do bdad.a_closure bdad.am_d_def bdad.fbox_def local.dmq.dqmsr.fd_def local.do_fix_subid)

lemma fbox_do_dia_de_morgan: "p \<le> 1 \<Longrightarrow> bdad.fbox x p = 1 - do_dia x (1 - p)"
  using bdad.fbox_def local.dmq.dqmsr.fd_def local.do_fix_subid by force

lemma cd_dia_bbox_de_morgan: "p \<le> 1 \<Longrightarrow> cd_dia x p = 1 - bdar.bbox x (1 - p)"
  by (smt (verit, best) ad_do bdar.bbox_def bdar.bdia_def cd_dia_bdia local.cd_fix_subid local.do_subid local.docd_compat)

lemma bbox_cd_dia_de_morgan: "p \<le> 1 \<Longrightarrow> bdar.bbox x p = 1 - cd_dia x (1 - p)"
  using bdar.bbox_def local.cd_fix_subid local.dmq.coddual.dqmsr.fd_def by force

lemma do_box_bbox: "p \<le> 1 \<Longrightarrow> do_box x p = bdar.bbox x p"
proof-
  assume a: "p \<le> 1"
  {fix q
  assume b: "q \<le> 1"
  hence "(q \<le> do_box x p) = (x \<cdot> q \<le> p \<cdot> x)"
    by (simp add: a local.do_box_demod_subid)
  also have "\<dots> = (x \<cdot> cd q \<le> cd p \<cdot> x)"
    by (metis a b local.cd_fix_subid)
  also have "\<dots> = (cd q \<le> bdar.bbox x p)"
   by (metis bdar.bbox_def bdar.bdia_def cd_dia_bdia local.bdar.ardual.a_closure' local.bdar.ardual.ans_d_def local.bdar.ardual.dnsz.dsg1 local.bdar.ardual.fbox_demodalisation3 local.bdar.ardual.fbox_one local.dmq.coddual.dqmsr.fd_def local.nsrnqo.mult_oner)
  also have "\<dots> = (q \<le> bdar.bbox x p)"
    using b local.cd_fix_subid by force
  finally have "(q \<le> do_box x p) = (q \<le> bdar.bbox x p)".}
  thus ?thesis
    by (metis bdar.bbox_def local.bdar.ardual.a_subid' local.do_box_subid local.dual_order.antisym local.eq_refl)
qed

lemma cd_box_fbox: "p \<le> 1 \<Longrightarrow> cd_box x p = bdad.fbox x p"
  by (smt (verit, ccfv_SIG) bdar.bbox_def do_box_bbox local.bdad.fbox_def local.cd_dia_do_dia_conv local.cd_inv local.cd_fix_subid local.cd_top local.diff_eq local.dmq.bb_def local.dmq.coddual.dqmsr.fd_def local.dmq.coddual.mult_assoc local.dmq.dqmsr.fd_def local.dmq.fb_def local.do_box_cd_box_conv local.do_fix_subid local.do_top local.inf.cobounded1)

lemma do_dia_cd_box_de_morgan: "p \<le> 1 \<Longrightarrow> do_dia x p = 1 - cd_box x (1 - p)"
  by (simp add: cd_box_fbox local.diff_eq local.do_dia_fbox_de_morgan)

lemma cd_box_do_dia_de_morgan: "p \<le> 1 \<Longrightarrow> cd_box x p = 1 - do_dia x (1 - p)"
  by (simp add: cd_box_fbox local.fbox_do_dia_de_morgan)

lemma cd_dia_do_box_de_morgan: "p \<le> 1 \<Longrightarrow> cd_dia x p = 1 - do_box x (1 - p)"
  by (simp add: do_box_bbox local.cd_dia_bbox_de_morgan local.diff_eq)

lemma do_box_cd_dia_de_morgan: "p \<le> 1 \<Longrightarrow> do_box x p = 1 - cd_dia x (1 - p)"
  by (simp add: do_box_bbox local.bbox_cd_dia_de_morgan)

end

class dc_involutive_modal_quantale = dc_modal_quantale + involutive_quantale

begin

sublocale invmqmka: involutive_dr_modal_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar invol dom cod..

lemma do_approx_dom: "do x \<le> dom x"
proof -
  have "do x = dom (do x) \<cdot> do x"
    by simp
  also have "\<dots> \<le> dom (1 \<sqinter> (x \<cdot> x\<^sup>\<circ>))"
    by (simp add: local.do_def local.dqmsr.domain_subid)
  also have "\<dots> \<le> dom 1 \<sqinter> dom (x \<cdot>  x\<^sup>\<circ>)"
    using local.dom_meet_sub by presburger
  also have "\<dots> \<le> dom (x \<cdot> dom (x\<^sup>\<circ>))"
    by simp
  also have "\<dots> \<le> dom x"
    by (simp add: local.dqmsr.domain_1'')
  finally show ?thesis.
qed

end

class dc_modal_quantale_converse = dc_involutive_modal_quantale + quantale_converse

sublocale dc_modal_quantale_converse \<subseteq> invmqmka: dr_modal_kleene_algebra_converse  "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar invol dom cod..

class dc_modal_quantale_strong_converse = dc_involutive_modal_quantale +
  assumes weak_dom_def: "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  and weak_cod_def: "cod x \<le> x\<^sup>\<circ> \<cdot> x"

begin

sublocale invmqmka: dr_modal_kleene_algebra_strong_converse  "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar invol dom cod
  by (unfold_locales, simp_all add: local.weak_dom_def local.weak_cod_def)

lemma dom_def: "dom x = 1 \<sqinter> (x \<cdot> x\<^sup>\<circ>)"
  using local.do_approx_dom local.do_def local.dual_order.eq_iff local.weak_dom_def by force

lemma cod_def: "cod x = 1 \<sqinter> (x\<^sup>\<circ> \<cdot> x)"
  using local.dom_def local.invmqmka.d_conv_cod by auto

lemma do_dom: "do x = dom x"
  by (simp add: local.do_def local.dom_def)

lemma cd_cod: "cd x = cod x"
  by (simp add: local.cd_def local.cod_def)

end

class dc_modal_dedekind_quantale = dc_involutive_modal_quantale + dedekind_quantale

class cd_distributive_modal_dedekind_quantale = dc_modal_dedekind_quantale + distrib_unital_quantale

class dc_boolean_modal_dedekind_quantale = dc_modal_dedekind_quantale + bool_unital_quantale

begin

lemma subid_idem: "p \<le> 1 \<Longrightarrow> p \<cdot> p = p"
  by (simp add: local.subid_mult_meet)

lemma subid_comm: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<cdot> q = q \<cdot> p"
  using local.inf.commute local.subid_mult_meet by force

lemma subid_meet_comp: "p \<le> 1 \<Longrightarrow> q \<le> 1 \<Longrightarrow> p \<sqinter> q = p \<cdot> q"
  by (simp add: local.subid_mult_meet)

lemma subid_dom: "p \<le> 1 \<Longrightarrow> dom p = p"
proof-
  assume h: "p \<le> 1"
  have a: "p \<squnion> (1 \<sqinter> -p) = 1"
    by (metis h local.inf_sup_absorb local.sup.commute local.sup.orderE local.sup_compl_top local.sup_inf_distrib1)
  have b: "(1 \<sqinter> -p) \<sqinter> p = \<bottom>"
    by (simp add: local.inf.commute)
  hence "dom p = (p \<squnion> (1 \<sqinter> -p)) \<cdot> dom p"
    by (simp add: a)
  also have "\<dots> = p \<cdot> dom p \<squnion> dom ((1 \<sqinter> -p) \<cdot> dom p) \<cdot> (1 \<sqinter> -p) \<cdot> dom p"
    using local.dqmsr.dsg1 local.wswq.distrib_right mult_assoc by presburger
  also have "\<dots> \<le> p \<squnion> dom ((1 \<sqinter> -p) \<cdot> dom p)"
    by (metis b h local.dom_subid local.dom_zero local.inf.cobounded1 local.mqdual.cod_local local.mult_botr local.sup.mono subid_comm subid_meet_comp)
  also have "\<dots> = p \<squnion> dom ((1 \<sqinter> -p) \<cdot> p)"
    by simp
  also have "\<dots> = p \<squnion> dom \<bottom>"
    using b h subid_meet_comp by fastforce
  also have "\<dots> = p"
    by simp
  finally have "dom p \<le> p".
  thus ?thesis
    using h local.dqmsr.domain_subid local.dual_order.antisym by presburger
qed

lemma do_prop: "(do x \<le> do y) = (x \<le> do y \<cdot> \<top>)"
  by (simp add: local.lla)

lemma do_lla: "(do x \<le> do y) = (x \<le> do y \<cdot> x)"
  by (simp add: local.lla_var)

lemma lla_subid: "p \<le> 1 \<Longrightarrow> ((dom x \<le> p) = (x \<le> p \<cdot> x))"
  by (metis local.dqmsr.dom_llp subid_dom)

lemma dom_do: "dom x = do x"
proof-
  have "x \<le> do x \<cdot> x"
    by simp
  hence "dom x \<le> do x"
    using lla_subid local.do_subid local.dodo by presburger
  thus ?thesis
    by (simp add: local.antisym_conv local.do_approx_dom)
qed

end

end

