(* Title:      Demonic refinement algebra
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)


header {* Basis for Demonic Refinement Algebras  *}

theory DRA_Base
  imports "$AFP/Kleene_Algebra/Kleene_Algebra"
begin

text {*
  Demonic refinement algebra is based on a Kleene algebra without the right annihilation law $x \cdot 0 = 0$.
  In the Archive~\cite{ArmstrongSW13}, only left Kleene algebras without the right annihilation law exist. So we need to define
  an expansion.
*}
class kleene_algebra_zerol = left_kleene_algebra_zerol + 
  assumes star_inductr: "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
begin

text {*
  These lemmas were copied from AFP (Kleene Algebra).
  They are also valid without right annihilation.
*}

lemma star_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (metis add_lub order_refl star_inductr)

lemma star_inductr_var_equiv: "y \<cdot> x \<le> y \<longleftrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (metis order_trans mult_isol star_ext star_inductr_var)

lemma star_sim2: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
proof -
  assume "z \<cdot> x \<le> y \<cdot> z"
  hence "y\<^sup>\<star> \<cdot> z \<cdot> x \<le> y\<^sup>\<star> \<cdot> y \<cdot> z"
    by (metis distrib_left less_eq_def mult_assoc)
  also have "... \<le> y\<^sup>\<star> \<cdot> z"
    by (metis (full_types) mult_isor star_1l star_slide_var)
  hence "z + y\<^sup>\<star> \<cdot> z \<cdot> x \<le> y\<^sup>\<star> \<cdot> z"
    by (metis add_lub_var calculation mult_isor mult_onel order_trans star_ref)
  thus "z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
    by (metis mult.assoc star_inductr)
qed

lemma star_sim3: "z \<cdot> x = y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> = y\<^sup>\<star> \<cdot> z"
  by (metis eq_iff star_sim1 star_sim2)

lemma star_sim4: "x \<cdot> y \<le>  y \<cdot> x \<Longrightarrow> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  by (metis star_sim1 star_sim2)

lemma star_inductr_eq: "z + y \<cdot> x = y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  by (metis eq_iff star_inductr)

lemma star_inductr_var_eq: "y \<cdot> x = y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (metis eq_iff star_inductr_var)

lemma star_inductr_var_eq2: "y \<cdot> x = y \<Longrightarrow> y \<cdot> x\<^sup>\<star> = y"
  by (metis mult_onel star_one star_sim3)

lemma bubble_sort: "y \<cdot> x \<le> x \<cdot> y \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis church_rosser star_sim4)

lemma independence1: "x \<cdot> y = 0 \<Longrightarrow> x\<^sup>\<star> \<cdot> y = y"
proof -
  assume "x \<cdot> y = 0"
  also have "x\<^sup>\<star> \<cdot> y = y + x\<^sup>\<star> \<cdot> x \<cdot> y"
    by (metis distrib_right mult_onel star_unfoldr_eq)
  thus "x\<^sup>\<star> \<cdot> y = y"
    by (metis add_0_left add_commute add_ub1 calculation eq_iff star_inductl_eq)
qed

lemma independence2: "x \<cdot> y = 0 \<Longrightarrow> x \<cdot> y\<^sup>\<star> = x"
  by (metis annil mult_onel star_sim3 star_zero)

lemma lazycomm_var: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y \<longleftrightarrow> y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
proof
  let ?t = "x \<cdot> (x + y)\<^sup>\<star>"
  assume "y \<cdot> x \<le> ?t + y"
  also have "(?t + y) \<cdot> x = ?t \<cdot> x + y \<cdot> x"
    by (metis distrib_right)
  moreover have "... \<le> ?t \<cdot> x + ?t + y"
    by (metis add_iso_var calculation le_less add_assoc)
  moreover have "... \<le> ?t + y"
    by (metis add_iso_var add_lub_var mult.assoc mult_isol order_refl prod_star_closure star_subdist_var_1)
  hence "y + (?t + y) \<cdot> x \<le> ?t + y"
    by (metis add.commute add_lub_var add_ub1 calculation less_eq_def mult.assoc distrib_left star_subdist_var_1 star_trans_eq)
  thus "y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
    by (metis star_inductr)
next
  assume "y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
  thus "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
    by (metis mult_isol order_trans star_ext)
qed

lemma arden_var: "(\<forall>y v. y \<le> x \<cdot> y + v \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> v) \<Longrightarrow> z = x \<cdot> z + w \<longrightarrow> z = x\<^sup>\<star> \<cdot> w"
  by (metis add_comm eq_iff star_inductl_eq)

lemma "(\<forall>x y. y \<le> x \<cdot> y \<longrightarrow> y = 0) \<Longrightarrow> y \<le> x \<cdot> y + z \<Longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z"
  by (metis eq_refl mult_onel)
end

end
