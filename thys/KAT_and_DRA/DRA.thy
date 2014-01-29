(* Title:      Demonic refinement algebra
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

header {* Demonic Refinement Algebras *}

theory DRA
  imports DRA_Base
begin

text {*
  A demonic refinement algebra~\cite{Wright02} is a Kleene algebra without right annihilation plus 
  an operation for possibly infinite iteration.
*}
class dra = kleene_algebra_zerol +
  fixes strong_iteration :: "'a \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [101] 100)
  assumes iteration_unfoldl [simp] : "1 + x \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
  and coinduction: "y \<le> z + x \<cdot> y \<longrightarrow> y \<le> x\<^sup>\<infinity> \<cdot> z"
  and isolation [simp]: "x\<^sup>\<star> + x\<^sup>\<infinity>\<cdot>0 = x\<^sup>\<infinity>"
begin

text {* $\top$ is an abort statement, defined as an infinite skip. It is the maximal element of any DRA. *}

abbreviation top_elem :: "'a" ("\<top>") where "\<top> \<equiv> 1\<^sup>\<infinity>"

text {* Simple/basic lemmas about iteration operator *}

lemma iteration_refl: "1 \<le> x\<^sup>\<infinity>"
  by (metis add_ub1 iteration_unfoldl)

lemma top_ref: "x \<le> \<top>"
  by (metis add_idem' add_lub add_ub1 mult_1_left mult_1_right coinduction)

lemma top_mult_annil[simp]: "\<top>\<cdot>x = \<top>"
  by (metis add_ub2 eq_iff mult_1_left coinduction top_ref)

lemma top_add_annil[simp]: "\<top> + x = \<top>"
  by (metis add_commute less_eq_def top_ref)

lemma top_elim: "x\<cdot>y \<le> x\<cdot>\<top>"
  by (metis mult_isol top_ref)  

lemma iteration_unfoldl_distl: "y\<cdot>x\<^sup>\<infinity> = y + y\<cdot>x\<cdot>x\<^sup>\<infinity>"
  by (metis distrib_left mult_assoc mult_oner iteration_unfoldl)

lemma iteration_unfoldl_distr: "x\<^sup>\<infinity>\<cdot>y = y + x\<cdot>x\<^sup>\<infinity>\<cdot>y"
  by (metis distrib_right' mult_1_left iteration_unfoldl)

lemma iteration_unfoldl': "z\<cdot>x\<^sup>\<infinity>\<cdot>y = z\<cdot>y + z\<cdot>x\<cdot>x\<^sup>\<infinity>\<cdot>y"
  by (metis distrib_left mult_assoc iteration_unfoldl_distr)

lemma iteration_idem[simp]: "x\<^sup>\<infinity>\<cdot>x\<^sup>\<infinity> = x\<^sup>\<infinity>"
  by (metis add_zerol annil isolation mult_assoc iteration_refl iteration_unfoldl_distr star_inductl_var_eq2 star_invol star_sum_unfold sup_id_star1)

lemma iteration_induct: "x\<cdot>x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>x"
  by (metis eq_iff mult_assoc coinduction iteration_unfoldl_distl)

lemma iteration_ref_star: "x\<^sup>\<star> \<le> x\<^sup>\<infinity>"
  by (metis eq_refl iteration_unfoldl star_inductl_one)

lemma iteration_subdist: "x\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
  by (metis add_assoc' distrib_right' mult_oner coinduction add_ub1 iteration_unfoldl)

lemma iteration_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<infinity> \<le> y\<^sup>\<infinity>"
  by (metis iteration_subdist order_prop)

lemma iteration_unfoldr: "1 + x\<^sup>\<infinity> \<cdot> x = x\<^sup>\<infinity>"
  by (metis add_0_left annil eq_refl isolation mult_assoc iteration_idem iteration_unfoldl iteration_unfoldl_distr star_denest star_one star_prod_unfold star_slide tc)

lemma iteration_unfoldr_distl: "y\<cdot>x\<^sup>\<infinity> = y + y\<cdot>x\<^sup>\<infinity>\<cdot>x"
  by (metis distrib_left mult_assoc mult_oner iteration_unfoldr)

lemma iteration_unfoldr_distr: "x\<^sup>\<infinity>\<cdot>y = y + x\<^sup>\<infinity>\<cdot>x\<cdot>y"
  by (metis iteration_unfoldl_distr iteration_unfoldr_distl)

lemma iteration_unfold_eq: "x\<^sup>\<infinity>\<cdot>x = x\<cdot>x\<^sup>\<infinity>"
  by (metis iteration_unfoldl_distr iteration_unfoldr_distl)
  
lemma iteration_unfoldr': "z\<cdot>x\<^sup>\<infinity>\<cdot>y = z\<cdot>y + z\<cdot>x\<^sup>\<infinity>\<cdot>x\<cdot>y"
  by (metis distrib_left mult_assoc iteration_unfoldr_distr)

lemma iteration_double[simp]: "(x\<^sup>\<infinity>)\<^sup>\<infinity> = \<top>"
  by (metis less_eq_def iteration_iso iteration_refl top_add_annil)

lemma star_iteration[simp]: "(x\<^sup>\<star>)\<^sup>\<infinity> = \<top>"
  by (metis less_eq_def iteration_iso star_ref top_add_annil)

lemma iteration_star[simp]: "(x\<^sup>\<infinity>)\<^sup>\<star> = x\<^sup>\<infinity>"
  by (metis boffa less_eq_def iteration_idem iteration_refl)

lemma iteration_star2[simp]: "x\<^sup>\<star>\<cdot>x\<^sup>\<infinity> = x\<^sup>\<infinity>"
  by (metis add_assoc boffa isolation mult_1_right iteration_idem iteration_unfoldl star_denest star_denest_var_2 star_invol star_slide star_zero)

lemma iteration_zero[simp]: "0\<^sup>\<infinity> = 1"
  by (metis add_zeror annil iteration_unfoldl)

lemma iteration_annil[simp]: "(x\<cdot>0)\<^sup>\<infinity> = 1 + x\<cdot>0"
  by (metis annil iteration_unfoldl mult_assoc)

lemma iteration_subdenest: "x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
  by (metis add_commute mult_isol_var iteration_idem iteration_subdist)
  
lemma sup_id_top: "1 \<le> y \<Longrightarrow> y \<cdot> \<top> = \<top>"
  by (metis antisym_conv iteration_unfold_eq mult_isol_var top_mult_annil top_ref)

lemma iteration_top[simp]: "x\<^sup>\<infinity>\<cdot>\<top> = \<top>"
  by (metis iteration_refl sup_id_top)

text {* Next, we prove some simulation laws for data refinement. *}

lemma iteration_sim: "z\<cdot>y \<le> x\<cdot>z \<Longrightarrow> z\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>z"
proof -
  assume assms: "z\<cdot>y \<le> x\<cdot>z"
  have "z\<cdot>y\<^sup>\<infinity> = z + z\<cdot>y\<cdot>y\<^sup>\<infinity>"
    by (metis distrib_left mult_assoc mult_oner iteration_unfoldl)
  also have "... \<le> z + x\<cdot>z\<cdot>y\<^sup>\<infinity>"
    by (metis assms add_commute add_iso mult_isor)
  finally show "z\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>z"
    by (metis mult_assoc coinduction)
qed

text {* Nitpick gives a counterexample to the dual simulation law. *}

lemma "y\<cdot>z \<le> z\<cdot>x \<Longrightarrow> y\<^sup>\<infinity>\<cdot>z \<le> z\<cdot>x\<^sup>\<infinity>"
  (* nitpick *) oops
  
text {* Next, we prove some sliding laws. *}

lemma iteration_slide_var: "x\<cdot>(y\<cdot>x)\<^sup>\<infinity> \<le> (x\<cdot>y)\<^sup>\<infinity>\<cdot>x"
  by (metis eq_refl iteration_sim mult_assoc)

lemma iteration_prod_unfold: "(y\<cdot>x)\<^sup>\<infinity> = 1 + y\<cdot>(x\<cdot>y)\<^sup>\<infinity>\<cdot>x"
  apply (rule antisym, metis iteration_unfoldl add_iso_var eq_refl iteration_slide_var mult_assoc mult_isol)
  by (metis add_iso_var iteration_refl iteration_slide_var iteration_unfoldr iteration_zero mult_assoc mult_isol mult_isol_var mult_oner)

lemma iteration_slide: "x\<cdot>(y\<cdot>x)\<^sup>\<infinity> = (x\<cdot>y)\<^sup>\<infinity>\<cdot>x"
  by (metis iteration_prod_unfold iteration_unfoldl_distr distrib_left mult_1_right mult_assoc)

text {* Nitpick refutes the next lemma. *}

lemma "(x\<^sup>\<star>\<cdot>y\<^sup>\<star>)\<^sup>\<infinity> = (x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
  (* nitpick *) oops

lemma star_iteration_slide: "(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> = y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
proof -
  have "y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> \<le> 1 + (x\<^sup>\<star>\<cdot>y)\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> + x\<^sup>\<star>\<cdot>y\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
    by (metis star_unfoldl_eq distrib_right' eq_refl iteration_unfoldl star_ref mult_1_left mult_isor add_iso_var)
  hence "y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity> \<le> 1 + x\<^sup>\<star>\<cdot>y\<cdot>y\<^sup>\<star>\<cdot>(x\<^sup>\<star>\<cdot>y)\<^sup>\<infinity>"
    by (metis less_eq_def add_assoc distrib_left distrib_right mult_1_left mult_assoc star_ref)
  thus ?thesis
    by (metis mult_1_right mult_assoc coinduction star_ref mult_1_left mult_isor add_commute less_eq_def)
qed

text {* The following laws are called denesting laws. *}

lemma iteration_sub_denest: "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "(x + y)\<^sup>\<infinity> = x\<cdot>(x + y)\<^sup>\<infinity> + y\<cdot>(x + y)\<^sup>\<infinity> + 1"
    by (metis add_commute distrib_right' iteration_unfoldl)
  hence "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>(y\<cdot>(x + y)\<^sup>\<infinity> + 1)"
    by (metis add_assoc' add_lub_var add_ub1 add_ub2 coinduction)
  moreover hence "x\<^sup>\<infinity>\<cdot>(y\<cdot>(x + y)\<^sup>\<infinity> + 1) \<le> x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis add_iso mult_assoc mult_isol add_commute coinduction mult_oner mult_isol)
  ultimately show ?thesis
    by (metis dual_order.trans)
qed

lemma iteration_denest: "(x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> \<le> x\<cdot>x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> + y\<cdot>x\<^sup>\<infinity>\<cdot>(y\<cdot>x\<^sup>\<infinity>)\<^sup>\<infinity> + 1"
    by (metis add_commute iteration_unfoldl_distr add_assoc' add_commute iteration_unfoldl order_refl)
  thus ?thesis
    by (metis add_commute iteration_sub_denest order.antisym coinduction distrib_right' iteration_sub_denest mult_assoc mult_oner order.antisym)
qed

lemma iteration_denest2: "(x + y)\<^sup>\<infinity> = y\<^sup>\<star>\<cdot>x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
proof -
  have "(x + y)\<^sup>\<infinity> = y\<^sup>\<infinity>\<cdot>x\<cdot>(y\<^sup>\<infinity>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_commute iteration_denest iteration_slide iteration_unfoldl_distr)
  also have "... = y\<^sup>\<star>\<cdot>x\<cdot>(y\<^sup>\<infinity>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> + y\<^sup>\<infinity>\<cdot>0 + y\<^sup>\<infinity>"
    by (metis isolation mult_assoc distrib_right' annil mult_assoc)
  also have "... = y\<^sup>\<star>\<cdot>x\<cdot>(y\<^sup>\<infinity>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_assoc distrib_left mult_1_right add_0_left mult_1_right)
  finally show ?thesis
    by (metis add_commute iteration_denest iteration_slide mult_assoc)
qed

lemma iteration_denest3: "(x + y)\<^sup>\<infinity> = (y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
  apply (rule antisym, metis add_commute iteration_denest2 eq_refl coinduction)
  by (metis add_commute iteration_denest iteration_slide mult_isor iteration_iso iteration_ref_star)

text {* Now we prove separation laws for reasoning about distributed systems in the framework of action systems. *}

lemma iteration_sep: "y\<cdot>x \<le> x\<cdot>y \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
proof -
  assume "y\<cdot>x \<le> x\<cdot>y"
  hence "y\<^sup>\<star>\<cdot>x \<le> x\<cdot>(x + y)\<^sup>\<star>"
    by (metis star_sim1 add_commute mult_isol order_trans star_subdist)
  hence "y\<^sup>\<star>\<cdot>x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> \<le> x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis mult_isor mult_assoc iteration_star2 add_iso_var eq_refl)
  thus ?thesis
    by (metis iteration_denest2 add_commute coinduction add_commute less_eq_def iteration_subdenest)
qed

lemma iteration_sim2: "y\<cdot>x \<le> x\<cdot>y \<Longrightarrow> y\<^sup>\<infinity>\<cdot>x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
  by (metis add_commute iteration_sep iteration_subdenest)

lemma iteration_sep2: "y\<cdot>x \<le> x\<cdot>y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
proof - 
  assume "y\<cdot>x \<le> x\<cdot>y\<^sup>\<star>"
  hence "y\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<star>\<cdot>y\<^sup>\<infinity>"
    by (metis mult_assoc mult_isor iteration_sim star_denest_var_2 star_sim1 star_slide_var star_trans_eq tc_eq)
  moreover have "x\<^sup>\<infinity>\<cdot>y\<^sup>\<star>\<cdot>y\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis eq_refl mult_assoc iteration_star2)
  moreover have "(y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity> \<le> y\<^sup>\<star>\<cdot>(y\<^sup>\<star>\<cdot>x)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis mult_isor mult_onel star_ref)
  ultimately show ?thesis
    by (metis antisym iteration_denest3 iteration_subdenest order_trans)
qed

lemma iteration_sep3: "y\<cdot>x \<le> x\<cdot>(x + y) \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
proof -
  assume "y\<cdot>x \<le> x\<cdot>(x + y)"
  hence "y\<^sup>\<star>\<cdot>x \<le> x\<cdot>(x + y)\<^sup>\<star>"
    by (metis star_sim1)
  hence "y\<^sup>\<star>\<cdot>x\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> \<le> x\<cdot>(x + y)\<^sup>\<star>\<cdot>(x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_iso mult_isor)
  hence "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis mult_assoc iteration_denest2 iteration_star2 add_commute coinduction)
  thus ?thesis
    by (metis add_commute less_eq_def iteration_subdenest)
qed

lemma iteration_sep4: "\<lbrakk>y\<cdot>0 = 0; z\<cdot>x = 0; y\<cdot>x \<le> (x + z)\<cdot>y\<^sup>\<star>\<rbrakk> \<Longrightarrow> (x + y + z)\<^sup>\<infinity> = x\<^sup>\<infinity>\<cdot>(y + z)\<^sup>\<infinity>"
proof -
  assume assms: "y\<cdot>0 = 0" "z\<cdot>x = 0" "y\<cdot>x \<le> (x + z)\<cdot>y\<^sup>\<star>"
  have "y\<cdot>y\<^sup>\<star>\<cdot>z \<le> y\<^sup>\<star>\<cdot>z\<cdot>y\<^sup>\<star>"
    by (metis mult_isor star_1l mult_oner order_trans star_plus_one subdistl)
  have "y\<^sup>\<star>\<cdot>z\<cdot>x \<le> x\<cdot>y\<^sup>\<star>\<cdot>z"
    by (metis zero_least assms(1) assms(2) independence1 mult_assoc)
  have "y\<cdot>(x + y\<^sup>\<star>\<cdot>z) \<le> (x + z)\<cdot>y\<^sup>\<star> + y\<cdot>y\<^sup>\<star>\<cdot>z"
    by (metis assms(3) distrib_left mult_assoc add_iso)
  also have "... \<le> (x + y\<^sup>\<star>\<cdot>z)\<cdot>y\<^sup>\<star> + y\<cdot>y\<^sup>\<star>\<cdot>z" 
    by (metis star_ref add_iso_var eq_refl mult_1_left mult_isor)
  also have "... \<le> (x + y\<^sup>\<star>\<cdot>z)\<cdot>y\<^sup>\<star> + y\<^sup>\<star>\<cdot>z \<cdot>y\<^sup>\<star>" using `y\<cdot>y\<^sup>\<star>\<cdot>z \<le> y\<^sup>\<star>\<cdot>z\<cdot>y\<^sup>\<star>`
    by (metis add_commute add_iso)
  finally have "y\<cdot>(x + y\<^sup>\<star>\<cdot>z) \<le> (x + y\<^sup>\<star>\<cdot>z)\<cdot>y\<^sup>\<star>"
    by (metis add_commute add_idem' add_left_commute distrib_right)
  moreover have "(x + y + z)\<^sup>\<infinity> \<le> (x + y + y\<^sup>\<star>\<cdot>z)\<^sup>\<infinity>"
    by (metis star_ref add_iso_var eq_refl mult_1_left mult_isor iteration_iso)  
  moreover have "... = (x + y\<^sup>\<star>\<cdot>z)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>"
    by (metis add_assoc add_commute calculation iteration_sep2)
  moreover have "... = x\<^sup>\<infinity>\<cdot>(y\<^sup>\<star>\<cdot>z)\<^sup>\<infinity>\<cdot>y\<^sup>\<infinity>" using `y\<^sup>\<star>\<cdot>z\<cdot>x \<le> x\<cdot>y\<^sup>\<star>\<cdot>z`
    by (metis iteration_sep mult_assoc)
  ultimately have "(x + y + z)\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>(y + z)\<^sup>\<infinity>"
    by (metis add_commute mult_assoc iteration_denest3)
  thus ?thesis
    by (metis add_commute add_left_commute less_eq_def iteration_subdenest)
qed

text {* Finally, we prove some blocking laws. *}

text {* Nitpick refutes the next lemma. *}

lemma "x\<cdot>y = 0 \<Longrightarrow> x\<^sup>\<infinity>\<cdot>y = y"
  (* nitpick *) oops

lemma iteration_idep: "x\<cdot>y = 0 \<Longrightarrow> x\<cdot>y\<^sup>\<infinity> = x"
  by (metis add_zeror annil iteration_unfoldl_distl)

text {* Nitpick refutes the next lemma. *}

lemma "y\<cdot>w \<le> x\<cdot>y + z \<Longrightarrow> y\<cdot>w\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>z"
  (* nitpick *) oops

text {* At the end of this file, we consider a data refinement example from von Wright~\cite{Wright02}. *}

lemma data_refinement:
  assumes "s' \<le> s\<cdot>z" "z\<cdot>e' \<le> e" "z\<cdot>a' \<le> a\<cdot>z" "z\<cdot>b \<le> z" "b\<^sup>\<infinity> = b\<^sup>\<star>"
  shows "s'\<cdot>(a' + b)\<^sup>\<infinity>\<cdot>e' \<le> s\<cdot>a\<^sup>\<infinity>\<cdot>e"
proof -
  have "z\<cdot>b\<^sup>\<star> \<le> z"
    by (metis assms(4) star_inductr_var)
  have "(z\<cdot>a')\<cdot>b\<^sup>\<star> \<le> (a\<cdot>z)\<cdot>b\<^sup>\<star>"
    by (metis assms(3) mult_assoc mult_isor)
  hence "z\<cdot>(a'\<cdot>b\<^sup>\<star>)\<^sup>\<infinity> \<le>  a\<^sup>\<infinity>\<cdot>z" using `z\<cdot>b\<^sup>\<star> \<le> z`
    by (metis mult_assoc mult_isol order_trans iteration_sim mult_assoc)
  have "s'\<cdot>(a' + b)\<^sup>\<infinity>\<cdot>e' \<le> s'\<cdot>b\<^sup>\<star>\<cdot>(a'\<cdot>b\<^sup>\<star>)\<^sup>\<infinity>\<cdot>e'"
    by (metis add_commute assms(5) eq_refl iteration_denest mult_assoc)
  also have "... \<le> s\<cdot>z\<cdot>b\<^sup>\<star>\<cdot>(a'\<cdot>b\<^sup>\<star>)\<^sup>\<infinity>\<cdot>e'"
    by (metis assms(1) mult_isor)
  also have "... \<le> s\<cdot>z\<cdot>(a'\<cdot>b\<^sup>\<star>)\<^sup>\<infinity>\<cdot>e'" using `z\<cdot>b\<^sup>\<star> \<le> z`
    by (metis mult_assoc mult_isol mult_isor)
  also have "... \<le> s\<cdot>a\<^sup>\<infinity>\<cdot>z\<cdot>e'" using `z\<cdot>(a'\<cdot>b\<^sup>\<star>)\<^sup>\<infinity> \<le>  a\<^sup>\<infinity>\<cdot>z`
    by (metis mult_assoc mult_isol mult_isor)
  finally show ?thesis
    by (metis assms(2) mult_assoc mult_isol mult_assoc mult_isol order_trans)
qed


end

end
