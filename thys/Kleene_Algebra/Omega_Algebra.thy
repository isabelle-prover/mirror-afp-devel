(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Omega Algebras *}

theory Omega_Algebra
imports Kleene_Algebra
begin

text {*
\emph{Omega algebras}~\cite{cohen00omega} extend Kleene algebras by an
$\omega$-operation that axiomatizes infinite iteration (just like the
Kleene star axiomatizes finite iteration).
*}


subsection {* Left Omega Algebras *}

text {*
In this section we consider \emph{left omega algebras}, i.e., omega
algebras based on left Kleene algebras. Surprisingly, we are still
looking for statements mentioning~$\omega$ that are true in omega
algebras, but do not already hold in left omega algebras.
*}

class left_omega_algebra = left_kleene_algebra_zero + omega_op +
  assumes omega_unfold: "x\<^bsup>\<omega>\<^esup> \<le> x \<cdot> x\<^bsup>\<omega>\<^esup>"
  and omega_coinduct: "y \<le> z + x \<cdot> y \<longrightarrow> y \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
begin

text {* First we prove some variants of the coinduction axiom. *}

lemma omega_coinduct_var1: "y \<le> 1 + x \<cdot> y \<longrightarrow> y \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star>"
  by (metis mult_oner omega_coinduct)

lemma  omega_coinduct_var2: "y \<le> x \<cdot> y \<longrightarrow> y \<le> x\<^bsup>\<omega>\<^esup>"
  by (metis add.commute add_zero_l annir omega_coinduct)

lemma omega_coinduct_eq: "y = z + x \<cdot> y \<longrightarrow> y \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
  by (metis eq_refl omega_coinduct)

lemma omega_coinduct_eq_var1: "y = 1 + x \<cdot> y \<longrightarrow> y \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star>"
  by (metis eq_refl omega_coinduct_var1)

lemma  omega_coinduct_eq_var2: "y = x \<cdot> y \<longrightarrow> y \<le> x\<^bsup>\<omega>\<^esup>"
  by (metis eq_refl omega_coinduct_var2)

lemma "y = x \<cdot> y + z \<longrightarrow> y = x\<^sup>\<star> \<cdot> z + x\<^bsup>\<omega>\<^esup>"
  nitpick [expect=genuine] -- "2-element counterexample"
oops

lemma "y = 1 + x \<cdot> y \<longrightarrow> y = x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star>"
  nitpick [expect=genuine] -- "3-element counterexample"
oops

lemma "y = x \<cdot> y \<longrightarrow> y = x\<^bsup>\<omega>\<^esup>"
  nitpick [expect=genuine] -- "2-element counterexample"
oops

text {* Next we strengthen the unfold law to an equation. *}

lemma omega_unfold_eq [simp]: "x \<cdot> x\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  have "x \<cdot> x\<^bsup>\<omega>\<^esup> \<le> x \<cdot> x \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc mult_isol omega_unfold)
  thus "x \<cdot> x\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc omega_coinduct_var2)
  show  "x\<^bsup>\<omega>\<^esup> \<le> x \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (fact omega_unfold)
qed

lemma omega_unfold_var: "z + x \<cdot> x\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
  by (metis add_lub add_ub1 omega_coinduct omega_unfold_eq)

lemma "z + x \<cdot> x\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
  nitpick [expect=genuine] -- "4-element counterexample"
oops

text {* We now prove subdistributivity and isotonicity of omega. *}

lemma omega_subdist: "x\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
proof -
  have "x\<^bsup>\<omega>\<^esup> \<le> (x + y) \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (metis add_ub1 mult_isor omega_unfold_eq)
  thus ?thesis
    by (metis omega_coinduct_var2)
qed

lemma omega_iso: "x \<le> y \<longrightarrow> x\<^bsup>\<omega>\<^esup> \<le> y\<^bsup>\<omega>\<^esup>"
  by (metis less_eq_def omega_subdist)

lemma omega_subdist_var: "x\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
  by (metis add.commute add_lub omega_subdist)

lemma zero_omega [simp]: "0\<^bsup>\<omega>\<^esup> = 0"
  by (metis annil omega_unfold_eq)

text {* The next lemma is another variant of omega unfold *}

lemma star_omega_1 [simp]: "x\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  have "x \<cdot> x\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup>"
    by (metis eq_refl omega_unfold_eq)
  thus "x\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup>"
    by (metis star_inductl_var)
  show "x\<^bsup>\<omega>\<^esup> \<le> x\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (metis star_ref mult_isor mult_onel)
qed

text {* The next lemma says that~@{term "1\<^bsup>\<omega>\<^esup>"} is the maximal element
of omega algebra. We therefore baptise it~$\top$. *}

lemma max_element: "x \<le> 1\<^bsup>\<omega>\<^esup>"
  by (metis eq_refl mult_onel omega_coinduct_var2)

definition top ("\<top>")
  where "\<top> = 1\<^bsup>\<omega>\<^esup>"

lemma star_omega_3 [simp]: "(x\<^sup>\<star>)\<^bsup>\<omega>\<^esup> = \<top>"
proof -
  have "1 \<le> x\<^sup>\<star>"
    by (fact star_ref)
  hence "\<top> \<le> (x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis omega_iso top_def)
  thus ?thesis
    by (metis eq_iff max_element top_def)
qed

text {* The following lemma is strange since it is counterintuitive
that one should be able to append something after an infinite
iteration. *}

lemma omega_1: "x\<^bsup>\<omega>\<^esup> \<cdot> y \<le> x\<^bsup>\<omega>\<^esup>"
proof -
  have "x\<^bsup>\<omega>\<^esup> \<cdot> y \<le> x \<cdot> x\<^bsup>\<omega>\<^esup> \<cdot> y"
    by (metis eq_refl omega_unfold_eq)
  thus ?thesis
    by (metis mult.assoc omega_coinduct_var2)
qed

lemma "x\<^bsup>\<omega>\<^esup> \<cdot> y = x\<^bsup>\<omega>\<^esup>"
  nitpick [expect=genuine] -- "2-element counterexample"
oops

lemma omega_sup_id: "1 \<le> y \<longrightarrow> x\<^bsup>\<omega>\<^esup> \<cdot> y = x\<^bsup>\<omega>\<^esup>"
  by (metis eq_iff mult_isol mult_oner omega_1)

lemma omega_top [simp]: "x\<^bsup>\<omega>\<^esup> \<cdot> \<top> = x\<^bsup>\<omega>\<^esup>"
  by (metis max_element omega_sup_id top_def)

lemma supid_omega: "1 \<le> x \<longrightarrow> x\<^bsup>\<omega>\<^esup> = \<top>"
  by (metis eq_iff max_element omega_iso top_def)

lemma "x\<^bsup>\<omega>\<^esup> = \<top> \<longrightarrow> 1 \<le> x"
  nitpick [expect=genuine] -- "4-element counterexample"
oops

text {* Next we prove a simulation law for the omega operation *}

lemma omega_simulation: "z \<cdot> x \<le> y \<cdot> z \<longrightarrow> z \<cdot> x\<^bsup>\<omega>\<^esup> \<le> y\<^bsup>\<omega>\<^esup>"
proof
  assume "z \<cdot> x \<le> y \<cdot> z"
  also have "z \<cdot> x\<^bsup>\<omega>\<^esup> = z \<cdot> x \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc omega_unfold_eq)
  moreover have "... \<le> y \<cdot> z \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (metis mult_isor calculation)
  thus "z \<cdot> x\<^bsup>\<omega>\<^esup> \<le> y\<^bsup>\<omega>\<^esup>"
    by (metis calculation mult.assoc omega_coinduct_var2)
qed

lemma "z \<cdot> x \<le> y \<cdot> z \<longrightarrow> z \<cdot> x\<^bsup>\<omega>\<^esup> \<le> y\<^bsup>\<omega>\<^esup> \<cdot> z"
  nitpick [expect=genuine] -- "4-element counterexample"
oops

lemma "y \<cdot> z  \<le> z \<cdot> x \<longrightarrow> y\<^bsup>\<omega>\<^esup> \<le> z \<cdot> x\<^bsup>\<omega>\<^esup>"
  nitpick [expect=genuine] -- "2-element counterexample"
oops

lemma "y \<cdot> z  \<le> z \<cdot> x \<longrightarrow> y\<^bsup>\<omega>\<^esup> \<cdot> z \<le> x\<^bsup>\<omega>\<^esup>"
  nitpick [expect=genuine] -- "4-element counterexample"
oops

text {* Next we prove transitivity of omega elements. *}

lemma omega_trans: "x\<^bsup>\<omega>\<^esup> \<cdot> x\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup>"
  by (fact omega_1)

lemma omega_omega: "(x\<^bsup>\<omega>\<^esup>)\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup>"
  by (metis omega_1 omega_unfold_eq)

(*
lemma "x\<^bsup>\<omega>\<^esup> \<cdot> x\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup>"
nitpick -- "no proof, no counterexample"

lemma "(x\<^bsup>\<omega>\<^esup>)\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup>"
nitpick -- "no proof, no counterexample"
*)

text {* The next lemmas are axioms of Wagner's complete axiomatisation
for omega-regular languages~\cite{Wagner77omega}, but in a slightly
different setting.  *}

lemma wagner_1 [simp]: "(x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  have "(x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup> = x \<cdot> x\<^sup>\<star> \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc omega_unfold_eq)
  also have "... = x \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc star_slide_var)
  also have "... = x \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc star_trans_eq)
  also have "... = x \<cdot> (x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc omega_unfold_eq)
  thus "(x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup>"
    by (metis calculation eq_refl omega_coinduct_var2)
   show "x\<^bsup>\<omega>\<^esup> \<le> (x \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis mult_isol mult_oner omega_iso star_ref)
qed

lemma wagner_2_var: "x \<cdot> (y \<cdot> x)\<^bsup>\<omega>\<^esup> \<le> (x \<cdot> y)\<^bsup>\<omega>\<^esup>"
proof -
  have "x \<cdot> y \<cdot> x \<le> x \<cdot> y \<cdot> x"
    by auto
  thus "x \<cdot> (y \<cdot> x)\<^bsup>\<omega>\<^esup> \<le> (x \<cdot> y)\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc omega_simulation)
qed

lemma wagner_2 [simp]: "x \<cdot> (y \<cdot> x)\<^bsup>\<omega>\<^esup> = (x \<cdot> y)\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  show "x \<cdot> (y \<cdot> x)\<^bsup>\<omega>\<^esup> \<le> (x \<cdot> y)\<^bsup>\<omega>\<^esup>"
    by (rule wagner_2_var)
  have "(x \<cdot> y)\<^bsup>\<omega>\<^esup> = x \<cdot> y \<cdot> (x \<cdot> y)\<^bsup>\<omega>\<^esup>"
    by (metis omega_unfold_eq)
  thus "(x \<cdot> y)\<^bsup>\<omega>\<^esup> \<le> x \<cdot> (y \<cdot> x)\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc mult_isol wagner_2_var)
qed

text {*
This identity is called~(A8) in Wagner's paper.
*}

lemma wagner_3:
assumes "x \<cdot> (x + y)\<^bsup>\<omega>\<^esup> + z = (x + y)\<^bsup>\<omega>\<^esup>"
shows "(x + y)\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
proof (rule antisym)
  show  "(x + y)\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
    by (metis add.commute assms omega_coinduct_eq)
  have "x\<^sup>\<star> \<cdot> z \<le> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add.commute assms star_inductl_eq)
  thus "x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z \<le> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add_lub omega_subdist)
qed

text {*
This identity is called~(R4) in Wagner's paper.
*}

lemma wagner_1_var [simp]: "(x\<^sup>\<star> \<cdot> x)\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup>"
  by (metis star_slide_var wagner_1)

lemma star_omega_4 [simp]: "(x\<^bsup>\<omega>\<^esup>)\<^sup>\<star> = 1 + x\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  have "(x\<^bsup>\<omega>\<^esup>)\<^sup>\<star> = 1 + x\<^bsup>\<omega>\<^esup> \<cdot> (x\<^bsup>\<omega>\<^esup>)\<^sup>\<star>"
    by simp
  also have "... \<le> 1 + x\<^bsup>\<omega>\<^esup> \<cdot> \<top>"
    by (metis add_iso_var eq_refl omega_1 omega_top)
  thus "(x\<^bsup>\<omega>\<^esup>)\<^sup>\<star> \<le> 1 + x\<^bsup>\<omega>\<^esup>"
    by (metis calculation omega_top)
  show "1 + x\<^bsup>\<omega>\<^esup> \<le> (x\<^bsup>\<omega>\<^esup>)\<^sup>\<star>"
    by (metis star2 star_ext)
qed

lemma star_omega_5 [simp]: "x\<^bsup>\<omega>\<^esup> \<cdot> (x\<^bsup>\<omega>\<^esup>)\<^sup>\<star> = x\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  show "x\<^bsup>\<omega>\<^esup> \<cdot> (x\<^bsup>\<omega>\<^esup>)\<^sup>\<star> \<le> x\<^bsup>\<omega>\<^esup>"
    by (rule omega_1)
  show "x\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup> \<cdot> (x\<^bsup>\<omega>\<^esup>)\<^sup>\<star>"
    by (metis mult_oner star_ref mult_isol)
qed

text {* The next law shows how omegas below a sum can be unfolded. *}

lemma omega_sum_unfold: "x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^bsup>\<omega>\<^esup> = (x + y)\<^bsup>\<omega>\<^esup>"
proof -
  have "(x + y)\<^bsup>\<omega>\<^esup> = x \<cdot> (x + y)\<^bsup>\<omega>\<^esup> + y \<cdot> (x+y)\<^bsup>\<omega>\<^esup>"
    by (metis distrib_right omega_unfold_eq)
  thus ?thesis
    by (metis mult.assoc wagner_3)
qed

text {*
The next two lemmas apply induction and coinduction to this law.
*}

lemma omega_sum_unfold_coind: "(x + y)\<^bsup>\<omega>\<^esup> \<le> (x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup>"
  by (metis omega_coinduct_eq omega_sum_unfold)

lemma omega_sum_unfold_ind: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
  by (metis omega_sum_unfold star_inductl_eq)

lemma wagner_1_gen: "(x \<cdot> y\<^sup>\<star>)\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
proof -
  have "(x \<cdot> y\<^sup>\<star>)\<^bsup>\<omega>\<^esup> \<le> ((x + y) \<cdot> (x + y)\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis add_ub1 add_ub2 mult_isol_var omega_iso star_iso)
  thus ?thesis
    by (metis wagner_1)
qed

lemma wagner_1_var_gen: "(x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
proof -
  have "(x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^bsup>\<omega>\<^esup>"
    by (metis wagner_2)
  also have "... \<le> x\<^sup>\<star> \<cdot> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add.commute mult_isol wagner_1_gen)
  also have "... \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add_ub1 mult_isor star_iso)
  thus ?thesis
    by (metis calculation order_trans star_omega_1)
qed

text {* The next lemma is a variant of the denest law for the star at
the level of omega. *}

lemma omega_denest [simp]: "(x + y)\<^bsup>\<omega>\<^esup> = (x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  show "(x + y)\<^bsup>\<omega>\<^esup> \<le> (x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup>"
    by (rule omega_sum_unfold_coind)
  have "(x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> \<le>  (x + y)\<^bsup>\<omega>\<^esup>"
    by (rule wagner_1_var_gen)
  hence "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis omega_sum_unfold_ind)
  thus "(x\<^sup>\<star> \<cdot> y)\<^bsup>\<omega>\<^esup> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add_lub wagner_1_var_gen)
qed

text {* The next lemma yields a separation theorem for infinite
iteration in the presence of a quasicommutation property. A
nondeterministic loop over~@{term x} and~@{term y} can be refined into
separate infinite loops over~@{term x} and~@{term y}.  *}

lemma omega_sum_refine:
  assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  shows "(x + y)\<^bsup>\<omega>\<^esup> = x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> y\<^bsup>\<omega>\<^esup>"
proof (rule antisym)
  have "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    by (metis assms quasicomm_var)
  also have "(x + y)\<^bsup>\<omega>\<^esup> = y\<^bsup>\<omega>\<^esup> + y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add.commute omega_sum_unfold)
  moreover have "... \<le> x \<cdot> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup>"
    by (metis add_iso add_lub add_ub2 calculation(1) mult_isor)
  moreover have "... \<le> x \<cdot> (x + y)\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup>"
    by (metis mult.assoc order_refl star_omega_1)
  thus "(x + y)\<^bsup>\<omega>\<^esup> \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> y\<^bsup>\<omega>\<^esup>"
    by (metis add.commute calculation mult.assoc omega_coinduct star_omega_1)
  have "x\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
    by (rule omega_subdist)
  moreover have "x\<^sup>\<star> \<cdot> y\<^bsup>\<omega>\<^esup> \<le> x\<^sup>\<star> \<cdot> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis calculation add_ub1 mult_isol)
  moreover have"... \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^bsup>\<omega>\<^esup>"
    by (metis add_ub1 star_iso mult_isor)
  moreover have "... = (x + y)\<^bsup>\<omega>\<^esup>"
     by (rule star_omega_1)
   thus "x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> y\<^bsup>\<omega>\<^esup> \<le> (x + y)\<^bsup>\<omega>\<^esup>"
     by (metis add.commute add_lub calculation mult_isol omega_subdist order_trans star_omega_1)
qed

text {* The following theorem by Bachmair and
Dershowitz~\cite{bachmair86commutation} is a corollary. *}

lemma bachmair_dershowitz:
  assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  shows "(x + y)\<^bsup>\<omega>\<^esup> = 0 \<longleftrightarrow> x\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup> = 0"
proof
  assume "(x + y)\<^bsup>\<omega>\<^esup> = 0"
  show "x\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup> = 0"
    by (metis `(x + y)\<^bsup>\<omega>\<^esup> = (0\<Colon>'a)` add.commute add_zero_r annir omega_sum_unfold)
next
  assume "x\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup> = 0"
  show "(x + y)\<^bsup>\<omega>\<^esup> = 0"
    by (metis `x\<^bsup>\<omega>\<^esup> + y\<^bsup>\<omega>\<^esup> = (0\<Colon>'a)` assms no_trivial_inverse omega_sum_refine distrib_left star_omega_1)
qed

text {*
The next lemmas consider an abstract variant of the empty word
property from language theory and match it with the absence of
infinite iteration~\cite{struth12regeq}.
*}

definition (in dioid_one_zero) ewp
where "ewp x \<equiv> \<not>(\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0)"

lemma ewp_super_id1: "0 \<noteq> 1 \<longrightarrow> 1 \<le> x \<longrightarrow> ewp x"
  by (metis ewp_def mult_oner)

lemma "0 \<noteq> 1 \<longrightarrow> 1 \<le> x \<longleftrightarrow> ewp x"
  nitpick [expect=genuine] -- "3-element counterexample"
oops

text {* The next facts relate the absence of the empty word property
with the absence of infinite iteration. *}

lemma ewp_neg_and_omega: "\<not> ewp x \<longleftrightarrow> x\<^bsup>\<omega>\<^esup> = 0"
proof
  assume "\<not> ewp x"
  hence "\<forall> y. y \<le> x \<cdot> y \<longrightarrow> y = 0"
    by (metis ewp_def)
  thus "x\<^bsup>\<omega>\<^esup> = 0"
    by (metis omega_unfold)
next
  assume "x\<^bsup>\<omega>\<^esup> = 0"
  hence "\<forall> y. y \<le> x \<cdot> y \<longrightarrow> y = 0"
    by (metis omega_coinduct_var2 zero_unique)
  thus "\<not> ewp x"
    by (metis ewp_def)
qed

lemma ewp_alt1: "(\<forall>z. x\<^bsup>\<omega>\<^esup> \<le> x\<^sup>\<star> \<cdot> z) \<longleftrightarrow> (\<forall>y z. y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z)"
  by (metis add_comm less_eq_def omega_coinduct omega_unfold_eq order_prop)

lemma ewp_alt: "x\<^bsup>\<omega>\<^esup> = 0 \<longleftrightarrow> (\<forall>y z. y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z)"
  by (metis annir antisym ewp_alt1 zero_least)

text {* So we have obtained a condition for Arden's lemma in omega
algebra.  *}

lemma omega_super_id1: "0 \<noteq> 1 \<longrightarrow> 1 \<le> x \<longrightarrow> x\<^bsup>\<omega>\<^esup> \<noteq> 0"
  by (metis eq_iff max_element omega_iso zero_least)

lemma omega_super_id2: "0 \<noteq> 1 \<longrightarrow> x\<^bsup>\<omega>\<^esup> = 0 \<longrightarrow> \<not>(1 \<le> x)"
  by (metis omega_super_id1)

text {* The next lemmas are abstract versions of Arden's lemma from
language theory.  *}

lemma ardens_lemma_var:
  assumes "x\<^bsup>\<omega>\<^esup> = 0" and  "z + x \<cdot> y = y"
  shows "x\<^sup>\<star> \<cdot> z = y"
proof -
  have "y \<le> x\<^bsup>\<omega>\<^esup> + x\<^sup>\<star> \<cdot> z"
    by (metis assms omega_coinduct order_refl)
  hence "y \<le> x\<^sup>\<star> \<cdot> z"
    by (metis add_zero_l assms)
  thus "x\<^sup>\<star> \<cdot> z = y"
    by (metis assms eq_iff star_inductl_eq)
qed

lemma ardens_lemma: "\<not> ewp x \<longrightarrow> z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y"
  by (metis ardens_lemma_var ewp_neg_and_omega)

lemma ardens_lemma_equiv:
  assumes "\<not> ewp x"
  shows "z + x \<cdot> y = y \<longleftrightarrow> x\<^sup>\<star> \<cdot> z = y"
proof
  assume "z + x \<cdot> y = y"
  thus "x\<^sup>\<star> \<cdot> z = y"
    by (metis ardens_lemma assms)
next
  assume "x\<^sup>\<star> \<cdot> z = y"
  also have "z + x \<cdot> y = z + x \<cdot> x\<^sup>\<star> \<cdot> z"
    by (metis calculation mult.assoc)
  moreover have "... = (1 + x \<cdot> x\<^sup>\<star>) \<cdot> z"
    by (metis distrib_right mult_onel)
  moreover have "... = x\<^sup>\<star> \<cdot> z"
    by (metis star_unfoldl_eq)
  thus "z + x \<cdot> y = y"
    by (metis calculation)
qed

lemma ardens_lemma_var_equiv: "x\<^bsup>\<omega>\<^esup> = 0 \<longrightarrow> (z + x \<cdot> y = y \<longleftrightarrow> x\<^sup>\<star> \<cdot> z = y)"
  by (metis ardens_lemma_equiv ewp_neg_and_omega)

lemma arden_conv1: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longrightarrow> \<not> ewp x"
  by (metis add_zero_l annir ewp_neg_and_omega omega_unfold_eq)

lemma arden_conv2: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longrightarrow> x\<^bsup>\<omega>\<^esup> = 0"
  by (metis arden_conv1 ewp_neg_and_omega)

lemma arden_var3: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longleftrightarrow> x\<^bsup>\<omega>\<^esup> = 0"
  by (metis arden_conv2 ardens_lemma_var)

end


subsection {* Omega Algebras *}

class omega_algebra = kleene_algebra + left_omega_algebra

end
