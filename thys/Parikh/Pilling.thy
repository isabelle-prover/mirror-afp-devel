(* Authors: Fabian Lehr *)

section \<open>Pilling's proof of Parikh's theorem\<close>

theory Pilling
  imports 
    "Reg_Lang_Exp_Eqns"
begin


text \<open>We prove Parikh's theorem, closely following Pilling's proof \<^cite>\<open>Pilling\<close>. The rough
idea is as follows: As seen in section \ref{sec:cfl_as_eqns_sys}, each CFG can be interpreted as a
system of \<^const>\<open>reg_eval\<close> equations of the first type and we can easily convert it into a system
of the second type by applying the Parikh image on both sides of each equation. Pilling now shows
that there is a regular solution to the latter system and that this solution is furthermore minimal.
Using the relations explored in section \ref{sec:eqns_sys_relations} we prove that the CFG's
language is a minimal solution of the same sytem and hence that the Parikh image of the CFG's
language and of the regular solution must be identical; this finishes the proof of Parikh's theorem.

Notably, while in \<^cite>\<open>Pilling\<close> Pilling proves an auxiliary lemma first and applies this lemma in
the proof of the main theorem, we were able to complete the whole proof without using the lemma.\<close>


subsection \<open>Special representation of regular language expressions\<close>

text \<open>To each \<^const>\<open>reg_eval\<close> regular language expression and variable \<open>x\<close> corresponds a second
regular language expression with the same Parikh image and of the form depicted in equation (3) in
\<^cite>\<open>Pilling\<close>. We call regular language expressions of this form "bipartite regular language
expressions" since they decompose into two subexpressions where one of them contains the variable
\<open>x\<close> and the other one does not:\<close>
definition bipart_rlexp :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> bool" where
  "bipart_rlexp x f \<equiv> \<exists>p q. reg_eval p \<and> reg_eval q \<and>
    f = Union p (Concat q (Var x)) \<and> x \<notin> vars p"


text \<open>All bipartite regular language expressions evaluate to regular languages. Additionally,
for each \<^const>\<open>reg_eval\<close> regular language expression and variable \<open>x\<close>, there exists a bipartite
regular language expression with identical Parikh image and almost identical set of variables.
While the first proof is simple, the second one is more complex and needs the results of the
sections \ref{sec:parikh_img_star} and \ref{sec:parikh_img_star2}:\<close>
lemma "bipart_rlexp x f \<Longrightarrow> reg_eval f"
  unfolding bipart_rlexp_def by fastforce


lemma reg_eval_bipart_rlexp_Variable: "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars (Var y) \<union> {x}
                                        \<and> (\<forall>v. \<Psi> (eval (Var y) v) = \<Psi> (eval f' v))"
proof (cases "x = y")
let ?f' = "Union (Const {}) (Concat (Const {[]}) (Var x))"
  case True
  then have "bipart_rlexp x ?f'"
    unfolding bipart_rlexp_def using emptyset_regular epsilon_regular by fastforce
  moreover have "eval ?f' v = eval (Var y) v" for v :: "'a valuation" using True by simp
  moreover have "vars ?f' = vars (Var y) \<union> {x}" using True by simp
  ultimately show ?thesis by metis
next
  let ?f' = "Union (Var y) (Concat (Const {}) (Var x))"
  case False
  then have "bipart_rlexp x ?f'"
    unfolding bipart_rlexp_def using emptyset_regular epsilon_regular by fastforce
  moreover have "eval ?f' v = eval (Var y) v" for v :: "'a valuation" using False by simp
  moreover have "vars ?f' = vars (Var y) \<union> {x}" by simp
  ultimately show ?thesis by metis
qed

lemma reg_eval_bipart_rlexp_Const:
  assumes "regular_lang l"
    shows "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars (Const l) \<union> {x}
                \<and> (\<forall>v. \<Psi> (eval (Const l) v) = \<Psi> (eval f' v))"
proof -
  let ?f' = "Union (Const l) (Concat (Const {}) (Var x))"
  have "bipart_rlexp x ?f'"
    unfolding bipart_rlexp_def using assms emptyset_regular by simp
  moreover have "eval ?f' v = eval (Const l) v" for v :: "'a valuation" by simp
  moreover have "vars ?f' = vars (Const l) \<union> {x}" by simp 
  ultimately show ?thesis by metis
qed

lemma reg_eval_bipart_rlexp_Union:
  assumes "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f1 \<union> {x} \<and>
                (\<forall>v. \<Psi> (eval f1 v) = \<Psi> (eval f' v))"
          "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f2 \<union> {x} \<and>
                (\<forall>v. \<Psi> (eval f2 v) = \<Psi> (eval f' v))"
    shows "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars (Union f1 f2) \<union> {x} \<and>
                (\<forall>v. \<Psi> (eval (Union f1 f2) v) = \<Psi> (eval f' v))"
proof -
  from assms obtain f1' f2' where f1'_intro: "bipart_rlexp x f1' \<and> vars f1' = vars f1 \<union> {x} \<and>
      (\<forall>v. \<Psi> (eval f1 v) = \<Psi> (eval f1' v))"
    and f2'_intro: "bipart_rlexp x f2' \<and> vars f2' = vars f2 \<union> {x} \<and>
      (\<forall>v. \<Psi> (eval f2 v) = \<Psi> (eval f2' v))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "reg_eval p1 \<and> reg_eval q1 \<and>
    f1' = Union p1 (Concat q1 (Var x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "reg_eval p2 \<and> reg_eval q2 \<and> f2' = Union p2 (Concat q2 (Var x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding bipart_rlexp_def by auto
  let ?f' = "Union (Union p1 p2) (Concat (Union q1 q2) (Var x))"
  have "bipart_rlexp x ?f'" unfolding bipart_rlexp_def using p1_q1_intro p2_q2_intro by auto
  moreover have "\<Psi> (eval ?f' v) = \<Psi> (eval (Union f1 f2) v)" for v
    using p1_q1_intro p2_q2_intro f1'_intro f2'_intro
    by (simp add: conc_Un_distrib(2) sup_assoc sup_left_commute)
  moreover from f1'_intro f2'_intro p1_q1_intro p2_q2_intro
    have "vars ?f' = vars (Union f1 f2) \<union> {x}" by auto
  ultimately show ?thesis by metis
qed

lemma reg_eval_bipart_rlexp_Concat:
  assumes "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f1 \<union> {x} \<and>
                (\<forall>v. \<Psi> (eval f1 v) = \<Psi> (eval f' v))"
          "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f2 \<union> {x} \<and>
                (\<forall>v. \<Psi> (eval f2 v) = \<Psi> (eval f' v))"
    shows "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars (Concat f1 f2) \<union> {x} \<and>
                (\<forall>v. \<Psi> (eval (Concat f1 f2) v) = \<Psi> (eval f' v))"
proof -
  from assms obtain f1' f2' where f1'_intro: "bipart_rlexp x f1' \<and> vars f1' = vars f1 \<union> {x} \<and>
      (\<forall>v. \<Psi> (eval f1 v) = \<Psi> (eval f1' v))"
    and f2'_intro: "bipart_rlexp x f2' \<and> vars f2' = vars f2 \<union> {x} \<and>
      (\<forall>v. \<Psi> (eval f2 v) = \<Psi> (eval f2' v))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "reg_eval p1 \<and> reg_eval q1 \<and>
    f1' = Union p1 (Concat q1 (Var x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "reg_eval p2 \<and> reg_eval q2 \<and> f2' = Union p2 (Concat q2 (Var x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding bipart_rlexp_def by auto
  let ?q' = "Union (Concat q1 (Concat (Var x) q2)) (Union (Concat p1 q2) (Concat q1 p2))"
  let ?f' = "Union (Concat p1 p2) (Concat ?q' (Var x))"
  have "\<forall>v. (\<Psi> (eval (Concat f1 f2) v) = \<Psi> (eval ?f' v))"
  proof (rule allI)
    fix v
    have f2_subst: "\<Psi> (eval f2 v) = \<Psi> (eval p2 v \<union> eval q2 v @@ v x)"
      using p2_q2_intro f2'_intro by auto
    have "\<Psi> (eval (Concat f1 f2) v) = \<Psi> ((eval p1 v \<union> eval q1 v @@ v x) @@ eval f2 v)"
      using p1_q1_intro f1'_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(4) parikh_conc_right)
    also have "\<dots> = \<Psi> (eval p1 v @@ eval f2 v \<union> eval q1 v @@ v x @@ eval f2 v)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = \<Psi> (eval p1 v @@ (eval p2 v \<union> eval q2 v @@ v x)
        \<union> eval q1 v @@ v x @@ (eval p2 v \<union> eval q2 v @@ v x))"
      using f2_subst by (smt (verit, ccfv_threshold) parikh_conc_right parikh_img_Un parikh_img_commut)
    also have "\<dots> = \<Psi> (eval p1 v @@ eval p2 v \<union> (eval p1 v @@ eval q2 v @@ v x \<union>
        eval q1 v @@ eval p2 v @@ v x \<union> eval q1 v @@ v x @@ eval q2 v @@ v x))"
      using parikh_img_commut by (smt (z3) conc_Un_distrib(1) parikh_conc_right parikh_img_Un sup_assoc)
    also have "\<dots> = \<Psi> (eval p1 v @@ eval p2 v \<union> (eval p1 v @@ eval q2 v \<union>
        eval q1 v @@ eval p2 v \<union> eval q1 v @@ v x @@ eval q2 v) @@ v x)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = \<Psi> (eval ?f' v)"
      by (simp add: Un_commute)
    finally show "\<Psi> (eval (Concat f1 f2) v) = \<Psi> (eval ?f' v)" .
  qed
  moreover have "bipart_rlexp x ?f'" unfolding bipart_rlexp_def using p1_q1_intro p2_q2_intro by auto
  moreover from f1'_intro f2'_intro p1_q1_intro p2_q2_intro
    have "vars ?f' = vars (Concat f1 f2) \<union> {x}" by auto
  ultimately show ?thesis by metis
qed

lemma reg_eval_bipart_rlexp_Star:
  assumes "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f \<union> {x}
                \<and> (\<forall>v. \<Psi> (eval f v) = \<Psi> (eval f' v))"
  shows "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars (Star f) \<union> {x}
                \<and> (\<forall>v. \<Psi> (eval (Star f) v) = \<Psi> (eval f' v))"
proof -
  from assms obtain f' where f'_intro: "bipart_rlexp x f' \<and> vars f' = vars f \<union> {x} \<and>
      (\<forall>v. \<Psi> (eval f v) = \<Psi> (eval f' v))" by auto
  then obtain p q where p_q_intro: "reg_eval p \<and> reg_eval q \<and>
    f' = Union p (Concat q (Var x)) \<and> (\<forall>y \<in> vars p. y \<noteq> x)" unfolding bipart_rlexp_def by auto
  let ?q_new = "Concat (Star p) (Concat (Star (Concat q (Var x))) (Concat (Star (Concat q (Var x))) q))"
  let ?f_new = "Union (Star p) (Concat ?q_new (Var x))"
  have "\<forall>v. (\<Psi> (eval (Star f) v) = \<Psi> (eval ?f_new v))"
  proof (rule allI)
    fix v
    have "\<Psi> (eval (Star f) v) = \<Psi> (star (eval p v \<union> eval q v @@ v x))"
      using f'_intro parikh_star_mono_eq p_q_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(4) eval.simps(5))
    also have "\<dots> = \<Psi> (star (eval p v) @@ star (eval q v @@ v x))"
      using parikh_img_star by blast
    also have "\<dots> = \<Psi> (star (eval p v) @@
        star ({[]} \<union> star (eval q v @@ v x) @@ eval q v @@ v x))"
      by (metis Un_commute conc_star_comm star_idemp star_unfold_left)
    also have "\<dots> = \<Psi> (star (eval p v) @@ star (star (eval q v @@ v x) @@ eval q v @@ v x))"
      by auto
    also have "\<dots> = \<Psi> (star (eval p v) @@ ({[]} \<union> star (eval q v @@ v x)
        @@ star (eval q v @@ v x) @@ eval q v @@ v x))"
      using parikh_img_star2 parikh_conc_left by blast
    also have "\<dots> = \<Psi> (star (eval p v) @@ {[]} \<union> star (eval p v) @@ star (eval q v @@ v x)
        @@ star (eval q v @@ v x) @@ eval q v @@ v x)" by (metis conc_Un_distrib(1))
    also have "\<dots> = \<Psi> (eval ?f_new v)" by (simp add: conc_assoc)
    finally show "\<Psi> (eval (Star f) v) = \<Psi> (eval ?f_new v)" .
  qed
  moreover have "bipart_rlexp x ?f_new" unfolding bipart_rlexp_def using p_q_intro by fastforce
  moreover from f'_intro p_q_intro have "vars ?f_new = vars (Star f) \<union> {x}" by auto
  ultimately show ?thesis by metis
qed

lemma reg_eval_bipart_rlexp: "reg_eval f \<Longrightarrow>
    \<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f \<union> {x} \<and>
         (\<forall>s. \<Psi> (eval f s) = \<Psi> (eval f' s))"
proof (induction f rule: reg_eval.induct)
  case (1 uu)
  from reg_eval_bipart_rlexp_Variable show ?case by blast
next
  case (2 l)
  then have "regular_lang l" by simp
  from reg_eval_bipart_rlexp_Const[OF this] show ?case by blast
next
  case (3 f g)
  then have "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f \<union> {x} \<and> (\<forall>v. \<Psi> (eval f v) = \<Psi> (eval f' v))"
            "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars g \<union> {x} \<and> (\<forall>v. \<Psi> (eval g v) = \<Psi> (eval f' v))"
    by auto
  from reg_eval_bipart_rlexp_Union[OF this] show ?case by blast
next
  case (4 f g)
  then have "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f \<union> {x} \<and> (\<forall>v. \<Psi> (eval f v) = \<Psi> (eval f' v))"
            "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars g \<union> {x} \<and> (\<forall>v. \<Psi> (eval g v) = \<Psi> (eval f' v))"
    by auto
  from reg_eval_bipart_rlexp_Concat[OF this] show ?case by blast
next
  case (5 f)
  then have "\<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f \<union> {x} \<and> (\<forall>v. \<Psi> (eval f v) = \<Psi> (eval f' v))"
    by auto
  from reg_eval_bipart_rlexp_Star[OF this] show ?case by blast
qed


subsection \<open>Minimal solution for a single equation\<close>

text \<open>The aim is to prove that every system of \<^const>\<open>reg_eval\<close> equations of the second type
has some minimal solution which is \<^const>\<open>reg_eval\<close>. In this section, we prove this property
only for the case of a single equation. First we assume that the equation is bipartite but later
in this section we will abandon this assumption.\<close>

locale single_bipartite_eq =
  fixes x :: "nat"
  fixes p :: "'a rlexp"
  fixes q :: "'a rlexp"
  assumes p_reg:      "reg_eval p"
  assumes q_reg:      "reg_eval q"
  assumes x_not_in_p: "x \<notin> vars p"
begin

text \<open>The equation and the minimal solution look as follows. Here, \<open>x\<close> describes the variable whose
solution is to be determined. In the subsequent lemmas, we prove that the solution is \<^const>\<open>reg_eval\<close>
and fulfills each of the three conditions of the predicate \<^const>\<open>partial_min_sol_one_ineq\<close>.
In particular, we will use the lemmas of the sections \ref{sec:rlexp_homogeneous} and
\ref{sec:parikh_arden} here:\<close>
abbreviation "eq \<equiv> Union p (Concat q (Var x))"
abbreviation "sol \<equiv> Concat (Star (subst (Var(x := p)) q)) p"

lemma sol_is_reg: "reg_eval sol"
proof -
  from p_reg q_reg have r_reg: "reg_eval (subst (Var(x := p)) q)"
    using subst_reg_eval_update by auto
  with p_reg show "reg_eval sol" by auto
qed

lemma sol_vars: "vars sol \<subseteq> vars eq - {x}"
proof -
  let ?upd = "Var(x := p)"
  let ?subst_q = "subst ?upd q"
  from x_not_in_p have vars_p: "vars p \<subseteq> vars eq - {x}" by fastforce
  moreover have "vars p \<union> vars q \<subseteq> vars eq" by auto
  ultimately have "vars ?subst_q \<subseteq> vars eq - {x}" using vars_subst_upd_upper by blast
  with x_not_in_p show ?thesis by auto
qed

lemma sol_is_sol_ineq: "partial_sol_ineq x eq sol"
unfolding partial_sol_ineq_def proof (rule allI, rule impI)
  fix v
  assume x_is_sol: "v x = eval sol v"
  let ?r = "subst (Var (x := p)) q"
  let ?upd = "Var(x := sol)"
  let ?q_subst = "subst ?upd q"
  let ?eq_subst = "subst ?upd eq"
  have homogeneous_app: "\<Psi> (eval ?q_subst v) \<subseteq> \<Psi> (eval (Concat (Star ?r) ?r) v)"
    using rlexp_homogeneous by blast
  from x_not_in_p have "eval (subst ?upd p) v = eval p v" using eval_vars_subst[of p] by simp
  then have "\<Psi> (eval ?eq_subst v) = \<Psi> (eval p v \<union> eval ?q_subst v @@ eval sol v)"
    by simp
  also have "\<dots> \<subseteq> \<Psi> (eval p v \<union> eval (Concat (Star ?r) ?r) v @@ eval sol v)"
    using homogeneous_app by (metis dual_order.refl parikh_conc_right_subset parikh_img_Un sup.mono)
  also have "\<dots> = \<Psi> (eval p v) \<union>
      \<Psi> (star (eval ?r v) @@ eval ?r v @@ star (eval ?r v) @@ eval p v)"
    by (simp add: conc_assoc)
  also have "\<dots> = \<Psi> (eval p v) \<union>
      \<Psi> (eval ?r v @@ star (eval ?r v) @@ eval p v)"
    using parikh_img_commut conc_star_star by (smt (verit, best) conc_assoc conc_star_comm)
  also have "\<dots> = \<Psi> (star (eval ?r v) @@ eval p v)"
    using star_unfold_left
    by (smt (verit) conc_Un_distrib(2) conc_assoc conc_epsilon(1) parikh_img_Un sup_commute)
  finally have *: "\<Psi> (eval ?eq_subst v) \<subseteq> \<Psi> (v x)" using x_is_sol by simp
  from x_is_sol have "v = v(x := eval sol v)" using fun_upd_triv by metis
  then have "eval eq v = eval (subst (Var(x := sol)) eq) v"
    using substitution_lemma_upd[where f=eq] by presburger
  with * show "solves_ineq_comm x eq v" unfolding solves_ineq_comm_def by argo
qed

lemma sol_is_minimal:
  assumes is_sol:    "solves_ineq_comm x eq v"
      and sol'_s:    "v x = eval sol' v"
    shows            "\<Psi> (eval sol v) \<subseteq> \<Psi> (v x)"
proof -
  from is_sol sol'_s have is_sol': "\<Psi> (eval q v @@ v x \<union> eval p v) \<subseteq> \<Psi> (v x)"
    unfolding solves_ineq_comm_def by simp
  then have 1: "\<Psi> (eval (Concat (Star q) p) v) \<subseteq> \<Psi> (v x)"
    using parikh_img_arden by auto
  from is_sol' have "\<Psi> (eval p v) \<subseteq> \<Psi> (eval (Var x) v)" by auto
  then have "\<Psi> (eval (subst (Var(x := p)) q) v) \<subseteq> \<Psi> (eval q v)"
    using parikh_img_subst_mono_upd by (metis fun_upd_triv subst_id)
  then have "\<Psi> (eval (Star (subst (Var(x := p)) q)) v) \<subseteq> \<Psi> (eval (Star q) v)"
    using parikh_star_mono by auto
  then have "\<Psi> (eval sol v) \<subseteq> \<Psi> (eval (Concat (Star q) p) v)"
    using parikh_conc_right_subset by (metis eval.simps(4))
  with 1 show ?thesis by fast
qed

text \<open>In summary, \<open>sol\<close> is a minimal partial solution and it is \<^const>\<open>reg_eval\<close>:\<close>
lemma sol_is_minimal_reg_sol:
  "reg_eval sol \<and> partial_min_sol_one_ineq x eq sol"
  unfolding partial_min_sol_one_ineq_def
  using sol_is_reg sol_vars sol_is_sol_ineq sol_is_minimal
  by blast

end


text \<open>As announced at the beginning of this section, we now extend the previous result to arbitrary
equations, i.e.\ we show that each \<^const>\<open>reg_eval\<close> equation has some minimal partial solution which is
\<^const>\<open>reg_eval\<close>:\<close>
lemma exists_minimal_reg_sol:
  assumes eq_reg: "reg_eval eq"
  shows "\<exists>sol. reg_eval sol \<and> partial_min_sol_one_ineq x eq sol"
proof -
  from reg_eval_bipart_rlexp[OF eq_reg] obtain eq'
    where eq'_intro: "bipart_rlexp x eq' \<and> vars eq' = vars eq \<union> {x} \<and>
                    (\<forall>v. \<Psi> (eval eq v) = \<Psi> (eval eq' v))" by blast
  then obtain p q
    where p_q_intro: "reg_eval p \<and> reg_eval q \<and> eq' = Union p (Concat q (Var x)) \<and> x \<notin> vars p"
    unfolding bipart_rlexp_def by blast
  let ?sol = "Concat (Star (subst (Var(x := p)) q)) p"
  from p_q_intro have sol_prop: "reg_eval ?sol \<and> partial_min_sol_one_ineq x eq' ?sol"
    using single_bipartite_eq.sol_is_minimal_reg_sol unfolding single_bipartite_eq_def by blast
  with eq'_intro have "partial_min_sol_one_ineq x eq ?sol"
    using same_min_sol_if_same_parikh_img by blast
  with sol_prop show ?thesis by blast
qed


subsection \<open>Minimal solution of the whole system of equations\<close>

text \<open>In this section we will extend the last section's result to whole systems of \<^const>\<open>reg_eval\<close>
equations. For this purpose, we will show by induction on \<open>r\<close> that the first \<open>r\<close> equations have
some minimal partial solution which is \<^const>\<open>reg_eval\<close>.

We start with the centerpiece of the induction step: If a \<^const>\<open>reg_eval\<close> and minimal partial solution
\<open>sols\<close> exists for the first \<open>r\<close> equations and furthermore a \<^const>\<open>reg_eval\<close> and minimal partial solution
\<open>sol_r\<close> exists for the \<open>r\<close>-th equation, then there exists a \<^const>\<open>reg_eval\<close> and minimal partial solution
for the first \<open>Suc r\<close> equations as well.\<close>

locale min_sol_induction_step =
  fixes r :: nat
    and sys :: "'a eq_sys"
    and sols :: "nat \<Rightarrow> 'a rlexp"
    and sol_r :: "'a rlexp"
  assumes eqs_reg:      "\<forall>eq \<in> set sys. reg_eval eq"
      and sys_valid:    "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
      and r_valid:      "r < length sys"
      and sols_is_sol:  "partial_min_sol_ineq_sys r sys sols"
      and sols_reg:     "\<forall>i. reg_eval (sols i)"
      and sol_r_is_sol: "partial_min_sol_one_ineq r (subst_sys sols sys ! r) sol_r"
      and sol_r_reg:    "reg_eval sol_r"
begin

text \<open>Throughout the proof, a modified system of equations will be occasionally used to simplify
the proof; this modified system is obtained by substituting the partial solutions of
the first \<open>r\<close> equations into the original system. Additionally
we retrieve a partial solution for the first \<open>Suc r\<close> equations - named \<open>sols'\<close> - by substituting the partial
solution of the \<open>r\<close>-th equation into the partial solutions of each of the first \<open>r\<close> equations:\<close>
abbreviation "sys' \<equiv> subst_sys sols sys"
abbreviation "sols' \<equiv> \<lambda>i. subst (Var(r := sol_r)) (sols i)"

lemma sols'_r: "sols' r = sol_r"
  using sols_is_sol unfolding partial_min_sol_ineq_sys_def by simp


text \<open>The next lemmas show that \<^const>\<open>sols'\<close> is still \<^const>\<open>reg_eval\<close> and that it complies with
each of the four conditions defined by the predicate \<^const>\<open>partial_min_sol_ineq_sys\<close>:\<close>
lemma sols'_reg: "\<forall>i. reg_eval (sols' i)"
  using sols_reg sol_r_reg using subst_reg_eval_update by blast

lemma sols'_is_sol: "solution_ineq_sys (take (Suc r) sys) sols'"
unfolding solution_ineq_sys_def proof (rule allI, rule impI)
  fix v
  assume s_sols': "\<forall>x. v x = eval (sols' x) v"
  from sols'_r s_sols' have s_r_sol_r: "v r = eval sol_r v" by simp
  with s_sols' have s_sols: "v x = eval (sols x) v" for x
    using substitution_lemma_upd[where f="sols x"] by (auto simp add: fun_upd_idem)
  with sols_is_sol have solves_r_sys: "solves_ineq_sys_comm (take r sys) v"
    unfolding partial_min_sol_ineq_sys_def solution_ineq_sys_def by meson
  have "eval (sys ! r) (\<lambda>y. eval (sols y) v) = eval (sys' ! r) v"
    using substitution_lemma[of "\<lambda>y. eval (sols y) v"]
    by (simp add: r_valid Suc_le_lessD subst_sys_subst)
  with s_sols have "eval (sys ! r) v = eval (sys' ! r) v"
    by (metis (mono_tags, lifting) eval_vars)
  with sol_r_is_sol s_r_sol_r have "\<Psi> (eval (sys ! r) v) \<subseteq> \<Psi> (v r)"
    unfolding partial_min_sol_one_ineq_def partial_sol_ineq_def solves_ineq_comm_def by simp
  with solves_r_sys show "solves_ineq_sys_comm (take (Suc r) sys) v"
    unfolding solves_ineq_sys_comm_def solves_ineq_comm_def by (auto simp add: less_Suc_eq)
qed

lemma sols'_min: "\<forall>sols2 v2. (\<forall>x. v2 x = eval (sols2 x) v2)
                   \<and> solves_ineq_sys_comm (take (Suc r) sys) v2
                   \<longrightarrow> (\<forall>i. \<Psi> (eval (sols' i) v2) \<subseteq> \<Psi> (v2 i))"
proof (rule allI | rule impI)+
  fix sols2 v2 i
  assume as: "(\<forall>x. v2 x = eval (sols2 x) v2) \<and> solves_ineq_sys_comm (take (Suc r) sys) v2"
  then have "solves_ineq_sys_comm (take r sys) v2" unfolding solves_ineq_sys_comm_def by fastforce
  with as sols_is_sol have sols_s2: "\<Psi> (eval (sols i) v2) \<subseteq> \<Psi> (v2 i)" for i
    unfolding partial_min_sol_ineq_sys_def by auto
  have "eval (sys' ! r) v2 = eval (sys ! r) (\<lambda>i. eval (sols i) v2)"
    unfolding subst_sys_def using substitution_lemma[where f="sys ! r"]
    by (simp add: r_valid Suc_le_lessD)
  with sols_s2 have "\<Psi> (eval (sys' ! r) v2) \<subseteq> \<Psi> (eval (sys ! r) v2)"
    using rlexp_mono_parikh[of "sys ! r"] by auto
  with as have "solves_ineq_comm r (sys' ! r) v2"
    unfolding solves_ineq_sys_comm_def solves_ineq_comm_def using r_valid by force
  with as sol_r_is_sol have sol_r_min: "\<Psi> (eval sol_r v2) \<subseteq> \<Psi> (v2 r)"
    unfolding partial_min_sol_one_ineq_def by blast
  let ?v' = "v2(r := eval sol_r v2)"
  from sol_r_min have "\<Psi> (?v' i) \<subseteq> \<Psi> (v2 i)" for i by simp
  with sols_s2 show "\<Psi> (eval (sols' i) v2) \<subseteq> \<Psi> (v2 i)"
    using substitution_lemma_upd[where f="sols i"] rlexp_mono_parikh[of "sols i" ?v' v2] by force
qed

lemma sols'_vars_gt_r: "\<forall>i \<ge> Suc r. sols' i = Var i"
  using sols_is_sol unfolding partial_min_sol_ineq_sys_def by auto

lemma sols'_vars_leq_r: "\<forall>i < Suc r. \<forall>x \<in> vars (sols' i). x \<ge> Suc r \<and> x < length sys"
proof -
  from sols_is_sol have "\<forall>i < r. \<forall>x \<in> vars (sols i). x \<ge> r \<and> x < length sys"
    unfolding partial_min_sol_ineq_sys_def by simp
  with sols_is_sol have vars_sols: "\<forall>i < length sys. \<forall>x \<in> vars (sols i). x \<ge> r \<and> x < length sys"
    unfolding partial_min_sol_ineq_sys_def by (metis empty_iff insert_iff leI vars.simps(1))
  with sys_valid have "\<forall>x \<in> vars (subst sols (sys ! i)). x \<ge> r \<and> x < length sys" if "i < length sys" for i
    using vars_subst[of sols "sys ! i"] that by (metis UN_E nth_mem)
  then have "\<forall>x \<in> vars (sys' ! i). x \<ge> r \<and> x < length sys" if "i < length sys" for i
    unfolding subst_sys_def using r_valid that by auto
  moreover from sol_r_is_sol have "vars (sol_r) \<subseteq> vars (sys' ! r) - {r}"
    unfolding partial_min_sol_one_ineq_def by simp
  ultimately have vars_sol_r: "\<forall>x \<in> vars sol_r. x > r \<and> x < length sys"
    unfolding partial_min_sol_one_ineq_def using r_valid
    by (metis DiffE insertCI nat_less_le subsetD)
  moreover have "vars (sols' i) \<subseteq> vars (sols i) - {r} \<union> vars sol_r" if "i < length sys" for i
    using vars_subst_upd_upper by meson
  ultimately have "\<forall>x \<in> vars (sols' i). x > r \<and> x < length sys" if "i < length sys" for i
    using vars_sols that by fastforce
  then show ?thesis by (meson r_valid Suc_le_eq dual_order.strict_trans1)
qed


text \<open>In summary, \<^const>\<open>sols'\<close> is a minimal partial solution of the first \<open>Suc r\<close> equations. This
allows us to prove the centerpiece of the induction step in the next lemma, namely that there exists
a \<^const>\<open>reg_eval\<close> and minimal partial solution for the first \<open>Suc r\<close> equations:\<close>
lemma sols'_is_min_sol: "partial_min_sol_ineq_sys (Suc r) sys sols'"
  unfolding partial_min_sol_ineq_sys_def
  using sols'_is_sol sols'_min sols'_vars_gt_r sols'_vars_leq_r
  by blast

lemma exists_min_sol_Suc_r:
  "\<exists>sols'. partial_min_sol_ineq_sys (Suc r) sys sols' \<and> (\<forall>i. reg_eval (sols' i))"
  using sols'_reg sols'_is_min_sol by blast

end


text \<open>Now follows the actual induction proof: For every \<open>r\<close>, there exists a \<^const>\<open>reg_eval\<close> and minimal partial
solution of the first \<open>r\<close> equations. This then implies that there exists a regular and minimal (non-partial)
solution of the whole system:\<close>
lemma exists_minimal_reg_sol_sys_aux:
  assumes eqs_reg:   "\<forall>eq \<in> set sys. reg_eval eq"
      and sys_valid: "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
      and r_valid:   "r \<le> length sys"   
    shows            "\<exists>sols. partial_min_sol_ineq_sys r sys sols \<and> (\<forall>i. reg_eval (sols i))"
using r_valid proof (induction r)
  case 0
  have "solution_ineq_sys (take 0 sys) Var"
    unfolding solution_ineq_sys_def solves_ineq_sys_comm_def by simp
  then show ?case unfolding partial_min_sol_ineq_sys_def by auto
next
  case (Suc r)
  then obtain sols where sols_intro: "partial_min_sol_ineq_sys r sys sols \<and> (\<forall>i. reg_eval (sols i))"
    by auto
  let ?sys' = "subst_sys sols sys"
  from eqs_reg Suc.prems have "reg_eval (sys ! r)" by simp
  with sols_intro Suc.prems have sys_r_reg: "reg_eval (?sys' ! r)"
    using subst_reg_eval[of "sys ! r"] subst_sys_subst[of r sys] by simp
  then obtain sol_r where sol_r_intro:
    "reg_eval sol_r \<and> partial_min_sol_one_ineq r (?sys' ! r) sol_r"
    using exists_minimal_reg_sol by blast
  with Suc sols_intro sys_valid eqs_reg have "min_sol_induction_step r sys sols sol_r"
    unfolding min_sol_induction_step_def by force
  from min_sol_induction_step.exists_min_sol_Suc_r[OF this] show ?case by blast
qed

lemma exists_minimal_reg_sol_sys:
  assumes eqs_reg:   "\<forall>eq \<in> set sys. reg_eval eq"
      and sys_valid: "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
    shows            "\<exists>sols. min_sol_ineq_sys_comm sys sols \<and> (\<forall>i. regular_lang (sols i))"
proof -
  from eqs_reg sys_valid have
    "\<exists>sols. partial_min_sol_ineq_sys (length sys) sys sols \<and> (\<forall>i. reg_eval (sols i))"
    using exists_minimal_reg_sol_sys_aux by blast
  then obtain sols where
    sols_intro: "partial_min_sol_ineq_sys (length sys) sys sols \<and> (\<forall>i. reg_eval (sols i))"
    by blast
  then have "const_rlexp (sols i)" if "i < length sys" for i
    using that unfolding partial_min_sol_ineq_sys_def by (meson equals0I leD)
  with sols_intro have "\<exists>l. regular_lang l \<and> (\<forall>v. eval (sols i) v = l)" if "i < length sys" for i
    using that const_rlexp_regular_lang by metis
  then obtain ls where ls_intro: "\<forall>i < length sys. regular_lang (ls i) \<and> (\<forall>v. eval (sols i) v = ls i)"
    by metis
  let ?ls' = "\<lambda>i. if i < length sys then ls i else {}"
  from ls_intro have ls'_intro:
    "(\<forall>i < length sys. regular_lang (?ls' i) \<and> (\<forall>v. eval (sols i) v = ?ls' i))
     \<and> (\<forall>i \<ge> length sys. ?ls' i = {})" by force
  then have ls'_regular: "regular_lang (?ls' i)" for i by (meson lang.simps(1))
  from ls'_intro sols_intro have "solves_ineq_sys_comm sys ?ls'"
    unfolding partial_min_sol_ineq_sys_def solution_ineq_sys_def
    by (smt (verit) eval.simps(1) linorder_not_less nless_le take_all_iff)
  moreover have "\<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. \<Psi> (?ls' x) \<subseteq> \<Psi> (sol' x))"
  proof (rule allI, rule impI)
    fix sol' x
    assume as: "solves_ineq_sys_comm sys sol'"
    let ?sol_rlexps = "\<lambda>i. Const (sol' i)"
    from as have "solves_ineq_sys_comm (take (length sys) sys) sol'" by simp
    moreover have "sol' x = eval (?sol_rlexps x) sol'" for x by simp
    ultimately show "\<forall>x. \<Psi> (?ls' x) \<subseteq> \<Psi> (sol' x)"
      using sols_intro unfolding partial_min_sol_ineq_sys_def
      by (smt (verit) empty_subsetI eval.simps(1) ls'_intro parikh_img_mono)
  qed
  ultimately have "min_sol_ineq_sys_comm sys ?ls'" unfolding min_sol_ineq_sys_comm_def by blast
  with ls'_regular show ?thesis by blast
qed



subsection \<open>Parikh's theorem\<close>

text \<open>Finally we are able to prove Parikh's theorem, i.e.\ that to each context free language exists
a regular language with identical Parikh image:\<close>
theorem Parikh:
  assumes "CFL (TYPE('n)) L"
  shows   "\<exists>L'. regular_lang L' \<and> \<Psi> L = \<Psi> L'"
proof -
  from assms obtain P and S::'n where *: "L = Lang P S \<and> finite P" unfolding CFL_def by blast
  show ?thesis
  proof (cases "S \<in> Nts P")
    case True
    from * finite_Nts exists_bij_Nt_Var obtain \<gamma> \<gamma>' where **: "bij_Nt_Var (Nts P) \<gamma> \<gamma>'" by metis
    let ?sol = "\<lambda>i. if i < card (Nts P) then Lang_lfp P (\<gamma> i) else {}"
    from ** True have "\<gamma>' S < card (Nts P)" "\<gamma> (\<gamma>' S) = S"
      unfolding bij_Nt_Var_def bij_betw_def by auto
    with Lang_lfp_eq_Lang have ***: "Lang P S = ?sol (\<gamma>' S)" by metis
    from * ** CFG_eq_sys.CFL_is_min_sol obtain sys
      where sys_intro: "(\<forall>eq \<in> set sys. reg_eval eq) \<and> (\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys)
                        \<and> min_sol_ineq_sys sys ?sol"
      unfolding CFG_eq_sys_def by blast
    with min_sol_min_sol_comm have sol_is_min_sol: "min_sol_ineq_sys_comm sys ?sol" by fast
    from sys_intro exists_minimal_reg_sol_sys obtain sol' where
      sol'_intro: "min_sol_ineq_sys_comm sys sol' \<and> regular_lang (sol' (\<gamma>' S))" by fastforce
    with sol_is_min_sol min_sol_comm_unique have "\<Psi> (?sol (\<gamma>' S)) = \<Psi> (sol' (\<gamma>' S))"
      by blast
    with * *** sol'_intro show ?thesis by auto
  next
    case False
    with Nts_Lhss_Rhs_Nts have "S \<notin> Lhss P" by fast
    from Lang_empty_if_notin_Lhss[OF this] * show ?thesis by (metis lang.simps(1))
  qed
qed

(* TODO rm with next release *)
lemma singleton_set_mset_subset: fixes X Y :: "'a list set"
  assumes "\<forall>xs \<in> X. set xs \<subseteq> {a}" "mset ` X \<subseteq> mset ` Y"
  shows "X \<subseteq> Y"
proof
  fix xs assume "xs \<in> X"
  obtain ys where ys: "ys \<in> Y" "mset xs = mset ys"
    using \<open>xs \<in> X\<close> assms(2) by auto
  then show "xs \<in> Y" using \<open>xs \<in> X\<close> assms(1) ys
    by (metis singleton_iff mset_eq_setD replicate_eqI set_empty subset_singletonD size_mset)
qed

lemma singleton_set_mset_eq: fixes X Y :: "'a list set"
  assumes "\<forall>xs \<in> X. set xs \<subseteq> {a}" "mset ` X = mset ` Y"
  shows "X = Y"
proof -
  have "\<forall>ys \<in> Y. set ys \<subseteq> {a}"
    by (metis (mono_tags, lifting) assms image_iff mset_eq_setD)
  thus ?thesis
    by (metis antisym assms(1,2) singleton_set_mset_subset subset_refl)
qed

lemma derives_tms_syms_subset:
  "P \<turnstile> \<alpha> \<Rightarrow>* \<gamma> \<Longrightarrow> tms_syms \<gamma> \<subseteq> tms_syms \<alpha> \<union> Tms P"
by(induction rule: derives_induct) (auto simp:tms_syms_def Tms_def)
(* end rm *)

text \<open>Corollary: Every context-free language over a single letter is regular.\<close>

corollary CFL_1_Tm_regular:
  assumes "CFL (TYPE('n)) L" and "\<forall>w \<in> L. set w \<subseteq> {a}"
  shows "regular_lang L"
proof -
  obtain L' where "regular_lang L'" "\<Psi> L = \<Psi> L'"
    using Parikh[OF assms(1)] by blast
  have "L = L'"
    by (metis \<open>\<Psi> L = \<Psi> L'\<close> \<open>\<forall>w\<in>L. set w \<subseteq> {a}\<close> parikh_img_def singleton_set_mset_eq)
  with \<open>regular_lang L'\<close> show ?thesis by blast
qed

corollary CFG_1_Tm_regular:
  assumes "finite P" "Tms P = {a}"
  shows "regular_lang (Lang P A)"
proof -
  let ?L = "Lang P A"
  have "\<forall>w \<in> ?L. set w \<subseteq> {a}"
    using derives_tms_syms_subset[of P "[Nt A]" "map Tm _"] assms(2)
    unfolding Lang_def tms_syms_def by auto
  thus ?thesis
    by (meson CFL_1_Tm_regular CFL_def assms(1))
qed

no_notation parikh_img ("\<Psi>")

end
