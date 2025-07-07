(* Authors: Fabian Lehr *)

section \<open>Context free grammars and systems of equations\<close>

theory Reg_Lang_Exp_Eqns
  imports
    "Parikh_Img"
    "Context_Free_Grammar.Context_Free_Language"
begin

text \<open>In this section, we will first introduce two types of systems of
equations. Then we will show that to each CFG corresponds a system of equations of the first type 
and that the language defined by the CFG is a minimal solution of this systems. Lastly we prove
some relations between the two types of systems of equations.\<close>


subsection \<open>Introduction of systems of equations\<close>

text \<open>For the first type of systems, each equation is of the form
\[X_i \supseteq r_i\]
For the second type of systems, each equation is of the form
\[\Psi \; X_i \supseteq \Psi \; r_i\]
i.e.\ the Parikh image is applied on both sides of each equation.
In both cases, we represent the whole system by a list of regular language expressions where each
of the variables \<open>X\<^sub>0, X\<^sub>1, \<dots>\<close> is identified by its integer, i.e.\ \<^term>\<open>Var i\<close> denotes the variable
\<open>X\<^sub>i\<close>. The \<open>i\<close>-th item of the list then represents the right-hand side \<open>r\<^sub>i\<close> of the \<open>i\<close>-th equation:\<close>

type_synonym 'a eq_sys = "'a rlexp list"


text \<open>Now we can define what it means for a valuation \<open>v\<close> to solve a system of equations of the
first type, i.e.\ a system without Parikh images. Afterwards we characterize minimal solutions of
such a system.\<close>
definition solves_ineq_sys :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_ineq_sys sys v \<equiv> \<forall>i < length sys. eval (sys ! i) v \<subseteq> v i"

definition min_sol_ineq_sys :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "min_sol_ineq_sys sys sol \<equiv>
    solves_ineq_sys sys sol \<and> (\<forall>sol'. solves_ineq_sys sys sol' \<longrightarrow> (\<forall>x. sol x \<subseteq> sol' x))"


text \<open>The previous definitions can easily be extended to the second type of systems of equations
where the Parikh image is applied on both sides of each equation:\<close>
definition solves_ineq_comm :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_ineq_comm x eq v \<equiv> \<Psi> (eval eq v) \<subseteq> \<Psi> (v x)"

definition solves_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_ineq_sys_comm sys v \<equiv> \<forall>i < length sys. solves_ineq_comm i (sys ! i) v"

definition min_sol_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "min_sol_ineq_sys_comm sys sol \<equiv>
    solves_ineq_sys_comm sys sol \<and>
    (\<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. \<Psi> (sol x) \<subseteq> \<Psi> (sol' x)))"

text \<open>Substitution into each equation of a system:\<close>
definition subst_sys :: "(nat \<Rightarrow> 'a rlexp) \<Rightarrow> 'a eq_sys \<Rightarrow> 'a eq_sys" where
  "subst_sys \<equiv> map \<circ> subst"

lemma subst_sys_subst:
  assumes "i < length sys"
  shows "(subst_sys s sys) ! i = subst s (sys ! i)"
  unfolding subst_sys_def by (simp add: assms)


subsection \<open>Partial solutions of systems of equations\<close>

text \<open>We introduce partial solutions, i.e.\ solutions which might depend on one or multiple
variables. They are therefore not represented as languages, but as regular language expressions.
\<open>sol\<close> is a partial solution of the \<open>x\<close>-th equation if and only if it solves the equation
independently on the values of the other variables:\<close>
definition partial_sol_ineq :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a rlexp \<Rightarrow> bool" where
  "partial_sol_ineq x eq sol \<equiv> \<forall>v. v x = eval sol v \<longrightarrow> solves_ineq_comm x eq v"

text \<open>We generalize the previous definition to partial solutions of whole systems of equations:
\<open>sols\<close> maps each variable \<open>i\<close> to a regular language expression representing the partial solution
of the \<open>i\<close>-th equation. \<open>sols\<close> is then a partial solution of the whole system if it satisfies the
following predicate:\<close>
definition solution_ineq_sys :: "'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a rlexp) \<Rightarrow> bool" where
  "solution_ineq_sys sys sols \<equiv> \<forall>v. (\<forall>x. v x = eval (sols x) v) \<longrightarrow> solves_ineq_sys_comm sys v"

text \<open>Given the \<open>x\<close>-th equation \<open>eq\<close>, \<open>sol\<close> is a minimal partial solution of this equation if and
only if
\begin{enumerate}
  \item \<open>sol\<close> is a partial solution of \<open>eq\<close>
  \item \<open>sol\<close> is a proper partial solution (i.e.\ it does not depend on \<open>x\<close>) and only
    depends on variables occurring in the equation \<open>eq\<close>
  \item no partial solution of the equation \<open>eq\<close> is smaller than \<open>sol\<close>
\end{enumerate}
\<close>
definition partial_min_sol_one_ineq :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a rlexp \<Rightarrow> bool" where
  "partial_min_sol_one_ineq x eq sol \<equiv>
    partial_sol_ineq x eq sol \<and>
    vars sol \<subseteq> vars eq - {x} \<and>
    (\<forall>sol' v'. solves_ineq_comm x eq v' \<and> v' x = eval sol' v'
               \<longrightarrow> \<Psi> (eval sol v') \<subseteq> \<Psi> (v' x))"

text \<open>Given a whole system of equations \<open>sys\<close>, we can generalize the previous definition such that
\<open>sols\<close> is a minimal solution (possibly dependent on the variables $X_n, X_{n+1}, \dots$) of
the first \<open>n\<close> equations. Besides the three conditions described above, we introduce a forth
condition: \<open>sols i = Var i\<close> for \<open>i \<ge> n\<close>, i.e.\ \<open>sols\<close> assigns only spurious solutions to the
equations which are not yet solved:\<close>
definition partial_min_sol_ineq_sys :: "nat \<Rightarrow> 'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a rlexp) \<Rightarrow> bool" where
  "partial_min_sol_ineq_sys n sys sols \<equiv>
    solution_ineq_sys (take n sys) sols \<and>
    (\<forall>i \<ge> n. sols i = Var i) \<and>
    (\<forall>i < n. \<forall>x \<in> vars (sols i). x \<ge> n \<and> x < length sys) \<and>
    (\<forall>sols' v'. (\<forall>x. v' x = eval (sols' x) v')
                  \<and> solves_ineq_sys_comm (take n sys) v'
                  \<longrightarrow> (\<forall>i. \<Psi> (eval (sols i) v') \<subseteq> \<Psi> (v' i)))"


text \<open>If the Parikh image of two equations \<open>f\<close> and \<open>g\<close> is identical on all valuations, then their
minimal partial solutions are identical, too:\<close>
lemma same_min_sol_if_same_parikh_img:
  assumes same_parikh_img: "\<forall>v. \<Psi> (eval f v) = \<Psi> (eval g v)"
      and same_vars:       "vars f - {x} = vars g - {x}"
      and minimal_sol:     "partial_min_sol_one_ineq x f sol"
    shows                  "partial_min_sol_one_ineq x g sol"
proof -
  from minimal_sol have "vars sol \<subseteq> vars g - {x}"
    unfolding partial_min_sol_one_ineq_def using same_vars by blast
  moreover from same_parikh_img minimal_sol have "partial_sol_ineq x g sol"
    unfolding partial_min_sol_one_ineq_def partial_sol_ineq_def solves_ineq_comm_def by simp
  moreover from same_parikh_img minimal_sol have "\<forall>sol' v'. solves_ineq_comm x g v' \<and> v' x = eval sol' v'
               \<longrightarrow> \<Psi> (eval sol v') \<subseteq> \<Psi> (v' x)"
    unfolding partial_min_sol_one_ineq_def solves_ineq_comm_def by blast
  ultimately show ?thesis unfolding partial_min_sol_one_ineq_def by fast
qed



subsection \<open>CFLs as minimal solutions to systems of equations\<close>

text \<open>\label{sec:cfl_as_eqns_sys}\<close>
text \<open>We show that each CFG induces a system of equations of the first type, i.e.\ without Parikh images,
such that each equation is \<^const>\<open>reg_eval\<close> and the CFG's language is the minimal solution of the system.
First, we describe how to derive the system of equations from a CFG. This requires us to fix some
bijection between the variables in the system and the non-terminals occurring in the CFG:\<close>

definition bij_Nt_Var :: "'n set \<Rightarrow> (nat \<Rightarrow> 'n) \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> bool" where
  "bij_Nt_Var A \<gamma> \<gamma>' \<equiv> bij_betw \<gamma> {..< card A} A \<and> bij_betw \<gamma>' A {..< card A}
                          \<and> (\<forall>x \<in> {..< card A}. \<gamma>' (\<gamma> x) = x) \<and> (\<forall>y \<in> A. \<gamma> (\<gamma>' y) = y)"

lemma exists_bij_Nt_Var:
  assumes "finite A"
  shows   "\<exists>\<gamma> \<gamma>'. bij_Nt_Var A \<gamma> \<gamma>'"
proof -
  from assms have "\<exists>\<gamma>. bij_betw \<gamma> {..< card A} A" by (simp add: bij_betw_iff_card)
  then obtain \<gamma> where 1: "bij_betw \<gamma> {..< card A} A" by blast
  let ?\<gamma>' = "the_inv_into {..< card A} \<gamma>"
  from the_inv_into_f_f 1 have 2: "\<forall>x \<in> {..< card A}. ?\<gamma>' (\<gamma> x) = x" unfolding bij_betw_def by fast
  from bij_betw_the_inv_into[OF 1] have 3: "bij_betw ?\<gamma>' A {..< card A}" by blast
  with 1 f_the_inv_into_f_bij_betw have 4: "\<forall>y \<in> A. \<gamma> (?\<gamma>' y) = y" by metis
  from 1 2 3 4 show ?thesis unfolding bij_Nt_Var_def by blast
qed


locale CFG_eq_sys =
  fixes P :: "('n,'a) Prods"
  fixes S :: 'n
  fixes \<gamma> :: "nat \<Rightarrow> 'n"
  fixes \<gamma>' :: "'n \<Rightarrow> nat"
  assumes finite_P: "finite P"
  assumes bij_\<gamma>_\<gamma>':  "bij_Nt_Var (Nts P) \<gamma> \<gamma>'"
begin

text \<open>The following definitions construct a regular language expression for a single production. This
happens step by step, i.e.\ starting with a single symbol (terminal or non-terminal) and then extending
this to a single production. The definitions closely follow the definitions \<^term>\<open>inst_sym\<close>,
\<^term>\<open>concats\<close> and \<^term>\<open>inst_syms\<close> in \<^theory>\<open>Context_Free_Grammar.Context_Free_Language\<close>.\<close>

definition rlexp_sym :: "('n, 'a) sym \<Rightarrow> 'a rlexp" where
  "rlexp_sym s = (case s of Tm a \<Rightarrow> Const {[a]} | Nt A \<Rightarrow> Var (\<gamma>' A))"

definition rlexp_concats :: "'a rlexp list \<Rightarrow> 'a rlexp" where
  "rlexp_concats fs = foldr Concat fs (Const {[]})"

definition rlexp_syms :: "('n, 'a) syms \<Rightarrow> 'a rlexp" where
  "rlexp_syms w = rlexp_concats (map rlexp_sym w)"


text \<open>Now it is shown that the regular language expression constructed for a single production
is \<^const>\<open>reg_eval\<close>. Again, this happens step by step:\<close>

lemma rlexp_sym_reg: "reg_eval (rlexp_sym s)"
unfolding rlexp_sym_def proof (induction s)
  case (Tm x)
  have "regular_lang {[x]}" by (meson lang.simps(3))
  then show ?case by auto
qed auto

lemma rlexp_concats_reg:
  assumes "\<forall>f \<in> set fs. reg_eval f"
    shows "reg_eval (rlexp_concats fs)"
  using assms unfolding rlexp_concats_def by (induction fs) (use epsilon_regular in auto)

lemma rlexp_syms_reg: "reg_eval (rlexp_syms w)"
proof -
  from rlexp_sym_reg have "\<forall>s \<in> set w. reg_eval (rlexp_sym s)" by blast
  with rlexp_concats_reg show ?thesis unfolding rlexp_syms_def
    by (metis (no_types, lifting) image_iff list.set_map)
qed


text \<open>The subsequent lemmas prove that all variables appearing in the regular language
expression of a single production correspond to non-terminals appearing in the production:\<close>

lemma rlexp_sym_vars_Nt:
  assumes "s (\<gamma>' A) = L A"
    shows "vars (rlexp_sym (Nt A)) = {\<gamma>' A}"
  using assms unfolding rlexp_sym_def by simp

lemma rlexp_sym_vars_Tm: "vars (rlexp_sym (Tm x)) = {}"
  unfolding rlexp_sym_def by simp

lemma rlexp_concats_vars: "vars (rlexp_concats fs) = \<Union>(vars ` set fs)"
  unfolding rlexp_concats_def by (induction fs) simp_all

(* it even holds equality, but we will not need it *)
lemma insts'_vars: "vars (rlexp_syms w) \<subseteq> \<gamma>' ` nts_syms w"
proof
  fix x
  assume "x \<in> vars (rlexp_syms w)"
  with rlexp_concats_vars have "x \<in> \<Union>(vars ` set (map rlexp_sym w))"
    unfolding rlexp_syms_def by blast
  then obtain f where *: "f \<in> set (map rlexp_sym w) \<and> x \<in> vars f" by blast
  then obtain s where **: "s \<in> set w \<and> rlexp_sym s = f" by auto
  with * rlexp_sym_vars_Tm obtain A where ***: "s = Nt A" by (metis empty_iff sym.exhaust)
  with ** have ****: "A \<in> nts_syms w" unfolding nts_syms_def by blast
  with rlexp_sym_vars_Nt have "vars (rlexp_sym (Nt A)) = {\<gamma>' A}" by blast
  with * ** *** **** show "x \<in> \<gamma>' ` nts_syms w" by blast
qed


text \<open>Evaluating the regular language expression of a single production under a valuation
corresponds to instantiating the non-terminals in the production according to the valuation:\<close>

lemma rlexp_sym_inst_Nt:
  assumes "v (\<gamma>' A) = L A"
    shows "eval (rlexp_sym (Nt A)) v = inst_sym L (Nt A)"
  using assms unfolding rlexp_sym_def inst_sym_def by force

lemma rlexp_sym_inst_Tm: "eval (rlexp_sym (Tm a)) v = inst_sym L (Tm a)"
  unfolding rlexp_sym_def inst_sym_def by force

lemma rlexp_concats_concats:
  assumes "length fs = length Ls"
      and "\<forall>i < length fs. eval (fs ! i) v = Ls ! i"
    shows "eval (rlexp_concats fs) v = concats Ls"
using assms proof (induction fs arbitrary: Ls)
  case Nil
  then show ?case unfolding rlexp_concats_def concats_def by simp
next
  case (Cons f1 fs)
  then obtain L1 Lr where *: "Ls = L1#Lr" by (metis length_Suc_conv)
  with Cons have "eval (rlexp_concats fs) v = concats Lr" by fastforce
  moreover from Cons.prems * have "eval f1 v = L1" by force
  ultimately show ?case unfolding rlexp_concats_def concats_def by (simp add: "*")
qed

lemma rlexp_syms_insts:
  assumes "\<forall>A \<in> nts_syms w. v (\<gamma>' A) = L A"
    shows "eval (rlexp_syms w) v = inst_syms L w"
proof -
  have "\<forall>i < length w. eval (rlexp_sym (w!i)) v = inst_sym L (w!i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < length w"
    then show "eval (rlexp_sym (w ! i)) v = inst_sym L (w ! i)"
      proof (induction "w!i")
      case (Nt A)
      with assms have "v (\<gamma>' A) = L A" unfolding nts_syms_def by force
      with rlexp_sym_inst_Nt Nt show ?case by metis
    next
      case (Tm x)
      with rlexp_sym_inst_Tm show ?case by metis
    qed
  qed
  then show ?thesis unfolding rlexp_syms_def inst_syms_def using rlexp_concats_concats
    by (metis (mono_tags, lifting) length_map nth_map)
qed


text \<open>Each non-terminal of the CFG induces some \<^const>\<open>reg_eval\<close> equation. We do not directly construct
the equation but only prove its existence:\<close>
lemma subst_lang_rlexp:
  "\<exists>eq. reg_eval eq \<and> vars eq \<subseteq> \<gamma>' ` Nts P
         \<and> (\<forall>v L. (\<forall>A \<in> Nts P. v (\<gamma>' A) = L A) \<longrightarrow> eval eq v = subst_lang P L A)"
proof -
  let ?Insts = "rlexp_syms ` (Rhss P A)"
  from finite_Rhss[OF finite_P] have "finite ?Insts" by simp
  moreover from rlexp_syms_reg have "\<forall>f \<in> ?Insts. reg_eval f" by blast
  ultimately obtain eq where *: "reg_eval eq \<and> \<Union>(vars ` ?Insts) = vars eq
                                  \<and> (\<forall>v. (\<Union>f \<in> ?Insts. eval f v) = eval eq v)"
    using finite_Union_regular by metis
  moreover have "vars eq \<subseteq> \<gamma>' ` Nts P"
  proof
    fix x
    assume "x \<in> vars eq"
    with * obtain f where **: "f \<in> ?Insts \<and> x \<in> vars f" by blast
    then obtain w where ***: "w \<in> Rhss P A \<and> f = rlexp_syms w" by blast
    with ** insts'_vars have "x \<in> \<gamma>' ` nts_syms w" by auto
    with *** show "x \<in> \<gamma>' ` Nts P" unfolding Nts_def Rhss_def by blast
  qed
  moreover have "\<forall>v L. (\<forall>A \<in> Nts P. v (\<gamma>' A) = L A) \<longrightarrow> eval eq v = subst_lang P L A"
  proof (rule allI | rule impI)+
    fix v :: "nat \<Rightarrow> 'a lang" and L :: "'n \<Rightarrow> 'a lang"
    assume state_L: "\<forall>A \<in> Nts P. v (\<gamma>' A) = L A"
    have "\<forall>w \<in> Rhss P A. eval (rlexp_syms w) v = inst_syms L w"
    proof
      fix w
      assume "w \<in> Rhss P A"
      with state_L Nts_nts_syms have "\<forall>A \<in> nts_syms w. v (\<gamma>' A) = L A" by fast
      from rlexp_syms_insts[OF this] show "eval (rlexp_syms w) v = inst_syms L w" by blast
    qed
    then have "subst_lang P L A = (\<Union>f \<in> ?Insts. eval f v)" unfolding subst_lang_def by auto
    with * show "eval eq v = subst_lang P L A" by auto
  qed
  ultimately show ?thesis by auto
qed


text \<open>The whole CFG induces a system of \<^const>\<open>reg_eval\<close> equations. We first define which conditions
this system should fulfill and show its existence in the second step:\<close>

abbreviation "CFG_sys sys \<equiv>
  length sys = card (Nts P) \<and>
    (\<forall>i < card (Nts P). reg_eval (sys ! i) \<and> (\<forall>x \<in> vars (sys ! i). x < card (Nts P))
                        \<and> (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A)
                            \<longrightarrow> eval (sys ! i) s = subst_lang P L (\<gamma> i)))"

lemma CFG_as_eq_sys: "\<exists>sys. CFG_sys sys"
proof -
  from bij_\<gamma>_\<gamma>' have *: "\<And>eq. vars eq \<subseteq> \<gamma>' ` Nts P \<Longrightarrow> \<forall>x \<in> vars eq. x < card (Nts P)"
    unfolding bij_Nt_Var_def bij_betw_def by auto
  from subst_lang_rlexp have "\<forall>A. \<exists>eq. reg_eval eq \<and> vars eq \<subseteq> \<gamma>' ` Nts P \<and>
                             (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A) \<longrightarrow> eval eq s = subst_lang P L A)"
    by blast
  with bij_\<gamma>_\<gamma>' * have "\<forall>i < card (Nts P). \<exists>eq. reg_eval eq \<and> (\<forall>x \<in> vars eq. x < card (Nts P))
                    \<and> (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A) \<longrightarrow> eval eq s = subst_lang P L (\<gamma> i))"
    unfolding bij_Nt_Var_def by metis
  with Skolem_list_nth[where P="\<lambda>i eq. reg_eval eq \<and> (\<forall>x \<in> vars eq. x < card (Nts P))
                       \<and> (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A) \<longrightarrow> eval eq s = subst_lang P L (\<gamma> i))"]
    show ?thesis by blast
qed


text \<open>As we have proved that each CFG induces a system of \<^const>\<open>reg_eval\<close> equations, it remains to
show that the  CFG's language is a minimal solution of this system. The first lemma proves that
the CFG's language is a solution and the next two lemmas prove that it is minimal:\<close>

abbreviation "sol \<equiv> \<lambda>i. if i < card (Nts P) then Lang_lfp P (\<gamma> i) else {}"

lemma CFG_sys_CFL_is_sol:
  assumes "CFG_sys sys"
  shows "solves_ineq_sys sys sol"
unfolding solves_ineq_sys_def proof (rule allI, rule impI)
  fix i
  assume "i < length sys"
  with assms have "i < card (Nts P)" by argo
  from bij_\<gamma>_\<gamma>' have *: "\<forall>A \<in> Nts P. sol (\<gamma>' A) = Lang_lfp P A"
    unfolding bij_Nt_Var_def bij_betw_def by force
  with \<open>i < card (Nts P)\<close> assms have "eval (sys ! i) sol = subst_lang P (Lang_lfp P) (\<gamma> i)"
    by presburger
  with lfp_fixpoint[OF mono_if_omega_cont[OF omega_cont_Lang_lfp]] have 1: "eval (sys ! i) sol = Lang_lfp P (\<gamma> i)"
    unfolding Lang_lfp_def by metis
  from \<open>i < card (Nts P)\<close> bij_\<gamma>_\<gamma>' have "\<gamma> i \<in> Nts P"
    unfolding bij_Nt_Var_def using bij_betwE by blast
  with * have "Lang_lfp P (\<gamma> i) = sol (\<gamma>' (\<gamma> i))" by auto
  also have "\<dots> = sol i" using bij_\<gamma>_\<gamma>' \<open>i < card (Nts P)\<close> unfolding bij_Nt_Var_def by auto
  finally show "eval (sys ! i) sol \<subseteq> sol i" using 1 by blast
qed

lemma CFG_sys_CFL_is_min_aux:
  assumes "CFG_sys sys"
      and "solves_ineq_sys sys sol'"
    shows "Lang_lfp P \<le> (\<lambda>A. sol' (\<gamma>' A))" (is "_ \<le> ?L'")
proof -
  have "subst_lang P ?L' A \<subseteq> ?L' A" for A
  proof (cases "A \<in> Nts P")
    case True
    with assms(1) bij_\<gamma>_\<gamma>' have "\<gamma>' A < length sys"
      unfolding bij_Nt_Var_def bij_betw_def by fastforce
    with assms(1) bij_\<gamma>_\<gamma>' True have "subst_lang P ?L' A = eval (sys ! \<gamma>' A) sol'"
      unfolding bij_Nt_Var_def by metis
    also from True assms(2) \<open>\<gamma>' A < length sys\<close> bij_\<gamma>_\<gamma>' have "\<dots> \<subseteq> ?L' A"
      unfolding solves_ineq_sys_def bij_Nt_Var_def by blast
    finally show ?thesis .
  next
    case False
    then have "Rhss P A = {}" unfolding Nts_def Rhss_def by blast
    with False show ?thesis unfolding subst_lang_def by simp
  qed
  then have "subst_lang P ?L' \<le> ?L'" by (simp add: le_funI)
  from lfp_lowerbound[of "subst_lang P", OF this] Lang_lfp_def show ?thesis by metis
qed

lemma CFG_sys_CFL_is_min:
  assumes "CFG_sys sys"
      and "solves_ineq_sys sys sol'"
    shows "sol x \<subseteq> sol' x"
proof (cases "x < card (Nts P)")
  case True
  then have "sol x = Lang_lfp P (\<gamma> x)" by argo
  also from CFG_sys_CFL_is_min_aux[OF assms] have "\<dots> \<subseteq> sol' (\<gamma>' (\<gamma> x))" by (simp add: le_fun_def)
  finally show ?thesis using True bij_\<gamma>_\<gamma>' unfolding bij_Nt_Var_def by auto
next
  case False
  then show ?thesis by auto
qed


text \<open>Lastly we combine all of the previous lemmas into the desired result of this section, namely
that each CFG induces a system of \<^const>\<open>reg_eval\<close> equations such that the CFG's language is a
minimal solution of the system:\<close>
lemma CFL_is_min_sol:
  "\<exists>sys. (\<forall>eq \<in> set sys. reg_eval eq) \<and> (\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys)
          \<and> min_sol_ineq_sys sys sol"
proof -
  from CFG_as_eq_sys obtain sys where *: "CFG_sys sys" by blast
  then have "length sys = card (Nts P)" by blast
  moreover from * have "\<forall>eq \<in> set sys. reg_eval eq" by (simp add: all_set_conv_all_nth)
  moreover from * \<open>length sys = card (Nts P)\<close> have "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
    by (simp add: all_set_conv_all_nth)
  moreover from CFG_sys_CFL_is_sol[OF *] CFG_sys_CFL_is_min[OF *]
    have "min_sol_ineq_sys sys sol" unfolding min_sol_ineq_sys_def by blast
  ultimately show ?thesis by blast
qed

end


subsection \<open>Relation between the two types of systems of equations\<close>

text \<open>\label{sec:eqns_sys_relations}\<close>
text \<open>One can simply convert a system \<open>sys\<close> of equations of the second type (i.e.\ with Parikh
images) into a system of equations of the first type by dropping the Parikh images on both sides of
each equation. The following lemmas describe how the two systems are related to each other.

First of all, to any solution \<open>sol\<close> of \<open>sys\<close> exists a valuation whose Parikh image is
identical to that of \<open>sol\<close> and which is a solution of the other system (i.e.\ the system obtained
by dropping all Parikh images in \<open>sys\<close>). The following proof explicitly gives such a solution,
namely \<^term>\<open>\<lambda>x. \<Union>(parikh_img_eq_class (sol x))\<close>, benefiting from the results of section \ref{sec:parikh_eq_class}:\<close>
lemma sol_comm_sol:
  assumes sol_is_sol_comm: "solves_ineq_sys_comm sys sol"
  shows   "\<exists>sol'. (\<forall>x. \<Psi> (sol x) = \<Psi> (sol' x)) \<and> solves_ineq_sys sys sol'"
proof
  let ?sol' = "\<lambda>x. \<Union>(parikh_img_eq_class (sol x))"
  have sol'_sol: "\<forall>x. \<Psi> (?sol' x) = \<Psi> (sol x)"
      using parikh_img_Union_class by metis
  moreover have "solves_ineq_sys sys ?sol'"
  unfolding solves_ineq_sys_def proof (rule allI, rule impI)
    fix i
    assume "i < length sys"
    with sol_is_sol_comm have "\<Psi> (eval (sys ! i) sol) \<subseteq> \<Psi> (sol i)"
      unfolding solves_ineq_sys_comm_def solves_ineq_comm_def by blast
    moreover from sol'_sol have "\<Psi> (eval (sys ! i) ?sol') = \<Psi> (eval (sys ! i) sol)"
      using rlexp_mono_parikh_eq by meson
    ultimately have "\<Psi> (eval (sys ! i) ?sol') \<subseteq> \<Psi> (sol i)" by simp
    then show "eval (sys ! i) ?sol' \<subseteq> ?sol' i" using subseteq_comm_subseteq by metis
  qed
  ultimately show "(\<forall>x. \<Psi> (sol x) = \<Psi> (?sol' x)) \<and> solves_ineq_sys sys ?sol'"
    by simp
qed

text \<open>The converse works similarly: Given a minimal solution \<open>sol\<close> of the system \<open>sys\<close> of the first type,
then \<open>sol\<close> is also a minimal solution to the system obtained by converting \<open>sys\<close> into a system of the second
type (which can be achieved by applying the Parikh image on both sides of each equation):\<close>
lemma min_sol_min_sol_comm:
  assumes "min_sol_ineq_sys sys sol"
    shows "min_sol_ineq_sys_comm sys sol"
unfolding min_sol_ineq_sys_comm_def proof
  from assms show "solves_ineq_sys_comm sys sol"
    unfolding min_sol_ineq_sys_def min_sol_ineq_sys_comm_def solves_ineq_sys_def
      solves_ineq_sys_comm_def solves_ineq_comm_def by (simp add: parikh_img_mono)
  show " \<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. \<Psi> (sol x) \<subseteq> \<Psi> (sol' x))"
  proof (rule allI, rule impI)
    fix sol'
    assume "solves_ineq_sys_comm sys sol'"
    with sol_comm_sol obtain sol'' where sol''_intro:
      "(\<forall>x. \<Psi> (sol' x) = \<Psi> (sol'' x)) \<and> solves_ineq_sys sys sol''" by meson
    with assms have "\<forall>x. sol x \<subseteq> sol'' x" unfolding min_sol_ineq_sys_def by auto
    with sol''_intro show "\<forall>x. \<Psi> (sol x) \<subseteq> \<Psi> (sol' x)"
      using parikh_img_mono by metis
  qed
qed

text \<open>All minimal solutions of a system of the second type have the same Parikh image:\<close>
lemma min_sol_comm_unique:
  assumes sol1_is_min_sol: "min_sol_ineq_sys_comm sys sol1"
      and sol2_is_min_sol: "min_sol_ineq_sys_comm sys sol2"
    shows                  "\<Psi> (sol1 x) = \<Psi> (sol2 x)"
proof -
  from sol1_is_min_sol sol2_is_min_sol have "\<Psi> (sol1 x) \<subseteq> \<Psi> (sol2 x)"
    unfolding min_sol_ineq_sys_comm_def by simp
  moreover from sol1_is_min_sol sol2_is_min_sol have "\<Psi> (sol2 x) \<subseteq> \<Psi> (sol1 x)"
    unfolding min_sol_ineq_sys_comm_def by simp
  ultimately show ?thesis by blast
qed

end
