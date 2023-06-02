theory MLSS_Suc_Theory
  imports Main "HOL-Library.Adhoc_Overloading" Fresh_Identifiers.Fresh
begin

section \<open>Solver for the Theory of the Successor Function\<close>
text \<open>
  This theory implements a solver for the theory consisting of
  variables, 0, and the successor function.
  We only deal with equality and not with disequality or inequality.
  Disequalities of the form \<^term>\<open>l \<noteq> 0\<close> are translated to
  \<^term>\<open>l = Suc x\<close> for some fresh \<^term>\<open>x\<close>.

  Note that disequalities and inequalities can always be fulfilled
  by choosing large enough values for the variables.
\<close>

datatype 'a suc_term = Var 'a | Zero | Succ nat "'a suc_term"

datatype 'a suc_atom = is_Eq: Eq "'a suc_term" "'a suc_term" | is_NEq: NEq "'a suc_term" "'a suc_term"

lemma finite_set_suc_term[simp]: "finite (set_suc_term t)"
  by (induction t) auto

lemma finite_set_suc_atom[simp]: "finite (set_suc_atom a)"
  by (cases a) auto

fun succ :: "nat \<Rightarrow> 'a suc_term \<Rightarrow> 'a suc_term" where
  "succ n (Succ k t) = succ (n + k) t"
| "succ 0 t = t"
| "succ n t = Succ n t"

fun is_Succ_normal_term :: "'a suc_term \<Rightarrow> bool" where
  "is_Succ_normal_term (Var _) \<longleftrightarrow> True"
| "is_Succ_normal_term Zero \<longleftrightarrow> True"
| "is_Succ_normal_term (Succ n Zero) \<longleftrightarrow> n \<noteq> 0"
| "is_Succ_normal_term (Succ n (Var _)) \<longleftrightarrow> n \<noteq> 0"
| "is_Succ_normal_term (Succ _ (Succ _ _)) \<longleftrightarrow> False"

lemma not_is_Succ_normal_Succ_0[simp]: "\<not> is_Succ_normal_term (Succ 0 t)"
  by (cases t) auto

lemma is_Succ_normal_term_SuccD[simp]: "is_Succ_normal_term (Succ n t) \<Longrightarrow> is_Succ_normal_term t"
  by (cases t) auto

fun is_Succ_normal_atom :: "'a suc_atom \<Rightarrow> bool" where
  "is_Succ_normal_atom (Eq t1 t2) \<longleftrightarrow> is_Succ_normal_term t1 \<and> is_Succ_normal_term t2"
| "is_Succ_normal_atom (NEq t1 t2) \<longleftrightarrow> is_Succ_normal_term t1 \<and> is_Succ_normal_term t2"

consts is_Succ_normal :: "'a \<Rightarrow> bool"
adhoc_overloading is_Succ_normal is_Succ_normal_term is_Succ_normal_atom

fun I_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a suc_term \<Rightarrow> nat" where
  "I_term v (Var x) = v x"
| "I_term v Zero = 0"
| "I_term v (Succ n t) = (Suc ^^ n) (I_term v t)"

fun I_atom :: "('a \<Rightarrow> nat) \<Rightarrow> 'a suc_atom \<Rightarrow> bool" where
  "I_atom v (Eq t1 t2) \<longleftrightarrow> I_term v t1 = I_term v t2"
| "I_atom v (NEq t1 t2) \<longleftrightarrow> I_term v t1 \<noteq> I_term v t2"

fun subst_term :: "('a \<Rightarrow> 'a suc_term) \<Rightarrow> 'a suc_term \<Rightarrow> 'a suc_term" where
  "subst_term \<sigma> (Var x) = succ 0 (\<sigma> x)"
| "subst_term _ Zero = Zero"
| "subst_term \<sigma> (Succ n t) = succ n (subst_term \<sigma> t)"

fun subst_atom :: "('a \<Rightarrow> 'a suc_term) \<Rightarrow> 'a suc_atom \<Rightarrow> 'a suc_atom" where
  "subst_atom \<sigma> (Eq t1 t2) = Eq (subst_term \<sigma> t1) (subst_term \<sigma> t2)"
| "subst_atom \<sigma> (NEq t1 t2) = NEq (subst_term \<sigma> t1) (subst_term \<sigma> t2)"

lemma I_term_succ: "I_term v (succ n t) = I_term v (Succ n t)"
  by (induction n t rule: succ.induct) auto

lemma is_Succ_normal_succ[simp]: "is_Succ_normal (succ n t)"
  by (induction n t rule: succ.induct) auto

lemma is_Succ_normal_subst_term[simp]: "is_Succ_normal (subst_term \<sigma> t)"
  by (induction t) auto

lemma is_Succ_normal_subst_atom[simp]: "is_Succ_normal (subst_atom \<sigma> a)"
  by (cases a) simp_all

lemma is_NEq_subst_atom[simp]:
  "is_NEq (subst_atom v a) \<longleftrightarrow> is_NEq a"
  by (cases a) auto

abbreviation solve_Var_Eq_Succ where
"solve_Var_Eq_Succ solve x n t es \<equiv>
    (if (Var x) = t
      then (if n = 0 then solve es else None)
      else map_option ((#) (Eq (Var x) (succ n t)))
            (solve (map (subst_atom (Var(x := succ n t))) es))
    )"

lemma size_succ_leq[termination_simp]: "size (succ n t) \<le> Suc (size t)"
  by (induction n t rule: succ.induct) auto

function (sequential) solve :: "'a suc_atom list \<Rightarrow> 'a suc_atom list option" where
  "solve [] = Some []"
| "solve (Eq (Var x) (Var y) # es) = solve_Var_Eq_Succ solve x 0 (Var y) es"
| "solve (Eq (Var x) (Succ n t) # es) = solve_Var_Eq_Succ solve x n t es"
| "solve (Eq (Succ n t) (Var x) # es) = solve_Var_Eq_Succ solve x n t es"
| "solve (Eq (Succ n s) (Succ k t) # es) =
    (if n \<ge> k
      then solve (Eq t (succ (n - k) s) # es)
      else solve (Eq s (succ (k - n) t) # es)
    )"
| "solve (Eq Zero Zero # es) = solve es"
| "solve (Eq Zero (Var x) # es) = solve_Var_Eq_Succ solve x 0 Zero es"
| "solve (Eq (Var x) Zero # es) = solve_Var_Eq_Succ solve x 0 Zero es"
| "solve (Eq Zero (Succ 0 t) # es) = solve (Eq t Zero # es)"
| "solve (Eq Zero (Succ n t) # es) = None"
| "solve (Eq (Succ 0 t) Zero # es) = solve (Eq t Zero # es)"
| "solve (Eq (Succ n t) Zero # es) = None"
  by pat_completeness auto
termination by size_change


abbreviation "is_normal a \<equiv> \<not> is_NEq a \<and> is_Succ_normal a"

lemma is_Succ_normal_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "a \<in> set ss"
  shows "is_Succ_normal a"
  using assms
  by (induction es arbitrary: ss rule: solve.induct) (auto split: if_splits)

lemma I_term_subst_term:
  assumes "I_atom v (Eq (Var x) t)"
  shows "I_term v (subst_term (Var(x := t)) s) = I_term v s"
  using assms
  by (induction s) (auto simp: I_term_succ)

lemma I_atom_subst_atom:
  assumes "I_atom v (Eq (Var x) t)"
  shows "I_atom v (subst_atom (Var(x := t)) a) \<longleftrightarrow> I_atom v a"
  using assms
  by (cases a) (auto simp: I_term_subst_term)

lemma I_atom_solve_None:
  assumes "solve es = None" "\<forall>a \<in> set es. is_normal a"
  shows "\<exists>a \<in> set es. \<not> I_atom v a"
proof -
  have "False" if "\<forall>a \<in> set es. I_atom v a"
    using assms that
    by (induction es rule: solve.induct)
       (force simp: I_atom_subst_atom I_term_succ split: if_splits)+
  then show ?thesis
    by blast
qed

lemma set_suc_term_succ[simp]: "set_suc_term (succ n t) = set_suc_term t"
  by (induction n t rule: succ.induct) auto

lemma not_mem_subst_term_self:
  assumes "x \<notin> set_suc_term t"
  shows "x \<notin> set_suc_term (subst_term (Var(x := t)) s)"
  using assms
  by (induction s) auto

lemma not_mem_subst_atom_self:
  assumes "x \<notin> set_suc_term t"
  shows "x \<notin> set_suc_atom (subst_atom (Var(x := t)) a)"
  using not_mem_subst_term_self[OF assms] by (cases a) simp_all

lemma not_mem_subst_term:
  assumes "z \<notin> set_suc_term t" "z \<notin> set_suc_term s"
  shows "z \<notin> set_suc_term (subst_term (Var(x := t)) s)"
  using assms 
  by (induction s) auto

lemma not_mem_subst_atom:
  assumes "z \<notin> set_suc_term t" "z \<notin> set_suc_atom a"
  shows "z \<notin> set_suc_atom (subst_atom (Var(x := t)) a)"
  using not_mem_subst_term[OF assms(1)] assms(2) by (cases a) simp_all

lemma not_mem_suc_atom_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "\<forall>a \<in> set es. z \<notin> set_suc_atom a"
  shows "\<forall>a \<in> set ss. z \<notin> set_suc_atom a"
  using assms
  by (induction es arbitrary: ss rule: solve.induct)
     (force simp: not_mem_subst_atom split: if_splits)+

lemma not_mem_suc_atom_if_solve:
  assumes "solve es = Some (Eq (Var x) t # ss)" "\<forall>a \<in> set es. is_normal a"
  shows "\<forall>a \<in> set ss. x \<notin> set_suc_atom a"
  using assms
proof(induction es arbitrary: ss rule: solve.induct)
  case (2 y z es)
  note not_mem_suc_atom_solve[where ?es="map (subst_atom (Var(y := Var z))) es" and ?z=y]
  with 2 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
next
  case (3 y n t es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(y := succ n t))) es" and ?z=y]
  with 3 show ?case
    apply (simp split: if_splits)
    by (metis is_Succ_normal_term.simps(5) not_mem_subst_atom_self set_suc_term_succ suc_term.set_cases)
next                                                                     
  case (4 n t y es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(y := succ n t))) es" and ?z=y]
  with 4 show ?case
    apply (simp split: if_splits)
    by (metis is_Succ_normal_term.simps(5) not_mem_subst_atom_self set_suc_term_succ suc_term.set_cases)
next
  case (7 y es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(y := Zero))) es" and ?z=y]
  with 7 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
next
  case (8 y es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(y := Zero))) es" and ?z=y]
  with 8 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
qed (auto split: if_splits)

fun assign :: "'a suc_atom list \<Rightarrow> ('a \<Rightarrow> nat)" where
  "assign [] = (\<lambda>x. 0)"
| "assign (Eq (Var x) (Var y) # ss) = (let ass = assign ss in ass(x := ass y))"
| "assign (Eq (Var x) (Succ n (Var y)) # ss) = (let ass = assign ss in ass(x := (Suc^^n) (ass y)))"
| "assign (Eq (Var x) Zero # ss) = (let ass = assign ss in ass(x := 0))"
| "assign (Eq (Var x) (Succ n Zero) # ss) = (let ass = assign ss in ass (x := (Suc^^n) 0))"
| "assign (Eq (Var x) (Succ n (Succ k t)) # ss) = assign (Eq (Var x) (Succ (n + k) t) # ss)"

lemma assign_succ:
  "assign (Eq (Var x) (succ n t) # ss) = assign (Eq (Var x) (Succ n t) # ss)"
  by (induction n t rule: succ.induct) auto

lemma I_term_fun_upd:
  assumes "x \<notin> set_suc_term t"
  shows "I_term (v(x := s)) t = I_term v t"
  using assms by (induction t) auto

lemma I_atom_fun_upd:
  assumes "x \<notin> set_suc_atom a"
  shows "I_atom (v(x := s)) a = I_atom v a"
  using assms by (cases a) (auto simp: I_term_fun_upd)

lemma I_atom_fun_updI:
  assumes "x \<notin> set_suc_atom a" "I_atom v a"
  shows "I_atom (v(x := s)) a"
  using assms I_atom_fun_upd by metis

lemma I_atom_assign_if_solve_Some:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  shows "\<forall>a \<in> set ss. I_atom (assign ss) a"
  using assms
proof(induction es arbitrary: ss rule: solve.induct)
  case (2 x y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Var y) # es" and ?x=x]
  with 2 show ?case
    by (auto simp: Let_def I_atom_fun_upd split: if_splits)
next
  case (3 x n t es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n t) # es" and ?x=x]
  with 3 show ?case
    by (cases t)
       (auto simp: Let_def I_term_succ I_atom_fun_upd assign_succ split: if_splits)
next
  case (4 n t x es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n t) # es" and ?x=x]
  with 4 show ?case
    by (cases t)
       (auto simp: Let_def I_term_succ I_atom_fun_upd assign_succ split: if_splits)
next
  case (7 x es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) Zero # es" and ?x=x]
  with 7 show ?case
    by (auto simp: Let_def I_atom_fun_upd split: if_splits)
next
  case (8 x es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) Zero # es" and ?x=x]
  with 8 show ?case
    by (auto simp: Let_def I_atom_fun_upd split: if_splits)
qed (auto split: if_splits)

lemma I_atom_iff_if_I_atom_solve_Some:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  shows "(\<forall>a \<in> set ss. I_atom v a) \<longleftrightarrow> (\<forall>a \<in> set es. I_atom v a)"
  using assms
  by (induction es arbitrary: ss rule: solve.induct)
     (auto simp: I_term_succ I_atom_subst_atom split: if_splits)

lemma assign_minimal_if_solve_Some:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "\<forall>a \<in> set ss. I_atom v a"
  shows "assign ss z \<le> v z"
  using assms
proof(induction es arbitrary: ss z rule: solve.induct)
  case (2 x y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Var y) # es" and ?x=x]
  with 2 show ?case
    by (auto simp: Let_def split: if_splits)
next
  case (3 x n t es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n t) # es" and ?x=x]
  with 3 show ?case
    by (cases t) (auto simp: Let_def I_term_succ assign_succ split: if_splits)
next
  case (4 n t x es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n t) # es" and ?x=x]
  with 4 show ?case
    by (cases t) (auto simp: Let_def I_term_succ assign_succ split: if_splits)
qed (auto split: if_splits)

fun elim_NEq_Zero_aux :: "('a::fresh) set \<Rightarrow> 'a suc_atom list \<Rightarrow> 'a suc_atom list" where
  "elim_NEq_Zero_aux _ [] = []"
| "elim_NEq_Zero_aux us (NEq (Var x) Zero # es) =
    (let fx = fresh us x in Eq (Var x) (Succ 1 (Var fx)) # elim_NEq_Zero_aux (insert fx us) es)"
| "elim_NEq_Zero_aux us (e # es) = e # elim_NEq_Zero_aux us es"

definition elim_NEq_Zero :: "('a::fresh) suc_atom list \<Rightarrow> 'a suc_atom list"
  where "elim_NEq_Zero es \<equiv> elim_NEq_Zero_aux (\<Union>(set_suc_atom ` set es)) es"

lemma is_normal_elim_NEq_Zero_aux:
  assumes "\<forall>a \<in> set es. is_Eq a \<longrightarrow> is_normal a"
  assumes "\<forall>a \<in> set es. is_NEq a \<longrightarrow> (\<exists>x. a = NEq (Var x) Zero)"
  shows "\<forall>a \<in> set (elim_NEq_Zero_aux us es). is_normal a"
  using assms
  by (induction es rule: elim_NEq_Zero_aux.induct) (auto simp: Let_def)

lemma is_normal_elim_NEq_Zero:
  assumes "\<forall>a \<in> set es. is_Eq a \<longrightarrow> is_normal a"
  assumes "\<forall>a \<in> set es. is_NEq a \<longrightarrow> (\<exists>x. a = NEq (Var x) Zero)"
  shows "\<forall>a \<in> set (elim_NEq_Zero es). is_normal a"
  using is_normal_elim_NEq_Zero_aux[OF assms] unfolding elim_NEq_Zero_def by blast

lemma I_atom_Var_NEq_Zero_if_I_atom_Var_Eq_Succ:
  "I_atom v (Eq (Var x) (Succ 1 (Var fx))) \<Longrightarrow> I_atom v (NEq (Var x) Zero)"
  by simp

lemma I_atom_if_I_atom_elim_NEq_Zero_aux:
  assumes "\<forall>a \<in> set (elim_NEq_Zero_aux us es). I_atom v a"
  shows "\<forall>a \<in> set es. I_atom v a"
  using assms I_atom_Var_NEq_Zero_if_I_atom_Var_Eq_Succ
  by (induction us es rule: elim_NEq_Zero_aux.induct) (auto simp: Let_def)

lemma I_atom_if_I_atom_elim_NEq_Zero:
  assumes "\<forall>a \<in> set (elim_NEq_Zero es). I_atom v a"
  shows "\<forall>a \<in> set es. I_atom v a"
  using assms I_atom_if_I_atom_elim_NEq_Zero_aux
  unfolding elim_NEq_Zero_def by blast

lemma I_term_if_eq_on_set_suc_term:
  assumes "\<forall>x \<in> set_suc_term t. v' x = v x"
  shows "I_term v' t = I_term v t"
  using assms
  by (induction t) auto

lemma I_atom_if_eq_on_set_suc_atom:
  assumes "\<forall>x \<in> set_suc_atom a. v' x = v x"
  shows "I_atom v' a = I_atom v a"
  using assms
  by (cases a) (simp; metis I_term_if_eq_on_set_suc_term UnI1 UnI2)+

lemma not_mem_set_suc_atom_elim_NEq_zero_aux:
  assumes "finite us" "\<Union>(set_suc_atom ` set es) \<subseteq> us"
  assumes "a \<in> set (elim_NEq_Zero_aux us es)"
  assumes "x \<in> us - \<Union>(set_suc_atom ` set es)"
  shows "x \<notin> set_suc_atom a"
  using assms
  by (induction us es arbitrary: x rule: elim_NEq_Zero_aux.induct)
     (auto simp: fresh_notIn Let_def)

lemma I_atom_elim_NEq_Zero_aux_if_I_atom:
  assumes "\<Union>(set_suc_atom ` set es) \<subseteq> us" "finite us"
  assumes "\<forall>a \<in> set es. I_atom v a"
  obtains v' where "\<forall>a \<in> set (elim_NEq_Zero_aux us es). I_atom v' a"
                   "\<forall>x \<in> us. v' x = v x"
  using assms
proof(induction us es arbitrary: thesis rule: elim_NEq_Zero_aux.induct)
  case (1 us)
  then show ?case by auto
next
  case (2 us x es thesis)
  then obtain v' where
    v': "\<forall>a \<in> set (elim_NEq_Zero_aux (insert (fresh us x) us) es). I_atom v' a"
        "\<forall>x \<in> insert (fresh us x) us. v' x = v x"
    by (auto simp: subset_insertI2)
  define v'' where "v'' \<equiv> v'(fresh us x := nat.pred (v' x))"

  from v' "2.prems"(3) have "fresh us x \<notin> us" "\<forall>x \<in> us. v'' x = v x"
    unfolding v''_def using fresh_notIn by (metis fun_upd_apply insertCI)+
  moreover from "2.prems"(2) have "x \<in> us"
    by auto
  moreover from "2.prems"(4) have "v x \<noteq> 0"
    by simp
  with v' \<open>x \<in> us\<close> have "v' x \<noteq> 0"
    by simp
  with \<open>x \<in> us\<close> have "v x = Suc (v'' (fresh us x))"
    unfolding v''_def by (auto simp: v'(2))
  moreover have "I_atom v'' a = I_atom v' a"
    if "a \<in> set (elim_NEq_Zero_aux (insert (fresh us x) us) es)" for a
  proof -
    have "fresh us x \<in> insert (fresh us x) us - \<Union>(set_suc_atom ` set es)"
      using "2.prems"(2) \<open>fresh us x \<notin> us\<close> by auto
    note not_mem_set_suc_atom_elim_NEq_zero_aux[OF _ _ _ this]
    with that have "fresh us x \<notin> set_suc_atom a"
      using "2.prems"(2,3) by auto
    then show ?thesis
      unfolding v''_def by (simp add: I_atom_fun_upd)
  qed
  ultimately show ?case
    by (intro "2"(2)[where ?v'=v'']) (auto simp: v'(1) Let_def)
qed (simp; metis I_term_if_eq_on_set_suc_term in_mono)+

lemma I_atom_elim_NEq_Zero_if_I_atom:
  assumes "\<forall>a \<in> set es. I_atom v a"
  obtains v' where "\<forall>a \<in> set (elim_NEq_Zero es). I_atom v' a"
                   "\<forall>x \<in> \<Union>(set_suc_atom ` set es). v' x = v x"
proof -
  have "finite (\<Union>(set_suc_atom ` set es))"
    by simp
  note I_atom_elim_NEq_Zero_aux_if_I_atom[OF _ this assms]
  with that show ?thesis
    unfolding elim_NEq_Zero_def by blast
qed

lemma not_I_atom_if_solve_elim_NEq_Zero_None:
  assumes "\<forall>a \<in> set es. is_Eq a \<longrightarrow> is_normal a"
  assumes "\<forall>a \<in> set es. is_NEq a \<longrightarrow> (\<exists>x. a = NEq (Var x) Zero)"
  assumes "solve (elim_NEq_Zero es) = None"
  shows "\<exists>a \<in> set es. \<not> I_atom v a"
proof -
  from is_normal_elim_NEq_Zero assms have "\<forall>a \<in> set (elim_NEq_Zero es). is_normal a"
    by blast
  note I_atom_solve_None[OF assms(3) this]
  then have "\<exists>a \<in> set (elim_NEq_Zero es). \<not> I_atom v a" for v
    by blast
  with I_atom_elim_NEq_Zero_if_I_atom show ?thesis
    by metis
qed

lemma
  assumes "\<forall>a \<in> set es. is_Eq a \<longrightarrow> is_normal a"
  assumes "\<forall>a \<in> set es. is_NEq a \<longrightarrow> (\<exists>x. a = NEq (Var x) Zero)"
  assumes "solve (elim_NEq_Zero es) = Some ss"
  shows I_atom_assign_if_solve_elim_NEq_Zero_Some:
      "\<forall>a \<in> set es. I_atom (assign ss) a"
    and I_atom_assign_minimal_if_solve_elim_NEq_Zero_Some:
      "\<lbrakk> \<forall>a \<in> set es. I_atom v a; z \<in> \<Union>(set_suc_atom ` set es) \<rbrakk>
       \<Longrightarrow> assign ss z \<le> v z"
proof -
  from is_normal_elim_NEq_Zero assms have normal: "\<forall>a \<in> set (elim_NEq_Zero es). is_normal a"
    by blast  
  note I_atom_assign_if_solve_Some[OF assms(3) normal]
  note this[unfolded I_atom_iff_if_I_atom_solve_Some[OF assms(3) normal]]
  from I_atom_if_I_atom_elim_NEq_Zero[OF this] show "\<forall>a \<in> set es. I_atom (assign ss) a" .

  note assign_minimal_if_solve_Some[OF assms(3) normal]
  then have "assign ss z \<le> v z" if "\<forall>a \<in> set (elim_NEq_Zero es). I_atom v a" for v
    using that I_atom_iff_if_I_atom_solve_Some[OF assms(3) normal] by blast
  then show "assign ss z \<le> v z"
    if "\<forall>a \<in> set es. I_atom v a" "z \<in> \<Union>(set_suc_atom ` set es)" for v
    using that I_atom_elim_NEq_Zero_if_I_atom by metis
qed

hide_const (open) Var Eq NEq subst_term subst_atom is_normal I_term I_atom is_Eq is_NEq assign solve

end