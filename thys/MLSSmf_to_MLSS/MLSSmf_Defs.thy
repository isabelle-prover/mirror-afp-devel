theory MLSSmf_Defs
  imports Main
begin

section \<open>Syntax of MLSSmf\<close>

datatype (vars_term: 'v, funs_term: 'f) MLSSmf_term =
  Empty nat (\<open>\<emptyset>\<^sub>m _\<close>) | is_Var: Var\<^sub>m 'v |
  Union "('v, 'f) MLSSmf_term" "('v, 'f) MLSSmf_term" (infix \<open>\<squnion>\<^sub>m\<close> 64) |
  Inter "('v, 'f) MLSSmf_term" "('v, 'f) MLSSmf_term" (infix \<open>\<sqinter>\<^sub>m\<close> 65) |
  Diff "('v, 'f) MLSSmf_term" "('v, 'f) MLSSmf_term" (infix \<open>-\<^sub>m\<close> 66) |
  Single\<^sub>m "('v, 'f) MLSSmf_term" |
  App 'f "('v, 'f) MLSSmf_term"

fun var_list_term :: "('v, 'f) MLSSmf_term \<Rightarrow> 'v list" where
  "var_list_term (\<emptyset>\<^sub>m _) = []"
| "var_list_term (Var\<^sub>m x) = [x]"
| "var_list_term (t\<^sub>1 \<squnion>\<^sub>m t\<^sub>2) = var_list_term t\<^sub>1 @ var_list_term t\<^sub>2"
| "var_list_term (t\<^sub>1 \<sqinter>\<^sub>m t\<^sub>2) = var_list_term t\<^sub>1 @ var_list_term t\<^sub>2"
| "var_list_term (t\<^sub>1 -\<^sub>m t\<^sub>2) = var_list_term t\<^sub>1 @ var_list_term t\<^sub>2"
| "var_list_term (Single\<^sub>m t) = var_list_term t"
| "var_list_term (App f t) = var_list_term t"
lemma set_var_list_term[simp]: "set (var_list_term t) = vars_term t"
  by (induction t) auto

fun fun_list_term :: "('v, 'f) MLSSmf_term \<Rightarrow> 'f list" where
  "fun_list_term (App f t) = f # fun_list_term t"
| "fun_list_term (t\<^sub>1 \<squnion>\<^sub>m t\<^sub>2) = fun_list_term t\<^sub>1 @ fun_list_term t\<^sub>2"
| "fun_list_term (t\<^sub>1 \<sqinter>\<^sub>m t\<^sub>2) = fun_list_term t\<^sub>1 @ fun_list_term t\<^sub>2"
| "fun_list_term (t\<^sub>1 -\<^sub>m t\<^sub>2) = fun_list_term t\<^sub>1 @ fun_list_term t\<^sub>2"
| "fun_list_term (Single\<^sub>m t) = fun_list_term t"
| "fun_list_term _ = []"
lemma set_fun_list_term[simp]: "set (fun_list_term t) = funs_term t"
  by (induction t) auto

datatype (vars_atom: 'v, funs_atom: 'f) MLSSmf_atom =
  Elem "('v, 'f) MLSSmf_term" "('v, 'f) MLSSmf_term" (infix \<open>\<in>\<^sub>m\<close> 61) |
  Equal "('v, 'f) MLSSmf_term" "('v, 'f) MLSSmf_term" (infix \<open>=\<^sub>m\<close> 60) |
  Inc 'f (\<open>inc'(_')\<close> [60] 60) |
  Dec 'f (\<open>dec'(_')\<close> [60] 60) |
  Additive 'f (\<open>add'(_')\<close> [60] 60) |
  Multiplicative 'f (\<open>mul'(_')\<close> [60] 60) |
  LeqF 'f 'f (infix \<open>\<preceq>\<^sub>m\<close> 66)

fun var_list_atom :: "('v, 'f) MLSSmf_atom \<Rightarrow> 'v list" where
  "var_list_atom (t\<^sub>1 \<in>\<^sub>m t\<^sub>2) = var_list_term t\<^sub>1 @ var_list_term t\<^sub>2"
| "var_list_atom (t\<^sub>1 =\<^sub>m t\<^sub>2) = var_list_term t\<^sub>1 @ var_list_term t\<^sub>2"
| "var_list_atom _ = []"
lemma set_var_list_atom[simp]: "set (var_list_atom a) = vars_atom a"
  by (cases a) auto

fun fun_list_atom :: "('v, 'f) MLSSmf_atom \<Rightarrow> 'f list" where
  "fun_list_atom (t\<^sub>1 \<in>\<^sub>m t\<^sub>2) = fun_list_term t\<^sub>1 @ fun_list_term t\<^sub>2"
| "fun_list_atom (t\<^sub>1 =\<^sub>m t\<^sub>2) = fun_list_term t\<^sub>1 @ fun_list_term t\<^sub>2"
| "fun_list_atom (inc(f)) = [f]"
| "fun_list_atom (dec(f)) = [f]"
| "fun_list_atom (add(f)) = [f]"
| "fun_list_atom (mul(f)) = [f]"
| "fun_list_atom (f \<preceq>\<^sub>m g) = [f, g]"
lemma set_fun_list_atom[simp]: "set (fun_list_atom a) = funs_atom a"
  by (cases a) auto

datatype (vars_literal: 'v, funs_literal: 'f) MLSSmf_literal =
  AT\<^sub>m "('v, 'f) MLSSmf_atom" |
  AF\<^sub>m "('v, 'f) MLSSmf_atom" (* negation of atom *)

fun var_list_literal :: "('v, 'f) MLSSmf_literal \<Rightarrow> 'v list" where
  "var_list_literal (AT\<^sub>m a) = var_list_atom a"
| "var_list_literal (AF\<^sub>m a) = var_list_atom a"
lemma set_var_list_literal[simp]: "set (var_list_literal lt) = vars_literal lt"
  by (cases lt) auto

fun fun_list_literal :: "('v, 'f) MLSSmf_literal \<Rightarrow> 'f list" where
  "fun_list_literal (AT\<^sub>m a) = fun_list_atom a"
| "fun_list_literal (AF\<^sub>m a) = fun_list_atom a"
lemma set_fun_list_literal[simp]: "set (fun_list_literal lt) = funs_literal lt"
  by (cases lt) auto

type_synonym ('v, 'f) MLSSmf_clause = "('v, 'f) MLSSmf_literal list" (* conjunction of literals *)

fun vars_in_clause :: "('v, 'f) MLSSmf_clause \<Rightarrow> 'v set" where
  "vars_in_clause cl = \<Union>(set (map vars_literal cl))"

fun funs_in_clause :: "('v, 'f) MLSSmf_clause \<Rightarrow> 'f set" where
  "funs_in_clause cl = \<Union>(set (map funs_literal cl))"

fun var_list_clause :: "('v, 'f) MLSSmf_clause \<Rightarrow> 'v list" where
  "var_list_clause ls = remdups (concat (map var_list_literal ls))"
lemma set_var_list_clause[simp]: "set (var_list_clause ls) = vars_in_clause ls"
  by (induction ls) auto

fun fun_list_clause :: "('v, 'f) MLSSmf_clause \<Rightarrow> 'f list" where
  "fun_list_clause ls = remdups (concat (map fun_list_literal ls))"
lemma set_fun_list_clause[simp]: "set (fun_list_clause ls) = funs_in_clause ls"
  by (induction ls) auto

section \<open>Definition of "normalized"\<close>

fun is_empty_or_var :: "('v, 'f) MLSSmf_term \<Rightarrow> bool" where
  "is_empty_or_var (\<emptyset>\<^sub>m _) = True" |
  "is_empty_or_var (Var\<^sub>m _) = True" |
  "is_empty_or_var _ = False"

inductive norm_literal :: "('v, 'f) MLSSmf_literal \<Rightarrow> bool" where
     inc: "norm_literal (AT\<^sub>m (inc(f)))" |
     dec: "norm_literal (AT\<^sub>m (dec(f)))" |
     add: "norm_literal (AT\<^sub>m (add(f)))" |
     mul: "norm_literal (AT\<^sub>m (mul(f)))" |
      le: "norm_literal (AT\<^sub>m (f \<preceq>\<^sub>m g))" |
      eq: "norm_literal (AT\<^sub>m (Var\<^sub>m x =\<^sub>m Var\<^sub>m y))" |
eq_empty: "norm_literal (AT\<^sub>m (Var\<^sub>m x =\<^sub>m \<emptyset>\<^sub>m n))" |
     neq: "norm_literal (AF\<^sub>m (Var\<^sub>m x =\<^sub>m Var\<^sub>m y))" |
   union: "norm_literal (AT\<^sub>m (Var\<^sub>m x =\<^sub>m Var\<^sub>m y \<squnion>\<^sub>m Var\<^sub>m z))" |
    diff: "norm_literal (AT\<^sub>m (Var\<^sub>m x =\<^sub>m Var\<^sub>m y -\<^sub>m Var\<^sub>m z))" |  
  single: "norm_literal (AT\<^sub>m (Var\<^sub>m x =\<^sub>m Single\<^sub>m (Var\<^sub>m y)))" |
     app: "norm_literal (AT\<^sub>m (Var\<^sub>m x =\<^sub>m App f (Var\<^sub>m y)))"

lemma norm_literal_neq:
  assumes "norm_literal lt"
      and "lt = AF\<^sub>m a"
    shows "\<exists>x y. a = Var\<^sub>m x =\<^sub>m Var\<^sub>m y"
  using assms by (cases lt rule: norm_literal.cases) auto

fun non_func_terms_in_norm_literal :: "('v, 'f) MLSSmf_literal \<Rightarrow> ('v, 'f) MLSSmf_term set" where
  "non_func_terms_in_norm_literal (AT\<^sub>m (x =\<^sub>m y \<squnion>\<^sub>m z)) = {x, y, z}" |
  "non_func_terms_in_norm_literal (AT\<^sub>m (x =\<^sub>m y -\<^sub>m z)) = {x, y, z}" |
  "non_func_terms_in_norm_literal (AT\<^sub>m (x =\<^sub>m Single\<^sub>m y)) = {x, y}" |
  "non_func_terms_in_norm_literal (AT\<^sub>m (x =\<^sub>m App f y)) = {x, y}" |
  "non_func_terms_in_norm_literal (AT\<^sub>m (x =\<^sub>m y)) =
   (if is_empty_or_var x then {x} else {}) \<union> (if is_empty_or_var y then {y} else {})" |
  "non_func_terms_in_norm_literal (AF\<^sub>m (x =\<^sub>m y)) =
   (if is_empty_or_var x then {x} else {}) \<union> (if is_empty_or_var y then {y} else {})" |
  "non_func_terms_in_norm_literal _ = {}"

lemma non_func_terms_in_norm_literal_is_empty_or_var:
  "norm_literal lt \<Longrightarrow> t \<in> non_func_terms_in_norm_literal lt \<Longrightarrow> is_empty_or_var t"
  by (cases lt rule: norm_literal.cases) auto

inductive norm_clause :: "('v, 'f) MLSSmf_clause \<Rightarrow> bool" where
  "norm_clause []" |
  "norm_clause ls \<Longrightarrow> norm_literal l \<Longrightarrow> norm_clause (l # ls)"

inductive_cases normE[elim]: "norm_clause (l # ls)"

lemma literal_in_norm_clause_is_norm[intro]:
  assumes "norm_clause \<C>" 
      and "l \<in> set \<C>"
    shows "norm_literal l"
  using assms
  by (induction \<C>) auto

section \<open>Functions for collecting variables and functions\<close>

consts vars\<^sub>m :: "'a \<Rightarrow> 'b set"
adhoc_overloading
  vars\<^sub>m \<rightleftharpoons> vars_term and
  vars\<^sub>m \<rightleftharpoons> vars_atom and
  vars\<^sub>m \<rightleftharpoons> vars_literal and
  vars\<^sub>m \<rightleftharpoons> vars_in_clause

consts funs\<^sub>m :: "'a \<Rightarrow> 'b set"
adhoc_overloading
  funs\<^sub>m \<rightleftharpoons> funs_term and
  funs\<^sub>m \<rightleftharpoons> funs_atom and
  funs\<^sub>m \<rightleftharpoons> funs_literal and
  funs\<^sub>m \<rightleftharpoons> funs_in_clause


lemma vars_in_lt_in_cl[intro]:
  "x \<in> vars\<^sub>m lt \<Longrightarrow> lt \<in> set \<C> \<Longrightarrow> x \<in> vars\<^sub>m \<C>"
  by (induction \<C>) auto

lemma vars_term_finite[intro]: "finite (vars\<^sub>m (t::('v, 'f) MLSSmf_term))"
  by (induction t) auto

lemma vars_atom_finite[intro]: "finite (vars\<^sub>m (a::('v, 'f) MLSSmf_atom))"
  by (induction a) auto

lemma vars_literal_finite[intro]: "finite (vars\<^sub>m (lt::('v, 'f) MLSSmf_literal))"
  by (cases lt) auto

lemma vars_finite[intro]: "finite (vars\<^sub>m (\<C>::('v, 'f) MLSSmf_clause))"
proof (induction \<C>)
  case Nil
  then show ?case by simp
next
  case (Cons a \<C>)
  moreover
  have "finite (vars\<^sub>m a)" by blast
  moreover
  have "vars\<^sub>m (a # \<C>) = (vars\<^sub>m a) \<union> \<Union>(set (map vars_literal \<C>))"
    by auto
  ultimately
  show ?case by force
qed

lemma funs_in_lt_in_cl[intro]:
  "x \<in> funs\<^sub>m lt \<Longrightarrow> lt \<in> set \<C> \<Longrightarrow> x \<in> funs\<^sub>m \<C>"
  by (induction \<C>) auto

lemma funs_term_finite[intro]: "finite (funs\<^sub>m (t::('v, 'f) MLSSmf_term))"
  by (induction t) auto

lemma funs_atom_finite[intro]: "finite (funs\<^sub>m (a::('v, 'f) MLSSmf_atom))"
  by (induction a) auto

lemma funs_literal_finite[intro]: "finite (funs\<^sub>m (lt::('v, 'f) MLSSmf_literal))"
  by (cases lt) auto

lemma funs_finite[intro]: "finite (funs\<^sub>m (\<C>::('v, 'f) MLSSmf_clause))"
proof (induction \<C>)
  case Nil
  then show ?case by simp
next
  case (Cons a \<C>)
  moreover
  have "finite (funs\<^sub>m a)" by blast
  moreover
  have "funs\<^sub>m (a # \<C>) = (funs\<^sub>m a) \<union> \<Union>(set (map funs_literal \<C>))"
    by auto
  ultimately
  show ?case by force
qed

end