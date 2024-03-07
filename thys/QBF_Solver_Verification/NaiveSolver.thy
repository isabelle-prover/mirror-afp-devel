section \<open>Naive Solver Implementation and Verification\<close>

theory NaiveSolver
  imports Main
begin

subsection \<open>QBF Datatype, Semantics, and Satisfiability\<close>

subsubsection \<open>QBF Datatype\<close>

text \<open>QBFs based on~\cite{BuningBubeck2021}.\<close>

datatype QBF = Var nat
  | Neg QBF
  | Conj "QBF list"
  | Disj "QBF list"
  | Ex nat QBF
  | All nat QBF

subsubsection \<open>Formalisation of Semantics and Termination of Semantics\<close>

text \<open>Substitute True or False for a variable:\<close>
fun substitute_var :: "nat \<Rightarrow> bool \<Rightarrow> QBF \<Rightarrow> QBF" where
  "substitute_var z True (Var z') = (if z = z' then Conj [] else Var z')"
| "substitute_var z False (Var z') = (if z = z' then Disj [] else Var z')"
| "substitute_var z b (Neg qbf) = Neg (substitute_var z b qbf)"
| "substitute_var z b (Conj qbf_list) = Conj (map (substitute_var z b) qbf_list)"
| "substitute_var z b (Disj qbf_list) = Disj (map (substitute_var z b) qbf_list)"
| "substitute_var z b (Ex x qbf) = Ex x (if x = z then qbf else substitute_var z b qbf)"
| "substitute_var z b (All y qbf) = All y (if z = y then qbf else substitute_var z b qbf)"

text \<open>Measures the number of QBF constructors in argument, required to show termination of semantics.\<close>
  (* Could we use the size function instead? *)
fun qbf_measure :: "QBF \<Rightarrow> nat" where
  "qbf_measure (Var _) = 1"
| "qbf_measure (Neg qbf) = 1 + qbf_measure qbf"
| "qbf_measure (Conj qbf_list) = 1 + sum_list (map qbf_measure qbf_list)"
| "qbf_measure (Disj qbf_list) = 1 + sum_list (map qbf_measure qbf_list)"
| "qbf_measure (Ex _ qbf) = 1 + qbf_measure qbf"
| "qbf_measure (All _ qbf) = 1 + qbf_measure qbf"

text \<open>Substituting for variable does not change the QBF measure.\<close>
lemma qbf_measure_substitute: "qbf_measure (substitute_var z b qbf) = qbf_measure qbf"
proof (induction qbf)
  case (Var x)
  show "qbf_measure (substitute_var z b (Var x)) = qbf_measure (Var x)"
    by (cases b) auto
next
  case (Neg qbf)
  thus "qbf_measure (substitute_var z b (Neg qbf)) = qbf_measure (Neg qbf)" by simp
next
  case (Conj qbf_list)
  thus "qbf_measure (substitute_var z b (Conj qbf_list)) = qbf_measure (Conj qbf_list)"
  proof (induction qbf_list)
    case Nil
    thus "qbf_measure (substitute_var z b (Conj [])) = qbf_measure (Conj [])" by simp
  next
    case (Cons x xs)
    thus "qbf_measure (substitute_var z b (Conj (x # xs))) = qbf_measure (Conj (x # xs))" by simp
  qed
next
  case (Disj qbf_list)
  thus "qbf_measure (substitute_var z b (Disj qbf_list)) = qbf_measure (Disj qbf_list)"
  proof (induction qbf_list)
    case Nil
    thus "qbf_measure (substitute_var z b (Disj [])) = qbf_measure (Disj [])" by simp
  next
    case (Cons x xs)
    thus "qbf_measure (substitute_var z b (Disj (x # xs))) = qbf_measure (Disj (x # xs))" by simp
  qed
next
  case (Ex x qbf)
  thus "qbf_measure (substitute_var z b (QBF.Ex x qbf)) = qbf_measure (QBF.Ex x qbf)" by simp
next
  case (All y qbf)
  thus "qbf_measure (substitute_var z b (QBF.All y qbf)) = qbf_measure (QBF.All y qbf)" by simp
qed

text \<open>The measure of an element in a disjunction/conjunction is less than the measure of the
disjunction/conjunction.\<close>
lemma qbf_measure_lt_sum_list:
  assumes "qbf \<in> set qbf_list"
  shows "qbf_measure qbf < Suc (sum_list (map qbf_measure qbf_list))"
proof -
  obtain left right where "left @ qbf # right = qbf_list" by (metis assms split_list)
  hence "sum_list (map qbf_measure qbf_list)
        = sum_list (map qbf_measure left) + qbf_measure qbf + sum_list (map qbf_measure right)"
    by fastforce
  thus "qbf_measure qbf < Suc (sum_list (map qbf_measure qbf_list))" by simp
qed

text \<open>Semantics based on~\cite{BuningBubeck2021}.\<close>

function qbf_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> QBF \<Rightarrow> bool" where
  "qbf_semantics I (Var z) = I z"
| "qbf_semantics I (Neg qbf) = (\<not>(qbf_semantics I qbf))"
| "qbf_semantics I (Conj qbf_list) = list_all (qbf_semantics I) qbf_list"
| "qbf_semantics I (Disj qbf_list) = list_ex (qbf_semantics I) qbf_list"
| "qbf_semantics I (Ex x qbf) = ((qbf_semantics I (substitute_var x True qbf))
                                \<or> (qbf_semantics I (substitute_var x False qbf)))"
| "qbf_semantics I (All x qbf) = ((qbf_semantics I (substitute_var x True qbf))
                                 \<and> (qbf_semantics I (substitute_var x False qbf)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(I,qbf). qbf_measure qbf)")
  by (auto simp add: qbf_measure_substitute qbf_measure_lt_sum_list)

text \<open>Simple tests.\<close>

definition "test_qbf = (All 3 (Conj [Disj [Neg (Var 2), Var 3, Var 1], Disj [Neg (Var 1), Var 2]]))"

value "substitute_var 1 False test_qbf"
value "substitute_var 1 True test_qbf"
value "substitute_var 2 False test_qbf"
value "substitute_var 2 True test_qbf"
value "substitute_var 3 False test_qbf"
value "substitute_var 3 True test_qbf"

value "qbf_semantics (\<lambda>x. False) test_qbf"
value "qbf_semantics ((\<lambda>x. False)(2 := True)) test_qbf"
value "qbf_semantics (((\<lambda>x. False)(2 := True))(1 := True)) test_qbf"

subsubsection \<open>Formalisation of Satisfiability\<close>

definition satisfiable :: "QBF \<Rightarrow> bool" where
  "satisfiable qbf = (\<exists>I. qbf_semantics I qbf)"

definition logically_eq :: "QBF \<Rightarrow> QBF \<Rightarrow> bool" where
  "logically_eq qbf1 qbf2 = (\<forall>I. qbf_semantics I qbf1 = qbf_semantics I qbf2)"

subsection \<open>Existential Closure\<close>

subsubsection \<open>Formalisation of Free Variables\<close>

fun free_variables_aux :: "nat set \<Rightarrow> QBF \<Rightarrow> nat list" where
  "free_variables_aux bound (Var x) = (if x \<in> bound then [] else [x])"
| "free_variables_aux bound (Neg qbf) = free_variables_aux bound qbf"
| "free_variables_aux bound (Conj list) = concat (map (free_variables_aux bound) list)"
| "free_variables_aux bound (Disj list) = concat (map (free_variables_aux bound) list)"
| "free_variables_aux bound (Ex x qbf) = free_variables_aux (insert x bound) qbf"
| "free_variables_aux bound (All x qbf) = free_variables_aux (insert x bound) qbf"

fun free_variables :: "QBF \<Rightarrow> nat list" where
  "free_variables qbf = sort (remdups (free_variables_aux {} qbf))"

lemma bound_subtract_equiv:
  "set (free_variables_aux (bound \<union> new) qbf) = set (free_variables_aux bound qbf) - new"
  by (induction bound qbf rule: free_variables_aux.induct) auto

subsubsection \<open>Formalisation of Existential Closure\<close>

fun existential_closure_aux :: "QBF \<Rightarrow> nat list \<Rightarrow> QBF" where
  "existential_closure_aux qbf Nil = qbf"
| "existential_closure_aux qbf (Cons x xs) = Ex x (existential_closure_aux qbf xs)"

fun existential_closure :: "QBF \<Rightarrow> QBF" where
  "existential_closure qbf = existential_closure_aux qbf (free_variables qbf)"

subsubsection \<open>Preservation of Satisfiability under Existential Quantification\<close>

lemma swap_substitute_var_order:
  assumes "x1 \<noteq> x2 \<or> b1 = b2"
  shows "substitute_var x1 b1 (substitute_var x2 b2 qbf)
        = substitute_var x2 b2 (substitute_var x1 b1 qbf)"
proof (induction qbf)
  case (Var x)
  show ?case
  proof (cases b2)
    case True
    then show ?thesis using assms by (cases b1) auto
  next
    case False
    then show ?thesis using assms by (cases b1) auto
  qed
qed simp_all

lemma remove_outer_substitute_var:
  assumes "x1 = x2"
  shows "substitute_var x1 b1 (substitute_var x2 b2 qbf) = (substitute_var x2 b2 qbf)" using assms
proof (induction qbf)
  case (Var x)
  show ?case
  proof (cases b2)
    case True
    then show ?thesis using assms by (cases b1) auto
  next
    case False
    then show ?thesis using assms by (cases b1) auto
  qed
qed simp_all

lemma qbf_semantics_substitute_eq_assign:
  "qbf_semantics I (substitute_var x b qbf) \<longleftrightarrow> qbf_semantics (I(x := b)) qbf"
proof (induction "I(x := b)" qbf rule: qbf_semantics.induct)
  case (1 z)
  then show ?case by (cases b) auto
next
  case (3 qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (4 qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (5 x' qbf)
  thus ?case by (cases "x' = x")
      (auto simp add: swap_substitute_var_order remove_outer_substitute_var)
next
  case (6 x' qbf)
  thus ?case by (cases "x' = x")
      (auto simp add: swap_substitute_var_order remove_outer_substitute_var)
qed auto

lemma sat_iff_ex_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (Ex x qbf)"
proof (cases "satisfiable qbf")
  case True
  from this obtain I where I_def: "qbf_semantics I qbf" unfolding satisfiable_def by blast
  have "I(x := I x) = I(x := True) \<or> I(x := I x) = I(x := False)" by (cases "I x") auto
  hence "I = I(x := True) \<or> I = I(x := False)" by simp
  hence "qbf_semantics (I(x := True)) qbf \<or> qbf_semantics (I(x := False)) qbf"
    using I_def by fastforce
  moreover have "satisfiable (Ex x qbf)
                = (\<exists>I. qbf_semantics (I(x := True)) qbf
                  \<or> qbf_semantics (I(x := False)) qbf)"
    by (simp add: satisfiable_def qbf_semantics_substitute_eq_assign)
  ultimately have "satisfiable (QBF.Ex x qbf)" by blast
  thus ?thesis using True by simp
next
  case False
  thus ?thesis unfolding satisfiable_def using qbf_semantics_substitute_eq_assign by simp
qed

subsubsection \<open>Preservation of Satisfiability under Existential Closure\<close>

lemma sat_iff_ex_close_aux_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (existential_closure_aux qbf vars)"
  using sat_iff_ex_sat by (induction vars) auto

theorem sat_iff_ex_close_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (existential_closure qbf)"
  using sat_iff_ex_close_aux_sat by simp

subsubsection \<open>Non-Existence of Free Variables in Existential Closure\<close>

lemma ex_closure_aux_vars_not_free:
  "set (free_variables (existential_closure_aux qbf vars)) = set (free_variables qbf) - set vars"
proof (induction vars)
  case (Cons x xs)
  thus ?case using bound_subtract_equiv[of "{}" "{x}"] by auto
qed auto

theorem ex_closure_no_free: "set (free_variables (existential_closure qbf)) = {}"
  using ex_closure_aux_vars_not_free by simp

subsection \<open>Sequence Utility Function\<close>

text \<open>Like sequence in Haskell specialised for option types.\<close>
fun sequence_aux :: "'a option list \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
  "sequence_aux [] list = Some list"
| "sequence_aux (Some x # xs) list = sequence_aux xs (x # list)"
| "sequence_aux (None # xs) list = None"

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
  "sequence list = map_option rev (sequence_aux list [])"

lemma list_no_None_ex_list_map_Some:
  assumes "list_all (\<lambda>x. x \<noteq> None) list"
  shows "\<exists>xs. map Some xs = list" using assms
proof (induction list)
  case (Cons a list)
  from this obtain xs where "map Some xs = list" by fastforce
  moreover from Cons obtain x where "Some x = a" by fastforce
  ultimately have "map Some (x # xs) = a # list" by simp
  thus "\<exists>xs. map Some xs = a # list" by (rule exI)
qed auto

lemma sequence_aux_content: "sequence_aux (map Some xs) list = Some (rev xs @ list)"
  by (induction xs arbitrary: list) auto

lemma sequence_content: "sequence (map Some xs) = Some xs"
proof -
  have "sequence (map Some xs) = map_option rev (sequence_aux (map Some xs) [])" by simp
  moreover have "sequence_aux (map Some xs) [] = Some (rev xs @ [])"
    using sequence_aux_content by fastforce
  ultimately show "sequence (map Some xs) = Some xs" by simp
qed

subsection \<open>Naive Solver\<close>

subsubsection \<open>Expanding Quantifiers\<close>

fun list_max :: "nat list \<Rightarrow> nat" where
  "list_max Nil = 0"
| "list_max (Cons x xs) = max x (list_max xs)"

fun qbf_quantifier_depth :: "QBF \<Rightarrow> nat" where
  "qbf_quantifier_depth (Var x) = 0"
| "qbf_quantifier_depth (Neg qbf) = qbf_quantifier_depth qbf"
| "qbf_quantifier_depth (Conj list) = list_max (map qbf_quantifier_depth list)"
| "qbf_quantifier_depth (Disj list) = list_max (map qbf_quantifier_depth list)"
| "qbf_quantifier_depth (Ex x qbf) = 1 + (qbf_quantifier_depth qbf)"
| "qbf_quantifier_depth (All x qbf) = 1 + (qbf_quantifier_depth qbf)"

lemma qbf_quantifier_depth_substitute:
  "qbf_quantifier_depth (substitute_var z b qbf) = qbf_quantifier_depth qbf"
proof (induction qbf)
  case (Var x)
  show ?case by (cases b) auto
next
  case (Conj xs)
  thus ?case by (induction xs) auto
next
  case (Disj xs)
  thus ?case by (induction xs) auto
qed auto

lemma qbf_quantifier_depth_eq_max:
  assumes "\<not>qbf_quantifier_depth z < list_max (map qbf_quantifier_depth qbf_list)"
    and "z \<in> set qbf_list"
  shows "qbf_quantifier_depth z = list_max (map qbf_quantifier_depth qbf_list)" using assms
proof (induction qbf_list)
  case (Cons x xs)
  thus "qbf_quantifier_depth z = list_max (map qbf_quantifier_depth (x # xs))"
    by (cases "x = z") auto
qed auto

function expand_quantifiers :: "QBF \<Rightarrow> QBF" where
  "expand_quantifiers (Var x) = (Var x)"
| "expand_quantifiers (Neg qbf) = Neg (expand_quantifiers qbf)"
| "expand_quantifiers (Conj list) = Conj (map expand_quantifiers list)"
| "expand_quantifiers (Disj list) = Disj (map expand_quantifiers list)"
| "expand_quantifiers (Ex x qbf) = (Disj [substitute_var x True (expand_quantifiers qbf),
                                          substitute_var x False (expand_quantifiers qbf)])"
| "expand_quantifiers (All x qbf) = (Conj [substitute_var x True (expand_quantifiers qbf),
                                           substitute_var x False (expand_quantifiers qbf)])"
  by pat_completeness auto
termination
  apply (relation "measures [qbf_quantifier_depth, qbf_measure]")
  by (auto simp add: qbf_quantifier_depth_substitute qbf_quantifier_depth_eq_max)
    (auto simp add: qbf_measure_lt_sum_list)

text \<open>Property 1: no quantifiers after expansion.\<close>
lemma no_quants_after_expand_quants: "qbf_quantifier_depth (expand_quantifiers qbf) = 0"
proof (induction qbf)
  case (Conj x)
  thus ?case by (induction x) auto
next
  case (Disj x)
  thus ?case by (induction x) auto
next
  case (Ex x1a qbf)
  thus ?case using qbf_quantifier_depth_substitute Ex.IH by simp
next
  case (All x1a qbf)
  thus ?case using qbf_quantifier_depth_substitute All.IH by simp
qed auto

text \<open>Property 2: semantics invariant under expansion (logical equivalence).\<close>
lemma semantics_inv_under_expand:
  "qbf_semantics I qbf = qbf_semantics I (expand_quantifiers qbf)"
proof (induction qbf arbitrary: I)
  case (Conj x)
  thus ?case by (induction x) auto
next
  case (Disj x)
  thus ?case by (induction x) auto
next
  case (Ex x1a qbf)
  thus "qbf_semantics I (QBF.Ex x1a qbf) = qbf_semantics I (expand_quantifiers (QBF.Ex x1a qbf))"
    using qbf_semantics_substitute_eq_assign by fastforce
next
  case (All x1a qbf)
  thus "qbf_semantics I (QBF.All x1a qbf) = qbf_semantics I (expand_quantifiers (QBF.All x1a qbf))"
    using qbf_semantics_substitute_eq_assign by fastforce
qed auto

lemma sat_iff_expand_quants_sat: "satisfiable qbf \<longleftrightarrow> satisfiable (expand_quantifiers qbf)"
  unfolding satisfiable_def using semantics_inv_under_expand by simp

text \<open>Property 3: free variables invariant under expansion.\<close>
lemma set_free_vars_subst_all_eq:
  "set (free_variables (substitute_var x b qbf)) = set (free_variables (All x qbf))"
proof (induction x b qbf rule: substitute_var.induct)
  case (6 z b x qbf)
  then show ?case
  proof (cases "x = z")
    case False
    hence "set (free_variables (substitute_var z b (QBF.Ex x qbf)))
                   = set (free_variables (substitute_var z b qbf)) - {x}"
      using bound_subtract_equiv[where ?new = "{x}"] by simp
    also have "... = set (free_variables (QBF.All z qbf)) - {x}" using 6 False by simp
    also have "... = set (free_variables_aux {x, z} qbf)"
      using bound_subtract_equiv[where ?new = "{x}"] by simp
    also have "... = set (free_variables (QBF.All z (QBF.Ex x qbf)))" by simp
    finally show ?thesis .
  qed simp
next
  case (7 z b y qbf)
  thus ?case
  proof (cases "y = z")
    case False (* Similar to case "6, False" *)
    thus ?thesis using 7 bound_subtract_equiv[where ?new = "{y}"] by simp
  qed simp
qed auto

lemma set_free_vars_subst_ex_eq:
  "set (free_variables (substitute_var x b qbf)) = set (free_variables (Ex x qbf))"
proof (induction x b qbf rule: substitute_var.induct)
  case (6 z b x qbf)
  then show ?case
  proof (cases "x = z")
    case False (* Similar to proof in set_free_vars_subst_all_eq *) 
    thus ?thesis using 6 bound_subtract_equiv[where ?new = "{x}"] by simp
  qed auto
next
  case (7 z b y qbf)
  thus ?case
  proof (cases "y = z")
    case False (* Similar to proof in set_free_vars_subst_all_eq *)
    thus ?thesis using 7 bound_subtract_equiv[where ?new = "{y}"] by simp
  qed auto
qed auto

lemma free_vars_inv_under_expand_quants:
  "set (free_variables (expand_quantifiers qbf)) = set (free_variables qbf)"
proof (induction qbf)
  case (Ex x1a qbf)
  have "set (free_variables (expand_quantifiers (QBF.Ex x1a qbf)))
                 = set (free_variables_aux {x1a} (expand_quantifiers qbf))"
    using set_free_vars_subst_ex_eq by simp
  also have "... = set (free_variables (expand_quantifiers qbf)) - {x1a}"
    using bound_subtract_equiv[where ?new = "{x1a}"] by simp
  also have "... = set (free_variables qbf) - {x1a}" using Ex.IH by simp
  also have "... = set (free_variables_aux {x1a} qbf)"
    using bound_subtract_equiv[where ?new = "{x1a}"] by simp
  also have "... = set (free_variables (QBF.Ex x1a qbf))" by simp
  finally show ?case .
next
  case (All x1a qbf) (* Similar to above *)
  thus ?case using bound_subtract_equiv[where ?new = "{x1a}"] set_free_vars_subst_all_eq by simp
qed auto

subsubsection \<open>Expanding Formulas\<close>

fun expand_qbf :: "QBF \<Rightarrow> QBF" where
  "expand_qbf qbf = expand_quantifiers (existential_closure qbf)"

text \<open>The important properties from the existential closure and quantifier expansion are preserved.\<close>
lemma sat_iff_expand_qbf_sat: "satisfiable (expand_qbf qbf) \<longleftrightarrow> satisfiable qbf"
  using sat_iff_ex_close_sat sat_iff_expand_quants_sat by simp

lemma expand_qbf_no_free: "set (free_variables (expand_qbf qbf)) = {}"
proof -
  have "set (free_variables (expand_qbf qbf)) = set (free_variables (existential_closure qbf))"
    using free_vars_inv_under_expand_quants by simp
  thus ?thesis using ex_closure_no_free by metis
qed

lemma expand_qbf_no_quants: "qbf_quantifier_depth (expand_qbf qbf) = 0"
  using no_quants_after_expand_quants by simp

subsubsection \<open>Evaluating Expanded Formulas\<close>

fun eval_qbf :: "QBF \<Rightarrow> bool option" where
  "eval_qbf (Var x) = None" |
  "eval_qbf (Neg qbf) = map_option (\<lambda>x. \<not>x) (eval_qbf qbf)" |
  "eval_qbf (Conj list) = map_option (list_all id) (sequence (map eval_qbf list))" |
  "eval_qbf (Disj list) = map_option (list_ex id) (sequence (map eval_qbf list))" |
  "eval_qbf (Ex x qbf) = None" |
  "eval_qbf (All x qbf) = None"

lemma pred_map_ex: "list_ex Q (map f x) = list_ex (Q \<circ> f) x"
  by (induction x) auto

text \<open>The evaluation implements the semantics.\<close>
lemma eval_qbf_implements_semantics:
  assumes "set (free_variables qbf) = {}" and "qbf_quantifier_depth qbf = 0"
  shows "eval_qbf qbf = Some (qbf_semantics I qbf)" using assms
proof (induction qbf)
  case (Conj x)
  hence "\<forall>q \<in> set x. eval_qbf q = Some (qbf_semantics I q)" by (induction x) auto
  thus "eval_qbf (Conj x) = Some (qbf_semantics I (Conj x))"
  proof (induction x)
    case Nil
    show "eval_qbf (Conj []) = Some (qbf_semantics I (Conj []))" by simp
  next
    case (Cons y ys)
    have "map eval_qbf ys = map Some (map (qbf_semantics I) ys)" using Cons by simp
    moreover have "eval_qbf y = Some (qbf_semantics I y)" using Cons.prems by simp
    ultimately have "map eval_qbf (y # ys) = map Some (map (qbf_semantics I) (y # ys))" by simp
    hence "sequence (map eval_qbf (y # ys)) = Some (map (qbf_semantics I) (y # ys))"
      using sequence_content by metis
    hence "eval_qbf (Conj (y # ys))
          = Some (list_all id (map (qbf_semantics I) (y # ys)))"
      by simp
    hence "eval_qbf (Conj (y # ys)) = Some (list_all (qbf_semantics I) (y # ys))"
      by (simp add: fun.map_ident list.pred_map)
    thus "eval_qbf (Conj (y # ys)) = Some (qbf_semantics I (Conj (y # ys)))" by simp
  qed
next
  case (Disj x) (* Similar to previous case *)
  hence "\<forall>q \<in> set x. eval_qbf q = Some (qbf_semantics I q)" by (induction x) auto
  thus "eval_qbf (Disj x) = Some (qbf_semantics I (Disj x))"
  proof (induction x)
    case Nil
    show "eval_qbf (Disj []) = Some (qbf_semantics I (Disj []))" by simp
  next
    case (Cons y ys)
    have "map eval_qbf ys = map Some (map (qbf_semantics I) ys)" using Cons by simp
    moreover have "eval_qbf y = Some (qbf_semantics I y)" using Cons.prems by simp
    ultimately have "map eval_qbf (y # ys) = map Some (map (qbf_semantics I) (y # ys))" by simp
    hence "sequence (map eval_qbf (y # ys)) = Some (map (qbf_semantics I) (y # ys))"
      using sequence_content by metis
    hence "eval_qbf (Disj (y # ys))
          = Some (list_ex id (map (qbf_semantics I) (y # ys)))"
      by simp
    hence "eval_qbf (Disj (y # ys)) = Some (list_ex (qbf_semantics I) (y # ys))"
      by (simp add: fun.map_ident pred_map_ex)
    thus "eval_qbf (Disj (y # ys)) = Some (qbf_semantics I (Disj (y # ys)))" by simp
  qed
qed auto

subsubsection \<open>Naive Solver\<close>

fun naive_solver :: "QBF \<Rightarrow> bool" where
  "naive_solver qbf = the (eval_qbf (expand_qbf qbf))"

theorem naive_solver_correct: "naive_solver qbf \<longleftrightarrow> satisfiable qbf"
proof -
  have "\<forall>I. naive_solver qbf = the (Some (qbf_semantics I (expand_qbf qbf)))"
    using expand_qbf_no_free expand_qbf_no_quants eval_qbf_implements_semantics by simp
  hence "naive_solver qbf = satisfiable (expand_qbf qbf)" unfolding satisfiable_def by simp
  thus "naive_solver qbf = satisfiable qbf" using sat_iff_expand_qbf_sat by simp
qed

text \<open>Simple tests.\<close>

value test_qbf
value "existential_closure test_qbf"
value "expand_qbf test_qbf"
value "naive_solver test_qbf"

end