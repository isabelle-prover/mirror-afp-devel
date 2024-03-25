section \<open>Search-Based Solver Implementation and Verification\<close>

theory SearchSolver
  imports PCNF
begin

subsection \<open>Formalisation of PCNF Assignment\<close>

fun lit_neg :: "literal \<Rightarrow> literal" where
  "lit_neg (P l) = N l"
| "lit_neg (N l) = P l"

fun lit_var :: "literal \<Rightarrow> nat" where
  "lit_var (P l) = l"
| "lit_var (N l) = l"

fun remove_lit_neg :: "literal \<Rightarrow> clause \<Rightarrow> clause" where
  "remove_lit_neg lit clause = filter (\<lambda>l. l \<noteq> lit_neg lit) clause"

fun remove_lit_clauses :: "literal \<Rightarrow> matrix \<Rightarrow> matrix" where
  "remove_lit_clauses lit matrix = filter (\<lambda>cl. \<not>(list_ex (\<lambda>l. l = lit) cl)) matrix"

fun matrix_assign :: "literal \<Rightarrow> matrix \<Rightarrow> matrix" where
  "matrix_assign lit matrix = remove_lit_clauses lit (map (remove_lit_neg lit) matrix)"

fun prefix_pop :: "prefix \<Rightarrow> prefix" where
  "prefix_pop Empty = Empty"
| "prefix_pop (UniversalFirst (x, Nil) Nil) = Empty"
| "prefix_pop (UniversalFirst (x, Nil) (Cons (y, ys) qs)) = ExistentialFirst (y, ys) qs"
| "prefix_pop (UniversalFirst (x, (Cons xx xs)) qs) = UniversalFirst (xx, xs) qs"
| "prefix_pop (ExistentialFirst (x, Nil) Nil) = Empty"
| "prefix_pop (ExistentialFirst (x, Nil) (Cons (y, ys) qs)) = UniversalFirst (y, ys) qs"
| "prefix_pop (ExistentialFirst (x, (Cons xx xs)) qs) = ExistentialFirst (xx, xs) qs"

fun add_universal_to_prefix :: "nat \<Rightarrow> prefix \<Rightarrow> prefix" where
  "add_universal_to_prefix x Empty = UniversalFirst (x, []) []"
| "add_universal_to_prefix x (UniversalFirst (y, ys) qs) = UniversalFirst (x, y # ys) qs"
| "add_universal_to_prefix x (ExistentialFirst (y, ys) qs) = UniversalFirst (x, []) ((y, ys) # qs)"

fun add_existential_to_prefix :: "nat \<Rightarrow> prefix \<Rightarrow> prefix" where
  "add_existential_to_prefix x Empty = ExistentialFirst (x, []) []"
| "add_existential_to_prefix x (ExistentialFirst (y, ys) qs) = ExistentialFirst (x, y # ys) qs"
| "add_existential_to_prefix x (UniversalFirst (y, ys) qs) = ExistentialFirst (x, []) ((y, ys) # qs)"

fun quant_sets_measure :: "quant_sets \<Rightarrow> nat" where
  "quant_sets_measure Nil = 0"
| "quant_sets_measure (Cons (x, xs) qs) = 1 + length xs + quant_sets_measure qs"

fun prefix_measure :: "prefix \<Rightarrow> nat" where
  "prefix_measure Empty = 0"
| "prefix_measure (UniversalFirst q qs) = quant_sets_measure (Cons q qs)"
| "prefix_measure (ExistentialFirst q qs) = quant_sets_measure (Cons q qs)"

lemma prefix_pop_decreases_measure:
  "prefix \<noteq> Empty \<Longrightarrow> prefix_measure (prefix_pop prefix) < prefix_measure prefix"
  by (induction rule: prefix_pop.induct) auto

function remove_var_prefix :: "nat \<Rightarrow> prefix \<Rightarrow> prefix" where
  "remove_var_prefix x Empty = Empty"
| "remove_var_prefix x (UniversalFirst (y, ys) qs) = (if x = y
    then remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs))
    else add_universal_to_prefix y (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs))))"
| "remove_var_prefix x (ExistentialFirst (y, ys) qs) = (if x = y
    then remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs))
    else add_existential_to_prefix y (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs))))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x, pre). prefix_measure pre)")
     (auto simp add: prefix_pop_decreases_measure simp del: prefix_measure.simps)

fun pcnf_assign :: "literal \<Rightarrow> pcnf \<Rightarrow> pcnf" where
  "pcnf_assign lit (prefix, matrix) =
     (remove_var_prefix (lit_var lit) prefix, matrix_assign lit matrix)"

text \<open>Simple tests.\<close>

value "the (convert_inv test_qbf)"
value "pcnf_assign (P 1) (the (convert_inv test_qbf))"
value "pcnf_assign (P 3) (the (convert_inv test_qbf))"

subsection \<open>Effect of PCNF Assignments on the Set of all Free Variables\<close>

subsubsection \<open>Variables, Prefix Variables, and Free Variables\<close>

fun variables_aux :: "QBF \<Rightarrow> nat list" where
  "variables_aux (Var x) = [x]"
| "variables_aux (Neg qbf) = variables_aux qbf"
| "variables_aux (Conj list) = concat (map variables_aux list)"
| "variables_aux (Disj list) = concat (map variables_aux list)"
| "variables_aux (Ex x qbf) = variables_aux qbf"
| "variables_aux (All x qbf) = variables_aux qbf"

fun variables :: "QBF \<Rightarrow> nat list" where
  "variables qbf = sort (remdups (variables_aux qbf))"

fun prefix_variables_aux :: "QBF \<Rightarrow> nat list" where
  "prefix_variables_aux (All y qbf) = Cons y (prefix_variables_aux qbf)"
| "prefix_variables_aux (Ex x qbf) = Cons x (prefix_variables_aux qbf)"
| "prefix_variables_aux _ = Nil"

fun prefix_variables :: "QBF \<Rightarrow> nat list" where
  "prefix_variables qbf = sort (remdups (prefix_variables_aux qbf))"

fun pcnf_variables :: "pcnf \<Rightarrow> nat list" where
  "pcnf_variables pcnf = variables (convert pcnf)"

fun pcnf_prefix_variables :: "pcnf \<Rightarrow> nat list" where
  "pcnf_prefix_variables pcnf = prefix_variables (convert pcnf)"

fun pcnf_free_variables :: "pcnf \<Rightarrow> nat list" where
  "pcnf_free_variables pcnf = free_variables (convert pcnf)"

(* We will show that the set of free variables is non-increasing after assignment using
the following proof skeleton: *)
lemma free_assgn_proof_skeleton:
  "free = var - pre \<Longrightarrow> free_assgn = var_assgn - pre_assgn
  \<Longrightarrow> var_assgn \<subseteq> var - lit
  \<Longrightarrow> pre_assgn = pre - lit
  \<Longrightarrow> free_assgn \<subseteq> free - lit"
  by auto

subsubsection \<open>Free Variables is Variables without Prefix Variables\<close>

(* free = vars - prefix *)
lemma lit_p_free_eq_vars:
  "literal_p qbf \<Longrightarrow> set (free_variables qbf) = set (variables qbf)"
  by (induction qbf rule: literal_p.induct) auto

lemma cl_p_free_eq_vars:
  assumes "clause_p qbf"
  shows "set (free_variables qbf) = set (variables qbf)"
proof -
  obtain qbf_list where list_def: "qbf = Disj qbf_list"
    using assms by (induction qbf rule: clause_p.induct) auto
  moreover from this have "list_all literal_p qbf_list" using assms by simp
  ultimately show ?thesis using lit_p_free_eq_vars by (induction qbf_list arbitrary: qbf) auto
qed

lemma cnf_p_free_eq_vars:
  assumes "cnf_p qbf"
  shows "set (free_variables qbf) = set (variables qbf)"
proof -
  obtain qbf_list where list_def: "qbf = Conj qbf_list"
    using assms by (induction qbf rule: cnf_p.induct) auto
  moreover from this have "list_all clause_p qbf_list" using assms by simp
  ultimately show ?thesis using cl_p_free_eq_vars by (induction qbf_list arbitrary: qbf) auto
qed

lemma pcnf_p_free_eq_vars_minus_prefix_aux:
  "pcnf_p qbf \<Longrightarrow> set (free_variables qbf) = set (variables qbf) - set (prefix_variables_aux qbf)"
proof (induction qbf rule: prefix_variables_aux.induct)
  case (1 y qbf)
  thus ?case using bound_subtract_equiv[of "{}" "{y}" qbf] by force
next
  case (2 x qbf)
  thus ?case using bound_subtract_equiv[of "{}" "{x}" qbf] by force
next
  case ("3_3" v)
  hence "cnf_p (Conj v)" by (induction "Conj v" rule: pcnf_p.induct) auto
  thus ?case using cnf_p_free_eq_vars by fastforce
qed auto

lemma pcnf_p_free_eq_vars_minus_prefix:
  "pcnf_p qbf \<Longrightarrow> set (free_variables qbf) = set (variables qbf) - set (prefix_variables qbf)"
  using pcnf_p_free_eq_vars_minus_prefix_aux by simp

lemma pcnf_free_eq_vars_minus_prefix:
  "set (pcnf_free_variables pcnf)
  = set (pcnf_variables pcnf) - set (pcnf_prefix_variables pcnf)"
  using pcnf_p_free_eq_vars_minus_prefix convert_pcnf_p by simp

subsubsection \<open>Set of Matrix Variables is Non-increasing under PCNF Assignments\<close>

(* We show: var_assgn \<subseteq> var - lit *)
lemma lit_not_in_matrix_assign_variables:
  "lit_var lit \<notin> set (variables (convert_matrix (matrix_assign lit matrix)))"
proof (induction matrix)
  case (Cons cl cls)
  then show ?case
  proof (induction cl)
    case (Cons l ls)
    then show ?case
    proof (induction l)
      case (P x)
      then show ?case
      proof (induction lit)
        case (P x')
        then show ?case by (cases "x = x'") auto
      next
        case (N x')
        then show ?case by (cases "x = x'") auto
      qed
    next
      case (N x)
      then show ?case
      proof (induction lit)
        case (P x')
        then show ?case by (cases "x = x'") auto
      next
        case (N x')
        then show ?case by (cases "x = x'") auto
      qed
    qed
  qed auto
qed auto

lemma matrix_assign_vars_subseteq_matrix_vars_minus_lit:
  "set (variables (convert_matrix (matrix_assign lit matrix)))
  \<subseteq> set (variables (convert_matrix matrix)) - {lit_var lit}"
  using lit_not_in_matrix_assign_variables by force

lemma pcnf_vars_eq_matrix_vars:
  "set (pcnf_variables (prefix, matrix))
  = set (variables (convert_matrix matrix))"
  by (induction "(prefix, matrix)" arbitrary: prefix rule: convert.induct) auto

lemma pcnf_assign_vars_subseteq_vars_minus_lit:
  "set (pcnf_variables (pcnf_assign x pcnf))
  \<subseteq> set (pcnf_variables pcnf) - {lit_var x}"
  using matrix_assign_vars_subseteq_matrix_vars_minus_lit pcnf_vars_eq_matrix_vars
  by (induction pcnf) simp

subsubsection \<open>PCNF Assignment Removes Variable from Prefix\<close>

(* We show: prefix_assgn = prefix - lit *)
lemma add_ex_adds_prefix_var:
  "set (pcnf_prefix_variables (add_existential_to_front x pcnf))
  = set (pcnf_prefix_variables pcnf) \<union> {x}"
  using convert_add_ex bound_subtract_equiv[of "{}" "{x}" "convert pcnf"] by auto

lemma add_ex_to_prefix_eq_add_to_front:
  "(add_existential_to_prefix x prefix, matrix) = add_existential_to_front x (prefix, matrix)"
  by (induction prefix) auto

lemma add_all_adds_prefix_var:
  "set (pcnf_prefix_variables (add_universal_to_front x pcnf))
  = set (pcnf_prefix_variables pcnf) \<union> {x}"
  using convert_add_all bound_subtract_equiv[of "{}" "{x}" "convert pcnf"] by auto

lemma add_all_to_prefix_eq_add_to_front:
  "(add_universal_to_prefix x prefix, matrix) = add_universal_to_front x (prefix, matrix)"
  by (induction prefix) auto

lemma prefix_assign_vars_eq_prefix_vars_minus_lit:
  "set (pcnf_prefix_variables (remove_var_prefix x prefix, matrix))
  = set (pcnf_prefix_variables (prefix, matrix)) - {x}"
proof (induction "(prefix, matrix)" arbitrary: prefix rule: convert.induct)
  case (4 x q qs)
  then show ?case
    using add_all_adds_prefix_var add_all_to_prefix_eq_add_to_front by (induction q) auto
next
  case (5 x q qs)
  then show ?case using add_ex_adds_prefix_var add_ex_to_prefix_eq_add_to_front by (induction q) auto
next
  case (6 x y ys qs)
  then show ?case using add_all_adds_prefix_var add_all_to_prefix_eq_add_to_front by auto
next
  case (7 x y ys qs)
  then show ?case using add_ex_adds_prefix_var add_ex_to_prefix_eq_add_to_front by auto
qed auto

lemma prefix_vars_matrix_inv:
  "set (pcnf_prefix_variables (prefix, matrix1))
  = set (pcnf_prefix_variables (prefix, matrix2))"
  by (induction "(prefix, matrix1)" arbitrary: prefix rule: convert.induct) auto

lemma pcnf_prefix_vars_eq_prefix_minus_lit:
  "set (pcnf_prefix_variables (pcnf_assign x pcnf))
  = set (pcnf_prefix_variables pcnf) - {lit_var x}"
  using prefix_assign_vars_eq_prefix_vars_minus_lit prefix_vars_matrix_inv
  by (induction pcnf) fastforce

subsubsection \<open>Set of Free Variables is Non-increasing under PCNF Assignments\<close>

(* This concludes the proof of the theorem: *)
theorem pcnf_assign_free_subseteq_free_minus_lit:
  "set (pcnf_free_variables (pcnf_assign x pcnf)) \<subseteq> set (pcnf_free_variables pcnf) - {lit_var x}"
  using free_assgn_proof_skeleton[OF
      pcnf_free_eq_vars_minus_prefix[of pcnf]
      pcnf_free_eq_vars_minus_prefix[of "pcnf_assign x pcnf"]
      pcnf_assign_vars_subseteq_vars_minus_lit[of x pcnf]
      pcnf_prefix_vars_eq_prefix_minus_lit[of x pcnf]] .

subsection \<open>PCNF Existential Closure\<close>

subsubsection \<open>Formalization of PCNF Existential Closure\<close>

fun pcnf_existential_closure :: "pcnf \<Rightarrow> pcnf" where
"pcnf_existential_closure pcnf = the (convert_inv (existential_closure (convert pcnf)))"

subsubsection \<open>PCNF Existential Closure Preserves Satisfiability\<close>

lemma ex_closure_aux_pcnf_p_inv:
  "pcnf_p qbf \<Longrightarrow> pcnf_p (existential_closure_aux qbf vars)"
  by (induction qbf vars rule: existential_closure_aux.induct) auto

lemma ex_closure_pcnf_p_inv:
  "pcnf_p qbf \<Longrightarrow> pcnf_p (existential_closure qbf)"
  using ex_closure_aux_pcnf_p_inv by simp

theorem pcnf_sat_iff_ex_close_sat:
  "satisfiable (convert pcnf) = satisfiable (convert (pcnf_existential_closure pcnf))"
  using convert_inv_inv convert_pcnf_p ex_closure_pcnf_p_inv sat_iff_ex_close_sat by auto

subsubsection \<open>No Free Variables in PCNF Existential Closure\<close>

theorem pcnf_ex_closure_no_free:
  "pcnf_free_variables (pcnf_existential_closure pcnf) = []"
  using convert_inv_inv convert_pcnf_p ex_closure_pcnf_p_inv ex_closure_no_free by auto

subsection \<open>Search Solver (Part 1: Preliminaries)\<close>

subsubsection \<open>Conditions for True and False PCNF Formulas\<close>

lemma single_clause_variables:
  "set (pcnf_variables (Empty, [cl])) = set (map lit_var cl)"
proof (induction cl)
  case (Cons l ls)
  then show ?case by (induction l) auto
qed auto

lemma empty_prefix_cons_matrix_variables:
  "set (pcnf_variables (Empty, Cons cl cls))
  = set (pcnf_variables (Empty, cls)) \<union> set (map lit_var cl)"
  using single_clause_variables by auto

lemma false_if_empty_clause_in_matrix:
  "[] \<in> set matrix \<Longrightarrow> pcnf_semantics I (prefix, matrix) = False"
  by (induction I "(prefix, matrix)" arbitrary: prefix rule: pcnf_semantics.induct)
     (induction matrix, auto)

lemma true_if_matrix_empty:
  "matrix = [] \<Longrightarrow> pcnf_semantics I (prefix, matrix) = True"
  by (induction I "(prefix, matrix)" arbitrary: prefix rule: pcnf_semantics.induct) auto

lemma matrix_shape_if_no_variables:
  "pcnf_variables (Empty, matrix) = [] \<Longrightarrow> (\<exists>n. matrix = replicate n [])"
proof (induction matrix)
  case (Cons cl cls)
  show ?case
  proof (cases "cl = Nil")
    case True
    from this obtain n where "cls = replicate n []" using Cons by fastforce
    hence "cl # cls = replicate (Suc n) []" using True by simp
    then show ?thesis by (rule exI) 
  next
    case False
    hence "set (pcnf_variables (Empty, cl # cls)) \<noteq> {}"
      using empty_prefix_cons_matrix_variables by simp
    hence False using Cons by blast
    then show ?thesis by simp
  qed
qed auto

lemma empty_clause_or_matrix_if_no_variables:
  "pcnf_variables (Empty, matrix) = [] \<Longrightarrow> [] \<in> set matrix \<or> matrix = []"
  using matrix_shape_if_no_variables by fastforce

subsubsection \<open>Satisfiability Equivalences for First Variable in Prefix\<close>

(*
We show:
\<exists>x\<Phi> \<approx>sat \<Phi>_x \<or> \<Phi>_\<not>x and \<forall>y\<Phi> \<approx>sat \<Phi>_y \<and> \<Phi>_\<not>y
if z is the first variable in the prefix.
*)

(* The clause semantics is invariant when removing false literals. *)
lemma clause_semantics_inv_remove_false:
  "clause_semantics (I(z := True)) cl = clause_semantics (I(z := True)) (remove_lit_neg (P z) cl)"
  by (induction cl) auto

lemma clause_semantics_inv_remove_true:
  "clause_semantics (I(z := False)) cl = clause_semantics (I(z := False)) (remove_lit_neg (N z) cl)"
  by (induction cl) auto

(* The matrix semantics is invariant when removing clauses containing true literals. *)
lemma matrix_semantics_inv_remove_true:
  "matrix_semantics (I(z := True)) (matrix_assign (P z) matrix)
  = matrix_semantics (I(z := True)) matrix"
proof (induction matrix)
  case (Cons cl cls)
  then show ?case
  proof (cases "P z \<in> set cl")
    case True
    hence 0: "clause_semantics (I(z := True)) cl" by (induction cl) auto
    have "matrix_semantics (I(z := True)) (matrix_assign (P z) (cl # cls))
         = matrix_semantics (I(z := True)) (matrix_assign (P z) cls)"
      using 0 clause_semantics_inv_remove_false by simp
    moreover have "matrix_semantics (I(z := True)) (cl # cls)
                  = matrix_semantics (I(z := True)) cls"
      using 0 by simp
    ultimately show ?thesis using Cons by blast
  next
    case False
    hence "matrix_assign (P z) (cl # cls) = remove_lit_neg (P z) cl # matrix_assign (P z) cls"
      by (induction cl) auto
    hence "matrix_semantics (I(z := True)) (matrix_assign (P z) (cl # cls))
          \<longleftrightarrow> clause_semantics (I(z := True)) (remove_lit_neg (P z) cl)
            \<and> matrix_semantics (I(z := True)) (matrix_assign (P z) cls)" by simp
    moreover have "matrix_semantics (I(z := True)) (cl # cls)
                  \<longleftrightarrow> clause_semantics (I(z := True)) cl
                    \<and> matrix_semantics (I(z := True)) cls" by simp
    ultimately show ?thesis using Cons clause_semantics_inv_remove_false by blast
  qed
qed auto

lemma matrix_semantics_inv_remove_true':
  assumes "y \<noteq> z"
  shows "matrix_semantics (I(z := True, y := b)) (matrix_assign (P z) matrix)
        = matrix_semantics (I(z := True, y := b)) matrix"
  using assms matrix_semantics_inv_remove_true fun_upd_twist by metis

lemma matrix_semantics_inv_remove_false:
  "matrix_semantics (I(z := False)) (matrix_assign (N z) matrix)
  = matrix_semantics (I(z := False)) matrix"
proof (induction matrix)
  case (Cons cl cls)
  then show ?case
  proof (cases "N z \<in> set cl")
    case True
    hence 0: "clause_semantics (I(z := False)) cl" by (induction cl) auto
    have "matrix_semantics (I(z := False)) (matrix_assign (N z) (cl # cls))
         = matrix_semantics (I(z := False)) (matrix_assign (N z) cls)"
      using 0 clause_semantics_inv_remove_true by simp
    moreover have "matrix_semantics (I(z := False)) (cl # cls)
                  = matrix_semantics (I(z := False)) cls"
      using 0 by simp
    ultimately show ?thesis using Cons by blast
  next
    case False
    hence "matrix_assign (N z) (cl # cls) = remove_lit_neg (N z) cl # matrix_assign (N z) cls"
      by (induction cl) auto
    hence "matrix_semantics (I(z := False)) (matrix_assign (N z) (cl # cls))
          \<longleftrightarrow> clause_semantics (I(z := False)) (remove_lit_neg (N z) cl)
            \<and> matrix_semantics (I(z := False)) (matrix_assign (N z) cls)" by simp
    moreover have "matrix_semantics (I(z := False)) (cl # cls)
                  \<longleftrightarrow> clause_semantics (I(z := False)) cl
                    \<and> matrix_semantics (I(z := False)) cls" by simp
    ultimately show ?thesis using Cons clause_semantics_inv_remove_true by blast
  qed
qed auto

lemma matrix_semantics_inv_remove_false':
  assumes "y \<noteq> z"
  shows "matrix_semantics (I(z := False, y := b)) (matrix_assign (N z) matrix)
        = matrix_semantics (I(z := False, y := b)) matrix"
  using assms matrix_semantics_inv_remove_false fun_upd_twist by metis

(* The matrix semantics is true for some I iff it is true for some matrix assignment. *)
lemma matrix_semantics_disj_iff_true_assgn:
  "(\<exists>b. matrix_semantics (I(z := b)) matrix)
  \<longleftrightarrow> matrix_semantics (I(z := True)) (matrix_assign (P z) matrix)
    \<or> matrix_semantics (I(z := False)) (matrix_assign (N z) matrix)"
  using matrix_semantics_inv_remove_true matrix_semantics_inv_remove_false by (metis (full_types))

(* The matrix semantics is true for all I iff it is true for both matrix assignments. *)
lemma matrix_semantics_conj_iff_true_assgn:
  "(\<forall>b. matrix_semantics (I(z := b)) matrix)
  \<longleftrightarrow> matrix_semantics (I(z := True)) (matrix_assign (P z) matrix)
    \<and> matrix_semantics (I(z := False)) (matrix_assign (N z) matrix)"
  using matrix_semantics_inv_remove_true matrix_semantics_inv_remove_false by (metis (full_types))

(* A pcnf assignment for a variable not in the prefix is equal to a matrix assignment. *)
lemma pcnf_assign_free_eq_matrix_assgn':
  assumes "lit_var lit \<notin> set (prefix_variables_aux (convert (prefix, matrix)))"
  shows "pcnf_assign lit (prefix, matrix) = (prefix, matrix_assign lit matrix)"
  using assms
  by (induction "(prefix, matrix)" arbitrary: prefix rule: convert.induct) auto

lemma pcnf_assign_free_eq_matrix_assgn:
  assumes "lit_var lit \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_assign lit (prefix, matrix) = (prefix, matrix_assign lit matrix)"
  using assms pcnf_assign_free_eq_matrix_assgn' by simp

(* Lemmas for variables not in prefix. *)
lemma neq_first_if_notin_all_prefix:
  "z \<notin> set (pcnf_prefix_variables (UniversalFirst (y, ys) qs, matrix)) \<Longrightarrow> z \<noteq> y"
  by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct) auto

lemma neq_first_if_notin_ex_prefix:
  "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (x, xs) qs, matrix)) \<Longrightarrow> z \<noteq> x"
  by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct) auto

lemma notin_pop_prefix_if_notin_prefix:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "z \<notin> set (pcnf_prefix_variables (prefix_pop prefix, matrix))"
  using assms
proof (induction prefix)
  case (UniversalFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair y ys)
    then show ?case
      by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct) auto
  qed
next
  case (ExistentialFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair x xs)
    then show ?case
      by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct) auto
  qed
qed auto

(* The pcnf semantics is invariant when assigning true literals. *)
lemma pcnf_semantics_inv_matrix_assign_true:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := True)) (prefix, matrix_assign (P z) matrix)
        = pcnf_semantics (I(z := True)) (prefix, matrix)"
  using assms
proof (induction I "(prefix, matrix)" arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I matrix)
  then show ?case using matrix_semantics_inv_remove_true by simp
next
  case (2 I y matrix)
  then show ?case using matrix_semantics_inv_remove_true' by simp
next
  case (3 I x matrix)
  then show ?case using matrix_semantics_inv_remove_true' by simp
next
  case (4 I y q qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := True)) (ExistentialFirst q qs, matrix) =
    pcnf_semantics (I(z := True)) (ExistentialFirst q qs, matrix_assign (P z) matrix)"
    for I using 4 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (5 I x q qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := True)) (UniversalFirst q qs, matrix) =
    pcnf_semantics (I(z := True)) (UniversalFirst q qs, matrix_assign (P z) matrix)"
    for I using 5 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := True)) (UniversalFirst (yy, ys) qs, matrix) =
    pcnf_semantics (I(z := True)) (UniversalFirst (yy, ys) qs, matrix_assign (P z) matrix)"
    for I using 6 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := True)) (ExistentialFirst (xx, xs) qs, matrix) =
    pcnf_semantics (I(z := True)) (ExistentialFirst (xx, xs) qs, matrix_assign (P z) matrix)"
    for I using 7 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
qed

lemma pcnf_semantics_inv_matrix_assign_false:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := False)) (prefix, matrix_assign (N z) matrix)
        = pcnf_semantics (I(z := False)) (prefix, matrix)"
  using assms
proof (induction I "(prefix, matrix)" arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I matrix)
  then show ?case using matrix_semantics_inv_remove_false by simp
next
  case (2 I y matrix)
  then show ?case using matrix_semantics_inv_remove_false' by simp
next
  case (3 I x matrix)
  then show ?case using matrix_semantics_inv_remove_false' by simp
next
  case (4 I y q qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := False)) (ExistentialFirst q qs, matrix) =
    pcnf_semantics (I(z := False)) (ExistentialFirst q qs, matrix_assign (N z) matrix)"
    for I using 4 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (5 I x q qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  hence "pcnf_semantics (I(z := False)) (UniversalFirst q qs, matrix) =
    pcnf_semantics (I(z := False)) (UniversalFirst q qs, matrix_assign (N z) matrix)"
    for I using 5 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs matrix)
  hence neq: "z \<noteq> y" using neq_first_if_notin_all_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := False)) (UniversalFirst (yy, ys) qs, matrix) =
    pcnf_semantics (I(z := False)) (UniversalFirst (yy, ys) qs, matrix_assign (N z) matrix)"
    for I using 6 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs matrix)
  hence neq: "z \<noteq> x" using neq_first_if_notin_ex_prefix by blast
  have "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  hence "pcnf_semantics (I(z := False)) (ExistentialFirst (xx, xs) qs, matrix) =
    pcnf_semantics (I(z := False)) (ExistentialFirst (xx, xs) qs, matrix_assign (N z) matrix)"
    for I using 7 by blast
  then show ?case using neq by (simp add: fun_upd_twist)
qed

(* Disjunctions of the pcnf semantics are invariant when assigning true literals. *)
lemma pcnf_semantics_disj_iff_matrix_assign_disj:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := True)) (prefix, matrix)
        \<or> pcnf_semantics (I(z := False)) (prefix, matrix)
        \<longleftrightarrow>
        pcnf_semantics (I(z := True)) (prefix, matrix_assign (P z) matrix)
        \<or> pcnf_semantics (I(z := False)) (prefix, matrix_assign (N z) matrix)"
  using assms
proof (induction I "(prefix, matrix_assign (P z) matrix)"
    arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I)
  then show ?case using ex_bool_eq matrix_semantics_disj_iff_true_assgn by simp
next
  case (2 I y)
  hence neq: "y \<noteq> z" by simp
  show ?case using ex_bool_eq matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (3 I x)
  hence neq: "x \<noteq> z" by simp
  show ?case using ex_bool_eq matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (4 I y q qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (5 I x q qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
qed

(* Conjunctions of the pcnf semantics are invariant when assigning true literals. *)
lemma pcnf_semantics_conj_iff_matrix_assign_conj:
  assumes "z \<notin> set (pcnf_prefix_variables (prefix, matrix))"
  shows "pcnf_semantics (I(z := True)) (prefix, matrix)
        \<and> pcnf_semantics (I(z := False)) (prefix, matrix)
        \<longleftrightarrow>
        pcnf_semantics (I(z := True)) (prefix, matrix_assign (P z) matrix)
        \<and> pcnf_semantics (I(z := False)) (prefix, matrix_assign (N z) matrix)"
  using assms
proof (induction I "(prefix, matrix_assign (P z) matrix)"
    arbitrary: I prefix matrix rule: pcnf_semantics.induct)
  case (1 I)
  then show ?case using all_bool_eq matrix_semantics_conj_iff_true_assgn by simp
next
  case (2 I y)
  hence neq: "y \<noteq> z" by simp
  show ?case using matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (3 I x)
  hence neq: "x \<noteq> z" by simp
  show ?case using matrix_semantics_inv_remove_true'
      matrix_semantics_inv_remove_false' neq by simp
next
  case (4 I y q qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have "prefix_pop (UniversalFirst (y, []) (q # qs)) = ExistentialFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst q qs, matrix))"
    using 4(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (5 I x q qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have "prefix_pop (ExistentialFirst (x, []) (q # qs)) = UniversalFirst q qs"
    by (induction q) auto
  hence nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst q qs, matrix))"
    using 5(3) notin_pop_prefix_if_notin_prefix by metis
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (6 I y yy ys qs)
  hence neq: "y \<noteq> z" using neq_first_if_notin_all_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (UniversalFirst (yy, ys) qs, matrix))"
    using 6(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
next
  case (7 I x xx xs qs)
  hence neq: "x \<noteq> z" using neq_first_if_notin_ex_prefix by blast
  have nin: "z \<notin> set (pcnf_prefix_variables (ExistentialFirst (xx, xs) qs, matrix))"
    using 7(3) notin_pop_prefix_if_notin_prefix by fastforce
  show ?case using nin neq pcnf_semantics_inv_matrix_assign_true
      pcnf_semantics_inv_matrix_assign_false by (simp add: fun_upd_twist)
qed

(* Semantics is equal under two interpretations if they agree on the free variables. *)
lemma semantics_eq_if_free_vars_eq:
  assumes "\<forall>x \<in> set (free_variables qbf). I(x) = J(x)"
  shows "qbf_semantics I qbf = qbf_semantics J qbf" using assms
proof (induction I qbf rule: qbf_semantics.induct)
  case (3 I qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (4 I qbf_list)
  then show ?case by (induction qbf_list) auto
next
  case (5 I x qbf)
  hence "qbf_semantics I (substitute_var x b qbf)
        = qbf_semantics J (substitute_var x b qbf)"
    for b using set_free_vars_subst_ex_eq by (metis (full_types))
  then show ?case by simp
next
  case (6 I x qbf)
  hence "qbf_semantics I (substitute_var x b qbf)
        = qbf_semantics J (substitute_var x b qbf)"
    for b using set_free_vars_subst_all_eq by (metis (full_types))
  then show ?case by simp
qed auto

lemma pcnf_semantics_eq_if_free_vars_eq:
  assumes "\<forall>x \<in> set (pcnf_free_variables pcnf). I(x) = J(x)"
  shows "pcnf_semantics I pcnf = pcnf_semantics J pcnf"
  using assms semantics_eq_if_free_vars_eq qbf_semantics_eq_pcnf_semantics by simp

(* Interpretation value of assigned variables does not matter *)
lemma x_notin_assign_P_x:
  "x \<notin> set (pcnf_variables (pcnf_assign (P x) pcnf))"
  using pcnf_assign_vars_subseteq_vars_minus_lit by fastforce

lemma x_notin_assign_N_x:
  "x \<notin> set (pcnf_variables (pcnf_assign (N x) pcnf))"
  using pcnf_assign_vars_subseteq_vars_minus_lit by fastforce

lemma interp_value_ignored_for_pcnf_P_assign:
  "pcnf_semantics (I(x := b)) (pcnf_assign (P x) pcnf)
  = pcnf_semantics I (pcnf_assign (P x) pcnf)"
  using pcnf_semantics_eq_if_free_vars_eq x_notin_assign_P_x
    pcnf_free_eq_vars_minus_prefix by simp

lemma interp_value_ignored_for_pcnf_N_assign:
  "pcnf_semantics (I(x := b)) (pcnf_assign (N x) pcnf)
  = pcnf_semantics I (pcnf_assign (N x) pcnf)"
  using pcnf_semantics_eq_if_free_vars_eq x_notin_assign_N_x
    pcnf_free_eq_vars_minus_prefix by simp

(* A pcnf starting with an existential is satisfiable iff one of the possible assignments is. *)
lemma sat_ex_first_iff_one_assign_sat:
  assumes "x \<notin> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  shows "satisfiable (convert (ExistentialFirst (x, xs) qs, matrix))
  \<longleftrightarrow> satisfiable (convert (pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)))
    \<or> satisfiable (convert (pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix)))"
proof -
  let ?pre = "ExistentialFirst (x, xs) qs"
  have "satisfiable (convert (?pre, matrix))
       = (\<exists>I. pcnf_semantics I (?pre, matrix))"
    using satisfiable_def qbf_semantics_eq_pcnf_semantics by simp
  also have "... =
       (\<exists>I. pcnf_semantics (I(x := True)) (prefix_pop ?pre, matrix) \<or>
            pcnf_semantics (I(x := False)) (prefix_pop ?pre, matrix))"
    by (induction "?pre" rule: prefix_pop.induct) auto
  also have "... =
    (\<exists>I. pcnf_semantics (I(x := True)) (prefix_pop ?pre, matrix_assign (P x) matrix) \<or>
         pcnf_semantics (I(x := False)) (prefix_pop ?pre, matrix_assign (N x) matrix))"
    using pcnf_semantics_disj_iff_matrix_assign_disj assms by blast
  also have "... \<longleftrightarrow>
    (\<exists>I. pcnf_semantics (I(x := True)) (pcnf_assign (P x) (?pre, matrix))) \<or>
    (\<exists>I. pcnf_semantics (I(x := False)) (pcnf_assign (N x) (?pre, matrix)))"
    using pcnf_assign_free_eq_matrix_assgn[of "P x"] pcnf_assign_free_eq_matrix_assgn[of "N x"]
      assms by auto
  also have "... \<longleftrightarrow>
    (\<exists>I. pcnf_semantics I (pcnf_assign (P x) (?pre, matrix))) \<or>
    (\<exists>I. pcnf_semantics I (pcnf_assign (N x) (?pre, matrix)))"
    using interp_value_ignored_for_pcnf_N_assign interp_value_ignored_for_pcnf_P_assign
    by blast
  also have "... \<longleftrightarrow>
    satisfiable (convert (pcnf_assign (P x) (?pre, matrix))) \<or>
    satisfiable (convert (pcnf_assign (N x) (?pre, matrix)))"
    using satisfiable_def qbf_semantics_eq_pcnf_semantics by simp
  finally show ?thesis .
qed

(* A pcnf starting with an existential is satisfiable
  iff the disjunction of both possible assignments is.
  That is: \<exists>x\<Phi> \<approx>sat \<Phi>_x \<or> \<Phi>_\<not>x. *)
theorem sat_ex_first_iff_assign_disj_sat:
  assumes "x \<notin> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  shows "satisfiable (convert (ExistentialFirst (x, xs) qs, matrix))
  \<longleftrightarrow> satisfiable (Disj
    [convert (pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)),
     convert (pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix))])"
  using assms sat_ex_first_iff_one_assign_sat satisfiable_def
    qbf_semantics_eq_pcnf_semantics by auto

(* A pcnf starting with an universal is satisfiable
  iff the conjunction of both possible assignments is. 
  That is: \<forall>y\<Phi> \<approx>sat \<Phi>_y \<and> \<Phi>_\<not>y. *)
theorem sat_all_first_iff_assign_conj_sat:
  assumes "y \<notin> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  shows "satisfiable (convert (UniversalFirst (y, ys) qs, matrix))
  \<longleftrightarrow> satisfiable (Conj
    [convert (pcnf_assign (P y) (UniversalFirst (y, ys) qs, matrix)),
     convert (pcnf_assign (N y) (UniversalFirst (y, ys) qs, matrix))])"
proof -
  let ?pre = "UniversalFirst (y, ys) qs"
  have "satisfiable (convert (?pre, matrix))
       = (\<exists>I. pcnf_semantics I (?pre, matrix))"
    using satisfiable_def qbf_semantics_eq_pcnf_semantics by simp
  also have "... =
    (\<exists>I. pcnf_semantics (I(y := True)) (prefix_pop ?pre, matrix) \<and>
         pcnf_semantics (I(y := False)) (prefix_pop ?pre, matrix))"
    by (induction "?pre" rule: prefix_pop.induct) auto
  also have "... =
    (\<exists>I. pcnf_semantics (I(y := True)) (prefix_pop ?pre, matrix_assign (P y) matrix) \<and>
         pcnf_semantics (I(y := False)) (prefix_pop ?pre, matrix_assign (N y) matrix))"
    using pcnf_semantics_conj_iff_matrix_assign_conj assms by blast
  also have "... =
    (\<exists>I. pcnf_semantics (I(y := True)) (pcnf_assign (P y) (?pre, matrix)) \<and>
         pcnf_semantics (I(y := False)) (pcnf_assign (N y) (?pre, matrix)))"
    using pcnf_assign_free_eq_matrix_assgn[of "P y"] pcnf_assign_free_eq_matrix_assgn[of "N y"]
      assms by simp
  also have "... =
    (\<exists>I. pcnf_semantics I (pcnf_assign (P y) (?pre, matrix)) \<and>
         pcnf_semantics I (pcnf_assign (N y) (?pre, matrix)))"
    using interp_value_ignored_for_pcnf_N_assign interp_value_ignored_for_pcnf_P_assign by blast
  also have "... =
    (\<exists>I. qbf_semantics I (convert (pcnf_assign (P y) (?pre, matrix))) \<and>
         qbf_semantics I (convert (pcnf_assign (N y) (?pre, matrix))))"
      using qbf_semantics_eq_pcnf_semantics by blast
  also have "... =
    satisfiable (Conj
      [convert (pcnf_assign (P y) (?pre, matrix)),
       convert (pcnf_assign (N y) (?pre, matrix))])"
    unfolding satisfiable_def by simp
  finally show ?thesis .
qed

subsection \<open>Cleansed PCNF Formulas\<close>

subsubsection \<open>Predicate for Cleansed Formulas\<close>

fun cleansed_p :: "pcnf \<Rightarrow> bool" where
  "cleansed_p pcnf = distinct (prefix_variables_aux (convert pcnf))"

lemma prefix_pop_cleansed_if_cleansed:
  "cleansed_p (prefix, matrix) \<Longrightarrow> cleansed_p (prefix_pop prefix, matrix)"
  by (induction prefix rule: prefix_pop.induct) auto

lemma prefix_variables_aux_matrix_inv:
  "prefix_variables_aux (convert (prefix, matrix1))
  = prefix_variables_aux (convert (prefix, matrix2))"
  by (induction "(prefix, matrix1)" arbitrary: prefix rule: convert.induct) auto

lemma eq_prefix_cleansed_p_add_all_inv:
  "cleansed_p (add_universal_to_front y (prefix, matrix1))
  = cleansed_p (add_universal_to_front y (prefix, matrix2))"
proof (induction y "(prefix, matrix1)" arbitrary: prefix rule: add_universal_to_front.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys qs)
  have "prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
next
  case (3 x y ys qs)
    have "prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
qed

lemma eq_prefix_cleansed_p_add_ex_inv:
  "cleansed_p (add_existential_to_front x (prefix, matrix1))
  = cleansed_p (add_existential_to_front x (prefix, matrix2))"
proof (induction x "(prefix, matrix1)" arbitrary: prefix rule: add_universal_to_front.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys qs)
  have "prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (UniversalFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
next
  case (3 x y ys qs)
    have "prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix1))
       = prefix_variables_aux (convert (ExistentialFirst (y, ys) qs, matrix2))"
    using prefix_variables_aux_matrix_inv by simp
  then show ?case by simp
qed

lemma cleansed_p_matrix_inv:
  "cleansed_p (prefix, matrix1) = cleansed_p (prefix, matrix2)"
proof (induction "(prefix, matrix1)" arbitrary: prefix rule: convert.induct)
  case (4 x q qs)
  have "(UniversalFirst (x, []) (q # qs), matrix)
       = add_universal_to_front x (ExistentialFirst q qs, matrix)"
    for matrix by (induction q) auto
  then show ?case using eq_prefix_cleansed_p_add_all_inv by simp 
next
  case (5 x q qs)
    have "(ExistentialFirst (x, []) (q # qs), matrix)
       = add_existential_to_front x (UniversalFirst q qs, matrix)"
    for matrix by (induction q) auto
  then show ?case using eq_prefix_cleansed_p_add_ex_inv by simp
next
  case (6 x y ys qs)
  have "(UniversalFirst (x, y # ys) qs, matrix)
       = add_universal_to_front x (UniversalFirst (y, ys) qs, matrix)"
    for matrix by simp
  then show ?case using eq_prefix_cleansed_p_add_all_inv by metis
next
  case (7 x y ys qs)
  have "(ExistentialFirst (x, y # ys) qs, matrix)
       = add_existential_to_front x (ExistentialFirst (y, ys) qs, matrix)"
    for matrix by simp
  then show ?case using eq_prefix_cleansed_p_add_ex_inv by metis
qed auto

lemma cleansed_prefix_first_ex_unique:
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "x \<notin> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  using assms by (induction "ExistentialFirst (x, xs) qs" rule: prefix_pop.induct) auto

lemma cleansed_prefix_first_all_unique:
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "y \<notin> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  using assms by (induction "UniversalFirst (y, ys) qs" rule: prefix_pop.induct) auto

subsubsection \<open>The Cleansed Predicate is Invariant under PCNF Assignment\<close>

lemma cleansed_add_new_ex_to_front:
  assumes "cleansed_p pcnf"
    and "x \<notin> set (pcnf_prefix_variables pcnf)"
  shows "cleansed_p (add_existential_to_front x pcnf)"
  using assms by (induction x pcnf rule: add_existential_to_front.induct) auto

lemma cleansed_add_new_all_to_front:
  assumes "cleansed_p pcnf"
    and "y \<notin> set (pcnf_prefix_variables pcnf)"
  shows "cleansed_p (add_universal_to_front y pcnf)"
  using assms by (induction y pcnf rule: add_existential_to_front.induct) auto

lemma pcnf_assign_p_ex_eq:
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)
        = (prefix_pop (ExistentialFirst (x, xs) qs), matrix_assign (P x) matrix)"
  using assms by (metis cleansed_prefix_first_ex_unique lit_var.simps(1)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(3))

lemma pcnf_assign_p_all_eq:
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "pcnf_assign (P y) (UniversalFirst (y, ys) qs, matrix)
        = (prefix_pop (UniversalFirst (y, ys) qs), matrix_assign (P y) matrix)"
  using assms by (metis cleansed_prefix_first_all_unique lit_var.simps(1)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(2))

lemma pcnf_assign_n_ex_eq:
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix)
        = (prefix_pop (ExistentialFirst (x, xs) qs), matrix_assign (N x) matrix)"
  using assms by (metis cleansed_prefix_first_ex_unique lit_var.simps(2)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(3))

lemma pcnf_assign_n_all_eq:
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "pcnf_assign (N y) (UniversalFirst (y, ys) qs, matrix)
        = (prefix_pop (UniversalFirst (y, ys) qs), matrix_assign (N y) matrix)"
  using assms by (metis cleansed_prefix_first_all_unique lit_var.simps(2)
      pcnf_assign.simps pcnf_assign_free_eq_matrix_assgn remove_var_prefix.simps(2))

theorem pcnf_assign_cleansed_inv:
  "cleansed_p pcnf \<Longrightarrow> cleansed_p (pcnf_assign lit pcnf)"
proof (induction pcnf rule: convert.induct)
  case (4 x q qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 4 cleansed_p_matrix_inv
        pcnf_assign_n_all_eq[of ?z] pcnf_assign_p_all_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (ExistentialFirst q qs), ?mat)"
      using 4 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (ExistentialFirst q qs), ?mat))"
      using 4 False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_universal_to_prefix x (remove_var_prefix ?z (ExistentialFirst q qs)), ?mat)"
      using cleansed_add_new_all_to_front add_all_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (UniversalFirst (x, []) (q # qs)), ?mat)"
      using False by (induction q) auto
    then show ?thesis by simp
  qed
next
  case (5 x q qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 5 cleansed_p_matrix_inv
        pcnf_assign_n_ex_eq[of ?z] pcnf_assign_p_ex_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (UniversalFirst q qs), ?mat)"
      using 5 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (UniversalFirst q qs), ?mat))"
      using 5 False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_existential_to_prefix x (remove_var_prefix ?z (UniversalFirst q qs)), ?mat)"
      using cleansed_add_new_ex_to_front add_ex_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (ExistentialFirst (x, []) (q # qs)), ?mat)"
      using False by (induction q) auto
    then show ?thesis by simp
  qed
next
  case (6 x y ys qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 6 cleansed_p_matrix_inv
        pcnf_assign_n_all_eq[of ?z] pcnf_assign_p_all_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (UniversalFirst (y, ys) qs), ?mat)"
      using 6 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (UniversalFirst (y, ys) qs), ?mat))"
      using 6(2) False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_universal_to_prefix x (remove_var_prefix ?z (UniversalFirst (y, ys) qs)), ?mat)"
      using cleansed_add_new_all_to_front add_all_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (UniversalFirst (x, (y # ys)) qs), ?mat)"
      using False by simp
    then show ?thesis by simp
  qed
next
  case (7 x y ys qs matrix)
  let ?z = "lit_var lit"
  show ?case
  proof (cases "x = ?z")
    case True
    then show ?thesis using 7 cleansed_p_matrix_inv
        pcnf_assign_n_ex_eq[of ?z] pcnf_assign_p_ex_eq[of ?z]
        prefix_pop_cleansed_if_cleansed lit_var.elims by metis
  next
    case False
    let ?mat = "matrix_assign lit matrix"
    have "cleansed_p (remove_var_prefix ?z (ExistentialFirst (y, ys) qs), ?mat)"
      using 7 by simp
    moreover have "x \<notin> set (pcnf_prefix_variables (remove_var_prefix ?z (ExistentialFirst (y, ys) qs), ?mat))"
      using 7(2) False prefix_assign_vars_eq_prefix_vars_minus_lit[of ?z] prefix_vars_matrix_inv
      by fastforce
    ultimately have "cleansed_p (add_existential_to_prefix x (remove_var_prefix ?z (ExistentialFirst (y, ys) qs)), ?mat)"
      using cleansed_add_new_ex_to_front add_ex_to_prefix_eq_add_to_front by simp
    then have "cleansed_p (remove_var_prefix ?z (ExistentialFirst (x, (y # ys)) qs), ?mat)"
      using False by simp
    then show ?thesis by simp
  qed
qed auto

subsubsection \<open>Cleansing PCNF Formulas\<close>

function pcnf_cleanse :: "pcnf \<Rightarrow> pcnf" where
  "pcnf_cleanse (Empty, matrix) = (Empty, matrix)"
| "pcnf_cleanse (UniversalFirst (y, ys) qs, matrix) =
    (if y \<in> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))
      then pcnf_cleanse (prefix_pop (UniversalFirst (y, ys) qs), matrix)
      else add_universal_to_front y
        (pcnf_cleanse (prefix_pop (UniversalFirst (y, ys) qs), matrix)))"
| "pcnf_cleanse (ExistentialFirst (x, xs) qs, matrix) =
    (if x \<in> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))
      then pcnf_cleanse (prefix_pop (ExistentialFirst (x, xs) qs), matrix)
      else add_existential_to_front x
        (pcnf_cleanse (prefix_pop (ExistentialFirst (x, xs) qs), matrix)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(pre, mat). prefix_measure pre)")
     (auto simp add: prefix_pop_decreases_measure simp del: prefix_measure.simps)

text \<open>Simple tests.\<close>

value "pcnf_cleanse (UniversalFirst (0, [0]) [(0, [1, 2, 0, 1])], [])"

subsubsection \<open>Cleansing Yields a Cleansed Formula\<close>

(* cleansing preserves prefix variables *)
lemma prefix_pop_all_prefix_vars_set:
  "set (pcnf_prefix_variables (UniversalFirst (y, ys) qs, matrix))
  = {y} \<union> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct, induction qs) auto

lemma prefix_pop_ex_prefix_vars_set:
  "set (pcnf_prefix_variables (ExistentialFirst (x, xs) qs, matrix))
  = {x} \<union> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct, induction qs) auto

lemma cleanse_prefix_vars_inv:
  "set (pcnf_prefix_variables (prefix, matrix))
  = set (pcnf_prefix_variables (pcnf_cleanse (prefix, matrix)))"
  using add_all_adds_prefix_var prefix_pop_all_prefix_vars_set
    add_ex_adds_prefix_var prefix_pop_ex_prefix_vars_set
  by (induction "(prefix, matrix)" arbitrary: prefix rule: pcnf_cleanse.induct) auto

(* cleansed_p holds after cleansing *)
theorem pcnf_cleanse_cleanses:
  "cleansed_p (pcnf_cleanse pcnf)"
  using cleanse_prefix_vars_inv cleansed_add_new_all_to_front cleansed_add_new_ex_to_front
  by (induction pcnf rule: pcnf_cleanse.induct) auto

subsubsection \<open>Cleansing Preserves the Set of Free Variables\<close>

lemma prefix_pop_all_vars_inv:
  "set (pcnf_variables (UniversalFirst (y, ys) qs, matrix))
  = set (pcnf_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  by (induction "(UniversalFirst (y, ys) qs, matrix)" rule: convert.induct, induction qs) auto

lemma prefix_pop_ex_vars_inv:
  "set (pcnf_variables (ExistentialFirst (x, xs) qs, matrix))
  = set (pcnf_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  by (induction "(ExistentialFirst (x, xs) qs, matrix)" rule: convert.induct, induction qs) auto

lemma add_all_vars_inv:
  "set (pcnf_variables (add_universal_to_front y pcnf))
  = set (pcnf_variables pcnf)"
  using convert_add_all by auto

lemma add_ex_vars_inv:
  "set (pcnf_variables (add_existential_to_front x pcnf))
  = set (pcnf_variables pcnf)"
  using convert_add_ex by auto

lemma cleanse_vars_inv:
  "set (pcnf_variables (prefix, matrix))
  = set (pcnf_variables (pcnf_cleanse (prefix, matrix)))"
  using add_all_vars_inv prefix_pop_all_vars_inv
    add_ex_vars_inv prefix_pop_ex_vars_inv
  by (induction "(prefix, matrix)" arbitrary: prefix rule: pcnf_cleanse.induct) auto

theorem cleanse_free_vars_inv:
  "set (pcnf_free_variables pcnf)
  = set (pcnf_free_variables (pcnf_cleanse pcnf))"
  using cleanse_prefix_vars_inv cleanse_vars_inv pcnf_free_eq_vars_minus_prefix
  by (induction pcnf) simp_all

subsubsection \<open>Cleansing Preserves Semantics\<close>

lemma pop_redundant_ex_prefix_var_semantics_eq:
  assumes "x \<in> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
  shows "pcnf_semantics I (ExistentialFirst (x, xs) qs, matrix)
        = pcnf_semantics I (prefix_pop (ExistentialFirst (x, xs) qs), matrix)"
proof -
  let ?pcnf = "(ExistentialFirst (x, xs) qs, matrix)"
  let ?pop = "(prefix_pop (ExistentialFirst (x, xs) qs), matrix)"
  have "set (pcnf_prefix_variables ?pcnf) = set (pcnf_prefix_variables ?pop)"
    using assms prefix_pop_ex_prefix_vars_set by auto
  hence "x \<notin> set (pcnf_free_variables ?pop)"
    using assms pcnf_free_eq_vars_minus_prefix by simp
  hence 0: "\<forall>z \<in> set (pcnf_free_variables ?pop). (I(x := b)) z = I z"
    for b by simp
  moreover have "pcnf_semantics I ?pcnf
       \<longleftrightarrow> pcnf_semantics (I(x := True)) ?pop
         \<or> pcnf_semantics (I(x := False)) ?pop"
    by (induction "ExistentialFirst (x, xs) qs" rule: prefix_pop.induct) auto
  ultimately show ?thesis using pcnf_semantics_eq_if_free_vars_eq by blast
qed

lemma pop_redundant_all_prefix_var_semantics_eq:
  assumes "y \<in> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
  shows "pcnf_semantics I (UniversalFirst (y, ys) qs, matrix)
        = pcnf_semantics I (prefix_pop (UniversalFirst (y, ys) qs), matrix)"
proof -
  let ?pcnf = "(UniversalFirst (y, ys) qs, matrix)"
  let ?pop = "(prefix_pop (UniversalFirst (y, ys) qs), matrix)"
  have "set (pcnf_prefix_variables ?pcnf) = set (pcnf_prefix_variables ?pop)"
    using assms prefix_pop_all_prefix_vars_set by auto
  hence "y \<notin> set (pcnf_free_variables ?pop)"
    using assms pcnf_free_eq_vars_minus_prefix by simp
  hence 0: "\<forall>z \<in> set (pcnf_free_variables ?pop). (I(y := b)) z = I z"
    for b by simp
  moreover have "pcnf_semantics I ?pcnf
       \<longleftrightarrow> pcnf_semantics (I(y := True)) ?pop
         \<and> pcnf_semantics (I(y := False)) ?pop"
    by (induction "ExistentialFirst (y, ys) qs" rule: prefix_pop.induct) auto
  ultimately show ?thesis using pcnf_semantics_eq_if_free_vars_eq by blast
qed

lemma pcnf_semantics_disj_eq_add_ex:
  "pcnf_semantics (I(y := True)) pcnf \<or> pcnf_semantics (I(y := False)) pcnf
  \<longleftrightarrow> pcnf_semantics I (add_existential_to_front y pcnf)"
  using convert_add_ex qbf_semantics_eq_pcnf_semantics qbf_semantics_substitute_eq_assign by simp

lemma pcnf_semantics_conj_eq_add_all:
  "pcnf_semantics (I(y := True)) pcnf \<and> pcnf_semantics (I(y := False)) pcnf
  \<longleftrightarrow> pcnf_semantics I (add_universal_to_front y pcnf)"
  using convert_add_all qbf_semantics_eq_pcnf_semantics qbf_semantics_substitute_eq_assign by simp

theorem pcnf_cleanse_preserves_semantics:
  "pcnf_semantics I pcnf = pcnf_semantics I (pcnf_cleanse pcnf)"
proof (induction pcnf arbitrary: I rule: pcnf_cleanse.induct)
  case (2 y ys qs matrix)
  hence 0: "pcnf_semantics I (prefix_pop (UniversalFirst (y, ys) qs), matrix) =
    pcnf_semantics I (pcnf_cleanse (prefix_pop (UniversalFirst (y, ys) qs), matrix))"
    for I by cases auto
  show ?case
  proof (cases "y \<in> set (pcnf_prefix_variables (prefix_pop (UniversalFirst (y, ys) qs), matrix))")
    case True
    then show ?thesis
      using 0 pop_redundant_all_prefix_var_semantics_eq by simp
  next
    case False
    moreover have "pcnf_semantics I (UniversalFirst (y, ys) qs, matrix)
       \<longleftrightarrow> pcnf_semantics (I(y := True)) (prefix_pop (UniversalFirst (y, ys) qs), matrix)
         \<and> pcnf_semantics (I(y := False)) (prefix_pop (UniversalFirst (y, ys) qs), matrix)"
      by (induction "UniversalFirst (y, ys) qs" rule: prefix_pop.induct) auto
    ultimately show ?thesis using 0 pcnf_semantics_conj_eq_add_all by simp
  qed
next
  case (3 x xs qs matrix)
  hence 0: "pcnf_semantics I (prefix_pop (ExistentialFirst (x, xs) qs), matrix) =
    pcnf_semantics I (pcnf_cleanse (prefix_pop (ExistentialFirst (x, xs) qs), matrix))"
    for I by cases auto
  show ?case
  proof (cases "x \<in> set (pcnf_prefix_variables (prefix_pop (ExistentialFirst (x, xs) qs), matrix))")
    case True
    then show ?thesis
      using 0 pop_redundant_ex_prefix_var_semantics_eq by simp
  next
    case False
    moreover have "pcnf_semantics I (ExistentialFirst (x, xs) qs, matrix)
       \<longleftrightarrow> pcnf_semantics (I(x := True)) (prefix_pop (ExistentialFirst (x, xs) qs), matrix)
         \<or> pcnf_semantics (I(x := False)) (prefix_pop (ExistentialFirst (x, xs) qs), matrix)"
      by (induction "ExistentialFirst (x, xs) qs" rule: prefix_pop.induct) auto
    ultimately show ?thesis using 0 pcnf_semantics_disj_eq_add_ex by simp
  qed
qed auto

(* The first-variable satisfiability theorems can be restated using cleansed formulas: *)
theorem sat_ex_first_iff_assign_disj_sat':
  assumes "cleansed_p (ExistentialFirst (x, xs) qs, matrix)"
  shows "satisfiable (convert (ExistentialFirst (x, xs) qs, matrix))
  \<longleftrightarrow> satisfiable (Disj
    [convert (pcnf_assign (P x) (ExistentialFirst (x, xs) qs, matrix)),
     convert (pcnf_assign (N x) (ExistentialFirst (x, xs) qs, matrix))])"
  using assms cleansed_prefix_first_ex_unique sat_ex_first_iff_assign_disj_sat by auto

theorem sat_all_first_iff_assign_conj_sat':
  assumes "cleansed_p (UniversalFirst (y, ys) qs, matrix)"
  shows "satisfiable (convert (UniversalFirst (y, ys) qs, matrix))
  \<longleftrightarrow> satisfiable (Conj
    [convert (pcnf_assign (P y) (UniversalFirst (y, ys) qs, matrix)),
     convert (pcnf_assign (N y) (UniversalFirst (y, ys) qs, matrix))])"
  using assms cleansed_prefix_first_all_unique sat_all_first_iff_assign_conj_sat by auto

subsection \<open>Search Solver (Part 2: The Solver)\<close>

lemma add_all_inc_prefix_measure:
  "prefix_measure (add_universal_to_prefix y prefix) = Suc (prefix_measure prefix)"
  by (induction y prefix rule: add_universal_to_prefix.induct) auto

lemma add_ex_inc_prefix_measure:
  "prefix_measure (add_existential_to_prefix x prefix) = Suc (prefix_measure prefix)"
  by (induction x prefix rule: add_universal_to_prefix.induct) auto

lemma remove_var_non_increasing_measure:
  "prefix_measure (remove_var_prefix z prefix) \<le> prefix_measure prefix"
proof (induction z prefix rule: remove_var_prefix.induct)
  case (2 x y ys qs)
  hence 0: "prefix_measure (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs)))
    \<le> prefix_measure (prefix_pop (UniversalFirst (y, ys) qs))"
  by (cases "x = y") (cases "prefix_pop (UniversalFirst (y, ys) qs) = Empty",simp_all)+
  show ?case
  proof (cases "x = y")
    case True
    hence "prefix_measure (remove_var_prefix x (UniversalFirst (y, ys) qs))
          = prefix_measure (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs)))" by simp
    also have "... \<le> prefix_measure (prefix_pop (UniversalFirst (y, ys) qs))" using 0 by simp
    also have "... \<le> prefix_measure (UniversalFirst (y, ys) qs)"
      using prefix_pop_decreases_measure less_imp_le_nat by blast
    finally show ?thesis .
  next
    case False
    hence "prefix_measure (remove_var_prefix x (UniversalFirst (y, ys) qs))
          = prefix_measure (add_universal_to_prefix y
              (remove_var_prefix x (prefix_pop (UniversalFirst (y, ys) qs))))" by simp
    also have "... \<le> Suc (prefix_measure (prefix_pop (UniversalFirst (y, ys) qs)))"
      using 0 add_all_inc_prefix_measure by simp
    also have "... \<le> prefix_measure (UniversalFirst (y, ys) qs)"
      using Suc_leI prefix_pop_decreases_measure by blast
    finally show ?thesis .
  qed
next
  case (3 x y ys qs)
  hence 0: "prefix_measure (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs)))
    \<le> prefix_measure (prefix_pop (ExistentialFirst (y, ys) qs))"
  by (cases "x = y") (cases "prefix_pop (ExistentialFirst (y, ys) qs) = Empty",simp_all)+
  show ?case
  proof (cases "x = y")
    case True
    hence "prefix_measure (remove_var_prefix x (ExistentialFirst (y, ys) qs))
          = prefix_measure (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs)))" by simp
    also have "... \<le> prefix_measure (prefix_pop (ExistentialFirst (y, ys) qs))" using 0 by simp
    also have "... \<le> prefix_measure (ExistentialFirst (y, ys) qs)"
      using le_eq_less_or_eq prefix_pop_decreases_measure by blast
    finally show ?thesis .
  next
    case False
    hence "prefix_measure (remove_var_prefix x (ExistentialFirst (y, ys) qs))
          = prefix_measure (add_existential_to_prefix y
              (remove_var_prefix x (prefix_pop (ExistentialFirst (y, ys) qs))))" by simp
    also have "... \<le> Suc (prefix_measure (prefix_pop (ExistentialFirst (y, ys) qs)))"
      using 0 add_ex_inc_prefix_measure by simp
    also have "... \<le> prefix_measure (ExistentialFirst (y, ys) qs)"
      using Suc_leI prefix_pop_decreases_measure by blast
    finally show ?thesis .
  qed
qed auto

fun first_var :: "prefix \<Rightarrow> nat option" where
  "first_var (ExistentialFirst (x, xs) qs) = Some x"
| "first_var (UniversalFirst (y, ys) qs) = Some y"
| "first_var Empty = None"

lemma remove_first_var_decreases_measure:
  assumes "prefix \<noteq> Empty"
  shows "prefix_measure (remove_var_prefix (the (first_var prefix)) prefix) < prefix_measure prefix"
  using assms
proof (induction prefix)
  case (UniversalFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair y ys)
    let ?pre = "UniversalFirst (y, ys) qs"
    let ?var = "the (first_var ?pre)"
    have "prefix_measure (remove_var_prefix ?var ?pre)
         \<le> prefix_measure (prefix_pop ?pre)"
      using remove_var_non_increasing_measure by simp
    also have "... < prefix_measure ?pre"
      using prefix_pop_decreases_measure by blast
    finally show ?case .
  qed
next
  case (ExistentialFirst q qs)
  then show ?case
  proof (induction q)
    case (Pair x xs)
    let ?pre = "ExistentialFirst (x, xs) qs"
    let ?var = "the (first_var ?pre)"
    have "prefix_measure (remove_var_prefix ?var ?pre)
         \<le> prefix_measure (prefix_pop ?pre)"
      using remove_var_non_increasing_measure by simp
    also have "... < prefix_measure ?pre"
      using prefix_pop_decreases_measure by blast
    finally show ?case .
  qed
qed auto

fun first_existential :: "prefix \<Rightarrow> bool option" where
  "first_existential (ExistentialFirst q qs) = Some True"
| "first_existential (UniversalFirst q qs) = Some False"
| "first_existential Empty = None"

function search :: "pcnf \<Rightarrow> bool option" where
  "search (prefix, matrix) =
    (if [] \<in> set matrix then Some False
    else if matrix = [] then Some True
    else Option.bind (first_var prefix) (\<lambda>z.
      Option.bind (first_existential prefix) (\<lambda>e. if e
        then combine_options (\<or>)
          (search (pcnf_assign (P z) (prefix, matrix)))
          (search (pcnf_assign (N z) (prefix, matrix)))
        else combine_options (\<and>)
          (search (pcnf_assign (P z) (prefix, matrix)))
          (search (pcnf_assign (N z) (prefix, matrix))))))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(pre, mat). prefix_measure pre)")
      apply simp
     apply (metis first_existential.simps(3) in_measure lit_var.simps(1) option.sel option.simps(3) pcnf_assign.simps prod.simps(2) remove_first_var_decreases_measure)
    apply (metis case_prod_conv first_existential.simps(3) in_measure lit_var.simps(2) option.sel option.simps(3) pcnf_assign.simps remove_first_var_decreases_measure)
   apply (metis case_prod_conv first_existential.simps(3) in_measure lit_var.simps(1) option.sel option.simps(3) pcnf_assign.simps remove_first_var_decreases_measure)
  by (metis case_prod_conv first_existential.simps(3) in_measure lit_var.simps(2) option.sel option.simps(3) pcnf_assign.simps remove_first_var_decreases_measure)

text \<open>Simple tests.\<close>

value "search (UniversalFirst (1, []) [(2, [3])], [])"
value "search (UniversalFirst (1, []) [(2, [3])], [[]])"
value "search (UniversalFirst (1, []) [(2, [3])], [[P 1]])"
value "search (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2]])"
value "search (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2], [N 1, P 3]])"

fun search_solver :: "pcnf \<Rightarrow> bool" where
  "search_solver pcnf = the (search (pcnf_cleanse (pcnf_existential_closure pcnf)))"

text \<open>Simple tests.\<close>

value "search_solver (UniversalFirst (1, []) [(2, [3])], [])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2], [N 1, P 3]])"
value "search_solver (UniversalFirst (1, []) [(2, [3])], [[P 1, N 2], [N 1, P 3], [P 4]])"
value "search_solver (UniversalFirst (1, []) [(2, [3, 3, 3])], [[P 1, N 2], [N 1, P 3], [P 4]])"

subsubsection \<open>Correctness of the Search Function\<close>

lemma no_vars_if_no_free_no_prefix_vars:
  "pcnf_free_variables pcnf = [] \<Longrightarrow> pcnf_prefix_variables pcnf = [] \<Longrightarrow> pcnf_variables pcnf = []"
  by (metis Diff_iff list.set_intros(1) neq_Nil_conv pcnf_free_eq_vars_minus_prefix)

lemma no_vars_if_no_free_empty_prefix:
  "pcnf_free_variables (Empty, matrix) = [] \<Longrightarrow> pcnf_variables (Empty, matrix) = []"
  using no_vars_if_no_free_no_prefix_vars by fastforce

lemma search_cleansed_closed_yields_Some:
  assumes "cleansed_p pcnf" and "pcnf_free_variables pcnf = []"
  shows "(\<exists>b. search pcnf = Some b)" using assms
proof (induction pcnf rule: search.induct)
  case (1 prefix matrix)
  then show ?case
  proof (cases "[] \<in> set matrix")
    case 2: False
    then show ?thesis
    proof (cases "matrix = []")
      case 3: False
      then show ?thesis
      proof (cases "first_var prefix")
        case None
        hence "prefix = Empty" by (induction prefix) auto
        hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
            `pcnf_free_variables (prefix, matrix) = []`
            empty_clause_or_matrix_if_no_variables
            no_vars_if_no_free_empty_prefix by blast
        then show ?thesis by simp
      next
        case 4: (Some z)
        then show ?thesis
        proof (cases "first_existential prefix")
          case None
          hence "prefix = Empty" by (induction prefix) auto
          hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
              `pcnf_free_variables (prefix, matrix) = []`
              empty_clause_or_matrix_if_no_variables
              no_vars_if_no_free_empty_prefix by blast
          then show ?thesis by simp
        next
          case 5: (Some e)
          have 6: "pcnf_free_variables (pcnf_assign lit (prefix, matrix)) = []"
            for lit using pcnf_assign_free_subseteq_free_minus_lit 1(6)
              Diff_empty set_empty subset_Diff_insert subset_empty
              by metis
          then show ?thesis
          proof (cases e)
            case 7: True
            have "search (prefix, matrix)
                  = combine_options (\<or>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 7 by simp
            moreover have "\<exists>b. search (pcnf_assign (P z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(1)[of z e] by blast
            moreover have "\<exists>b. search (pcnf_assign (N z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(2)[of z e] by blast
            ultimately show ?thesis by force
          next
            case 7: False
            have "search (prefix, matrix)
                  = combine_options (\<and>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 7 by simp
            moreover have "\<exists>b. search (pcnf_assign (P z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(3)[of z e] by blast
            moreover have "\<exists>b. search (pcnf_assign (N z) (prefix, matrix)) = Some b"
              using 2 3 4 5 6 7 1(5,6) pcnf_assign_cleansed_inv 1(4)[of z e] by blast
            ultimately show ?thesis by force
          qed
        qed
      qed
    qed auto
  qed auto
qed

theorem search_cleansed_closed_correct:
  assumes "cleansed_p pcnf" and "pcnf_free_variables pcnf = []"
  shows "search pcnf = Some (satisfiable (convert pcnf))" using assms
proof (induction pcnf rule: search.induct)
  case (1 prefix matrix)
  then show ?case
  proof (cases "[] \<in> set matrix")
    case True
    then show ?thesis
      using false_if_empty_clause_in_matrix qbf_semantics_eq_pcnf_semantics satisfiable_def by simp
  next
    case 2: False
    then show ?thesis
    proof (cases "matrix = []")
      case True
      then show ?thesis
        using true_if_matrix_empty qbf_semantics_eq_pcnf_semantics satisfiable_def by simp
    next
      case 3: False
      then show ?thesis
      proof (cases "first_var prefix")
        case None
        hence "prefix = Empty" by (induction prefix) auto
        hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
            `pcnf_free_variables (prefix, matrix) = []`
            empty_clause_or_matrix_if_no_variables
            no_vars_if_no_free_empty_prefix by blast
        then show ?thesis by simp
      next
        case 4: (Some z)
        then show ?thesis
        proof (cases "first_existential prefix")
          case None
          hence "prefix = Empty" by (induction prefix) auto
          hence False using `matrix \<noteq> []` `[] \<notin> set matrix`
              `pcnf_free_variables (prefix, matrix) = []`
              empty_clause_or_matrix_if_no_variables
              no_vars_if_no_free_empty_prefix by blast
          then show ?thesis by simp
        next
          case 5: (Some e)
          have 6: "pcnf_free_variables (pcnf_assign lit (prefix, matrix)) = []"
            for lit using pcnf_assign_free_subseteq_free_minus_lit 1(6)
              Diff_empty set_empty subset_Diff_insert subset_empty
            by metis
          hence 7: "\<exists>b. search (pcnf_assign lit (prefix, matrix)) = Some b" for lit
            using search_cleansed_closed_yields_Some pcnf_assign_cleansed_inv 6 1(5,6) by blast
          then show ?thesis
          proof (cases e)
            case 8: True
            from this obtain x xs qs where prefix_def: "prefix = ExistentialFirst (x, xs) qs"
              using 5 by (induction prefix) auto
            have "search (prefix, matrix)
                  = combine_options (\<or>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 8 by simp
            hence 9: "the (search (prefix, matrix))
                  \<longleftrightarrow> the (search (pcnf_assign (P z) (prefix, matrix)))
                    \<or> the (search (pcnf_assign (N z) (prefix, matrix)))"
              using 7 combine_options_simps(3) option.sel by metis
            have "search (pcnf_assign (P z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (P z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(1)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (P z) (prefix, matrix)))) = {}"
              using 6[of "P z"] by simp
            ultimately have 10: "\<forall>I. the (search (pcnf_assign (P z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (P z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (P z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "search (pcnf_assign (N z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (N z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(2)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (N z) (prefix, matrix)))) = {}"
              using 6[of "N z"] by simp
            ultimately have 11: "\<forall>I. the (search (pcnf_assign (N z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (N z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (N z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "the (search (prefix, matrix))
                 = satisfiable (Disj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))])"
              using 9 10 11 satisfiable_def by simp
            hence "search (prefix, matrix)
                 = Some (satisfiable (Disj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))]))"
              using 1(5,6) search_cleansed_closed_yields_Some by fastforce
            moreover have "z = x" using prefix_def 4 by simp
            ultimately show ?thesis using sat_ex_first_iff_assign_disj_sat' prefix_def 1(5) by simp
          next
            case 8: False
            from this obtain y ys qs where prefix_def: "prefix = UniversalFirst (y, ys) qs"
              using 5 by (induction prefix) auto
            have "search (prefix, matrix)
                  = combine_options (\<and>)
                      (search (pcnf_assign (P z) (prefix, matrix)))
                      (search (pcnf_assign (N z) (prefix, matrix)))"
              using 2 3 4 5 8 by simp
            hence 9: "the (search (prefix, matrix))
                  \<longleftrightarrow> the (search (pcnf_assign (P z) (prefix, matrix)))
                    \<and> the (search (pcnf_assign (N z) (prefix, matrix)))"
              using 7 combine_options_simps(3) option.sel by metis
            have "search (pcnf_assign (P z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (P z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(3)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (P z) (prefix, matrix)))) = {}"
              using 6[of "P z"] by simp
            ultimately have 10: "\<forall>I. the (search (pcnf_assign (P z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (P z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (P z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "search (pcnf_assign (N z) (prefix, matrix))
                 = Some (satisfiable (convert (pcnf_assign (N z) (prefix, matrix))))"
              using 2 3 4 5 6 8 1(5,6) pcnf_assign_cleansed_inv 1(4)[of z e] by blast
            moreover have "set (free_variables (convert (pcnf_assign (N z) (prefix, matrix)))) = {}"
              using 6[of "N z"] by simp
            ultimately have 11: "\<forall>I. the (search (pcnf_assign (N z) (prefix, matrix)))
                  = qbf_semantics I (convert (pcnf_assign (N z) (prefix, matrix)))"
              using semantics_eq_if_free_vars_eq[of "convert (pcnf_assign (N z) (prefix, matrix))"]
              by (auto simp add: satisfiable_def)
            have "the (search (prefix, matrix))
                 = satisfiable (Conj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))])"
              using 9 10 11 satisfiable_def by simp
            hence "search (prefix, matrix)
                 = Some (satisfiable (Conj
                   [convert (pcnf_assign (P z) (prefix, matrix)),
                    convert (pcnf_assign (N z) (prefix, matrix))]))"
              using 1(5,6) search_cleansed_closed_yields_Some by fastforce
            moreover have "z = y" using prefix_def 4 by simp
            ultimately show ?thesis using sat_all_first_iff_assign_conj_sat' prefix_def 1(5) by simp
          qed
        qed
      qed
    qed
  qed
qed

subsubsection \<open>Correctness of the Search Solver\<close>

theorem search_solver_correct:
  "search_solver pcnf \<longleftrightarrow> satisfiable (convert pcnf)"
proof -
  have "satisfiable (convert pcnf)
       = satisfiable (convert (pcnf_cleanse (pcnf_existential_closure pcnf)))"
    using pcnf_sat_iff_ex_close_sat pcnf_cleanse_preserves_semantics
      qbf_semantics_eq_pcnf_semantics satisfiable_def by simp
  moreover have "pcnf_free_variables (pcnf_cleanse (pcnf_existential_closure pcnf)) = []"
    using pcnf_ex_closure_no_free cleanse_free_vars_inv set_empty by metis
  moreover have "cleansed_p (pcnf_cleanse (pcnf_existential_closure pcnf))"
    using pcnf_cleanse_cleanses by blast
  ultimately show ?thesis using search_cleansed_closed_correct by simp
qed

end