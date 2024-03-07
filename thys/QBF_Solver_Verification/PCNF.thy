section \<open>Prenex Conjunctive Normal Form Datatype\<close>

theory PCNF
  imports NaiveSolver
begin

subsection \<open>Prenex Conjunctive Normal Form Datatype\<close>

datatype literal = P nat | N nat

type_synonym clause = "literal list"
type_synonym matrix = "clause list"

type_synonym quant_set = "nat \<times> nat list"
type_synonym quant_sets = "quant_set list"

datatype prefix = UniversalFirst quant_set quant_sets
  | ExistentialFirst quant_set quant_sets
  | Empty

type_synonym pcnf = "prefix \<times> matrix"

subsubsection \<open>PCNF Predicate for Generic QBFs\<close>

(* Is the QBF a literal? *)
fun literal_p :: "QBF \<Rightarrow> bool" where
  "literal_p (Var _) = True"
| "literal_p (Neg (Var _)) = True"
| "literal_p _ = False"

(* Is the QBF a clause? *)
fun clause_p :: "QBF \<Rightarrow> bool" where
  "clause_p (Disj list) = list_all literal_p list"
| "clause_p _ = False"

(* Is the QBF in conjunctive normal form? *)
fun cnf_p :: "QBF \<Rightarrow> bool" where
  "cnf_p (Conj list) = list_all clause_p list"
| "cnf_p _ = False"

(* Is the QBF in prenex normal form with a conjunctive normal form matrix? *)
fun pcnf_p :: "QBF \<Rightarrow> bool" where
  "pcnf_p (Ex _ qbf) = pcnf_p qbf"
| "pcnf_p (All _ qbf) = pcnf_p qbf"
| "pcnf_p (Conj list) = cnf_p (Conj list)"
| "pcnf_p _ = False"

subsubsection \<open>Bijection with PCNF Subset of Generic QBF Datatype\<close>

text \<open>Conversion functions, left-inverses thereof, and proofs of the left-inverseness.\<close>

(* Convert literal *)
fun convert_literal :: "literal \<Rightarrow> QBF" where
  "convert_literal (P z) = Var z"
| "convert_literal (N z) = Neg (Var z)"

lemma convert_literal_p: "literal_p (convert_literal lit)"
  by (cases lit) auto

fun convert_literal_inv :: "QBF \<Rightarrow> literal option" where
  "convert_literal_inv (Var z) = Some (P z)"
| "convert_literal_inv (Neg (Var z)) = Some (N z)"
| "convert_literal_inv _ = None"

lemma literal_inv: "convert_literal_inv (convert_literal lit) = Some lit"
  by (cases lit) auto

(* Convert clause *)
fun convert_clause :: "clause \<Rightarrow> QBF" where
  "convert_clause cl = Disj (map convert_literal cl)"

lemma convert_clause_p: "clause_p (convert_clause cl)"
  using convert_literal_p by (induction cl) auto

fun convert_clause_inv :: "QBF \<Rightarrow> clause option" where
  "convert_clause_inv (Disj list) = sequence (map convert_literal_inv list)"
| "convert_clause_inv _ = None"

lemma clause_inv: "convert_clause_inv (convert_clause cl) = Some cl"
proof -
  let ?list = "map convert_literal_inv (map convert_literal cl)"
  have "\<forall>x \<in> set cl. convert_literal_inv (convert_literal x) = Some x" using literal_inv by simp
  hence "map Some cl = ?list" using list_no_None_ex_list_map_Some by fastforce
  hence "sequence ?list = Some cl" using sequence_content by metis
  thus "convert_clause_inv (convert_clause cl) = Some cl" by simp
qed

(* Convert matrix *)
fun convert_matrix :: "matrix \<Rightarrow> QBF" where
  "convert_matrix matrix = Conj (map convert_clause matrix)"

lemma convert_cnf_p: "cnf_p (convert_matrix mat)"
  using convert_clause_p by (induction mat) auto

fun convert_matrix_inv :: "QBF \<Rightarrow> matrix option" where
  "convert_matrix_inv (Conj list) = sequence (map convert_clause_inv list)"
| "convert_matrix_inv _ = None"

lemma matrix_inv: "convert_matrix_inv (convert_matrix mat) = Some mat"
proof -
  let ?list = "map convert_clause_inv (map convert_clause mat)"
  have "\<forall>x \<in> set mat. convert_clause_inv (convert_clause x) = Some x" using clause_inv by simp
  hence "map Some mat = ?list" using list_no_None_ex_list_map_Some by fastforce
  hence "sequence ?list = Some mat" using sequence_content by metis
  thus "convert_matrix_inv (convert_matrix mat) = Some mat" by simp
qed

(* Convert prefix *)

(* Length of quantifier set, used to show termination of convert. *)
fun q_length :: "'a \<times> 'a list \<Rightarrow> nat" where
  "q_length (x, xs) = 1 + length xs"

(* Measure length of all quantifier sets in prefix, used to show termination of convert. *)
fun measure_prefix_length :: "pcnf \<Rightarrow> nat" where
  "measure_prefix_length (Empty, _) = 0"
| "measure_prefix_length (UniversalFirst q qs, _) = q_length q + sum_list (map q_length qs)"
| "measure_prefix_length (ExistentialFirst q qs, _) = q_length q + sum_list (map q_length qs)"

(* Convert a PCNF formula to a QBF formula. A left-inverse exists, see theorem convert_inv. *)
function convert :: "pcnf \<Rightarrow> QBF" where
  "convert (Empty, matrix) = convert_matrix matrix"
| "convert (UniversalFirst (x, []) [], matrix) = All x (convert (Empty, matrix))"
| "convert (ExistentialFirst (x, []) [], matrix) = Ex x (convert (Empty, matrix))"
| "convert (UniversalFirst (x, []) (q # qs), matrix) = All x (convert (ExistentialFirst q qs, matrix))"
| "convert (ExistentialFirst (x, []) (q # qs), matrix) = Ex x (convert (UniversalFirst q qs, matrix))"
| "convert (UniversalFirst (x, y # ys) qs, matrix) = All x (convert (UniversalFirst (y, ys) qs, matrix))"
| "convert (ExistentialFirst (x, y # ys) qs, matrix) = Ex x (convert (ExistentialFirst (y, ys) qs, matrix))"
  by pat_completeness auto
termination
  by (relation "measure measure_prefix_length") auto

theorem convert_pcnf_p: "pcnf_p (convert pcnf)"
  using convert_cnf_p by (induction rule: convert.induct) auto

(* Add universal quantifier to front of pcnf formula. *)
fun add_universal_to_front :: "nat \<Rightarrow> pcnf \<Rightarrow> pcnf" where
  "add_universal_to_front x (Empty, matrix) = (UniversalFirst (x, []) [], matrix)"
| "add_universal_to_front x (UniversalFirst (y, ys) qs, matrix) = (UniversalFirst (x, y # ys) qs, matrix)"
| "add_universal_to_front x (ExistentialFirst (y, ys) qs, matrix) = (UniversalFirst (x, []) ((y, ys) # qs), matrix)"

(* Add existential quantifier to front of pcnf formula. *)
fun add_existential_to_front :: "nat \<Rightarrow> pcnf \<Rightarrow> pcnf" where
  "add_existential_to_front x (Empty, matrix) = (ExistentialFirst (x, []) [], matrix)"
| "add_existential_to_front x (ExistentialFirst (y, ys) qs, matrix) = (ExistentialFirst (x, y # ys) qs, matrix)"
| "add_existential_to_front x (UniversalFirst (y, ys) qs, matrix) = (ExistentialFirst (x, []) ((y, ys) # qs), matrix)"

(* Left-inverse for convert, see theorem convert_inv. *)
fun convert_inv :: "QBF \<Rightarrow> pcnf option" where
  "convert_inv (All x qbf) = map_option (\<lambda>p. add_universal_to_front x p) (convert_inv qbf)"
| "convert_inv (Ex x qbf) = map_option (\<lambda>p. add_existential_to_front x p) (convert_inv qbf)"
| "convert_inv qbf = map_option (\<lambda>m. (Empty, m)) (convert_matrix_inv qbf)"

lemma convert_add_all: "convert (add_universal_to_front x pcnf) = All x (convert pcnf)"
  by (induction rule: add_universal_to_front.induct) auto

lemma convert_add_ex: "convert (add_existential_to_front x pcnf) = Ex x (convert pcnf)"
  by (induction rule: add_existential_to_front.induct) auto

(* convert_inv is a left-inverse of convert *)
theorem convert_inv: "convert_inv (convert pcnf) = Some pcnf"
proof (induction pcnf)
  case (Pair prefix matrix)
  show "convert_inv (convert (prefix, matrix)) = Some (prefix, matrix)"
    using matrix_inv by (induction rule: convert.induct) auto
qed

(* Corollary: convert is injective. *)
theorem convert_injective: "inj convert"
  apply (rule inj_on_inverseI[where ?g = "the \<circ> convert_inv"])
  by (simp add: convert_inv)

text \<open>There is a PCNF formula yielding any @{const pcnf_p} QBF formula:\<close>

lemma convert_literal_p_ex:
  assumes "literal_p lit"
  shows "\<exists>l. convert_literal l = lit"
proof -
  have "\<exists>l. convert_literal l = Var x" for x using convert_literal.simps by blast
  moreover have "\<exists>l. convert_literal l = Neg (Var x)" for x using convert_literal.simps by blast
  ultimately show "\<exists>l. convert_literal l = lit"
    using assms by (induction rule: literal_p.induct) auto
qed

lemma convert_clause_p_ex:
  assumes "clause_p cl"
  shows "\<exists>c. convert_clause c = cl"
proof -
  from assms obtain xs where 0: "Disj xs = cl" by (metis clause_p.elims(2))
  hence "list_all literal_p xs" using assms by fastforce  
  hence "\<exists>ys. map convert_literal ys = xs" using convert_literal_p_ex
  proof (induction xs)
    case Nil
    show "\<exists>ys. map convert_literal ys = []" by simp
  next
    case (Cons x xs)
    from this obtain ys where "map convert_literal ys = xs" by fastforce
    moreover from Cons obtain y where "convert_literal y = x" by fastforce
    ultimately have "map convert_literal (y # ys) = x # xs" by simp
    thus "\<exists>ys. map convert_literal ys = x # xs" by (rule exI)
  qed
  thus "\<exists>c. convert_clause c = cl" using 0 by fastforce
qed

lemma convert_cnf_p_ex:
  assumes "cnf_p mat"
  shows "\<exists>m. convert_matrix m = mat"
proof -
  from assms obtain xs where 0: "Conj xs = mat" by (metis cnf_p.elims(2))
  hence "list_all clause_p xs" using assms by fastforce
  hence "\<exists>ys. map convert_clause ys = xs" using convert_clause_p_ex
  proof (induction xs)
    case Nil
    show "\<exists>ys. map convert_clause ys = []" by simp
  next
    case (Cons x xs)
    from this obtain ys where "map convert_clause ys = xs" by fastforce
    moreover from Cons obtain y where "convert_clause y = x" by fastforce
    ultimately have "map convert_clause (y # ys) = x # xs" by simp
    thus "\<exists>ys. map convert_clause ys = x # xs" by (rule exI)
  qed
  thus "\<exists>m. convert_matrix m = mat" using 0 by fastforce
qed

theorem convert_pcnf_p_ex:
  assumes "pcnf_p qbf"
  shows "\<exists>pcnf. convert pcnf = qbf" using assms
proof (induction qbf)
  case (Conj x)
  hence "cnf_p (Conj x)" by simp
  from this obtain m where "convert_matrix m = Conj x" using convert_cnf_p_ex by blast
  hence "convert (Empty, m) = Conj x" by simp
  thus "\<exists>pcnf. convert pcnf = Conj x" by (rule exI)
next
  case (Ex x1a qbf)
  from this obtain pcnf where "convert pcnf = qbf" by fastforce
  hence "convert (add_existential_to_front x1a pcnf) = Ex x1a qbf" using convert_add_ex by simp
  thus "\<exists>pcnf. convert pcnf = QBF.Ex x1a qbf" by (rule exI)
next
  case (All x1a qbf)
  from this obtain pcnf where "convert pcnf = qbf" by fastforce
  hence "convert (add_universal_to_front x1a pcnf) = All x1a qbf" using convert_add_all by simp
  thus "\<exists>pcnf. convert pcnf = QBF.All x1a qbf" by (rule exI)
qed auto

(* range of convert *)
theorem convert_range: "range convert = {p. pcnf_p p}"
  using convert_pcnf_p convert_pcnf_p_ex by blast

(* convert bijective on pcnf_p subset of QBF *)
theorem convert_bijective_on: "bij_betw convert UNIV {p. pcnf_p p}"
  by (simp add: bij_betw_def convert_injective convert_range)

subsubsection \<open>Preservation of Semantics under the Bijection\<close>

fun literal_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> literal \<Rightarrow> bool" where
  "literal_semantics I (P x) = I x"
| "literal_semantics I (N x) = (\<not>I x)"

fun clause_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> clause \<Rightarrow> bool" where
  "clause_semantics I clause = list_ex (literal_semantics I) clause"

fun matrix_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> matrix \<Rightarrow> bool" where
  "matrix_semantics I matrix = list_all (clause_semantics I) matrix"

function pcnf_semantics :: "(nat \<Rightarrow> bool) \<Rightarrow> pcnf \<Rightarrow> bool" where
  "pcnf_semantics I (Empty, matrix) =
    matrix_semantics I matrix"
| "pcnf_semantics I (UniversalFirst (y, []) [], matrix) =
    (pcnf_semantics (I(y := True)) (Empty, matrix)
    \<and> pcnf_semantics (I(y := False)) (Empty, matrix))"
| "pcnf_semantics I (ExistentialFirst (x, []) [], matrix) =
    (pcnf_semantics (I(x := True)) (Empty, matrix)
    \<or> pcnf_semantics (I(x := False)) (Empty, matrix))"
| "pcnf_semantics I (UniversalFirst (y, []) (q # qs), matrix) =
    (pcnf_semantics (I(y := True)) (ExistentialFirst q qs, matrix)
    \<and> pcnf_semantics (I(y := False)) (ExistentialFirst q qs, matrix))"
| "pcnf_semantics I (ExistentialFirst (x, []) (q # qs), matrix) =
    (pcnf_semantics (I(x := True)) (UniversalFirst q qs, matrix)
    \<or> pcnf_semantics (I(x := False)) (UniversalFirst q qs, matrix))"
| "pcnf_semantics I (UniversalFirst (y, yy # ys) qs, matrix) =
    (pcnf_semantics (I(y := True)) (UniversalFirst (yy, ys) qs, matrix)
    \<and> pcnf_semantics (I(y := False)) (UniversalFirst (yy, ys) qs, matrix))"
| "pcnf_semantics I (ExistentialFirst (x, xx # xs) qs, matrix) =
    (pcnf_semantics (I(x := True)) (ExistentialFirst (xx, xs) qs, matrix)
    \<or> pcnf_semantics (I(x := False)) (ExistentialFirst (xx, xs) qs, matrix))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(I,p). measure_prefix_length p)") auto

theorem qbf_semantics_eq_pcnf_semantics:
  "pcnf_semantics I pcnf = qbf_semantics I (convert pcnf)"
proof (induction pcnf arbitrary: I rule: convert.induct)
  case (1 matrix)
  then show ?case
  proof (induction matrix)
    case (Cons cl cls)
    then show ?case
    proof (induction cl)
      case (Cons l ls)
      then show ?case by (induction l) force+
    qed auto
  qed auto
next
  case (2 x matrix)
  then show ?case using convert.simps(2) pcnf_semantics.simps(2)
      qbf_semantics.simps(6) qbf_semantics_substitute_eq_assign by presburger
next
  case (3 x matrix)
  then show ?case using convert.simps(3) pcnf_semantics.simps(3)
      qbf_semantics.simps(5) qbf_semantics_substitute_eq_assign by presburger
next
  case (4 x q qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
next
  case (5 x q qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
next
  case (6 x y ys qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
next
  case (7 x y ys qs matrix)
  then show ?case using qbf_semantics_substitute_eq_assign by fastforce
qed

(* convert is left-inverse of convert_inv for pcnf_p QBF formulas *)
lemma convert_inv_inv:
  "pcnf_p qbf \<Longrightarrow> convert (the (convert_inv qbf)) = qbf"
  by (metis convert_inv convert_pcnf_p_ex option.sel)

theorem qbf_semantics_eq_pcnf_semantics':
  assumes "pcnf_p qbf"
  shows "qbf_semantics I qbf = pcnf_semantics I (the (convert_inv qbf))"
  using qbf_semantics_eq_pcnf_semantics assms convert_inv_inv by simp

end