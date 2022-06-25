theory FO
  imports Main
begin

abbreviation "sorted_distinct xs \<equiv> sorted xs \<and> distinct xs"

datatype 'a fo_term = Const 'a | Var nat

type_synonym 'a val = "nat \<Rightarrow> 'a"

fun list_fo_term :: "'a fo_term \<Rightarrow> 'a list" where
  "list_fo_term (Const c) = [c]"
| "list_fo_term _ = []"

fun fv_fo_term_list :: "'a fo_term \<Rightarrow> nat list" where
  "fv_fo_term_list (Var n) = [n]"
| "fv_fo_term_list _ = []"

fun fv_fo_term_set :: "'a fo_term \<Rightarrow> nat set" where
  "fv_fo_term_set (Var n) = {n}"
| "fv_fo_term_set _ = {}"

definition fv_fo_terms_set :: "('a fo_term) list \<Rightarrow> nat set" where
  "fv_fo_terms_set ts = \<Union>(set (map fv_fo_term_set ts))"

fun fv_fo_terms_list_rec :: "('a fo_term) list \<Rightarrow> nat list" where
  "fv_fo_terms_list_rec [] = []"
| "fv_fo_terms_list_rec (t # ts) = fv_fo_term_list t @ fv_fo_terms_list_rec ts"

definition fv_fo_terms_list :: "('a fo_term) list \<Rightarrow> nat list" where
  "fv_fo_terms_list ts = remdups_adj (sort (fv_fo_terms_list_rec ts))"

fun eval_term :: "'a val \<Rightarrow> 'a fo_term \<Rightarrow> 'a" (infix "\<cdot>" 60) where
  "eval_term \<sigma> (Const c) = c"
| "eval_term \<sigma> (Var n) = \<sigma> n"

definition eval_terms :: "'a val \<Rightarrow> ('a fo_term) list \<Rightarrow> 'a list" (infix "\<odot>" 60) where
  "eval_terms \<sigma> ts = map (eval_term \<sigma>) ts"

lemma finite_set_fo_term: "finite (set_fo_term t)"
  by (cases t) auto

lemma list_fo_term_set: "set (list_fo_term t) = set_fo_term t"
  by (cases t) auto

lemma finite_fv_fo_term_set: "finite (fv_fo_term_set t)"
  by (cases t) auto

lemma fv_fo_term_setD: "n \<in> fv_fo_term_set t \<Longrightarrow> t = Var n"
  by (cases t) auto

lemma fv_fo_term_set_list: "set (fv_fo_term_list t) = fv_fo_term_set t"
  by (cases t) auto

lemma sorted_distinct_fv_fo_term_list: "sorted_distinct (fv_fo_term_list t)"
  by (cases t) auto

lemma fv_fo_term_set_cong: "fv_fo_term_set t = fv_fo_term_set (map_fo_term f t)"
  by (cases t) auto

lemma fv_fo_terms_setI: "Var m \<in> set ts \<Longrightarrow> m \<in> fv_fo_terms_set ts"
  by (induction ts) (auto simp: fv_fo_terms_set_def)

lemma fv_fo_terms_setD: "m \<in> fv_fo_terms_set ts \<Longrightarrow> Var m \<in> set ts"
  by (induction ts) (auto simp: fv_fo_terms_set_def dest: fv_fo_term_setD)

lemma finite_fv_fo_terms_set: "finite (fv_fo_terms_set ts)"
  by (auto simp: fv_fo_terms_set_def finite_fv_fo_term_set)

lemma fv_fo_terms_set_list: "set (fv_fo_terms_list ts) = fv_fo_terms_set ts"
  using fv_fo_term_set_list
  unfolding fv_fo_terms_list_def
  by (induction ts rule: fv_fo_terms_list_rec.induct)
     (auto simp: fv_fo_terms_set_def set_insort_key)

lemma distinct_remdups_adj_sort: "sorted xs \<Longrightarrow> distinct (remdups_adj xs)"
  by (induction xs rule: induct_list012) auto

lemma sorted_distinct_fv_fo_terms_list: "sorted_distinct (fv_fo_terms_list ts)"
  unfolding fv_fo_terms_list_def
  by (induction ts rule: fv_fo_terms_list_rec.induct)
     (auto simp add: sorted_insort intro: distinct_remdups_adj_sort)

lemma fv_fo_terms_set_cong: "fv_fo_terms_set ts = fv_fo_terms_set (map (map_fo_term f) ts)"
  using fv_fo_term_set_cong
  by (induction ts) (fastforce simp: fv_fo_terms_set_def)+

lemma eval_term_cong: "(\<And>n. n \<in> fv_fo_term_set t \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  eval_term \<sigma> t = eval_term \<sigma>' t"
  by (cases t) auto

lemma eval_terms_fv_fo_terms_set: "\<sigma> \<odot> ts = \<sigma>' \<odot> ts \<Longrightarrow> n \<in> fv_fo_terms_set ts \<Longrightarrow> \<sigma> n = \<sigma>' n"
proof (induction ts)
  case (Cons t ts)
  then show ?case
    by (cases t) (auto simp: eval_terms_def fv_fo_terms_set_def)
qed (auto simp: eval_terms_def fv_fo_terms_set_def)

lemma eval_terms_cong: "(\<And>n. n \<in> fv_fo_terms_set ts \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  eval_terms \<sigma> ts = eval_terms \<sigma>' ts"
  by (auto simp: eval_terms_def fv_fo_terms_set_def intro: eval_term_cong)

datatype ('a, 'b) fo_fmla =
  Pred 'b "('a fo_term) list"
| Bool bool
| Eqa "'a fo_term" "'a fo_term"
| Neg "('a, 'b) fo_fmla"
| Conj "('a, 'b) fo_fmla" "('a, 'b) fo_fmla"
| Disj "('a, 'b) fo_fmla" "('a, 'b) fo_fmla"
| Exists nat "('a, 'b) fo_fmla"
| Forall nat "('a, 'b) fo_fmla"

fun fv_fo_fmla_list_rec :: "('a, 'b) fo_fmla \<Rightarrow> nat list" where
  "fv_fo_fmla_list_rec (Pred _ ts) = fv_fo_terms_list ts"
| "fv_fo_fmla_list_rec (Bool b) = []"
| "fv_fo_fmla_list_rec (Eqa t t') = fv_fo_term_list t @ fv_fo_term_list t'"
| "fv_fo_fmla_list_rec (Neg \<phi>) = fv_fo_fmla_list_rec \<phi>"
| "fv_fo_fmla_list_rec (Conj \<phi> \<psi>) = fv_fo_fmla_list_rec \<phi> @ fv_fo_fmla_list_rec \<psi>"
| "fv_fo_fmla_list_rec (Disj \<phi> \<psi>) = fv_fo_fmla_list_rec \<phi> @ fv_fo_fmla_list_rec \<psi>"
| "fv_fo_fmla_list_rec (Exists n \<phi>) = filter (\<lambda>m. n \<noteq> m) (fv_fo_fmla_list_rec \<phi>)"
| "fv_fo_fmla_list_rec (Forall n \<phi>) = filter (\<lambda>m. n \<noteq> m) (fv_fo_fmla_list_rec \<phi>)"

definition fv_fo_fmla_list :: "('a, 'b) fo_fmla \<Rightarrow> nat list" where
  "fv_fo_fmla_list \<phi> = remdups_adj (sort (fv_fo_fmla_list_rec \<phi>))"

fun fv_fo_fmla :: "('a, 'b) fo_fmla \<Rightarrow> nat set" where
  "fv_fo_fmla (Pred _ ts) = fv_fo_terms_set ts"
| "fv_fo_fmla (Bool b) = {}"
| "fv_fo_fmla (Eqa t t') = fv_fo_term_set t \<union> fv_fo_term_set t'"
| "fv_fo_fmla (Neg \<phi>) = fv_fo_fmla \<phi>"
| "fv_fo_fmla (Conj \<phi> \<psi>) = fv_fo_fmla \<phi> \<union> fv_fo_fmla \<psi>"
| "fv_fo_fmla (Disj \<phi> \<psi>) = fv_fo_fmla \<phi> \<union> fv_fo_fmla \<psi>"
| "fv_fo_fmla (Exists n \<phi>) = fv_fo_fmla \<phi> - {n}"
| "fv_fo_fmla (Forall n \<phi>) = fv_fo_fmla \<phi> - {n}"

lemma finite_fv_fo_fmla: "finite (fv_fo_fmla \<phi>)"
  by (induction \<phi> rule: fv_fo_fmla.induct)
     (auto simp: finite_fv_fo_term_set finite_fv_fo_terms_set)

lemma fv_fo_fmla_list_set: "set (fv_fo_fmla_list \<phi>) = fv_fo_fmla \<phi>"
  unfolding fv_fo_fmla_list_def
  by (induction \<phi> rule: fv_fo_fmla.induct) (auto simp: fv_fo_terms_set_list fv_fo_term_set_list)

lemma sorted_distinct_fv_list: "sorted_distinct (fv_fo_fmla_list \<phi>)"
  by (auto simp: fv_fo_fmla_list_def intro: distinct_remdups_adj_sort)

lemma length_fv_fo_fmla_list: "length (fv_fo_fmla_list \<phi>) = card (fv_fo_fmla \<phi>)"
  using fv_fo_fmla_list_set[of \<phi>] sorted_distinct_fv_list[of \<phi>]
    distinct_card[of "fv_fo_fmla_list \<phi>"]
  by auto

lemma fv_fo_fmla_list_eq: "fv_fo_fmla \<phi> = fv_fo_fmla \<psi> \<Longrightarrow> fv_fo_fmla_list \<phi> = fv_fo_fmla_list \<psi>"
  using fv_fo_fmla_list_set sorted_distinct_fv_list
  by (metis sorted_distinct_set_unique)

lemma fv_fo_fmla_list_Conj: "fv_fo_fmla_list (Conj \<phi> \<psi>) = fv_fo_fmla_list (Conj \<psi> \<phi>)"
  using fv_fo_fmla_list_eq[of "Conj \<phi> \<psi>" "Conj \<psi> \<phi>"]
  by auto

type_synonym 'a table = "('a list) set"

type_synonym ('t, 'b) fo_intp = "'b \<times> nat \<Rightarrow> 't"

fun wf_fo_intp :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> bool" where
  "wf_fo_intp (Pred r ts) I \<longleftrightarrow> finite (I (r, length ts))"
| "wf_fo_intp (Bool b) I \<longleftrightarrow> True"
| "wf_fo_intp (Eqa t t') I \<longleftrightarrow> True"
| "wf_fo_intp (Neg \<phi>) I \<longleftrightarrow> wf_fo_intp \<phi> I"
| "wf_fo_intp (Conj \<phi> \<psi>) I \<longleftrightarrow> wf_fo_intp \<phi> I \<and> wf_fo_intp \<psi> I"
| "wf_fo_intp (Disj \<phi> \<psi>) I \<longleftrightarrow> wf_fo_intp \<phi> I \<and> wf_fo_intp \<psi> I"
| "wf_fo_intp (Exists n \<phi>) I \<longleftrightarrow> wf_fo_intp \<phi> I"
| "wf_fo_intp (Forall n \<phi>) I \<longleftrightarrow> wf_fo_intp \<phi> I"

fun sat :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> 'a val \<Rightarrow> bool" where
  "sat (Pred r ts) I \<sigma> \<longleftrightarrow> \<sigma> \<odot> ts \<in> I (r, length ts)"
| "sat (Bool b) I \<sigma> \<longleftrightarrow> b"
| "sat (Eqa t t') I \<sigma> \<longleftrightarrow> \<sigma> \<cdot> t = \<sigma> \<cdot> t'"
| "sat (Neg \<phi>) I \<sigma> \<longleftrightarrow> \<not>sat \<phi> I \<sigma>"
| "sat (Conj \<phi> \<psi>) I \<sigma> \<longleftrightarrow> sat \<phi> I \<sigma> \<and> sat \<psi> I \<sigma>"
| "sat (Disj \<phi> \<psi>) I \<sigma> \<longleftrightarrow> sat \<phi> I \<sigma> \<or> sat \<psi> I \<sigma>"
| "sat (Exists n \<phi>) I \<sigma> \<longleftrightarrow> (\<exists>x. sat \<phi> I (\<sigma>(n := x)))"
| "sat (Forall n \<phi>) I \<sigma> \<longleftrightarrow> (\<forall>x. sat \<phi> I (\<sigma>(n := x)))"

lemma sat_fv_cong: "(\<And>n. n \<in> fv_fo_fmla \<phi> \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  sat \<phi> I \<sigma> \<longleftrightarrow> sat \<phi> I \<sigma>'"
proof (induction \<phi> arbitrary: \<sigma> \<sigma>')
  case (Neg \<phi>)
  show ?case
    using Neg(1)[of \<sigma> \<sigma>'] Neg(2)
    by auto
next
  case (Conj \<phi> \<psi>)
  show ?case
    using Conj(1,2)[of \<sigma> \<sigma>'] Conj(3)
    by auto
next
  case (Disj \<phi> \<psi>)
  show ?case
    using Disj(1,2)[of \<sigma> \<sigma>'] Disj(3)
    by auto
next
  case (Exists n \<phi>)
  have "\<And>x. sat \<phi> I (\<sigma>(n := x)) = sat \<phi> I (\<sigma>'(n := x))"
    using Exists(2)
    by (auto intro!: Exists(1))
  then show ?case
    by simp
next
  case (Forall n \<phi>)
  have "\<And>x. sat \<phi> I (\<sigma>(n := x)) = sat \<phi> I (\<sigma>'(n := x))"
    using Forall(2)
    by (auto intro!: Forall(1))
  then show ?case
    by simp
qed (auto cong: eval_terms_cong eval_term_cong)

definition proj_sat :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> 'a table" where
  "proj_sat \<phi> I = (\<lambda>\<sigma>. map \<sigma> (fv_fo_fmla_list \<phi>)) ` {\<sigma>. sat \<phi> I \<sigma>}"

end