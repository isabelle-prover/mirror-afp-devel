section \<open>Relational Calculus\<close>

(*<*)
theory Relational_Calculus
imports
  Preliminaries
  "Deriving.Derive"
begin
(*>*)

subsection \<open>First-order Terms\<close>

datatype 'a "term" = Const 'a | Var nat

type_synonym 'a val = "nat \<Rightarrow> 'a"

fun fv_term_set :: "'a term \<Rightarrow> nat set" where
  "fv_term_set (Var n) = {n}"
| "fv_term_set _ = {}"

fun fv_fo_term_list :: "'a term \<Rightarrow> nat list" where
  "fv_fo_term_list (Var n) = [n]"
| "fv_fo_term_list _ = []"

definition fv_terms_set :: "('a term) list \<Rightarrow> nat set" where
  "fv_terms_set ts = \<Union>(set (map fv_term_set ts))"

fun eval_term :: "'a val \<Rightarrow> 'a term \<Rightarrow> 'a" (infix "\<cdot>" 60) where
  "eval_term \<sigma> (Const c) = c"
| "eval_term \<sigma> (Var n) = \<sigma> n"

definition eval_terms :: "'a val \<Rightarrow> ('a term) list \<Rightarrow> 'a list" (infix "\<odot>" 60) where
  "eval_terms \<sigma> ts = map (eval_term \<sigma>) ts"

lemma finite_set_term: "finite (set_term t)"
  by (cases t) auto

lemma finite_fv_term_set: "finite (fv_term_set t)"
  by (cases t) auto

lemma fv_term_setD: "n \<in> fv_term_set t \<Longrightarrow> t = Var n"
  by (cases t) auto

lemma fv_term_set_cong: "fv_term_set t = fv_term_set (map_term f t)"
  by (cases t) auto

lemma fv_terms_setI: "Var m \<in> set ts \<Longrightarrow> m \<in> fv_terms_set ts"
  by (induction ts) (auto simp: fv_terms_set_def)

lemma fv_terms_setD: "m \<in> fv_terms_set ts \<Longrightarrow> Var m \<in> set ts"
  by (induction ts) (auto simp: fv_terms_set_def dest: fv_term_setD)

lemma finite_fv_terms_set: "finite (fv_terms_set ts)"
  by (auto simp: fv_terms_set_def finite_fv_term_set)

lemma fv_terms_set_cong: "fv_terms_set ts = fv_terms_set (map (map_term f) ts)"
  using fv_term_set_cong
  by (induction ts) (fastforce simp: fv_terms_set_def)+

lemma eval_term_cong: "(\<And>n. n \<in> fv_term_set t \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  eval_term \<sigma> t = eval_term \<sigma>' t"
  by (cases t) auto

lemma eval_terms_fv_terms_set: "\<sigma> \<odot> ts = \<sigma>' \<odot> ts \<Longrightarrow> n \<in> fv_terms_set ts \<Longrightarrow> \<sigma> n = \<sigma>' n"
proof (induction ts)
  case (Cons t ts)
  then show ?case
    by (cases t) (auto simp: eval_terms_def fv_terms_set_def)
qed (auto simp: eval_terms_def fv_terms_set_def)

lemma eval_terms_cong: "(\<And>n. n \<in> fv_terms_set ts \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
  eval_terms \<sigma> ts = eval_terms \<sigma>' ts"
  by (auto simp: eval_terms_def fv_terms_set_def intro: eval_term_cong)

subsection \<open>Relational Calculus Syntax and Semantics\<close>

datatype (discs_sels) ('a, 'b) fmla =
  Pred 'b "('a term) list"
| Bool bool
| Eq nat "'a term"
| Neg "('a, 'b) fmla"
| Conj "('a, 'b) fmla" "('a, 'b) fmla"
| Disj "('a, 'b) fmla" "('a, 'b) fmla"
| Exists nat "('a, 'b) fmla"

derive linorder "term"
derive linorder fmla

fun fv :: "('a, 'b) fmla \<Rightarrow> nat set" where
  "fv (Pred _ ts) = fv_terms_set ts"
| "fv (Bool b) = {}"
| "fv (Eq x t') = {x} \<union> fv_term_set t'"
| "fv (Neg \<phi>) = fv \<phi>"
| "fv (Conj \<phi> \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (Disj \<phi> \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (Exists z \<phi>) = fv \<phi> - {z}"

definition exists where "exists x Q = (if x \<in> fv Q then Exists x Q else Q)"
abbreviation "Forall x Q \<equiv> Neg (Exists x (Neg Q))"
abbreviation "forall x Q \<equiv> Neg (exists x (Neg Q))"
abbreviation "Impl Q1 Q2 \<equiv> Disj (Neg Q1) Q2"

definition "EXISTS xs Q = fold Exists xs Q"

abbreviation close where
  "close Q \<equiv> EXISTS (sorted_list_of_set (fv Q)) Q"

lemma fv_exists[simp]: "fv (exists x Q) = fv Q - {x}"
  by (auto simp: exists_def)

lemma fv_EXISTS: "fv (EXISTS xs Q) = fv Q - set xs"
  by (induct xs arbitrary: Q) (auto simp: EXISTS_def)

lemma exists_Exists: "x \<in> fv Q \<Longrightarrow> exists x Q = Exists x Q"
  by (auto simp: exists_def)

lemma is_Bool_exists[simp]: "is_Bool (exists x Q) = is_Bool Q"
  by (auto simp: exists_def is_Bool_def)

lemma finite_fv[simp]: "finite (fv \<phi>)"
  by (induction \<phi> rule: fv.induct)
     (auto simp: finite_fv_term_set finite_fv_terms_set)

lemma fv_close[simp]: "fv (close Q) = {}"
  by (subst fv_EXISTS) auto

type_synonym 'a table = "('a list) set"
type_synonym ('a, 'b) intp = "'b \<times> nat \<Rightarrow> 'a table"

definition adom :: "('a, 'b) intp \<Rightarrow> 'a set" where
  "adom I = (\<Union>rn. \<Union>xs \<in> I rn. set xs)"

fun sat :: "('a, 'b) fmla \<Rightarrow> ('a, 'b) intp \<Rightarrow> 'a val \<Rightarrow> bool" where
  "sat (Pred r ts) I \<sigma> \<longleftrightarrow> \<sigma> \<odot> ts \<in> I (r, length ts)"
| "sat (Bool b) I \<sigma> \<longleftrightarrow> b"
| "sat (Eq x t') I \<sigma> \<longleftrightarrow> \<sigma> x = \<sigma> \<cdot> t'"
| "sat (Neg \<phi>) I \<sigma> \<longleftrightarrow> \<not>sat \<phi> I \<sigma>"
| "sat (Conj \<phi> \<psi>) I \<sigma> \<longleftrightarrow> sat \<phi> I \<sigma> \<and> sat \<psi> I \<sigma>"
| "sat (Disj \<phi> \<psi>) I \<sigma> \<longleftrightarrow> sat \<phi> I \<sigma> \<or> sat \<psi> I \<sigma>"
| "sat (Exists z \<phi>) I \<sigma> \<longleftrightarrow> (\<exists>x. sat \<phi> I (\<sigma>(z := x)))"

lemma sat_fv_cong: "(\<And>n. n \<in> fv \<phi> \<Longrightarrow> \<sigma> n = \<sigma>' n) \<Longrightarrow>
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
qed (auto cong: eval_terms_cong eval_term_cong)

lemma sat_fun_upd: "n \<notin> fv Q \<Longrightarrow> sat Q I (\<sigma>(n := z)) = sat Q I \<sigma>"
  by (rule sat_fv_cong) auto

lemma sat_exists[simp]: "sat (exists n Q) I \<sigma> = (\<exists>x. sat Q I (\<sigma>(n := x)))"
  by (auto simp add: exists_def sat_fun_upd)

abbreviation eq (infix "\<approx>" 80) where
  "x \<approx> y \<equiv> Eq x (Var y)"

definition equiv (infix "\<triangleq>" 100) where
  "Q1 \<triangleq> Q2 = (\<forall>I \<sigma>. finite (adom I) \<longrightarrow> sat Q1 I \<sigma> \<longleftrightarrow> sat Q2 I \<sigma>)"

lemma equiv_refl[iff]: "Q \<triangleq> Q"
  unfolding equiv_def by auto

lemma equiv_sym[sym]: "Q1 \<triangleq> Q2 \<Longrightarrow> Q2 \<triangleq> Q1"
  unfolding equiv_def by auto

lemma equiv_trans[trans]: "Q1 \<triangleq> Q2 \<Longrightarrow> Q2 \<triangleq> Q3 \<Longrightarrow> Q1 \<triangleq> Q3"
  unfolding equiv_def by auto

lemma equiv_Neg_cong[simp]: "Q \<triangleq> Q' \<Longrightarrow> Neg Q \<triangleq> Neg Q'"
  unfolding equiv_def by auto

lemma equiv_Conj_cong[simp]: "Q1 \<triangleq> Q1' \<Longrightarrow> Q2 \<triangleq> Q2' \<Longrightarrow> Conj Q1 Q2 \<triangleq> Conj Q1' Q2'"
  unfolding equiv_def by auto

lemma equiv_Disj_cong[simp]: "Q1 \<triangleq> Q1' \<Longrightarrow> Q2 \<triangleq> Q2' \<Longrightarrow> Disj Q1 Q2 \<triangleq> Disj Q1' Q2'"
  unfolding equiv_def by auto

lemma equiv_Exists_cong[simp]: "Q \<triangleq> Q' \<Longrightarrow> Exists x Q \<triangleq> Exists x Q'"
  unfolding equiv_def by auto

lemma equiv_Exists_exists_cong[simp]: "Q \<triangleq> Q' \<Longrightarrow> Exists x Q \<triangleq> exists x Q'"
  unfolding equiv_def by auto

lemma equiv_Exists_Disj: "Exists x (Disj Q1 Q2) \<triangleq> Disj (Exists x Q1) (Exists x Q2)"
  unfolding equiv_def by auto

lemma equiv_Disj_Assoc: "Disj (Disj Q1 Q2) Q3 \<triangleq> Disj Q1 (Disj Q2 Q3)"
  unfolding equiv_def by auto

lemma foldr_Disj_equiv_cong[simp]:
  "list_all2 (\<triangleq>) xs ys \<Longrightarrow> b \<triangleq> c \<Longrightarrow> foldr Disj xs b \<triangleq> foldr Disj ys c"
  by (induct xs ys arbitrary: b c rule: list.rel_induct) auto

lemma Exists_nonfree_equiv: "x \<notin> fv Q \<Longrightarrow> Exists x Q \<triangleq> Q"
  unfolding equiv_def sat.simps
  by (metis exists_def sat_exists)

subsection \<open>Constant Propagation\<close>

fun cp where
  "cp (Eq x t) = (case t of Var y \<Rightarrow> if x = y then Bool True else x \<approx> y | _ \<Rightarrow> Eq x t)"
| "cp (Neg Q) = (let Q' = cp Q in if is_Bool Q' then Bool (\<not> un_Bool Q') else Neg Q')"
| "cp (Conj Q1 Q2) =
    (let Q1' = cp Q1; Q2' = cp Q2 in
    if is_Bool Q1' then if un_Bool Q1' then Q2' else Bool False
    else if is_Bool Q2' then if un_Bool Q2' then Q1' else Bool False
    else Conj Q1' Q2')"
| "cp (Disj Q1 Q2) =
    (let Q1' = cp Q1; Q2' = cp Q2 in
    if is_Bool Q1' then if un_Bool Q1' then Bool True else Q2'
    else if is_Bool Q2' then if un_Bool Q2' then Bool True else Q1'
    else Disj Q1' Q2')"
| "cp (Exists x Q) = exists x (cp Q)"
| "cp Q = Q"

lemma fv_cp: "fv (cp Q) \<subseteq> fv Q"
  by (induct Q) (auto simp: Let_def split: fmla.splits term.splits)

lemma cp_exists[simp]: "cp (exists x Q) = exists x (cp Q)"
  by (auto simp: exists_def fv_cp[THEN set_mp])

fun nocp where
  "nocp (Bool b) = False"
| "nocp (Pred p ts) = True"
| "nocp (Eq x t) = (t \<noteq> Var x)"
| "nocp (Neg Q) = nocp Q"
| "nocp (Conj Q1 Q2) = (nocp Q1 \<and> nocp Q2)"
| "nocp (Disj Q1 Q2) = (nocp Q1 \<and> nocp Q2)"
| "nocp (Exists x Q) = (x \<in> fv Q \<and> nocp Q)"

lemma nocp_exists[simp]: "nocp (exists x Q) = nocp Q"
  unfolding exists_def by auto

lemma nocp_cp_triv: "nocp Q \<Longrightarrow> cp Q = Q"
  by (induct Q) (auto simp: exists_def is_Bool_def split: fmla.splits term.splits)

lemma is_Bool_cp_triv: "is_Bool Q \<Longrightarrow> cp Q = Q"
  by (auto simp: is_Bool_def)

lemma nocp_cp_or_is_Bool: "nocp (cp Q) \<or> is_Bool (cp Q)"
  by (induct Q) (auto simp: Let_def split: fmla.splits term.splits)

lemma cp_idem[simp]: "cp (cp Q) = cp Q"
  using is_Bool_cp_triv nocp_cp_triv nocp_cp_or_is_Bool by blast

lemma sat_cp[simp]: "sat (cp Q) I \<sigma> = sat Q I \<sigma>"
  by (induct Q arbitrary: \<sigma>) (auto 0 0 simp: Let_def is_Bool_def split: term.splits fmla.splits)

lemma equiv_cp_cong[simp]: "Q \<triangleq> Q' \<Longrightarrow> cp Q \<triangleq> cp Q'"
  by (auto simp: equiv_def)

lemma equiv_cp[simp]: "cp Q \<triangleq> Q"
  by (auto simp: equiv_def)

definition cpropagated where "cpropagated Q = (nocp Q \<or> is_Bool Q)"

lemma cpropagated_cp[simp]: "cpropagated (cp Q)"
  by (auto simp: cpropagated_def nocp_cp_or_is_Bool)

lemma nocp_cpropagated[simp]: "nocp Q \<Longrightarrow> cpropagated Q"
  by (auto simp: cpropagated_def)

lemma cpropagated_cp_triv: "cpropagated Q \<Longrightarrow> cp Q = Q"
  by (auto simp: cpropagated_def nocp_cp_triv is_Bool_def)

lemma cpropagated_nocp: "cpropagated Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> nocp Q"
  by (auto simp: cpropagated_def is_Bool_def)

lemma cpropagated_simps[simp]:
  "cpropagated (Bool b) \<longleftrightarrow> True"
  "cpropagated (Pred p ts) \<longleftrightarrow> True"
  "cpropagated (Eq x t) \<longleftrightarrow> t \<noteq> Var x"
  "cpropagated (Neg Q) \<longleftrightarrow> nocp Q"
  "cpropagated (Conj Q1 Q2) \<longleftrightarrow> nocp Q1 \<and> nocp Q2"
  "cpropagated (Disj Q1 Q2) \<longleftrightarrow> nocp Q1 \<and> nocp Q2"
  "cpropagated (Exists x Q) \<longleftrightarrow> x \<in> fv Q \<and> nocp Q"
  by (auto simp: cpropagated_def)

subsection \<open>Big Disjunction\<close>

fun foldr1 where
  "foldr1 f (x # xs) z = foldr f xs x"
| "foldr1 f [] z = z"

definition DISJ where
  "DISJ G = foldr1 Disj (sorted_list_of_set G) (Bool False)"

lemma sat_foldr_Disj[simp]: "sat (foldr Disj xs Q) I \<sigma> = (\<exists>Q \<in> set xs \<union> {Q}. sat Q I \<sigma>)"
  by (induct xs arbitrary: Q) auto

lemma sat_foldr1_Disj[simp]: "sat (foldr1 Disj xs Q) I \<sigma> = (if xs = [] then sat Q I \<sigma> else \<exists>Q \<in> set xs. sat Q I \<sigma>)"
  by (cases xs) auto

lemma sat_DISJ[simp]: "finite G \<Longrightarrow> sat (DISJ G) I \<sigma> = (\<exists>Q \<in> G. sat Q I \<sigma>)"
  unfolding DISJ_def by auto

lemma foldr_Disj_equiv: "insert Q (set Qs) = insert Q' (set Qs') \<Longrightarrow> foldr Disj Qs Q \<triangleq> foldr Disj Qs' Q'"
  by (auto simp: equiv_def set_eq_iff)

lemma foldr1_Disj_equiv: "set Qs = set Qs' \<Longrightarrow> foldr1 Disj Qs (Bool False) \<triangleq> foldr1 Disj Qs' (Bool False)"
  by (cases Qs; cases Qs') (auto simp: foldr_Disj_equiv)

lemma foldr1_Disj_equiv_cong[simp]:
  "list_all2 (\<triangleq>) xs ys \<Longrightarrow> b \<triangleq> c \<Longrightarrow> foldr1 Disj xs b \<triangleq> foldr1 Disj ys c"
  by (erule list.rel_cases) auto

lemma Exists_foldr_Disj:
  "Exists x (foldr Disj xs b) \<triangleq> foldr Disj (map (exists x) xs) (exists x b)"
  by (auto simp: equiv_def)

lemma Exists_foldr1_Disj:
  "Exists x (foldr1 Disj xs b) \<triangleq> foldr1 Disj (map (exists x) xs) (exists x b)"
  by (auto simp: equiv_def)

lemma Exists_DISJ:
  "finite \<Q> \<Longrightarrow> Exists x (DISJ \<Q>) \<triangleq> DISJ (exists x ` \<Q>)"
  unfolding DISJ_def
  by (rule equiv_trans[OF Exists_foldr1_Disj])
    (auto simp: exists_def intro!: foldr1_Disj_equiv equiv_trans[OF _ equiv_sym[OF equiv_cp]])

lemma Exists_cp_DISJ:
  "finite \<Q> \<Longrightarrow> Exists x (cp (DISJ \<Q>)) \<triangleq> DISJ (exists x ` \<Q>)"
  by (rule equiv_trans[OF equiv_Exists_cong[OF equiv_cp] Exists_DISJ])

lemma Disj_empty[simp]: "DISJ {} = Bool False"
  unfolding DISJ_def by auto
lemma Disj_single[simp]: "DISJ {x} = x"
  unfolding DISJ_def by auto

lemma DISJ_insert[simp]: "finite X \<Longrightarrow> DISJ (insert x X) \<triangleq> Disj x (DISJ X)"
  by (induct X arbitrary: x rule: finite_induct) (auto simp: equiv_def)

lemma DISJ_union[simp]: "finite X \<Longrightarrow> finite Y \<Longrightarrow> DISJ (X \<union> Y) \<triangleq> Disj (DISJ X) (DISJ Y)"
  by (induct X rule: finite_induct)
    (auto intro!: DISJ_insert[THEN equiv_trans] simp: equiv_def)

lemma DISJ_exists_pull_out: "finite \<Q> \<Longrightarrow> Q \<in> \<Q> \<Longrightarrow>
  DISJ (exists x ` \<Q>) \<triangleq> Disj (Exists x Q) (DISJ (exists x ` (\<Q> - {Q})))"
  by (auto simp: equiv_def)

lemma DISJ_push_in: "finite \<Q> \<Longrightarrow> Disj Q (DISJ \<Q>) \<triangleq> DISJ (insert Q \<Q>)"
  by (auto simp: equiv_def)

lemma DISJ_insert_reorder: "finite \<Q> \<Longrightarrow> DISJ (insert (Disj Q1 Q2) \<Q>) \<triangleq> DISJ (insert Q2 (insert Q1 \<Q>))"
  by (auto simp: equiv_def)

lemma DISJ_insert_reorder': "finite \<Q> \<Longrightarrow> finite \<Q>' \<Longrightarrow> DISJ (insert (Disj (DISJ \<Q>') Q2) \<Q>) \<triangleq> DISJ (insert Q2 (\<Q>' \<union> \<Q>))"
  by (auto simp: equiv_def)

lemma fv_foldr_Disj[simp]: "fv (foldr Disj Qs Q) = (fv Q \<union> (\<Union>Q \<in> set Qs. fv Q))"
  by (induct Qs) auto

lemma fv_foldr1_Disj[simp]: "fv (foldr1 Disj Qs Q) = (if Qs = [] then fv Q else (\<Union>Q \<in> set Qs. fv Q))"
  by (cases Qs) auto

lemma fv_DISJ: "finite \<Q> \<Longrightarrow> fv (DISJ \<Q>) \<subseteq> (\<Union>Q \<in> \<Q>. fv Q)"
  by (auto simp: DISJ_def dest!: fv_cp[THEN set_mp] split: if_splits)

lemma fv_DISJ_close[simp]: "finite \<Q> \<Longrightarrow> fv (DISJ (close ` \<Q>)) = {}"
  by (auto dest!: fv_DISJ[THEN set_mp, rotated 1])

lemma fv_cp_foldr_Disj: "\<forall>Q\<in>set Qs \<union> {Q}. cpropagated Q \<and> fv Q = A \<Longrightarrow> fv (cp (foldr Disj Qs Q)) = A"
  by (induct Qs) (auto simp: cpropagated_cp_triv Let_def is_Bool_def)

lemma fv_cp_foldr1_Disj: "cp (foldr1 Disj Qs (Bool False)) \<noteq> Bool False \<Longrightarrow>
  \<forall>Q\<in>set Qs. cpropagated Q \<and> fv Q = A \<Longrightarrow>
  fv (cp (foldr1 Disj Qs (Bool False))) = A"
  by (cases Qs) (auto simp: fv_cp_foldr_Disj)

lemma fv_cp_DISJ_eq: "finite \<Q> \<Longrightarrow> cp (DISJ \<Q>) \<noteq> Bool False \<Longrightarrow> \<forall>Q \<in> \<Q>. cpropagated Q \<and> fv Q = A \<Longrightarrow> fv (cp (DISJ \<Q>)) = A"
  by (auto simp: DISJ_def fv_cp_foldr1_Disj)

fun sub where
  "sub (Bool t) = {Bool t}"
| "sub (Pred p ts) = {Pred p ts}"
| "sub (Eq x t) = {Eq x t}"
| "sub (Neg Q) = insert (Neg Q) (sub Q)"
| "sub (Conj Q1 Q2) = insert (Conj Q1 Q2) (sub Q1 \<union> sub Q2)"
| "sub (Disj Q1 Q2) = insert (Disj Q1 Q2) (sub Q1 \<union> sub Q2)"
| "sub (Exists z Q) = insert (Exists z Q) (sub Q)"

lemma cpropagated_sub: "cpropagated Q \<Longrightarrow> Q' \<in> sub Q \<Longrightarrow> cpropagated Q'"
  by (induct Q) auto

lemma Exists_in_sub_cp_foldr_Disj:
  "Exists x Q' \<in> sub (cp (foldr Disj Qs Q)) \<Longrightarrow> Exists x Q' \<in> sub (cp Q) \<or> (\<exists>Q \<in> set Qs. Exists x Q' \<in> sub (cp Q))"
  by (induct Qs arbitrary: Q) (auto simp: Let_def split: if_splits)

lemma Exists_in_sub_cp_foldr1_Disj:
  "Exists x Q' \<in> sub (cp (foldr1 Disj Qs Q)) \<Longrightarrow> Qs = [] \<and> Exists x Q' \<in> sub (cp Q) \<or> (\<exists>Q \<in> set Qs. Exists x Q' \<in> sub (cp Q))"
  by (cases Qs) (auto simp: Exists_in_sub_cp_foldr_Disj)

lemma Exists_in_sub_cp_DISJ: "Exists x Q' \<in> sub (cp (DISJ \<Q>)) \<Longrightarrow> finite \<Q> \<Longrightarrow> (\<exists>Q \<in> \<Q>. Exists x Q' \<in> sub (cp Q))"
  unfolding DISJ_def by (drule Exists_in_sub_cp_foldr1_Disj) auto

lemma Exists_in_sub_foldr_Disj:
  "Exists x Q' \<in> sub (foldr Disj Qs Q) \<Longrightarrow> Exists x Q' \<in> sub Q \<or> (\<exists>Q \<in> set Qs. Exists x Q' \<in> sub Q)"
  by (induct Qs arbitrary: Q) (auto simp: Let_def split: if_splits)

lemma Exists_in_sub_foldr1_Disj:
  "Exists x Q' \<in> sub (foldr1 Disj Qs Q) \<Longrightarrow> Qs = [] \<and> Exists x Q' \<in> sub Q \<or> (\<exists>Q \<in> set Qs. Exists x Q' \<in> sub Q)"
  by (cases Qs) (auto simp: Exists_in_sub_foldr_Disj)

lemma Exists_in_sub_DISJ: "Exists x Q' \<in> sub (DISJ \<Q>) \<Longrightarrow> finite \<Q> \<Longrightarrow> (\<exists>Q \<in> \<Q>. Exists x Q' \<in> sub Q)"
  unfolding DISJ_def by (drule Exists_in_sub_foldr1_Disj) auto

subsection \<open>Substitution\<close>

fun subst_term ("_[_ \<^bold>\<rightarrow>t _]" [90, 0, 0] 91) where
  "Var z[x \<^bold>\<rightarrow>t y] = Var (if x = z then y else z)"
| "Const c[x \<^bold>\<rightarrow>t y] = Const c"

abbreviation substs_term ("_[_ \<^bold>\<rightarrow>t\<^sup>* _]" [90, 0, 0] 91) where
  "t[xs \<^bold>\<rightarrow>t\<^sup>* ys] \<equiv> fold (\<lambda>(x, y) t. t[x \<^bold>\<rightarrow>t y]) (zip xs ys) t"

lemma size_subst_term[simp]: "size (t[x \<^bold>\<rightarrow>t y]) = size t"
  by (cases t) auto

lemma fv_subst_term[simp]: "fv_term_set (t[x \<^bold>\<rightarrow>t y]) =
  (if x \<in> fv_term_set t then insert y (fv_term_set t - {x}) else fv_term_set t)"
  by (cases t) auto

definition "fresh2 x y Q = Suc (Max (insert x (insert y (fv Q))))"

function (sequential) subst :: "('a, 'b) fmla \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) fmla" ("_[_ \<^bold>\<rightarrow> _]" [90, 0, 0] 91) where
  "Bool t[x \<^bold>\<rightarrow> y] = Bool t"
| "Pred p ts[x \<^bold>\<rightarrow> y] = Pred p (map (\<lambda>t. t[x \<^bold>\<rightarrow>t y]) ts)"
| "Eq z t[x \<^bold>\<rightarrow> y] = Eq (if z = x then y else z) (t[x \<^bold>\<rightarrow>t y])"
| "Neg Q[x \<^bold>\<rightarrow> y] = Neg (Q[x \<^bold>\<rightarrow> y])"
| "Conj Q1 Q2[x \<^bold>\<rightarrow> y] = Conj (Q1[x \<^bold>\<rightarrow> y]) (Q2[x \<^bold>\<rightarrow> y])"
| "Disj Q1 Q2[x \<^bold>\<rightarrow> y] = Disj (Q1[x \<^bold>\<rightarrow> y]) (Q2[x \<^bold>\<rightarrow> y])"
| "Exists z Q[x \<^bold>\<rightarrow> y] = (if x = z then Exists x Q else
    if z = y then let z' = fresh2 x y Q in Exists z' (Q[z \<^bold>\<rightarrow> z'][x \<^bold>\<rightarrow> y]) else Exists z (Q[x \<^bold>\<rightarrow> y]))"
  by pat_completeness auto

abbreviation substs ("_[_ \<^bold>\<rightarrow>\<^sup>* _]" [90, 0, 0] 91) where
  "Q[xs \<^bold>\<rightarrow>\<^sup>* ys] \<equiv> fold (\<lambda>(x, y) Q. Q[x \<^bold>\<rightarrow> y]) (zip xs ys) Q"

lemma size_subst_p[simp]: "subst_dom (Q, x, y) \<Longrightarrow> size (Q[x \<^bold>\<rightarrow> y]) = size Q"
  by (induct Q x y rule: subst.pinduct) (auto simp: subst.psimps o_def Let_def exists_def)

termination by lexicographic_order

lemma size_subst[simp]: "size (Q[x \<^bold>\<rightarrow> y]) = size Q"
  by (induct Q x y rule: subst.induct) (auto simp: o_def Let_def exists_def)

lemma fresh2_gt:
  "x < fresh2 x y Q"
  "y < fresh2 x y Q"
  "z \<in> fv Q \<Longrightarrow> z < fresh2 x y Q"
  unfolding fresh2_def less_Suc_eq_le
  by (auto simp: max_def Max_ge_iff)

lemma fresh2:
  "x \<noteq> fresh2 x y Q"
  "y \<noteq> fresh2 x y Q"
  "fresh2 x y Q \<notin> fv Q"
  using fresh2_gt(1)[of x y Q] fresh2_gt(2)[of y x Q] fresh2_gt(3)[of "fresh2 x y Q" Q x y]
  by auto

lemma fv_subst:
  "fv (Q[x \<^bold>\<rightarrow> y]) = (if x \<in> fv Q then insert y (fv Q - {x}) else fv Q)"
  by (induct Q x y rule: subst.induct)
    (auto simp:  fv_terms_set_def Let_def fresh2 split: if_splits)

lemma subst_term_triv: "x \<notin> fv_term_set t \<Longrightarrow> t[x \<^bold>\<rightarrow>t y] = t"
  by (cases t) auto

lemma subst_exists: "exists z Q[x \<^bold>\<rightarrow> y] = (if z \<in> fv Q then if x = z then exists x Q else
    if z = y then let z' = fresh2 x y Q in exists z' (Q[z \<^bold>\<rightarrow> z'][x \<^bold>\<rightarrow> y]) else exists z (Q[x \<^bold>\<rightarrow> y]) else Q[x \<^bold>\<rightarrow> y])"
  by (auto simp: exists_def Let_def fv_subst fresh2 dest: sym)

lemma eval_subst[simp]: "\<sigma> \<cdot> t[x \<^bold>\<rightarrow>t y] = \<sigma>(x := \<sigma> y) \<cdot> t"
  by (cases t) auto

lemma sat_subst[simp]: "sat (Q[x \<^bold>\<rightarrow> y]) I \<sigma> = sat Q I (\<sigma>(x := \<sigma> y))"
  by (induct Q x y arbitrary: \<sigma> rule: subst.induct)
    (auto 0 3 simp: eval_terms_def o_def Let_def fun_upd_twist[symmetric] sat_fun_upd fresh2 dest: sym)

lemma substs_Bool[simp]: "length xs = length ys \<Longrightarrow> Bool b[xs \<^bold>\<rightarrow>\<^sup>* ys] = Bool b"
  by (induct xs ys rule: list_induct2) auto

lemma substs_Neg[simp]: "length xs = length ys \<Longrightarrow> Neg Q[xs \<^bold>\<rightarrow>\<^sup>* ys] = Neg (Q[xs \<^bold>\<rightarrow>\<^sup>* ys])"
  by (induct xs ys arbitrary: Q rule: list_induct2) (auto simp: Let_def)

lemma substs_Conj[simp]: "length xs = length ys \<Longrightarrow> Conj Q1 Q2[xs \<^bold>\<rightarrow>\<^sup>* ys] = Conj (Q1[xs \<^bold>\<rightarrow>\<^sup>* ys]) (Q2[xs \<^bold>\<rightarrow>\<^sup>* ys])"
  by (induct xs ys arbitrary: Q1 Q2 rule: list_induct2) auto

lemma substs_Disj[simp]: "length xs = length ys \<Longrightarrow> Disj Q1 Q2[xs \<^bold>\<rightarrow>\<^sup>* ys] = Disj (Q1[xs \<^bold>\<rightarrow>\<^sup>* ys]) (Q2[xs \<^bold>\<rightarrow>\<^sup>* ys])"
  by (induct xs ys arbitrary: Q1 Q2 rule: list_induct2) auto

fun substs_bd where
  "substs_bd z (x # xs) (y # ys) Q = (if x = z then substs_bd z xs ys Q else
     if z = y then substs_bd (fresh2 x y Q) xs ys (Q[y \<^bold>\<rightarrow> fresh2 x y Q][x \<^bold>\<rightarrow> y]) else substs_bd z xs ys (Q[x \<^bold>\<rightarrow> y]))"
| "substs_bd z _ _ _ = z"

fun substs_src where
  "substs_src z (x # xs) (y # ys) Q = (if x = z then substs_src z xs ys Q else
     if z = y then [y, x] @ substs_src (fresh2 x y Q) xs ys (Q[y \<^bold>\<rightarrow> fresh2 x y Q][x \<^bold>\<rightarrow> y]) else x # substs_src z xs ys (Q[x \<^bold>\<rightarrow> y]))"
| "substs_src _ _ _ _ = []"

fun substs_dst where
  "substs_dst z (x # xs) (y # ys) Q = (if x = z then substs_dst z xs ys Q else
     if z = y then [fresh2 x y Q, y] @ substs_dst (fresh2 x y Q) xs ys (Q[y \<^bold>\<rightarrow> fresh2 x y Q][x \<^bold>\<rightarrow> y]) else y # substs_dst z xs ys (Q[x \<^bold>\<rightarrow> y]))"
| "substs_dst _ _ _ _ = []"

lemma length_substs[simp]: "length xs = length ys \<Longrightarrow> length (substs_src z xs ys Q) = length (substs_dst z xs ys Q)"
  by (induct xs ys arbitrary: z Q rule: list_induct2) auto

lemma substs_Exists[simp]: "length xs = length ys \<Longrightarrow>
  Exists z Q[xs \<^bold>\<rightarrow>\<^sup>* ys] = Exists (substs_bd z xs ys Q) (Q[substs_src z xs ys Q \<^bold>\<rightarrow>\<^sup>* substs_dst z xs ys Q])"
  by (induct xs ys arbitrary: Q z rule: list_induct2) (auto simp: Let_def intro: exI[of _ "[]"])

fun subst_var where
  "subst_var (x # xs) (y # ys) z = (if x = z then subst_var xs ys y else subst_var xs ys z)"
| "subst_var _ _ z = z"

lemma substs_Eq[simp]: "length xs = length ys \<Longrightarrow> (Eq x t)[xs \<^bold>\<rightarrow>\<^sup>* ys] = Eq (subst_var xs ys x) (t[xs \<^bold>\<rightarrow>t\<^sup>* ys])"
  by (induct xs ys arbitrary: x t rule: list_induct2) auto

lemma substs_term_Var[simp]: "length xs = length ys \<Longrightarrow> (Var x)[xs \<^bold>\<rightarrow>t\<^sup>* ys] = Var (subst_var xs ys x)"
  by (induct xs ys arbitrary: x rule: list_induct2) auto

lemma substs_term_Const[simp]: "length xs = length ys \<Longrightarrow> (Const c)[xs \<^bold>\<rightarrow>t\<^sup>* ys] = Const c"
  by (induct xs ys rule: list_induct2) auto

lemma in_fv_substs:
  "length xs = length ys \<Longrightarrow> x \<in> fv Q \<Longrightarrow> subst_var xs ys x \<in> fv (Q[xs \<^bold>\<rightarrow>\<^sup>* ys])"
  by (induct xs ys arbitrary: x Q rule: list_induct2) (auto simp: fv_subst)

lemma exists_cp_subst: "x \<noteq> y \<Longrightarrow> exists x (cp (Q[x \<^bold>\<rightarrow> y])) = cp (Q[x \<^bold>\<rightarrow> y])"
  by (auto simp: exists_def fv_subst dest!: set_mp[OF fv_cp] split: if_splits)

subsection \<open>Generated Variables\<close>

inductive ap where
  Pred: "ap (Pred p ts)"
| Eqc: "ap (Eq x (Const c))"

inductive gen where
  "gen x (Bool False) {}"
| "ap Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> gen x Q {Q}"
| "gen x Q G \<Longrightarrow> gen x (Neg (Neg Q)) G"
| "gen x (Conj (Neg Q1) (Neg Q2)) G \<Longrightarrow> gen x (Neg (Disj Q1 Q2)) G"
| "gen x (Disj (Neg Q1) (Neg Q2)) G \<Longrightarrow> gen x (Neg (Conj Q1 Q2)) G"
| "gen x Q1 G1 \<Longrightarrow> gen x Q2 G2 \<Longrightarrow> gen x (Disj Q1 Q2) (G1 \<union> G2)"
| "gen x Q1 G \<or> gen x Q2 G \<Longrightarrow> gen x (Conj Q1 Q2) G"
| "gen y Q G \<Longrightarrow> gen x (Conj Q (x \<approx> y)) ((\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` G)"
| "gen y Q G \<Longrightarrow> gen x (Conj Q (y \<approx> x)) ((\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` G)"
| "x \<noteq> y \<Longrightarrow> gen x Q G \<Longrightarrow>  gen x (Exists y Q) (exists y ` G)"

inductive gen' where
  "gen' x (Bool False) {}"
| "ap Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> gen' x Q {Q}"
| "gen' x Q G \<Longrightarrow> gen' x (Neg (Neg Q)) G"
| "gen' x (Conj (Neg Q1) (Neg Q2)) G \<Longrightarrow> gen' x (Neg (Disj Q1 Q2)) G"
| "gen' x (Disj (Neg Q1) (Neg Q2)) G \<Longrightarrow> gen' x (Neg (Conj Q1 Q2)) G"
| "gen' x Q1 G1 \<Longrightarrow> gen' x Q2 G2 \<Longrightarrow> gen' x (Disj Q1 Q2) (G1 \<union> G2)"
| "gen' x Q1 G \<or> gen' x Q2 G \<Longrightarrow> gen' x (Conj Q1 Q2) G"
| "gen' y Q G \<Longrightarrow> gen' x (Conj Q (x \<approx> y)) ((\<lambda>Q. Q[y \<^bold>\<rightarrow> x]) ` G)"
| "gen' y Q G \<Longrightarrow> gen' x (Conj Q (y \<approx> x)) ((\<lambda>Q. Q[y \<^bold>\<rightarrow> x]) ` G)"
| "x \<noteq> y \<Longrightarrow> gen' x Q G \<Longrightarrow>  gen' x (Exists y Q) (exists y ` G)"

inductive qp where
  ap: "ap Q \<Longrightarrow> qp Q"
| exists: "qp Q \<Longrightarrow> qp (exists x Q)"

lemma qp_Exists: "qp Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> qp (Exists x Q)"
  by (metis qp.exists exists_def)

lemma qp_ExistsE: "qp (Exists x Q) \<Longrightarrow> (qp Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> R) \<Longrightarrow> R"
  by (induct "Exists x Q" rule: qp.induct) (auto elim!: ap.cases simp: exists_def split: if_splits)

fun qp_impl where
  "qp_impl (Eq x (Const c)) = True"
| "qp_impl (Pred x ts) = True"
| "qp_impl (Exists x Q) = (x \<in> fv Q \<and> qp Q)"
| "qp_impl _ = False"

lemma qp_imp_qp_impl: "qp Q \<Longrightarrow> qp_impl Q"
  by (induct Q rule: qp.induct) (auto elim!: ap.cases simp: exists_def)

lemma qp_impl_imp_qp: "qp_impl Q \<Longrightarrow> qp Q"
  by (induct Q rule: qp_impl.induct) (auto intro: ap.intros qp_Exists qp.ap)

lemma qp_code[code]: "qp Q = qp_impl Q"
  using qp_imp_qp_impl qp_impl_imp_qp by blast

lemma ap_cp: "ap Q \<Longrightarrow> ap (cp Q)"
  by (induct Q rule: ap.induct) (auto intro: ap.intros)

lemma qp_cp: "qp Q \<Longrightarrow> qp (cp Q)"
  by (induct Q rule: qp.induct) (auto intro: qp.intros ap_cp)

lemma ap_substs: "ap Q \<Longrightarrow> length xs = length ys \<Longrightarrow> ap (Q[xs \<^bold>\<rightarrow>\<^sup>* ys])"
proof (induct Q arbitrary: xs ys rule: ap.induct)
  case (Pred p ts)
  then show ?case
    by (induct xs ys arbitrary: ts rule: list_induct2) (auto intro!: ap.intros)
next
  case (Eqc x c)
  then show ?case
    by (induct xs ys arbitrary: x rule: list_induct2) (auto intro!: ap.intros)
qed

lemma ap_subst': "ap (Q[x \<^bold>\<rightarrow> y]) \<Longrightarrow> ap Q"
proof (induct "Q[x \<^bold>\<rightarrow> y]" arbitrary: Q rule: ap.induct)
  case (Pred p ts)
  then show ?case
    by (cases Q) (auto simp: Let_def split: if_splits intro: ap.intros)
next
  case (Eqc x c)
  then show ?case
  proof (cases Q)
    case (Eq x t)
    with Eqc show ?thesis
      by (cases t) (auto intro: ap.intros)
  qed (auto simp: Let_def split: if_splits)
qed

lemma qp_substs: "qp Q \<Longrightarrow> length xs = length ys \<Longrightarrow> qp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys])"
proof (induct Q arbitrary: xs ys rule: qp.induct)
  case (ap Q)
  then show ?case
    by (rule qp.ap[OF ap_substs])
next
  case (exists Q z)
  from exists(3,1,2) show ?case
  proof (induct xs ys arbitrary: Q z rule: list_induct2)
    case Nil
    then show ?case
      by (auto intro: qp.intros)
  next
    case (Cons x xs y ys)
    have [simp]: "Q[x \<^bold>\<rightarrow> y][xs \<^bold>\<rightarrow>\<^sup>* ys] = Q[x # xs \<^bold>\<rightarrow>\<^sup>* y # ys]" for Q :: "('a, 'b) fmla" and x y xs ys
      by auto
    have IH1[simp]: "qp (Q[x \<^bold>\<rightarrow> y])" for x y
      using Cons(4)[of "[x]" "[y]"] by auto
    have IH2[simp]: "qp (Q[x \<^bold>\<rightarrow> y][a \<^bold>\<rightarrow> b])" for x y a b
      using Cons(4)[of "[x, a]" "[y, b]"] by auto
    note zip_Cons_Cons[simp del]
    show ?case
      unfolding zip_Cons_Cons fold.simps prod.case o_apply subst_exists using Cons(1,3)
      by (auto simp: Let_def intro!: qp.intros(2) Cons(2,4))
  qed
qed

lemma qp_subst: "qp Q \<Longrightarrow> qp (Q[x \<^bold>\<rightarrow> y])"
  using qp_substs[of Q "[x]" "[y]"] by auto

lemma qp_Neg[dest]: "qp (Neg Q) \<Longrightarrow> False"
  by (rule qp.induct[where P = "\<lambda>Q'. Q' = Neg Q \<longrightarrow> False", THEN mp]) (auto elim!: ap.cases simp: exists_def)

lemma qp_Disj[dest]: "qp (Disj Q1 Q2) \<Longrightarrow> False"
  by (rule qp.induct[where P = "\<lambda>Q. Q = Disj Q1 Q2 \<longrightarrow> False", THEN mp]) (auto elim!: ap.cases simp: exists_def)

lemma qp_Conj[dest]: "qp (Conj Q1 Q2) \<Longrightarrow> False"
  by (rule qp.induct[where P = "\<lambda>Q. Q = Conj Q1 Q2 \<longrightarrow> False", THEN mp]) (auto elim!: ap.cases simp: exists_def)

lemma qp_eq[dest]: "qp (x \<approx> y) \<Longrightarrow> False"
  by (rule qp.induct[where P = "\<lambda>Q. (\<exists>x y. Q = x \<approx> y) \<longrightarrow> False", THEN mp]) (auto elim!: ap.cases simp: exists_def)

lemma qp_subst': "qp (Q[x \<^bold>\<rightarrow> y]) \<Longrightarrow> qp Q"
proof (induct Q x y rule: subst.induct)
  case (3 z t x y)
  then show ?case
    by (cases t) (auto intro!: ap Eqc split: if_splits)
qed (auto 0 3 simp: qp_Exists fv_subst Let_def fresh2 Pred ap dest: sym elim!: qp_ExistsE split: if_splits)

lemma qp_subst_eq[simp]: "qp (Q[x \<^bold>\<rightarrow> y]) = qp Q"
  using qp_subst qp_subst' by blast

lemma gen_qp: "gen x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> qp Qqp"
  by (induct x Q G arbitrary: Qqp rule: gen.induct) (auto intro: qp.intros ap.intros qp_cp)

lemma gen'_qp: "gen' x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> qp Qqp"
  by (induct x Q G arbitrary: Qqp rule: gen'.induct) (auto intro: qp.intros ap.intros)

lemma ap_cp_triv: "ap Q \<Longrightarrow> cp Q = Q"
  by (induct Q rule: ap.induct) auto

lemma qp_cp_triv: "qp Q \<Longrightarrow> cp Q = Q"
  by (induct Q rule: qp.induct) (auto simp: ap_cp_triv)

lemma ap_cp_subst_triv: "ap Q \<Longrightarrow> cp (Q[x \<^bold>\<rightarrow> y]) = Q[x \<^bold>\<rightarrow> y]"
  by (induct Q rule: ap.induct) auto

lemma qp_cp_subst_triv: "qp Q \<Longrightarrow> cp (Q[x \<^bold>\<rightarrow> y]) = Q[x \<^bold>\<rightarrow> y]"
  by (induct Q rule: qp.induct)
    (auto simp: exists_def qp_cp_triv Let_def fv_subst fresh2 ap_cp_subst_triv dest: sym)

lemma gen_nocp_intros:
  "gen y Q G \<Longrightarrow> gen x (Conj Q (x \<approx> y)) ((\<lambda>Q. Q[y \<^bold>\<rightarrow> x]) ` G)"
  "gen y Q G \<Longrightarrow> gen x (Conj Q (y \<approx> x)) ((\<lambda>Q. Q[y \<^bold>\<rightarrow> x]) ` G)"
  by (metis (no_types, lifting) gen.intros(8) gen_qp image_cong qp_cp_subst_triv,
      metis (no_types, lifting) gen.intros(9) gen_qp image_cong qp_cp_subst_triv)

lemma gen'_cp_intros:
  "gen' y Q G \<Longrightarrow> gen' x (Conj Q (x \<approx> y)) ((\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` G)"
  "gen' y Q G \<Longrightarrow> gen' x (Conj Q (y \<approx> x)) ((\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` G)"
  by (metis (no_types, lifting) gen'.intros(8) gen'_qp image_cong qp_cp_subst_triv,
      metis (no_types, lifting) gen'.intros(9) gen'_qp image_cong qp_cp_subst_triv)

lemma gen'_gen: "gen' x Q G \<Longrightarrow> gen x Q G"
  by (induct x Q G rule: gen'.induct) (auto intro!: gen.intros gen_nocp_intros)

lemma gen_gen': "gen x Q G \<Longrightarrow> gen' x Q G"
  by (induct x Q G rule: gen.induct) (auto intro!: gen'.intros gen'_cp_intros)

lemma gen_eq_gen': "gen = gen'"
  using gen'_gen gen_gen' by blast

lemmas gen_induct[consumes 1] = gen'.induct[folded gen_eq_gen']

abbreviation Gen where "Gen x Q \<equiv> (\<exists>G. gen x Q G)"

lemma qp_Gen: "qp Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> Gen x Q"
  by (induct Q rule: qp.induct) (force simp: exists_def intro: gen.intros)+

lemma qp_gen: "qp Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> gen x Q {Q}"
  by (induct Q rule: qp.induct)
    (force simp: exists_def intro: gen.intros dest: gen.intros(10))+

lemma gen_foldr_Disj:
  "list_all2 (gen x) Qs Gs \<Longrightarrow> gen x Q G \<Longrightarrow> GG = G \<union> (\<Union>G \<in> set Gs. G) \<Longrightarrow>
  gen x (foldr Disj Qs Q) GG"
proof (induct Qs Gs arbitrary: Q G GG rule: list.rel_induct)
  case (Cons Q' Qs G' Gs)
  then have GG: "GG = G' \<union> (G \<union> (\<Union>G \<in> set Gs. G))"
    by auto
  from Cons(1,3-) show ?case
    unfolding foldr.simps o_apply GG
    by (intro gen.intros Cons(2)[OF _ refl]) auto
qed simp

lemma gen_foldr1_Disj:
  "list_all2 (gen x) Qs Gs \<Longrightarrow> gen x Q G \<Longrightarrow> GG = (if Qs = [] then G else (\<Union>G \<in> set Gs. G)) \<Longrightarrow>
  gen x (foldr1 Disj Qs Q) GG"
  by (erule list.rel_cases) (auto simp: gen_foldr_Disj)

lemma gen_Bool_True[simp]: "gen x (Bool True) G = False"
  by (auto elim: gen.cases)

lemma gen_Bool_False[simp]: "gen x (Bool False) G = (G = {})"
  by (auto elim: gen.cases intro: gen.intros)

lemma gen_Gen_cp: "gen x Q G \<Longrightarrow> Gen x (cp Q)"
  by (induct x Q G rule: gen_induct)
    (auto split: if_splits simp: Let_def ap_cp_triv is_Bool_def exists_def intro: gen.intros)

lemma Gen_cp: "Gen x Q \<Longrightarrow> Gen x (cp Q)"
  by (metis gen_Gen_cp)

lemma Gen_DISJ: "finite \<Q> \<Longrightarrow> \<forall>Q \<in> \<Q>. qp Q \<and> x \<in> fv Q \<Longrightarrow> Gen x (DISJ \<Q>)"
  unfolding DISJ_def
  by (rule exI gen_foldr1_Disj[where Gs="map (\<lambda>Q. {Q}) (sorted_list_of_set \<Q>)" and G="{}"])+
    (auto simp: list.rel_map qp_cp_triv qp_gen gen.intros intro!: list.rel_refl_strong)

lemma Gen_cp_DISJ: "finite \<Q> \<Longrightarrow> \<forall>Q \<in> \<Q>. qp Q \<and> x \<in> fv Q \<Longrightarrow> Gen x (cp (DISJ \<Q>))"
  by (rule Gen_cp Gen_DISJ)+

lemma gen_Pred[simp]:
  "gen z (Pred p ts) G \<longleftrightarrow> z \<in> fv_terms_set ts \<and> G = {Pred p ts}"
  by (auto elim: gen.cases intro: gen.intros ap.intros)

lemma gen_Eq[simp]:
  "gen z (Eq a t) G \<longleftrightarrow> z = a \<and> (\<exists>c. t = Const c \<and> G = {Eq a t})"
  by (auto elim: gen.cases elim!: ap.cases intro: gen.intros ap.intros)

lemma gen_empty_cp: "gen z Q G \<Longrightarrow> G = {} \<Longrightarrow> cp Q = Bool False"
  by (induct z Q G rule: gen_induct)
    (fastforce simp: Let_def exists_def split: if_splits)+

inductive genempty where
  "genempty (Bool False)"
| "genempty Q \<Longrightarrow> genempty (Neg (Neg Q))"
| "genempty (Conj (Neg Q1) (Neg Q2)) \<Longrightarrow> genempty (Neg (Disj Q1 Q2))"
| "genempty (Disj (Neg Q1) (Neg Q2)) \<Longrightarrow> genempty (Neg (Conj Q1 Q2))"
| "genempty Q1 \<Longrightarrow> genempty Q2 \<Longrightarrow> genempty (Disj Q1 Q2)"
| "genempty Q1 \<or> genempty Q2 \<Longrightarrow> genempty (Conj Q1 Q2)"
| "genempty Q \<Longrightarrow> genempty (Conj Q (x \<approx> y))"
| "genempty Q \<Longrightarrow> genempty (Conj Q (y \<approx> x))"
| "genempty Q \<Longrightarrow> genempty (Exists y Q)"

lemma gen_genempty: "gen z Q G \<Longrightarrow> G = {} \<Longrightarrow> genempty Q"
  by (induct z Q G rule: gen.induct) (auto intro: genempty.intros)

lemma genempty_substs: "genempty Q \<Longrightarrow> length xs = length ys \<Longrightarrow> genempty (Q[xs \<^bold>\<rightarrow>\<^sup>* ys])"
  by (induct Q arbitrary: xs ys rule: genempty.induct) (auto intro: genempty.intros)

lemma genempty_substs_Exists: "genempty Q \<Longrightarrow> length xs = length ys \<Longrightarrow> genempty (Exists y Q[xs \<^bold>\<rightarrow>\<^sup>* ys])"
  by (auto intro!: genempty.intros genempty_substs)

lemma genempty_cp: "genempty Q \<Longrightarrow> cp Q = Bool False"
  by (induct Q rule: genempty.induct)
    (auto simp: Let_def exists_def split: if_splits)

lemma gen_empty_cp_substs:
  "gen x Q {} \<Longrightarrow> length xs = length ys \<Longrightarrow> cp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys]) = Bool False"
  by (rule genempty_cp[OF genempty_substs[OF gen_genempty[OF _ refl]]])

lemma gen_empty_cp_substs_Exists:
  "gen x Q {} \<Longrightarrow> length xs = length ys \<Longrightarrow> cp (Exists y Q[xs \<^bold>\<rightarrow>\<^sup>* ys]) = Bool False"
  by (rule genempty_cp[OF genempty_substs_Exists[OF gen_genempty[OF _ refl]]])

lemma gen_Gen_substs_Exists:
  "length xs = length ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> fv Q \<Longrightarrow>
   (\<And>xs ys. length xs = length ys \<Longrightarrow> Gen (subst_var xs ys x) (cp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys]))) \<Longrightarrow>
   Gen (subst_var xs ys x) (cp (Exists y Q[xs \<^bold>\<rightarrow>\<^sup>* ys]))"
proof (induct xs ys arbitrary: y x Q rule: list_induct2)
  case Nil
  from Nil(1) Nil(3)[of "[]" "[]"] show ?case
    by (auto simp: exists_def intro: gen.intros)
next
  case (Cons xx xs yy ys)
  have "Gen (subst_var xs ys yy) (cp (Q[[y,x]@xs \<^bold>\<rightarrow>\<^sup>* [fresh2 x y Q,yy]@ys]))"
    if "length xs = length ys" and "x \<noteq> y" for xs ys
    using Cons(5)[of "[y,x]@xs" "[fresh2 x y Q,yy]@ys"] that Cons.prems by auto
  moreover have "Gen (subst_var xs ys x) (cp (Q[[yy,xx]@xs \<^bold>\<rightarrow>\<^sup>* [fresh2 xx yy Q,yy]@ys]))"
    if "length xs = length ys" "x \<noteq> yy" "x \<noteq> xx" for xs ys
    using Cons(5)[of "[yy,xx]@xs" "[fresh2 xx yy Q,yy]@ys"] that Cons.prems by auto
  moreover have "Gen (subst_var xs ys yy) (cp (Q[[x]@xs \<^bold>\<rightarrow>\<^sup>* [yy]@ys]))"
    if "length xs = length ys" and "x = xx" for xs ys
    using Cons(5)[of "[x]@xs" "[yy]@ys"] that Cons.prems by auto
  moreover have "Gen (subst_var xs ys x) (cp (Q[[xx]@xs \<^bold>\<rightarrow>\<^sup>* [yy]@ys]))"
    if "length xs = length ys" and "x \<noteq> xx" for xs ys
    using Cons(5)[of "[xx]@xs" "[yy]@ys"] that Cons.prems by auto
  ultimately show ?case using Cons
    by (auto simp: Let_def fresh2 fv_subst intro: Cons(2) simp del: substs_Exists split: if_splits)
qed

lemma gen_fv:
  "gen x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> x \<in> fv Qqp \<and> fv Qqp \<subseteq> fv Q"
  by (induct x Q G arbitrary: Qqp rule: gen_induct)
    (force simp: fv_subst dest: fv_cp[THEN set_mp])+

lemma gen_sat:
  fixes x :: nat
  shows "gen x Q G \<Longrightarrow> sat Q I \<sigma> \<Longrightarrow> \<exists>Qqp \<in> G. sat Qqp I \<sigma>"
  by (induct x Q G arbitrary: \<sigma> rule: gen_induct)
    (auto 6 0 simp: fun_upd_idem intro: UnI1 UnI2)

subsection \<open>Variable Erasure\<close>

fun erase :: "('a, 'b) fmla \<Rightarrow> nat \<Rightarrow> ('a, 'b) fmla" (infix "\<^bold>\<bottom>" 65) where
  "Bool t \<^bold>\<bottom> x = Bool t"
| "Pred p ts \<^bold>\<bottom> x = (if x \<in> fv_terms_set ts then Bool False else Pred p ts)"
| "Eq z t \<^bold>\<bottom> x = (if t = Var z then Bool True else
     if x = z \<or> x \<in> fv_term_set t then Bool False else Eq z t)"
| "Neg Q \<^bold>\<bottom> x = Neg (Q \<^bold>\<bottom> x)"
| "Conj Q1 Q2 \<^bold>\<bottom> x = Conj (Q1 \<^bold>\<bottom> x) (Q2 \<^bold>\<bottom> x)"
| "Disj Q1 Q2 \<^bold>\<bottom> x = Disj (Q1 \<^bold>\<bottom> x) (Q2 \<^bold>\<bottom> x)"
| "Exists z Q \<^bold>\<bottom> x = (if x = z then Exists x Q else Exists z (Q \<^bold>\<bottom> x))"

lemma fv_erase: "fv (Q \<^bold>\<bottom> x) \<subseteq> fv Q - {x}"
  by (induct Q) auto

lemma ap_cp_erase: "ap Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> cp (Q \<^bold>\<bottom> x) = Bool False"
  by (induct Q rule: ap.induct) auto

lemma qp_cp_erase: "qp Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> cp (Q \<^bold>\<bottom> x) = Bool False"
  by (induct Q rule: qp.induct) (auto simp: exists_def ap_cp_erase split: if_splits)

lemma sat_erase: "sat (Q \<^bold>\<bottom> x) I (\<sigma>(x := z)) = sat (Q \<^bold>\<bottom> x) I \<sigma>"
  by (rule sat_fun_upd) (auto dest: fv_erase[THEN set_mp])

lemma exists_cp_erase: "exists x (cp (Q \<^bold>\<bottom> x)) = cp (Q \<^bold>\<bottom> x)"
  by (auto simp: exists_def dest: set_mp[OF fv_cp] set_mp[OF fv_erase])

lemma gen_cp_erase:
  fixes x :: nat
  shows "gen x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> cp (Qqp \<^bold>\<bottom> x) = Bool False"
  by (metis gen_qp qp_cp_erase gen_fv)

subsection \<open>Generated Variables and Substitutions\<close>

lemma gen_Gen_cp_substs: "gen z Q G \<Longrightarrow> length xs = length ys \<Longrightarrow>
  Gen (subst_var xs ys z) (cp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys]))"
proof (induct z Q G arbitrary: xs ys rule: gen_induct)
  case (2 Q x)
  show ?case
    by (subst ap_cp_triv) (rule exI gen.intros(2) ap_substs 2 in_fv_substs)+
next
  case (3 x Q G)
  then show ?case
    by (fastforce simp: Let_def intro: gen.intros)
next
  case (4 x Q1 Q2 G)
  from 4(2)[of xs ys] 4(1,3) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(4) split: if_splits)
next
  case (5 x Q1 Q2 G)
  from 5(2)[of xs ys] 5(1,3) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(5) split: if_splits)
next
  case (6 x Q1 G1 Q2 G2)
  from 6(2,4)[of xs ys] 6(1,3,5) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(6) split: if_splits)
next
  case (7 x Q1 G Q2)
  from 7(1) show ?case
  proof (elim disjE conjE, goal_cases L R)
    case L
    from L(1) L(2)[rule_format, of xs ys] 7(2) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(7) split: if_splits)
  next
    case R
    from R(1) R(2)[rule_format, of xs ys] 7(2) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(7) split: if_splits)
  qed
next
  case (8 y Q G x)
  from 8(2)[of xs ys] 8(1,3) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(8) split: if_splits)
next
  case (9 y Q G x)
  from 9(2)[of xs ys] 9(1,3) show ?case
    by (auto simp: Let_def is_Bool_def intro!: gen.intros(9) split: if_splits)
next
  case (10 x y Q G)
  show ?case
  proof (cases "x \<in> fv Q")
    case True
    with 10(4,1) show ?thesis using 10(3)
      by (rule gen_Gen_substs_Exists)
  next
    case False
    with 10(2) have "G = {}"
      by (auto dest: gen_fv)
    with 10(2,4) have "cp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys]) = Bool False"
      by (auto intro!: gen_empty_cp_substs[of x])
    with 10(2,4) have "cp (Exists y Q[xs \<^bold>\<rightarrow>\<^sup>* ys]) = Bool False" unfolding \<open>G = {}\<close>
      by (intro gen_empty_cp_substs_Exists)
    then show ?thesis
      by auto
  qed
qed (fastforce simp: Let_def is_Bool_def intro!: gen.intros split: if_splits)+

lemma Gen_cp_substs: "Gen z Q \<Longrightarrow> length xs = length ys \<Longrightarrow> Gen (subst_var xs ys z) (cp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys]))"
  by (blast intro: gen_Gen_cp_substs)

lemma Gen_cp_subst: "Gen z Q \<Longrightarrow> z \<noteq> x \<Longrightarrow> Gen z (cp (Q[x \<^bold>\<rightarrow> y]))"
  using Gen_cp_substs[of z Q "[x]" "[y]"] by auto

lemma substs_bd_fv: "length xs = length ys \<Longrightarrow> substs_bd z xs ys Q \<in> fv (Q[substs_src z xs ys Q \<^bold>\<rightarrow>\<^sup>* substs_dst z xs ys Q]) \<Longrightarrow> z \<in> fv Q"
proof (induct xs ys arbitrary: z Q rule: list_induct2)
  case (Cons x xs y ys)
  from Cons(1,3) show ?case
    by (auto 0 4 simp: fv_subst fresh2 dest: Cons(2) sym split: if_splits)
qed simp

lemma Gen_substs_bd: "length xs = length ys \<Longrightarrow>
  (\<And>xs ys. length xs = length ys \<Longrightarrow> Gen (subst_var xs ys z) (cp (Qz[xs \<^bold>\<rightarrow>\<^sup>* ys]))) \<Longrightarrow>
  Gen (substs_bd z xs ys Qz) (cp (Qz[substs_src z xs ys Qz \<^bold>\<rightarrow>\<^sup>* substs_dst z xs ys Qz]))"
proof (induct xs ys arbitrary: z Qz rule: list_induct2)
  case Nil
  from Nil(1)[of "[]" "[]"] show ?case
    by simp
next
  case (Cons x xs y ys)
  have "Gen (subst_var xs ys (fresh2 x y Qz)) (cp (Qz[y \<^bold>\<rightarrow> fresh2 x y Qz][x \<^bold>\<rightarrow> y][xs \<^bold>\<rightarrow>\<^sup>* ys]))"
    if "length xs = length ys" "z = y" for xs ys
    using that Cons(3)[of "[y,x]@xs" "[fresh2 x y Qz,y]@ys"]
    by (auto simp: fresh2)
  moreover have "Gen (subst_var xs ys z) (cp (Qz[x \<^bold>\<rightarrow> y][xs \<^bold>\<rightarrow>\<^sup>* ys]))"
    if "length xs = length ys" "x \<noteq> z" for xs ys
    using that Cons(3)[of "[x]@xs" "[y]@ys"]
    by (auto simp: fresh2)
  ultimately show ?case using Cons(1,3)
    by (auto intro!: Cons(2))
qed

subsection \<open>Safe-Range Queries\<close>

definition nongens where
  "nongens Q = {x \<in> fv Q. \<not> Gen x Q}"

abbreviation rrf where
  "rrf Q \<equiv> nongens Q = {}"

definition rrb where
  "rrb Q = (\<forall>y Qy. Exists y Qy \<in> sub Q \<longrightarrow> Gen y Qy)"

lemma rrb_simps[simp]:
  "rrb (Bool b) = True"
  "rrb (Pred p ts) = True"
  "rrb (Eq x t) = True"
  "rrb (Neg Q) = rrb Q"
  "rrb (Disj Q1 Q2) = (rrb Q1 \<and> rrb Q2)"
  "rrb (Conj Q1 Q2) = (rrb Q1 \<and> rrb Q2)"
  "rrb (Exists y Qy) = (Gen y Qy \<and> rrb Qy)"
  "rrb (exists y Qy) = ((y \<in> fv Qy \<longrightarrow> Gen y Qy) \<and> rrb Qy)"
  by (auto simp: rrb_def exists_def)

lemma ap_rrb[simp]: "ap Q \<Longrightarrow> rrb Q"
  by (cases Q rule: ap.cases) auto

lemma qp_rrb[simp]: "qp Q \<Longrightarrow> rrb Q"
  by (induct Q rule: qp.induct) (auto simp: qp_Gen)

lemma rrb_cp: "rrb Q \<Longrightarrow> rrb (cp Q)"
  by (induct Q rule: cp.induct)
    (auto split: term.splits simp: Let_def exists_def Gen_cp dest!: fv_cp[THEN set_mp])

lemma gen_Gen_erase: "gen x Q G \<Longrightarrow> Gen x (Q \<^bold>\<bottom> z)"
  by (induct x Q G rule: gen_induct)
    (auto 0 4 intro: gen.intros qp.intros ap.intros elim!: ap.cases)

lemma Gen_erase: "Gen x Q \<Longrightarrow> Gen x (Q \<^bold>\<bottom> z)"
  by (metis gen_Gen_erase)

lemma rrb_erase: "rrb Q \<Longrightarrow> rrb (Q \<^bold>\<bottom> x)"
  by (induct Q x rule: erase.induct)
    (auto split: term.splits simp: Let_def exists_def Gen_erase dest!: fv_cp[THEN set_mp])

lemma rrb_DISJ[simp]: "finite \<Q> \<Longrightarrow> (\<forall>Q \<in> \<Q>. rrb Q) \<Longrightarrow> rrb (DISJ \<Q>)"
  by (auto simp: rrb_def dest!: Exists_in_sub_DISJ)

lemma rrb_cp_substs: "rrb Q \<Longrightarrow> length xs = length ys \<Longrightarrow> rrb (cp (Q[xs \<^bold>\<rightarrow>\<^sup>* ys]))"
proof (induct "size Q" arbitrary: Q xs ys rule: less_induct)
  case less
  then show ?case
  proof (cases Q)
    case (Exists z Qz)
    from less(2,3) show ?thesis
      unfolding Exists substs_Exists[OF less(3)] cp.simps rrb_simps
      by (intro conjI impI less(1) Gen_substs_bd Gen_cp_substs) (simp_all add: Exists)
  qed (auto simp: Let_def ap_cp ap_substs ap.intros split: term.splits)
qed

lemma rrb_cp_subst: "rrb Q \<Longrightarrow> rrb (cp (Q[x \<^bold>\<rightarrow> y]))"
  using rrb_cp_substs[of Q "[x]" "[y]"]
  by auto

definition "sr Q = (rrf Q \<and> rrb Q)"

lemma nongens_cp: "nongens (cp Q) \<subseteq> nongens Q"
  unfolding nongens_def by (auto dest: gen_Gen_cp fv_cp[THEN set_mp])

lemma sr_Disj: "fv Q1 = fv Q2 \<Longrightarrow> sr (Disj Q1 Q2) = (sr Q1 \<and> sr Q2)"
  by (auto 0 4 simp: sr_def nongens_def elim!: ap.cases elim: gen.cases intro: gen.intros)

lemma sr_foldr_Disj: "\<forall>Q' \<in> set Qs. fv Q' = fv Q  \<Longrightarrow> sr (foldr Disj Qs Q) \<longleftrightarrow> (\<forall>Q \<in> set Qs. sr Q) \<and> sr Q"
  by (induct Qs) (auto simp: sr_Disj)

lemma sr_foldr1_Disj: "\<forall>Q' \<in> set Qs. fv Q' = X  \<Longrightarrow> sr (foldr1 Disj Qs Q) \<longleftrightarrow> (if Qs = [] then sr Q else (\<forall>Q \<in> set Qs. sr Q))"
  by (cases Qs) (auto simp: sr_foldr_Disj)

lemma sr_False[simp]: "sr (Bool False)"
  by (auto simp: sr_def nongens_def)

lemma sr_cp: "sr Q \<Longrightarrow> sr (cp Q)"
  by (auto simp: rrb_cp sr_def dest: nongens_cp[THEN set_mp])

lemma sr_DISJ: "finite \<Q> \<Longrightarrow> \<forall>Q' \<in> \<Q>. fv Q' = X \<Longrightarrow> (\<forall>Q \<in> \<Q>. sr Q) \<Longrightarrow> sr (DISJ \<Q>)"
  by (auto simp: DISJ_def sr_foldr1_Disj[of _ X] sr_cp)

lemma sr_Conj_eq: "sr Q \<Longrightarrow> x \<in> fv Q \<or> y \<in> fv Q \<Longrightarrow> sr (Conj Q (x \<approx> y))"
  by (auto simp: sr_def nongens_def intro: gen.intros)

subsection \<open>Simplification\<close>

locale simplification =
  fixes simp :: "('a::{infinite, linorder}, 'b :: linorder) fmla \<Rightarrow> ('a, 'b) fmla"
    and simplified :: "('a, 'b) fmla \<Rightarrow> bool"
  assumes sat_simp: "sat (simp Q) I \<sigma> = sat Q I \<sigma>"
      and fv_simp: "fv (simp Q) \<subseteq> fv Q"
      and rrb_simp: "rrb Q \<Longrightarrow> rrb (simp Q)"
      and gen_Gen_simp: "gen x Q G \<Longrightarrow> Gen x (simp Q)"
      and fv_simp_Disj_same: "fv (simp Q1) = X \<Longrightarrow> fv (simp Q2) = X \<Longrightarrow> fv (simp (Disj Q1 Q2)) = X"
      and simp_False: "simp (Bool False) = Bool False"
      and simplified_sub: "simplified Q \<Longrightarrow> Q' \<in> sub Q \<Longrightarrow> simplified Q'"
      and simplified_Conj_eq: "simplified Q \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> fv Q \<or> y \<in> fv Q \<Longrightarrow> simplified (Conj Q (x \<approx> y))"
      and simplified_fv_simp: "simplified Q \<Longrightarrow> fv (simp Q) = fv Q"
      and simplified_simp: "simplified (simp Q)"
      and simplified_cp: "simplified (cp Q)"
begin

lemma Gen_simp: "Gen x Q \<Longrightarrow> Gen x (simp Q)"
  by (metis gen_Gen_simp)

lemma nongens_simp: "nongens (simp Q) \<subseteq> nongens Q"
  using Gen_simp by (auto simp: nongens_def dest!: fv_simp[THEN set_mp])

lemma sr_simp: "sr Q \<Longrightarrow> sr (simp Q)"
  by (auto simp: rrb_simp sr_def dest: nongens_simp[THEN set_mp])

lemma equiv_simp_cong: "Q \<triangleq> Q' \<Longrightarrow> simp Q \<triangleq> simp Q'"
  by (auto simp: equiv_def sat_simp)

lemma equiv_simp: "simp Q \<triangleq> Q"
  by (auto simp: equiv_def sat_simp)

lemma fv_simp_foldr_Disj: "\<forall>Q\<in>set Qs \<union> {Q}. simplified Q \<and> fv Q = A \<Longrightarrow>
  fv (simp (foldr Disj Qs Q)) = A"
  by (induct Qs) (auto simp: Let_def is_Bool_def simplified_fv_simp fv_simp_Disj_same)

lemma fv_simp_foldr1_Disj: "simp (foldr1 Disj Qs (Bool False)) \<noteq> Bool False \<Longrightarrow>
  \<forall>Q\<in>set Qs. simplified Q \<and> fv Q = A \<Longrightarrow>
  fv (simp (foldr1 Disj Qs (Bool False))) = A"
  by (cases Qs) (auto simp: fv_simp_foldr_Disj simp_False)

lemma fv_simp_DISJ_eq:
  "finite \<Q> \<Longrightarrow> simp (DISJ \<Q>) \<noteq> Bool False \<Longrightarrow> \<forall>Q \<in> \<Q>. simplified Q \<and> fv Q = A \<Longrightarrow> fv (simp (DISJ \<Q>)) = A"
  by (auto simp: DISJ_def fv_simp_foldr1_Disj)

end

subsection \<open>Covered Variables\<close>

inductive cov where
  Eq_self: "cov x (x \<approx> x) {}"
| nonfree: "x \<notin> fv Q \<Longrightarrow> cov x Q {}"
| EqL: "x \<noteq> y \<Longrightarrow> cov x (x \<approx> y) {x \<approx> y}"
| EqR: "x \<noteq> y \<Longrightarrow> cov x (y \<approx> x) {x \<approx> y}"
| ap: "ap Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> cov x Q {Q}"
| Neg: "cov x Q G \<Longrightarrow> cov x (Neg Q) G"
| Disj: "cov x Q1 G1 \<Longrightarrow> cov x Q2 G2 \<Longrightarrow> cov x (Disj Q1 Q2) (G1 \<union> G2)"
| DisjL: "cov x Q1 G \<Longrightarrow> cp (Q1 \<^bold>\<bottom> x) = Bool True \<Longrightarrow> cov x (Disj Q1 Q2) G"
| DisjR: "cov x Q2 G \<Longrightarrow> cp (Q2 \<^bold>\<bottom> x) = Bool True \<Longrightarrow> cov x (Disj Q1 Q2) G"
| Conj: "cov x Q1 G1 \<Longrightarrow> cov x Q2 G2 \<Longrightarrow> cov x (Conj Q1 Q2) (G1 \<union> G2)"
| ConjL: "cov x Q1 G \<Longrightarrow> cp (Q1 \<^bold>\<bottom> x) = Bool False \<Longrightarrow> cov x (Conj Q1 Q2) G"
| ConjR: "cov x Q2 G \<Longrightarrow> cp (Q2 \<^bold>\<bottom> x) = Bool False \<Longrightarrow> cov x (Conj Q1 Q2) G"
| Exists: "x \<noteq> y \<Longrightarrow> cov x Q G \<Longrightarrow> x \<approx> y \<notin> G \<Longrightarrow> cov x (Exists y Q) (exists y ` G)"
| Exists_gen: "x \<noteq> y \<Longrightarrow> cov x Q G \<Longrightarrow> gen y Q Gy \<Longrightarrow> cov x (Exists y Q) ((exists y ` (G - {x \<approx> y})) \<union> ((\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` Gy))"

inductive cov' where
  Eq_self: "cov' x (x \<approx> x) {}"
| nonfree: "x \<notin> fv Q \<Longrightarrow> cov' x Q {}"
| EqL: "x \<noteq> y \<Longrightarrow> cov' x (x \<approx> y) {x \<approx> y}"
| EqR: "x \<noteq> y \<Longrightarrow> cov' x (y \<approx> x) {x \<approx> y}"
| ap: "ap Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> cov' x Q {Q}"
| Neg: "cov' x Q G \<Longrightarrow> cov' x (Neg Q) G"
| Disj: "cov' x Q1 G1 \<Longrightarrow> cov' x Q2 G2 \<Longrightarrow> cov' x (Disj Q1 Q2) (G1 \<union> G2)"
| DisjL: "cov' x Q1 G \<Longrightarrow> cp (Q1 \<^bold>\<bottom> x) = Bool True \<Longrightarrow> cov' x (Disj Q1 Q2) G"
| DisjR: "cov' x Q2 G \<Longrightarrow> cp (Q2 \<^bold>\<bottom> x) = Bool True \<Longrightarrow> cov' x (Disj Q1 Q2) G"
| Conj: "cov' x Q1 G1 \<Longrightarrow> cov' x Q2 G2 \<Longrightarrow> cov' x (Conj Q1 Q2) (G1 \<union> G2)"
| ConjL: "cov' x Q1 G \<Longrightarrow> cp (Q1 \<^bold>\<bottom> x) = Bool False \<Longrightarrow> cov' x (Conj Q1 Q2) G"
| ConjR: "cov' x Q2 G \<Longrightarrow> cp (Q2 \<^bold>\<bottom> x) = Bool False \<Longrightarrow> cov' x (Conj Q1 Q2) G"
| Exists: "x \<noteq> y \<Longrightarrow> cov' x Q G \<Longrightarrow> x \<approx> y \<notin> G \<Longrightarrow> cov' x (Exists y Q) (exists y ` G)"
| Exists_gen: "x \<noteq> y \<Longrightarrow> cov' x Q G \<Longrightarrow> gen y Q Gy \<Longrightarrow> cov' x (Exists y Q) ((exists y ` (G - {x \<approx> y})) \<union> ((\<lambda>Q. Q[y \<^bold>\<rightarrow> x]) ` Gy))"

lemma cov_nocp_intros:
  "x \<noteq> y \<Longrightarrow> cov x Q G \<Longrightarrow> gen y Q Gy \<Longrightarrow> cov x (Exists y Q) ((exists y ` (G - {x \<approx> y})) \<union> ((\<lambda>Q. Q[y \<^bold>\<rightarrow> x]) ` Gy))"
  by (metis (no_types, lifting) cov.Exists_gen gen_qp image_cong qp_cp_subst_triv)

lemma cov'_cp_intros:
  "x \<noteq> y \<Longrightarrow> cov' x Q G \<Longrightarrow> gen y Q Gy \<Longrightarrow> cov' x (Exists y Q) ((exists y ` (G - {x \<approx> y})) \<union> ((\<lambda>Q. cp (Q[y \<^bold>\<rightarrow> x])) ` Gy))"
  by (metis (no_types, lifting) cov'.Exists_gen gen_qp image_cong qp_cp_subst_triv)

lemma cov'_cov: "cov' x Q G \<Longrightarrow> cov x Q G"
  by (induct x Q G rule: cov'.induct) (force intro: cov.intros cov_nocp_intros)+

lemma cov_cov': "cov x Q G \<Longrightarrow> cov' x Q G"
  by (induct x Q G rule: cov.induct) (force intro: cov'.intros cov'_cp_intros)+

lemma cov_eq_cov': "cov = cov'"
  using cov'_cov cov_cov' by blast

lemmas cov_induct[consumes 1, case_names Eq_self nonfree EqL EqR ap Neg Disj DisjL DisjR Conj ConjL ConjR Exists Exists_gen] =
  cov'.induct[folded cov_eq_cov']

lemma ex_cov: "rrb Q \<Longrightarrow> x \<in> fv Q \<Longrightarrow> \<exists>G. cov x Q G"
proof (induct Q)
  case (Eq z t)
  then show ?case
    by (cases t) (auto 6 0 intro: cov.intros ap.intros)
next
  case (Exists z Q)
  then obtain G Gz where "cov x Q G" "gen z Q Gz" "x \<noteq> z"
    by force
  then show ?case
    by (cases "x \<approx> z \<in> G") (auto intro: cov.intros)
qed (auto intro: cov.intros ap.intros)

definition qps where
  "qps G = {Q \<in> G. qp Q}"

lemma qps_qp: "Q \<in> qps G \<Longrightarrow> qp Q"
  by (auto simp: qps_def)

lemma qps_in: "Q \<in> qps G \<Longrightarrow> Q \<in> G"
  by (auto simp: qps_def)

lemma qps_empty[simp]: "qps {} = {}"
  by (auto simp: qps_def)

lemma qps_insert: "qps (insert Q Qs) = (if qp Q then insert Q (qps Qs) else qps Qs)"
  by (auto simp: qps_def)

lemma qps_union[simp]: "qps (X \<union> Y) = qps X \<union> qps Y"
  by (auto simp: qps_def)

lemma finite_qps[simp]: "finite G \<Longrightarrow> finite (qps G)"
  by (auto simp: qps_def)

lemma qps_exists[simp]: "x \<noteq> y \<Longrightarrow> qps (exists y ` G) = exists y ` qps G"
  by (auto simp: qps_def image_iff exists_def qp_Exists elim: qp_ExistsE)

lemma qps_subst[simp]: "qps ((\<lambda>Q. Q[x \<^bold>\<rightarrow> y]) ` G) = (\<lambda>Q. Q[x \<^bold>\<rightarrow> y]) ` qps G"
  by (auto simp: qps_def image_iff exists_def)

lemma qps_minus[simp]: "qps (G - {x \<approx> y}) = qps G"
  by (auto simp: qps_def)

lemma gen_qps[simp]: "gen x Q G \<Longrightarrow> qps G = G"
  by (auto dest: gen_qp simp: qps_def)

lemma qps_rrb[simp]: "Q \<in> qps G \<Longrightarrow> rrb Q"
  by (auto simp: qps_def)

definition eqs where
  "eqs x G = {y. x \<noteq> y \<and> x \<approx> y \<in> G}"

lemma eqs_in: "y \<in> eqs x G \<Longrightarrow> x \<approx> y \<in> G"
  by (auto simp: eqs_def)

lemma eqs_noteq: "y \<in> eqs x Q \<Longrightarrow> x \<noteq> y"
  unfolding eqs_def by auto

lemma eqs_empty[simp]: "eqs x {} = {}"
  by (auto simp: eqs_def)

lemma eqs_union[simp]: "eqs x (X \<union> Y) = eqs x X \<union> eqs x Y"
  by (auto simp: eqs_def)

lemma finite_eqs[simp]: "finite G \<Longrightarrow> finite (eqs x G)"
  by (force simp: eqs_def image_iff elim!: finite_surj[where f = "\<lambda>Q. SOME y. Q = x \<approx> y"])

lemma eqs_exists[simp]: "x \<noteq> y \<Longrightarrow> eqs x (exists y ` G) = eqs x G - {y}"
  by (auto simp: eqs_def exists_def image_iff)

lemma notin_eqs[simp]: "x \<approx> y \<notin> G \<Longrightarrow> y \<notin> eqs x G"
  by (auto simp: eqs_def)

lemma eqs_minus[simp]: "eqs x (G - {x \<approx> y}) = eqs x G - {y}"
  by (auto simp: eqs_def)

lemma Var_eq_subst_iff: "Var z = t[x \<^bold>\<rightarrow>t y] \<longleftrightarrow> (if z = x then x = y \<and> t = Var x else
  if z = y then t = Var x \<or> t = Var y else t = Var z)"
  by (cases t) auto

lemma Eq_eq_subst_iff: "y \<approx> z = Q[x \<^bold>\<rightarrow> y] \<longleftrightarrow> (if z = x then x = y \<and> Q = x \<approx> x else
  Q = x \<approx> z \<or> Q = y \<approx> z \<or> (z = y \<and> Q \<in> {x \<approx> x, y \<approx> y, y \<approx> x}))"
  by (cases Q) (auto simp: Let_def Var_eq_subst_iff split: if_splits)

lemma eqs_subst[simp]: "x \<noteq> y \<Longrightarrow> eqs y ((\<lambda>Q. Q[x \<^bold>\<rightarrow> y]) ` G) = (eqs y G - {x}) \<union> (eqs x G - {y})"
  by (auto simp: eqs_def image_iff exists_def Eq_eq_subst_iff)

lemma gen_eqs[simp]: "gen x Q G \<Longrightarrow> eqs z G = {}"
  by (auto dest: gen_qp simp: eqs_def)

lemma eqs_insert: "eqs x (insert Q Qs) = (case Q of z \<approx> y \<Rightarrow>
  if z = x \<and> z \<noteq> y then insert y (eqs x Qs) else eqs x Qs | _ \<Rightarrow> eqs x Qs)"
  by (auto simp: eqs_def split: fmla.splits term.splits)

lemma eqs_insert': "y \<noteq> x \<Longrightarrow> eqs x (insert (x \<approx> y) Qs) = insert y (eqs x Qs)"
  by (auto simp: eqs_def split: fmla.splits term.splits)

lemma eqs_code[code]: "eqs x G = (\<lambda>eq. case eq of y \<approx> z \<Rightarrow> z) ` (Set.filter (\<lambda>eq. case eq of y \<approx> z \<Rightarrow> x = y \<and> x \<noteq> z | _ => False) G)"
  by (auto simp: eqs_def image_iff Set.filter_def split: term.splits fmla.splits)

lemma gen_finite[simp]: "gen x Q G \<Longrightarrow> finite G"
  by (induct x Q G rule: gen_induct) auto

lemma cov_finite[simp]: "cov x Q G \<Longrightarrow> finite G"
  by (induct x Q G rule: cov.induct) auto

lemma gen_sat_erase: "gen y Q Gy \<Longrightarrow> sat (Q \<^bold>\<bottom> x) I \<sigma> \<Longrightarrow> \<exists>Q\<in>Gy. sat Q I \<sigma>"
  by (induct y Q Gy arbitrary: \<sigma> rule: gen_induct)
    (force elim!: ap.cases dest: sym gen_sat split: if_splits)+

lemma cov_sat_erase: "cov x Q G \<Longrightarrow>
  sat (Neg (Disj (DISJ (qps G)) (DISJ ((\<lambda>y. x \<approx> y) ` eqs x G)))) I \<sigma> \<Longrightarrow>
  sat Q I \<sigma> \<longleftrightarrow> sat (cp (Q \<^bold>\<bottom> x)) I \<sigma>"
  unfolding sat_cp
proof (induct x Q G arbitrary: \<sigma> rule: cov_induct)
  case (Eq_self x)
  then show ?case
    by auto
next
  case (nonfree x Q)
  from nonfree(1) show ?case
    by (induct Q arbitrary: \<sigma>) auto
next
  case (EqL x y)
  then show ?case
    by (auto simp: eqs_def)
next
  case (EqR x y)
  then show ?case
    by (auto simp: eqs_def)
next
  case (ap Q x)
  then show ?case
    by (auto simp: qps_def qp.intros elim!: ap.cases)
next
  case (Neg x Q G)
  then show ?case
    by auto
next
  case (Disj x Q1 G1 Q2 G2)
  then show ?case
    by auto
next
  case (DisjL x Q1 G Q2)
  then have "sat (Q1 \<^bold>\<bottom> x) I \<sigma>"
    by (subst sat_cp[symmetric]) auto
  with DisjL show ?case
    by auto
next
  case (DisjR x Q2 G Q1)
  then have "sat (Q2 \<^bold>\<bottom> x) I \<sigma>"
    by (subst sat_cp[symmetric]) auto
  with DisjR show ?case
    by auto
next
  case (Conj x Q1 G1 Q2 G2)
  then show ?case
    by auto
next
  case (ConjL x Q1 G Q2)
  then have "\<not> sat (Q1 \<^bold>\<bottom> x) I \<sigma>"
    by (subst sat_cp[symmetric]) auto
  with ConjL show ?case
    by auto
next
  case (ConjR x Q2 G Q1)
  then have "\<not> sat (Q2 \<^bold>\<bottom> x) I \<sigma>"
    by (subst sat_cp[symmetric]) auto
  with ConjR show ?case
    by auto
next
  case (Exists x y Q G)
  then show ?case
    by fastforce
next
  case (Exists_gen x y Q G Gy)
  show ?case
    unfolding sat.simps erase.simps Exists_gen(1)[THEN eq_False[THEN iffD2]] if_False
  proof (intro ex_cong1)
    fix z
    show "sat Q I (\<sigma>(y := z)) = sat (Q \<^bold>\<bottom> x) I (\<sigma>(y := z))"
    proof (cases "z = \<sigma> x")
      case True
      with Exists_gen(2,4,5) show ?thesis
        by (auto dest: gen_sat gen_sat_erase simp: ball_Un)
    next
      case False
      with Exists_gen(1,2,4,5) show ?thesis
        by (intro Exists_gen(3)) (auto simp: ball_Un fun_upd_def)
    qed
  qed
qed

lemma cov_fv_aux: "cov x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> x \<in> fv Qqp \<and> fv Qqp - {x} \<subseteq> fv Q"
  by (induct x Q G arbitrary: Qqp rule: cov_induct)
    (auto simp: fv_subst subset_eq gen_fv[THEN conjunct1]
      gen_fv[THEN conjunct2, THEN set_mp] dest: gen_fv split: if_splits)

lemma cov_fv: "cov x Q G \<Longrightarrow> x \<in> fv Q \<Longrightarrow> Qqp \<in> G \<Longrightarrow> x \<in> fv Qqp \<and> fv Qqp \<subseteq> fv Q"
  using cov_fv_aux[of x Q G Qqp] by auto

lemma Gen_Conj:
  "Gen x Q1 \<Longrightarrow> Gen x (Conj Q1 Q2)"
  "Gen x Q2 \<Longrightarrow> Gen x (Conj Q1 Q2)"
  by (auto intro: gen.intros)

lemma cov_Gen_qps: "cov x Q G \<Longrightarrow> x \<in> fv Q \<Longrightarrow> Gen x (Conj Q (DISJ (qps G)))"
  by (intro Gen_Conj(2) Gen_DISJ) (auto simp: qps_def dest: cov_fv)

lemma cov_equiv:
  assumes "cov x Q G" "\<And>Q I \<sigma>. sat (simp Q) I \<sigma> = sat Q I \<sigma>"
  shows "Q \<triangleq> Disj (simp (Conj Q (DISJ (qps G))))
    (Disj (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G))
    (Conj (Q \<^bold>\<bottom> x) (Neg (Disj (DISJ (qps G)) (DISJ ((\<lambda>y. x \<approx> y) ` eqs x G))))))"
  (is "_ \<triangleq> ?rhs")
unfolding equiv_def proof (intro allI impI)
  fix I \<sigma>
  show "sat Q I \<sigma> = sat ?rhs I \<sigma>"
    using cov_sat_erase[OF assms(1), of I \<sigma>] assms
    by (fastforce dest: sym simp del: cp.simps)
qed

fun csts_term where
  "csts_term (Var x) = {}"
| "csts_term (Const c) = {c}"

fun csts where
  "csts (Bool b) = {}"
| "csts (Pred p ts) = (\<Union>t \<in> set ts. csts_term t)"
| "csts (Eq x t) = csts_term t"
| "csts (Neg Q) = csts Q"
| "csts (Conj Q1 Q2) = csts Q1 \<union> csts Q2"
| "csts (Disj Q1 Q2) = csts Q1 \<union> csts Q2"
| "csts (Exists x Q) = csts Q"

lemma finite_csts_term[simp]: "finite (csts_term t)"
  by (induct t) auto

lemma finite_csts[simp]: "finite (csts t)"
  by (induct t) auto

lemma ap_fresh_val: "ap Q \<Longrightarrow> \<sigma> x \<notin> adom I \<Longrightarrow> \<sigma> x \<notin> csts Q \<Longrightarrow> sat Q I \<sigma> \<Longrightarrow> x \<notin> fv Q"
proof (induct Q pred: ap)
  case (Pred p ts)
  show ?case unfolding fv.simps fv_terms_set_def set_map UN_iff bex_simps
  proof safe
    fix t
    assume "t \<in> set ts" "x \<in> fv_term_set t"
    with Pred show "False"
      by (cases t) (force simp: adom_def eval_terms_def)+
  qed
qed auto

lemma qp_fresh_val: "qp Q \<Longrightarrow> \<sigma> x \<notin> adom I \<Longrightarrow> \<sigma> x \<notin> csts Q \<Longrightarrow> sat Q I \<sigma> \<Longrightarrow> x \<notin> fv Q"
proof (induct Q arbitrary: \<sigma> rule: qp.induct)
  case (ap Q)
  then show ?case by (rule ap_fresh_val)
next
  case (exists Q z)
  from exists(2)[of \<sigma>] exists(2)[of "\<sigma>(z := _)"] exists(1,3-) show ?case
    by (cases "x = z") (auto simp: exists_def fun_upd_def split: if_splits)
qed

lemma ex_fresh_val:
  fixes Q :: "('a :: infinite, 'b) fmla"
  assumes "finite (adom I)" "finite A"
  shows "\<exists>x. x \<notin> adom I \<and> x \<notin> csts Q \<and> x \<notin> A"
  by (metis UnCI assms ex_new_if_finite finite_Un finite_csts infinite_UNIV)

definition fresh_val :: "('a :: infinite, 'b) fmla \<Rightarrow> ('a, 'b) intp \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "fresh_val Q I A = (SOME x. x \<notin> adom I \<and> x \<notin> csts Q \<and> x \<notin> A)"

lemma fresh_val:
  "finite (adom I) \<Longrightarrow> finite A \<Longrightarrow> fresh_val Q I A \<notin> adom I"
  "finite (adom I) \<Longrightarrow> finite A \<Longrightarrow> fresh_val Q I A \<notin> csts Q"
  "finite (adom I) \<Longrightarrow> finite A \<Longrightarrow> fresh_val Q I A \<notin> A"
  using someI_ex[OF ex_fresh_val, of I A Q]
  by (auto simp: fresh_val_def)

lemma csts_exists[simp]: "csts (exists x Q) = csts Q"
  by (auto simp: exists_def)

lemma csts_term_subst_term[simp]: "csts_term (t[x \<^bold>\<rightarrow>t y]) = csts_term t"
  by (cases t) auto

lemma csts_subst[simp]: "csts (Q[x \<^bold>\<rightarrow> y]) = csts Q"
  by (induct Q x y rule: subst.induct) (auto simp: Let_def)

lemma gen_csts: "gen x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> csts Qqp \<subseteq> csts Q"
  by (induct x Q G arbitrary: Qqp rule: gen_induct) (auto simp: subset_eq)

lemma cov_csts: "cov x Q G \<Longrightarrow> Qqp \<in> G \<Longrightarrow> csts Qqp \<subseteq> csts Q"
  by (induct x Q G arbitrary: Qqp rule: cov_induct)
    (auto simp: subset_eq gen_csts[THEN set_mp])

lemma not_self_eqs[simp]: "x \<notin> eqs x G"
  by (auto simp: eqs_def)

lemma (in simplification) cov_Exists_equiv:
  fixes Q :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "cov x Q G" "x \<in> fv Q"
  shows "Exists x Q \<triangleq> Disj (Exists x (simp (Conj Q (DISJ (qps G)))))
    (Disj (DISJ ((\<lambda>y. cp (Q[x \<^bold>\<rightarrow> y])) ` eqs x G)) (cp (Q \<^bold>\<bottom> x)))"
proof -
  have "Exists x Q \<triangleq> Exists x (Disj (simp (Conj Q (DISJ (qps G))))
    (Disj (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G))
      (Conj (Q \<^bold>\<bottom> x) (Neg (Disj (DISJ (qps G)) (DISJ ((\<approx>) x ` eqs x G)))))))"
    by (rule equiv_Exists_cong[OF cov_equiv[OF assms(1) sat_simp]])
  also have "\<dots> \<triangleq> Disj (Exists x (simp (Conj Q (DISJ (qps G))))) (Disj
    (Exists x (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G)))
      (Exists x (Conj (Q \<^bold>\<bottom> x) (Neg (Disj (DISJ (qps G)) (DISJ ((\<approx>) x ` eqs x G)))))))"
    by (auto intro!: equiv_trans[OF equiv_Exists_Disj] equiv_Disj_cong[OF equiv_refl])
  also have "\<dots> \<triangleq> Disj (Exists x (simp (Conj Q (DISJ (qps G)))))
    (Disj (DISJ ((\<lambda>y. cp (Q[x \<^bold>\<rightarrow> y])) ` eqs x G)) (cp (Q \<^bold>\<bottom> x)))"
  proof (rule equiv_Disj_cong[OF equiv_refl equiv_Disj_cong])
    show "Exists x (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G)) \<triangleq> DISJ ((\<lambda>y. cp (Q[x \<^bold>\<rightarrow> y])) ` eqs x G)"
      using assms(1) unfolding equiv_def
      by simp (auto simp: eqs_def)
  next
    show "Exists x (Conj (Q \<^bold>\<bottom> x) (Neg (Disj (DISJ (qps G)) (DISJ ((\<approx>) x ` eqs x G))))) \<triangleq> cp (Q \<^bold>\<bottom> x)"
      unfolding equiv_def sat.simps sat_erase sat_cp
        sat_DISJ[OF finite_qps[OF cov_finite[OF assms(1)]]]
        sat_DISJ[OF finite_imageI[OF finite_eqs[OF cov_finite[OF assms(1)]]]]
    proof (intro allI impI)
      fix I :: "('a, 'b) intp" and \<sigma>
      assume "finite (adom I)"
      then show "(\<exists>z. sat (Q \<^bold>\<bottom> x) I \<sigma> \<and> \<not> ((\<exists>Q\<in>qps G. sat Q I (\<sigma>(x := z))) \<or> (\<exists>Q\<in>(\<approx>) x ` eqs x G. sat Q I (\<sigma>(x := z))))) =
        sat (Q \<^bold>\<bottom> x) I \<sigma>"
        using fresh_val[OF _ finite_imageI[OF finite_fv], of I Q \<sigma> Q] assms
        by (auto 0 3 simp: qps_def eqs_def intro!: exI[of _ "fresh_val Q I  (\<sigma> ` fv Q)"]
            dest: cov_fv cov_csts[THEN set_mp]
            qp_fresh_val[where \<sigma>="\<sigma>(x := fresh_val Q I (\<sigma> ` fv Q))" and x=x and I=I])
    qed
  qed
  finally show ?thesis .
qed

definition "eval_on V Q I =
  (let xs = sorted_list_of_set V
  in {ds. length xs = length ds \<and> (\<exists>\<sigma>. sat Q I (\<sigma>[xs :=\<^sup>* ds]))})"

definition "eval Q I = eval_on (fv Q) Q I"

lemmas eval_deep_def = eval_def[unfolded eval_on_def]

lemma (in simplification) cov_eval_fin:
  fixes Q :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "cov x Q G" "x \<in> fv Q" "finite (adom I)" "\<And>\<sigma>. \<not> sat (Q \<^bold>\<bottom> x) I \<sigma>"
  shows "eval Q I = eval_on (fv Q) (Disj (simp (Conj Q (DISJ (qps G))))
    (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G))) I"
    (is "eval Q I = eval_on (fv Q) ?Q I")
proof -
  from assms(1) have fv: "fv ?Q \<subseteq> fv Q"
    by (auto dest!: fv_cp[THEN set_mp] fv_simp[THEN set_mp] fv_DISJ[THEN set_mp, rotated -1]
      eqs_in qps_in cov_fv[OF assms(1,2)] simp: fv_subst simp del: cp.simps split: if_splits)
  show ?thesis
    unfolding eval_deep_def eval_on_def Let_def fv
  proof (intro Collect_eqI arg_cong2[of _ _ _ _ "(\<and>)"] ex_cong1)
    fix ds \<sigma>
    show "sat Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* ds]) \<longleftrightarrow>
          sat ?Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* ds])"
      by (subst cov_equiv[OF assms(1) sat_simp, unfolded equiv_def, rule_format, OF assms(3)])
        (auto simp: assms(4))
  qed simp
qed

lemma (in simplification) cov_sat_fin:
  fixes Q :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "cov x Q G" "x \<in> fv Q" "finite (adom I)" "\<And>\<sigma>. \<not> sat (Q \<^bold>\<bottom> x) I \<sigma>"
  shows "sat Q I \<sigma> = sat (Disj (simp (Conj Q (DISJ (qps G))))
    (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G))) I \<sigma>"
    (is "sat Q I \<sigma> = sat ?Q I \<sigma>")
proof -
  from assms(1) have fv: "fv ?Q \<subseteq> fv Q"
    by (auto dest!: fv_cp[THEN set_mp] fv_simp[THEN set_mp] fv_DISJ[THEN set_mp, rotated -1]
      eqs_in qps_in cov_fv[OF assms(1,2)] simp: fv_subst simp del: cp.simps split: if_splits)
  show ?thesis
    by (subst cov_equiv[OF assms(1) sat_simp, unfolded equiv_def, rule_format, OF assms(3)])
      (auto simp: assms(4))
qed

lemma equiv_eval_eqI: "finite (adom I) \<Longrightarrow> fv Q = fv Q' \<Longrightarrow> Q \<triangleq> Q' \<Longrightarrow> eval Q I = eval Q' I"
  by (auto simp: eval_deep_def equiv_def)

lemma equiv_eval_on_eqI: "finite (adom I) \<Longrightarrow> Q \<triangleq> Q' \<Longrightarrow> eval_on X Q I = eval_on X Q' I"
  by (auto simp: eval_on_def equiv_def)

lemma equiv_eval_on_eval_eqI: "finite (adom I) \<Longrightarrow> fv Q \<subseteq> fv Q' \<Longrightarrow> Q \<triangleq> Q' \<Longrightarrow> eval_on (fv Q') Q I = eval Q' I"
  by (auto simp: eval_deep_def eval_on_def equiv_def)

lemma finite_eval_on_Disj2D:
  assumes "finite X"
  shows "finite (eval_on X (Disj Q1 Q2) I) \<Longrightarrow> finite (eval_on X Q2 I)"
  unfolding eval_on_def Let_def
  by (auto elim!: finite_subset[rotated])

lemma finite_eval_Disj2D: "finite (eval (Disj Q1 Q2) I) \<Longrightarrow> finite (eval Q2 I)"
  unfolding eval_deep_def Let_def
proof (safe elim!: finite_surj)
  fix ds \<sigma>
  assume "length (sorted_list_of_set (fv Q2)) = length ds" "sat Q2 I (\<sigma>[sorted_list_of_set (fv Q2) :=\<^sup>* ds])"
  moreover obtain zs where "zs \<in> extend (fv Q2) (sorted_list_of_set (fv Q1 \<union> fv Q2)) ds"
    using extend_nonempty by blast
  ultimately show "ds \<in> restrict (fv Q2) (sorted_list_of_set (fv (Disj Q1 Q2))) `
    {ds. length (sorted_list_of_set (fv (Disj Q1 Q2))) = length ds \<and>
         (\<exists>\<sigma>. sat (Disj Q1 Q2) I (\<sigma>[sorted_list_of_set (fv (Disj Q1 Q2)) :=\<^sup>* ds]))}"
    by (auto simp: Let_def image_iff restrict_extend fun_upds_extend length_extend
      elim!: sat_fv_cong[THEN iffD2, rotated -1]
      intro!: exI[of _ zs] exI[of _ \<sigma>] disjI2)
qed

lemma infinite_eval_Disj2:
  fixes Q1 Q2 :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "fv Q2 \<subset> fv (Disj Q1 Q2)" "sat Q2 I \<sigma>"
  shows "infinite (eval (Disj Q1 Q2) I)"
proof -
  from assms(1) obtain z where "z \<in> fv Q1" "z \<notin> fv Q2"
    by auto
  then have "d \<in> (\<lambda>ds. lookup (sorted_list_of_set (fv Q1 \<union> fv Q2)) ds z) ` eval (Disj Q1 Q2) I" for d
    using assms(2)
    by (auto simp: fun_upds_map_self eval_deep_def Let_def length_extend intro!: exI[of _ \<sigma>] disjI2 imageI
        dest!: ex_lookup_extend[of _ _ "(sorted_list_of_set (fv Q1 \<union> fv Q2))" "map \<sigma> (sorted_list_of_set (fv Q2))" d]
        elim!: sat_fv_cong[THEN iffD2, rotated -1] fun_upds_extend[THEN trans])
  then show ?thesis
    by (rule infinite_surj[OF infinite_UNIV, OF subsetI])
qed

lemma infinite_eval_on_Disj2:
  fixes Q1 Q2 :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "fv Q2 \<subset> X" "fv Q1 \<subseteq> X""finite X" "sat Q2 I \<sigma>"
  shows "infinite (eval_on X (Disj Q1 Q2) I)"
proof -
  from assms(1) obtain z where "z \<in> X" "z \<notin> fv Q2"
    by auto
  then have "d \<in> (\<lambda>ds. lookup (sorted_list_of_set X) ds z) ` eval_on X (Disj Q1 Q2) I" for d
    using assms ex_lookup_extend[of z "fv Q2" "(sorted_list_of_set X)" "map \<sigma> (sorted_list_of_set (fv Q2))" d]
    by (auto simp: fun_upds_map_self eval_on_def Let_def subset_eq length_extend intro!: exI[of _ \<sigma>] disjI2 imageI
        elim!: sat_fv_cong[THEN iffD2, rotated -1] fun_upds_extend[rotated -1, THEN trans])
  then show ?thesis
    by (rule infinite_surj[OF infinite_UNIV, OF subsetI])
qed

lemma cov_eval_inf:
  fixes Q :: "('a :: {infinite, linorder}, 'b :: linorder) fmla"
  assumes "cov x Q G" "x \<in> fv Q" "finite (adom I)" "sat (Q \<^bold>\<bottom> x) I \<sigma>"
  shows "infinite (eval Q I)"
proof -
  let ?Q1 = "Conj Q (DISJ (qps G))"
  let ?Q2 = "DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G)"
  define Q3 where "Q3 = Conj (Q \<^bold>\<bottom> x) (Neg (Disj (DISJ (qps G)) (DISJ ((\<lambda>y. x \<approx> y) ` eqs x G))))"
  let ?Q = "Disj ?Q1 (Disj ?Q2 Q3)"
  from assms(1) have fv123: "fv ?Q1 \<subseteq> fv Q" "fv ?Q2 \<subseteq> fv Q" "fv Q3 \<subseteq> fv Q" and fin_fv[simp]: "finite (fv Q3)" unfolding Q3_def
    by (auto dest!: fv_cp[THEN set_mp] fv_DISJ[THEN set_mp, rotated 1] fv_erase[THEN set_mp]
      eqs_in qps_in cov_fv[OF assms(1,2)] simp: fv_subst simp del: cp.simps)
  then have fv: "fv ?Q \<subseteq> fv Q"
    by auto
  from assms(1,2,4) have sat: "sat Q3 I (\<sigma>(x := d))" if "d \<notin> adom I \<union> csts Q \<union> \<sigma> ` fv Q" for d
    using that cov_fv[OF assms(1,2) qps_in] cov_fv[OF assms(1,2) eqs_in, of _ x]
      qp_fresh_val[OF qps_qp, of _ G "\<sigma>(x := d)" x I] cov_csts[OF assms(1) qps_in]
    by (auto 5 2 simp: image_iff Q3_def elim!: sat_fv_cong[THEN iffD2, rotated -1]
      dest: fv_erase[THEN set_mp] dest: eqs_in)
  from assms(3) have inf: "infinite {d. d \<notin> adom I \<union> csts Q \<union> \<sigma> ` fv Q}"
    unfolding Compl_eq[symmetric] Compl_eq_Diff_UNIV
    by (intro Diff_infinite_finite) (auto simp: infinite_UNIV)
  { assume "x \<in> fv Q3"
    let ?f = "\<lambda>ds. lookup (sorted_list_of_set (fv Q)) ds x"
    from inf have "infinite (eval_on (fv Q) Q3 I)"
    proof (rule infinite_surj[where f="?f"], intro subsetI, elim CollectE)
      fix z
      assume "z \<notin> adom I \<union> csts Q \<union> \<sigma> ` fv Q"
      with \<open>x \<in> fv Q3\<close> fv123 sat show "z \<in> ?f ` eval_on (fv Q) Q3 I"
        by (auto simp: eval_on_def image_iff Let_def fun_upds_single subset_eq simp del: cp.simps
          intro!: exI[of _ \<sigma>] exI[of _ "map (\<sigma>(x := z)) (sorted_list_of_set (fv Q))"])
    qed
    then have "infinite (eval_on (fv Q) ?Q I)"
      by (rule contrapos_nn) (auto dest!: finite_eval_on_Disj2D[rotated])
  }
  moreover
  { assume x: "x \<notin> fv Q3"
    from inf obtain d where "d \<notin> adom I \<union> csts Q \<union> \<sigma> ` fv Q"
      by (meson not_finite_existsD)
    with fv123 sat[of d] assms(2) x have "infinite (eval_on (fv Q) (Disj (Disj ?Q1 ?Q2) Q3) I)"
      by (intro infinite_eval_on_Disj2[of _"fv Q" _ _ "(\<sigma>(x := d))"]) (auto simp del: cp.simps)
    moreover have "eval_on (fv Q) (Disj (Disj ?Q1 ?Q2) Q3) I = eval_on (fv Q) ?Q I"
      by (rule equiv_eval_on_eqI[OF assms(3) equiv_Disj_Assoc])
    ultimately have "infinite (eval_on (fv Q) ?Q I)"
      by simp
  }
  moreover have "eval Q I = eval_on (fv Q) ?Q I"
    unfolding Q3_def
    by (rule equiv_eval_on_eval_eqI[symmetric, OF assms(3) fv[unfolded Q3_def] cov_equiv[OF assms(1) refl, THEN equiv_sym]])
  ultimately show ?thesis
    by auto
qed

subsection \<open>More on Evaluation\<close>

lemma eval_Bool_False[simp]: "eval (Bool False) I = {}"
  by (auto simp: eval_deep_def)

lemma eval_on_False[simp]: "eval_on X (Bool False) I = {}"
  by (auto simp: eval_on_def)

lemma eval_DISJ_prune_unsat: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> \<forall>Q \<in> B - A. \<forall>\<sigma>. \<not> sat Q I \<sigma> \<Longrightarrow> eval_on X (DISJ A) I = eval_on X (DISJ B) I"
  by (auto simp: eval_on_def finite_subset)

lemma eval_DISJ: "finite \<Q> \<Longrightarrow> \<forall>Q \<in> \<Q>. fv Q = A \<Longrightarrow> eval_on A (DISJ \<Q>) I = (\<Union>Q \<in> \<Q>. eval Q I)"
  by (auto simp: eval_deep_def eval_on_def)

lemma eval_cp_DISJ_closed: "finite \<Q> \<Longrightarrow> \<forall>Q \<in> \<Q>. fv Q = {} \<Longrightarrow> eval (cp (DISJ \<Q>)) I = (\<Union>Q \<in> \<Q>. eval Q I)"
  using fv_DISJ[of \<Q>] fv_cp[of "DISJ \<Q>"] by (auto simp: eval_deep_def)

lemma (in simplification) eval_simp_DISJ_closed: "finite \<Q> \<Longrightarrow> \<forall>Q \<in> \<Q>. fv Q = {} \<Longrightarrow> eval (simp (DISJ \<Q>)) I = (\<Union>Q \<in> \<Q>. eval Q I)"
  using fv_DISJ[of \<Q>] fv_simp[of "DISJ \<Q>"] by (auto simp: eval_deep_def sat_simp)

lemma eval_cong: "fv Q = fv Q' \<Longrightarrow> (\<And>\<sigma>. sat Q I \<sigma> = sat Q' I \<sigma>) \<Longrightarrow> eval Q I = eval Q' I"
  by (auto simp: eval_deep_def)

lemma eval_on_cong: "(\<And>\<sigma>. sat Q I \<sigma> = sat Q' I \<sigma>) \<Longrightarrow> eval_on X Q I = eval_on X Q' I"
  by (auto simp: eval_on_def)

lemma eval_empty_alt: "eval Q I = {} \<longleftrightarrow> (\<forall>\<sigma>. \<not> sat Q I \<sigma>)"
proof (intro iffI allI)
  fix \<sigma>
  assume "eval Q I = {}"
  then show "\<not> sat Q I \<sigma>"
    by (auto simp: eval_deep_def fun_upds_map_self
      dest!: spec[of _ "map \<sigma> (sorted_list_of_set (fv Q))"] spec[of _ \<sigma>])
qed (auto simp: eval_deep_def)

lemma sat_EXISTS: "distinct xs \<Longrightarrow> sat (EXISTS xs Q) I \<sigma> = (\<exists>ds. length ds = length xs \<and> sat Q I (\<sigma>[xs :=\<^sup>* ds]))"
proof (induct xs arbitrary: Q \<sigma>)
  case (Cons x xs)
  then show ?case
    by (auto 0 3 simp: EXISTS_def length_Suc_conv fun_upds_twist fun_upd_def[symmetric])
qed (simp add: EXISTS_def)

lemma eval_empty_close: "eval (close Q) I = {} \<longleftrightarrow> (\<forall>\<sigma>. \<not> sat Q I \<sigma>)"
  by (subst eval_empty_alt)
    (auto simp: sat_EXISTS fun_upds_map_self dest: spec2[of _ \<sigma> "map \<sigma>(sorted_list_of_set (fv Q))" for \<sigma>])

lemma infinite_eval_on_extra_variables:
  assumes "finite X" "fv (Q :: ('a :: infinite, 'b) fmla) \<subset> X" "\<exists>\<sigma>. sat Q I \<sigma>"
  shows "infinite (eval_on X Q I)"
proof -
  from assms obtain x \<sigma> where "x \<in> X - fv Q" "fv Q \<subseteq> X" "sat Q I \<sigma>"
    by auto
  with assms(1) show ?thesis
    by (intro infinite_surj[OF infinite_UNIV, of "\<lambda>ds. ds ! index (sorted_list_of_set X) x"])
      (force simp: eval_on_def image_iff fun_upds_in
        elim!: sat_fv_cong[THEN iffD1, rotated]
        intro!: exI[of _ "map (\<lambda>y. if x = y then _ else \<sigma> y) (sorted_list_of_set X)"] exI[of _ \<sigma>])
qed

lemma eval_on_cp: "eval_on X (cp Q) = eval_on X Q"
  by (auto simp: eval_on_def)

lemma (in simplification) eval_on_simp: "eval_on X (simp Q) = eval_on X Q"
  by (auto simp: eval_on_def sat_simp)

lemma (in simplification) eval_simp_False: "eval (simp (Bool False)) I = {}"
  using fv_simp[of "Bool False"] by (auto simp: eval_deep_def sat_simp)

abbreviation "idx_of_var x Q \<equiv> index (sorted_list_of_set (fv Q)) x"

lemma evalE: "ds \<in> eval Q I \<Longrightarrow> (\<And>\<sigma>. length ds = card (fv Q) \<Longrightarrow> sat Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* ds]) \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding eval_deep_def by auto

lemma infinite_eval_Conj:
  assumes "x \<notin> fv Q" "infinite (eval Q I)"
  shows "infinite (eval (Conj Q (x \<approx> y)) I)"
    (is "infinite (eval ?Qxy I)")
proof (cases "x = y")
  case True
  let ?f = "remove_nth (idx_of_var x ?Qxy)"
  let ?g = "insert_nth (idx_of_var x ?Qxy) undefined"
  show ?thesis
    using assms(2)
  proof (elim infinite_surj[of _ ?f], intro subsetI, elim evalE)
    fix ds \<sigma>
    assume ds: "length ds = card (fv Q)" "sat Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* ds])"
    show "ds \<in> ?f ` eval ?Qxy I"
    proof (intro image_eqI[of _ _ "?g ds"])
      from ds assms(1) True show "ds = ?f (?g ds)"
        by (intro remove_nth_insert_nth[symmetric])
          (auto simp: less_Suc_eq_le[symmetric] set_insort_key)
    next
      from ds assms(1) True show "?g ds \<in> eval ?Qxy I"
        by (auto simp: eval_deep_def Let_def length_insert_nth distinct_insort set_insort_key fun_upds_in
          simp del: insert_nth_take_drop elim!: sat_fv_cong[THEN iffD1, rotated]
          intro!: exI[of _ \<sigma>] trans[OF _ insert_nth_nth_index[symmetric]])
    qed
  qed
next
  case xy: False
  show ?thesis
  proof (cases "y \<in> fv Q")
    case True
    let ?f = "remove_nth (idx_of_var x ?Qxy)"
    let ?g = "\<lambda>ds. insert_nth (idx_of_var x ?Qxy) (ds ! idx_of_var y Q) ds"
    from assms(2) show ?thesis
    proof (elim infinite_surj[of _ ?f], intro subsetI, elim evalE)
      fix ds \<sigma>
      assume ds: "length ds = card (fv Q)" "sat Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* ds])"
      show "ds \<in> ?f ` eval ?Qxy I"
      proof (intro image_eqI[of _ _ "?g ds"])
        from ds assms(1) True show "ds = ?f (?g ds)"
          by (intro remove_nth_insert_nth[symmetric])
            (auto simp: less_Suc_eq_le[symmetric] set_insort_key)
      next
        from assms(1) True have "remove1 x (insort y (sorted_list_of_set (insert x (fv Q) - {y}))) = sorted_list_of_set (fv Q)"
          by (metis Diff_insert_absorb finite_fv finite_insert insert_iff
              sorted_list_of_set.fold_insort_key.remove sorted_list_of_set.sorted_key_list_of_set_remove)
        moreover have "index (insort y (sorted_list_of_set (insert x (fv Q) - {y}))) x \<le> length ds"
          using ds(1) assms(1) True
          by (subst less_Suc_eq_le[symmetric]) (auto simp: set_insort_key intro: index_less_size)
        ultimately show "?g ds \<in> eval ?Qxy I"
          using  ds assms(1) True
          by (auto simp: eval_deep_def Let_def length_insert_nth distinct_insort set_insort_key fun_upds_in nth_insert_nth
            simp del: insert_nth_take_drop elim!: sat_fv_cong[THEN iffD1, rotated]
            intro!: exI[of _ \<sigma>] trans[OF _ insert_nth_nth_index[symmetric]])
      qed
    qed
  next
    case False
    let ?Qxx = "Conj Q (x \<approx> x)"
    let ?f = "remove_nth (idx_of_var x ?Qxx) o remove_nth (idx_of_var y ?Qxy)"
    let ?g1 = "insert_nth (idx_of_var y ?Qxy) undefined"
    let ?g2 = "insert_nth (idx_of_var x ?Qxx) undefined"
    let ?g = "?g1 o ?g2"
    from assms(2) show ?thesis
    proof (elim infinite_surj[of _ ?f], intro subsetI, elim evalE)
      fix ds \<sigma>
      assume ds: "length ds = card (fv Q)" "sat Q I (\<sigma>[sorted_list_of_set (fv Q) :=\<^sup>* ds])"
      then show "ds \<in> ?f ` eval ?Qxy I"
      proof (intro image_eqI[of _ _ "?g ds"])
        from ds assms(1) xy False show "ds = ?f (?g ds)"
          by (auto simp: less_Suc_eq_le[symmetric] set_insort_key index_less_size
            length_insert_nth remove_nth_insert_nth simp del: insert_nth_take_drop)
      next
        from ds(1) have "index (insort x (sorted_list_of_set (fv Q))) x \<le> length ds"
          by (auto simp: less_Suc_eq_le[symmetric] set_insort_key)
        moreover from ds(1) have "index (insort y (insort x (sorted_list_of_set (fv Q)))) y \<le> Suc (length ds)"
          by (auto simp: less_Suc_eq_le[symmetric] set_insort_key)
        ultimately show "?g ds \<in> eval ?Qxy I"
          using ds assms(1) xy False unfolding eval_deep_def Let_def
          by (auto simp: fun_upds_in distinct_insort set_insort_key length_insert_nth
            insert_nth_nth_index nth_insert_nth elim!: sat_fv_cong[THEN iffD1, rotated]
            intro!: exI[of _ \<sigma>] trans[OF _ insert_nth_nth_index[symmetric]] simp del: insert_nth_take_drop) []
      qed
    qed
  qed
    qed

lemma infinite_Implies_mono_on: "infinite (eval_on X Q I) \<Longrightarrow> finite X \<Longrightarrow> (\<And>\<sigma>. sat (Impl Q Q') I \<sigma>) \<Longrightarrow> infinite (eval_on X Q' I)"
  by (erule contrapos_nn, rule finite_subset[rotated]) (auto simp: eval_on_def image_iff)

(*<*)
end
(*>*)