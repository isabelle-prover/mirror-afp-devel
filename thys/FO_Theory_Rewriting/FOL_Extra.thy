theory FOL_Extra
  imports
    Type_Instances_Impl
    "FOL-Fitting.FOL_Fitting"
    "HOL-Library.FSet"
begin

section \<open>Additional support for FOL-Fitting\<close>
subsection \<open>Iff\<close>

definition Iff where
  "Iff p q = And (Impl p q) (Impl q p)"

lemma eval_Iff:
  "eval e f g (Iff p q) \<longleftrightarrow> (eval e f g p \<longleftrightarrow> eval e f g q)"
  by (auto simp: Iff_def)


subsection \<open>Replacement of subformulas\<close>

datatype ('a, 'b) ctxt
  = Hole
  | And1 "('a, 'b) ctxt" "('a, 'b) form"
  | And2 "('a, 'b) form" "('a, 'b) ctxt"
  | Or1 "('a, 'b) ctxt" "('a, 'b) form"
  | Or2 "('a, 'b) form" "('a, 'b) ctxt"
  | Impl1 "('a, 'b) ctxt" "('a, 'b) form"
  | Impl2 "('a, 'b) form" "('a, 'b) ctxt"
  | Neg1 "('a, 'b) ctxt"
  | Forall1 "('a, 'b) ctxt"
  | Exists1 "('a, 'b) ctxt"

primrec apply_ctxt :: "('a, 'b) ctxt \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form" where
  "apply_ctxt Hole p = p"
| "apply_ctxt (And1 c v) p = And (apply_ctxt c p) v"
| "apply_ctxt (And2 u c) p = And u (apply_ctxt c p)"
| "apply_ctxt (Or1 c v) p = Or (apply_ctxt c p) v"
| "apply_ctxt (Or2 u c) p = Or u (apply_ctxt c p)"
| "apply_ctxt (Impl1 c v) p = Impl (apply_ctxt c p) v"
| "apply_ctxt (Impl2 u c) p = Impl u (apply_ctxt c p)"
| "apply_ctxt (Neg1 c) p = Neg (apply_ctxt c p)"
| "apply_ctxt (Forall1 c) p = Forall (apply_ctxt c p)"
| "apply_ctxt (Exists1 c) p = Exists (apply_ctxt c p)"

lemma replace_subformula:
  assumes "\<And>e. eval e f g (Iff p q)"
  shows "eval e f g (Iff (apply_ctxt c p) (apply_ctxt c q))"
  by (induct c arbitrary: e) (auto simp: assms[unfolded eval_Iff] Iff_def)


subsection \<open>Propositional identities\<close>

lemma prop_ids:
  "eval e f g (Iff (And p q) (And q p))"
  "eval e f g (Iff (Or p q) (Or q p))"
  "eval e f g (Iff (Or p (Or q r)) (Or (Or p q) r))"
  "eval e f g (Iff (And p (And q r)) (And (And p q) r))"
  "eval e f g (Iff (Neg (Or p q)) (And (Neg p) (Neg q)))"
  "eval e f g (Iff (Neg (And p q)) (Or (Neg p) (Neg q)))"
  (* ... *)
  by (auto simp: Iff_def)


subsection \<open>de Bruijn index manipulation for formulas; cf. @{term liftt}\<close>

primrec liftti :: "nat \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "liftti i (Var j) = (if i > j then Var j else Var (Suc j))"
| "liftti i (App f ts) = App f (map (liftti i) ts)"

lemma liftts_def':
  "liftts ts = map liftt ts"
  by (induct ts) auto

text \<open>@{term liftt} is a special case of @{term liftti}\<close>
lemma lifttti_0:
  "liftti 0 t = liftt t"
  by (induct t) (auto simp: liftts_def')

primrec lifti :: "nat \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form" where
  "lifti i FF = FF"
| "lifti i TT = TT"
| "lifti i (Pred b ts) = Pred b (map (liftti i) ts)"
| "lifti i (And p q) = And (lifti i p) (lifti i q)"
| "lifti i (Or p q) = Or (lifti i p) (lifti i q)"
| "lifti i (Impl p q) = Impl (lifti i p) (lifti i q)"
| "lifti i (Neg p) = Neg (lifti i p)"
| "lifti i (Forall p) = Forall (lifti (Suc i) p)"
| "lifti i (Exists p) = Exists (lifti (Suc i) p)"

abbreviation lift where
  "lift \<equiv> lifti 0"

text \<open>interaction of @{term lifti} and @{term eval}\<close>

lemma evalts_def':
  "evalts e f ts = map (evalt e f) ts"
  by (induct ts) auto

lemma evalt_liftti:
  "evalt (e\<langle>i:z\<rangle>) f (liftti i t) = evalt e f t"
  by (induct t) (auto simp: evalts_def' cong: map_cong)

lemma eval_lifti [simp]:
  "eval (e\<langle>i:z\<rangle>) f g (lifti i p) = eval e f g p"
  by (induct p arbitrary: e i) (auto simp: evalt_liftti evalts_def' comp_def)


subsection \<open>Quantifier Identities\<close>

lemma quant_ids:
  "eval e f g (Iff (Neg (Exists p)) (Forall (Neg p)))"
  "eval e f g (Iff (Neg (Forall p)) (Exists (Neg p)))"
  "eval e f g (Iff (And p (Forall q)) (Forall (And (lift p) q)))"
  "eval e f g (Iff (And p (Exists q)) (Exists (And (lift p) q)))"
  "eval e f g (Iff (Or p (Forall q)) (Forall (Or (lift p) q)))"
  "eval e f g (Iff (Or p (Exists q)) (Exists (Or (lift p) q)))"
  (* ... *)
  by (auto simp: Iff_def)

(* We'd need a bit of more machinery to deal with "\<forall>x y. P(x,y) \<longleftrightarrow> \<forall>y x. P(x, y)":
 * swapping of de Bruijn indices (perhaps arbitrary permutation?) *) 


subsection \<open>Function symbols and predicates, with arities.\<close>

primrec predas_form :: "('a, 'b) form \<Rightarrow> ('b \<times> nat) set" where
  "predas_form FF = {}"
| "predas_form TT = {}"
| "predas_form (Pred b ts) = {(b, length ts)}"
| "predas_form (And p q) = predas_form p \<union> predas_form q"
| "predas_form (Or p q) = predas_form p \<union> predas_form q"
| "predas_form (Impl p q) = predas_form p \<union> predas_form q"
| "predas_form (Neg p) = predas_form p"
| "predas_form (Forall p) = predas_form p"
| "predas_form (Exists p) = predas_form p"

primrec funas_term :: "'a term \<Rightarrow> ('a \<times> nat) set" where
  "funas_term (Var x) = {}"
| "funas_term (App f ts) = {(f, length ts)} \<union> \<Union>(set (map funas_term ts))"

primrec terms_form :: "('a, 'b) form \<Rightarrow> 'a term set" where
  "terms_form FF = {}"
| "terms_form TT = {}"
| "terms_form (Pred b ts) = set ts"
| "terms_form (And p q) = terms_form p \<union> terms_form q"
| "terms_form (Or p q) = terms_form p \<union> terms_form q"
| "terms_form (Impl p q) = terms_form p \<union> terms_form q"
| "terms_form (Neg p) = terms_form p"
| "terms_form (Forall p) = terms_form p"
| "terms_form (Exists p) = terms_form p"

definition funas_form :: "('a, 'b) form \<Rightarrow> ('a \<times> nat) set" where
  "funas_form f \<equiv> \<Union>(funas_term ` terms_form f)"


subsection \<open>Negation Normal Form\<close>

inductive is_nnf :: "('a, 'b) form \<Rightarrow> bool" where
  "is_nnf TT"
| "is_nnf FF"
| "is_nnf (Pred p ts)"
| "is_nnf (Neg (Pred p ts))"
| "is_nnf p \<Longrightarrow> is_nnf q \<Longrightarrow> is_nnf (And p q)"
| "is_nnf p \<Longrightarrow> is_nnf q \<Longrightarrow> is_nnf (Or p q)"
| "is_nnf p \<Longrightarrow> is_nnf (Forall p)"
| "is_nnf p \<Longrightarrow> is_nnf (Exists p)"

primrec nnf' :: "bool \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form" where
  "nnf' b TT          = (if b then TT else FF)"
| "nnf' b FF          = (if b then FF else TT)"
| "nnf' b (Pred p ts) = (if b then id else Neg) (Pred p ts)"
| "nnf' b (And p q)   = (if b then And else Or) (nnf' b p) (nnf' b q)"
| "nnf' b (Or p q)    = (if b then Or else And) (nnf' b p) (nnf' b q)"
| "nnf' b (Impl p q)  = (if b then Or else And) (nnf' (\<not> b) p) (nnf' b q)"
| "nnf' b (Neg p)     = nnf' (\<not> b) p"
| "nnf' b (Forall p)  = (if b then Forall else Exists) (nnf' b p)"
| "nnf' b (Exists p)  = (if b then Exists else Forall) (nnf' b p)"

lemma eval_nnf':
  "eval e f g (nnf' b p) \<longleftrightarrow> (eval e f g p \<longleftrightarrow> b)"
  by (induct p arbitrary: e b) auto

lemma is_nnf_nnf':
  "is_nnf (nnf' b p)"
  by (induct p arbitrary: b) (auto intro: is_nnf.intros)

abbreviation nnf where
  "nnf \<equiv> nnf' True"

lemmas nnf_simpls [simp] = eval_nnf'[where b = True, unfolded eq_True] is_nnf_nnf'[where b = True]


subsection \<open>Reasoning modulo ACI01\<close>

datatype ('a, 'b) form_aci
  = TT_aci
  | FF_aci
  | Pred_aci bool 'b "'a term list"
  | And_aci "('a, 'b) form_aci fset"
  | Or_aci "('a, 'b) form_aci fset"
  | Forall_aci "('a, 'b) form_aci"
  | Exists_aci "('a, 'b) form_aci"

text \<open>evaluation, see @{const eval}\<close>

primrec eval_aci :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow>
  ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow> ('a, 'b) form_aci \<Rightarrow> bool\<close> where
  "eval_aci e f g FF_aci            \<longleftrightarrow> False"
| "eval_aci e f g TT_aci            \<longleftrightarrow> True"
| "eval_aci e f g (Pred_aci b a ts) \<longleftrightarrow> (g a (evalts e f ts) \<longleftrightarrow> b)"
| "eval_aci e f g (And_aci ps)      \<longleftrightarrow> fBall (fimage (eval_aci e f g) ps) id"
| "eval_aci e f g (Or_aci ps)       \<longleftrightarrow> fBex (fimage (eval_aci e f g) ps) id"
| "eval_aci e f g (Forall_aci p)    \<longleftrightarrow> (\<forall>z. eval_aci (e\<langle>0:z\<rangle>) f g p)"
| "eval_aci e f g (Exists_aci p)    \<longleftrightarrow> (\<exists>z. eval_aci (e\<langle>0:z\<rangle>) f g p)"

text \<open>smart constructor: conjunction\<close>

fun and_aci where
  "and_aci FF_aci       _            = FF_aci"
| "and_aci _            FF_aci       = FF_aci"
| "and_aci TT_aci       q            = q"
| "and_aci p            TT_aci       = p"
| "and_aci (And_aci ps) (And_aci qs) = And_aci (ps |\<union>| qs)"
| "and_aci (And_aci ps) q            = And_aci (ps |\<union>| {|q|})"
| "and_aci p            (And_aci qs) = And_aci ({|p|} |\<union>| qs)"
| "and_aci p            q            = (if p = q then p else And_aci {|p,q|})"

lemma eval_and_aci [simp]:
  "eval_aci e f g (and_aci p q) \<longleftrightarrow> eval_aci e f g p \<and> eval_aci e f g q"
  by (cases "(p, q)" rule: and_aci.cases) (simp_all add: ball_Un, meson+)

declare and_aci.simps [simp del]

text \<open>smart constructor: disjunction\<close>

fun or_aci where
  "or_aci TT_aci       _            = TT_aci"
| "or_aci _            TT_aci       = TT_aci"
| "or_aci FF_aci       q            = q"
| "or_aci p            FF_aci       = p"
| "or_aci (Or_aci ps)  (Or_aci qs)  = Or_aci (ps |\<union>| qs)"
| "or_aci (Or_aci ps)  q            = Or_aci (ps |\<union>| {|q|})"
| "or_aci p            (Or_aci qs)  = Or_aci ({|p|} |\<union>| qs)"
| "or_aci p            q            = (if p = q then p else Or_aci {|p,q|})"

lemma eval_or_aci [simp]:
  "eval_aci e f g (or_aci p q) \<longleftrightarrow> eval_aci e f g p \<or> eval_aci e f g q"
  by (cases "(p, q)" rule: or_aci.cases) (simp_all add: bex_Un, meson+)

declare or_aci.simps [simp del]

text \<open>convert negation normal form to ACIU01 normal form\<close>

fun nnf_to_aci :: "('a, 'b) form \<Rightarrow> ('a, 'b) form_aci" where
  "nnf_to_aci FF                = FF_aci"
| "nnf_to_aci TT                = TT_aci"
| "nnf_to_aci (Pred b ts)       = Pred_aci True b ts"
| "nnf_to_aci (Neg (Pred b ts)) = Pred_aci False b ts"
| "nnf_to_aci (And p q)         = and_aci (nnf_to_aci p) (nnf_to_aci q)"
| "nnf_to_aci (Or p q)          = or_aci (nnf_to_aci p) (nnf_to_aci q)"
| "nnf_to_aci (Forall p)        = Forall_aci (nnf_to_aci p)"
| "nnf_to_aci (Exists p)        = Exists_aci (nnf_to_aci p)"
| "nnf_to_aci _                 = undefined" (* the remaining cases are impossible for NNFs *)

lemma eval_nnf_to_aci:
  "is_nnf p \<Longrightarrow> eval_aci e f g (nnf_to_aci p) \<longleftrightarrow> eval e f g p"
  by (induct p arbitrary: e rule: is_nnf.induct) simp_all


subsection \<open>A (mostly) Propositional Equivalence Check\<close>

text \<open>We reason modulo $\forall = \neg\exists\neg$, de Morgan, double negation, and
  ACUI01 of $\vee$ and $\wedge$, by converting to negation normal form, and then collapsing
  conjunctions and disjunctions taking units, absorption, commutativity, associativity, and
  idempotence into account. We only need soundness for a certifier.\<close>

lemma check_equivalence_by_nnf_aci:
  "nnf_to_aci (nnf p) = nnf_to_aci (nnf q) \<Longrightarrow> eval e f g p \<longleftrightarrow> eval e f g q"
  by (metis eval_nnf_to_aci is_nnf_nnf' eval_nnf')


subsection \<open>Reasoning modulo ACI01\<close>

datatype ('a, 'b) form_list_aci
  = TT_aci
  | FF_aci
  | Pred_aci bool 'b "'a term list"
  | And_aci "('a, 'b) form_list_aci list"
  | Or_aci "('a, 'b) form_list_aci list"
  | Forall_aci "('a, 'b) form_list_aci"
  | Exists_aci "('a, 'b) form_list_aci"

text \<open>evaluation, see @{const eval}\<close>

fun eval_list_aci :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow>
  ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow> ('a, 'b) form_list_aci \<Rightarrow> bool\<close> where
  "eval_list_aci e f g FF_aci            \<longleftrightarrow> False"
| "eval_list_aci e f g TT_aci            \<longleftrightarrow> True"
| "eval_list_aci e f g (Pred_aci b a ts) \<longleftrightarrow> (g a (evalts e f ts) \<longleftrightarrow> b)"
| "eval_list_aci e f g (And_aci ps)      \<longleftrightarrow> list_all (\<lambda> fm. eval_list_aci e f g fm) ps"
| "eval_list_aci e f g (Or_aci ps)       \<longleftrightarrow> list_ex (\<lambda> fm. eval_list_aci e f g fm) ps"
| "eval_list_aci e f g (Forall_aci p)    \<longleftrightarrow> (\<forall>z. eval_list_aci (e\<langle>0:z\<rangle>) f g p)"
| "eval_list_aci e f g (Exists_aci p)    \<longleftrightarrow> (\<exists>z. eval_list_aci (e\<langle>0:z\<rangle>) f g p)"

text \<open>smart constructor: conjunction\<close>

fun and_list_aci where
  "and_list_aci FF_aci       _            = FF_aci"
| "and_list_aci _            FF_aci       = FF_aci"
| "and_list_aci TT_aci       q            = q"
| "and_list_aci p            TT_aci       = p"
| "and_list_aci (And_aci ps) (And_aci qs) = And_aci (remdups (ps @ qs))"
| "and_list_aci (And_aci ps) q            = And_aci (List.insert q ps)"
| "and_list_aci p            (And_aci qs) = And_aci (List.insert p qs)"
| "and_list_aci p            q            = (if p = q then p else And_aci [p,q])"

lemma eval_and_list_aci [simp]:
  "eval_list_aci e f g (and_list_aci p q) \<longleftrightarrow> eval_list_aci e f g p \<and> eval_list_aci e f g q"
  apply (cases "(p, q)" rule: and_list_aci.cases)
  apply (simp_all add: list.pred_set list_ex_iff)
  apply blast+
  done

declare and_list_aci.simps [simp del]

text \<open>smart constructor: disjunction\<close>

fun or_list_aci where
  "or_list_aci TT_aci       _            = TT_aci"
| "or_list_aci _            TT_aci       = TT_aci"
| "or_list_aci FF_aci       q            = q"
| "or_list_aci p            FF_aci       = p"
| "or_list_aci (Or_aci ps)  (Or_aci qs)  = Or_aci (remdups (ps @ qs))"
| "or_list_aci (Or_aci ps)  q            = Or_aci (List.insert q ps)"
| "or_list_aci p            (Or_aci qs)  = Or_aci (List.insert p qs)"
| "or_list_aci p            q            = (if p = q then p else Or_aci [p,q])"

lemma eval_or_list_aci [simp]:
  "eval_list_aci e f g (or_list_aci p q) \<longleftrightarrow> eval_list_aci e f g p \<or> eval_list_aci e f g q"
  by (cases "(p, q)" rule: or_list_aci.cases) (simp_all add: list.pred_set list_ex_iff, blast+)

declare or_list_aci.simps [simp del]

text \<open>convert negation normal form to ACIU01 normal form\<close>

fun nnf_to_list_aci :: "('a, 'b) form \<Rightarrow> ('a, 'b) form_list_aci" where
  "nnf_to_list_aci FF                = FF_aci"
| "nnf_to_list_aci TT                = TT_aci"
| "nnf_to_list_aci (Pred b ts)       = Pred_aci True b ts"
| "nnf_to_list_aci (Neg (Pred b ts)) = Pred_aci False b ts"
| "nnf_to_list_aci (And p q)         = and_list_aci (nnf_to_list_aci p) (nnf_to_list_aci q)"
| "nnf_to_list_aci (Or p q)          = or_list_aci (nnf_to_list_aci p) (nnf_to_list_aci q)"
| "nnf_to_list_aci (Forall p)        = Forall_aci (nnf_to_list_aci p)"
| "nnf_to_list_aci (Exists p)        = Exists_aci (nnf_to_list_aci p)"
| "nnf_to_list_aci _                 = undefined" (* the remaining cases are impossible for NNFs *)

lemma eval_nnf_to_list_aci:
  "is_nnf p \<Longrightarrow> eval_list_aci e f g (nnf_to_list_aci p) \<longleftrightarrow> eval e f g p"
  by (induct p arbitrary: e rule: is_nnf.induct) simp_all

subsection \<open>A (mostly) Propositional Equivalence Check\<close>

text \<open>We reason modulo $\forall = \neg\exists\neg$, de Morgan, double negation, and
  ACUI01 of $\vee$ and $\wedge$, by converting to negation normal form, and then collapsing
  conjunctions and disjunctions taking units, absorption, commutativity, associativity, and
  idempotence into account. We only need soundness for a certifier.\<close>

derive linorder "term"
derive compare "term"
derive linorder form_list_aci
derive compare form_list_aci

fun ord_form_list_aci where
  "ord_form_list_aci TT_aci = TT_aci"
| "ord_form_list_aci FF_aci = FF_aci"
| "ord_form_list_aci (Pred_aci bool b ts) = Pred_aci bool b ts"
| "ord_form_list_aci (And_aci fm) = (And_aci (sort (map ord_form_list_aci fm)))"
| "ord_form_list_aci (Or_aci fm) = (Or_aci (sort (map ord_form_list_aci fm)))"
| "ord_form_list_aci (Forall_aci fm) = (Forall_aci (ord_form_list_aci fm))"
| "ord_form_list_aci (Exists_aci fm) = Exists_aci (ord_form_list_aci fm)"

lemma and_list_aci_simps:
  "and_list_aci TT_aci q = q"
  "and_list_aci q FF_aci = FF_aci"
  by (cases q, auto simp add: and_list_aci.simps)+

lemma ord_form_list_idemp:
  "ord_form_list_aci (ord_form_list_aci q) = ord_form_list_aci q"
  apply (induct q) apply (auto simp: list.set_map)
  apply (smt imageE list.set_map map_idI set_sort sorted_sort_id sorted_sort_key)+
  done

lemma eval_lsit_aci_ord_form_list_aci:
  "eval_list_aci e f g (ord_form_list_aci p) \<longleftrightarrow> eval_list_aci e f g p"
  by (induct p arbitrary: e) (auto simp: list.pred_set list_ex_iff)

lemma check_equivalence_by_nnf_sortedlist_aci:
  "ord_form_list_aci (nnf_to_list_aci (nnf p)) = ord_form_list_aci (nnf_to_list_aci (nnf q)) \<Longrightarrow> eval e f g p \<longleftrightarrow> eval e f g q"
  by (metis eval_nnf_to_list_aci eval_lsit_aci_ord_form_list_aci is_nnf_nnf' eval_nnf')

hide_type (open) "term"
hide_const (open) Var
hide_type (open) ctxt

end