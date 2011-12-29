theory Set_Monad
imports 
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

definition pred_of_set :: "'a set \<Rightarrow> 'a Predicate.pred"
  where [code del]: "pred_of_set = Predicate.Pred \<circ> (\<lambda>A x. Set.member x A)"

lemma eval_pred_of_set [simp]: "Predicate.eval (pred_of_set A) = (\<lambda>x. Set.member x A)"
  by(simp add: pred_of_set_def)

definition of_pred :: "'a Predicate.pred \<Rightarrow> 'a set"
  where "of_pred = Collect \<circ> Predicate.eval"

definition of_seq :: "'a Predicate.seq \<Rightarrow> 'a set"
  where "of_seq = of_pred \<circ> Predicate.pred_of_seq"

lemmas bind_def = Set.bind_def
lemmas bind_bind = Set.bind_bind
lemmas empty_bind = Set.empty_bind
lemmas bind_const = Set.bind_const

lemma member_SUPR: (* FIXME delete candidate: should be subsumed by default simpset as soon as SUP_apply is included *)
  "x \<in> UNION A f = (SUP B:A. (\<lambda>x. x \<in> f B)) x"
  by auto -- {* dangerous as simp rule: @{const UNION} is standard operation *}

definition single :: "'a \<Rightarrow> 'a set"
  where "single a = {a}"

definition undefined :: "'a set"
  where [simp]: "undefined = Collect HOL.undefined"

code_abort undefined

definition Undefined :: "unit \<Rightarrow> 'a set"
  where "Undefined _ = Collect HOL.undefined"

code_abort Undefined

lemma undefined_code [code_unfold]:
  "undefined = Undefined ()"
  by (simp add: Undefined_def)

lemma bind_single [simp, code_unfold]:
  "A \<guillemotright>= single = A"
  by (simp add: bind_def single_def)

lemma single_bind [simp, code_unfold]:
  "single a \<guillemotright>= B = B a"
  by (simp add: bind_def single_def)

declare Set.empty_bind [code_unfold]

lemma member_single [simp]:
  "x \<in> single a <-> x = a"
by (simp add: single_def)

lemma single_sup_simps [simp, code_unfold]:
  shows single_sup: "sup (single a) A = insert a A"
  and sup_single: "sup A (single a) = insert a A"
  by (unfold set_eq_iff) auto

lemma member_of_pred [simp]:
  "x \<in> of_pred P = Predicate.eval P x"
  by (simp add: of_pred_def)

lemma member_of_seq [simp]:
  "x \<in> of_seq xq = Predicate.member xq x"
  by (simp add: of_seq_def eval_member)

lemma of_pred_code [code]:
  "of_pred (Predicate.Seq f) = (case f () of
     Predicate.Empty \<Rightarrow> {}
   | Predicate.Insert x P \<Rightarrow> insert x (of_pred P)
   | Predicate.Join P xq \<Rightarrow> sup (of_pred P) (of_seq xq))"
   by (auto split: seq.split simp add: Predicate.Seq_def of_pred_def eval_member set_eq_iff)

lemma of_seq_code [code]:
  "of_seq Predicate.Empty = {}"
  "of_seq (Predicate.Insert x P) = insert x (of_pred P)"
  "of_seq (Predicate.Join P xq) = sup (of_pred P) (of_seq xq)"
  by (auto simp add: of_seq_def of_pred_def set_eq_iff)

lemma single_code [code]:
  "single a = set [a]"
  by (simp add: set_eq_iff)

lemma pred_of_cset_code [code]:
  "pred_of_set (set xs) = foldr sup (map Predicate.single xs) bot"
proof -
  have "pred_of_set (set xs) = Predicate.Pred (\<lambda>x. x \<in> set xs)"
    by (auto simp add: pred_of_set_def)
  moreover have "foldr sup (map Predicate.single xs) bot = \<dots>"
    by (induct xs) (auto simp add: bot_pred_def intro: pred_eqI)
  ultimately show ?thesis by simp
qed

end
