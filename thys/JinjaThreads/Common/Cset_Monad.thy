theory Cset_Monad imports 
  "List_Cset"
  "~~/src/HOL/Library/Monad_Syntax"
begin

definition pred_of_cset :: "'a Cset.set \<Rightarrow> 'a Predicate.pred"
where [code del]: "pred_of_cset = Predicate.Pred \<circ> Cset.member"

lemma eval_pred_of_cset [simp]: "Predicate.eval (pred_of_cset A) = Cset.member A"
by(simp add: pred_of_cset_def)

(* Use locale context to obtain a Cset. prefix: should use proper name spaces instead *)
locale Cset begin

definition bind :: "'a Cset.set \<Rightarrow> ('a \<Rightarrow> 'b Cset.set) \<Rightarrow> 'b Cset.set" (infixl "\<guillemotright>=" 70)
where "A \<guillemotright>= f = Cset.Set (\<Union>x \<in> member A. member (f x))"

definition single :: "'a \<Rightarrow> 'a Cset.set"
where "single a = Cset.Set {a}"

definition of_pred :: "'a Predicate.pred \<Rightarrow> 'a Cset.set"
where "of_pred = Cset.Set \<circ> Predicate.eval"

definition of_seq :: "'a Predicate.seq \<Rightarrow> 'a Cset.set"
where "of_seq = of_pred \<circ> Predicate.pred_of_seq"

definition undefined :: "'a Cset.set"
where [simp]: "undefined = Cset.Set HOL.undefined"

definition Undefined :: "unit \<Rightarrow> 'a Cset.set"
where [code]: "Undefined _ = Cset.Set HOL.undefined"

lemma bind_bind:
  "(A \<guillemotright>= B) \<guillemotright>= C = A \<guillemotright>= (\<lambda>x. B x \<guillemotright>= C)"
by(simp add: bind_def)

lemma bind_single [simp]:
  "A \<guillemotright>= single = A"
by(simp add: bind_def single_def)

lemma single_bind [simp]:
  "single a \<guillemotright>= B = B a"
by(simp add: bind_def single_def)

lemma member_SUPR [simp]:
  "member (SUPR A f) = SUPR A (member \<circ> f)"
unfolding SUP_def by simp

lemma member_bind [simp]:
  "member (P \<guillemotright>= f) = member (SUPR (member P) f)"
by (simp add: bind_def Cset.set_eq_iff)

lemma member_single [simp]:
  "member (single a) = {a}"
by(simp add: single_def)

lemma bind_const: "A \<guillemotright>= (\<lambda>_. B) = (if Cset.is_empty A then Cset.empty else B)"
by(auto simp add: Cset.set_eq_iff)

lemma single_sup_simps [simp]:
  shows single_sup: "sup (single a) A = Cset.insert a A"
  and sup_single: "sup A (single a) = Cset.insert a A"
by(auto simp add: Cset.set_eq_iff)

lemma empty_bind [simp]:
  "Cset.empty \<guillemotright>= f = Cset.empty"
by(simp add: Cset.set_eq_iff)

lemma member_of_pred [simp]:
  "member (of_pred P) = {x. Predicate.eval P x}"
by(simp add: of_pred_def Collect_def)

lemma member_of_seq [simp]:
  "member (of_seq xq) = {x. Predicate.member xq x}"
by(simp add: of_seq_def eval_member)

lemma of_pred_code:
  "of_pred (Predicate.Seq f) = (case f () of
     Predicate.Empty \<Rightarrow> Cset.empty
   | Predicate.Insert x P \<Rightarrow> Cset.insert x (of_pred P)
   | Predicate.Join P xq \<Rightarrow> sup (of_pred P) (of_seq xq))"
by(auto split: seq.split simp add: Predicate.Seq_def of_pred_def eval_member Cset.set_eq_iff)

lemma of_seq_code:
  "of_seq Predicate.Empty = Cset.empty"
  "of_seq (Predicate.Insert x P) = Cset.insert x (of_pred P)"
  "of_seq (Predicate.Join P xq) = sup (of_pred P) (of_seq xq)"
by(auto simp add: of_seq_def of_pred_def Cset.set_eq_iff)

lemma undefined_code:
  "undefined = Undefined ()"
by(simp add: Undefined_def)

no_notation bind (infixl "\<guillemotright>=" 70)

end

setup {*
  Adhoc_Overloading.add_variant @{const_name bind} @{const_name Cset.bind}
*}

declare
  Cset.bind_single [simp, code_unfold]
  Cset.single_bind [simp, code_unfold]
  Cset.member_SUPR [simp]
  Cset.member_bind [simp]
  Cset.member_single [simp]
  Cset.single_sup_simps [simp, code_unfold]
  Cset.empty_bind [simp, code_unfold]
  Cset.member_of_pred [simp]
  Cset.member_of_seq [simp]
  Cset.of_pred_code [code]
  Cset.of_seq_code [code]
  Cset.undefined_def [simp]
  Cset.undefined_code [code_unfold]

code_abort Cset.Undefined

locale List_Cset begin

lemma single_code:
  "Cset.single a = Cset.set [a]"
by(simp add: Cset.single_def Cset.set_def)

lemma bind_code:
  "(Cset.set xs) \<guillemotright>= f = foldl (\<lambda>A x. sup A (f x)) (Cset.set []) xs"
apply(rule sym)
apply(induct xs rule: rev_induct)
apply(auto simp add: Cset.bind_def Cset.set_def)
done

lemma pred_of_cset_code: 
  "pred_of_cset (Cset.set xs) = foldr sup (map Predicate.single xs) bot"
proof -
  have "pred_of_cset (Cset.set xs) = Predicate.Pred (\<lambda>x. x \<in> set xs)"
    by(auto simp add: pred_of_cset_def mem_def)
  moreover have "foldr sup (map Predicate.single xs) bot = \<dots>"
    by(induct xs)(auto simp add: bot_pred_def intro: pred_eqI, simp add: mem_def)
  ultimately show ?thesis by(simp)
qed

end

declare
  List_Cset.single_code [code]
  List_Cset.bind_code [code]
  List_Cset.pred_of_cset_code [code]

end