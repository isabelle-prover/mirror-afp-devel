(*  ID:         $Id: ListSum.thy,v 1.4 2007-06-24 20:26:09 nipkow Exp $
    Author:     Gertrud Bauer, Tobias Nipkow
*)

header "Summation Over Lists"

theory ListSum
imports ListAux
begin

consts ListSum :: "'b list \<Rightarrow> ('b \<Rightarrow> 'a::comm_monoid_add) \<Rightarrow> 'a::comm_monoid_add" 
primrec 
 "ListSum [] f = 0"
 "ListSum (l#ls) f = f l + ListSum ls f"

syntax "_ListSum" :: "idt \<Rightarrow> 'b list \<Rightarrow> ('a::comm_monoid_add) \<Rightarrow> 
  ('a::comm_monoid_add)"    ("\<Sum>\<^bsub>_\<in>_\<^esub> _")
translations "\<Sum>\<^bsub>x\<in>xs\<^esub> f" == "ListSum xs (\<lambda>x. f)" 

(* implementation on natural numbers *)
(* 1. nat list sum *)
consts natListSum :: "'b list \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> nat" 
primrec 
 "natListSum [] f = 0"
 "natListSum (l#ls) f = f l + natListSum ls f"

(* implementation on integers *)
(* 2. int list sum *)
consts intListSum :: "'b list \<Rightarrow> ('b \<Rightarrow> int) \<Rightarrow> int" 
primrec 
 "intListSum [] f = 0"
 "intListSum (l#ls) f = f l + intListSum ls f"



lemma [THEN eq_reflection, code unfold]: "((ListSum ls f)::nat) = natListSum ls f"
 by (induct ls) simp_all

lemma [THEN eq_reflection, code unfold]: "((ListSum ls f)::int) = intListSum ls f"
 by (induct ls) simp_all



lemma [simp]: "\<Sum>\<^bsub>v \<in> V\<^esub> 0 = (0::nat)" by (induct V) simp_all

lemma ListSum_compl1: 
  "(\<Sum>\<^bsub>x \<in> [x\<leftarrow>xs. \<not> P x]\<^esub> f x) + \<Sum>\<^bsub>x \<in> [x\<leftarrow>xs. P x]\<^esub> f x = \<Sum>\<^bsub>x \<in> xs\<^esub> (f x::nat)" 
 by (induct xs) simp_all

lemma ListSum_compl2: 
  "(\<Sum>\<^bsub>x \<in>  [x\<leftarrow>xs. P x]\<^esub> f x) + \<Sum>\<^bsub>x \<in>  [x\<leftarrow>xs. \<not> P x]\<^esub> f x = \<Sum>\<^bsub>x \<in> xs\<^esub> (f x::nat)" 
 by (induct xs) simp_all

lemmas ListSum_compl = ListSum_compl1 ListSum_compl2


lemma ListSum_conv_setsum:
 "distinct xs \<Longrightarrow> ListSum xs f =  setsum f (set xs)"
by(induct xs) simp_all


lemma listsum_cong:
 "\<lbrakk> xs = ys; \<And>y. y \<in> set ys ==> f y = g y \<rbrakk>
  \<Longrightarrow> ListSum xs f = ListSum ys g"
apply simp
apply(erule thin_rl)
by (induct ys) simp_all


lemma strong_listsum_cong[cong]:
 "\<lbrakk> xs = ys; \<And>y. y \<in> set ys =simp=> f y = g y \<rbrakk>
  \<Longrightarrow> ListSum xs f = ListSum ys g"
by(auto simp:simp_implies_def intro!:listsum_cong)


lemma ListSum_eq [trans]: 
  "(\<And>v. v \<in> set V \<Longrightarrow> f v = g v) \<Longrightarrow> \<Sum>\<^bsub>v \<in> V\<^esub> f v = \<Sum>\<^bsub>v \<in> V\<^esub> g v" 
by(auto intro!:listsum_cong)


lemma ListSum_set_eq: 
 "\<And>C. distinct B \<Longrightarrow> distinct C \<Longrightarrow> set B = set C \<Longrightarrow>
  \<Sum>\<^bsub>a \<in> B\<^esub> f a = \<Sum>\<^bsub>a \<in> C\<^esub> (f a::nat)"
  by (simp add: ListSum_conv_setsum)

lemma ListSum_disj_union: 
  "distinct A \<Longrightarrow> distinct B \<Longrightarrow> distinct C \<Longrightarrow> 
  set C = set A \<union> set B  \<Longrightarrow> 
  set A \<inter> set B = {} \<Longrightarrow>
  \<Sum>\<^bsub>a \<in> C\<^esub> (f a) = (\<Sum>\<^bsub>a \<in> A\<^esub> f a) + (\<Sum>\<^bsub>a \<in> B\<^esub> (f a::nat))"
  by (simp add: ListSum_conv_setsum setsum_Un_disjoint)


constdefs separating :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> bool"
  "separating V F \<equiv> 
   (\<forall>v1 \<in> V. \<forall>v2 \<in> V. v1 \<noteq> v2 \<longrightarrow>  F v1 \<inter> F v2 = {})"


lemma separating_insert1: 
  "separating (insert a V) F \<Longrightarrow> separating V F"
  by (simp add: separating_def)

lemma separating_insert2:
  "separating (insert a V) F \<Longrightarrow> a \<notin> V \<Longrightarrow>  v \<in> V \<Longrightarrow> 
  F a \<inter> F v = {}"
  by (auto simp add: separating_def)

lemma setsum_disj_Union: 
 "finite V \<Longrightarrow> 
  (\<And>f. finite (F f)) \<Longrightarrow> 
  separating V F \<Longrightarrow> 
  (\<Sum>v\<in>V. \<Sum>f\<in>(F v). (w f::nat)) = (\<Sum>f\<in>(\<Union>v\<in>V. F v). w f)"
proof (induct  rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert a V) 
  then have s: "separating (insert a V) F" by simp
  then have "separating V F" by (rule_tac separating_insert1)
  with insert
  have IH: "(\<Sum>v\<in>V. \<Sum>f\<in>(F v). w f) = (\<Sum>f\<in>(\<Union>v\<in>V. F v). w f)" 
    by simp

  moreover have prems: "finite V" "a \<notin> V" "\<And>f. finite (F f)" .

  moreover from s have "\<And>v. a \<notin> V \<Longrightarrow> v \<in> V \<Longrightarrow> F a \<inter> F v = {}"
   by (simp add: separating_insert2)
  with prems have "(F a) \<inter> (\<Union>v\<in>V. F v) = {}" by auto 

  ultimately show ?case by (simp add: setsum_Un_disjoint)
qed


lemma listsum_const[simp]: 
  "\<Sum>\<^bsub>x \<in> xs\<^esub> k = length xs * k"
by (induct xs) (simp_all add: ring_distribs)

lemma ListSum_add: 
  "(\<Sum>\<^bsub>x \<in> V\<^esub> f x) + \<Sum>\<^bsub>x \<in> V\<^esub> g x = \<Sum>\<^bsub>x \<in> V\<^esub> (f x + (g x::nat))" 
  by (induct V) auto

lemma ListSum_le: 
  "(\<And>v. v \<in> set V \<Longrightarrow> f v \<le> g v) \<Longrightarrow> \<Sum>\<^bsub>v \<in> V\<^esub> f v \<le> \<Sum>\<^bsub>v \<in> V\<^esub> (g v::nat)"
proof (induct V)
  case Nil then show ?case by simp
next
  case (Cons v V) then have "\<Sum>\<^bsub>v \<in> V\<^esub> f v \<le> \<Sum>\<^bsub>v \<in> V\<^esub> g v" by simp
  moreover from Cons have "f v \<le> g v" by simp
  ultimately show ?case by simp
qed

lemma ListSum1_bound:
 "a \<in> set F \<Longrightarrow> (d a::nat)  \<le> \<Sum>\<^bsub>f \<in> F\<^esub> d f"
by (induct F) auto

lemma ListSum2_bound:
  "a \<in> set F \<Longrightarrow> b \<in> set F \<Longrightarrow> a \<noteq> b \<Longrightarrow> d a + d b \<le> \<Sum>\<^bsub>f \<in> F\<^esub> (d f::nat)"
proof (induct F)
  case Nil then show ?case by simp
next
  case (Cons f F)
  then have "a = f \<or> a \<in> set F"  "b = f \<or> b \<in> set F" by simp_all
  then show ?case
  proof (elim disjE)
    assume "a = f"  "b = f" with Cons have False by simp
    then show ?thesis by simp
  next
    assume "a = f"  "b \<in> set F"
    with Cons show ?thesis by (simp add: ListSum1_bound)
  next
    assume "a \<in> set F" "b = f"
    with Cons show ?thesis by (simp add: ListSum1_bound)
  next
    assume "a \<in> set F" "b \<in> set F"
    with Cons have "d a + d b \<le> \<Sum>\<^bsub>f \<in> F\<^esub> d f" by simp
    then show ?thesis by simp
  qed
qed

end
