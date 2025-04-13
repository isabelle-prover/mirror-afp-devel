subsection\<open>Sublists\<close>

theory SubList
  imports
    "HOL-Library.Sublist"
    "HOL-Library.Multiset"
begin

lemmas subseq_trans = subseq_order.order_trans

lemma subseq_Cons_Cons: 
  assumes "subseq (a # as) (b # bs)"
  shows "subseq as bs"
  using assms by (cases "a = b") (auto intro: subseq_Cons')

lemma subseq_induct2:
  "\<lbrakk> subseq xs ys;
  \<And> bs. P [] bs;
  \<And> a as bs. \<lbrakk> subseq as bs; P as bs \<rbrakk> \<Longrightarrow> P (a # as) (a # bs);
  \<And> a as b bs. \<lbrakk> a \<noteq> b; subseq as bs; subseq (a # as) bs; P as bs; P (a # as) bs \<rbrakk> \<Longrightarrow> P (a # as) (b # bs) \<rbrakk>
  \<Longrightarrow> P xs ys" 
proof (induct ys arbitrary: xs)
  case Nil then show ?case by (metis list_emb_Nil2)
next
  case (Cons y ys')
  note Cons_ys = Cons
  note sl = Cons(2)
  note step_eq = Cons(4)
  note step_neq = Cons(5)
  show ?case proof (cases xs) 
    case Nil show ?thesis unfolding Nil using Cons.prems(2) by auto
  next
    case (Cons x xs') 
    have sl': "subseq xs' ys'" by (metis Cons sl subseq_Cons_Cons)
    from sl' have P': "P xs' ys'" using Cons_ys by auto
    show ?thesis proof (cases "x = y")
      case False 
      have sl'': "subseq (x # xs') ys'" using sl unfolding Cons using False by auto
      then have P'': "P (x # xs') ys'" by (metis Cons.hyps Cons_ys(3) step_eq step_neq)
      show ?thesis using step_neq[OF False sl' sl'' P' P''] unfolding Cons by auto
    next
      case True 
      show ?thesis using step_eq[OF sl' P'] unfolding Cons True[symmetric] by auto
    qed
  qed
qed

lemma subseq_submultiset:
  "subseq xs ys \<Longrightarrow> mset xs \<subseteq># mset ys"
  by (induct rule: list_emb.induct) (auto intro: subset_mset.order_trans)

lemma subseq_subset:
  "subseq xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (induct rule: list_emb.induct) auto

lemma remove1_subseq:
  "subseq (remove1 x xs) xs"
  by (induct xs) auto

lemma subseq_concat:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> subseq (f x) (g x)"
  shows "subseq (concat (map f xs)) (concat (map g xs))"
  using assms by (induct xs) (auto intro: list_emb_append_mono)

end