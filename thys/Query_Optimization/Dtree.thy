(* Author: Bernhard Stöckl *)

theory Dtree
  imports Complex_Main "Directed_Tree_Additions" "HOL-Library.FSet"
begin

section \<open>Algebraic Type for Directed Trees\<close>

datatype (dverts:'a, darcs: 'b) dtree = Node (root: 'a) (sucs: "(('a,'b) dtree \<times> 'b) fset")

subsection \<open>Termination Proofs\<close>

lemma fset_sum_ge_elem: "finite xs \<Longrightarrow> x \<in> xs \<Longrightarrow> (\<Sum>u\<in>xs. (f::'a \<Rightarrow> nat) u) \<ge> f x"
  by (simp add: sum_nonneg_leq_bound)

lemma dtree_size_decr_aux:
  assumes "(x,y) \<in> fset xs"
  shows "size x < size (Node r xs)"
proof -
  have 0: "((x,size x),y) \<in> (map_prod (\<lambda>u. (u, size u)) (\<lambda>u. u)) ` fset xs" using assms by fast
  have "size x < Suc (size_prod snd (\<lambda>_. 0) ((x,size x),y))" by simp
  also have
    "\<dots> \<le> (\<Sum>u\<in>(map_prod (\<lambda>x. (x, size x)) (\<lambda>y. y)) ` fset xs. Suc (size_prod snd (\<lambda>_. 0) u)) + 1"
    using fset_sum_ge_elem 0 finite_fset finite_imageI
    by (metis (mono_tags, lifting) add_increasing2 zero_le_one)
  finally show ?thesis by simp
qed

lemma dtree_size_decr_aux': "t1 \<in> fst ` fset xs \<Longrightarrow> size t1 < size (Node r xs)"
  using dtree_size_decr_aux by fastforce

lemma dtree_size_decr[termination_simp]:
  assumes "(x, y) \<in> fset (xs:: (('a, 'b) dtree \<times> 'b) fset)"
  shows "size x < Suc (\<Sum>u\<in>map_prod (\<lambda>x. (x, size x)) (\<lambda>y. y) ` fset xs. Suc (Suc (snd (fst u))))"
proof -
  let ?xs = "(map_prod (\<lambda>x. (x, size x)) (\<lambda>y. y)) ` fset xs"
  have "size x < (\<Sum>u\<in>?xs. Suc (size_prod snd (\<lambda>_. 0) u)) + 1"
    using dtree_size_decr_aux assms by fastforce
  also have "\<dots> = Suc (\<Sum>u\<in>?xs. Suc (Suc (snd (fst u))))" by (simp add: size_prod_simp)
  finally show ?thesis by blast
qed

subsection "Dtree Basic Functions"

fun darcs_mset :: "('a,'b) dtree \<Rightarrow> 'b multiset" where
  "darcs_mset (Node r xs) = (\<Sum>(t,e) \<in> fset xs. {#e#} + darcs_mset t)"

fun dverts_mset :: "('a,'b) dtree \<Rightarrow> 'a multiset" where
  "dverts_mset (Node r xs) = {#r#} + (\<Sum>(t,e) \<in> fset xs. dverts_mset t)"

(* disjoint_darcs & wf_darcs' are old definitions equivalent to wf_darcs; still used for proofs *)
abbreviation disjoint_darcs :: "(('a,'b) dtree \<times> 'b) fset \<Rightarrow> bool" where
  "disjoint_darcs xs \<equiv> (\<forall>(x,e1) \<in> fset xs. e1 \<notin> darcs x \<and> (\<forall>(y,e2) \<in> fset xs.
    (darcs x \<union> {e1}) \<inter> (darcs y \<union> {e2}) = {} \<or> (x,e1)=(y,e2)))"

fun wf_darcs' :: "('a,'b) dtree \<Rightarrow> bool" where
  "wf_darcs' (Node r xs) = (disjoint_darcs xs \<and> (\<forall>(x,e) \<in> fset xs. wf_darcs' x))"

definition wf_darcs :: "('a,'b) dtree \<Rightarrow> bool" where
  "wf_darcs t = (\<forall>x \<in># darcs_mset t. count (darcs_mset t) x = 1)"

(* same here as with wf_darcs' *)
fun wf_dverts' :: "('a,'b) dtree \<Rightarrow> bool" where
  "wf_dverts' (Node r xs) = (\<forall>(x,e1) \<in> fset xs.
    r \<notin> dverts x \<and> (\<forall>(y,e2) \<in> fset xs. (dverts x \<inter> dverts y = {} \<or> (x,e1)=(y,e2))) \<and> wf_dverts' x)"

definition wf_dverts :: "('a,'b) dtree \<Rightarrow> bool" where
  "wf_dverts t = (\<forall>x \<in># dverts_mset t. count (dverts_mset t) x = 1)"

fun dtail :: "('a,'b) dtree \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a" where
  "dtail (Node r xs) def = (\<lambda>e. if e \<in> snd ` fset xs then r
    else (ffold (\<lambda>(x,e2) b.
      if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
      then b else dtail x def) def xs) e)"
 (* (x,y) \<in> fset case required for termination proof (always fulfilled)
    disjointness requirement for commutativity  *)

fun dhead :: "('a,'b) dtree \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a" where
  "dhead (Node r xs) def = (\<lambda>e. (ffold (\<lambda>(x,e2) b.
      if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs)
      then b else if e=e2 then root x else dhead x def e) (def e) xs))"

abbreviation from_dtree :: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a,'b) dtree \<Rightarrow> ('a,'b) pre_digraph" where
  "from_dtree deft defh t \<equiv>
    \<lparr>verts = dverts t, arcs = darcs t, tail = dtail t deft, head = dhead t defh\<rparr>"

abbreviation from_dtree' :: "('a,'b) dtree \<Rightarrow> ('a,'b) pre_digraph" where
  "from_dtree' t \<equiv> from_dtree (\<lambda>_. root t) (\<lambda>_. root t) t"

fun is_subtree :: "('a,'b) dtree \<Rightarrow> ('a,'b) dtree \<Rightarrow> bool" where
  "is_subtree x (Node r xs) =
    (x = Node r xs \<or> (\<exists>(y,e) \<in> fset xs. is_subtree x y))"

definition strict_subtree :: "('a,'b) dtree \<Rightarrow> ('a,'b) dtree \<Rightarrow> bool" where
  "strict_subtree t1 t2 \<longleftrightarrow> is_subtree t1 t2 \<and> t1 \<noteq> t2"

fun num_leaves :: "('a,'b) dtree \<Rightarrow> nat" where
  "num_leaves (Node r xs) = (if xs = {||} then 1 else (\<Sum>(t,e)\<in> fset xs. num_leaves t))"

subsection "Dtree Basic Proofs"

lemma finite_dverts: "finite (dverts t)"
  by(induction t) auto

lemma finite_darcs: "finite (darcs t)"
  by(induction t) auto

lemma dverts_child_subseteq: "x \<in> fst ` fset xs \<Longrightarrow> dverts x \<subseteq> dverts (Node r xs)"
  by fastforce

lemma dverts_suc_subseteq: "x \<in> fst ` fset (sucs t) \<Longrightarrow> dverts x \<subseteq> dverts t"
  using dverts_child_subseteq[of x "sucs t" "root t"] by simp

lemma dverts_root_or_child: "v \<in> dverts (Node r xs) \<Longrightarrow> v = r \<or> v \<in> (\<Union>(t,e) \<in> fset xs. dverts t)"
  by auto

lemma dverts_root_or_suc: "v \<in> dverts t \<Longrightarrow> v = root t \<or> (\<exists>(t,e) \<in> fset (sucs t).v \<in> dverts t)"
  using dverts_root_or_child[of v "root t" "sucs t"] by auto

lemma dverts_child_if_not_root:
  "\<lbrakk>v \<in> dverts (Node r xs); v \<noteq> r\<rbrakk> \<Longrightarrow> \<exists>t\<in>fst ` fset xs. v \<in> dverts t"
  by force

lemma dverts_suc_if_not_root:
  "\<lbrakk>v \<in> dverts t; v \<noteq> root t\<rbrakk> \<Longrightarrow> \<exists>t\<in>fst ` fset (sucs t). v \<in> dverts t"
  using dverts_root_or_suc by force

lemma darcs_child_subseteq: "x \<in> fst ` fset xs \<Longrightarrow> darcs x \<subseteq> darcs (Node r xs)"
  by force

lemma mset_sum_elem: "x \<in># (\<Sum>y \<in> fset Y. f y) \<Longrightarrow> \<exists>y \<in> fset Y. x \<in># f y"
  by (induction Y) auto

lemma mset_sum_elem_iff: "x \<in># (\<Sum>y \<in> fset Y. f y) \<longleftrightarrow> (\<exists>y \<in> fset Y. x \<in># f y)"
  by (induction Y) auto

lemma mset_sum_elemI: "\<lbrakk>y \<in> fset Y; x \<in># f y\<rbrakk> \<Longrightarrow> x \<in># (\<Sum>y \<in> fset Y. f y)"
  by (induction Y) auto

lemma darcs_mset_elem:
  "x \<in># darcs_mset (Node r xs) \<Longrightarrow> \<exists>(t,e) \<in> fset xs. x \<in># darcs_mset t \<or> x = e"
  using mset_sum_elem by fastforce

lemma darcs_mset_if_nsnd:
  "\<lbrakk>x \<in># darcs_mset (Node r xs); x \<notin> snd ` fset xs\<rbrakk> \<Longrightarrow> \<exists>(t1,e1) \<in> fset xs. x \<in># darcs_mset t1"
  using darcs_mset_elem[of x r xs] by force

lemma darcs_mset_suc_if_nsnd:
  "\<lbrakk>x \<in># darcs_mset t; x \<notin> snd ` fset (sucs t)\<rbrakk> \<Longrightarrow> \<exists>(t1,e1) \<in> fset (sucs t). x \<in># darcs_mset t1"
  using darcs_mset_if_nsnd[of x "root t" "sucs t"] by simp

lemma darcs_mset_if_nchild:
  "\<lbrakk>x \<in># darcs_mset (Node r xs); \<nexists>t1 e1. (t1,e1) \<in> fset xs \<and> x \<in># darcs_mset t1\<rbrakk>
    \<Longrightarrow> x \<in> snd ` fset xs"
  using mset_sum_elem by force

lemma darcs_mset_if_nsuc:
  "\<lbrakk>x \<in># darcs_mset t; \<nexists>t1 e1. (t1,e1) \<in> fset (sucs t) \<and> x \<in># darcs_mset t1\<rbrakk>
    \<Longrightarrow> x \<in> snd ` fset (sucs t)"
  using darcs_mset_if_nchild[of x "root t" "sucs t"] by simp

lemma darcs_mset_if_snd[intro]: "x \<in> snd ` fset xs \<Longrightarrow> x \<in># darcs_mset (Node r xs)"
  by (induction xs) auto

lemma darcs_mset_suc_if_snd[intro]: "x \<in> snd ` fset (sucs t) \<Longrightarrow> x \<in># darcs_mset t"
  using darcs_mset_if_snd[of x "sucs t" "root t"] by simp

lemma darcs_mset_if_child[intro]:
  "\<lbrakk>(t1,e1) \<in> fset xs; x \<in># darcs_mset t1\<rbrakk> \<Longrightarrow> x \<in># darcs_mset (Node r xs)"
  by (induction xs) auto

lemma darcs_mset_if_suc[intro]:
  "\<lbrakk>(t1,e1) \<in> fset (sucs t); x \<in># darcs_mset t1\<rbrakk> \<Longrightarrow> x \<in># darcs_mset t"
  using darcs_mset_if_child[of t1 e1 "sucs t" x "root t"] by simp

lemma darcs_mset_sub_darcs: "set_mset (darcs_mset t) \<subseteq> darcs t"
proof(standard, induction t rule: darcs_mset.induct)
  case (1 r xs)
  then show ?case
  proof(cases "x \<in> snd ` fset xs")
    case False
    then obtain t1 e1 where "(t1,e1) \<in> fset xs \<and> x \<in># darcs_mset t1"
      using "1.prems" darcs_mset_if_nsnd[of x r] by blast
    then show ?thesis using "1.IH" by force
  qed(force)
qed

lemma darcs_sub_darcs_mset: "darcs t \<subseteq> set_mset (darcs_mset t)"
proof(standard, induction t rule: darcs_mset.induct)
  case (1 r xs)
  then show ?case
  proof(cases "x \<in> snd ` fset xs")
    case False
    then obtain t1 e1 where "(t1,e1) \<in> fset xs \<and> x \<in> darcs t1"
      using "1.prems" by force
    then show ?thesis using "1.IH" by blast
  qed(blast)
qed

lemma darcs_mset_eq_darcs[simp]: "set_mset (darcs_mset t) = darcs t"
  using darcs_mset_sub_darcs darcs_sub_darcs_mset by force

lemma dverts_mset_elem:
  "x \<in># dverts_mset (Node r xs) \<Longrightarrow> (\<exists>(t,e) \<in> fset xs. x \<in># dverts_mset t) \<or> x = r"
  using mset_sum_elem by fastforce

lemma dverts_mset_if_nroot:
  "\<lbrakk>x \<in># dverts_mset (Node r xs); x \<noteq> r\<rbrakk> \<Longrightarrow> \<exists>(t1,e1) \<in> fset xs. x \<in># dverts_mset t1"
  using dverts_mset_elem[of x r xs] by blast

lemma dverts_mset_suc_if_nroot:
  "\<lbrakk>x \<in># dverts_mset t; x \<noteq> root t\<rbrakk> \<Longrightarrow> \<exists>(t1,e1) \<in> fset (sucs t). x \<in># dverts_mset t1"
  using dverts_mset_if_nroot[of x "root t" "sucs t"] by simp

lemma dverts_mset_if_nchild:
  "\<lbrakk>x \<in># dverts_mset (Node r xs); \<nexists>t1 e1. (t1,e1) \<in> fset xs \<and> x \<in># dverts_mset t1\<rbrakk> \<Longrightarrow> x = r"
  using mset_sum_elem by force

lemma dverts_mset_if_nsuc:
  "\<lbrakk>x \<in># dverts_mset t; \<nexists>t1 e1. (t1,e1) \<in> fset (sucs t) \<and> x \<in># dverts_mset t1\<rbrakk> \<Longrightarrow> x = root t"
  using dverts_mset_if_nchild[of x "root t" "sucs t"] by simp

lemma dverts_mset_if_root[intro]: "x = r \<Longrightarrow> x \<in># dverts_mset (Node r xs)"
  by simp

lemma dverts_mset_suc_if_root[intro]: "x = root t \<Longrightarrow> x \<in># dverts_mset t"
  using dverts_mset_if_root[of x "root t" "sucs t"] by simp

lemma dverts_mset_if_child[intro]:
  "\<lbrakk>(t1,e1) \<in> fset xs; x \<in># dverts_mset t1\<rbrakk> \<Longrightarrow> x \<in># dverts_mset (Node r xs)"
  by (induction xs) auto

lemma dverts_mset_if_suc[intro]:
  "\<lbrakk>(t1,e1) \<in> fset (sucs t); x \<in># dverts_mset t1\<rbrakk> \<Longrightarrow> x \<in># dverts_mset t"
  using dverts_mset_if_child[of t1 e1 "sucs t" x "root t"] by simp

lemma dverts_mset_sub_dverts: "set_mset (dverts_mset t) \<subseteq> dverts t"
proof(standard, induction t)
  case (Node r xs)
  then show ?case
  proof(cases "x = r")
    case False
    then obtain t1 e1 where "(t1,e1) \<in> fset xs \<and> x \<in># dverts_mset t1"
      using Node.prems dverts_mset_if_nroot by fast
    then show ?thesis using Node.IH by fastforce
  qed(simp)
qed

lemma dverts_sub_dverts_mset: "dverts t \<subseteq> set_mset (dverts_mset t)"
proof(standard, induction t rule: dverts_mset.induct)
  case (1 r xs)
  then show ?case
  proof(cases "x = r")
    case False
    then obtain t1 e1 where "(t1,e1) \<in> fset xs \<and> x \<in> dverts t1"
      using "1.prems" by force
    then show ?thesis using "1.IH" by blast
  qed(simp)
qed

lemma dverts_mset_eq_dverts[simp]: "set_mset (dverts_mset t) = dverts t"
  using dverts_mset_sub_dverts dverts_sub_dverts_mset by force

lemma mset_sum_count_le: "y \<in> fset Y \<Longrightarrow> count (f y) x \<le> count (\<Sum>y \<in> fset Y. f y) x"
  by (induction Y) auto

lemma darcs_mset_alt:
  "darcs_mset (Node r xs) = (\<Sum>(t,e) \<in> fset xs. {#e#}) + (\<Sum>(t,e) \<in> fset xs. darcs_mset t)"
  by (induction xs) auto

lemma darcs_mset_ge_child:
  "t1 \<in> fst ` fset xs \<Longrightarrow> count (darcs_mset t1) x \<le> count (darcs_mset (Node r xs)) x"
  by (induction xs) force+

lemma darcs_mset_ge_suc:
  "t1 \<in> fst ` fset (sucs t) \<Longrightarrow> count (darcs_mset t1) x \<le> count (darcs_mset t) x"
  using darcs_mset_ge_child[of t1 "sucs t" x "root t"] by simp

lemma darcs_mset_count_sum_aux:
  "(\<Sum>(t1,e1) \<in> fset xs. count (darcs_mset t1) x) = count ((\<Sum>(t,e) \<in> fset xs. darcs_mset t)) x"
  by (smt (verit, ccfv_SIG) count_add_mset count_sum  multi_self_add_other_not_self
      prod.case prod.case_distrib split_cong sum.cong)

lemma darcs_mset_count_sum_aux0:
  "x \<notin> snd ` fset xs \<Longrightarrow> count ((\<Sum>(t, e)\<in>fset xs. {#e#})) x = 0"
  by (induction xs) auto

lemma darcs_mset_count_sum_eq:
  "x \<notin> snd ` fset xs
    \<Longrightarrow> (\<Sum>(t1,e1) \<in> fset xs. count (darcs_mset t1) x) = count (darcs_mset (Node r xs)) x"
  unfolding darcs_mset_alt using darcs_mset_count_sum_aux darcs_mset_count_sum_aux0 by fastforce

lemma darcs_mset_count_sum_ge:
  "(\<Sum>(t1,e1) \<in> fset xs. count (darcs_mset t1) x) \<le> count (darcs_mset (Node r xs)) x"
  by (induction xs) (auto split: prod.splits)

lemma wf_darcs_alt: "wf_darcs t \<longleftrightarrow> (\<forall>x. count (darcs_mset t) x \<le> 1)"
  unfolding wf_darcs_def by (metis count_greater_eq_one_iff dual_order.eq_iff linorder_le_cases)

lemma disjoint_darcs_simp:
  "\<lbrakk>(t1,e1) \<in> fset xs; (t2,e2) \<in> fset xs; (t1,e1) \<noteq> (t2,e2); disjoint_darcs xs\<rbrakk>
    \<Longrightarrow> (darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
  by fast

lemma disjoint_darcs_single: "e \<notin> darcs t \<longleftrightarrow> disjoint_darcs {|(t,e)|}"
  by simp

lemma disjoint_darcs_insert: "disjoint_darcs (finsert x xs) \<Longrightarrow> disjoint_darcs xs"
  by simp fast

lemma wf_darcs_rec[dest]:
  assumes "wf_darcs (Node r xs)" and "t1 \<in> fst ` fset xs"
  shows "wf_darcs t1"
unfolding wf_darcs_def proof (rule ccontr)
  assume asm: "\<not> (\<forall>x \<in># darcs_mset t1. count (darcs_mset t1) x = 1)"
  then obtain x where x_def: "x \<in># darcs_mset t1" "count (darcs_mset t1) x \<noteq> 1"
    by blast
  then have "count (darcs_mset t1) x > 1" by (simp add: order_le_neq_trans)
  then have "count (darcs_mset (Node r xs)) x > 1"
    using assms(2) darcs_mset_ge_child[of t1 xs x] by simp
  moreover have "x \<in># (darcs_mset (Node r xs))"
    using x_def(1) assms(2) by fastforce
  ultimately show False using assms(1) unfolding wf_darcs_def by simp
qed

lemma disjoint_darcs_if_wf_aux1: "\<lbrakk>wf_darcs (Node r xs); (t1,e1) \<in> fset xs\<rbrakk> \<Longrightarrow> e1 \<notin> darcs t1"
  apply (induction xs)
   apply(auto simp: wf_darcs_def split: if_splits prod.splits)[2]
  by (metis UnI2 add_is_1 count_eq_zero_iff)

lemma fset_sum_ge_elem2:
  "\<lbrakk>x \<in> fset X; y \<in> fset X; x \<noteq> y\<rbrakk> \<Longrightarrow> (f :: 'a \<Rightarrow> nat) x + f y \<le> (\<Sum>x \<in> fset X. f x)"
  by (induction X) (auto simp: fset_sum_ge_elem)

lemma darcs_children_count_ge2_aux:
  assumes "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)"
      and "e \<in> darcs t1" and "e \<in> darcs t2"
    shows "(\<Sum>(t1, e1)\<in>fset xs. count (darcs_mset t1) e) \<ge> 2"
proof -
  have "2 \<le> 1 + count (darcs_mset t2) e"
    using assms(2,5) by simp
  also have "\<dots> \<le> count (darcs_mset t1) e + count (darcs_mset t2) e"
    using assms(1,4) by simp
  finally show ?thesis
    using fset_sum_ge_elem2[OF assms(1-3), of "\<lambda>(t1,e1). count (darcs_mset t1) e"] by simp
qed

lemma darcs_children_count_ge2:
  assumes "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)"
      and "e \<in> darcs t1" and "e \<in> darcs t2"
    shows "count (darcs_mset (Node r xs)) e \<ge> 2"
  using darcs_children_count_ge2_aux[OF assms] darcs_mset_count_sum_ge dual_order.trans by fast

lemma darcs_children_count_not1:
  "\<lbrakk>(t1,e1) \<in> fset xs; (t2,e2) \<in> fset xs; (t1,e1) \<noteq> (t2,e2); e \<in> darcs t1; e \<in> darcs t2\<rbrakk>
    \<Longrightarrow> count (darcs_mset (Node r xs)) e \<noteq> 1"
  using darcs_children_count_ge2 by fastforce

lemma disjoint_darcs_if_wf_aux2:
  assumes "wf_darcs (Node r xs)"
      and "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)"
    shows "darcs t1 \<inter> darcs t2 = {}"
proof(rule ccontr)
  assume "darcs t1 \<inter> darcs t2 \<noteq> {}"
  then obtain e where e_def: "e \<in> darcs t1" "e \<in> darcs t2" by blast
  then have "e \<in> darcs (Node r xs)" using assms(2) by force
  then have "e \<in># darcs_mset (Node r xs)" using darcs_mset_eq_darcs by fast
  then show False
    using darcs_children_count_ge2[OF assms(2-4) e_def] assms(1) unfolding wf_darcs_def by simp
qed

lemma darcs_child_count_ge1:
  "\<lbrakk>(t1,e1) \<in> fset xs; e2 \<in> darcs t1\<rbrakk> \<Longrightarrow> count (\<Sum>(t, e)\<in>fset xs. darcs_mset t) e2 \<ge> 1"
  by (simp add: mset_sum_elemI)

lemma darcs_snd_count_ge1:
  "(t2,e2) \<in> fset xs \<Longrightarrow> count (\<Sum>(t, e)\<in>fset xs. {#e#}) e2 \<ge> 1"
  by (simp add: mset_sum_elemI)

lemma darcs_child_count_ge2:
  "\<lbrakk>(t1,e1) \<in> fset xs; (t2,e2) \<in> fset xs; e2 \<in> darcs t1\<rbrakk> \<Longrightarrow> count (darcs_mset (Node r xs)) e2 \<ge> 2"
  unfolding darcs_mset_alt
  by (metis darcs_child_count_ge1 darcs_snd_count_ge1 add_mono count_union one_add_one)

lemma disjoint_darcs_if_wf_aux3:
  assumes "wf_darcs (Node r xs)" and "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs"
  shows "e2 \<notin> darcs t1"
proof
  assume asm: "e2 \<in> darcs t1"
  then have "e2 \<in> darcs (Node r xs)" using assms(2) by force
  then have "e2 \<in># darcs_mset (Node r xs)" using darcs_mset_eq_darcs by fast
  then show False using darcs_child_count_ge2 asm assms(1-3) unfolding wf_darcs_def by fastforce
qed

lemma darcs_snds_count_ge2_aux:
  assumes "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)" and "e1 = e2"
  shows "count (\<Sum>(t, e)\<in>fset xs. {#e#}) e2 \<ge> 2"
using assms proof(induction xs)
  case (insert x xs)
  then consider "x = (t1,e1)" | "x = (t2,e2)" | "(t1,e1) \<in> fset xs" "(t2,e2) \<in> fset xs" by auto
  then show ?case
  proof(cases)
    case 1
    then have "count (\<Sum>(t, e)\<in>fset xs. {#e#}) e2 \<ge> 1"
      using insert.prems(2,3) darcs_snd_count_ge1 by auto
    then show ?thesis using insert.prems(4) insert.hyps 1 by auto
  next
    case 2
    then have "count (\<Sum>(t, e)\<in>fset xs. {#e#}) e2 \<ge> 1"
      using insert.prems(1,3,4) darcs_snd_count_ge1 by auto
    then show ?thesis using insert.prems(4) insert.hyps 2 by auto
  next
    case 3
    then show ?thesis using insert.IH insert.prems(3,4) insert.hyps by auto
  qed
qed(simp)

lemma darcs_snds_count_ge2:
  "\<lbrakk>(t1,e1) \<in> fset xs; (t2,e2) \<in> fset xs; (t1,e1) \<noteq> (t2,e2); e1 = e2\<rbrakk>
    \<Longrightarrow> count (darcs_mset (Node r xs)) e2 \<ge> 2"
  using darcs_snds_count_ge2_aux unfolding darcs_mset_alt by fastforce

lemma disjoint_darcs_if_wf_aux4:
  assumes "wf_darcs (Node r xs)"
      and "(t1,e1) \<in> fset xs"
      and "(t2,e2) \<in> fset xs"
      and "(t1,e1) \<noteq> (t2,e2)"
    shows "e1 \<noteq> e2"
proof
  assume asm: "e1 = e2"
  have "e2 \<in># darcs_mset (Node r xs)" using assms(3) darcs_mset_if_snd by fastforce
  then show False
    using assms(1) darcs_snds_count_ge2[OF assms(2-4) asm] unfolding wf_darcs_def by simp
qed

lemma disjoint_darcs_if_wf_aux5:
  "\<lbrakk>wf_darcs (Node r xs); (t1,e1) \<in> fset xs; (t2,e2) \<in> fset xs; (t1,e1) \<noteq> (t2,e2)\<rbrakk>
    \<Longrightarrow>(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
  by (auto dest: disjoint_darcs_if_wf_aux4 disjoint_darcs_if_wf_aux3 disjoint_darcs_if_wf_aux2)

lemma disjoint_darcs_if_wf_xs: "wf_darcs (Node r xs) \<Longrightarrow> disjoint_darcs xs"
  by (auto dest: disjoint_darcs_if_wf_aux1 disjoint_darcs_if_wf_aux5)

lemma disjoint_darcs_if_wf: "wf_darcs t \<Longrightarrow> disjoint_darcs (sucs t)"
  using disjoint_darcs_if_wf_xs[of "root t" "sucs t"] by simp

lemma wf_darcs'_if_darcs: "wf_darcs t \<Longrightarrow> wf_darcs' t"
proof(induction t)
  case (Node r xs)
  then show ?case using disjoint_darcs_if_wf_xs[OF Node.prems] by fastforce
qed

lemma wf_darcs_if_darcs'_aux:
  "\<lbrakk>\<forall>(x,e) \<in> fset xs. wf_darcs x; disjoint_darcs xs\<rbrakk> \<Longrightarrow> wf_darcs (Node r xs)"
  apply(simp split: prod.splits)
  apply(induction xs)
   apply(auto simp: wf_darcs_def count_eq_zero_iff)[2]
  by (fastforce dest: mset_sum_elem)+

lemma wf_darcs_if_darcs': "wf_darcs' t \<Longrightarrow> wf_darcs t"
proof(induction t)
  case (Node r xs)
  then show ?case using wf_darcs_if_darcs'_aux[of xs] by fastforce
qed

corollary wf_darcs_iff_darcs': "wf_darcs t \<longleftrightarrow> wf_darcs' t"
  using wf_darcs_if_darcs' wf_darcs'_if_darcs by blast

lemma disjoint_darcs_subset:
  assumes "xs |\<subseteq>| ys" and "disjoint_darcs ys"
  shows "disjoint_darcs xs"
proof (rule ccontr)
  assume "\<not> disjoint_darcs xs"
  then obtain x e1 y e2 where x_def: "(x,e1) \<in> fset xs" "(y,e2) \<in> fset xs"
      "e1 \<in> darcs x \<or> (darcs x \<union> {e1}) \<inter> (darcs y \<union> {e2}) \<noteq> {} \<and> (x,e1)\<noteq>(y,e2)"
    by blast
  have "(x,e1) \<in> fset ys" "(y,e2) \<in> fset ys" using x_def(1,2) assms(1) less_eq_fset.rep_eq by fast+
  then show False using assms(2) x_def(3) by fast
qed

lemma disjoint_darcs_img:
  assumes "disjoint_darcs xs" and "\<forall>(t,e) \<in> fset xs. darcs (f t) \<subseteq> darcs t"
  shows "disjoint_darcs ((\<lambda>(t,e). (f t,e)) |`| xs)" (is "disjoint_darcs ?xs")
proof (rule ccontr)
  assume "\<not> disjoint_darcs ?xs"
  then obtain x1 e1 y1 e2 where asm: "(x1,e1) \<in> fset ?xs" "(y1,e2) \<in> fset ?xs"
      "e1 \<in> darcs x1 \<or> (darcs x1 \<union> {e1}) \<inter> (darcs y1 \<union> {e2}) \<noteq> {} \<and> (x1,e1)\<noteq>(y1,e2)"
    by blast
  then obtain x2 where x2_def: "f x2 = x1" "(x2,e1) \<in> fset xs" by auto
  obtain y2 where y2_def: "f y2 = y1" "(y2,e2) \<in> fset xs" using asm(2) by auto
  have "darcs x1 \<subseteq> darcs x2" using assms(2) x2_def by fast
  moreover have "darcs y1 \<subseteq> darcs y2" using assms(2) y2_def by fast
  ultimately have "\<not> disjoint_darcs xs" using asm(3) x2_def y2_def by fast
  then show False using assms(1) by blast
qed

lemma dverts_mset_count_sum_ge:
  "(\<Sum>(t1,e1) \<in> fset xs. count (dverts_mset t1) x) \<le> count (dverts_mset (Node r xs)) x"
  by (induction xs) auto

lemma dverts_children_count_ge2_aux:
  assumes "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)"
      and "x \<in> dverts t1" and "x \<in> dverts t2"
    shows "(\<Sum>(t1, e1)\<in>fset xs. count (dverts_mset t1) x) \<ge> 2"
proof -
  have "2 \<le> count (dverts_mset t1) x + 1" using assms(4) by simp
  also have "\<dots> \<le> count (dverts_mset t1) x + count (dverts_mset t2) x" using assms(5) by simp
  finally show ?thesis
    using fset_sum_ge_elem2[OF assms(1-3), of "\<lambda>(t1,e1). count (dverts_mset t1) x"] by simp
qed

lemma dverts_children_count_ge2:
  assumes "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)"
      and "x \<in> dverts t1" and "x \<in> dverts t2"
    shows "count (dverts_mset (Node r xs)) x \<ge> 2"
  using dverts_children_count_ge2_aux[OF assms] dverts_mset_count_sum_ge le_trans by fast

lemma disjoint_dverts_if_wf_aux:
  assumes "wf_dverts (Node r xs)"
      and "(t1,e1) \<in> fset xs" and "(t2,e2) \<in> fset xs" and "(t1,e1) \<noteq> (t2,e2)"
    shows "dverts t1 \<inter> dverts t2 = {}"
proof (rule ccontr)
  assume "dverts t1 \<inter> dverts t2 \<noteq> {}"
  then obtain x where x_def: "x \<in> dverts t1" "x \<in> dverts t2" by blast
  then have "2 \<le> count (dverts_mset (Node r xs)) x"
    using dverts_children_count_ge2[OF assms(2-4)] by blast
  moreover have "x \<in># (dverts_mset (Node r xs))" using assms(2) x_def(1) by fastforce
  ultimately show False using assms(1) unfolding wf_dverts_def by fastforce
qed

lemma disjoint_dverts_if_wf:
  "wf_dverts (Node r xs)
    \<Longrightarrow> \<forall>(x,e1) \<in> fset xs. \<forall>(y,e2) \<in> fset xs. (dverts x \<inter> dverts y = {} \<or> (x,e1)=(y,e2))"
  using disjoint_dverts_if_wf_aux by fast

lemma disjoint_dverts_if_wf_sucs:
  "wf_dverts t
    \<Longrightarrow> \<forall>(x,e1) \<in> fset (sucs t). \<forall>(y,e2) \<in> fset (sucs t).
          (dverts x \<inter> dverts y = {} \<or> (x,e1)=(y,e2))"
  using disjoint_dverts_if_wf[of "root t" "sucs t"] by simp

lemma dverts_child_count_ge1:
  "\<lbrakk>(t1,e1) \<in> fset xs; x \<in> dverts t1\<rbrakk> \<Longrightarrow> count (\<Sum>(t, e)\<in>fset xs. dverts_mset t) x \<ge> 1"
  by (simp add: mset_sum_elemI)

lemma root_not_child_if_wf_dverts: "\<lbrakk>wf_dverts (Node r xs); (t1,e1) \<in> fset xs\<rbrakk> \<Longrightarrow> r \<notin> dverts t1"
  by (fastforce dest: dverts_child_count_ge1 simp: wf_dverts_def)

lemma root_not_child_if_wf_dverts': "wf_dverts (Node r xs) \<Longrightarrow> \<forall>(t1,e1) \<in> fset xs. r \<notin> dverts t1"
  by (fastforce dest: dverts_child_count_ge1 simp: wf_dverts_def)

lemma dverts_mset_ge_child:
  "t1 \<in> fst ` fset xs \<Longrightarrow> count (dverts_mset t1) x \<le> count (dverts_mset (Node r xs)) x"
  by (induction xs) force+

lemma wf_dverts_rec[dest]:
  assumes "wf_dverts (Node r xs)" and "t1 \<in> fst ` fset xs"
  shows "wf_dverts t1"
unfolding wf_dverts_def proof (rule ccontr)
  assume asm: "\<not> (\<forall>x \<in># dverts_mset t1. count (dverts_mset t1) x = 1)"
  then obtain x where x_def: "x \<in># dverts_mset t1" "count (dverts_mset t1) x \<noteq> 1"
    by blast
  then have "count (dverts_mset t1) x > 1" by (simp add: order_le_neq_trans)
  then have "count (dverts_mset (Node r xs)) x > 1"
    using assms(2) dverts_mset_ge_child[of t1 xs x r] by simp
  moreover have "x \<in># (dverts_mset (Node r xs))"
    using x_def(1) assms(2) by fastforce
  ultimately show False using assms(1) unfolding wf_dverts_def by fastforce
qed

lemma wf_dverts'_if_dverts: "wf_dverts t \<Longrightarrow> wf_dverts' t"
proof(induction t)
  case (Node r xs)
  then have "\<forall>(x,e1)\<in>fset xs. wf_dverts' x" by auto
  then show ?case
    using disjoint_dverts_if_wf[OF Node.prems] root_not_child_if_wf_dverts'[OF Node.prems]
    by fastforce
qed

lemma wf_dverts_if_dverts'_aux:
  "\<lbrakk>\<forall>(x,e) \<in> fset xs. wf_dverts x;
    \<forall>(x,e1) \<in> fset xs. r \<notin> dverts x \<and> (\<forall>(y,e2) \<in> fset xs.
      (dverts x \<inter> dverts y = {} \<or> (x,e1)=(y,e2)))\<rbrakk>
    \<Longrightarrow> wf_dverts (Node r xs)"
  apply(simp split: prod.splits)
  apply(induction xs)
   apply(auto simp: wf_dverts_def count_eq_zero_iff)[2]
  by (fastforce dest: mset_sum_elem)+

lemma wf_dverts_if_dverts': "wf_dverts' t \<Longrightarrow> wf_dverts t"
proof(induction t)
  case (Node r xs)
  then show ?case using wf_dverts_if_dverts'_aux[of xs] by fastforce
qed

corollary wf_dverts_iff_dverts': "wf_dverts t \<longleftrightarrow> wf_dverts' t"
  using wf_dverts_if_dverts' wf_dverts'_if_dverts by blast

lemma wf_dverts_sub:
  assumes "xs |\<subseteq>| ys" and "wf_dverts (Node r ys)"
  shows "wf_dverts (Node r xs)"
proof -
  have "ys |\<union>| xs = ys" using assms(1) by blast
  then have "wf_dverts (Node r (ys |\<union>| xs))" using assms(2) by simp
  then show ?thesis unfolding wf_dverts_iff_dverts' by fastforce
qed

lemma count_subset_le:
  "xs |\<subseteq>| ys \<Longrightarrow> count (\<Sum>x \<in> fset xs. f x) a \<le> count (\<Sum>x \<in> fset ys. f x) a"
proof(induction ys arbitrary: xs)
  case (insert y ys)
  then show ?case
  proof(cases "y |\<in>| xs")
    case True
    then obtain xs' where xs'_def: "finsert y xs' = xs" "y |\<notin>| xs'"
      by blast
    then have "xs' |\<subseteq>| ys" using insert.prems by blast
    have "count (\<Sum>x \<in> fset xs. f x) a = count (\<Sum>x \<in> fset xs'. f x) a + count (f y) a"
      using xs'_def by auto
    also have "\<dots> \<le> count (\<Sum>x \<in> fset ys. f x) a + count (f y) a"
      using \<open>xs' |\<subseteq>| ys\<close> insert.IH by simp
    also have "\<dots> = count (\<Sum>x \<in> fset (finsert y ys). f x) a"
      using insert.hyps by auto
    finally show ?thesis .
  next
    case False
    then have "count (\<Sum>x \<in> fset xs. f x) a \<le> count (\<Sum>x \<in> fset ys. f x) a"
      using insert.prems insert.IH by blast
    then show ?thesis using insert.hyps by auto
  qed
qed(simp)

lemma darcs_mset_count_le_subset:
  "xs |\<subseteq>| ys \<Longrightarrow> count (darcs_mset (Node r' xs)) x \<le> count (darcs_mset (Node r ys)) x"
  using count_subset_le by fastforce

lemma wf_darcs_sub: "\<lbrakk>xs |\<subseteq>| ys; wf_darcs (Node r' ys)\<rbrakk> \<Longrightarrow> wf_darcs (Node r xs)"
  unfolding wf_darcs_def using darcs_mset_count_le_subset
  by (smt (verit, best) count_greater_eq_one_iff le_trans verit_la_disequality)

lemma wf_darcs_sucs: "\<lbrakk>wf_darcs t; x \<in> fset (sucs t)\<rbrakk> \<Longrightarrow> wf_darcs (Node r {|x|})"
  using wf_darcs_sub[of "{|x|}" "sucs t" "root t"] by (simp add: less_eq_fset.rep_eq)

lemma size_fset_alt:
  "size_fset (size_prod snd (\<lambda>_. 0)) (map_prod (\<lambda>t. (t, size t)) (\<lambda>x. x) |`| xs)
  = (\<Sum>(x,y)\<in> fset xs. size x + 2)"
proof -
  have "size_fset (size_prod snd (\<lambda>_. 0)) (map_prod (\<lambda>t. (t, size t)) (\<lambda>x. x) |`| xs)
        = (\<Sum>u\<in>(\<lambda>(x,y). ((x,size x), y)) ` fset xs. snd (fst u) + 2)"
    by (simp add: size_prod_simp map_prod_def)
  also have "\<dots> = (\<Sum>(x,y) \<in> fset xs. size x + 2)"
    using case_prod_beta' comm_monoid_add_class.sum.eq_general
    by (smt (verit, del_insts) Pair_inject fstI imageE imageI prod_eqI snd_conv)
  finally show ?thesis .
qed

lemma dtree_size_alt: "size (Node r xs) = (\<Sum>(x,y)\<in> fset xs. size x + 2) + 1"
  using size_fset_alt by auto

lemma dtree_size_eq_root: "size (Node r xs) = size (Node r' xs)"
  by auto

lemma size_combine_decr: "size (Node (r@root t1) (sucs t1)) < size (Node r {|(t1, e1)|})"
  using dtree_size_eq_root[of "r@root t1" "sucs t1" "root t1"] by simp

lemma size_le_if_child_subset: "xs |\<subseteq>| ys \<Longrightarrow> size (Node r xs) \<le> size (Node v ys)"
  unfolding dtree_size_alt by (simp add: dtree_size_alt less_eq_fset.rep_eq sum.subset_diff)

lemma size_le_if_sucs_subset: "sucs t1 |\<subseteq>| sucs t2 \<Longrightarrow> size t1 \<le> size t2"
  using size_le_if_child_subset[of "sucs t1" "sucs t2" "root t1" "root t2"] by simp

lemma combine_uneq: "Node r {|(t1, e1)|} \<noteq> Node (r@root t1) (sucs t1)"
  using size_combine_decr[of r t1 e1] by fastforce

lemma child_uneq: "t \<in> fst ` fset xs \<Longrightarrow> Node r xs \<noteq> t"
  using dtree_size_decr_aux' by fastforce

lemma suc_uneq: "t1 \<in> fst ` fset (sucs t) \<Longrightarrow> t \<noteq> t1"
  using child_uneq[of t1 "sucs t" "root t"] by simp

lemma singleton_uneq: "Node r {|(t,e)|} \<noteq> t"
  using child_uneq[of t] by simp

lemma child_uneq': "t \<in> fst ` fset xs \<Longrightarrow> Node r xs \<noteq> Node v (sucs t)"
  using dtree_size_decr_aux'[of t] dtree_size_eq_root[of "root t" "sucs t"] by auto

lemma suc_uneq': "t1 \<in> fst ` fset (sucs t) \<Longrightarrow> t \<noteq> Node v (sucs t1)"
  using child_uneq'[of t1 "sucs t" "root t"] by simp

lemma singleton_uneq': "Node r {|(t,e)|} \<noteq> Node v (sucs t)"
  using child_uneq'[of t] by simp

lemma singleton_suc: "t \<in> fst ` fset (sucs (Node r {|(t,e)|}))"
  by simp

lemma fcard_image_le: "fcard (f |`| xs) \<le> fcard xs"
  by (simp add: FSet.fcard.rep_eq card_image_le)

lemma sum_img_le:
  assumes "\<forall>t \<in> fst ` fset xs. (g::'a \<Rightarrow> nat) (f t) \<le> g t"
  shows "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x) \<le> (\<Sum>(x,y)\<in> fset xs. g x)"
using assms proof(induction xs)
  case (insert x xs)
  obtain t e where t_def: "x = (t,e)" by fastforce
  then show ?case
  proof(cases "(f t,e) \<notin> fset ((\<lambda>(t,e). (f t, e)) |`| xs)")
    case True
    then have "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| (finsert x xs)). g x)
              = g (f t) + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
      using t_def by auto
    also have "\<dots> \<le> g t + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
      using insert.prems t_def by auto
    also have "\<dots> \<le> g t + (\<Sum>(x,y)\<in> fset xs. g x)" using insert by simp
    finally show ?thesis using insert.hyps t_def by fastforce
  next
    case False
    then have "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| (finsert x xs)). g x)
              = (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
      by (metis (no_types, lifting) t_def fimage_finsert finsert_absorb prod.case)
    also have "\<dots> \<le> (\<Sum>(x,y)\<in> fset xs. g x)" using insert by simp
    finally show ?thesis using insert.hyps t_def by fastforce
  qed
qed (simp)

lemma dtree_size_img_le:
  assumes "\<forall>t \<in> fst ` fset xs. size (f t) \<le> size t"
  shows "size (Node r ((\<lambda>(t,e). (f t, e)) |`| xs)) \<le> size (Node r xs)"
  using sum_img_le[of xs "\<lambda>x. size x + 2"] dtree_size_alt assms
  by (metis (mono_tags, lifting) add_right_mono)

lemma sum_img_lt:
  assumes "\<forall>t \<in> fst ` fset xs. (g::'a \<Rightarrow> nat) (f t) \<le> g t"
      and "\<exists>t \<in> fst ` fset xs. g (f t) < g t"
      and "\<forall>t \<in> fst ` fset xs. g t > 0"
    shows "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x) < (\<Sum>(x,y)\<in> fset xs. g x)"
using assms proof(induction xs)
  case (insert x xs)
  obtain t e where t_def: "x = (t,e)" by fastforce
  then show ?case
  proof(cases "(f t,e) \<notin> fset ((\<lambda>(t,e). (f t, e)) |`| xs)")
    case f_notin_xs: True
    show ?thesis
    proof(cases "g (f t) < g t")
      case True
      have "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| (finsert x xs)). g x)
                = g (f t) + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
        using t_def f_notin_xs by auto
      also have "\<dots> < g t + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
        using True by simp
      also have "\<dots> \<le> g t + (\<Sum>(x,y)\<in> fset xs. g x)" using sum_img_le insert.prems(1) by auto
      finally show ?thesis using insert.hyps t_def by fastforce
    next
      case False
      then have 0: "\<exists>t \<in> fst ` fset xs. g (f t) < g t" using insert.prems(2) t_def by simp
      have "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| (finsert x xs)). g x)
                = g (f t) + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
        using t_def f_notin_xs by auto
      also have "\<dots> \<le> g t + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
        using t_def insert.prems(1) by simp
      also have "\<dots> < g t + (\<Sum>(x,y)\<in> fset xs. g x)" using insert.IH insert.prems(1,3) 0 by simp
      finally show ?thesis using insert.hyps t_def by fastforce
    qed
  next
    case False
    then have "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| (finsert x xs)). g x)
              = (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
      by (metis (no_types, lifting) t_def fimage_finsert finsert_absorb prod.case)
    also have "\<dots> \<le> (\<Sum>(x,y)\<in> fset xs. g x)" using sum_img_le insert.prems(1) by auto
    also have "\<dots> < g t + (\<Sum>(x,y)\<in> fset xs. g x)" using insert.prems(3) t_def by simp
    finally show ?thesis using insert.hyps t_def by fastforce
  qed
qed (simp)

lemma dtree_size_img_lt:
  assumes "\<forall>t \<in> fst ` fset xs. size (f t) \<le> size t"
      and "\<exists>t \<in> fst ` fset xs. size (f t) < size t"
    shows "size (Node r ((\<lambda>(t,e). (f t, e)) |`| xs)) < size (Node r xs)"
proof -
  have 0: "\<forall>t \<in> fst ` fset xs. size (f t) + 2 \<le> size t + 2" using assms(1) by simp
  have "\<forall>t\<in>fst ` fset xs. 0 < size t + 2" by simp
  then show ?thesis using sum_img_lt[OF 0] dtree_size_alt assms(2) by (smt (z3) add_less_mono1)
qed

lemma sum_img_eq:
  assumes "\<forall>t \<in> fst ` fset xs. (g::'a \<Rightarrow> nat) (f t) = g t"
      and "fcard ((\<lambda>(t,e). (f t, e)) |`| xs) = fcard xs"
    shows "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x) = (\<Sum>(x,y)\<in> fset xs. g x)"
using assms proof(induction xs)
  case (insert x xs)
  obtain t e where t_def: "x = (t,e)" by fastforce
  then have 0: "(f t,e) \<notin> fset ((\<lambda>(t,e). (f t, e)) |`| xs)"
    using insert.prems(2) insert.hyps fcard_finsert_if fcard_image_le
    by (metis (mono_tags, lifting) case_prod_conv fimage_finsert leD lessI)
  then have 1: "fcard ((\<lambda>(t,e). (f t, e)) |`| xs) = fcard xs "
    using insert.prems(2) insert.hyps t_def Suc_inject
    by (metis (mono_tags, lifting) fcard_finsert_if fimage_finsert old.prod.case)
  have "(\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| (finsert x xs)). g x)
            = g (f t) + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
    using t_def 0 by auto
  also have "\<dots> = g t + (\<Sum>(x,y)\<in> fset ((\<lambda>(t,e). (f t, e)) |`| xs). g x)"
    using insert.prems t_def by auto
  also have "\<dots> = g t + (\<Sum>(x,y)\<in> fset xs. g x)" using insert.IH 1 insert.prems(1) by simp
  finally show ?case using insert.hyps t_def by fastforce
qed (simp)

lemma elem_neq_if_fset_neq:
  "((\<lambda>(t,e). (f t, e)) |`| xs) \<noteq> xs \<Longrightarrow> \<exists>t \<in> fst ` fset xs. f t \<noteq> t"
  by (smt (verit, ccfv_threshold) case_prod_eta case_prod_eta fimage.rep_eq fset_inject fst_conv
      image_cong image_ident image_subset_iff old.prod.case prod.case_distrib split_cong subsetI)

lemma ffold_commute_supset:
  "\<lbrakk>xs |\<subseteq>| ys; P ys; \<And>ys xs. \<lbrakk>xs |\<subseteq>| ys; P ys\<rbrakk> \<Longrightarrow> P xs;
    \<And>xs. comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not>Q a b \<or> \<not>P xs then b else R a b)\<rbrakk>
  \<Longrightarrow> ffold (\<lambda>a b. if a \<notin> fset ys \<or> \<not>Q a b \<or> \<not>P ys then b else R a b) acc xs
    = ffold (\<lambda>a b. if a \<notin> fset xs \<or> \<not>Q a b \<or> \<not>P xs then b else R a b) acc xs"
proof(induction xs arbitrary: ys)
  case empty
  show ?case
    unfolding empty.prems(4)[THEN comp_fun_commute.ffold_empty]
    by simp
next
  case (insert x xs)
  let ?f = "\<lambda>a b. if a \<notin> fset ys \<or> \<not>Q a b \<or> \<not>P ys then b else R a b"
  let ?f' = "\<lambda>a b. if a \<notin> fset xs \<or> \<not>Q a b \<or> \<not>P xs then b else R a b"
  let ?f1 = "\<lambda>a b. if a \<notin> fset (finsert x xs) \<or> \<not>Q a b \<or> \<not>P (finsert x xs) then b else R a b"
  have 0: "P (finsert x xs)" using insert.prems by simp
  have 1: "xs |\<subseteq>| (finsert x xs)" by blast
  have 2: "comp_fun_commute ?f1" using insert.prems(4) by blast
  have 3: "x \<in> fset ys" using insert.prems(1) by fastforce
  have "ffold ?f acc (finsert x xs) = ?f x (ffold ?f acc xs)"
    using comp_fun_commute.ffold_finsert[of ?f] insert.prems(4) insert.hyps by blast
  also have "\<dots> = ?f x (ffold ?f' acc xs)" using insert.IH[of ys] insert.prems by fastforce
  also have "\<dots> = ?f x (ffold ?f1 acc xs)" using insert.IH[OF 1 0] insert.prems(3,4) by presburger
  also have "\<dots> = ?f1 x (ffold ?f1 acc xs)" using 0 3 insert.prems(2) by fastforce
  also have "\<dots> = ffold ?f1 acc (finsert x xs)"
    using comp_fun_commute.ffold_finsert[of ?f1 x xs] 2 insert.hyps by presburger
  finally show ?case .
qed

lemma ffold_eq_fold: "\<lbrakk>finite xs; f = g\<rbrakk> \<Longrightarrow> ffold f acc (Abs_fset xs) = Finite_Set.fold g acc xs"
  unfolding ffold_def by (simp add: Abs_fset_inverse)

lemma Abs_fset_sub_if_sub:
  assumes "finite ys" and "xs \<subseteq> ys"
  shows "Abs_fset xs |\<subseteq>| Abs_fset ys"
proof (rule ccontr)
  assume "\<not>(Abs_fset xs |\<subseteq>| Abs_fset ys)"
  then obtain x where x_def: "x |\<in>| Abs_fset xs" "x |\<notin>| Abs_fset ys" by blast
  then have "x \<in> fset (Abs_fset xs) \<and> x \<notin> fset (Abs_fset ys)" by fast
  moreover have "finite xs" using assms finite_subset by auto
  ultimately show False using assms Abs_fset_inverse by blast
qed

lemma fold_commute_supset:
  assumes "finite ys" and "xs \<subseteq> ys" and "P ys" and "\<And>ys xs. \<lbrakk>xs \<subseteq> ys; P ys\<rbrakk> \<Longrightarrow> P xs"
      and "\<And>xs. comp_fun_commute (\<lambda>a b. if a \<notin> xs \<or> \<not>Q a b \<or> \<not>P xs then b else R a b)"
    shows "Finite_Set.fold (\<lambda>a b. if a \<notin> ys \<or> \<not>Q a b \<or> \<not>P ys then b else R a b) acc xs
          = Finite_Set.fold (\<lambda>a b. if a \<notin> xs \<or> \<not>Q a b \<or> \<not>P xs then b else R a b) acc xs"
proof -
  let ?f = "\<lambda>a b. if a \<notin> ys \<or> \<not>Q a b \<or> \<not>P ys then b else R a b"
  let ?f' = "\<lambda>a b. if a \<notin> xs \<or> \<not>Q a b \<or> \<not>P xs then b else R a b"
  let ?P = "\<lambda>xs. P (fset xs)"
  let ?g = "\<lambda>a b. if a \<notin> fset (Abs_fset ys) \<or> \<not>Q a b \<or> \<not>(?P (Abs_fset ys)) then b else R a b"
  let ?g' = "\<lambda>a b. if a \<notin> fset (Abs_fset xs) \<or> \<not>Q a b \<or> \<not>(?P (Abs_fset xs)) then b else R a b"
  have 0: "finite xs" using assms(1,2) finite_subset by auto
  then have 1: "Abs_fset xs |\<subseteq>| (Abs_fset ys)" using Abs_fset_sub_if_sub[OF assms(1,2)] by blast
  have 2: "?P (Abs_fset ys)" by (simp add: Abs_fset_inverse assms(1,3))
  have 3: "\<And>ys xs. \<lbrakk>xs |\<subseteq>| ys; ?P ys\<rbrakk> \<Longrightarrow> ?P xs" by (simp add: assms(4) less_eq_fset.rep_eq)
  have 4: "\<And>xs. comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not>Q a b \<or> \<not>(?P xs) then b else R a b)"
    using assms(5) by (simp add: less_eq_fset.rep_eq)
  have "?f' = ?g'" by (simp add: Abs_fset_inverse 0)
  have "?f = ?g" by (simp add: Abs_fset_inverse assms(1))
  then have "Finite_Set.fold (\<lambda>a b. if a \<notin> ys \<or> \<not>Q a b \<or> \<not>P ys then b else R a b) acc xs
            = ffold ?g acc (Abs_fset xs)" by (simp add: 0 ffold_eq_fold)
  also have "\<dots> = ffold ?g' acc (Abs_fset xs)"
    using ffold_commute_supset[OF 1, of ?P, OF 2 3 4] by simp
  finally show ?thesis using \<open>?f' = ?g'\<close> by (simp add: 0 ffold_eq_fold)
qed

lemma dtail_commute_aux:
  fixes r xs e def
  defines "f \<equiv> (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
            then b else dtail x def)"
  shows "(f y \<circ> f x) z = (f x \<circ> f y) z"
proof -
  obtain y1 y2 where y_def: "y = (y1,y2)" by fastforce
  obtain x1 x2 where x_def: "x = (x1,x2)" by fastforce
  show ?thesis
  proof(cases "(x1,x2) \<in> fset xs \<and> (y1,y2) \<in> fset xs")
    case 0: True
    then show ?thesis
    proof(cases "e \<in> darcs x1 \<and> e \<in> darcs y1")
      case True
      then have 1: "x1 = y1 \<or> \<not>wf_darcs (Node r xs)" using 0 disjoint_darcs_if_wf_aux2 by fast
      then show ?thesis using assms by (cases "x1=y1")(auto simp: x_def y_def)
    next
      case False
      then show ?thesis using assms by (simp add: x_def y_def)
    qed
  next
    case False
    then show ?thesis using assms by (simp add: x_def y_def)
  qed
qed

lemma dtail_commute:
  "comp_fun_commute (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
    then b else dtail x def)"
   using dtail_commute_aux[of xs] by unfold_locales blast

lemma dtail_f_alt:
  assumes "P = (\<lambda>xs. wf_darcs (Node r xs))"
      and "Q = (\<lambda>(t1,e1) b. e \<in> darcs t1)"
      and "R = (\<lambda>(t1,e1) b. dtail t1 def)"
    shows "(\<lambda>(t1,e1) b. if (t1,e1) \<notin> fset xs \<or> e \<notin> darcs t1\<or> \<not>wf_darcs (Node r xs)
            then b else dtail t1 def)
          = (\<lambda>a b. if a \<notin> fset xs \<or> \<not> Q a b \<or> \<not> P xs then b else R a b)"
  using assms by fast

lemma dtail_f_alt_commute:
  assumes "P = (\<lambda>xs. wf_darcs (Node r xs))"
      and "Q = (\<lambda>(t1,e1) b. e \<in> darcs t1)"
      and "R = (\<lambda>(t1,e1) b. dtail t1 def)"
    shows "comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not> Q a b \<or> \<not> P xs then b else R a b)"
  using dtail_commute[of xs e r def] dtail_f_alt[OF assms] by simp

lemma dtail_ffold_supset:
  assumes "xs |\<subseteq>| ys" and "wf_darcs (Node r ys)"
  shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset ys \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r ys)
      then b else dtail x def) def xs
    = ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
      then b else dtail x def) def xs"
proof -
  let ?P = "\<lambda>xs. wf_darcs (Node r xs)"
  let ?Q = "\<lambda>(t1,e1) b. e \<in> darcs t1"
  let ?R = "\<lambda>(t1,e1) b. dtail t1 def"
  have 0: "\<And>xs. comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b)"
    using dtail_f_alt_commute by fast
  have "ffold (\<lambda>a b. if a \<notin> fset ys \<or> \<not> ?Q a b \<or> \<not> ?P ys then b else ?R a b) def xs
      = ffold (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b) def xs"
    using ffold_commute_supset[OF assms(1),of ?P ?Q ?R,OF assms(2) wf_darcs_sub 0] by simp
  then show ?thesis using dtail_f_alt[of ?P r ?Q e ?R] by simp
qed

lemma dtail_in_child_eq_child_ffold:
  assumes "(t,e1) \<in> fset xs" and "e \<in> darcs t" and "wf_darcs (Node r xs)"
    shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
            then b else dtail x def) def xs
          = dtail t def"
using assms proof(induction xs)
  case (insert x' xs)
  let ?f = "(\<lambda>(x,e2) b.
              if (x,e2) \<notin> fset (finsert x' xs) \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r (finsert x' xs))
              then b else dtail x def)"
  let ?f' = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
              then b else dtail x def)"
  obtain x e3 where x_def: "x' = (x,e3)" by fastforce
  show ?case
  proof(cases "x=t")
    case True
    have "ffold ?f def (finsert x' xs) = (?f x' (ffold ?f def xs))"
      using comp_fun_commute.ffold_finsert[of ?f x' xs def] dtail_commute insert.hyps by fast
    also have "\<dots> = (?f (x,e3) (ffold ?f def xs))" using x_def by blast
    also have "\<dots> = dtail x def" using x_def insert.prems(2,3) True by fastforce
    finally show ?thesis using True by blast
  next
    case False
    then have 0: "(t,e1) \<in> fset xs" using insert.prems(1) x_def by simp
    have 1: "wf_darcs (Node r xs)" using wf_darcs_sub[OF fsubset_finsertI insert.prems(3)] .
    have 2: "xs |\<subseteq>| (finsert x' xs)" by blast
    have "(x,e3) \<in> fset (finsert x' xs)"  using x_def by simp
    have 3: "e \<notin> darcs x" using insert.prems(1-3) disjoint_darcs_if_wf x_def False by fastforce
    have "ffold ?f def (finsert x' xs) = (?f x' (ffold ?f def xs))"
      using comp_fun_commute.ffold_finsert[of ?f x' xs def] dtail_commute insert.hyps by fast
    also have "\<dots> = (?f (x,e3) (ffold ?f def xs))" using x_def by blast
    also have "\<dots> = (ffold ?f def xs)" using 3 by fastforce
    also have "\<dots> = (ffold ?f' def xs)"
        using dtail_ffold_supset[of xs "finsert x' xs"] insert.prems(3) 2 by simp
    also have "\<dots> = dtail t def" using insert.IH 0 1 insert.prems(2) by fast
    finally show ?thesis .
  qed
qed(simp)

lemma dtail_in_child_eq_child:
  assumes "(t,e1) \<in> fset xs" and "e \<in> darcs t" and "wf_darcs (Node r xs)"
  shows "dtail (Node r xs) def e = dtail t def e"
  using assms dtail_in_child_eq_child_ffold[OF assms] disjoint_darcs_if_wf_aux3 by fastforce

lemma dtail_ffold_notelem_eq_def:
  assumes "\<forall>(t,e1) \<in> fset xs. e \<notin> darcs t"
  shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset ys \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r ys)
          then b else dtail x def) def xs = def"
using assms proof(induction xs)
  case empty
  show ?case
    unfolding dtail_commute[THEN comp_fun_commute.ffold_empty]
    by simp
next
  case (insert x' xs)
  obtain x e3 where x_def: "x' = (x,e3)" by fastforce
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset ys \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r ys)
          then b else dtail x def)"
  have "ffold ?f def (finsert x' xs) = ?f x' (ffold ?f def xs)"
    using comp_fun_commute.ffold_finsert[of ?f x' xs] dtail_commute insert.hyps by fast
  also have "\<dots> = (ffold ?f def xs)" using insert.prems by auto
  also have "\<dots> = def" using insert.IH insert.prems by simp
  finally show ?case .
qed

lemma dtail_notelem_eq_def:
  assumes "e \<notin> darcs t"
  shows "dtail t def e = def e"
proof -
  obtain r xs where xs_def[simp]: "t = Node r xs" using dtree.exhaust by auto
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>wf_darcs (Node r xs)
              then b else dtail x def)"
  have 0: "\<forall>(t, e1)\<in>fset xs. e \<notin> darcs t" using assms by auto
  have "dtail (Node r xs) def e = ffold ?f def xs e" using assms by auto
  then show ?thesis using dtail_ffold_notelem_eq_def 0 by fastforce
qed

lemma dhead_commute_aux:
  fixes r xs e def
  defines "f \<equiv> (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs)
            then b else if e=e2 then root x else dhead x def e)"
  shows "(f y \<circ> f x) z = (f x \<circ> f y) z"
proof -
  obtain x1 x2 where x_def: "x = (x1,x2)" by fastforce
  obtain y1 y2 where y_def: "y = (y1,y2)" by fastforce
  show ?thesis
  proof(cases "(x1,x2) \<in> fset xs \<and> (y1,y2) \<in> fset xs")
    case 0: True
    then show ?thesis
    proof(cases "e \<in> darcs x1 \<and> e \<in> darcs y1")
      case True
      then have 1: "(x1,x2) = (y1,y2) \<or> \<not>wf_darcs (Node r xs)"
        using 0 disjoint_darcs_if_wf_aux2 by fast
      then show ?thesis using assms x_def y_def by (smt (z3) case_prod_conv comp_apply)
    next
      case False
      then show ?thesis
      proof(cases "x2=e")
        case True
        then show ?thesis using assms x_def y_def disjoint_darcs_if_wf by force
      next
        case False
        then show ?thesis using assms x_def y_def disjoint_darcs_if_wf by fastforce
      qed
    qed
  next
    case False
    then show ?thesis using assms by (simp add: x_def y_def)
  qed
qed

lemma dhead_commute:
  "comp_fun_commute (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs)
        then b else if e=e2 then root x else dhead x def e)"
  using dhead_commute_aux[of xs] by unfold_locales blast

lemma dhead_ffold_f_alt:
  assumes "P = (\<lambda>xs. wf_darcs (Node r xs))" and "Q = (\<lambda>(x,e2) _. e \<in> (darcs x \<union> {e2}))"
      and "R = (\<lambda>(x,e2) _. if e=e2 then root x else dhead x def e)"
    shows "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs) then b
            else if e=e2 then root x else dhead x def e)
          = (\<lambda>a b. if a \<notin> fset xs \<or> \<not> Q a b \<or> \<not> P xs then b else R a b)"
  using assms by fast

lemma dhead_ffold_f_alt_commute:
  assumes "P = (\<lambda>xs. wf_darcs (Node r xs))" and "Q = (\<lambda>(x,e2) _. e \<in> (darcs x \<union> {e2}))"
      and "R = (\<lambda>(x,e2) _. if e=e2 then root x else dhead x def e)"
    shows "comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not> Q a b \<or> \<not> P xs then b else R a b)"
using dhead_commute[of xs e r def] dhead_ffold_f_alt[OF assms] by simp

lemma dhead_ffold_supset:
  assumes "xs |\<subseteq>| ys" and "wf_darcs (Node r ys)"
  shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset ys \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r ys) then b
            else if e=e2 then root x else dhead x def e) (def e) xs
    = ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs) then b
            else if e=e2 then root x else dhead x def e) (def e) xs"
    (is "ffold ?f _ _ = ffold ?g _ _")
proof -
  let ?P = "\<lambda>xs. wf_darcs (Node r xs)"
  let ?Q = "\<lambda>(x,e2) _. e \<in> (darcs x \<union> {e2})"
  let ?R = "\<lambda>(x,e2) _. if e=e2 then root x else dhead x def e"
  have 0: "\<And>xs. comp_fun_commute (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b)"
    using dhead_ffold_f_alt_commute by fast
  have "ffold (\<lambda>a b. if a \<notin> fset ys \<or> \<not> ?Q a b \<or> \<not> ?P ys then b else ?R a b) (def e) xs
      = ffold (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b) (def e) xs"
    using ffold_commute_supset[OF assms(1), of ?P ?Q ?R, OF assms(2) wf_darcs_sub 0] by simp
  moreover have "?f = (\<lambda>a b. if a \<notin> fset ys \<or> \<not> ?Q a b \<or> \<not> ?P ys then b else ?R a b)" by fast
  moreover have "?g = (\<lambda>a b. if a \<notin> fset xs \<or> \<not> ?Q a b \<or> \<not> ?P xs then b else ?R a b)" by fast
  ultimately show ?thesis by argo
qed

lemma dhead_in_child_eq_child_ffold:
  assumes "(t,e1) \<in> fset xs" and "e \<in> darcs t"  and "wf_darcs (Node r xs)"
  shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs)
           then b else if e=e2 then root x else dhead x def e) (def e) xs
          = dhead t def e"
using assms proof(induction xs)
  case (insert x' xs)
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset (finsert x' xs) \<or> e \<notin> (darcs x \<union> {e2})
              \<or> \<not>wf_darcs (Node r (finsert x' xs))
            then b else if e=e2 then root x else dhead x def e)"
  let ?f' = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs) then b
            else if e=e2 then root x else dhead x def e)"
  obtain x e3 where x_def: "x' = (x,e3)" by fastforce
  show ?case
  proof(cases "x=t")
    case True
    have "ffold ?f (def e) (finsert x' xs) = (?f x' (ffold ?f (def e) xs))"
      using comp_fun_commute.ffold_finsert[of ?f x' xs "def e"] dhead_commute insert.hyps by fast
    also have "\<dots> = (?f (x,e3) (ffold ?f (def e) xs))" using x_def by blast
    also have "\<dots> = dhead x def e"
      using x_def insert.prems(2,3) True disjoint_darcs_if_wf by fastforce
    finally show ?thesis using True by blast
  next
    case False
    then have 0: "(t,e1) \<in> fset xs" using insert.prems(1) x_def by simp
    have 1: "wf_darcs (Node r xs)" using wf_darcs_sub[OF fsubset_finsertI insert.prems(3)] .
    have 2: "xs |\<subseteq>| (finsert x' xs)" by blast
    have 3: "e3 \<noteq> e" "e \<notin> darcs x"
      using insert.prems(1-3) disjoint_darcs_if_wf x_def False by fastforce+
    have "ffold ?f (def e) (finsert x' xs) = (?f x' (ffold ?f (def e) xs))"
      using comp_fun_commute.ffold_finsert[of ?f x' xs "def e"] dhead_commute insert.hyps by fast
    also have "\<dots> = (?f (x,e3) (ffold ?f (def e) xs))" using x_def by blast
    also have "\<dots> = (ffold ?f (def e) xs)" using 3 by simp
    also have "\<dots> = (ffold ?f' (def e) xs)"
        using dhead_ffold_supset[of xs "finsert x' xs"] insert.prems(3) 2 by simp
    also have "\<dots> = dhead t def e" using insert.IH 0 1 insert.prems(2) by fast
    finally show ?thesis .
  qed
qed(simp)

lemma dhead_in_child_eq_child:
  assumes "(t,e1) \<in> fset xs" and "e \<in> darcs t" and "wf_darcs (Node r xs)"
    shows "dhead (Node r xs) def e = dhead t def e"
  using assms dhead_in_child_eq_child_ffold[of t] by simp

lemma dhead_ffold_notelem_eq_def:
  assumes "\<forall>(t,e1) \<in> fset xs. e \<notin> darcs t \<and> e \<noteq> e1"
  shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset ys \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r ys) then b
            else if e=e2 then root x else dhead x def e) (def e) xs = def e"
using assms proof(induction xs)
  case empty
  show ?case
    apply (rule comp_fun_commute.ffold_empty)
    using dhead_commute by force
next
  case (insert x' xs)
  obtain x e3 where x_def: "x' = (x,e3)" by fastforce
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset ys \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r ys)
            then b else if e=e2 then root x else dhead x def e)"
  have "ffold ?f (def e) (finsert x' xs) = ?f x' (ffold ?f (def e) xs)"
    using comp_fun_commute.ffold_finsert[of ?f x' xs] dhead_commute insert.hyps by fast
  also have "\<dots> = (ffold ?f (def e) xs)" using insert.prems by auto
  also have "\<dots> = def e" using insert.IH insert.prems by simp
  finally show ?case .
qed

lemma dhead_notelem_eq_def:
  assumes "e \<notin> darcs t"
  shows "dhead t def e = def e"
proof -
  obtain r xs where xs_def[simp]: "t = Node r xs" using dtree.exhaust by auto
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs)
            then b else if e=e2 then root x else dhead x def e)"
  have 0: "\<forall>(t, e1)\<in>fset xs. e \<notin> darcs t \<and> e1\<noteq>e" using assms by auto
  have "dhead (Node r xs) def e = ffold ?f (def e) xs" by simp
  then show ?thesis using dhead_ffold_notelem_eq_def 0 by fastforce
qed

lemma dhead_in_set_eq_root_ffold:
  assumes "(t,e) \<in> fset xs" and "wf_darcs (Node r xs)"
  shows "ffold (\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs)
            then b else if e=e2 then root x else dhead x def e) (def e) xs
          = root t" (is "ffold ?f' _ _ = _")
using assms proof(induction xs)
  case (insert x' xs)
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset (finsert x' xs) \<or> e \<notin> (darcs x \<union> {e2})
              \<or> \<not>wf_darcs (Node r (finsert x' xs))
            then b else if e=e2 then root x else dhead x def e)"
  let ?f' = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>wf_darcs (Node r xs) then b
            else if e=e2 then root x else dhead x def e)"
  obtain x e3 where x_def: "x' = (x,e3)" by fastforce
  show ?case
  proof(cases "e3=e")
    case True
    then have "x=t" using insert.prems(1,2) x_def disjoint_darcs_if_wf by fastforce
    have "ffold ?f (def e) (finsert x' xs) = (?f x' (ffold ?f (def e) xs))"
      using comp_fun_commute.ffold_finsert[of ?f x' xs "def e"] dhead_commute insert.hyps by fast
    also have "\<dots> = (?f (x,e3) (ffold ?f (def e) xs))" using x_def by blast
    also have "\<dots> = root x" using x_def insert.prems(1,2) True by simp
    finally show ?thesis using True \<open>x=t\<close> by blast
  next
    case False
    then have 0: "(t,e) \<in> fset xs" using insert.prems(1) x_def by simp
    have 1: "wf_darcs (Node r xs)" using wf_darcs_sub[OF fsubset_finsertI insert.prems(2)] .
    have 2: "xs |\<subseteq>| (finsert x' xs)" by blast
    have 3: "e3 \<noteq> e" using insert.prems(2) False by simp
    have 4: "e \<notin> (darcs x \<union> {e3})"
      using insert.prems(1-2) False x_def disjoint_darcs_if_wf by fastforce
    have "ffold ?f (def e) (finsert x' xs) = (?f x' (ffold ?f (def e) xs))"
      using comp_fun_commute.ffold_finsert[of ?f x' xs "def e"] dhead_commute insert.hyps by fast
    also have "\<dots> = (?f (x,e3) (ffold ?f (def e) xs))" using x_def by blast
    also have "\<dots> = (ffold ?f (def e) xs)" using 4 by auto
    also have "\<dots> = (ffold ?f' (def e) xs)"
        using dhead_ffold_supset[of xs "finsert x' xs"] insert.prems(2) 2 by simp
    also have "\<dots> = root t" using insert.IH 0 1 insert.prems(2) by blast
    finally show ?thesis .
  qed
qed(simp)

lemma dhead_in_set_eq_root:
  "\<lbrakk>(t,e) \<in> fset xs; wf_darcs (Node r xs)\<rbrakk> \<Longrightarrow> dhead (Node r xs) def e = root t"
  using dhead_in_set_eq_root_ffold[of t] by simp

lemma self_subtree: "is_subtree t t"
  using is_subtree.elims(3) by blast

lemma subtree_trans: "is_subtree x y \<Longrightarrow> is_subtree y z \<Longrightarrow> is_subtree x z"
  by (induction z) fastforce+

lemma subtree_trans': "transp is_subtree"
  using subtree_trans transpI by auto

lemma subtree_if_child: "x \<in> fst ` fset xs \<Longrightarrow> is_subtree x (Node r xs)"
  using is_subtree.elims(3) by force

lemma subtree_if_suc: "t1 \<in> fst ` fset (sucs t2) \<Longrightarrow> is_subtree t1 t2"
  using subtree_if_child[of t1 "sucs t2" "root t2"] by simp

lemma child_sub_if_strict_subtree:
  "\<lbrakk>strict_subtree t1 (Node r xs)\<rbrakk> \<Longrightarrow> \<exists>t3 \<in> fst ` fset xs. is_subtree t1 t3"
  unfolding strict_subtree_def by force

lemma suc_sub_if_strict_subtree:
  "strict_subtree t1 t2 \<Longrightarrow> \<exists>t3 \<in> fst ` fset (sucs t2). is_subtree t1 t3"
  using child_sub_if_strict_subtree[of t1 "root t2"] by simp

lemma subtree_size_decr: "\<lbrakk>is_subtree t1 t2; t1 \<noteq> t2\<rbrakk> \<Longrightarrow> size t1 < size t2"
  using dtree_size_decr_aux by(induction t2) fastforce

lemma subtree_size_decr': "strict_subtree t1 t2 \<Longrightarrow> size t1 < size t2"
  unfolding strict_subtree_def using dtree_size_decr_aux by(induction t2) fastforce

lemma subtree_size_le: "is_subtree t1 t2 \<Longrightarrow> size t1 \<le> size t2"
  using subtree_size_decr by fastforce

lemma subtree_antisym: "\<lbrakk>is_subtree t1 t2; is_subtree t2 t1\<rbrakk> \<Longrightarrow> t1 = t2"
  using subtree_size_le subtree_size_decr by fastforce

lemma subtree_antisym': "antisymp is_subtree"
  using antisympI subtree_antisym by blast

corollary subtree_eq_if_trans_eq1: "\<lbrakk>is_subtree t1 t2; is_subtree t2 t3; t1 = t3\<rbrakk> \<Longrightarrow> t1 = t2"
  using subtree_antisym by blast

corollary subtree_eq_if_trans_eq2: "\<lbrakk>is_subtree t1 t2; is_subtree t2 t3; t1 = t3\<rbrakk> \<Longrightarrow> t2 = t3"
  using subtree_antisym by blast

lemma subtree_partial_ord: "class.order is_subtree strict_subtree"
  by standard (auto simp: self_subtree subtree_antisym strict_subtree_def intro: subtree_trans)

lemma finite_subtrees: "finite {x. is_subtree x t}"
  by (induction t) auto

lemma subtrees_insert_union:
  "{x. is_subtree x (Node r xs)} = insert (Node r xs) (\<Union>t1 \<in> fst ` fset xs. {x. is_subtree x t1})"
  by fastforce

lemma subtrees_insert_union_suc:
  "{x. is_subtree x t} = insert t (\<Union>t1 \<in> fst ` fset (sucs t). {x. is_subtree x t1})"
  using subtrees_insert_union[of "root t" "sucs t"] by simp

lemma darcs_subtree_subset: "is_subtree x y \<Longrightarrow> darcs x \<subseteq> darcs y"
  by(induction y) force

lemma dverts_subtree_subset: "is_subtree x y \<Longrightarrow> dverts x \<subseteq> dverts y"
  by(induction y) force

lemma single_subtree_root_dverts:
  "is_subtree (Node v2 {|(t2, e2)|}) t1 \<Longrightarrow> v2 \<in> dverts t1"
  by (fastforce dest: dverts_subtree_subset)

lemma single_subtree_child_root_dverts:
  "is_subtree (Node v2 {|(t2, e2)|}) t1 \<Longrightarrow> root t2 \<in> dverts t1"
  by (fastforce simp: dtree.set_sel(1) dest: dverts_subtree_subset)

lemma subtree_root_if_dverts: "x \<in> dverts t \<Longrightarrow> \<exists>xs. is_subtree (Node x xs) t"
  by(induction t) fastforce

lemma subtree_child_if_strict_subtree:
  "strict_subtree t1 t2 \<Longrightarrow> \<exists>r xs. is_subtree (Node r xs) t2 \<and> t1 \<in> fst ` fset xs"
proof(induction t2)
  case (Node r xs)
  then obtain t e where t_def: "(t,e) \<in> fset xs" "is_subtree t1 t"
    unfolding strict_subtree_def by auto
  show ?case
  proof(cases "t1 = t")
    case True
    then show ?thesis using t_def by force
  next
    case False
    then show ?thesis using Node.IH[OF t_def(1)] t_def unfolding strict_subtree_def by auto
  qed
qed

lemma subtree_child_if_dvert_notroot:
  assumes "v \<noteq> r" and "v \<in> dverts (Node r xs)"
  shows "\<exists>r' ys zs. is_subtree (Node r' ys) (Node r xs) \<and> Node v zs \<in> fst ` fset ys"
proof -
  obtain zs where sub: "is_subtree (Node v zs) (Node r xs)"
    using assms(2) subtree_root_if_dverts by fast
  then show ?thesis using subtree_child_if_strict_subtree strict_subtree_def assms(1) by fast
qed

lemma subtree_child_if_dvert_notelem:
  "\<lbrakk>v \<noteq> root t; v \<in> dverts t\<rbrakk> \<Longrightarrow> \<exists>r' ys zs. is_subtree (Node r' ys) t \<and> Node v zs \<in> fst ` fset ys"
  using subtree_child_if_dvert_notroot[of v "root t" "sucs t"] by simp

lemma strict_subtree_subset:
  assumes "strict_subtree t (Node r xs)" and "xs |\<subseteq>| ys"
  shows "strict_subtree t (Node r ys)"
proof -
  obtain t1 e1 where t1_def: "(t1,e1) \<in> fset xs" "is_subtree t t1"
    using assms(1) unfolding strict_subtree_def by auto
  have "size t < size (Node r xs)" using subtree_size_decr'[OF assms(1)] by blast
  then have "size t < size (Node r ys)" using size_le_if_child_subset[OF assms(2)] by simp
  moreover have "is_subtree t (Node r ys)" using assms(2) t1_def by auto
  ultimately show ?thesis unfolding strict_subtree_def by blast
qed

lemma strict_subtree_singleton:
  "\<lbrakk>strict_subtree t (Node r {|x|}); x |\<in>| xs\<rbrakk>
    \<Longrightarrow> strict_subtree t (Node r xs)"
  using strict_subtree_subset by fast

subsubsection "Finite Directed Trees to Dtree"

context finite_directed_tree
begin

lemma child_subtree:
  assumes "e \<in> out_arcs T r"
  shows "{x. (head T e) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x} \<subseteq> {x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x}"
proof -
  have "r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> (head T e)" using assms in_arcs_imp_in_arcs_ends by auto
  then show ?thesis by (metis Collect_mono reachable_trans)
qed

lemma child_strict_subtree:
  assumes "e \<in> out_arcs T r"
  shows "{x. (head T e) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x} \<subset> {x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x}"
proof -
  have "r \<rightarrow>\<^bsub>T\<^esub> (head T e)" using assms in_arcs_imp_in_arcs_ends by auto
  then have "\<not> ((head T e) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> r)" using reachable1_not_reverse by blast
  then show ?thesis using child_subtree assms by auto
qed

lemma child_card_decr:
  assumes "e \<in> out_arcs T r"
  shows "Finite_Set.card {x. (head T e) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x} < Finite_Set.card {x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x}"
  using assms child_strict_subtree by (meson psubset_card_mono reachable_verts_finite)

function to_dtree_aux :: "'a \<Rightarrow> ('a,'b) dtree" where
  "to_dtree_aux r = Node r (Abs_fset {(x,e).
    (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)})"
  by auto
termination
  by(relation "measure (\<lambda>r. Finite_Set.card {x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x})") (auto simp: child_card_decr)

definition to_dtree :: "('a,'b) dtree" where
  "to_dtree = to_dtree_aux root"

abbreviation from_dtree :: "('a,'b) dtree \<Rightarrow> ('a,'b) pre_digraph" where
  "from_dtree t \<equiv> Dtree.from_dtree (tail T) (head T) t"

lemma to_dtree_root_eq_root[simp]: "Dtree.root to_dtree = root"
  unfolding to_dtree_def by simp

lemma verts_fset_id: "fset (Abs_fset (verts T)) = verts T"
  by (simp add: Abs_fset_inverse)

lemma arcs_fset_id: "fset (Abs_fset (arcs T)) = arcs T"
  by (simp add: Abs_fset_inverse)

lemma dtree_leaf_child_empty:
  "leaf r \<Longrightarrow> {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)} = {}"
  unfolding leaf_def by simp

lemma dtree_leaf_no_children: "leaf r \<Longrightarrow> to_dtree_aux r = Node r {||}"
  using dtree_leaf_child_empty by (simp add: bot_fset.abs_eq)

lemma dtree_children_alt:
  "{(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}
    = {(x,e). e \<in> out_arcs T r \<and> x = to_dtree_aux (head T e)}"
  by metis

lemma dtree_children_img_alt:
  "(\<lambda>e. (to_dtree_aux (head T e),e)) ` (out_arcs T r)
  = {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
  using dtree_children_alt by blast

lemma dtree_children_fin:
  "finite {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
  using finite_imageI[of "out_arcs T r" "(\<lambda>e. (to_dtree_aux (head T e),e))"]
      dtree_children_img_alt finite_out_arcs by fastforce

lemma dtree_children_fset_id:
  assumes "to_dtree_aux r = Node r xs"
    shows "fset xs = {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
proof -
  let ?xs = "{(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
  have "finite ?xs" using dtree_children_fin by simp
  then have "fset (Abs_fset ?xs) = ?xs" using Abs_fset_inverse by blast
  then show ?thesis using assms Abs_fset_inverse by simp
qed

lemma to_dtree_aux_empty_if_notT:
  assumes "r \<notin> verts T"
  shows "to_dtree_aux r = Node r {||}"
proof(rule ccontr)
  assume asm: "to_dtree_aux r \<noteq> Node r {||}"
  then obtain xs where xs_def: "Node r xs = to_dtree_aux r" by simp
  then have "xs \<noteq> {||}" using asm by simp
  then obtain x e where x_def: "(x,e) \<in> fset xs" by fast
  then have "e \<in> out_arcs T r" using xs_def dtree_children_fset_id[of r] by (auto split: if_splits)
  then show False using assms by auto
qed

lemma to_dtree_aux_root: "Dtree.root (to_dtree_aux r) = r"
  by simp

lemma out_arc_if_child:
  assumes "x \<in> (fst ` {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)})"
  shows "\<exists>e. e \<in> out_arcs T r \<and> x = to_dtree_aux (head T e)"
proof -
  let ?xs = "{(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
  have "\<exists>y. y \<in> ?xs \<and> fst y = x" using assms by blast
  then show ?thesis by (smt (verit, best) case_prodE fst_conv mem_Collect_eq)
qed

lemma dominated_if_child_aux:
  assumes "x \<in> (fst ` {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)})"
  shows "r \<rightarrow>\<^bsub>T\<^esub> (Dtree.root x)"
proof -
  obtain e where "e \<in> out_arcs T r \<and> x = to_dtree_aux (head T e)"
    using assms out_arc_if_child by blast
  then show ?thesis using in_arcs_imp_in_arcs_ends by force
qed

lemma dominated_if_child:
  "\<lbrakk>to_dtree_aux r = Node r xs; x \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> r \<rightarrow>\<^bsub>T\<^esub> (Dtree.root x)"
  using dominated_if_child_aux dtree_children_fset_id by simp

lemma image_add_snd_snd_id: "snd ` ((\<lambda>e. (to_dtree_aux (head T e),e)) ` x) = x"
  by (intro equalityI subsetI) (force simp: image_iff)+

lemma to_dtree_aux_child_in_verts:
  assumes "Node r' xs = to_dtree_aux r" and "x \<in> fst ` fset xs"
  shows "Dtree.root x \<in> verts T"
proof -
  have "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x" using assms dominated_if_child by auto
  then show ?thesis using adj_in_verts(2) by auto
qed

lemma to_dtree_aux_parent_in_verts:
  assumes "Node r' xs = to_dtree_aux r" and "x \<in> fst ` fset xs"
  shows "r \<in> verts T"
proof -
  have "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x" using assms dominated_if_child by auto
  then show ?thesis using adj_in_verts(2) by auto
qed

lemma dtree_out_arcs:
  "snd ` {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)} = out_arcs T r"
  using dtree_children_img_alt by (metis image_add_snd_snd_id)

lemma dtree_out_arcs_eq_snd:
  assumes "to_dtree_aux r = Node r xs"
  shows "(snd ` (fset xs)) = out_arcs T r"
  using assms dtree_out_arcs dtree_children_fset_id by blast

lemma dtree_aux_fst_head_snd_aux:
  assumes "x \<in> {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
  shows "Dtree.root (fst x) = (head T (snd x))"
  using assms by (metis (mono_tags, lifting) Collect_case_prodD to_dtree_aux_root)

lemma dtree_aux_fst_head_snd:
  assumes "to_dtree_aux r = Node r xs" and "x \<in> fset xs"
  shows "Dtree.root (fst x) = (head T (snd x))"
  using assms dtree_children_fset_id dtree_aux_fst_head_snd_aux by simp

lemma child_if_dominated_aux:
  assumes "r \<rightarrow>\<^bsub>T\<^esub> x"
  shows "\<exists>y \<in> (fst ` {(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}).
           Dtree.root y = x"
proof -
  let ?xs = "{(x,e). (if e \<in> out_arcs T r then x = to_dtree_aux (head T e) else False)}"
  obtain e where e_def: "e \<in> out_arcs T r \<and> head T e = x" using assms by auto
  then have "e \<in> snd ` ?xs" using dtree_out_arcs by auto
  then obtain y where y_def: "y \<in> ?xs \<and> snd y = e" by blast
  then have "Dtree.root (fst y) = head T e" using dtree_aux_fst_head_snd_aux by blast
  then show ?thesis using e_def y_def by blast
qed

lemma child_if_dominated:
  assumes "to_dtree_aux r = Node r xs" and "r \<rightarrow>\<^bsub>T\<^esub> x"
  shows "\<exists>y \<in> (fst ` (fset xs)). Dtree.root y = x"
  using assms child_if_dominated_aux dtree_children_fset_id by presburger

lemma to_dtree_aux_reach_in_dverts: "\<lbrakk>t = to_dtree_aux r; r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x\<rbrakk> \<Longrightarrow> x \<in> dverts t"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  then show ?case
  proof(cases "r=x")
    case True
    then show ?thesis using \<open>r = r'\<close> by simp
  next
    case False
    then have "r \<rightarrow>\<^sup>+\<^bsub>T\<^esub> x" using "1.prems"(2) by blast
    then have "\<exists>r'. r \<rightarrow>\<^bsub>T\<^esub> r' \<and> r' \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
      by (metis False converse_reachable_cases reachable1_reachable)
    then obtain x' where x'_def: "r \<rightarrow>\<^bsub>T\<^esub> x' \<and> x' \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" by blast
    then obtain y where y_def: "y \<in> fst ` fset xs \<and> Dtree.root y = x'"
      using "1.prems"(1) child_if_dominated by fastforce
    then obtain yp where yp_def: "fst yp = y \<and> yp \<in> fset xs" using y_def by blast
    from y_def have "y = to_dtree_aux x'"
      using "1.prems"(1) dtree_children_fset_id \<open>r=r'\<close>
      by (metis (no_types, lifting) out_arc_if_child to_dtree_aux_root)
    then have "x \<in> dverts y" using "1.IH" prod.exhaust_sel yp_def x'_def by metis
    then show ?thesis using dtree.set_intros(2) y_def by auto
  qed
qed

lemma to_dtree_aux_dverts_reachable:
  "\<lbrakk>t = to_dtree_aux r; x \<in> dverts t; r \<in> verts T\<rbrakk> \<Longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  then show ?case
  proof(cases "r=x")
    case True
    then show ?thesis using "1.prems"(3) by auto
  next
    case False
    then obtain y where y_def: "y \<in> fst ` fset xs \<and> x \<in> dverts y"
      using "1.prems"(2) \<open>r = r'\<close> by fastforce
    then have 0: "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root y" using "1.prems"(1) \<open>r = r'\<close> dominated_if_child by simp
    then have 2: "Dtree.root y \<in> verts T" using adj_in_verts(2) by auto
    obtain yp where yp_def: "fst yp = y \<and> yp \<in> fset xs" using y_def by blast
    have "\<exists>yr. y = to_dtree_aux yr"
      using "1.prems"(1) y_def dtree_children_fset_id
      by (metis (no_types, lifting) \<open>r = r'\<close> out_arc_if_child)
    then have "Dtree.root y \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
      using "1.IH" 2 y_def yp_def surjective_pairing to_dtree_aux_root by metis
    then show ?thesis using 0 adj_reachable_trans by auto
  qed
qed

lemma dverts_eq_reachable: "r \<in> verts T \<Longrightarrow> dverts (to_dtree_aux r) = {x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x}"
  using to_dtree_aux_reach_in_dverts to_dtree_aux_dverts_reachable by blast

lemma dverts_eq_reachable': "\<lbrakk>r \<in> verts T; t = to_dtree_aux r\<rbrakk> \<Longrightarrow> dverts t = {x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x}"
  using dverts_eq_reachable by blast

lemma dverts_eq_verts: "dverts to_dtree = verts T"
  unfolding to_dtree_def using dverts_eq_reachable reachable_from_root reachable_in_verts(2)
  by (metis mem_Collect_eq root_in_T subsetI subset_antisym)

lemma arc_out_arc: "e \<in> arcs T \<Longrightarrow> \<exists>v \<in> verts T. e \<in> out_arcs T v"
  by simp

lemma darcs_in_out_arcs: "t = to_dtree_aux r \<Longrightarrow> e \<in> darcs t \<Longrightarrow> \<exists>v\<in>dverts t. e \<in> out_arcs T v"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then show ?case
  proof(cases "e \<in> snd ` fset xs")
    case True
    then show ?thesis
      using "1.prems"(1) dtree_out_arcs_eq_snd to_dtree_aux_root
      by (metis dtree.set_intros(1) dtree.sel(1))
  next
    case False
    then have "\<exists>y \<in> fst ` fset xs. e \<in> darcs y" using "1.prems"(2) by force
    then obtain y where y_def: "y \<in> fst ` fset xs \<and> e \<in> darcs y" by blast
    obtain yp where yp_def: "fst yp = y \<and> yp \<in> fset xs" using y_def by blast
    have 0: "(y, snd yp) = yp" using yp_def by auto
    have "\<exists>yr. y = to_dtree_aux yr"
      using "1.prems"(1) y_def dtree_children_fset_id
      by (metis (no_types, lifting) dtree.sel(1) out_arc_if_child to_dtree_aux_root)
    then have "\<exists>v\<in>dverts y. e \<in> out_arcs T v" using "1.IH" 0 y_def yp_def by blast
    then obtain v where "v \<in> dverts y \<and> e \<in> out_arcs T v" by blast
    then show ?thesis using y_def by auto
  qed
qed

lemma darcs_in_arcs: "e \<in> darcs to_dtree \<Longrightarrow> e \<in> arcs T"
  using darcs_in_out_arcs out_arcs_in_arcs to_dtree_def by fast

lemma out_arcs_in_darcs: "t = to_dtree_aux r \<Longrightarrow> \<exists>v\<in>dverts t. e \<in> out_arcs T v \<Longrightarrow> e \<in> darcs t"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r' = r" by simp
  then obtain v where v_def: "v\<in>dverts (Node r xs) \<and> e \<in> out_arcs T v" using "1.prems"(2) by blast
  then show ?case
  proof(cases "e \<in> snd ` fset xs")
    case True
    then show ?thesis by force
  next
    case False
    then have "e \<notin> out_arcs T r" using "1.prems"(1) \<open>r' = r\<close> dtree_out_arcs_eq_snd by metis
    then have "v \<noteq> r" using v_def by blast
    then obtain y where y_def: "y \<in> fst ` fset xs \<and> v \<in> dverts y" using v_def by force
    then obtain yp where yp_def: "fst yp = y \<and> yp \<in> fset xs" by blast
    have 0: "(y, snd yp) = yp" using yp_def by auto
    have "\<exists>yr. y = to_dtree_aux yr"
      using "1.prems"(1) y_def dtree_children_fset_id
      by (metis (no_types, lifting) dtree.sel(1) out_arc_if_child to_dtree_aux_root)
    then have "e \<in> darcs y" using "1.IH" 0 v_def y_def yp_def by blast
    then show ?thesis using y_def by force
  qed
qed

lemma arcs_in_darcs: "e \<in> arcs T \<Longrightarrow> e \<in> darcs to_dtree"
  using arc_out_arc out_arcs_in_darcs dverts_eq_verts to_dtree_def by fast

lemma darcs_eq_arcs: "darcs to_dtree = arcs T"
  using arcs_in_darcs darcs_in_arcs by blast

lemma to_dtree_aux_self:
  assumes "Node r xs = to_dtree_aux r" and "(y,e) \<in> fset xs"
  shows "y = to_dtree_aux (Dtree.root y)"
proof -
  have "\<exists>y'. y = to_dtree_aux y'"
    using assms dtree_children_fset_id by (metis (mono_tags, lifting) case_prodD mem_Collect_eq)
  then obtain y' where "y = to_dtree_aux y'" by blast
  then show ?thesis by simp
qed

lemma to_dtree_aux_self_subtree:
  "\<lbrakk>t1 = to_dtree_aux r; is_subtree t2 t1\<rbrakk> \<Longrightarrow> t2 = to_dtree_aux (Dtree.root t2)"
proof(induction t1 arbitrary: r)
  case (Node r' xs)
  then show ?case
  proof(cases "Node r' xs = t2")
    case True
    then show ?thesis using Node.prems(1) by force
  next
    case False
    then obtain t e where t_def: "(t,e) \<in> fset xs" "is_subtree t2 t" using Node.prems(2) by auto
    then have "t = to_dtree_aux (Dtree.root t)" using Node.prems(1) to_dtree_aux_self by simp
    then show ?thesis using Node.IH[of "(t,e)" t "Dtree.root t"] t_def by simp
  qed
qed

lemma to_dtree_self_subtree: "is_subtree t to_dtree \<Longrightarrow> t = to_dtree_aux (Dtree.root t)"
  unfolding to_dtree_def using to_dtree_aux_self_subtree by blast

lemma to_dtree_self_subtree': "is_subtree (Node r xs) to_dtree \<Longrightarrow> (Node r xs) = to_dtree_aux r"
  using to_dtree_self_subtree[of "Node r xs"] by simp

lemma child_if_dominated_to_dtree:
  "\<lbrakk>is_subtree (Node r xs) to_dtree; r \<rightarrow>\<^bsub>T\<^esub> v\<rbrakk> \<Longrightarrow> \<exists>t. t \<in> fst ` fset xs \<and> Dtree.root t = v"
  using child_if_dominated[of r] to_dtree_self_subtree' by simp

lemma child_if_dominated_to_dtree':
  "\<lbrakk>is_subtree (Node r xs) to_dtree; r \<rightarrow>\<^bsub>T\<^esub> v\<rbrakk> \<Longrightarrow> \<exists>ys. Node v ys \<in> fst ` fset xs"
  using child_if_dominated_to_dtree dtree.exhaust dtree.sel(1) by metis

lemma child_darc_tail_parent:
  assumes "Node r xs = to_dtree_aux r" and "(x,e) \<in> fset xs"
  shows "tail T e = r"
proof -
  have "e \<in> out_arcs T r"
    using assms dtree_children_fset_id by (metis (no_types, lifting) case_prodD mem_Collect_eq)
  then show ?thesis by simp
qed

lemma child_darc_head_root:
  "\<lbrakk>Node r xs = to_dtree_aux r; (t,e) \<in> fset xs\<rbrakk> \<Longrightarrow> head T e = Dtree.root t"
  using dtree_aux_fst_head_snd by force

lemma child_darc_in_arcs:
  assumes "Node r xs = to_dtree_aux r" and "(x,e) \<in> fset xs"
  shows "e \<in> arcs T"
proof -
  have "e \<in> out_arcs T r"
    using assms dtree_children_fset_id by (metis (no_types, lifting) case_prodD mem_Collect_eq)
  then show ?thesis by simp
qed

lemma darcs_neq_if_dtrees_neq:
  "\<lbrakk>Node r xs = to_dtree_aux r; (x,e1) \<in> fset xs; (y,e2) \<in> fset xs; x\<noteq>y\<rbrakk> \<Longrightarrow> e1 \<noteq> e2"
  using dtree_children_fset_id by (metis (mono_tags, lifting) case_prodD mem_Collect_eq)

lemma dtrees_neq_if_darcs_neq:
  "\<lbrakk>Node r xs = to_dtree_aux r; (x,e1) \<in> fset xs; (y,e2) \<in> fset xs; e1\<noteq>e2\<rbrakk> \<Longrightarrow> x \<noteq> y"
  using dtree_children_fset_id case_prodD dtree_aux_fst_head_snd fst_conv
  by (metis (no_types, lifting) mem_Collect_eq out_arcs_in_arcs snd_conv two_in_arcs_contr)

lemma dverts_disjoint:
  assumes "Node r xs = to_dtree_aux r" and "(x,e1) \<in> fset xs" and "(y,e2) \<in> fset xs"
      and "(x,e1)\<noteq>(y,e2)"
  shows "dverts x \<inter> dverts y = {}"
proof (rule ccontr)
  assume "dverts x \<inter> dverts y \<noteq> {}"
  then obtain v where v_def: "v \<in> dverts x \<and> v \<in> dverts y" by blast
  have "x \<noteq> y" using dtrees_neq_if_darcs_neq assms by blast
  have 0: "x = to_dtree_aux (Dtree.root x)" using to_dtree_aux_self assms(1,2) by blast
  have 1: "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x"
    using assms(1,2) dominated_if_child by (metis (no_types, opaque_lifting) fst_conv image_iff)
  then have 2: "Dtree.root x \<in> verts T" using adj_in_verts(2) by simp
  have 3: "y = to_dtree_aux (Dtree.root y)" using to_dtree_aux_self assms(1,3) by blast
  have 4: "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root y"
    using assms(1,3) dominated_if_child by (metis (no_types, opaque_lifting) fst_conv image_iff)
  then have 5: "Dtree.root y \<in> verts T" using adj_in_verts(2) by simp
  have "Dtree.root x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" using 0 2 to_dtree_aux_dverts_reachable v_def by blast
  moreover have "Dtree.root y \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" using 3 5 to_dtree_aux_dverts_reachable v_def by blast
  moreover have "Dtree.root x \<noteq> Dtree.root y" using 0 3 assms(4) \<open>x\<noteq>y\<close> by auto
  ultimately show False using 1 4 reachable_via_child_impl_same by simp
qed

lemma wf_dverts_to_dtree_aux1: "r \<notin> verts T \<Longrightarrow> wf_dverts (to_dtree_aux r)"
  using to_dtree_aux_empty_if_notT unfolding wf_dverts_iff_dverts' by simp

lemma wf_dverts_to_dtree_aux2: "r \<in> verts T \<Longrightarrow> t = to_dtree_aux r \<Longrightarrow> wf_dverts t"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  have "\<forall>(x,e) \<in> fset xs. wf_dverts x \<and> r \<notin> dverts x"
  proof (standard, standard, standard)
    fix xp x e
    assume asm: "xp \<in> fset xs" "xp = (x,e)"
    then have 0: "x = to_dtree_aux (Dtree.root x)" using to_dtree_aux_self "1.prems"(2) by simp
    have 2: "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x" using asm "1.prems" \<open>r = r'\<close>
      by (metis (no_types, opaque_lifting) dominated_if_child fst_conv image_iff)
    then have 3: "Dtree.root x \<in> verts T" using adj_in_verts(2) by simp
    then show "wf_dverts x" using "1.IH" asm 0 by blast
    show "r \<notin> dverts x"
    proof
      assume "r \<in> dverts x"
      then have "Dtree.root x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> r" using 0 3 to_dtree_aux_dverts_reachable by blast
      then have "r \<rightarrow>\<^sup>+\<^bsub>T\<^esub> r" using 2 by auto
      then show False using reachable1_not_reverse by blast
    qed
  qed
  then show ?case using dverts_disjoint \<open>r=r'\<close> "1.prems"(1,2) unfolding wf_dverts_iff_dverts'
    by (smt (verit, del_insts) wf_dverts'.simps case_prodI2 case_prod_conv)
qed

lemma wf_dverts_to_dtree_aux: "wf_dverts (to_dtree_aux r)"
  using wf_dverts_to_dtree_aux1 wf_dverts_to_dtree_aux2 by blast

lemma wf_dverts_to_dtree_aux': "t = to_dtree_aux r \<Longrightarrow> wf_dverts t"
  using wf_dverts_to_dtree_aux by blast

lemma wf_dverts_to_dtree: "wf_dverts to_dtree"
  using to_dtree_def wf_dverts_to_dtree_aux by simp

lemma darcs_not_in_subtree:
  assumes "Node r xs = to_dtree_aux r" and "(x,e) \<in> fset xs" and "(y,e2) \<in> fset xs"
  shows "e \<notin> darcs y"
proof
  assume asm: "e \<in> darcs y"
  have 0: "y = to_dtree_aux (Dtree.root y)" using to_dtree_aux_self assms(1,3) by blast
  then obtain v where v_def: "v \<in> dverts y \<and> e \<in> out_arcs T v" using darcs_in_out_arcs asm by blast
  have 1: "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root y"
    using assms(1,3) by (metis (no_types, opaque_lifting) dominated_if_child fst_conv image_iff)
  then have "Dtree.root y \<in> verts T" using adj_in_verts(2) by auto
  then have "Dtree.root y \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" using to_dtree_aux_dverts_reachable 0 v_def by blast
  then have "r \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v" using 1 by auto
  then have "r \<noteq> v" using reachable1_not_reverse two_in_arcs_contr by blast
  moreover have "tail T e = v" using v_def by simp
  moreover have "tail T e = r" using assms(1,2) child_darc_tail_parent by blast
  ultimately show False by blast
qed

lemma darcs_disjoint:
  assumes "Node r xs = to_dtree_aux r" and "r \<in> verts T"
      and "(x,e1) \<in> fset xs" and "(y,e2) \<in> fset xs" and "(x,e1)\<noteq>(y,e2)"
  shows "(darcs x \<union> {e1}) \<inter> (darcs y \<union> {e2}) = {}"
proof (rule ccontr)
  assume "(darcs x \<union> {e1}) \<inter> (darcs y \<union> {e2}) \<noteq> {}"
  moreover have "e1 \<notin> darcs y" using darcs_not_in_subtree assms(1-4) by blast
  moreover have "e2 \<notin> darcs x" using darcs_not_in_subtree assms(1-4) by blast
  moreover have "e1 \<noteq> e2" using darcs_neq_if_dtrees_neq assms by blast
  ultimately have "darcs x \<inter> darcs y \<noteq> {}" by blast
  then obtain e where e_def: "e \<in> darcs x \<and> e \<in> darcs y" by blast
  have "x = to_dtree_aux (Dtree.root x)" using to_dtree_aux_self assms(1,3) by blast
  then obtain v1 where v1_def: "v1 \<in> dverts x \<and> e \<in> out_arcs T v1"
    using darcs_in_out_arcs e_def by blast
  have "y = to_dtree_aux (Dtree.root y)" using to_dtree_aux_self assms(1,4) by blast
  then obtain v2 where v2_def: "v2 \<in> dverts y \<and> e \<in> out_arcs T v2"
    using darcs_in_out_arcs e_def by blast
  then have "v2 \<noteq> v1" using v1_def v2_def dverts_disjoint assms dtrees_neq_if_darcs_neq by blast
  then show False using v1_def v2_def by simp
qed

lemma wf_darcs_to_dtree_aux1: "r \<notin> verts T \<Longrightarrow> wf_darcs (to_dtree_aux r)"
  using to_dtree_aux_empty_if_notT unfolding wf_darcs_def by simp

lemma wf_darcs_to_dtree_aux2: "r \<in> verts T \<Longrightarrow> t = to_dtree_aux r \<Longrightarrow> wf_darcs t"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  have "\<forall>(x,e) \<in> fset xs. wf_darcs x"
  proof (standard, standard)
    fix xp x e
    assume asm: "xp \<in> fset xs" "xp = (x,e)"
    then have 0: "x = to_dtree_aux (Dtree.root x)" using to_dtree_aux_self "1.prems"(2) by simp
    have "r \<rightarrow>\<^bsub>T\<^esub> Dtree.root x" using asm "1.prems" \<open>r = r'\<close>
      by (metis (no_types, opaque_lifting) dominated_if_child fst_conv image_iff)
    then have "Dtree.root x \<in> verts T" using adj_in_verts(2) by simp
    then show "wf_darcs x" using "1.IH" asm 0 by blast
  qed
  moreover have "\<forall>(x,e1) \<in> fset xs. (\<forall>(y,e2) \<in> fset xs.
    (darcs x \<union> {e1}) \<inter> (darcs y \<union> {e2}) = {} \<or> (x,e1)=(y,e2))"
    using darcs_disjoint "1.prems" \<open>r = r'\<close> by blast
  ultimately show ?case using darcs_not_in_subtree "1.prems" \<open>r = r'\<close>
    by (smt (verit) case_prodD case_prodI2 wf_darcs_if_darcs'_aux)
qed

lemma wf_darcs_to_dtree_aux: "wf_darcs (to_dtree_aux r)"
  using wf_darcs_to_dtree_aux1 wf_darcs_to_dtree_aux2 by blast

lemma wf_darcs_to_dtree_aux': "t = to_dtree_aux r \<Longrightarrow> wf_darcs t"
  using wf_darcs_to_dtree_aux by blast

lemma wf_darcs_to_dtree: "wf_darcs to_dtree"
  using to_dtree_def wf_darcs_to_dtree_aux by simp

lemma dtail_aux_elem_eq_tail:
  "t = to_dtree_aux r \<Longrightarrow> e \<in> darcs t \<Longrightarrow> dtail t def e = tail T e"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> darcs x \<or> \<not>disjoint_darcs xs
              then b else dtail x def)"
  show ?case
  proof(cases "e \<in> snd ` fset xs")
    case True
    then have 0: "dtail (Node r' xs) def e = r" using \<open>r=r'\<close> by simp
    have "e \<in> out_arcs T r" using dtree_out_arcs_eq_snd "1.prems"(1) True by simp
    then have "tail T e = r" by simp
    then show ?thesis using 0 by blast
  next
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using "1.prems"(2) by force
    then have "x = to_dtree_aux (Dtree.root x)" using "1.prems"(1) \<open>r = r'\<close> to_dtree_aux_self by blast
    then have 0: "dtail x def e = tail T e" using "1.IH" x_def by blast
    have "wf_darcs (Node r xs)" using "1.prems"(1) wf_darcs_to_dtree_aux by simp
    then have "dtail (Node r' xs) def e = dtail x def e"
      using dtail_in_child_eq_child[of x] x_def "1.prems" by force
    then show ?thesis using 0 by simp
  qed
qed

lemma dtail_elem_eq_tail: "e \<in> darcs to_dtree \<Longrightarrow> dtail to_dtree def e = tail T e"
  using dtail_aux_elem_eq_tail to_dtree_def by blast

lemma to_dtree_dtail_eq_tail_aux: "dtail to_dtree (tail T) e = tail T e"
  using dtail_notelem_eq_def dtail_elem_eq_tail by metis

lemma to_dtree_dtail_eq_tail: "dtail to_dtree (tail T) = tail T"
  using to_dtree_dtail_eq_tail_aux by blast

lemma dhead_aux_elem_eq_head:
  "t = to_dtree_aux r \<Longrightarrow> e \<in> darcs t \<Longrightarrow> dhead t def e = head T e"
proof(induction t arbitrary: r rule: darcs_mset.induct)
  case (1 r' xs)
  then have "r = r'" by simp
  let ?f = "(\<lambda>(x,e2) b. if (x,e2) \<notin> fset xs \<or> e \<notin> (darcs x \<union> {e2}) \<or> \<not>disjoint_darcs xs
            then b else if e=e2 then Dtree.root x else dhead x def e)"
  obtain child where "child \<in> fset xs" using "1.prems"(2) by auto
  then have wf: "wf_darcs (Node r xs)" using "1.prems"(1) wf_darcs_to_dtree_aux by simp
  show ?case
  proof(cases "e \<in> snd ` fset xs")
    case True
    then obtain x where x_def: "(x,e) \<in> fset xs" by force
    then have 0: "dhead (Node r' xs) def e = Dtree.root x"
      using dhead_in_set_eq_root wf \<open>r=r'\<close> by fast
    have "e \<in> out_arcs T r" using dtree_out_arcs_eq_snd "1.prems"(1) True by simp
    then have "head T e = Dtree.root x" using x_def "1.prems"(1) dtree_aux_fst_head_snd by force
    then show ?thesis using 0 by simp
  next
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using "1.prems"(2) by force
    then have "x = to_dtree_aux (Dtree.root x)" using "1.prems"(1) \<open>r = r'\<close> to_dtree_aux_self by blast
    then have 0: "dhead x def e = head T e" using "1.IH" x_def by blast
    have "dhead (Node r' xs) def e = dhead x def e"
      using dhead_in_child_eq_child[of x] x_def wf \<open>r=r'\<close> by blast
    then show ?thesis using 0 by simp
  qed
qed

lemma dhead_elem_eq_head: "e \<in> darcs to_dtree \<Longrightarrow> dhead to_dtree def e = head T e"
  using dhead_aux_elem_eq_head to_dtree_def by blast

lemma to_dtree_dhead_eq_head_aux: "dhead to_dtree (head T) e = head T e"
  using dhead_notelem_eq_def dhead_elem_eq_head by metis

lemma to_dtree_dhead_eq_head: "dhead to_dtree (head T) = head T"
  using to_dtree_dhead_eq_head_aux by blast

lemma from_to_dtree_eq_orig: "from_dtree (to_dtree) = T"
  using to_dtree_dhead_eq_head to_dtree_dtail_eq_tail darcs_eq_arcs dverts_eq_verts by simp

lemma subtree_darc_tail_parent:
  "\<lbrakk>is_subtree (Node r xs) to_dtree; (t,e) \<in> fset xs\<rbrakk> \<Longrightarrow> tail T e = r"
  using child_darc_tail_parent to_dtree_self_subtree' by blast

lemma subtree_darc_head_root:
  "\<lbrakk>is_subtree (Node r xs) to_dtree; (t,e) \<in> fset xs\<rbrakk> \<Longrightarrow> head T e = Dtree.root t"
  using child_darc_head_root to_dtree_self_subtree' by blast

lemma subtree_darc_in_arcs:
  "\<lbrakk>is_subtree (Node r xs) to_dtree; (t,e) \<in> fset xs\<rbrakk> \<Longrightarrow> e \<in> arcs T"
  using to_dtree_self_subtree' child_darc_in_arcs by blast

lemma subtree_child_dom: "\<lbrakk>is_subtree (Node r xs) to_dtree; (t,e) \<in> fset xs\<rbrakk> \<Longrightarrow> r \<rightarrow>\<^bsub>T\<^esub> Dtree.root t"
  using subtree_darc_tail_parent subtree_darc_head_root subtree_darc_in_arcs
    in_arcs_imp_in_arcs_ends by fastforce

end

subsubsection "Well-Formed Dtrees"

locale wf_dtree =
  fixes t :: "('a,'b) dtree"
  assumes wf_arcs: "wf_darcs t"
      and wf_verts: "wf_dverts t"

begin

lemma wf_dtree_rec: "Node r xs = t \<Longrightarrow> (x,e) \<in> fset xs \<Longrightarrow> wf_dtree x"
   using wf_arcs wf_verts by (unfold_locales) auto

lemma wf_dtree_sub: "is_subtree x t \<Longrightarrow> wf_dtree x"
using wf_dtree_axioms proof(induction t rule: darcs_mset.induct)
  case (1 r xs)
  then interpret wf_dtree "Node r xs" by blast
  show ?case
  proof(cases "x = Node r xs")
    case True
    then show ?thesis by (simp add: wf_dtree_axioms)
  next
    case False
    then show ?thesis using "1.IH" wf_dtree_rec "1.prems"(1) by auto
  qed
qed

lemma root_not_subtree: "\<lbrakk>(Node r xs) = t; x \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> r \<notin> dverts x"
  using wf_verts root_not_child_if_wf_dverts by fastforce

lemma dverts_child_subset: "\<lbrakk>(Node r xs) = t; x \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> dverts x \<subset> dverts t"
  using root_not_subtree by fastforce

lemma child_arc_not_subtree: "\<lbrakk>(Node r xs) = t; (x,e1) \<in> fset xs\<rbrakk> \<Longrightarrow> e1 \<notin> darcs x"
  using wf_arcs disjoint_darcs_if_wf_aux3 by fast

lemma darcs_child_subset: "\<lbrakk>(Node r xs) = t; x \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> darcs x \<subset> darcs t"
  using child_arc_not_subtree by force

lemma dtail_in_dverts: "e \<in> darcs t \<Longrightarrow> dtail t def e \<in> dverts t"
using wf_arcs proof(induction t rule: darcs_mset.induct)
  case (1 r xs)
  show ?case
  proof(cases "e \<in> snd ` fset xs")
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using "1.prems"(1) by force
    then have "wf_darcs x" using "1.prems"(2) by auto
    then have "dtail x def e \<in> dverts x" using "1.IH" x_def by blast
    then have 0: "dtail x def e \<in> dverts (Node r xs)"
      using x_def by (auto simp: dverts_child_subseteq)
    have "dtail (Node r xs) def e = dtail x def e"
      using dtail_in_child_eq_child[of x] x_def "1.prems"(2) by blast
    then show ?thesis using 0 by argo
  qed (simp)
qed

lemma dtail_in_childverts:
  assumes "e \<in> darcs x" and "(x,e') \<in> fset xs" and "Node r xs = t"
  shows "dtail t def e \<in> dverts x"
proof -
  interpret X: wf_dtree x using assms(2,3) wf_dtree_rec by blast
  have "dtail t def e = dtail x def e"
    using dtail_in_child_eq_child[of x] assms wf_arcs by force
  then show ?thesis using assms(1) X.dtail_in_dverts by simp
qed

lemma dhead_in_dverts: "e \<in> darcs t \<Longrightarrow> dhead t def e \<in> dverts t"
using wf_arcs proof(induction t rule: darcs_mset.induct)
  case (1 r xs)
  show ?case
  proof(cases "e \<in> snd ` fset xs")
    case True
    then obtain x where x_def: "(x,e) \<in> fset xs" by force
    then have "dhead (Node r xs) def e = root x"
      using dhead_in_set_eq_root[of x] "1.prems"(2) by blast
    then show ?thesis using dtree.set_sel(1) x_def by fastforce
  next
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using "1.prems"(1) by force
    then have "wf_darcs x" using "1.prems"(2) by auto
    then have "dhead x def e \<in> dverts x" using "1.IH" x_def by blast
    then have 0: "dhead x def e \<in> dverts (Node r xs)"
      using x_def by (auto simp: dverts_child_subseteq)
    have "dhead (Node r xs) def e = dhead x def e"
      using dhead_in_child_eq_child[of x] x_def "1.prems"(2) by force
    then show ?thesis using 0 by argo
  qed
qed

lemma dhead_in_childverts:
  assumes "e \<in> darcs x" and "(x,e') \<in> fset xs" and "Node r xs = t"
  shows "dhead t def e \<in> dverts x"
proof -
  interpret X: wf_dtree x using wf_arcs wf_verts assms(2,3) by(unfold_locales) auto
  have "dhead t def e = dhead x def e"
    using dhead_in_child_eq_child[of x] assms wf_arcs by auto
  then show ?thesis using assms(1) X.dhead_in_dverts by simp
qed

lemma dhead_in_dverts_no_root: "e \<in> darcs t \<Longrightarrow> dhead t def e \<in> (dverts t - {root t})"
using wf_arcs wf_verts proof(induction t rule: darcs_mset.induct)
  case (1 r xs)
  interpret wf_dtree "Node r xs" using "1.prems"(2,3) by (unfold_locales) auto
  show ?case
  proof(cases "e \<in> snd ` fset xs")
    case True
    then obtain x where x_def: "(x,e) \<in> fset xs" by force
    then have "dhead (Node r xs) def e = root x"
      using dhead_in_set_eq_root[of x] "1.prems"(2) by simp
    then show ?thesis using dtree.set_sel(1) x_def "1.prems"(3) wf_dverts_iff_dverts' by fastforce
  next
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using "1.prems"(1) by force
    then have "wf_darcs x" using "1.prems"(2) by auto
    then have "dhead x def e \<in> dverts x" using "1.IH" x_def "1.prems"(3) by auto
    moreover have "r \<notin> dverts x" using root_not_subtree x_def by fastforce
    ultimately have 0: "dhead x def e \<in> dverts (Node r xs) - {root (Node r xs)}"
      using x_def dverts_child_subseteq by fastforce
    have "dhead (Node r xs) def e = dhead x def e"
      using dhead_in_child_eq_child[of x] x_def "1.prems"(2) by force
    then show ?thesis using 0 by argo
  qed
qed

lemma dhead_in_childverts_no_root:
  assumes "e \<in> darcs x" and "(x,e') \<in> fset xs" and "Node r xs = t"
  shows "dhead t def e \<in> (dverts x - {root x})"
proof -
  interpret X: wf_dtree x using assms(2,3) wf_dtree_rec by blast
  have "dhead t def e = dhead x def e"
    using dhead_in_child_eq_child[of x] assms wf_arcs by auto
  then show ?thesis using assms(1) X.dhead_in_dverts_no_root by simp
qed

lemma dtree_cas_iff_subtree:
  assumes "(x,e1) \<in> fset xs" and "Node r xs = t" and "set p \<subseteq> darcs x"
    shows "pre_digraph.cas (from_dtree dt dh x) u p v
        \<longleftrightarrow> pre_digraph.cas (from_dtree dt dh t) u p v"
      (is "pre_digraph.cas ?X _ _ _ \<longleftrightarrow> pre_digraph.cas ?T _ _ _")
using assms proof(induction p arbitrary: u)
  case Nil
  then show ?case by(simp add: pre_digraph.cas.simps(1))
next
  case (Cons p ps)
  note pre_digraph.cas.simps[simp]
  have "pre_digraph.cas ?T u (p # ps) v = (tail ?T p = u \<and> pre_digraph.cas ?T (head ?T p) ps v)"
    by simp
  also have "\<dots> = (tail ?T p = u \<and> pre_digraph.cas ?X (head ?T p) ps v)"
    using Cons.IH Cons.prems by simp
  also have "\<dots> = (tail ?X p = u \<and> pre_digraph.cas ?X (head ?T p) ps v)"
    using dtail_in_child_eq_child[of x] Cons.prems(1-3) wf_arcs by force
  also have "\<dots> = (tail ?X p = u \<and> pre_digraph.cas ?X (head ?X p) ps v)"
    using dhead_in_child_eq_child[of x] Cons.prems(1-3) wf_arcs by force
  finally show ?case by simp
qed

lemma dtree_cas_exists:
  "v \<in> dverts t \<Longrightarrow> \<exists>p. set p \<subseteq> darcs t \<and> pre_digraph.cas (from_dtree dt dh t) (root t) p v"
using wf_dtree_axioms proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "r=v")
    case True
    then have "pre_digraph.cas (from_dtree dt dh (Node r xs)) (root (Node r xs)) [] v"
      by (simp add: pre_digraph.cas.simps(1))
    then show ?thesis by force
  next
    case False
    then obtain x e where x_def: "(x,e) \<in> fset xs \<and> v \<in> dverts x" using Node.prems by auto
    let ?T = "from_dtree dt dh (Node r xs)"
    let ?X = "from_dtree dt dh x"
    interpret wf_dtree "Node r xs" by (rule Node.prems(2))
    have "wf_dtree x" using x_def wf_dtree_rec by blast
    then obtain p where p_def: "set p \<subseteq> darcs x \<and> pre_digraph.cas ?X (root x) p v"
      using Node.IH x_def by fastforce
    then have "pre_digraph.cas ?T (root x) p v"
      using dtree_cas_iff_subtree x_def Node.prems(2) by blast
    moreover have "head ?T e = root x"
      using x_def dhead_in_set_eq_root[of x] wf_arcs by simp
    moreover have "tail ?T e = r" using x_def by force
    ultimately have "pre_digraph.cas ?T (root (Node r xs)) (e#p) v"
      by (simp add: pre_digraph.cas.simps(2))
    moreover have "set (e#p) \<subseteq> darcs (Node r xs)" using p_def x_def by force
    ultimately show ?thesis by blast
  qed
qed

lemma dtree_awalk_exists:
  assumes "v \<in> dverts t"
  shows "\<exists>p. pre_digraph.awalk (from_dtree dt dh t) (root t) p v"
unfolding pre_digraph.awalk_def using dtree_cas_exists assms dtree.set_sel(1) by fastforce

lemma subtree_root_not_root: "t = Node r xs \<Longrightarrow> (x,e) \<in> fset xs \<Longrightarrow> root x \<noteq> r"
  using dtree.set_sel(1) root_not_subtree by fastforce

lemma dhead_not_root:
  assumes "e \<in> darcs t"
  shows "dhead t def e \<noteq> root t"
proof -
  obtain r xs where xs_def[simp]: "t = Node r xs" using dtree.exhaust by auto
  show ?thesis
  proof(cases "e \<in> snd ` fset xs")
    case True
    then obtain x where x_def: "(x,e) \<in> fset xs" by force
    then have "dhead (Node r xs) def e = root x"
      using dhead_in_set_eq_root[of x] wf_arcs by simp
    then show ?thesis using x_def subtree_root_not_root by simp
  next
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using assms by force
    then interpret X: wf_dtree x using wf_dtree_rec by auto
    have "dhead x def e \<in> dverts x" using x_def X.dhead_in_dverts by blast
    moreover have "dhead (Node r xs) def e = dhead x def e"
      using x_def dhead_in_child_eq_child[of x] wf_arcs by force
    ultimately show ?thesis using x_def root_not_subtree by fastforce
  qed
qed

lemma nohead_cas_no_arc_in_subset:
  "\<lbrakk>\<forall>e\<in>darcs t. dhead t dh e \<noteq> v; p\<noteq>[]; pre_digraph.cas (from_dtree dt dh t) u p v\<rbrakk>
    \<Longrightarrow> \<not>set p \<subseteq> darcs t"
  by(induction p arbitrary: u) (fastforce simp: pre_digraph.cas.simps)+

lemma dtail_root_in_set:
  assumes "e \<in> darcs t" and "t = Node r xs" and "dtail t dt e = r"
  shows "e \<in> snd ` fset xs"
proof (rule ccontr)
  assume "e \<notin> snd ` fset xs"
  then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using assms(1,2) by force
  interpret X: wf_dtree x using assms(2) x_def wf_dtree_rec by blast
  have "dtail t dt e = dtail x dt e"
    using dtail_in_child_eq_child[of x] wf_arcs assms(2) x_def by force
  then have "dtail t dt e \<in> dverts x" using X.dtail_in_dverts x_def by simp
  then show False using assms(2,3) wf_verts x_def unfolding wf_dverts_iff_dverts' by auto
qed

lemma dhead_notin_subtree_wo_root:
  assumes "(x,e) \<in> fset xs" and "p \<notin> darcs x" and "p \<in> darcs t" and "t = Node r xs"
  shows "dhead t dh p \<notin> (dverts x - {root x})"
proof(cases "p \<in> snd ` fset xs")
  case True
  then obtain x' where x'_def: "(x',p) \<in> fset xs" by auto
  then have 0: "dhead t dh p = root x'"
    using dhead_in_set_eq_root[of x'] wf_arcs assms(4) by auto
  have "root x' \<notin> (dverts x - {root x})"
  proof(cases "x'=x")
    case True
    then show ?thesis by blast
  next
    case False
    have "root x' \<in> dverts x'" by (simp add: dtree.set_sel(1))
    then show ?thesis using wf_verts x'_def assms(1,4) unfolding wf_dverts_iff_dverts' by fastforce
  qed
  then show ?thesis using 0 by simp
next
  case False
  then obtain x' e1 where x'_def: "(x',e1) \<in> fset xs \<and> p \<in> darcs x'" using assms(3,4) by force
  then have 0: "dhead t dh p = dhead x' dh p"
    using dhead_in_child_eq_child[of x'] wf_arcs assms(4) by auto
  interpret X: wf_dtree x' using assms(4) x'_def wf_dtree_rec by blast
  have 1: "dhead x' dh p \<in> dverts x'" using X.dhead_in_dverts x'_def by blast
  moreover have "dverts x' \<inter> dverts x = {}"
    using wf_verts x'_def assms(1,2,4) unfolding wf_dverts_iff_dverts' by fastforce
  ultimately show ?thesis using 0 by auto
qed

lemma subtree_uneq_if_arc_uneq:
  "\<lbrakk>(x1,e1) \<in> fset xs; (x2,e2) \<in> fset xs; e1\<noteq>e2; Node r xs = t\<rbrakk> \<Longrightarrow> x1 \<noteq> x2"
  using dtree.set_sel(1) wf_verts disjoint_dverts_if_wf_aux by fast

lemma arc_uneq_if_subtree_uneq:
  "\<lbrakk>(x1,e1) \<in> fset xs; (x2,e2) \<in> fset xs; x1\<noteq>x2; Node r xs = t\<rbrakk> \<Longrightarrow> e1 \<noteq> e2"
  using disjoint_darcs_if_wf[OF wf_arcs] by fastforce

lemma dhead_unique: "e \<in> darcs t \<Longrightarrow> p \<in> darcs t \<Longrightarrow> e \<noteq> p \<Longrightarrow> dhead t dh e \<noteq> dhead t dh p"
using wf_dtree_axioms proof(induction t rule: darcs_mset.induct)
  case ind: (1 r xs)
  then interpret wf_dtree "Node r xs" by blast
  show ?case
  proof(cases "\<exists>x \<in> fst ` fset xs. e \<in> darcs x \<and> p \<in> darcs x")
    case True
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x \<and> p \<in> darcs x" by force
    then have "wf_dtree x" using ind.prems(4) wf_dtree_rec by blast
    then have "dhead x dh e \<noteq> dhead x dh p" using ind x_def by blast
    then show ?thesis using True dhead_in_child_eq_child[of x] wf_arcs x_def by force
  next
    case False
    then consider "\<exists>x \<in> fst ` fset xs. e \<in> darcs x" | "\<exists>x \<in> fst ` fset xs. p \<in> darcs x"
      | "e \<in> snd ` fset xs \<and> p \<in> snd ` fset xs"
      using ind.prems(1,2) by force
    then show ?thesis
    proof(cases)
      case 1
      then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x \<and> p \<notin> darcs x"
        using False by force
      then interpret X: wf_dtree x using wf_dtree_rec by blast
      have "dhead x dh e \<in> (dverts x - {root x})" using X.dhead_in_dverts_no_root x_def by blast
      then have "dhead (Node r xs) dh e \<in> (dverts x - {root x})"
        using dhead_in_child_eq_child[of x] wf_arcs x_def by force
      moreover have "dhead (Node r xs) dh p \<notin> (dverts x - {root x})"
        using x_def dhead_notin_subtree_wo_root ind.prems(2) by blast
      ultimately show ?thesis by auto
    next
      case 2
      then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> p \<in> darcs x \<and> e \<notin> darcs x"
        using False by force
      then interpret X: wf_dtree x using wf_dtree_rec by blast
      have "dhead x dh p \<in> (dverts x - {root x})" using X.dhead_in_dverts_no_root x_def by blast
      then have "dhead (Node r xs) dh p \<in> (dverts x - {root x})"
        using dhead_in_child_eq_child[of x] wf_arcs x_def by force
      moreover have "dhead (Node r xs) dh e \<notin> (dverts x - {root x})"
        using x_def dhead_notin_subtree_wo_root ind.prems(1) by blast
      ultimately show ?thesis by auto
    next
      case 3
      then obtain x1 x2 where x_def: "(x1,p) \<in> fset xs \<and> (x2,e) \<in> fset xs" by force
      then have 0: "dhead (Node r xs) dh p = root x1 \<and> dhead (Node r xs) dh e = root x2"
        using dhead_in_set_eq_root[of x1] dhead_in_set_eq_root[of x2] wf_arcs by simp
      have "x1 \<noteq> x2" using subtree_uneq_if_arc_uneq x_def ind.prems(3) by blast
      then have "root x1 \<noteq> root x2"
        using wf_verts x_def dtree.set_sel(1) unfolding wf_dverts_iff_dverts' by fastforce
      then show ?thesis using 0 by argo
    qed
  qed
qed

lemma arc_in_subtree_if_tail_in_subtree:
  assumes "dtail t dt p \<in> dverts x"
      and "p \<in> darcs t"
      and "t = Node r xs"
      and "(x,e) \<in> fset xs"
    shows "p \<in> darcs x"
proof (rule ccontr)
  assume asm: "p \<notin> darcs x"
  show False
  proof(cases "p \<in> snd ` fset xs")
    case True
    then have "dtail t dt p = r" using assms(2,3) by simp
    then show ?thesis using assms(1,3,4) root_not_subtree by force
  next
    case False
    then obtain x' e1 where x'_def: "(x',e1) \<in> fset xs \<and> p \<in> darcs x'" using assms(2,3) by force
    then have "x \<noteq> x'" using asm by blast
    interpret X: wf_dtree x' using x'_def assms(3) wf_dtree_rec by blast
    have "dtail t dt p = dtail x' dt p"
      using dtail_in_child_eq_child[of x'] x'_def wf_arcs assms(3) by force
    then have "dtail t dt p \<in> dverts x'" using X.dtail_in_dverts by (simp add: x'_def)
    then have "dtail t dt p \<notin> dverts x"
      using \<open>x\<noteq>x'\<close> wf_verts assms(3,4) x'_def unfolding wf_dverts_iff_dverts' by fastforce
    then show ?thesis using assms(1) by blast
  qed
qed

lemma dhead_in_verts_if_dtail:
  assumes "dtail t dt p \<in> dverts x"
      and "p \<in> darcs t"
      and "t = Node r xs"
      and "(x,e) \<in> fset xs"
    shows "dhead t dh p \<in> dverts x"
proof -
  interpret X: wf_dtree x using assms(3,4) wf_dtree_rec by blast
  have 0: "p \<in> darcs x" using assms arc_in_subtree_if_tail_in_subtree by blast
  then have "dhead t dh p = dhead x dh p"
    using dhead_in_child_eq_child[of x] assms(3,4) wf_arcs by simp
  then show ?thesis using X.dhead_in_dverts 0 by simp
qed

lemma cas_darcs_in_subtree:
  assumes "pre_digraph.cas (from_dtree dt dh t) u ps v"
      and "set ps \<subseteq> darcs t"
      and "t = Node r xs"
      and "(x,e) \<in> fset xs"
      and "u \<in> dverts x"
    shows "set ps \<subseteq> darcs x"
using assms proof(induction ps arbitrary: u)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  note pre_digraph.cas.simps[simp]
  then have u_p: "dtail t dt p = u" using Cons.prems(1) by simp
  have "p \<in> darcs t" using Cons.prems(2) by simp
  then have 0: "p \<in> darcs x" using arc_in_subtree_if_tail_in_subtree Cons.prems(3-5) u_p by blast
  have 1: "dhead t dh p \<in> dverts x" using dhead_in_verts_if_dtail Cons.prems(2-5) u_p by force
  have "set ps \<subseteq> darcs t" using Cons.prems(2) by simp
  have "pre_digraph.cas (from_dtree dt dh t) (dhead t dh p) ps v" using Cons.prems(1) by simp
  then have "set ps \<subseteq> darcs x" using Cons.IH Cons.prems(2,3,4) 1 by simp
  then show ?case using 0 by simp
qed

lemma dtree_cas_in_subtree:
  assumes "pre_digraph.cas (from_dtree dt dh t) u ps v"
      and "set ps \<subseteq> darcs t"
      and "t = Node r xs"
      and "(x,e) \<in> fset xs"
      and "u \<in> dverts x"
    shows "pre_digraph.cas (from_dtree dt dh x) u ps v"
  using assms cas_darcs_in_subtree dtree_cas_iff_subtree by fast

lemma cas_to_end_subtree:
  assumes "set (p#ps) \<subseteq> darcs t" and "pre_digraph.cas (from_dtree dt dh t) (root t) (p#ps) v"
      and "t = Node r xs" and "(x,e) \<in> fset xs" and "v \<in> dverts x"
    shows "p = e"
proof (rule ccontr)
  assume asm: "p \<noteq> e"
  note pre_digraph.cas.simps[simp]
  have "dtail t dt p = r" using assms(2,3) by simp
  then have "p \<in> snd ` fset xs" using dtail_root_in_set assms(1,3) list.set_intros(1) by fast
  then obtain x' where x'_def: "(x',p) \<in> fset xs" by force
  show False
  proof(cases "ps=[]")
    case True
    then have "root x' = v"
      using dhead_in_set_eq_root[of x'] x'_def assms(2,3) wf_arcs by simp
    then have "x = x'"
      using wf_verts x'_def assms(3,4,5) dtree.set_sel(1) by (fastforce simp: wf_dverts_iff_dverts')
    then show ?thesis using asm assms(3,4) subtree_uneq_if_arc_uneq x'_def by blast
  next
    case False
    interpret X: wf_dtree x'  using wf_dtree_rec x'_def assms(3) by blast
    have "x' \<noteq> x" using asm assms(3,4) subtree_uneq_if_arc_uneq x'_def by blast
    then have x'_no_v: "\<forall>e\<in>darcs x'. dhead x' dh e \<noteq> v"
      using X.dhead_in_dverts assms(3,4,5) x'_def wf_verts
      by (fastforce simp: wf_dverts_iff_dverts')
    have 0: "pre_digraph.cas (from_dtree dt dh t) (dhead t dh p) ps v" using assms(2) by simp
    have 1: "dhead t dh p \<in> dverts x'"
      using dhead_in_set_eq_root[of x'] x'_def assms(3) dtree.set_sel(1) wf_arcs by auto
    then have "pre_digraph.cas (from_dtree dt dh x') (dhead t dh p) ps v"
      using dtree_cas_in_subtree x'_def assms(1,3) 0 by force
    then have "\<not> set ps \<subseteq> darcs x'" using X.nohead_cas_no_arc_in_subset x'_no_v False by blast
    moreover have "set ps \<subseteq> darcs x'" using cas_darcs_in_subtree assms(1,3) x'_def 0 1 by simp
    ultimately show ?thesis by blast
  qed
qed

lemma cas_unique_in_darcs: "\<lbrakk>v \<in> dverts t; pre_digraph.cas (from_dtree dt dh t) (root t) ps v;
        pre_digraph.cas (from_dtree dt dh t) (root t) es v\<rbrakk>
       \<Longrightarrow> ps = es \<or> \<not>set ps \<subseteq> darcs t \<or> \<not>set es \<subseteq> darcs t"
using wf_dtree_axioms proof(induction t arbitrary: ps es rule: darcs_mset.induct)
  case ind: (1 r xs)
  interpret wf_dtree "Node r xs" by (rule ind.prems(4))
  show ?case
  proof(cases "r=v")
    case True
    have 0: "\<forall>e \<in> darcs (Node r xs). dhead (Node r xs) dh e \<noteq> r" using dhead_not_root by force
    consider "ps = [] \<and> es = []" | "ps \<noteq> []" | "es \<noteq> []" by blast
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis by blast
    next
      case 2
      then show ?thesis using nohead_cas_no_arc_in_subset 0 ind.prems(2) True by blast
    next
      case 3
      then show ?thesis using nohead_cas_no_arc_in_subset 0 ind.prems(3) True by blast
    qed
  next
    case False
    then obtain x e where x_def: "(x,e) \<in> fset xs" "v \<in> dverts x" using ind.prems by auto
    then have wf_x: "wf_dtree x" using wf_dtree_rec by blast
    note pre_digraph.cas.simps[simp]
    have nempty: "ps \<noteq> [] \<and> es \<noteq> []" using ind.prems(2,3) False by force
    then obtain p ps' where p_def: "ps = p # ps'" using list.exhaust_sel by auto
    obtain e' es' where e'_def: "es = e' # es'" using list.exhaust_sel nempty by auto
    show ?thesis
    proof (rule ccontr)
      assume "\<not>(ps = es \<or> \<not>set ps \<subseteq> darcs (Node r xs) \<or> \<not>set es \<subseteq> darcs (Node r xs))"
      then have asm: "ps \<noteq> es \<and> set ps \<subseteq> darcs (Node r xs) \<and> set es \<subseteq> darcs (Node r xs)" by blast
      then have "p = e" using cas_to_end_subtree p_def ind.prems(2) x_def by blast
      moreover have "e' = e" using cas_to_end_subtree e'_def ind.prems(3) x_def asm by blast
      ultimately have "p = e'" by blast
      have "dhead (Node r xs) dh p = root x"
        using dhead_in_set_eq_root[of x] x_def(1) \<open>p=e\<close> wf_arcs by simp
      then have cas_p_r: "pre_digraph.cas (from_dtree dt dh (Node r xs)) (root x) ps' v"
        using ind.prems(2) p_def by fastforce
      moreover have 0: "root x \<in> dverts x" using dtree.set_sel(1) by blast
      ultimately have cas_ps: "pre_digraph.cas (from_dtree dt dh x) (root x) ps' v"
        using dtree_cas_in_subtree asm x_def(1) p_def dtree.set_sel(1) by force
      have "dhead (Node r xs) dh e' = root x"
        using dhead_in_set_eq_root[of x] x_def \<open>e'=e\<close> wf_arcs by simp
      then have cas_e_r: "pre_digraph.cas (from_dtree dt dh (Node r xs)) (root x) es' v"
        using ind.prems(3) e'_def by fastforce
      then have "pre_digraph.cas (from_dtree dt dh x) (root x) es' v"
        using dtree_cas_in_subtree asm x_def(1) e'_def 0 by force
      then have "ps' = es' \<or> \<not> set ps' \<subseteq> darcs x \<or> \<not> set es' \<subseteq> darcs x"
        using ind.IH cas_ps x_def wf_x by blast
      moreover have "set ps' \<subseteq> darcs x"
        using cas_darcs_in_subtree cas_p_r x_def(1) asm p_def 0 set_subset_Cons by fast
      moreover have "set es' \<subseteq> darcs x"
        using cas_darcs_in_subtree cas_e_r x_def(1) asm e'_def 0 set_subset_Cons by fast
      ultimately have "ps' = es'" by blast
      then show False using asm p_def e'_def \<open>p=e'\<close> by blast
    qed
  qed
qed

lemma dtree_awalk_unique:
  "\<lbrakk>v \<in> dverts t; pre_digraph.awalk (from_dtree dt dh t) (root t) ps v;
    pre_digraph.awalk (from_dtree dt dh t) (root t) es v\<rbrakk>
     \<Longrightarrow> ps = es"
  unfolding pre_digraph.awalk_def using cas_unique_in_darcs by fastforce

lemma dtree_unique_awalk_exists:
  assumes "v \<in> dverts t"
  shows "\<exists>!p. pre_digraph.awalk (from_dtree dt dh t) (root t) p v"
  using dtree_awalk_exists dtree_awalk_unique assms by blast

lemma from_dtree_directed: "directed_tree (from_dtree dt dh t) (root t)"
  apply(unfold_locales)
  by(auto simp: dtail_in_dverts dhead_in_dverts dtree.set_sel(1) dtree_unique_awalk_exists)

theorem from_dtree_fin_directed: "finite_directed_tree (from_dtree dt dh t) (root t)"
  apply(unfold_locales)
  by(auto simp: dtail_in_dverts dhead_in_dverts dtree.set_sel(1) dtree_unique_awalk_exists
      finite_dverts finite_darcs)

subsubsection "Identity of Transformation Operations"

lemma dhead_img_eq_root_img:
  "Node r xs = t
    \<Longrightarrow> (\<lambda>e. ((dhead (Node r xs) dh e), e)) ` snd ` fset xs = (\<lambda>(x,e). (root x, e)) ` fset xs"
  using dhead_in_set_eq_root wf_arcs snd_conv image_image disjoint_darcs_if_wf_xs
  by (smt (verit) case_prodE case_prod_conv image_cong)

lemma childarcs_in_out_arcs:
  "\<lbrakk>Node r xs = t; e \<in> snd ` fset xs\<rbrakk> \<Longrightarrow> e \<in> out_arcs (from_dtree dt dh t) r"
  by force

lemma out_arcs_in_childarcs:
  assumes "Node r xs = t" and "e \<in> out_arcs (from_dtree dt dh t) r"
  shows "e \<in> snd ` fset xs"
proof (rule ccontr)
  assume asm: "e \<notin> snd ` fset xs"
  have "e \<in> darcs t" using assms(2) by simp
  then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> e \<in> darcs x" using assms(1) asm by force
  then have "dtail t dt e \<in> dverts x" using assms(1) dtail_in_childverts by blast
  moreover have "r \<notin> dverts x" using assms(1) wf_verts x_def by (auto simp: wf_dverts_iff_dverts')
  ultimately show False using assms(2) by simp
qed

lemma childarcs_eq_out_arcs:
  "Node r xs = t \<Longrightarrow> snd ` fset xs = out_arcs (from_dtree dt dh t) r"
  using childarcs_in_out_arcs out_arcs_in_childarcs by fast

lemma dtail_in_subtree_eq_subtree:
  "\<lbrakk>is_subtree t1 t; e \<in> darcs t1\<rbrakk> \<Longrightarrow> dtail t def e = dtail t1 def e"
using wf_arcs proof(induction t rule: darcs_mset.induct)
  case (1 r xs)
  show ?case
  proof(cases "Node r xs=t1")
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> is_subtree t1 x" using "1.prems"(1) by auto
    then have "e \<in> darcs x" using "1.prems"(2) darcs_subtree_subset by blast
    then have "dtail (Node r xs) def e = dtail x def e"
      using dtail_in_child_eq_child[of x] x_def "1.prems"(3) by blast
    then show ?thesis using "1.IH" x_def "1.prems"(2-3) by fastforce
  qed (simp)
qed

lemma dtail_in_subdverts:
  assumes "e \<in> darcs x" and "is_subtree x t"
  shows "dtail t def e \<in> dverts x"
proof -
  interpret X: wf_dtree x by (simp add: assms(2) wf_dtree_sub)
  have "dtail t def e = dtail x def e" using dtail_in_subtree_eq_subtree assms(1,2) by blast
  then show ?thesis using assms(1) X.dtail_in_dverts by simp
qed

lemma dhead_in_subtree_eq_subtree:
  "\<lbrakk>is_subtree t1 t; e \<in> darcs t1\<rbrakk> \<Longrightarrow> dhead t def e = dhead t1 def e"
using wf_arcs proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "Node r xs=t1")
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs \<and> is_subtree t1 x" using Node.prems(1) by auto
    then have "e \<in> darcs x" using Node.prems(2) darcs_subtree_subset by blast
    then have "dhead (Node r xs) def e = dhead x def e"
      using dhead_in_child_eq_child[of x] x_def Node.prems(3) by force
    then show ?thesis using Node.IH x_def Node.prems(2-3) by fastforce
  qed (simp)
qed

lemma subarcs_in_out_arcs:
  assumes "is_subtree (Node r xs) t" and "e \<in> snd ` fset xs"
  shows "e \<in> out_arcs (from_dtree dt dh t) r"
proof -
  have "e \<in> darcs (Node r xs)" using assms(2) by force
  then have "tail (from_dtree dt dh t) e = r"
    using dtail_in_subtree_eq_subtree assms(1,2) by auto
  then show ?thesis using darcs_subtree_subset assms(1,2) by fastforce
qed

lemma darc_in_sub_if_dtail_in_sub:
  assumes "dtail t dt e = v" and "e \<in> darcs t" and "(x,e1) \<in> fset xs"
      and "is_subtree t1 x" and "Node r xs = t" and "v \<in> dverts t1"
    shows "e \<in> darcs x"
proof (rule ccontr)
  assume asm: "e \<notin> darcs x"
  have "e \<notin> snd ` fset xs"
    using assms(1-6) asm arc_in_subtree_if_tail_in_subtree dverts_subtree_subset
    by (metis subset_eq)
  then obtain x2 e2 where x2_def: "(x2,e2) \<in> fset xs \<and> e \<in> darcs x2" using assms(2,5) by force
  then have "v \<in> dverts x" using assms(4,6) dverts_subtree_subset by fastforce
  then have "v \<notin> dverts x2" using assms(1-3,5) arc_in_subtree_if_tail_in_subtree asm by blast
  then have "dtail x2 dt e \<noteq> v" using assms(1,5) dtail_in_childverts x2_def by fast
  then have "dtail t dt e = dtail x2 dt e"
    using assms(1,5) x2_def \<open>v \<notin> dverts x2\<close> dtail_in_childverts by blast
  then show False using assms(1) \<open>dtail x2 dt e \<noteq> v\<close> by simp
qed

lemma out_arcs_in_subarcs_aux:
  assumes "is_subtree (Node r xs) t" and "dtail t dt e = r" and "e \<in> darcs t"
  shows "e \<in> snd ` fset xs"
using assms wf_dtree_axioms proof(induction t)
  case (Node v ys)
  then interpret wf_dtree "Node v ys" by blast
  show ?case
  proof(cases "Node v ys = Node r xs")
    case True
    then show ?thesis using dtail_root_in_set Node.prems(2,3) by blast
  next
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset ys \<and> is_subtree (Node r xs) x"
      using Node.prems(1) by auto
    then have "e \<in> darcs x"
      using darc_in_sub_if_dtail_in_sub Node.prems(2,3) dtree.set_intros(1) by fast
    moreover from this have "dtail x dt e = r"
      using dtail_in_child_eq_child[of x] x_def Node.prems(2) wf_arcs by force
    moreover from this have "wf_dtree x" using wf_verts wf_arcs x_def by(unfold_locales) auto
    ultimately show ?thesis using Node.IH x_def by force
  qed
qed

lemma out_arcs_in_subarcs:
  assumes "is_subtree (Node r xs) t" and "e \<in> out_arcs (from_dtree dt dh t) r"
  shows "e \<in> snd ` fset xs"
  using assms out_arcs_in_subarcs_aux by auto

lemma subarcs_eq_out_arcs:
  "is_subtree (Node r xs) t \<Longrightarrow> snd ` fset xs = out_arcs (from_dtree dt dh t) r"
  using subarcs_in_out_arcs out_arcs_in_subarcs by fast

lemma dhead_sub_img_eq_root_img:
  "is_subtree (Node v ys) t
    \<Longrightarrow> (\<lambda>e. ((dhead t dh e), e)) ` snd ` fset ys = (\<lambda>(x,e). (root x, e)) ` fset ys"
using wf_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret wf_dtree "Node r xs" by blast
  show ?case
  proof(cases "Node v ys = Node r xs")
    case True
    then show ?thesis using dhead_img_eq_root_img by simp
  next
    case False
    then obtain x e where x_def: "(x,e) \<in> fset xs \<and> is_subtree (Node v ys) x"
      using Node.prems(1) by auto
    then interpret X: wf_dtree x using wf_verts wf_arcs by(unfold_locales) auto
    have "\<forall>a \<in> snd ` fset ys. (\<lambda>e. ((dhead (Node r xs) dh e), e)) a = (\<lambda>e. ((dhead x dh e), e)) a"
    proof
      fix a
      assume asm: "a \<in> snd ` fset ys"
      then have "a \<in> darcs x" using x_def darcs_subtree_subset by fastforce
      then show "(\<lambda>e. ((dhead (Node r xs) dh e), e)) a = (\<lambda>e. ((dhead x dh e), e)) a"
        using dhead_in_child_eq_child[of x] x_def wf_arcs by auto
    qed
    then have "(\<lambda>e. ((dhead (Node r xs) dh e), e)) ` snd ` fset ys
            = (\<lambda>e. ((dhead x dh e), e)) ` snd ` fset ys"
      by (meson image_cong)
    then show ?thesis using Node.IH x_def X.wf_dtree_axioms by force
  qed
qed

lemma subtree_to_dtree_aux_eq:
  assumes "is_subtree x t" and "v \<in> dverts x"
  shows "finite_directed_tree.to_dtree_aux (from_dtree dt dh t) v
        = finite_directed_tree.to_dtree_aux (from_dtree dt dh x) v
      \<and> finite_directed_tree.to_dtree_aux (from_dtree dt dh x) (root x) = x"
using assms wf_dtree_axioms proof(induction x arbitrary: t v rule: darcs_mset.induct)
  case ind: (1 r xs)
  then interpret wf_dtree t by blast
  obtain r' xs' where r'_def: "t = Node r' xs'" using dtree.exhaust by auto
  interpret R_xs: wf_dtree "Node r xs" using ind.prems(1,3) wf_dtree_sub by simp
  let ?todt = "finite_directed_tree.to_dtree_aux"
  let ?T = "(from_dtree dt dh t)"
  let ?X = "(from_dtree dt dh (Node r xs))"
  interpret DT: finite_directed_tree ?T "root t" using from_dtree_fin_directed by blast
  interpret XT: finite_directed_tree ?X "root (Node r xs)"
    using R_xs.from_dtree_fin_directed by blast

  (* goal 2 *)
  have ih: "\<forall>y \<in> fset xs. (\<lambda>(x,e). (XT.to_dtree_aux (root x), e)) y = y"
  proof
    fix y
    assume asm: "y \<in> fset xs"
    obtain x e where x_def: "y = (x,e)" by fastforce
    then have "is_subtree x (Node r xs)" using subtree_if_child asm
      by (metis image_iff prod.sel(1))
    then have "?todt (from_dtree dt dh x) (root x) = x
            \<and> XT.to_dtree_aux (root x) = ?todt (from_dtree dt dh x) (root x)"
      using ind.IH R_xs.wf_dtree_axioms asm x_def dtree.set_sel(1) by blast
    then have "XT.to_dtree_aux (root x) = x" by simp
    then show "(\<lambda>(x,e). (XT.to_dtree_aux (root x), e)) y = y" using x_def by fast
  qed
  let ?f = "\<lambda>(x,e). (XT.to_dtree_aux x, e)"
  let ?g = "\<lambda>e. ((dhead (Node r xs) dh e), e)"
  obtain ys where ys_def: "XT.to_dtree_aux (root (Node r xs)) = Node r ys"
    using dtree.exhaust dtree.sel(1) XT.to_dtree_aux_root by metis
  then have "fset ys = (\<lambda>e. (XT.to_dtree_aux (head ?X e), e)) ` out_arcs ?X r"
    using XT.dtree_children_img_alt XT.dtree_children_fset_id dtree.sel(1) by (smt (verit))
  also have "\<dots> = (\<lambda>e. (XT.to_dtree_aux (dhead (Node r xs) dh e), e)) ` (snd ` fset xs)"
    using R_xs.childarcs_eq_out_arcs by simp
  also have "\<dots> = ?f ` ?g ` (snd ` fset xs)" by fast
  also have "\<dots> = ?f ` (\<lambda>(x,e). (root x, e)) ` fset xs" using R_xs.dhead_img_eq_root_img by simp
  also have "\<dots> = (\<lambda>(x,e). (XT.to_dtree_aux (root x), e)) ` fset xs" by fast
  also have "\<dots> = fset xs" using ih by simp
  finally have g2: "ys = xs" by (simp add: fset_inject)

  show ?case
  proof(cases "v = r")
    case True
    (* goal 1 *)
    have 0: "\<forall>y \<in> fset xs. (\<lambda>(x,e). (DT.to_dtree_aux (root x), e)) y = y"
    proof
      fix y
      assume asm: "y \<in> fset xs"
      obtain x e where x_def: "y = (x,e)" by fastforce
      then have "is_subtree x (Node r xs)" using subtree_if_child asm
        by (metis image_iff prod.sel(1))
      then have "is_subtree x t" using asm subtree_trans ind.prems(1) by blast
      then have "?todt (from_dtree dt dh x) (root x) = x
              \<and> DT.to_dtree_aux (root x) = ?todt (from_dtree dt dh x) (root x)"
        using ind.IH wf_dtree_axioms asm x_def dtree.set_sel(1) by blast
      then have "DT.to_dtree_aux (root x) = x" by simp
      then show "(\<lambda>(x,e). (DT.to_dtree_aux (root x), e)) y = y" using x_def by fast
    qed
    let ?f = "\<lambda>(x,e). (DT.to_dtree_aux x, e)"
    let ?g = "\<lambda>e. ((dhead (Node r' xs') dh e), e)"
    obtain zs where zs_def: "DT.to_dtree_aux v = Node v zs"
      using dtree.exhaust by simp
    then have "fset zs = (\<lambda>e. (DT.to_dtree_aux (head ?T e), e)) ` out_arcs ?T r"
      using DT.dtree_children_img_alt DT.dtree_children_fset_id True by presburger
    also have "\<dots> = (\<lambda>e. (DT.to_dtree_aux (dhead t dh e), e)) ` (snd ` fset xs)"
      using ind.prems(1) subarcs_eq_out_arcs by force
    also have "\<dots> = ?f ` ?g ` (snd ` fset xs)" using r'_def by fast
    also have "\<dots> = ?f ` (\<lambda>(x,e). (root x, e)) ` fset xs"
      using dhead_sub_img_eq_root_img ind.prems(1) r'_def by blast
    also have "\<dots> = (\<lambda>(x,e). (DT.to_dtree_aux (root x), e)) ` fset xs" by fast
    also have "\<dots> = fset xs" using 0 by simp
    finally have g1: "zs = xs" by (simp add: fset_inject)
    then show ?thesis using zs_def True g2 ys_def by simp
  next
    case False
    (* goal 1 *)
    then obtain x1 e1 where x_def: "(x1,e1) \<in> fset xs" "v \<in> dverts x1" using ind.prems(2) by auto
    then have "is_subtree x1 (Node r xs)" using subtree_if_child
      by (metis image_iff prod.sel(1))
    moreover from this have "is_subtree x1 t" using ind.prems(1) subtree_trans by blast
    ultimately have g1: "DT.to_dtree_aux v = XT.to_dtree_aux v"
      using ind.IH x_def by (metis R_xs.wf_dtree_axioms wf_dtree_axioms)
    then show ?thesis using g1 g2 ys_def by blast
  qed
qed

interpretation T: finite_directed_tree "from_dtree dt dh t" "root t"
  using from_dtree_fin_directed by simp

lemma to_from_dtree_aux_id: "T.to_dtree_aux dt dh (root t) = t"
  using subtree_to_dtree_aux_eq dtree.set_sel(1) self_subtree by blast

theorem to_from_dtree_id: "T.to_dtree dt dh = t"
  using to_from_dtree_aux_id T.to_dtree_def by simp

end

context finite_directed_tree
begin

lemma wf_to_dtree_aux: "wf_dtree (to_dtree_aux r)"
  unfolding wf_dtree_def using wf_dverts_to_dtree_aux wf_darcs_to_dtree_aux by blast

theorem wf_to_dtree: "wf_dtree to_dtree"
  unfolding to_dtree_def using wf_to_dtree_aux by blast

end

subsection \<open>Degrees of Nodes\<close>

fun max_deg :: "('a,'b) dtree \<Rightarrow> nat" where
  "max_deg (Node r xs) = (if xs = {||} then 0 else max (Max (max_deg ` fst ` fset xs)) (fcard xs))"

lemma mdeg_eq_fcard_if_empty: "xs = {||} \<Longrightarrow> max_deg (Node r xs) = fcard xs"
  by simp

lemma mdeg0_if_fcard0: "fcard xs = 0 \<Longrightarrow> max_deg (Node r xs) = 0"
  by simp

lemma mdeg0_iff_fcard0: "fcard xs = 0 \<longleftrightarrow> max_deg (Node r xs) = 0"
  by simp

lemma nempty_if_mdeg_gt_fcard: "max_deg (Node r xs) > fcard xs \<Longrightarrow> xs \<noteq> {||}"
  by auto

lemma mdeg_img_nempty: "max_deg (Node r xs) > fcard xs \<Longrightarrow> max_deg ` fst ` fset xs \<noteq> {}"
  using nempty_if_mdeg_gt_fcard[of xs] by fast

lemma mdeg_img_fin: "finite (max_deg ` fst ` fset xs)"
  by simp

lemma mdeg_Max_if_gt_fcard:
  "max_deg (Node r xs) > fcard xs \<Longrightarrow> max_deg (Node r xs) = Max (max_deg ` fst ` fset xs)"
  by (auto split: if_splits)

lemma mdeg_child_if_gt_fcard:
  "max_deg (Node r xs) > fcard xs \<Longrightarrow> \<exists>t \<in> fst ` fset xs. max_deg t = max_deg (Node r xs)"
  unfolding mdeg_Max_if_gt_fcard using Max_in[OF mdeg_img_fin mdeg_img_nempty] by force

lemma mdeg_child_if_wedge:
  "\<lbrakk>max_deg (Node r xs) > n; fcard xs \<le> n \<or> \<not>(\<forall>t \<in> fst ` fset xs. max_deg t \<le> n)\<rbrakk>
    \<Longrightarrow> \<exists>t \<in> fst ` fset xs. max_deg t > n"
  using mdeg_child_if_gt_fcard[of xs] by force

lemma maxif_eq_Max: "finite X \<Longrightarrow> (if X \<noteq> {} then max x (Max X) else x) = Max (insert x X)"
  by simp

lemma mdeg_img_empty_iff: "max_deg ` fst ` fset xs = {} \<longleftrightarrow> xs = {||}"
  by fast

lemma mdeg_alt: "max_deg (Node r xs) = Max (insert (fcard xs) (max_deg ` fst ` fset xs))"
  using maxif_eq_Max[OF mdeg_img_fin, of xs "fcard xs"] mdeg_img_empty_iff[of xs]
  by (auto split: if_splits)

lemma finite_fMax_union: "finite Y \<Longrightarrow> finite (\<Union>y\<in>Y. {Max (f y)})"
  by blast

lemma Max_union_Max_out:
  assumes "finite Y" and "\<forall>y \<in> Y. finite (f y)" and "\<forall>y \<in> Y. f y \<noteq> {}" and "Y \<noteq> {}"
  shows "Max (\<Union>y\<in>Y. {Max (f y)}) = Max (\<Union>y\<in>Y. f y)" (is "?M1=_")
proof -
  have "\<forall>y \<in> Y. \<forall>x \<in> f y. Max (f y) \<ge> x" using assms(2) by simp
  moreover have "\<forall>x \<in> (\<Union>y\<in>Y. {Max (f y)}). ?M1 \<ge> x" using assms(1) by simp
  moreover have M1_in: "?M1 \<in> (\<Union>y\<in>Y. {Max (f y)})"
    using assms(1,4) Max_in[OF finite_fMax_union] by auto
  ultimately have "\<forall>y \<in> Y. \<forall>x \<in> f y. ?M1 \<ge> x" by force
  then have "\<forall>x \<in> (\<Union>y\<in>Y. f y). ?M1 \<ge> x" by blast
  moreover have "?M1 \<in> (\<Union>y\<in>Y. (f y))" using M1_in assms(2-4) by force
  ultimately show ?thesis using assms(1,2) Max_eqI finite_UN_I by metis
qed

lemma Max_union_Max_out_insert:
  "\<lbrakk>finite Y; \<forall>y \<in> Y. finite (f y); \<forall>y \<in> Y. f y \<noteq> {}; Y \<noteq> {}\<rbrakk>
    \<Longrightarrow> Max (insert x (\<Union>y\<in>Y. {Max (f y)})) = Max (insert x (\<Union>y\<in>Y. f y))"
  using Max_union_Max_out[of Y f] by simp

lemma mdeg_alt2: "max_deg t = Max {fcard (sucs x)|x. is_subtree x t}"
proof(induction t rule: max_deg.induct)
  case (1 r xs)
  then show ?case
  proof(cases "xs = {||}")
    case False
    let ?f = "(\<lambda>t1. {fcard (sucs x)|x. is_subtree x t1})"
    let ?f' = "(\<lambda>t1. (\<lambda>x. fcard (sucs x)) ` {x. is_subtree x t1})"
    have fin: "finite (fst ` fset xs)" by simp
    have f_eq1: "?f = ?f'" by blast
    then have f_eq: "\<forall>y\<in>fst ` fset xs. (?f y = ?f' y)" by blast
    moreover have "\<forall>y\<in>fst ` fset xs. finite (?f' y)" using finite_subtrees by blast
    ultimately have fin': "\<forall>y\<in>fst ` fset xs. finite (?f y)" by simp
    have nempty: "\<forall>y\<in>fst ` fset xs. {fcard (sucs x) |x. is_subtree x y} \<noteq> {}"
      using self_subtree by blast
    have "max_deg ` fst ` fset xs = (\<Union>t1\<in>fst ` fset xs. {Max (?f t1)})"
      using "1.IH"[OF False] by auto
    then have "max_deg (Node r xs) = Max (insert (fcard xs) (\<Union>t1\<in>fst ` fset xs. {Max (?f t1)}))"
      using mdeg_alt[of r xs] by simp
    also have "\<dots> = Max (insert (fcard xs) (\<Union>t1\<in>fst ` fset xs. ?f t1))"
      using Max_union_Max_out_insert[OF fin fin' nempty] by fastforce
    also have "\<dots> = Max (insert (fcard xs) ((\<Union>t1\<in>fst ` fset xs. ?f' t1)))"
      using f_eq by simp
    also have "\<dots>
            = Max (insert (fcard xs) ((\<Union>t1\<in>fst ` fset xs. fcard ` sucs ` {x. is_subtree x t1})))"
      using image_image by metis
    also have "\<dots>
            = Max (insert (fcard xs) (fcard ` sucs ` (\<Union>t1\<in>fst ` fset xs. {x. is_subtree x t1})))"
      by (metis image_UN)
    also have "\<dots>
            = Max (fcard ` sucs ` (insert (Node r xs) (\<Union>t1\<in>fst ` fset xs. {x. is_subtree x t1})))"
      by force
    also have "\<dots> = Max (fcard ` sucs ` {x. is_subtree x (Node r xs)})"
      unfolding subtrees_insert_union by blast
    finally show ?thesis using f_eq1 image_image by metis
  qed(simp)
qed

lemma mdeg_singleton: "max_deg (Node r {|(t1,e1)|}) = max (max_deg t1) (fcard {|(t1,e1)|})"
  by simp

lemma mdeg_ge_child_aux: "(t1,e1) \<in> fset xs \<Longrightarrow> max_deg t1 \<le>  Max (max_deg ` fst ` fset xs)"
  using Max_ge[OF mdeg_img_fin] by fastforce

lemma mdeg_ge_child: "(t1,e1) \<in> fset xs \<Longrightarrow> max_deg t1 \<le> max_deg (Node r xs)"
  using mdeg_ge_child_aux by fastforce

lemma mdeg_ge_child': "t1 \<in> fst ` fset xs \<Longrightarrow> max_deg t1 \<le> max_deg (Node r xs)"
  using mdeg_ge_child[of t1] by force

lemma mdeg_ge_sub: "is_subtree t1 t2 \<Longrightarrow> max_deg t1 \<le> max_deg t2"
proof(induction t2)
  case (Node r xs)
  show ?case
  proof(cases "Node r xs=t1")
    case False
    then obtain x e1 where x_def: "(x,e1) \<in> fset xs" "is_subtree t1 x" using Node.prems(1) by auto
    then have "max_deg t1 \<le> max_deg x" using Node.IH by force
    then show ?thesis using mdeg_ge_child[OF x_def(1)] by simp
  qed(simp)
qed

lemma mdeg_gt_0_if_nempty: "xs \<noteq> {||} \<Longrightarrow> max_deg (Node r xs) > 0"
  using fcard_fempty by auto

corollary empty_if_mdeg_0: "max_deg (Node r xs) = 0 \<Longrightarrow> xs = {||}"
  using mdeg_gt_0_if_nempty by (metis less_numeral_extra(3))

lemma nempty_if_mdeg_n0: "max_deg (Node r xs) \<noteq> 0 \<Longrightarrow> xs \<noteq> {||}"
  by auto

corollary empty_iff_mdeg_0: "max_deg (Node r xs) = 0 \<longleftrightarrow> xs = {||}"
  using nempty_if_mdeg_n0 empty_if_mdeg_0 by auto

lemma mdeg_root: "max_deg (Node r xs) = max_deg (Node v xs)"
  by simp

lemma mdeg_ge_fcard: "fcard xs \<le> max_deg (Node r xs)"
  by simp

lemma mdeg_fcard_if_fcard_ge_child:
  "\<forall>(t,e) \<in> fset xs. max_deg t \<le> fcard xs \<Longrightarrow> max_deg (Node r xs) = fcard xs"
  using mdeg_child_if_gt_fcard[of xs r] mdeg_ge_fcard[of xs r] by fastforce

lemma mdeg_fcard_if_fcard_ge_child':
  "\<forall>t \<in> fst ` fset xs. max_deg t \<le> fcard xs \<Longrightarrow> max_deg (Node r xs) = fcard xs"
  using mdeg_fcard_if_fcard_ge_child[of xs r] by fastforce

lemma fcard_single_1: "fcard {|x|} = 1"
  by (simp add: fcard_finsert)

lemma fcard_single_1_iff: "fcard xs = 1 \<longleftrightarrow> (\<exists>x. xs = {|x|})"
  by (metis all_not_fin_conv bot.extremum fcard_seteq fcard_single_1
      finsert_fsubset le_numeral_extra(4))

lemma fcard_not0_if_elem: "\<exists>x. x \<in> fset xs \<Longrightarrow> fcard xs \<noteq> 0"
  by auto

lemma fcard1_if_le1_elem: "\<lbrakk>fcard xs \<le> 1; x \<in> fset xs\<rbrakk> \<Longrightarrow> fcard xs = 1"
  using fcard_not0_if_elem[of xs] by fastforce

lemma singleton_if_fcard_le1_elem: "\<lbrakk>fcard xs \<le> 1; x \<in> fset xs\<rbrakk> \<Longrightarrow> xs = {|x|}"
  using fcard_single_1_iff[of xs] fcard1_if_le1_elem by fastforce

lemma singleton_if_mdeg_le1_elem: "\<lbrakk>max_deg (Node r xs) \<le> 1; x \<in> fset xs\<rbrakk> \<Longrightarrow> xs = {|x|}"
  using singleton_if_fcard_le1_elem[of xs] mdeg_ge_fcard[of xs] by simp

lemma singleton_if_mdeg_le1_elem_suc: "\<lbrakk>max_deg t \<le> 1; x \<in> fset (sucs t)\<rbrakk> \<Longrightarrow> sucs t = {|x|}"
  using singleton_if_mdeg_le1_elem[of "root t" "sucs t"] by simp

lemma fcard0_if_le1_not_singleton: "\<lbrakk>\<forall>x. xs \<noteq> {|x|}; fcard xs \<le> 1\<rbrakk> \<Longrightarrow> fcard xs = 0"
  using fcard_single_1_iff[of xs] by fastforce

lemma empty_fset_if_fcard_le1_not_singleton: "\<lbrakk>\<forall>x. xs \<noteq> {|x|}; fcard xs \<le> 1\<rbrakk> \<Longrightarrow> xs = {||}"
  using fcard0_if_le1_not_singleton by auto

lemma fcard0_if_mdeg_le1_not_single: "\<lbrakk>\<forall>x. xs \<noteq> {|x|}; max_deg (Node r xs) \<le> 1\<rbrakk> \<Longrightarrow> fcard xs = 0"
  using fcard0_if_le1_not_singleton[of xs] mdeg_ge_fcard[of xs] by simp

lemma empty_fset_if_mdeg_le1_not_single: "\<lbrakk>\<forall>x. xs \<noteq> {|x|}; max_deg (Node r xs) \<le> 1\<rbrakk> \<Longrightarrow> xs = {||}"
  using fcard0_if_mdeg_le1_not_single by auto

lemma fcard0_if_mdeg_le1_not_single_suc:
  "\<lbrakk>\<forall>x. sucs t \<noteq> {|x|}; max_deg t \<le> 1\<rbrakk> \<Longrightarrow> fcard (sucs t) = 0"
  using fcard0_if_mdeg_le1_not_single[of "sucs t" "root t"] by simp

lemma empty_fset_if_mdeg_le1_not_single_suc: "\<lbrakk>\<forall>x. sucs t \<noteq> {|x|}; max_deg t \<le> 1\<rbrakk> \<Longrightarrow> sucs t = {||}"
  using fcard0_if_mdeg_le1_not_single_suc by auto

lemma mdeg_1_singleton:
  assumes "max_deg (Node r xs) = 1"
  shows "\<exists>x. xs = {|x|}"
proof -
  obtain x where x_def: "x |\<in>| xs"
    using assms by (metis all_not_fin_conv empty_iff_mdeg_0 zero_neq_one)
  moreover have "fcard xs \<le> 1" using assms mdeg_ge_fcard by metis
  ultimately have "xs = {|x|}"
    by (metis order_bot_class.bot.not_eq_extremum diff_Suc_1 diff_is_0_eq' fcard_finsert_disjoint
        less_nat_zero_code mk_disjoint_finsert pfsubset_fcard_mono)
  then show ?thesis by simp
qed

lemma subtree_child_if_dvert_notr_mdeg_le1:
  assumes "max_deg (Node r xs) \<le> 1" and "v \<noteq> r" and "v \<in> dverts (Node r xs)"
  shows "\<exists>r' e zs. is_subtree (Node r' {|(Node v zs,e)|}) (Node r xs)"
proof -
  obtain r' ys zs where zs_def: "is_subtree (Node r' ys) (Node r xs)" "Node v zs \<in> fst ` fset ys"
    using subtree_child_if_dvert_notroot[OF assms(2,3)] by blast
  have 0: "max_deg (Node r' ys) \<le> 1" using mdeg_ge_sub[OF zs_def(1)] assms(1) by simp
  obtain e where "{|(Node v zs,e)|} = ys"
    using singleton_if_mdeg_le1_elem[OF 0] zs_def(2) by fastforce
  then show ?thesis using zs_def(1) by blast
qed

lemma subtree_child_if_dvert_notroot_mdeg_le1:
  "\<lbrakk>max_deg t \<le> 1; v \<noteq> root t; v \<in> dverts t\<rbrakk>
    \<Longrightarrow> \<exists>r' e zs. is_subtree (Node r' {|(Node v zs,e)|}) t"
  using subtree_child_if_dvert_notr_mdeg_le1[of "root t" "sucs t"] by simp

lemma mdeg_child_sucs_eq_if_gt1:
  assumes "max_deg (Node r {|(t,e)|}) > 1"
  shows "max_deg (Node r {|(t,e)|}) = max_deg (Node v (sucs t))"
proof -
  have "fcard {|(t,e)|} = 1" using fcard_single_1 by fast
  then have "max_deg (Node r {|(t,e)|}) = max_deg t" using assms by simp
  then show ?thesis using mdeg_root[of "root t" "sucs t" v] dtree.exhaust_sel[of t] by argo
qed

lemma mdeg_child_sucs_le: "max_deg (Node v (sucs t)) \<le> max_deg (Node r {|(t,e)|})"
  using mdeg_root[of v "sucs t" "root t"] by simp

lemma mdeg_eq_child_if_singleton_gt1:
  "max_deg (Node r {|(t1,e1)|}) > 1 \<Longrightarrow> max_deg (Node r {|(t1,e1)|}) = max_deg t1"
  using mdeg_singleton[of r t1] by (auto simp: fcard_single_1 max_def)

lemma fcard_gt1_if_mdeg_gt_child:
  assumes "max_deg (Node r xs) > n" and "t1 \<in> fst ` fset xs" and "max_deg t1 \<le> n" and "n\<noteq>0"
  shows "fcard xs > 1"
proof(rule ccontr)
  assume "\<not>fcard xs > 1"
  then have "fcard xs \<le> 1" by simp
  then have "\<exists>e1. xs = {|(t1,e1)|}" using assms(2) singleton_if_fcard_le1_elem by fastforce
  then show False using mdeg_singleton[of r t1] assms(1,3,4) by (auto simp: fcard_single_1)
qed

lemma fcard_gt1_if_mdeg_gt_suc:
  "\<lbrakk>max_deg t2 > n; t1 \<in> fst ` fset (sucs t2); max_deg t1 \<le> n; n\<noteq>0\<rbrakk> \<Longrightarrow> fcard (sucs t2) > 1"
  using fcard_gt1_if_mdeg_gt_child[of n "root t2" "sucs t2"] by simp

lemma fcard_gt1_if_mdeg_gt_child1:
  "\<lbrakk>max_deg (Node r xs) > 1; t1 \<in> fst ` fset xs; max_deg t1 \<le> 1\<rbrakk> \<Longrightarrow> fcard xs > 1"
  using fcard_gt1_if_mdeg_gt_child by auto

lemma fcard_gt1_if_mdeg_gt_suc1:
  "\<lbrakk>max_deg t2 > 1; t1 \<in> fst ` fset (sucs t2); max_deg t1 \<le> 1\<rbrakk> \<Longrightarrow> fcard (sucs t2) > 1"
  using fcard_gt1_if_mdeg_gt_suc by blast

lemma fcard_lt_non_inj_f:
  "\<lbrakk>f a = f b; a \<in> fset xs; b \<in> fset xs; a\<noteq>b\<rbrakk> \<Longrightarrow> fcard (f |`| xs) < fcard xs"
proof(induction xs)
  case (insert x xs)
  then consider "a \<in> fset xs" "b \<in> fset xs" | "a = x" "b \<in> fset xs" | "a \<in> fset xs" "b = x"
    by auto
  then show ?case
  proof(cases)
    case 1
    then show ?thesis
      using insert.IH insert.prems(1,4) by (simp add: fcard_finsert_if)
  next
    case 2
    then show ?thesis
    proof(cases "fcard (f |`| xs) = fcard xs")
      case True
      then show ?thesis
        using 2 insert.hyps insert.prems(1)
        by (metis fcard_finsert_disjoint fimage_finsert finsert_fimage lessI)
    next
      case False
      then have "fcard (f |`| xs) \<le> fcard xs" using fcard_image_le by auto
      then have "fcard (f |`| xs) < fcard xs" using False by simp
      then show ?thesis
        using 2 insert.prems(1) fcard_image_le fcard_mono fimage_finsert less_le_not_le
        by (metis order_class.order.not_eq_order_implies_strict finsert_fimage fsubset_finsertI)
    qed
  next
    case 3
    then show ?thesis
    proof(cases "fcard (f |`| xs) = fcard xs")
      case True
      then show ?thesis
        using 3 insert.hyps insert.prems(1)
        by (metis fcard_finsert_disjoint fimage_finsert finsert_fimage lessI)
    next
      case False
      then have "fcard (f |`| xs) \<le> fcard xs" using fcard_image_le by auto
      then have "fcard (f |`| xs) < fcard xs" using False by simp
      then show ?thesis
        using 3 insert.prems(1) fcard_image_le fcard_mono fimage_finsert less_le_not_le
        by (metis order_class.order.not_eq_order_implies_strict finsert_fimage fsubset_finsertI)
    qed
  qed
qed (simp)

lemma mdeg_img_le:
  assumes "\<forall>(t,e) \<in> fset xs. max_deg (fst (f (t,e))) \<le> max_deg t"
  shows "max_deg (Node r (f |`| xs)) \<le> max_deg (Node r xs)"
proof(cases "max_deg (Node r (f |`| xs)) = fcard (f |`| xs)")
  case True
  then show ?thesis using fcard_image_le[of f xs] by auto
next
  case False
  then have "max_deg (Node r (f |`| xs)) > fcard (f |`| xs)"
    using mdeg_ge_fcard[of "f |`| xs"] by simp
  then obtain t1 e1 where t1_def:
      "(t1,e1) \<in> fset (f |`| xs)" "max_deg t1 = max_deg (Node r (f |`| xs))"
    using mdeg_child_if_gt_fcard[of "f |`| xs" r]
    by (metis (no_types, opaque_lifting) fst_conv imageE surj_pair)
  then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "f (t2,e2) = (t1,e1)" by auto
  then have "max_deg t2 \<ge> max_deg (Node r (f |`| xs))" using t1_def(2) assms by fastforce
  then show ?thesis using mdeg_ge_child[OF t2_def(1)] by simp
qed

lemma mdeg_img_le':
  assumes "\<forall>(t,e) \<in> fset xs. max_deg (f t) \<le> max_deg t"
  shows "max_deg (Node r ((\<lambda>(t,e). (f t, e)) |`| xs)) \<le> max_deg (Node r xs)"
  using mdeg_img_le[of xs "\<lambda>(t,e). (f t, e)"] assms by simp

lemma mdeg_le_if_fcard_and_child_le:
  "\<lbrakk>\<forall>(t,e) \<in> fset xs. max_deg t \<le> m; fcard xs \<le> m\<rbrakk> \<Longrightarrow> max_deg (Node r xs) \<le> m"
  using mdeg_ge_fcard mdeg_child_if_gt_fcard[of xs r] by fastforce

lemma mdeg_child_if_child_max:
  "\<lbrakk>\<forall>(t,e) \<in> fset xs. max_deg t \<le> max_deg t1; fcard xs \<le> max_deg t1; (t1,e1) \<in> fset xs\<rbrakk>
    \<Longrightarrow> max_deg (Node r xs) = max_deg t1"
  using mdeg_le_if_fcard_and_child_le[of xs "max_deg t1"] mdeg_ge_child[of t1 e1 xs] by simp

corollary mdeg_child_if_child_max':
  "\<lbrakk>\<forall>(t,e) \<in> fset xs. max_deg t \<le> max_deg t1; fcard xs \<le> max_deg t1; t1 \<in> fst ` fset xs\<rbrakk>
    \<Longrightarrow> max_deg (Node r xs) = max_deg t1"
  using mdeg_child_if_child_max[of xs t1] by force

lemma mdeg_img_eq:
  assumes "\<forall>(t,e) \<in> fset xs. max_deg (fst (f (t,e))) = max_deg t"
      and "fcard (f |`| xs) = fcard xs"
    shows "max_deg (Node r (f |`| xs)) = max_deg (Node r xs)"
proof(cases "max_deg (Node r (f |`| xs)) = fcard (f |`| xs)")
  case True
  then have "\<forall>(t,e) \<in> fset (f |`| xs). max_deg t \<le> fcard (f |`| xs)"
    using mdeg_ge_child
    by (metis (mono_tags, lifting) case_prodI2)
  then have "\<forall>(t,e) \<in> fset xs. max_deg t \<le> fcard xs" using assms by fastforce
  then have "max_deg (Node r xs) = fcard xs" using mdeg_fcard_if_fcard_ge_child by fast
  then show ?thesis using True assms(2) by simp
next
  case False
  then have "max_deg (Node r (f |`| xs)) > fcard (f |`| xs)"
    using mdeg_ge_fcard[of "f |`| xs"] by simp
  then obtain t1 e1 where t1_def:
      "(t1,e1) \<in> fset (f |`| xs)" "max_deg t1 = max_deg (Node r (f |`| xs))"
    using mdeg_child_if_gt_fcard[of "f |`| xs" r]
    by (metis (no_types, opaque_lifting) fst_conv imageE old.prod.exhaust)
  then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "f (t2,e2) = (t1,e1)" by auto
  then have mdeg_t21: "max_deg t2 = max_deg t1" using assms(1) by auto
  have "\<forall>(t3,e3) \<in> fset (f |`| xs). max_deg t3 \<le> max_deg t1"
    using t1_def(2) mdeg_ge_child[where xs="f |`| xs"]
    by (metis (no_types, lifting) case_prodI2)
  then have "\<forall>(t3,e3) \<in> fset xs. max_deg (fst (f (t3,e3))) \<le> max_deg t1" by auto
  then have "\<forall>(t3,e3) \<in> fset xs. max_deg t3 \<le> max_deg t2" using assms(1) mdeg_t21 by fastforce
  moreover have "max_deg t2 \<ge> fcard xs" using t1_def(2) assms(2) mdeg_t21 by simp
  ultimately have "max_deg (Node r xs) = max_deg t2"
    using t2_def(1) mdeg_child_if_child_max by metis
  then show ?thesis using t1_def(2) mdeg_t21 by simp
qed

lemma num_leaves_1_if_mdeg_1: "max_deg t \<le> 1 \<Longrightarrow> num_leaves t = 1"
proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "max_deg (Node r xs) = 0")
    case True
    then show ?thesis using empty_iff_mdeg_0 by auto
  next
    case False
    then have "max_deg (Node r xs) = 1" using Node.prems by simp
    then obtain t e where t_def: "xs = {|(t,e)|}" "(t,e) \<in> fset xs"
      using mdeg_1_singleton by fastforce
    then have "max_deg t \<le> 1" using Node.prems mdeg_ge_child by fastforce
    then show ?thesis using Node.IH t_def(1) by simp
  qed
qed

lemma num_leaves_ge1: "num_leaves t \<ge> 1"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "xs = {||}")
    case False
    then obtain t e where t_def: "(t,e) \<in> fset xs" by fast
    then have "1 \<le> num_leaves t" using Node by simp
    then show ?thesis
      using fset_sum_ge_elem[OF finite_fset[of xs] t_def, of "\<lambda>(t,e). num_leaves t"] by auto
  qed (simp)
qed

lemma num_leaves_ge_card: "num_leaves (Node r xs) \<ge> fcard xs"
proof(cases "xs = {||}")
  case False
  have "fcard xs = (\<Sum>x\<in> fset xs. 1)" using fcard.rep_eq by auto
  also have "\<dots> \<le> (\<Sum>x\<in> fset xs. num_leaves (fst x))" using num_leaves_ge1 sum_mono by metis
  finally show ?thesis using False by (simp add: fst_def prod.case_distrib)
qed (simp add: fcard_fempty)

lemma num_leaves_root: "num_leaves (Node r xs) = num_leaves (Node r' xs)"
  by simp

lemma num_leaves_singleton: "num_leaves (Node r {|(t,e)|}) = num_leaves t"
  by simp

subsection \<open>List Conversions\<close>

function dtree_to_list :: "('a,'b) dtree \<Rightarrow> ('a\<times>'b) list" where
  "dtree_to_list (Node r {|(t,e)|}) = (root t,e) # dtree_to_list t"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> dtree_to_list (Node r xs) = []"
  by (metis darcs_mset.cases surj_pair) auto
termination by lexicographic_order

fun dtree_from_list :: "'a \<Rightarrow> ('a\<times>'b) list \<Rightarrow> ('a,'b) dtree" where
  "dtree_from_list r [] = Node r {||}"
| "dtree_from_list r ((v,e)#xs) = Node r {|(dtree_from_list v xs, e)|}"

fun wf_list_arcs :: "('a\<times>'b) list \<Rightarrow> bool" where
  "wf_list_arcs [] = True"
| "wf_list_arcs ((v,e)#xs) = (e \<notin> snd ` set xs \<and> wf_list_arcs xs)"

fun wf_list_verts :: "('a\<times>'b) list \<Rightarrow> bool" where
  "wf_list_verts [] = True"
| "wf_list_verts ((v,e)#xs) = (v \<notin> fst ` set xs \<and> wf_list_verts xs)"

lemma dtree_to_list_sub_dverts_ins:
  "insert (root t) (fst ` set (dtree_to_list t)) \<subseteq> dverts t"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case False
    then obtain t e where t_def: "xs = {|(t,e)|}"
      using mdeg_1_singleton by fastforce
    then show ?thesis using Node.IH by fastforce
  qed (auto)
qed

lemma dtree_to_list_eq_dverts_ins:
  "max_deg t \<le> 1 \<Longrightarrow> insert (root t) (fst ` set (dtree_to_list t)) = dverts t"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "max_deg (Node r xs) = 0")
    case True
    then have "xs = {||}" using empty_iff_mdeg_0 by auto
    moreover from this have "\<forall>x. xs \<noteq> {|x|}" by blast
    ultimately show ?thesis by simp
  next
    case False
    then have "max_deg (Node r xs) = 1" using Node.prems by simp
    then obtain t e where t_def: "xs = {|(t,e)|}" "(t,e) \<in> fset xs"
      using mdeg_1_singleton by fastforce
    then have "max_deg t \<le> 1" using Node.prems mdeg_ge_child by fastforce
    then have "insert (root t) (fst ` set (dtree_to_list t)) = dverts t"
      using Node.IH t_def(2) by auto
    then show ?thesis using Node.prems(1) t_def(1) by simp
  qed
qed

lemma dtree_to_list_eq_dverts_sucs:
  "max_deg t \<le> 1 \<Longrightarrow> fst ` set (dtree_to_list t) = (\<Union>x \<in> fset (sucs t). dverts (fst x))"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "max_deg (Node r xs) = 0")
    case True
    then have "xs = {||}" using empty_iff_mdeg_0 by auto
    moreover from this have "\<forall>x. xs \<noteq> {|x|}" by blast
    ultimately show ?thesis by simp
  next
    case False
    then have "max_deg (Node r xs) = 1" using Node.prems by simp
    then obtain t e where t_def: "xs = {|(t,e)|}" "(t,e) \<in> fset xs"
      using mdeg_1_singleton by fastforce
    then have "max_deg t \<le> 1" using Node.prems mdeg_ge_child by fastforce
    then have "fst ` set (dtree_to_list t) = (\<Union>x \<in> fset (sucs t). dverts (fst x))"
      using Node.IH t_def(2) by auto
    moreover from this have "dverts t = insert (root t) (\<Union>x \<in> fset (sucs t). dverts (fst x))"
      using \<open>max_deg t \<le> 1\<close> dtree_to_list_eq_dverts_ins by fastforce
    ultimately show ?thesis using Node.prems(1) t_def(1) by force
  qed
qed

lemma dtree_to_list_sub_dverts:
  "wf_dverts t \<Longrightarrow> fst ` set (dtree_to_list t) \<subseteq> dverts t - {root t}"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case False
    then obtain t e where t_def: "xs = {|(t,e)|}"
      using mdeg_1_singleton by fastforce
    then have "wf_dverts t" using Node.prems mdeg_ge_child by fastforce
    then have "fst ` set (dtree_to_list t) \<subseteq> dverts t - {root t}" using Node.IH t_def(1) by auto
    then have "fst ` set (dtree_to_list (Node r xs)) \<subseteq> dverts t"
      using t_def(1) dtree.set_sel(1) by auto
    then show ?thesis using Node.prems(1) t_def(1) by (simp add: wf_dverts_iff_dverts')
  qed (auto)
qed

lemma dtree_to_list_eq_dverts:
  "\<lbrakk>wf_dverts t; max_deg t \<le> 1\<rbrakk> \<Longrightarrow> fst ` set (dtree_to_list t) = dverts t - {root t}"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "max_deg (Node r xs) = 0")
    case True
    then have "xs = {||}" using empty_iff_mdeg_0 by auto
    moreover from this have "\<forall>x. xs \<noteq> {|x|}" by blast
    ultimately show ?thesis by simp
  next
    case False
    then have "max_deg (Node r xs) = 1" using Node.prems by simp
    then obtain t e where t_def: "xs = {|(t,e)|}" "(t,e) \<in> fset xs"
      using mdeg_1_singleton by fastforce
    then have "max_deg t \<le> 1 \<and> wf_dverts t" using Node.prems mdeg_ge_child by fastforce
    then have "fst ` set (dtree_to_list t) = dverts t - {root t}" using Node.IH t_def(2) by auto
    then have "fst ` set (dtree_to_list (Node r xs)) = dverts t"
      using t_def(1) dtree.set_sel(1) by auto
    then show ?thesis using Node.prems(1) t_def(1) by (simp add: wf_dverts_iff_dverts')
  qed
qed

lemma dtree_to_list_eq_dverts_single:
  "\<lbrakk>max_deg t \<le> 1; sucs t = {|(t1,e1)|}\<rbrakk> \<Longrightarrow> fst ` set (dtree_to_list t) = dverts t1"
  by (simp add: dtree_to_list_eq_dverts_sucs)

lemma dtree_to_list_sub_darcs: "snd ` set (dtree_to_list t) \<subseteq> darcs t"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case False
    then obtain t e where "xs = {|(t,e)|}"
      using mdeg_1_singleton by fastforce
    then show ?thesis using Node.IH by fastforce
  qed (auto)
qed

lemma dtree_to_list_eq_darcs: "max_deg t \<le> 1 \<Longrightarrow> snd ` set (dtree_to_list t) = darcs t"
proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "max_deg (Node r xs) = 0")
    case True
    then have "xs = {||}" using empty_iff_mdeg_0 by auto
    moreover from this have "\<forall>x. xs \<noteq> {|x|}" by blast
    ultimately show ?thesis by simp
  next
    case False
    then have "max_deg (Node r xs) = 1" using Node.prems by simp
    then obtain t e where t_def: "xs = {|(t,e)|}" "(t,e) \<in> fset xs"
      using mdeg_1_singleton by fastforce
    then have "max_deg t \<le> 1" using Node.prems mdeg_ge_child by fastforce
    then have "snd ` set (dtree_to_list t) = darcs t" using Node.IH t_def(2) by auto
    then show ?thesis using t_def(1) by simp
  qed
qed

lemma dtree_from_list_eq_dverts: "dverts (dtree_from_list r xs) = insert r (fst ` set xs)"
  by(induction xs arbitrary: r) force+

lemma dtree_from_list_eq_darcs: "darcs (dtree_from_list r xs) = snd ` set xs"
  by(induction xs arbitrary: r) force+

lemma dtree_from_list_root_r[simp]: "root (dtree_from_list r xs) = r"
  using dtree.sel(1) dtree_from_list.elims by metis

lemma dtree_from_list_v_eq_r:
  "Node r xs = dtree_from_list v ys \<Longrightarrow> r = v"
  using dtree.sel(1)[of r xs] by simp

lemma dtree_from_list_fcard0_empty: "fcard (sucs (dtree_from_list r [])) = 0"
  by simp

lemma dtree_from_list_fcard0_iff_empty: "fcard (sucs (dtree_from_list r xs)) = 0 \<longleftrightarrow> xs = []"
  by(induction xs) auto

lemma dtree_from_list_fcard1_iff_nempty: "fcard (sucs (dtree_from_list r xs)) = 1 \<longleftrightarrow> xs \<noteq> []"
  by(induction xs) (auto simp: fcard_single_1 fcard_fempty)

lemma dtree_from_list_fcard_le1: "fcard (sucs (dtree_from_list r xs)) \<le> 1"
  by(induction xs) (auto simp: fcard_single_1 fcard_fempty)

lemma dtree_from_empty_deg_0: "max_deg (dtree_from_list r []) = 0"
  by simp

lemma dtree_from_list_deg_le_1: "max_deg (dtree_from_list r xs) \<le> 1"
proof(induction xs arbitrary: r)
  case Nil
  have "max_deg (dtree_from_list r []) = 0" by simp
  also have "\<dots> \<le> 1" by blast
  finally show ?case by blast
next
  case (Cons x xs)
  obtain v e where v_def: "x = (v,e)" by force
  let ?xs = "{|(dtree_from_list v xs, e)|}"
  have "dtree_from_list r (x#xs) = Node r ?xs" by (simp add: v_def)
  moreover have "max_deg (dtree_from_list v xs) \<le> 1" using Cons by simp
  moreover have "max_deg (Node r ?xs) = max (max_deg (dtree_from_list v xs)) (fcard ?xs)"
    using mdeg_singleton by fast
  ultimately show ?case by (simp add: fcard_finsert_if max_def)
qed

lemma dtree_from_list_deg_1: "xs \<noteq> [] \<longleftrightarrow> max_deg (dtree_from_list r xs) = 1"
proof (cases xs)
  case (Cons x xs)
  obtain v e where v_def: "x = (v,e)" by force
  let ?xs = "{|(dtree_from_list v xs, e)|}"
  have "dtree_from_list r (x#xs) = Node r ?xs" by (simp add: v_def)
  moreover have "max_deg (dtree_from_list v xs) \<le> 1" using dtree_from_list_deg_le_1 by fast
  moreover have "max_deg (Node r ?xs) = max (max_deg (dtree_from_list v xs)) (fcard ?xs)"
    using mdeg_singleton by fast
  ultimately show ?thesis using Cons by (simp add: fcard_finsert_if max_def)
qed (metis dtree_from_empty_deg_0 zero_neq_one)

lemma dtree_from_list_singleton: "xs \<noteq> [] \<Longrightarrow> \<exists>t e. dtree_from_list r xs = Node r {|(t,e)|}"
  using dtree_from_list.elims[of r xs] by fastforce

lemma dtree_from_to_list_id: "max_deg t \<le> 1 \<Longrightarrow> dtree_from_list (root t) (dtree_to_list t) = t"
proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "max_deg (Node r xs) = 0")
    case True
    then have "xs = {||}" using empty_iff_mdeg_0 by auto
    moreover from this have "\<forall>x. xs \<noteq> {|x|}" by blast
    ultimately show ?thesis using Node.prems by simp
  next
    case False
    then have "max_deg (Node r xs) = 1" using Node.prems by simp
    then obtain t e where t_def: "xs = {|(t,e)|}" "(t,e) \<in> fset xs"
      using mdeg_1_singleton by fastforce
    then have "max_deg t \<le> 1" using Node.prems mdeg_ge_child by fastforce
    then show ?thesis using Node.IH t_def(1) by simp
  qed
qed

lemma dtree_to_from_list_id: "dtree_to_list (dtree_from_list r xs) = xs"
proof(induction xs arbitrary: r)
  case Nil
  then show ?case
    using dtree_from_list_deg_1 dtree_from_list_deg_le_1 dtree_from_to_list_id by metis
next
  case (Cons x xs)
  obtain v e where v_def: "x = (v,e)" by force
  then have "dtree_to_list (dtree_from_list r (x#xs)) = (v,e)#dtree_to_list (dtree_from_list v xs)"
    by (metis dtree_from_list.elims dtree_to_list.simps(1) dtree.sel(1) dtree_from_list.simps(2))
  then show ?case by (simp add: v_def Cons)
qed

lemma dtree_from_list_eq_singleton_hd:
  "Node r0 {|(t0,e0)|} = dtree_from_list v1 ys \<Longrightarrow> (\<exists>xs. (root t0, e0) # xs = ys)"
  using dtree_to_list.simps(1)[of r0 t0 e0] dtree_to_from_list_id[of v1 ys] by simp

lemma dtree_from_list_eq_singleton:
  "Node r0 {|(t0,e0)|} = dtree_from_list v1 ys \<Longrightarrow> r0 = v1 \<and> (\<exists>xs. (root t0, e0) # xs = ys)"
  using dtree_from_list_eq_singleton_hd by fastforce

lemma dtree_from_list_uneq_sequence:
  "\<lbrakk>is_subtree (Node r0 {|(t0,e0)|}) (dtree_from_list v1 ys);
    Node r0 {|(t0,e0)|} \<noteq> dtree_from_list v1 ys\<rbrakk>
    \<Longrightarrow> \<exists>e as bs. as @ (r0,e) # (root t0, e0) # bs = ys"
proof(induction v1 ys rule: dtree_from_list.induct)
  case (2 r v e xs)
  then show ?case
  proof(cases "Node r0 {|(t0,e0)|} = dtree_from_list v xs")
    case True
    then show ?thesis using dtree_from_list_eq_singleton by fast
  next
    case False
    then obtain e1 as bs where "as @ (r0, e1) # (root t0, e0) # bs = xs" using 2 by auto
    then have "((v,e)#as) @ (r0, e1) # (root t0, e0) # bs = (v, e) # xs" by simp
    then show ?thesis by blast
  qed
qed(simp)

lemma dtree_from_list_sequence:
  "\<lbrakk>is_subtree (Node r0 {|(t0,e0)|}) (dtree_from_list v1 ys)\<rbrakk>
    \<Longrightarrow> \<exists>e as bs. as @ (r0,e) # (root t0, e0) # bs = ((v1,e1)#ys)"
  using dtree_from_list_uneq_sequence[of r0 t0 e0] dtree_from_list_eq_singleton append_Cons by fast

lemma dtree_from_list_eq_empty:
  "Node r {||} = dtree_from_list v ys \<Longrightarrow> r = v \<and> ys = []"
  using dtree_to_from_list_id dtree_from_list_v_eq_r dtree_from_list.simps(1) by metis

lemma dtree_from_list_sucs_cases:
  "Node r xs = dtree_from_list v ys \<Longrightarrow> xs = {||} \<or> (\<exists>x. xs = {|x|})"
  using dtree.inject dtree_from_list.simps(1) dtree_to_from_list_id dtree_to_list.simps(2) by metis

lemma dtree_from_list_uneq_sequence_xs:
  "strict_subtree (Node r0 xs0) (dtree_from_list v1 ys)
    \<Longrightarrow> \<exists>e as bs. as @ (r0,e) # bs = ys \<and> Node r0 xs0 = dtree_from_list r0 bs"
proof(induction v1 ys rule: dtree_from_list.induct)
  case (2 r v e xs)
  then show ?case
  proof(cases "Node r0 xs0 = dtree_from_list v xs")
    case True
    then show ?thesis using dtree_from_list_root_r dtree.sel(1)[of r0 xs0] by fastforce
  next
    case False
    then obtain e1 as bs where 0: "as @ (r0,e1) #  bs = xs" "Node r0 xs0 = dtree_from_list r0 bs"
      using 2 unfolding strict_subtree_def by auto
    then have "((v,e)#as) @ (r0,e1) #  bs = (v,e) # xs" by simp
    then show ?thesis using 0(2) by blast
  qed
qed(simp add: strict_subtree_def)

lemma dtree_from_list_sequence_xs:
  "\<lbrakk>is_subtree (Node r xs) (dtree_from_list v1 ys)\<rbrakk>
    \<Longrightarrow> \<exists>e as bs. as @ (r,e) # bs = ((v1,e1)#ys) \<and> Node r xs = dtree_from_list r bs"
  using dtree_from_list_uneq_sequence_xs[of r xs] dtree_from_list_v_eq_r strict_subtree_def
  by (fast intro!: append_Cons)

lemma dtree_from_list_sequence_dverts:
  "\<lbrakk>is_subtree (Node r xs) (dtree_from_list v1 ys)\<rbrakk>
    \<Longrightarrow> \<exists>e as bs. as @ (r,e) # bs = ((v1,e1)#ys) \<and> dverts (Node r xs) = insert r (fst ` set bs)"
  using dtree_from_list_sequence_xs[of r xs v1 ys e1] dtree_from_list_eq_dverts by metis

lemma dtree_from_list_dverts_subset_set:
  "set bs \<subseteq> set ds \<Longrightarrow> dverts (dtree_from_list r bs) \<subseteq> dverts (dtree_from_list r ds)"
  by (auto simp: dtree_from_list_eq_dverts)

lemma wf_darcs'_iff_wf_list_arcs: "wf_list_arcs xs \<longleftrightarrow> wf_darcs' (dtree_from_list r xs)"
  by(induction xs arbitrary: r rule: wf_list_arcs.induct) (auto simp: dtree_from_list_eq_darcs)

lemma wf_darcs_iff_wf_list_arcs: "wf_list_arcs xs \<longleftrightarrow> wf_darcs (dtree_from_list r xs)"
  using wf_darcs'_iff_wf_list_arcs wf_darcs_iff_darcs' by fast

lemma wf_dverts_iff_wf_list_verts:
  "r \<notin> fst ` set xs \<and> wf_list_verts xs \<longleftrightarrow> wf_dverts (dtree_from_list r xs)"
  by (induction xs arbitrary: r rule: wf_list_verts.induct)
    (auto simp: dtree_from_list_eq_dverts wf_dverts_iff_dverts')

theorem wf_dtree_iff_wf_list:
  "wf_list_arcs xs \<and> r \<notin> fst ` set xs \<and> wf_list_verts xs \<longleftrightarrow> wf_dtree (dtree_from_list r xs)"
  using wf_darcs_iff_wf_list_arcs wf_dverts_iff_wf_list_verts unfolding wf_dtree_def by fast

lemma wf_list_arcs_if_wf_darcs: "wf_darcs t \<Longrightarrow> wf_list_arcs (dtree_to_list t)"
proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case True
    then show ?thesis using dtree_to_list.simps(2) by simp
  next
    case False
    then obtain t1 e1 where "xs = {|(t1,e1)|}" by auto
    then show ?thesis
      using Node dtree_to_list_sub_darcs unfolding wf_darcs_iff_darcs' by fastforce
  qed
qed

lemma wf_list_verts_if_wf_dverts: "wf_dverts t \<Longrightarrow> wf_list_verts (dtree_to_list t)"
proof(induction t)
  case (Node r xs)
  then show ?case
  proof(cases "\<forall>x. xs \<noteq> {|x|}")
    case True
    then show ?thesis using dtree_to_list.simps(2) by simp
  next
    case False
    then obtain t1 e1 where "xs = {|(t1,e1)|}" by auto
    then show ?thesis using Node dtree_to_list_sub_dverts by (fastforce simp: wf_dverts_iff_dverts')
  qed
qed

lemma distinct_if_wf_list_arcs: "wf_list_arcs xs \<Longrightarrow> distinct xs"
  by (induction xs) force+

lemma distinct_if_wf_list_verts: "wf_list_verts xs \<Longrightarrow> distinct xs"
  by (induction xs) force+

lemma wf_list_arcs_alt: "wf_list_arcs xs \<longleftrightarrow> distinct (map snd xs)"
  by (induction xs) force+

lemma wf_list_verts_alt: "wf_list_verts xs \<longleftrightarrow> distinct (map fst xs)"
  by (induction xs) force+

lemma subtree_from_list_split_eq_if_wfverts:
  assumes "wf_list_verts (as@(r,e)#bs)"
      and "v \<notin> fst ` set (as@(r,e)#bs)"
      and "is_subtree (Node r xs) (dtree_from_list v (as@(r,e)#bs))"
    shows "Node r xs = dtree_from_list r bs"
proof -
  have 0: "wf_list_verts ((v,e)#as@(r,e)#bs)" using assms(1,2) by simp
  obtain as' e' bs' where as'_def:
      "as'@(r,e')#bs' = (v,e)#as@(r,e)#bs" "Node r xs = dtree_from_list r bs'"
    using assms(3) dtree_from_list_sequence_xs[of r xs] by blast
  then have 0: "wf_list_verts (as'@(r,e')#bs')" using assms(1,2) by simp
  have r_as': "r \<notin> fst ` set as'" using 0 unfolding wf_list_verts_alt by simp
  moreover have r_bs': "r \<notin> fst ` set bs'" using 0 unfolding wf_list_verts_alt by simp
  moreover have "(r,e) \<in> set (as'@(r,e')#bs')" using as'_def(1) by simp
  ultimately have "(r,e')= (r,e)" by force
  then show ?thesis
    using r_as' r_bs' as'_def append_Cons_eq_iff[of "(r,e)" as' bs' "(v,e)#as" bs] by force
qed

lemma subtree_from_list_split_eq_if_wfdverts:
  "\<lbrakk>wf_dverts (dtree_from_list v (as@(r,e)#bs));
    is_subtree (Node r xs) (dtree_from_list v (as@(r,e)#bs))\<rbrakk>
    \<Longrightarrow> Node r xs = dtree_from_list r bs"
  using subtree_from_list_split_eq_if_wfverts wf_dverts_iff_wf_list_verts by fast

lemma dtree_from_list_dverts_subset_wfdverts:
  assumes "set bs \<subseteq> set ds"
      and "wf_dverts (dtree_from_list v (as@(r,e1)#bs))"
      and "wf_dverts (dtree_from_list v (cs@(r,e2)#ds))"
      and "is_subtree (Node r xs) (dtree_from_list v (as@(r,e1)#bs))"
      and "is_subtree (Node r ys) (dtree_from_list v (cs@(r,e2)#ds))"
    shows "dverts (Node r xs) \<subseteq> dverts (Node r ys)"
  using dtree_from_list_dverts_subset_set[OF assms(1)]
    subtree_from_list_split_eq_if_wfdverts[OF assms(2,4)]
    subtree_from_list_split_eq_if_wfdverts[OF assms(3,5)]
  by simp

lemma dtree_from_list_dverts_subset_wfdverts':
  assumes "wf_dverts (dtree_from_list v as)"
      and "wf_dverts (dtree_from_list v cs)"
      and "is_subtree (Node r xs) (dtree_from_list v as)"
      and "is_subtree (Node r ys) (dtree_from_list v cs)"
      and "\<exists>as' e1 bs cs' e2 ds. as'@(r,e1)#bs = as \<and> cs'@(r,e2)#ds = cs \<and> set bs \<subseteq> set ds"
    shows "dverts (Node r xs) \<subseteq> dverts (Node r ys)"
  using dtree_from_list_dverts_subset_wfdverts assms by metis

lemma dtree_to_list_sequence_subtree:
  "\<lbrakk>max_deg t \<le> 1; strict_subtree (Node r xs) t\<rbrakk>
    \<Longrightarrow> \<exists>as e bs. dtree_to_list t = as@(r,e)#bs \<and> Node r xs = dtree_from_list r bs"
  by (metis dtree_from_list_uneq_sequence_xs dtree_from_to_list_id)

lemma dtree_to_list_sequence_subtree':
  "\<lbrakk>max_deg t \<le> 1; strict_subtree (Node r xs) t\<rbrakk>
    \<Longrightarrow> \<exists>as e bs. dtree_to_list t = as@(r,e)#bs \<and> dtree_to_list (Node r xs) = bs"
  using dtree_to_from_list_id[of r]  dtree_to_list_sequence_subtree[of t r xs] by fastforce

lemma dtree_to_list_subtree_dverts_eq_fsts:
  "\<lbrakk>max_deg t \<le> 1; strict_subtree (Node r xs) t\<rbrakk>
    \<Longrightarrow> \<exists>as e bs. dtree_to_list t = as@(r,e)#bs \<and> insert r (fst ` set bs) = dverts (Node r xs)"
  by (metis dtree_from_list_eq_dverts dtree_to_list_sequence_subtree)

lemma dtree_to_list_subtree_dverts_eq_fsts':
  "\<lbrakk>max_deg t \<le> 1; strict_subtree (Node r xs) t\<rbrakk>
    \<Longrightarrow> \<exists>as e bs. dtree_to_list t = as@(r,e)#bs \<and> (fst ` set ((r,e)#bs)) = dverts (Node r xs)"
  using dtree_to_list_subtree_dverts_eq_fsts by fastforce

lemma dtree_to_list_split_subtree:
  assumes "as@(r,e)#bs = dtree_to_list t"
  shows "\<exists>xs. strict_subtree (Node r xs) t \<and> dtree_to_list (Node r xs) = bs"
using assms proof(induction t arbitrary: as rule: dtree_to_list.induct)
  case (1 r1 t1 e1)
  show ?case
  proof(cases as)
    case Nil
    then have "dtree_to_list (Node r (sucs t1)) = bs" using "1.prems" by auto
    moreover have "is_subtree (Node r (sucs t1)) (Node r1 {|(t1, e1)|})"
      using subtree_if_child[of t1 "{|(t1, e1)|}"] "1.prems" Nil by simp
    moreover have "Node r1 {|(t1, e1)|} \<noteq> (Node r (sucs t1))" by (blast intro!: singleton_uneq')
    ultimately show ?thesis unfolding strict_subtree_def by blast
  next
    case (Cons a as')
    then show ?thesis using 1 unfolding strict_subtree_def by fastforce
  qed
qed(simp)

lemma dtree_to_list_split_subtree_dverts_eq_fsts:
  assumes "max_deg t \<le> 1" and "as@(r,e)#bs = dtree_to_list t"
  shows "\<exists>xs. strict_subtree (Node r xs) t \<and> dverts (Node r xs) = insert r (fst`set bs)"
proof -
  obtain xs where xs_def:
      "is_subtree (Node r xs) t" "Node r xs \<noteq> t" "dtree_to_list (Node r xs) = bs"
    using dtree_to_list_split_subtree[OF assms(2)] unfolding strict_subtree_def by blast
  have "max_deg (Node r xs) \<le> 1" using mdeg_ge_sub[OF xs_def(1)] assms(1) by simp
  then show ?thesis
    using dtree_to_list_eq_dverts_ins[of "Node r xs"] xs_def strict_subtree_def by auto
qed

lemma dtree_to_list_split_subtree_dverts_eq_fsts':
  assumes "max_deg t \<le> 1" and "as@(r,e)#bs = dtree_to_list t"
  shows "\<exists>xs. strict_subtree (Node r xs) t \<and> dverts (Node r xs) = (fst ` set ((r,e)#bs))"
  using dtree_to_list_split_subtree_dverts_eq_fsts[OF assms] by simp

lemma dtree_from_list_dverts_subset_wfdverts1:
  assumes "dverts t1 \<subseteq> fst ` set ((r,e2)#bs)"
      and "wf_dverts (dtree_from_list v (as@(r,e2)#bs))"
      and "is_subtree (Node r ys) (dtree_from_list v (as@(r,e2)#bs))"
    shows "dverts t1 \<subseteq> dverts (Node r ys)"
  using subtree_from_list_split_eq_if_wfdverts[OF assms(2,3)] assms(1) dtree_from_list_eq_dverts
  by fastforce

lemma dtree_from_list_dverts_subset_wfdverts1':
  assumes "wf_dverts (dtree_from_list v cs)"
      and "is_subtree (Node r ys) (dtree_from_list v cs)"
      and "\<exists>as e bs. as@(r,e)#bs = cs \<and> dverts t1 \<subseteq> fst ` set ((r,e)#bs)"
    shows "dverts t1 \<subseteq> dverts (Node r ys)"
  using dtree_from_list_dverts_subset_wfdverts1 assms by fast

lemma dtree_from_list_1_leaf: "num_leaves (dtree_from_list r xs) = 1"
  using num_leaves_1_if_mdeg_1 dtree_from_list_deg_le_1 by fast

subsection \<open>Inserting in Dtrees\<close>

abbreviation insert_before ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> (('a,'b) dtree \<times> 'b) fset \<Rightarrow> (('a,'b) dtree \<times> 'b) fset" where
  "insert_before v e y xs \<equiv> ffold (\<lambda>(t1,e1).
    finsert (if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))) {||} xs"

fun insert_between :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a,'b) dtree \<Rightarrow> ('a,'b) dtree" where
  "insert_between v e x y (Node r xs) = (if x=r \<and> (\<exists>t. t \<in> fst ` fset xs \<and> root t = y)
    then Node r (insert_before v e y xs)
    else if x=r then Node r (finsert (Node v {||},e) xs)
    else Node r ((\<lambda>(t,e1). (insert_between v e x y t,e1)) |`| xs))"

lemma insert_between_id_if_notin: "x \<notin> dverts t \<Longrightarrow> insert_between v e x y t = t"
proof(induction t)
  case (Node r xs)
  have "\<forall>(t,e) \<in> fset xs. x \<notin> dverts t" using Node.prems by force
  then have "\<forall>(t,e1) \<in> fset xs. (\<lambda>(t,e1). (insert_between v e x y t,e1)) (t,e1) = (t,e1)"
    using Node.IH by auto
  then have "((\<lambda>(t,e1). (insert_between v e x y t,e1)) |`| xs) = xs"
    by (smt (verit, ccfv_threshold) fset.map_cong0 case_prodE fimage_ident)
  then show ?case using Node.prems by simp
qed

context wf_dtree
begin

lemma insert_before_commute_aux:
  assumes "f = (\<lambda>(t1,e1). finsert (if root t1 = y1 then (Node v {|(t1,e1)|},e) else (t1,e1)))"
  shows "(f y \<circ> f x) z = (f x \<circ> f y) z"
proof -
  obtain t1 e1 where y_def: "y = (t1, e1)" by fastforce
  obtain t2 e2 where "x = (t2, e2)" by fastforce
  then show ?thesis using assms y_def by auto
qed

lemma insert_before_commute:
  "comp_fun_commute (\<lambda>(t1,e1). finsert (if root t1 = y1 then (Node v {|(t1,e1)|},e) else (t1,e1)))"
  using comp_fun_commute_def insert_before_commute_aux by fastforce

interpretation Comm:
  comp_fun_commute "\<lambda>(t1,e1). finsert (if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  by (rule insert_before_commute)

lemma root_not_new_in_orig:
  "\<lbrakk>(t1,e1) \<in> fset (insert_before v e y xs); root t1 \<noteq> v\<rbrakk> \<Longrightarrow> (t1,e1) \<in> fset xs"
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) \<in> fset (insert_before v e y xs)")
    case True
    then show ?thesis using insert.IH insert.prems(2) by simp
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "?f x = (t1,e1)" using False insert.prems(1) by force
    then have "x = (t1,e1)"
      by (smt (z3) insert.prems(2) dtree.sel(1) old.prod.exhaust prod.inject case_prod_conv)
    then show ?thesis by simp
  qed
qed

lemma root_not_y_in_new:
  "\<lbrakk>(t1,e1) \<in> fset xs; root t1 \<noteq> y\<rbrakk> \<Longrightarrow> (t1,e1) \<in> fset (insert_before v e y xs)"
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) = x")
    case True
    then show ?thesis using insert by auto
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then show ?thesis using insert.IH insert.prems by force
  qed
qed

lemma root_noty_if_in_insert_before:
  "\<lbrakk>(t1,e1) \<in> fset (insert_before v e y xs); v\<noteq>y\<rbrakk> \<Longrightarrow> root t1 \<noteq> y"
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) \<in> fset (insert_before v e y xs)")
    case True
    then show ?thesis using insert.IH insert.prems(2) by fast
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have 0: "?f x = (t1,e1)" using insert.prems False by simp
    then show ?thesis
    proof(cases "root t1 = v")
      case True
      then show ?thesis using insert.prems(2) by simp
    next
      case False
      then show ?thesis by (smt (z3) dtree.sel(1) old.prod.exhaust prod.inject 0 case_prod_conv)
    qed
  qed
qed

lemma in_insert_before_child_in_orig:
  "\<lbrakk>(t1,e1) \<in> fset (insert_before v e y xs); (t1,e1) \<notin> fset xs\<rbrakk>
    \<Longrightarrow> \<exists>(t2,e2) \<in> fset xs. (Node v {|(t2,e2)|}) = t1 \<and> root t2 = y \<and> e1=e"
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) \<in> fset (insert_before v e y xs)")
    case True
    then show ?thesis using insert.IH insert.prems(2) by simp
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then show ?thesis
      by (smt (z3) False Pair_inject old.prod.case case_prodI2 finsert_iff insert.prems)
  qed
qed

lemma insert_before_not_y_id:
  "\<not>(\<exists>t. t \<in> fst ` fset xs \<and> root t = y) \<Longrightarrow> insert_before v e y xs = xs"
proof(induction xs)
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
    by (simp add: insert.hyps prod.case_distrib)
  then have "insert_before v e y (finsert x xs) = finsert x (insert_before v e y xs)"
    using insert.prems
    by (smt (z3) old.prod.exhaust case_prod_conv finsertCI fst_conv image_eqI)
  moreover have "\<not>(\<exists>t. t \<in> fst ` fset xs \<and> root t = y)" using insert.prems by auto
  ultimately show ?case using insert.IH by blast
qed (simp)

lemma insert_before_alt:
  "insert_before v e y xs
  = (\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1)) |`| xs"
  by(induction xs) (auto simp: Product_Type.prod.case_distrib)

lemma dverts_insert_before_aux:
  "\<exists>t. t \<in> fst ` fset xs \<and> root t = y
    \<Longrightarrow> (\<Union>x\<in>fset (insert_before v e y xs). \<Union> (dverts ` Basic_BNFs.fsts x))
        = insert v (\<Union>x\<in>fset xs. \<Union> (dverts ` Basic_BNFs.fsts x))"
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  obtain t1 e1 where t1_def: "x = (t1,e1)" by fastforce
  then show ?case
  proof(cases "root t1 = y")
    case True
    then have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "insert_before v e y (finsert x xs)
                = finsert (Node v {|(t1,e1)|},e) (insert_before v e y xs)"
      using t1_def True by simp
    then have 0: "(\<Union>x\<in>fset (insert_before v e y (finsert x xs)). \<Union> (dverts ` Basic_BNFs.fsts x))
      = insert v (dverts t1) \<union> (\<Union>x\<in>fset (insert_before v e y xs). \<Union> (dverts ` Basic_BNFs.fsts x))"
      using t1_def by simp
    have 1: "dverts (Node v {|(t1,e1)|}) = insert v (dverts t1)" by simp
    show ?thesis
    proof(cases "\<exists>t. t \<in> fst ` fset xs \<and> root t = y")
      case True
      then show ?thesis using t1_def 0 insert.IH by simp
    next
      case False
      then show ?thesis using t1_def 0 insert_before_not_y_id by force
    qed
  next
    case False
    then have 0: "\<exists>t. t \<in> fst ` fset xs \<and> root t = y" using insert.prems t1_def by force
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "insert_before v e y (finsert x xs) = finsert x (insert_before v e y xs)"
      by (simp add: False t1_def)
    then show ?thesis using insert.IH insert.prems 0 by simp
  qed
qed

lemma insert_between_add_v_if_x_in:
  "x \<in> dverts t \<Longrightarrow> dverts (insert_between v e x y t) = insert v (dverts t)"
using wf_verts proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "x=r")
    case False
    then obtain t e1 where t_def: "(t,e1) \<in> fset xs" "x \<in> dverts t" using Node.prems(1) by auto
    then have "\<forall>(t2,e2) \<in> fset xs. (t,e1) \<noteq> (t2,e2) \<longrightarrow> x \<notin> dverts t2"
      using Node.prems(2) by (fastforce simp: wf_dverts_iff_dverts')
    then have "\<forall>(t2,e2) \<in> fset xs. (t,e1) = (t2,e2) \<or> (insert_between v e x y t2) = t2"
      using insert_between_id_if_notin by fast
    moreover have "(insert_between v e x y t,e1)
        \<in> fset ((\<lambda>(t,e1). (insert_between v e x y t,e1)) |`| xs)" using t_def(1) by force
    moreover have "dverts (insert_between v e x y t) = insert v (dverts t)"
      using Node.IH Node.prems(2) t_def by auto
    ultimately show ?thesis using False by force
  qed (auto simp: dverts_insert_before_aux)
qed

lemma insert_before_only1_new:
  assumes "\<forall>(x,e1) \<in> fset xs. \<forall>(y,e2) \<in> fset xs. (dverts x \<inter> dverts y = {} \<or> (x,e1)=(y,e2))"
      and "(t1,e1) \<noteq> (t2,e2)"
      and "(t1,e1) \<in> fset (insert_before v e y xs)"
      and "(t2,e2) \<in> fset (insert_before v e y xs)"
    shows "(t1,e1) \<in> fset xs \<or> (t2,e2) \<in> fset xs"
proof (rule ccontr)
  assume "\<not>((t1,e1) \<in> fset xs \<or> (t2,e2) \<in> fset xs)"
  then have asm: "(t1,e1) \<notin> fset xs" "(t2,e2) \<notin> fset xs" by auto
  obtain t3 e3 where t3_def: "(t3, e3)\<in>fset xs" "Node v {|(t3, e3)|} = t1" "root t3 = y" "e1=e"
    using in_insert_before_child_in_orig assms(3) asm(1) by fast
  obtain t4 e4 where t4_def: "(t4, e4)\<in>fset xs" "Node v {|(t4, e4)|} = t2" "root t4 = y" "e2=e"
    using in_insert_before_child_in_orig assms(4) asm(2) by fast
  then have "dverts t3 \<inter> dverts t4 \<noteq> {}" using t3_def(3) dtree.set_sel(1) by force
  then have "(t3,e3) = (t4,e4)" using assms(1) t3_def(1) t4_def(1) by fast
  then show False using assms(2) t3_def(2,4) t4_def(2,4) by fast
qed

lemma disjoint_dverts_aux1:
  assumes "\<forall>(t1,e1) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. (dverts t1 \<inter> dverts t2 = {} \<or> (t1,e1)=(t2,e2))"
      and "v \<notin> dverts (Node r xs)"
      and "(t1,e1) \<in> fset (insert_before v e y xs)"
      and "(t2,e2) \<in> fset (insert_before v e y xs)"
      and "(t1,e1) \<noteq> (t2,e2)"
    shows "dverts t1 \<inter> dverts t2 = {}"
proof -
  consider "(t1,e1) \<in> fset xs" "(t2,e2) \<in> fset xs"
        | "(t1,e1) \<notin> fset xs" "(t2,e2) \<in> fset xs"
        | "(t1,e1) \<in> fset xs" "(t2,e2) \<notin> fset xs"
    using insert_before_only1_new assms(1,3-5) by fast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using assms(1,5) by fast
  next
    case 2
    obtain t3 e3 where t3_def: "(t3, e3)\<in>fset xs" "Node v {|(t3, e3)|} = t1" "root t3 = y" "e1=e"
      using in_insert_before_child_in_orig assms(3) 2 by fast
    then have "y\<noteq>v" using assms(2) dtree.set_sel(1) by force
    then have "(t3,e3) \<noteq> (t2,e2)" using assms(4) t3_def(3) root_noty_if_in_insert_before by fast
    then have "dverts t3 \<inter> dverts t2 = {}" using assms(1) 2(2) t3_def(1) by fast
    then show ?thesis using assms(1,2) t3_def(1,2) 2(2) by force
  next
    case 3
    obtain t3 e3 where t3_def: "(t3, e3)\<in>fset xs" "Node v {|(t3, e3)|} = t2" "root t3 = y" "e2=e"
      using in_insert_before_child_in_orig assms(4) 3 by fast
    then have "y\<noteq>v" using assms(2) dtree.set_sel(1) by force
    then have "(t3,e3) \<noteq> (t1,e1)" using assms(3) t3_def(3) root_noty_if_in_insert_before by fast
    then have "dverts t3 \<inter> dverts t1 = {}" using assms(1) 3(1) t3_def(1) by fast
    then show ?thesis using assms(2) t3_def(2) 3(1) by force
  qed
qed

lemma disjoint_dverts_aux1':
  assumes "wf_dverts (Node r xs)" and "v \<notin> dverts (Node r xs)"
  shows "\<forall>(x,e1) \<in> fset (insert_before v e y xs). \<forall>(y,e2) \<in> fset (insert_before v e y xs).
          dverts x \<inter> dverts y = {} \<or> (x,e1) = (y,e2)"
  using assms disjoint_dverts_aux1 disjoint_dverts_if_wf unfolding wf_dverts_iff_dverts' by fast

lemma insert_before_wf_dverts:
  "\<lbrakk>\<forall>(t,e1) \<in> fset xs. wf_dverts t; v \<notin> dverts(Node r xs); (t1,e1) \<in> fset (insert_before v e y xs)\<rbrakk>
    \<Longrightarrow> wf_dverts t1"
proof(induction xs)
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) \<in> fset (insert_before v e y xs)")
    case in_xs: True
    then show ?thesis
    proof(cases "?f x = (t1,e1)")
      case True
      have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
        by (simp add: insert.hyps prod.case_distrib)
      then have "insert_before v e y (finsert x xs) = insert_before v e y xs"
        using True in_xs by fastforce
      then show ?thesis using insert.IH insert.prems by simp
    next
      case False
      then show ?thesis using in_xs insert.IH insert.prems(1,2) by auto
    qed
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "?f x = (t1,e1)" using False insert.prems(3) by fastforce
    then show ?thesis
    proof(cases "root t1 = v")
      case True
      then have "(t1,e1) \<notin> fset (finsert x xs)" using insert.prems(2) dtree.set_sel(1) by force
      then obtain t2 e2 where
        t2_def: "(t2, e2)\<in>fset (finsert x xs)" "Node v {|(t2, e2)|} = t1" "root t2 = y" "e1=e"
        using in_insert_before_child_in_orig[of t1] insert.prems(3) by blast
      then show ?thesis using insert.prems(1,2) by (fastforce simp: wf_dverts_iff_dverts')
    next
      case False
      then have "(t1,e1) = x"
        using insert.prems(1) dtree.sel(1) \<open>?f x = (t1,e1)\<close>
        by (smt (verit, ccfv_SIG) Pair_inject old.prod.case case_prodE finsertI1)
      then show ?thesis using insert.prems(1) by auto
    qed
  qed
qed (simp)

lemma insert_before_root_nin_verts:
  "\<lbrakk>\<forall>(t,e1)\<in>fset xs. r \<notin> dverts t; v \<notin> dverts (Node r xs); (t1,e1) \<in> fset (insert_before v e y xs)\<rbrakk>
    \<Longrightarrow> r \<notin> dverts t1"
proof(induction xs)
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) \<in> fset (insert_before v e y xs)")
    case in_xs: True
    then show ?thesis
    proof(cases "?f x = (t1,e1)")
      case True
      have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
        by (simp add: insert.hyps prod.case_distrib)
      then have "insert_before v e y (finsert x xs) = insert_before v e y xs"
        using True in_xs by fastforce
      then show ?thesis using insert.IH insert.prems by simp
    next
      case False
      then show ?thesis using in_xs insert.IH insert.prems(1,2) by auto
    qed
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "?f x = (t1,e1)" using False insert.prems(3) by fastforce
    then show ?thesis
    proof(cases "root t1 = v")
      case True
      then have "(t1,e1) \<notin> fset (finsert x xs)" using insert.prems(2) dtree.set_sel(1) by force
      then obtain t2 e2 where
        t2_def: "(t2, e2)\<in>fset (finsert x xs)" "Node v {|(t2, e2)|} = t1" "root t2 = y" "e1=e"
        using in_insert_before_child_in_orig[of t1] insert.prems(3) by blast
      then show ?thesis using insert.prems(1,2) by fastforce
    next
      case False
      then have "(t1,e1) = x"
        using insert.prems(1) dtree.sel(1) \<open>?f x = (t1,e1)\<close>
        by (smt (verit, ccfv_SIG) Pair_inject old.prod.case case_prodE finsertI1)
      then show ?thesis using insert.prems(1) by auto
    qed
  qed
qed (simp)

lemma disjoint_dverts_aux2:
  assumes "wf_dverts (Node r xs)" and "v \<notin> dverts (Node r xs)"
  shows "\<forall>(x,e1) \<in> fset (finsert (Node v {||},e) xs). \<forall>(y,e2) \<in> fset (finsert (Node v {||},e) xs).
          dverts x \<inter> dverts y = {} \<or> (x,e1) = (y,e2)"
  using assms by (fastforce simp: wf_dverts_iff_dverts')

lemma disjoint_dverts_aux3:
  assumes "(t2,e2) \<in> (\<lambda>(t1,e1). (insert_between v e x y t1, e1)) ` fset xs"
      and "(t3,e3) \<in> (\<lambda>(t1,e1). (insert_between v e x y t1, e1)) ` fset xs"
      and "(t2,e2)\<noteq>(t3,e3)"
      and "(t,e1) \<in> fset xs"
      and "x \<in> dverts t"
      and "wf_dverts (Node r xs)"
      and "v \<notin> dverts (Node r xs)"
    shows "dverts t2 \<inter> dverts t3 = {}"
proof -
  have "\<forall>(t2,e2) \<in> fset xs. (t,e1)=(t2,e2) \<or> x \<notin> dverts t2"
    using assms(4-6) by (fastforce simp: wf_dverts_iff_dverts')
  then have nt1_id: "\<forall>(t2,e2) \<in> fset xs. (t,e1) = (t2,e2) \<or> insert_between v e x y t2 = t2"
    using insert_between_id_if_notin by fastforce
  have dverts_t1: "dverts (insert_between v e x y t) = insert v (dverts t)"
    using assms(5-6) by (simp add: insert_between_add_v_if_x_in)
  have t1_disj: "\<forall>(t2,e2) \<in> fset xs. (t,e1) = (t2,e2) \<or> dverts t2 \<inter> insert v (dverts t) = {}"
    using assms(4-7) by (fastforce simp: wf_dverts_iff_dverts')
  consider "(t2,e2) = (insert_between v e x y t,e1)"
      | "(t3,e3) = (insert_between v e x y t,e1)"
      | "(t2,e2) \<noteq> (insert_between v e x y t,e1)" "(t3,e3) \<noteq> (insert_between v e x y t,e1)"
    by fast
  then show ?thesis
  proof(cases)
    case 1
    then have "(t3,e3) \<in> fset xs" using assms(2,3) nt1_id by fastforce
    moreover have "(t3,e3) \<noteq> (t,e1)" using assms(2,3) 1 nt1_id by fastforce
    ultimately show ?thesis using 1 t1_disj dverts_t1 by fastforce
  next
    case 2
    then have "(t2,e2) \<in> fset xs" using assms(1,3) nt1_id by fastforce
    moreover have "(t2,e2) \<noteq> (t,e1)" using assms(1,3) 2 nt1_id by auto
    ultimately show ?thesis using 2 t1_disj dverts_t1 by fastforce
  next
    case 3
    then have "(t2,e2) \<in> fset xs" using assms(1) nt1_id by fastforce
    moreover have "(t3,e3) \<in> fset xs" using assms(2) 3(2) nt1_id by auto
    ultimately show ?thesis using assms(3,6) by (fastforce simp: wf_dverts_iff_dverts')
  qed
qed

lemma insert_between_wf_dverts: "v \<notin> dverts t \<Longrightarrow> wf_dverts (insert_between v e x y t)"
using wf_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret wf_dtree "Node r xs" by blast
  consider "x=r" "\<exists>t. t \<in> fst ` fset xs \<and> root t = y"
              | "x=r" "\<not>(\<exists>t. t \<in> fst ` fset xs \<and> root t = y)" | "x\<noteq>r" by fast
  then show ?case
  proof(cases)
    case 1
    then have "insert_between v e x y (Node r xs) = Node r (insert_before v e y xs)" by simp
    moreover have "\<forall>(x,e1) \<in> fset (insert_before v e y xs). r \<notin> dverts x"
      using insert_before_root_nin_verts wf_verts Node.prems(1)
      by (fastforce simp: wf_dverts_iff_dverts')
    moreover have "\<forall>(x,e1) \<in> fset (insert_before v e y xs). wf_dverts x"
      using insert_before_wf_dverts Node.prems(1) wf_verts by fastforce
    moreover have "\<forall>(x, e1)\<in>fset (insert_before v e y xs).
           \<forall>(y, e2)\<in>fset (insert_before v e y xs). dverts x \<inter> dverts y = {} \<or> (x, e1) = (y, e2)"
      using disjoint_dverts_aux1' Node.prems(1) wf_verts unfolding wf_dverts_iff_dverts' by fast
    ultimately show ?thesis by (fastforce simp: wf_dverts_iff_dverts')
  next
    case 2
    then have "insert_between v e x y (Node r xs) = Node r (finsert (Node v {||},e) xs)" by simp
    then show ?thesis
      using disjoint_dverts_aux2[of r xs v] Node.prems(1) wf_verts
      by (fastforce simp: wf_dverts_iff_dverts')
  next
    case 3
    let ?f = "\<lambda>(t1,e1). (insert_between v e x y t1, e1)"
    show ?thesis
    proof(cases "\<exists>(t1,e1) \<in> fset xs. x \<in> dverts t1")
      case True
      then obtain t1 e1 where t1_def: "(t1,e1) \<in> fset xs" " x \<in> dverts t1" by blast
      then interpret T: wf_dtree t1 using wf_dtree_rec by blast
      have "\<forall>(t2,e2) \<in> ?f ` fset xs. \<forall>(t3,e3) \<in> ?f ` fset xs.
              (t2,e2) = (t3,e3) \<or> dverts t2 \<inter> dverts t3 = {}"
        using T.disjoint_dverts_aux3 Node.prems(1) t1_def wf_verts by blast
      moreover have "\<And>t2 e2. (t2,e2) \<in> ?f ` fset xs \<longrightarrow> r \<notin> dverts t2 \<and> wf_dverts t2"
      proof
        fix t2 e2
        assume asm: "(t2,e2) \<in> ?f ` fset xs"
        then show "r \<notin> dverts t2 \<and> wf_dverts t2"
        proof(cases "(t2,e2) = (insert_between v e x y t1,e1)")
          case True
          then have "wf_dverts (insert_between v e x y t1)"
            using Node.IH Node.prems(1) T.wf_dtree_axioms t1_def(1) by auto
          then show ?thesis
            using Node.prems(1) wf_verts True T.insert_between_add_v_if_x_in t1_def
            by (auto simp: wf_dverts_iff_dverts')
        next
          case False
          have "\<forall>(t2,e2) \<in> fset xs. (t1,e1)=(t2,e2) \<or> x \<notin> dverts t2"
            using wf_verts t1_def by (fastforce simp: wf_dverts_iff_dverts')
          then have "\<forall>(t2,e2) \<in> fset xs. (t1,e1) = (t2,e2) \<or> insert_between v e x y t2 = t2"
            using insert_between_id_if_notin by fastforce
          then show ?thesis using wf_verts asm False by (fastforce simp: wf_dverts_iff_dverts')
        qed
      qed
      ultimately show ?thesis using 3 by (fastforce simp: wf_dverts_iff_dverts')
    next
      case False
      then show ?thesis
        using wf_verts 3 insert_between_id_if_notin fst_conv
        by (smt (verit, ccfv_threshold) fsts.cases dtree.inject dtree.set_cases(1) case_prodI2)
    qed
  qed
qed

lemma darcs_insert_before_aux:
  "\<exists>t. t \<in> fst ` fset xs \<and> root t = y
    \<Longrightarrow> (\<Union>x\<in>fset (insert_before v e y xs). \<Union> (darcs ` Basic_BNFs.fsts x) \<union> Basic_BNFs.snds x)
        = insert e (\<Union>x\<in>fset xs. \<Union> (darcs ` Basic_BNFs.fsts x) \<union> Basic_BNFs.snds x)"
proof(induction xs)
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  let ?xs = "insert_before v e y (finsert x xs)"
  obtain t1 e1 where t1_def: "x = (t1,e1)" by fastforce
  then show ?case
  proof(cases "root t1 = y")
    case True
    then have "?xs = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "?xs = finsert (Node v {|(t1,e1)|},e) (insert_before v e y xs)"
      using t1_def True by simp
    then have 0: "(\<Union>x\<in>fset ?xs. \<Union> (darcs ` Basic_BNFs.fsts x) \<union> Basic_BNFs.snds x)
      = (\<Union> (darcs ` {Node v {|(t1,e1)|}}) \<union> {e})
        \<union> (\<Union>x\<in>fset (insert_before v e y xs). \<Union> (darcs ` Basic_BNFs.fsts x) \<union> Basic_BNFs.snds x)"
      using t1_def by simp
    have 1: "dverts (Node v {|(t1,e1)|}) = insert v (dverts t1)" by simp
    show ?thesis
    proof(cases "\<exists>t. t \<in> fst ` fset xs \<and> root t = y")
      case True
      then show ?thesis using t1_def 0 insert.IH by simp
    next
      case False
      then show ?thesis using t1_def 0 insert_before_not_y_id by force
    qed
  next
    case False
    then have 0: "\<exists>t. t \<in> fst ` fset xs \<and> root t = y" using insert.prems t1_def by force
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have "insert_before v e y (finsert x xs) = finsert x (insert_before v e y xs)"
      by (simp add: False t1_def)
    then show ?thesis using insert.IH insert.prems 0 by simp
  qed
qed (simp)

lemma insert_between_add_e_if_x_in:
  "x \<in> dverts t \<Longrightarrow> darcs (insert_between v e x y t) = insert e (darcs t)"
using wf_verts proof(induction t)
  case (Node r xs)
  show ?case
  proof(cases "x=r")
    case False
    then obtain t e1 where t_def: "(t,e1) \<in> fset xs" "x \<in> dverts t" using Node.prems(1) by auto
    then have "\<forall>(t2,e2) \<in> fset xs. (t,e1) \<noteq> (t2,e2) \<longrightarrow> x \<notin> dverts t2"
      using Node.prems(2) by (fastforce simp: wf_dverts_iff_dverts')
    then have "\<forall>(t2,e2) \<in> fset xs. (t,e1) = (t2,e2) \<or> (insert_between v e x y t2) = t2"
      using insert_between_id_if_notin by fast
    moreover have "(insert_between v e x y t,e1)
        \<in> fset ((\<lambda>(t,e1). (insert_between v e x y t,e1)) |`| xs)" using t_def(1) by force
    moreover have "darcs (insert_between v e x y t) = insert e (darcs t)"
      using Node.IH Node.prems(2) t_def by auto
    ultimately show ?thesis using False by force
  qed (auto simp: darcs_insert_before_aux)
qed

lemma disjoint_darcs_aux1_aux1:
  assumes "disjoint_darcs xs"
      and "wf_dverts (Node r xs)"
      and "v \<notin> dverts (Node r xs)"
      and "e \<notin> darcs (Node r xs)"
      and "(t1,e1) \<in> fset (insert_before v e y xs)"
      and "(t2,e2) \<in> fset (insert_before v e y xs)"
      and "(t1,e1) \<noteq> (t2,e2)"
    shows "(darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {}"
proof -
  consider "(t1,e1) \<in> fset xs" "(t2,e2) \<in> fset xs"
        | "(t1,e1) \<notin> fset xs" "(t2,e2) \<in> fset xs"
        | "(t1,e1) \<in> fset xs" "(t2,e2) \<notin> fset xs"
    using insert_before_only1_new assms(2,5-7) by (fastforce simp: wf_dverts_iff_dverts')
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using assms(1,7) by fast
  next
    case 2
    obtain t3 e3 where t3_def: "(t3, e3)\<in>fset xs" "Node v {|(t3, e3)|} = t1" "root t3 = y" "e1=e"
      using in_insert_before_child_in_orig assms(5) 2 by fast
    then have "v\<noteq>y" using assms(3) dtree.set_sel(1) by force
    then have "(t3,e3) \<noteq> (t2,e2)" using assms(6) t3_def(3) root_noty_if_in_insert_before by fast
    then have "(darcs t3 \<union> {e3}) \<inter> (darcs t2 \<union> {e2}) = {}" using assms(1) 2(2) t3_def(1) by fast
    then show ?thesis using assms(4) t3_def(4) 2(2) t3_def(2) by force
  next
    case 3
    obtain t3 e3 where t3_def: "(t3, e3)\<in>fset xs" "Node v {|(t3, e3)|} = t2" "root t3 = y" "e2=e"
      using in_insert_before_child_in_orig assms(6) 3 by fast
    then have "v\<noteq>y" using assms(3) dtree.set_sel(1) by force
    then have "(t3,e3) \<noteq> (t1,e1)" using assms(5) t3_def(3) root_noty_if_in_insert_before by fast
    then have "(darcs t3 \<union> {e3}) \<inter> (darcs t1 \<union> {e1}) = {}" using assms(1) 3(1) t3_def(1) by fast
    then show ?thesis using assms(4) t3_def(4) 3(1) t3_def(2) by force
  qed
qed

lemma disjoint_darcs_aux1_aux2:
  assumes "disjoint_darcs xs"
      and "e \<notin> darcs (Node r xs)"
      and "(t1,e1) \<in> fset (insert_before v e y xs)"
    shows "e1 \<notin> darcs t1"
proof(cases "(t1,e1) \<in> fset xs")
  case True
  then show ?thesis using assms(1) by fast
next
  case False
  then obtain t3 e3 where "(t3, e3)\<in>fset xs" "Node v {|(t3, e3)|} = t1" "e1=e"
    using in_insert_before_child_in_orig assms(3) by fast
  then show ?thesis using assms(2) by auto
qed

lemma disjoint_darcs_aux1:
  assumes "wf_dverts (Node r xs)" and "v \<notin> dverts (Node r xs)"
      and "wf_darcs (Node r xs)" and "e \<notin> darcs (Node r xs)"
    shows "disjoint_darcs (insert_before v e y xs)" (is "disjoint_darcs ?xs")
proof -
  have 0: "disjoint_darcs xs" using assms(3) disjoint_darcs_if_wf_xs by simp
  then have "\<forall>(t1,e1) \<in> fset ?xs. e1 \<notin> darcs t1"
    using disjoint_darcs_aux1_aux2[of xs] assms(4) by fast
  moreover have "\<forall>(t1,e1) \<in> fset ?xs. \<forall>(t2,e2) \<in> fset ?xs.
              (darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {} \<or> (t1,e1) = (t2,e2)"
    using disjoint_darcs_aux1_aux1[of xs] assms(1,2,4) 0 by blast
  ultimately show ?thesis by fast
qed

lemma insert_before_wf_darcs:
  "\<lbrakk>wf_darcs (Node r xs); e \<notin> darcs (Node r xs); (t1,e1) \<in> fset (insert_before v e y xs)\<rbrakk>
    \<Longrightarrow> wf_darcs t1"
proof(induction xs)
  case (insert x xs)
  let ?f = "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1))"
  show ?case
  proof(cases "(t1,e1) \<in> fset (insert_before v e y xs)")
    case in_xs: True
    then show ?thesis
    proof(cases "?f x = (t1,e1)")
      case True
      have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
        by (simp add: insert.hyps prod.case_distrib)
      then have "insert_before v e y (finsert x xs) = insert_before v e y xs"
        using True in_xs by fastforce
      moreover have "disjoint_darcs xs"
        using disjoint_darcs_insert[OF disjoint_darcs_if_wf_xs[OF insert.prems(1)]] .
      ultimately show ?thesis
        using insert.IH insert.prems unfolding wf_darcs_iff_darcs' by force
    next
      case False
      have "disjoint_darcs xs"
        using disjoint_darcs_insert[OF disjoint_darcs_if_wf_xs[OF insert.prems(1)]] .
      then show ?thesis
        using in_xs False insert.IH insert.prems(1,2) by (simp add: wf_darcs_iff_darcs')
    qed
  next
    case False
    have "insert_before v e y (finsert x xs) = finsert (?f x) (insert_before v e y xs)"
      by (simp add: insert.hyps prod.case_distrib)
    then have 0: "?f x = (t1,e1)" using False insert.prems(3) by fastforce
    then show ?thesis
    proof(cases "e1=e")
      case True
      then have "(t1,e1) \<notin> fset (finsert x xs)" using insert.prems(2) dtree.set_sel(1) by force
      then obtain t2 e2 where
        t2_def: "(t2, e2)\<in>fset (finsert x xs)" "Node v {|(t2, e2)|} = t1" "root t2 = y" "e1=e"
        using in_insert_before_child_in_orig[of t1] insert.prems(3) by blast
      then show ?thesis
        using insert.prems(1) t2_def by (fastforce simp: wf_darcs_iff_darcs')
    next
      case False
      then have "(t1,e1) = x"
        by (smt (z3) 0 old.prod.exhaust prod.inject case_prod_Pair_iden case_prod_conv)
      then show ?thesis using insert.prems(1) by auto
    qed
  qed
qed (simp)

lemma disjoint_darcs_aux2:
  assumes "wf_darcs (Node r xs)" and "e \<notin> darcs (Node r xs)"
  shows "disjoint_darcs (finsert (Node v {||},e) xs)"
  using assms unfolding wf_darcs_iff_darcs' by fastforce

lemma disjoint_darcs_aux3_aux1:
  assumes "(t,e1) \<in> fset xs"
      and "x \<in> dverts t"
      and "wf_darcs (Node r xs)"
      and "e \<notin> darcs (Node r xs)"
      and "(t2,e2) \<in> (\<lambda>(t1,e1). (insert_between v e x y t1, e1)) ` fset xs"
      and "(t3,e3) \<in> (\<lambda>(t1,e1). (insert_between v e x y t1, e1)) ` fset xs"
      and "(t2,e2)\<noteq>(t3,e3)"
      and "wf_dverts (Node r xs)"
    shows "(darcs t2 \<union> {e2}) \<inter> (darcs t3 \<union> {e3}) = {}"
proof -
  have "\<forall>(t2,e2) \<in> fset xs. (t,e1)=(t2,e2) \<or> x \<notin> dverts t2"
    using assms(1,2,8) by (fastforce simp: wf_dverts_iff_dverts')
  then have nt1_id: "\<forall>(t2,e2) \<in> fset xs. (t,e1) = (t2,e2) \<or> insert_between v e x y t2 = t2"
    using insert_between_id_if_notin by fastforce
  have darcs_t: "darcs (insert_between v e x y t) = insert e (darcs t)"
    using assms(2,3) by (simp add: insert_between_add_e_if_x_in)
  consider "(t2,e2) = (insert_between v e x y t,e1)"
      | "(t3,e3) = (insert_between v e x y t,e1)"
      | "(t2,e2) \<noteq> (insert_between v e x y t,e1)" "(t3,e3) \<noteq> (insert_between v e x y t,e1)"
    by fast
  then show ?thesis
  proof(cases)
    case 1
    then have "(t3,e3) \<in> fset xs" using assms(6,7) nt1_id by fastforce
    moreover have "(t3,e3) \<noteq> (t,e1)" using assms(6,7) 1 nt1_id by fastforce
    ultimately have "(darcs t \<union> {e1,e}) \<inter> (darcs t3 \<union> {e3}) = {}"
      using assms(1,3,4) unfolding wf_darcs_iff_darcs' by fastforce
    then show ?thesis using 1 darcs_t by auto
  next
    case 2
    then have "(t2,e2) \<in> fset xs" using assms(5,7) nt1_id by fastforce
    moreover have "(t2,e2) \<noteq> (t,e1)" using assms(5,7) 2 nt1_id by auto
    ultimately have "(darcs t \<union> {e1,e}) \<inter> (darcs t2 \<union> {e2}) = {}"
      using assms(1,3,4) unfolding wf_darcs_iff_darcs' by fastforce
    then show ?thesis using 2 darcs_t by force
  next
    case 3
    then have "(t2,e2) \<in> fset xs" using assms(5) nt1_id by fastforce
    moreover have "(t3,e3) \<in> fset xs" using assms(6) 3(2) nt1_id by auto
    ultimately show ?thesis using assms(3,7) unfolding wf_darcs_iff_darcs' by fastforce
  qed
qed

lemma disjoint_darcs_aux3_aux2:
  assumes "(t,e1) \<in> fset xs"
      and "x \<in> dverts t"
      and "wf_darcs (Node r xs)"
      and "e \<notin> darcs (Node r xs)"
      and "(t2,e2) \<in> (\<lambda>(t1,e1). (insert_between v e x y t1, e1)) ` fset xs"
      and "wf_dverts (Node r xs)"
    shows "e2 \<notin> darcs t2"
proof(cases "(t2,e2) \<in> fset xs")
  case True
  then show ?thesis using assms(3) unfolding wf_darcs_iff_darcs' by auto
next
  case False
  obtain t1 where t1_def: "insert_between v e x y t1 = t2" "(t1,e2) \<in> fset xs"
    using assms(5) by fast
  then have "x \<in> dverts t1" using insert_between_id_if_notin False by fastforce
  then have "t = t1" using assms(1,2,6) t1_def(2) by (fastforce simp: wf_dverts_iff_dverts')
  then have darcs_t: "darcs t2 = insert e (darcs t1)"
    using insert_between_add_e_if_x_in assms(2) t1_def(1) by force
  then show ?thesis using assms(3,4) t1_def(2) unfolding wf_darcs_iff_darcs' by fastforce
qed

lemma disjoint_darcs_aux3:
  assumes "(t,e1) \<in> fset xs"
      and "x \<in> dverts t"
      and "wf_darcs (Node r xs)"
      and "e \<notin> darcs (Node r xs)"
      and "wf_dverts (Node r xs)"
    shows "disjoint_darcs ((\<lambda>(t1,e1). (insert_between v e x y t1, e1)) |`| xs)"
proof -
  let ?xs = "(\<lambda>(t1,e1). (insert_between v e x y t1, e1)) |`| xs"
  let ?xs' = "(\<lambda>(t1,e1). (insert_between v e x y t1, e1)) ` fset xs"
  have 0: "fset ?xs = ?xs'" by simp
  then have "\<forall>(t1,e1) \<in> fset ?xs. e1 \<notin> darcs t1"
    using disjoint_darcs_aux3_aux2 assms by blast
  moreover have "\<forall>(t1,e1) \<in> ?xs'. \<forall>(t2,e2) \<in> ?xs'.
              (darcs t1 \<union> {e1}) \<inter> (darcs t2 \<union> {e2}) = {} \<or> (t1,e1) = (t2,e2)"
    using disjoint_darcs_aux3_aux1 assms by blast
  ultimately show ?thesis using 0 by fastforce
qed

lemma insert_between_wf_darcs:
  "\<lbrakk>e \<notin> darcs t; v \<notin> dverts t \<rbrakk> \<Longrightarrow> wf_darcs (insert_between v e x y t)"
using wf_dtree_axioms proof(induction t)
  case (Node r xs)
  then interpret wf_dtree "Node r xs" by blast
  consider "x=r" "\<exists>t. t \<in> fst ` fset xs \<and> root t = y"
              | "x=r" "\<not>(\<exists>t. t \<in> fst ` fset xs \<and> root t = y)" | "x\<noteq>r" by fast
  then show ?case
  proof(cases)
    case 1
    then have "insert_between v e x y (Node r xs) = Node r (insert_before v e y xs)" by simp
    moreover have "\<forall>(x,e1) \<in> fset (insert_before v e y xs). wf_darcs x"
      using insert_before_wf_darcs Node.prems(1) wf_arcs by fast
    moreover have "disjoint_darcs (insert_before v e y xs)"
      using disjoint_darcs_aux1[OF wf_verts Node.prems(2) wf_arcs Node.prems(1)] .
    ultimately show ?thesis by (simp add: wf_darcs_if_darcs'_aux)
  next
    case 2
    then have "insert_between v e x y (Node r xs) = Node r (finsert (Node v {||},e) xs)" by simp
    then show ?thesis
      using disjoint_darcs_aux2 Node.prems(1) wf_arcs by (simp add: wf_darcs_iff_darcs')
  next
    case 3
    let ?f = "\<lambda>(t1,e1). (insert_between v e x y t1, e1)"
    show ?thesis
    proof(cases "\<exists>(t1,e1) \<in> fset xs. x \<in> dverts t1")
      case True
      then obtain t1 e1 where t1_def: "(t1,e1) \<in> fset xs" " x \<in> dverts t1" by blast
      then interpret T: wf_dtree t1 using wf_dtree_rec by blast
      have "\<And>t2 e2. (t2,e2) \<in> fset (?f |`| xs) \<longrightarrow> wf_darcs t2"
      proof
        fix t2 e2
        assume asm: "(t2,e2) \<in> fset (?f |`| xs)"
        then show "wf_darcs t2"
        proof(cases "(t2,e2) = (insert_between v e x y t1,e1)")
          case True
          then have "wf_darcs (insert_between v e x y t1)"
            using Node t1_def(1) T.wf_dtree_axioms
            by (metis dtree.set_intros(2) dtree.set_intros(3) insertI1 prod_set_simps(1))
          then show ?thesis using True by blast
        next
          case False
          have "\<forall>(t2,e2) \<in> fset xs. (t1,e1)=(t2,e2) \<or> x \<notin> dverts t2"
            using wf_verts t1_def by (fastforce simp: wf_dverts_iff_dverts')
          then have "\<forall>(t2,e2) \<in> fset xs. (t1,e1) = (t2,e2) \<or> insert_between v e x y t2 = t2"
            using insert_between_id_if_notin by fastforce
          then show ?thesis using wf_arcs asm False by fastforce
        qed
      qed
      moreover have "disjoint_darcs (?f |`| xs)"
        using T.disjoint_darcs_aux3 Node.prems(1) t1_def wf_arcs wf_verts by presburger
      ultimately show ?thesis using 3 by (fastforce simp: wf_darcs_iff_darcs')
    next
      case False
      then show ?thesis
        using wf_arcs 3 insert_between_id_if_notin fst_conv
        by (smt (verit, ccfv_threshold) fsts.cases dtree.inject dtree.set_cases(1) case_prodI2)
    qed
  qed
qed

theorem insert_between_wf_dtree:
  "\<lbrakk>e \<notin> darcs t; v \<notin> dverts t \<rbrakk> \<Longrightarrow> wf_dtree (insert_between v e x y t)"
  by (simp add: insert_between_wf_dverts insert_between_wf_darcs wf_dtree_def)

lemma snds_neq_card_eq_card_snd:
  "\<forall>(t,e) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. e\<noteq>e2 \<or> (t,e) = (t2,e2) \<Longrightarrow> fcard xs = fcard (snd |`| xs)"
proof(induction xs)
  case empty
  then have "(snd |`| {||}) = {||}" by blast
  then show ?case by (simp add: fcard_fempty)
next
  case (insert x xs)
  have "fcard xs = fcard (snd |`| xs)" using insert.IH insert.prems by fastforce
  moreover have "snd x |\<notin>| snd |`| xs"
  proof
    assume asm: "snd x |\<in>| snd |`| xs"
    then obtain t e where t_def: "x = (t,e)" by fastforce
    then obtain t2 where t2_def: "(t2,e) |\<in>| xs" using asm by auto
    then have "(t,e)\<noteq>(t2,e)" using insert.hyps t_def by blast
    moreover have "(t,e) \<in> fset (finsert x xs)" using t_def by simp
    moreover have "(t2,e) \<in> fset (finsert x xs)" using t2_def by fastforce
    ultimately show False using insert.prems by fast
  qed
  ultimately show ?case by (simp add: fcard_finsert_disjoint local.insert.hyps)
qed

lemma snds_neq_img_snds_neq:
  assumes "\<forall>(t,e) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. e\<noteq>e2 \<or> (t,e) = (t2,e2)"
  shows "\<forall>(t1,e1) \<in> fset ((\<lambda>(t1,e1). (f t1, e1)) |`| xs).
          \<forall>(t2,e2) \<in> fset ((\<lambda>(t1,e1). (f t1, e1)) |`| xs). e1\<noteq>e2 \<or> (t1,e1) = (t2,e2)"
  using assms by auto

lemma snds_neq_if_disjoint_darcs:
  assumes "disjoint_darcs xs"
  shows "\<forall>(t,e) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. e\<noteq>e2 \<or> (t,e) = (t2,e2)"
  using assms by fast

lemma snds_neq_img_card_eq:
  assumes "\<forall>(t,e) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. e\<noteq>e2 \<or> (t,e) = (t2,e2)"
  shows "fcard ((\<lambda>(t1,e1). (f t1, e1)) |`| xs) = fcard xs"
proof -
  let ?f = "\<lambda>(t1,e1). (f t1, e1)"
  have "\<forall>(t,e) \<in> fset (?f |`| xs). \<forall>(t2,e2) \<in> fset (?f |`| xs). e\<noteq>e2 \<or> (t,e) = (t2,e2)"
    using assms snds_neq_img_snds_neq by auto
  then have "fcard (?f |`| xs) = fcard (snd |`| (?f |`| xs))"
    using snds_neq_card_eq_card_snd by blast
  moreover have "snd |`| (?f |`| xs) = snd |`| xs" by force
  moreover have "fcard xs = fcard (snd |`| xs)" using snds_neq_card_eq_card_snd assms by blast
  ultimately show ?thesis by simp
qed

lemma fst_neq_img_card_eq:
  assumes "\<forall>(t,e) \<in> fset xs. \<forall>(t2,e2) \<in> fset xs. f t \<noteq> f t2 \<or> (t,e) = (t2,e2)"
  shows "fcard ((\<lambda>(t1,e1). (f t1, e1)) |`| xs) = fcard xs"
using assms proof(induction xs)
  case empty
  then have "(snd |`| {||}) = {||}" by blast
  then show ?case by (simp add: fcard_fempty)
next
  case (insert x xs)
  have "fcard xs = fcard ((\<lambda>(t1,e1). (f t1, e1)) |`| xs)" using insert by fastforce
  moreover have "(\<lambda>(t1,e1). (f t1, e1)) x |\<notin>| (\<lambda>(t1,e1). (f t1, e1)) |`| xs"
  proof
    assume asm: "(\<lambda>(t1,e1). (f t1, e1)) x |\<in>| (\<lambda>(t1,e1). (f t1, e1)) |`| xs"
    then obtain t e where t_def: "x = (t,e)" by fastforce
    then obtain t2 e2 where t2_def:
        "(t2,e2) |\<in>| xs" "(\<lambda>(t1,e1). (f t1, e1)) (t2,e2) = (\<lambda>(t1,e1). (f t1, e1)) (t,e)"
      using asm by auto
    then have "(t,e)\<noteq>(t2,e)" using insert.hyps t_def by fast
    moreover have "(t,e) \<in> fset (finsert x xs)" using t_def by simp
    moreover have "(t2,e2) \<in> fset (finsert x xs)" using t2_def(1) by fastforce
    ultimately show False using insert.prems t2_def(2) by fast
  qed
  ultimately show ?case by (simp add: fcard_finsert_disjoint local.insert.hyps)
qed

lemma x_notin_insert_before:
  assumes "x |\<notin>| xs" and "wf_dverts (Node r (finsert x xs))"
  shows "(\<lambda>(t1,e1). if root t1 = y then (Node v {|(t1,e1)|},e) else (t1,e1)) x
          |\<notin>| (insert_before v e y xs)" (is "?f x |\<notin>|_")
proof (cases "root (fst x) = y")
  case True
  then obtain t1 e1 where t1_def: "x = (t1,e1)" "root t1 = y" by fastforce
  then have 0: "\<forall>(t2,e2) \<in> fset xs. dverts t1 \<inter> dverts t2 = {}"
    using assms disjoint_dverts_if_wf_aux by fastforce
  then have "\<forall>(t2,e2) \<in> fset xs. root t2 \<noteq> y"
    by (smt (verit, del_insts) dtree.set_sel(1) t1_def(2) case_prodD case_prodI2 disjoint_iff)
  hence "\<nexists>t. t \<in> fst ` fset xs \<and> dtree.root t = y"
    by fastforce
  then have 1: "(insert_before v e y xs) = xs" using insert_before_not_y_id by fastforce
  have "?f x = (Node v {|(t1,e1)|},e)" using t1_def by simp
  then have "\<forall>(t2,e2) \<in> fset xs. (fst (?f x)) \<noteq> t2" using 0 dtree.set_sel(1) by fastforce
  then have "\<forall>(t2,e2) \<in> fset (insert_before v e y xs). ?f x \<noteq> (t2,e2)" using 1 by fastforce
  then show ?thesis by fast
next
  case False
  then have x_id: "?f x = x" by (smt (verit) old.prod.exhaust case_prod_conv fst_conv)
  then show ?thesis
  proof(cases "\<exists>t1. t1 \<in> fst ` fset xs \<and> root t1 = y")
    case True
    then obtain t1 e1 where t1_def: "(t1,e1) \<in> fset xs" "root t1 = y" by force
    then have "(t1,e1) \<in> fset (finsert x xs)" by auto
    then have 0: "\<forall>(t2,e2) \<in> fset (finsert x xs). (t1,e1) = (t2,e2) \<or> dverts t1 \<inter> dverts t2 = {}"
      using assms(2) disjoint_dverts_if_wf_aux by fast
    then have "\<forall>(t2,e2) \<in> fset (finsert x xs). (t1,e1) = (t2,e2) \<or> root t2 \<noteq> y"
      using dtree.set_sel(1) t1_def(2) insert_not_empty
      by (smt (verit, ccfv_threshold) Int_insert_right_if1 prod.case_eq_if insert_absorb)
    then have "\<nexists>t. t \<in> fst ` fset (xs |-| {|(t1,e1)|}) \<and> root t = y" by fastforce
    then have 1: "?f |`| (xs |-| {|(t1,e1)|}) = (xs |-| {|(t1,e1)|})"
      using insert_before_not_y_id[of "xs |-| {|(t1,e1)|}"] by (simp add: insert_before_alt)
    have "?f (t1,e1) = (Node v {|(t1,e1)|},e)" using t1_def by simp
    then have "?f |`| xs = finsert (Node v {|(t1,e1)|},e) (?f |`| (xs |-| {|(t1,e1)|}))"
      using t1_def(1) by (metis (no_types, lifting) fimage_finsert finsert_fminus)
    then have "?f |`| xs = finsert (Node v {|(t1,e1)|},e) (xs |-| {|(t1,e1)|})"
      using 1 by simp
    then have 2: "insert_before v e y xs = finsert (Node v {|(t1,e1)|},e) (xs |-| {|(t1,e1)|})"
      by (simp add: insert_before_alt)
    have "dverts t1 \<inter> dverts (fst x) = {}" using 0 assms(1) t1_def(1) by fastforce
    then have "(Node v {|(t1,e1)|},e) \<noteq> x" using dtree.set_sel(1) by fastforce
    then show ?thesis using 2 assms(1) x_id by auto
  next
    case False
    then have "(insert_before v e y xs) = xs" using insert_before_not_y_id by fastforce
    then show ?thesis using assms(1) x_id by simp
  qed
qed

end

end