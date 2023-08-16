theory Limit
  imports Main
begin

section \<open>Slightly adjusted content from AFP/LocalLexing\<close>

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "natUnion f = \<Union> { f n | n. True }"

definition limit  :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

definition setmonotone :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "setmonotone f = (\<forall> X. X \<subseteq> f X)"

lemma subset_setmonotone: "setmonotone f \<Longrightarrow> X \<subseteq> f X"
  by (simp add: setmonotone_def)

lemma funpower_id [simp]: "funpower id n = id"
  by (rule ext, induct n, simp_all)

lemma limit_id [simp]: "limit id = id"
  by (rule ext, auto simp add: limit_def natUnion_def)

definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "chain C = (\<forall> i. C i \<subseteq> C (i + 1))"

definition continuous :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool"
where
  "continuous f = (\<forall> C. chain C \<longrightarrow> (chain (f o C) \<and> f (natUnion C) = natUnion (f o C)))"

lemma natUnion_upperbound: 
  "(\<And> n. f n \<subseteq> G) \<Longrightarrow> (natUnion f) \<subseteq> G"
by (auto simp add: natUnion_def)

lemma funpower_upperbound:
  "(\<And> I. I \<subseteq> G \<Longrightarrow> f I \<subseteq> G) \<Longrightarrow> I \<subseteq> G \<Longrightarrow> funpower f n I \<subseteq> G"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by simp
qed

lemma limit_upperbound:
  "(\<And> I. I \<subseteq> G \<Longrightarrow> f I \<subseteq> G) \<Longrightarrow> I \<subseteq> G \<Longrightarrow> limit f I \<subseteq> G"
by (simp add: funpower_upperbound limit_def natUnion_upperbound)

lemma elem_limit_simp: "x \<in> limit f X = (\<exists> n. x \<in> funpower f n X)"
by (auto simp add: limit_def natUnion_def)

definition pointwise :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "pointwise f = (\<forall> X. f X = \<Union> { f {x} | x. x \<in> X})" 

lemma natUnion_elem: "x \<in> f n \<Longrightarrow> x \<in> natUnion f"
using natUnion_def by fastforce
  
lemma limit_elem: "x \<in> funpower f n X \<Longrightarrow> x \<in> limit f X"
by (simp add: limit_def natUnion_elem)

definition pointbase :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "pointbase F I = \<Union> { F X | X. finite X \<and> X \<subseteq> I }"

definition pointbased :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "pointbased f = (\<exists> F. f = pointbase F)"  

lemma chain_implies_mono: "chain C \<Longrightarrow> mono C"
by (simp add: chain_def mono_iff_le_Suc)

lemma setmonotone_implies_chain_funpower:
  assumes setmonotone: "setmonotone f"
  shows "chain (\<lambda> n. funpower f n I)"
by (simp add: chain_def setmonotone subset_setmonotone)  

lemma natUnion_subset: "(\<And> n. \<exists> m. f n \<subseteq> g m) \<Longrightarrow> natUnion f \<subseteq> natUnion g"
  by (meson natUnion_elem natUnion_upperbound subset_iff)

lemma natUnion_eq[case_names Subset Superset]: 
  "(\<And> n. \<exists> m. f n \<subseteq> g m) \<Longrightarrow> (\<And> n. \<exists> m. g n \<subseteq> f m) \<Longrightarrow> natUnion f = natUnion g"
by (simp add: natUnion_subset subset_antisym)
  
lemma natUnion_shift[symmetric]: 
  assumes chain: "chain C"
  shows "natUnion C = natUnion (\<lambda> n. C (n + m))"
proof (induct rule: natUnion_eq)
  case (Subset n)
    show ?case using chain chain_implies_mono le_add1 mono_def by blast 
next
  case (Superset n)
    show ?case by blast 
qed

definition regular :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "regular f = (setmonotone f \<and> continuous f)"

lemma regular_fixpoint:
  assumes regular: "regular f"
  shows "f (limit f I) = limit f I"
proof -
  have setmonotone: "setmonotone f" using regular regular_def by blast
  have continuous: "continuous f" using regular regular_def by blast

  let ?C = "\<lambda> n. funpower f n I"
  have chain: "chain ?C"
    by (simp add: setmonotone setmonotone_implies_chain_funpower)
  have "f (limit f I) = f (natUnion ?C)"
    using limit_def by metis
  also have "f (natUnion ?C) = natUnion (f o ?C)"
    by (metis continuous continuous_def chain)
  also have "natUnion (f o ?C) = natUnion (\<lambda> n. f(funpower f n I))"
    by (meson comp_apply)
  also have "natUnion (\<lambda> n. f(funpower f n I)) = natUnion (\<lambda> n. ?C (n + 1))"
    by simp
  also have "natUnion (\<lambda> n. ?C(n + 1)) = natUnion ?C"
    by (metis (no_types, lifting) Limit.chain_def chain natUnion_eq)
  finally show ?thesis by (simp add: limit_def)
qed  
    
lemma fix_is_fix_of_limit:
  assumes fixpoint: "f I = I"   
  shows "limit f I = I"
proof -
  have funpower: "\<And> n. funpower f n I = I" 
  proof -  
    fix n :: nat
    from fixpoint show "funpower f n I = I"
      by (induct n, auto)
  qed
  show ?thesis by (simp add: limit_def funpower natUnion_def)
qed     

lemma limit_is_idempotent: "regular f \<Longrightarrow> limit f (limit f I) = limit f I"
by (simp add: fix_is_fix_of_limit regular_fixpoint)

definition mk_regular1 :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mk_regular1 P F I = I \<union> { F q x | q x. x \<in> I \<and> P q x }"

definition mk_regular2 :: "('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mk_regular2 P F I = I \<union> { F q x y | q x y. x \<in> I \<and> y \<in> I \<and> P q x y }"

end