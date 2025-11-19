theory Basic_Terms 
  imports Sorted_Contexts
begin

lemma map_le_map_add_left:
  assumes disj: "dom m \<inter> dom n = {}"
  shows "m \<subseteq>\<^sub>m m ++ n"
  using map_le_map_add map_add_comm[OF disj] by auto

section \<open>Basic Terms\<close>

text \<open>Given two signatures C and D, a term \<open>f(s\<^sub>1,\<dots>,s\<^sub>n)\<close> is called a basic term
if \<open>f : [\<sigma>\<^sub>1,\<dots>,\<sigma>\<^sub>n] \<rightarrow> \<tau> in D\<close> and \<open>s\<^sub>1 : \<sigma>\<^sub>1,\<dots>,s\<^sub>n : \<sigma>\<^sub>n in \<T>(C,X)\<close>.
We define the sorted set of basic terms as follows.\<close>

fun Basic_Term :: "('f,'s) ssig \<Rightarrow> ('f,'s) ssig \<Rightarrow> ('v \<rightharpoonup> 's) \<Rightarrow> ('f,'v) term \<rightharpoonup> 's" ("\<T>\<^sub>B'(_,_,_')")
  where "\<T>\<^sub>B(C,D,X) (Var x) = None"
  | "\<T>\<^sub>B(C,D,X) (Fun f ss) = (case those (map \<T>(C,X) ss) of Some \<sigma>s \<Rightarrow> D (f,\<sigma>s) | _ \<Rightarrow> None)"

abbreviation ground_Basic_Term ("\<T>\<^sub>B'(_,_')") where
  "\<T>\<^sub>B(C,D) \<equiv> \<T>\<^sub>B(C,D,\<lambda>x. None) :: ('f,unit) term \<rightharpoonup> 's"

lemma Var_hastype_Basic:
  "Var x : \<sigma> in \<T>\<^sub>B(C,D,X) \<longleftrightarrow> False" by (simp add: hastype_def)

lemma Fun_hastype_Basic:
  "Fun f ss : \<tau> in \<T>\<^sub>B(C,D,X) \<longleftrightarrow> (\<exists>\<sigma>s. f : \<sigma>s \<rightarrow> \<tau> in D \<and> ss :\<^sub>l \<sigma>s in \<T>(C,X))"
  apply (unfold hastype_list_iff_those)
  by (auto simp: hastype_def fun_hastype_def split:option.split_asm)

lemma hastype_Basic:
  "s : \<tau> in \<T>\<^sub>B(C,D,X) \<longleftrightarrow> (\<exists>f ss \<sigma>s. s = Fun f ss \<and> f : \<sigma>s \<rightarrow> \<tau> in D \<and> ss :\<^sub>l \<sigma>s in \<T>(C,X))"
  by (cases s, auto simp: Var_hastype_Basic Fun_hastype_Basic)

lemma in_dom_Basic:
  "s \<in> dom \<T>\<^sub>B(C,D,X) \<longleftrightarrow> (\<exists>f ss \<sigma>s \<tau>. s = Fun f ss \<and> f : \<sigma>s \<rightarrow> \<tau> in D \<and> ss :\<^sub>l \<sigma>s in \<T>(C,X))"
  by (auto simp: in_dom_iff_ex_type hastype_Basic)

lemma hastype_BasicE:
  assumes "s : \<tau> in \<T>\<^sub>B(C,D,X)"
    and "\<And>f ss \<sigma>s. s = Fun f ss \<Longrightarrow> f : \<sigma>s \<rightarrow> \<tau> in D \<Longrightarrow> ss :\<^sub>l \<sigma>s in \<T>(C,X) \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: hastype_Basic)

lemma hastype_BasicI:
  "s = Fun f ss \<Longrightarrow> f : \<sigma>s \<rightarrow> \<tau> in D \<Longrightarrow> ss :\<^sub>l \<sigma>s in \<T>(C,X) \<Longrightarrow> s : \<tau> in \<T>\<^sub>B(C,D,X)"
  by (auto simp: hastype_Basic)

lemma Basic_mono:
  assumes D: "D \<subseteq>\<^sub>m D'" and C: "C \<subseteq>\<^sub>m C'" and X: "X \<subseteq>\<^sub>m X'"
  shows "\<T>\<^sub>B(C,D,X) \<subseteq>\<^sub>m \<T>\<^sub>B(C',D',X')"
proof (safe intro!: subssetI elim!: hastype_BasicE)
  fix f ss \<sigma>s \<tau> assume f: "f : \<sigma>s \<rightarrow> \<tau> in D" and ss: "ss :\<^sub>l \<sigma>s in \<T>(C,X)"
  from subssigD[OF D f] Term_mono[OF C X, THEN subsset_hastype_listD, OF ss]
  show "Fun f ss : \<tau> in \<T>\<^sub>B(C',D',X')"
    by (intro hastype_BasicI[OF refl])
qed

text \<open>Basic terms are terms of the joint signature, if the signatures are disjoint.\<close>

lemma Basic_Term:
  assumes disj: "dom C \<inter> dom D = {}"
  shows "\<T>\<^sub>B(C,D,X) \<subseteq>\<^sub>m \<T>(C++D,X)"
proof (intro subssetI)
  fix s \<sigma>
  assume s: "s : \<sigma> in \<T>\<^sub>B(C,D,X)"
  show "s : \<sigma> in \<T>(C++D,X)"
  proof (cases s)
    case (Var x1)
    with s show ?thesis by (auto simp: Var_hastype_Basic)
  next
    case sfss: (Fun f ss)
    with s obtain \<tau>s where ss: "ss :\<^sub>l \<tau>s in \<T>(C,X)" and f: "f : \<tau>s \<rightarrow> \<sigma> in D"
      by (auto simp: Fun_hastype_Basic)
    from disj have C: "C \<subseteq>\<^sub>m C++D" by (simp add: map_le_map_add_left)
    from Term_mono_left[OF C, THEN subssetD] ss
    have ssF: "ss :\<^sub>l \<tau>s in \<T>(C++D,X)" by (metis subsset_hastype_listD subssetI)
    have "D \<subseteq>\<^sub>m C++D" by auto
    from subssigD[OF this f] have fF: "f : \<tau>s \<rightarrow> \<sigma> in C++D".
    with ssF have "Fun f ss : \<sigma> in \<T>(C++D,X)" by (auto simp: Fun_hastype)
    then show ?thesis by (auto simp: sfss)
  qed
qed

text \<open>Basic terms are preserved under constructor substitution.\<close>

lemma subst_Basic_Term:
  assumes \<theta>: "\<theta> :\<^sub>s X \<rightarrow> \<T>(C,V)" and s: "s : \<tau> in \<T>\<^sub>B(C,D,X)"
  shows "s\<cdot>\<theta> : \<tau> in \<T>\<^sub>B(C,D,V)"
proof-
  from s[unfolded hastype_Basic]
  obtain f ss \<sigma>s where s: "s = Fun f ss" and f: "f : \<sigma>s \<rightarrow> \<tau> in D" and ss: "ss :\<^sub>l \<sigma>s in \<T>(C,X)"
    by (auto simp: hastype_Basic)
  from map_subst_hastype[OF \<theta> ss] f
  show ?thesis by (auto simp: hastype_Basic s)
qed

lemma in_dom_Basic_Term_imp_vars: "s \<in> dom \<T>\<^sub>B(C,D,V) \<Longrightarrow> x \<in> vars s \<Longrightarrow> x \<in> dom V"
  apply (elim in_dom_hastypeE)
  apply (cases s)
  by (auto simp: Fun_hastype_Basic list_all2_conv_all_nth in_set_conv_nth dest!: hastype_in_Term_imp_vars)

lemma in_dom_Basic_empty_subst_id:
  assumes "s \<in> dom \<T>\<^sub>B(C,D,\<emptyset>)"
  shows "s\<cdot>\<theta> = s"
  using assms
  by (auto elim!: in_dom_hastypeE hastype_BasicE simp: o_def map_subst_Term_empty_id)

lemma in_dom_Basic_empty_subst_subst:
  assumes "s \<in> dom \<T>\<^sub>B(C,D,\<emptyset>)"
  shows "s\<cdot>\<theta>\<cdot>\<tau> = s\<cdot>undefined"
  using assms
  by (auto elim!: in_dom_hastypeE hastype_BasicE simp: o_def map_subst_subst_Term_empty)

end