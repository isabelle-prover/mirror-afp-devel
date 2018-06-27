(* Author: Alexander Maletzky *)

theory More_MPoly_Type_Class
  imports Polynomials.MPoly_Type_Class_Ordered General
begin

text \<open>Some further general properties of (ordered) multivariate polynomials needed for Gr\"obner
  bases. This theory is an extension of @{theory Polynomials.MPoly_Type_Class_Ordered}.\<close>
  
section \<open>Further Properties of Ordered Polynomials\<close>
  
context ordered_term
begin

subsection \<open>Monicity\<close>
  
definition monic :: "('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)" where
  "monic p = monom_mult (1 / lc p) 0 p"

definition monic_set :: "('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) set" where
  "monic_set = image monic"
  
definition is_monic_set :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool" where
  "is_monic_set B \<equiv> (\<forall>b\<in>B. b \<noteq> 0 \<longrightarrow> lc b = 1)"

lemma lookup_monic: "lookup (monic p) v = (lookup p v) / lc p"
proof -
  have "lookup (monic p) (0 \<oplus> v) = (1 / lc p) * (lookup p v)" unfolding monic_def
    by (rule lookup_monom_mult_plus)
  thus ?thesis by (simp add: term_simps)
qed

lemma lookup_monic_lt:
  assumes "p \<noteq> 0"
  shows "lookup (monic p) (lt p) = 1"
  unfolding monic_def
proof -
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  hence "1 / lc p \<noteq> 0" by simp
  let ?q = "monom_mult (1 / lc p) 0 p"
  have "lookup ?q (0 \<oplus> lt p) = (1 / lc p) * (lookup p (lt p))" by (rule lookup_monom_mult_plus)
  also have "... = (1 / lc p) * lc p" unfolding lc_def ..
  also have "... = 1" using \<open>lc p \<noteq> 0\<close> by simp
  finally have "lookup ?q (0 \<oplus> lt p) = 1" .
  thus "lookup ?q (lt p) = 1" by (simp add: term_simps)
qed
  
lemma monic_0 [simp]: "monic 0 = 0"
  unfolding monic_def by (rule monom_mult_zero_right)

lemma monic_0_iff: "(monic p = 0) \<longleftrightarrow> (p = 0)"
proof
  assume "monic p = 0"
  show "p = 0"
  proof (rule ccontr)
    assume "p \<noteq> 0"
    hence "lookup (monic p) (lt p) = 1" by (rule lookup_monic_lt)
    with \<open>monic p = 0\<close> have "lookup 0 (lt p) = (1::'b)" by simp
    thus False by simp
  qed
next
  assume p0: "p = 0"
  show "monic p = 0" unfolding p0 by (fact monic_0)
qed
  
lemma keys_monic [simp]: "keys (monic p) = keys p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True monic_0 ..
next
  case False
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  thm in_keys_iff
  show ?thesis
    by (rule set_eqI, simp add: in_keys_iff lookup_monic \<open>lc p \<noteq> 0\<close> del: lookup_not_eq_zero_eq_in_keys)
qed

lemma lt_monic [simp]: "lt (monic p) = lt p"
proof (cases "p = 0")
  case True
  show ?thesis unfolding True monic_0 ..
next
  case False
  have "lt (monom_mult (1 / lc p) 0 p) = 0 \<oplus> lt p"
  proof (rule lt_monom_mult)
    from False have "lc p \<noteq> 0" by (rule lc_not_0)
    thus "1 / lc p \<noteq> 0" by simp
  qed fact
  thus ?thesis by (simp add: monic_def term_simps)
qed

lemma lc_monic:
  assumes "p \<noteq> 0"
  shows "lc (monic p) = 1"
  using assms by (simp add: lc_def lookup_monic_lt)

lemma mult_lc_monic:
  assumes "p \<noteq> 0"
  shows "monom_mult (lc p) 0 (monic p) = p" (is "?q = p")
proof (rule poly_mapping_eqI)
  fix v
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  have "lookup ?q (0 \<oplus> v) = (lc p) * (lookup (monic p) v)" by (rule lookup_monom_mult_plus)
  also have "... = (lc p) * ((lookup p v) / lc p)" by (simp add: lookup_monic)
  also have "... = lookup p v" using \<open>lc p \<noteq> 0\<close> by simp
  finally show "lookup ?q v = lookup p v" by (simp add: term_simps)
qed

lemma is_monic_setI:
  assumes "\<And>b. b \<in> B \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> lc b = 1"
  shows "is_monic_set B"
  unfolding is_monic_set_def using assms by auto

lemma is_monic_setD:
  assumes "is_monic_set B" and "b \<in> B" and "b \<noteq> 0"
  shows "lc b = 1"
  using assms unfolding is_monic_set_def by auto

lemma Keys_monic_set [simp]: "Keys (monic_set A) = Keys A"
  by (simp add: Keys_def monic_set_def)
    
lemma monic_set_is_monic_set: "is_monic_set (monic_set A)"
proof (rule is_monic_setI)
  fix p
  assume pin: "p \<in> monic_set A" and "p \<noteq> 0"
  from pin obtain p' where p_def: "p = monic p'" and "p' \<in> A" unfolding monic_set_def ..
  from \<open>p \<noteq> 0\<close> have "p' \<noteq> 0" unfolding p_def monic_0_iff .
  thus "lc p = 1" unfolding p_def by (rule lc_monic)
qed
  
lemma monic_set_pmdl [simp]: "pmdl (monic_set B) = pmdl B"
proof
  show "pmdl (monic_set B) \<subseteq> pmdl B"
  proof
    fix p
    assume "p \<in> pmdl (monic_set B)"
    thus "p \<in> pmdl B"
    proof (induct p rule: pmdl_induct)
      case base: module_0
      show ?case by (fact pmdl.module_0)
    next
      case ind: (module_plus a b c t)
      from ind(3) obtain b' where b_def: "b = monic b'" and "b' \<in> B" unfolding monic_set_def ..
      have eq: "b = monom_mult (1 / lc b') 0 b'" by (simp only: b_def monic_def)
      show ?case unfolding eq monom_mult_assoc
        by (rule pmdl.module_closed_plus, fact, rule monom_mult_in_pmdl, fact)
    qed
  qed
next
  show "pmdl B \<subseteq> pmdl (monic_set B)"
  proof
    fix p
    assume "p \<in> pmdl B"
    thus "p \<in> pmdl (monic_set B)"
    proof (induct p rule: pmdl_induct)
      case base: module_0
      show ?case by (fact pmdl.module_0)
    next
      case ind: (module_plus a b c t)
      show ?case
      proof (cases "b = 0")
        case True
        from ind(2) show ?thesis by (simp add: True)
      next
        case False
        let ?b = "monic b"
        from ind(3) have "?b \<in> monic_set B" unfolding monic_set_def by (rule imageI)
        have "a + monom_mult c t (monom_mult (lc b) 0 ?b) \<in> pmdl (monic_set B)"
          unfolding monom_mult_assoc
          by (rule pmdl.module_closed_plus, fact, rule monom_mult_in_pmdl, fact)
        thus ?thesis unfolding mult_lc_monic[OF False] .
      qed
    qed
  qed
qed

end (* ordered_term *)

end (* theory *)
