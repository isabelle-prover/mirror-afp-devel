(* Title:      Containers/Extend_Partial_Order.thy
   Author:     Andreas Lochbihler, KIT *)

theory Extend_Partial_Order
imports Main
begin

section {* Every partial order can be extended to a total order *}

lemma ChainsD: "\<lbrakk> x \<in> C; C \<in> Chains r; y \<in> C \<rbrakk> \<Longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
by(simp add: Chains_def)

lemma Chains_Field: "\<lbrakk> C \<in> Chains r; x \<in> C \<rbrakk> \<Longrightarrow> x \<in> Field r"
by(auto simp add: Chains_def Field_def)

lemma total_onD:
  "\<lbrakk> total_on A r; x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> (x, y) \<in> r \<or> x = y \<or> (y, x) \<in> r"
unfolding total_on_def by blast

lemma linear_order_imp_linorder: "linear_order {(A, B). leq A B} \<Longrightarrow> class.linorder leq (\<lambda>x y. leq x y \<and> \<not> leq y x)"
by(unfold_locales)(auto 4 4 simp add: linear_order_on_def partial_order_on_def preorder_on_def dest: refl_onD antisymD transD total_onD)

lemma (in linorder) linear_order: "linear_order {(A, B). A \<le> B}"
by(auto simp add: linear_order_on_def partial_order_on_def preorder_on_def total_on_def intro: refl_onI antisymI transI)


definition order_consistent :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
where "order_consistent r s \<longleftrightarrow> (\<forall>a a'. (a, a') \<in> r \<longrightarrow> (a', a) \<in> s \<longrightarrow> a = a')"

lemma order_consistent_sym:
  "order_consistent r s \<Longrightarrow> order_consistent s r"
by(auto simp add: order_consistent_def)

lemma antisym_order_consistent_self:
  "antisym r \<Longrightarrow> order_consistent r r"
by(auto simp add: order_consistent_def dest: antisymD)


lemma refl_on_trancl:
  assumes "refl_on A r"
  shows "refl_on A (r^+)"
proof(rule refl_onI, safe del: conjI)
  fix a b
  assume "(a, b) \<in> r^+"
  thus "a \<in> A \<and> b \<in> A"
    by induct(blast intro: refl_onD1[OF assms] refl_onD2[OF assms])+
qed(blast dest: refl_onD[OF assms])

lemma total_on_refl_on_consistent_into:
  assumes r: "total_on A r" "refl_on A r"
  and consist: "order_consistent r s"
  and x: "x \<in> A" and y: "y \<in> A" and s: "(x, y) \<in> s"
  shows "(x, y) \<in> r"
proof(cases "x = y")
  case False
  with r x y have "(x, y) \<in> r \<or> (y, x) \<in> r" unfolding total_on_def by blast
  thus ?thesis
  proof
    assume "(y, x) \<in> r"
    with s consist have "x = y" unfolding order_consistent_def by blast
    with False show ?thesis by contradiction
  qed
qed(blast intro: refl_onD r x y)

lemma porder_linorder_tranclpE [consumes 5, case_names base step]:
  assumes r: "partial_order_on A r"
  and s: "linear_order_on B s"
  and consist: "order_consistent r s"
  and B_subset_A: "B \<subseteq> A"
  and trancl: "(x, y) \<in> (r \<union> s)^+"
  obtains "(x, y) \<in> r"
        | u v where "(x, u) \<in> r" "(u, v) \<in> s" "(v, y) \<in> r"
proof(atomize_elim)
  from r have "refl_on A r" "trans r" by(simp_all add: partial_order_on_def preorder_on_def)
  from s have "refl_on B s" "total_on B s" "trans s"
    by(simp_all add: partial_order_on_def preorder_on_def linear_order_on_def)

  from trancl show "(x, y) \<in> r \<or> (\<exists>u v. (x, u) \<in> r \<and> (u, v) \<in> s \<and> (v, y) \<in> r)"
  proof(induction)
    case (base y)
    thus ?case
    proof
      assume "(x, y) \<in> s"
      with `refl_on B s` have "x \<in> B" "y \<in> B"
        by(blast dest: refl_onD1 refl_onD2)+
      with B_subset_A have "x \<in> A" "y \<in> A" by blast+
      hence "(x, x) \<in> r" "(y, y) \<in> r"
        using `refl_on A r` by(blast intro: refl_onD)+
      with `(x, y) \<in> s` show ?thesis by blast
    qed(simp)
  next
    case (step y z)
    from `(y, z) \<in> r \<union> s` show ?case
    proof
      assume "(y, z) \<in> s"
      with `refl_on B s` have "y \<in> B" "z \<in> B"
        by(blast dest: refl_onD2 refl_onD1)+
      from step.IH show ?thesis
      proof
        assume "(x, y) \<in> r"
        moreover from `z \<in> B` B_subset_A `refl_on A r` 
        have "(z, z) \<in> r" by(blast dest: refl_onD)
        ultimately show ?thesis using `(y, z) \<in> s` by blast
      next
        assume "\<exists>u v. (x, u) \<in> r \<and> (u, v) \<in> s \<and> (v, y) \<in> r"
        then obtain u v where "(x, u) \<in> r" "(u, v) \<in> s" "(v, y) \<in> r" by blast
        from `refl_on B s` `(u, v) \<in> s` have "v \<in> B" by(rule refl_onD2)
        with `total_on B s` `refl_on B s` order_consistent_sym[OF consist]
        have "(v, y) \<in> s" using `y \<in> B` `(v, y) \<in> r`
          by(rule total_on_refl_on_consistent_into)
        with `trans s` have "(v, z) \<in> s" using `(y, z) \<in> s` by(rule transD)
        with `trans s` `(u, v) \<in> s` have "(u, z) \<in> s" by(rule transD)
        moreover from `z \<in> B` B_subset_A have "z \<in> A" ..
        with `refl_on A r` have "(z, z) \<in> r" by(rule refl_onD)
        ultimately show ?thesis using `(x, u) \<in> r` by blast
      qed
    next
      assume "(y, z) \<in> r"
      with step.IH show ?thesis
        by(blast intro: transD[OF `trans r`])
    qed
  qed
qed

lemma porder_on_consistent_linorder_on_trancl_antisym:
  assumes r: "partial_order_on A r"
  and s: "linear_order_on B s"
  and consist: "order_consistent r s"
  and B_subset_A: "B \<subseteq> A"
  shows "antisym ((r \<union> s)^+)"
proof(rule antisymI)
  fix x y
  let ?rs = "(r \<union> s)^+"
  assume "(x, y) \<in> ?rs" "(y, x) \<in> ?rs"
  from r have "antisym r" "trans r" by(simp_all add: partial_order_on_def preorder_on_def)
  from s have "total_on B s" "refl_on B s" "trans s" "antisym s"
    by(simp_all add: partial_order_on_def preorder_on_def linear_order_on_def)

  from r s consist B_subset_A `(x, y) \<in> ?rs`
  show "x = y"
  proof(cases rule: porder_linorder_tranclpE)
    case base
    from r s consist B_subset_A `(y, x) \<in> ?rs`
    show ?thesis
    proof(cases rule: porder_linorder_tranclpE)
      case base
      with `antisym r` `(x, y) \<in> r` show ?thesis by(rule antisymD)
    next
      case (step u v)
      from `(v, x) \<in> r` `(x, y) \<in> r` `(y, u) \<in> r` have "(v, u) \<in> r"
        by(blast intro: transD[OF `trans r`])
      with consist have "v = u" using `(u, v) \<in> s` 
        by(simp add: order_consistent_def) 
      with `(y, u) \<in> r` `(v, x) \<in> r` have "(y, x) \<in> r"
        by(blast intro: transD[OF `trans r`])
      with `antisym r` `(x, y) \<in> r` show ?thesis by(rule antisymD)
    qed
  next
    case (step u v)
    from r s consist B_subset_A `(y, x) \<in> ?rs`
    show ?thesis
    proof(cases rule: porder_linorder_tranclpE)
      case base
      from `(v, y) \<in> r` `(y, x) \<in> r` `(x, u) \<in> r` have "(v, u) \<in> r"
        by(blast intro: transD[OF `trans r`])
      with consist `(u, v) \<in> s`
      have "u = v" by(auto simp add: order_consistent_def)
      with `(v, y) \<in> r` `(x, u) \<in> r` have "(x, y) \<in> r"
        by(blast intro: transD[OF `trans r`])
      with `antisym r` show ?thesis using `(y, x) \<in> r` by(rule antisymD)
    next
      case (step u' v')
      note r_into_s = total_on_refl_on_consistent_into[OF `total_on B s` `refl_on B s` order_consistent_sym[OF consist]]
      from `refl_on B s` `(u, v) \<in> s` `(u', v') \<in> s`
      have "u \<in> B" "v \<in> B" "u' \<in> B" "v' \<in> B" by(blast dest: refl_onD1 refl_onD2)+
      from `trans r` `(v', x) \<in> r` `(x, u) \<in> r` have "(v', u) \<in> r" by(rule transD)
      with `v' \<in> B` `u \<in> B` have "(v', u) \<in> s" by(rule r_into_s)
      also note `(u, v) \<in> s` also (transD[OF `trans s`])
      from `trans r` `(v, y) \<in> r` `(y, u') \<in> r` have "(v, u') \<in> r" by(rule transD)
      with `v \<in> B` `u' \<in> B` have "(v, u') \<in> s" by(rule r_into_s)
      finally (transD[OF `trans s`])
      have "v' = u'" using `(u', v') \<in> s` by(rule antisymD[OF `antisym s`])
      moreover with `(v, u') \<in> s` `(v', u) \<in> s` have "(v, u) \<in> s"
        by(blast intro: transD[OF `trans s`])
      with `antisym s` `(u, v) \<in> s` have "u = v" by(rule antisymD)
      ultimately have "(x, y) \<in> r" "(y, x) \<in> r"
        using `(x, u) \<in> r` `(v, y) \<in> r` `(y, u') \<in> r` `(v', x) \<in> r`
        by(blast intro: transD[OF `trans r`])+
      with `antisym r` show ?thesis by(rule antisymD)
    qed
  qed
qed

lemma porder_on_linorder_on_tranclp_porder_onI:
  assumes r: "partial_order_on A r"
  and s: "linear_order_on B s" 
  and consist: "order_consistent r s"
  and subset: "B \<subseteq> A"
  shows "partial_order_on A ((r \<union> s)^+)"
  unfolding partial_order_on_def preorder_on_def
proof(intro conjI)
  let ?rs = "r \<union> s"
  from r have "refl_on A r" by(simp add: partial_order_on_def preorder_on_def)
  moreover from s have "refl_on B s"
    by(simp add: linear_order_on_def partial_order_on_def preorder_on_def)
  ultimately have "refl_on (A \<union> B) ?rs" by(rule refl_on_Un)
  also from subset have "A \<union> B = A" by blast
  finally show "refl_on A (?rs^+)" by(rule refl_on_trancl)

  show "trans (?rs^+)" by(rule trans_trancl)

  from r s consist subset show "antisym (?rs^+)"
    by(rule porder_on_consistent_linorder_on_trancl_antisym)
qed

lemma porder_extend_to_linorder:
  assumes r: "partial_order_on A r"
  obtains s where "linear_order_on A s" "order_consistent r s"
proof(atomize_elim)
  def S \<equiv> "{s. partial_order_on A s \<and> r \<subseteq> s}"
  from r have r_in_S: "r \<in> S" unfolding S_def by auto

  have "\<exists>y\<in>S. \<forall>x\<in>S. y \<subseteq> x \<longrightarrow> x = y"
  proof(rule Zorn_Lemma2[rule_format])
    fix c
    assume "c \<in> chains S"
    hence "c \<subseteq> S" by(rule chainsD2)

    show "\<exists>y\<in>S. \<forall>x\<in>c. x \<subseteq> y"
    proof(cases "c = {}")
      case True
      with r_in_S show ?thesis by blast
    next
      case False
      then obtain s where "s \<in> c" by blast
      hence s: "partial_order_on A s"
        and r_in_s: "r \<subseteq> s"
        using `c \<subseteq> S` unfolding S_def by blast+

      have "partial_order_on A (\<Union>c)"
        unfolding partial_order_on_def preorder_on_def
      proof(intro conjI)
        show "refl_on A (\<Union>c)"
        proof(rule refl_onI[OF subsetI])
          fix x
          assume "x \<in> \<Union>c"
          then obtain X where "X \<in> c" and "x \<in> X" by blast
          from `X \<in> c` `c \<subseteq> S` have "X \<in> S" ..
          hence "partial_order_on A X" unfolding S_def by simp
          with `x \<in> X` show "x \<in> A \<times> A"
            by(cases x)(auto simp add: partial_order_on_def preorder_on_def dest: refl_onD1 refl_onD2)
        next
          fix x
          assume "x \<in> A"
          with s have "(x, x) \<in> s" unfolding partial_order_on_def preorder_on_def
            by(blast dest: refl_onD)
          with `s \<in> c` show "(x, x) \<in> \<Union>c" by(rule UnionI)
        qed

        show "antisym (\<Union>c)"
        proof(rule antisymI)
          fix x y
          assume "(x, y) \<in> \<Union>c" "(y, x) \<in> \<Union>c"
          then obtain X Y where "X \<in> c" "Y \<in> c" "(x, y) \<in> X" "(y, x) \<in> Y" by blast
          from `X \<in> c` `Y \<in> c` `c \<subseteq> S` have "antisym X" "antisym Y"
            unfolding S_def by(auto simp add: partial_order_on_def)
          moreover from `c \<in> chains S` `X \<in> c` `Y \<in> c` 
          have "X \<subseteq> Y \<or> Y \<subseteq> X" by(rule chainsD)
          ultimately show "x = y" using `(x, y) \<in> X` `(y, x) \<in> Y` 
            by(auto dest: antisymD)
        qed

        show "trans (\<Union>c)"
        proof(rule transI)
          fix x y z
          assume "(x, y) \<in> \<Union>c" "(y, z) \<in> \<Union>c"
          then obtain X Y where "X \<in> c" "Y \<in> c" "(x, y) \<in> X" "(y, z) \<in> Y" by blast
          from `X \<in> c` `Y \<in> c` `c \<subseteq> S` have "trans X" "trans Y"
            unfolding S_def by(auto simp add: partial_order_on_def preorder_on_def)
          from `c \<in> chains S` `X \<in> c` `Y \<in> c` 
          have "X \<subseteq> Y \<or> Y \<subseteq> X" by(rule chainsD)
          thus "(x, z) \<in> \<Union>c"
          proof
            assume "X \<subseteq> Y"
            with `trans Y` `(x, y) \<in> X` `(y, z) \<in> Y`
            have "(x, z) \<in> Y" by(blast dest: transD)
            with `Y \<in> c` show ?thesis by(rule UnionI)
          next
            assume "Y \<subseteq> X"
            with `trans X` `(x, y) \<in> X` `(y, z) \<in> Y`
            have "(x, z) \<in> X" by(blast dest: transD)
            with `X \<in> c` show ?thesis by(rule UnionI)
          qed
        qed
      qed
      moreover
      have "r \<subseteq> \<Union>c" using r_in_s `s \<in> c` by blast
      ultimately have "\<Union>c \<in> S" unfolding S_def by simp
      thus ?thesis by blast
    qed
  qed
  then obtain s where "s \<in> S" and y_max: "\<And>t. \<lbrakk> t \<in> S; s \<subseteq> t \<rbrakk> \<Longrightarrow> s = t" by blast

  have "partial_order_on A s" using `s \<in> S`
    unfolding S_def by simp
  moreover
  have r_in_s: "r \<subseteq> s" using `s \<in> S` unfolding S_def by blast

  have "total_on A s"
    unfolding total_on_def
  proof(intro strip)
    fix x y
    assume "x \<in> A" "y \<in> A" "x \<noteq> y" 
    show "(x, y) \<in> s \<or> (y, x) \<in> s"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence xy: "(x, y) \<notin> s" "(y, x) \<notin> s" by simp_all

      def s' \<equiv> "{(a, b). a = x \<and> (b = y \<or> b = x) \<or> a = y \<and> b = y}"
      let ?s' = "(s \<union> s')^+"
      note `partial_order_on A s`
      moreover have "linear_order_on {x, y} s'" unfolding s'_def
        by(auto simp add: linear_order_on_def partial_order_on_def preorder_on_def total_on_def intro: refl_onI transI antisymI)
      moreover have "order_consistent s s'"
        unfolding s'_def using xy unfolding order_consistent_def by blast
      moreover have "{x, y} \<subseteq> A" using `x \<in> A` `y \<in> A` by blast
      ultimately have "partial_order_on A ?s'"
        by(rule porder_on_linorder_on_tranclp_porder_onI)
      moreover have "r \<subseteq> ?s'" using r_in_s by auto
      ultimately have "?s' \<in> S" unfolding S_def by simp
      moreover have "s \<subseteq> ?s'" by auto
      ultimately have "s = ?s'" by(rule y_max)
      moreover have "(x, y) \<in> ?s'" by(auto simp add: s'_def)
      ultimately show False using `(x, y) \<notin> s` by simp
    qed
  qed
  ultimately have "linear_order_on A s" by(simp add: linear_order_on_def)
  moreover have "order_consistent r s" unfolding order_consistent_def
  proof(intro strip)
    fix a a'
    assume "(a, a') \<in> r" "(a', a) \<in> s"
    from `(a, a') \<in> r` have "(a, a') \<in> s" using r_in_s by blast
    with `partial_order_on A s` `(a', a) \<in> s`
    show "a = a'" unfolding partial_order_on_def by(blast dest: antisymD)
  qed
  ultimately show "\<exists>s. linear_order_on A s \<and> order_consistent r s" by blast
qed

end