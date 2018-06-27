(* Author: Alexander Maletzky *)

section \<open>Auto-reducing Lists of Polynomials\<close>

theory Auto_Reduction
  imports Reduction More_MPoly_Type_Class
begin

subsection \<open>Reduction and Monic Sets\<close>

context ordered_term
begin

lemma is_red_monic: "is_red B (monic p) \<longleftrightarrow> is_red B p"
  unfolding is_red_adds_iff keys_monic ..

lemma red_monic_set [simp]: "red (monic_set B) = red B"
proof (rule, rule)
  fix p q
  show "red (monic_set B) p q \<longleftrightarrow> red B p q"
  proof
    assume "red (monic_set B) p q"
    then obtain f t where "f \<in> monic_set B" and *: "red_single p q f t" by (rule red_setE)
    from this(1) obtain g where "g \<in> B" and "f = monic g" unfolding monic_set_def ..
    from * have "f \<noteq> 0" by (simp add: red_single_def)
    hence "g \<noteq> 0" by (simp add: monic_0_iff \<open>f = monic g\<close>)
    hence "lc g \<noteq> 0" by (rule lc_not_0)
    have eq: "monom_mult (lc g) 0 f = g" by (simp add: \<open>f = monic g\<close> mult_lc_monic[OF \<open>g \<noteq> 0\<close>])
    from \<open>g \<in> B\<close> show "red B p q"
    proof (rule red_setI)
      from * \<open>lc g \<noteq> 0\<close> have "red_single p q (monom_mult (lc g) 0 f) t" by (rule red_single_mult_const)
      thus "red_single p q g t" by (simp only: eq)
    qed
  next
    assume "red B p q"
    then obtain f t where "f \<in> B" and *: "red_single p q f t" by (rule red_setE)
    from * have "f \<noteq> 0" by (simp add: red_single_def)
    hence "lc f \<noteq> 0" by (rule lc_not_0)
    hence "1 / lc f \<noteq> 0" by simp
    from \<open>f \<in> B\<close> have "monic f \<in> monic_set B" by (simp add: monic_set_def)
    thus "red (monic_set B) p q"
    proof (rule red_setI)
      from * \<open>1 / lc f \<noteq> 0\<close> show "red_single p q (monic f) t" unfolding monic_def
        by (rule red_single_mult_const)
    qed
  qed
qed

lemma is_red_monic_set [simp]: "is_red (monic_set B) p \<longleftrightarrow> is_red B p"
  by (simp add: is_red_def)

subsection \<open>Minimal Bases and Auto-reduced Bases\<close>

definition is_auto_reduced :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool" where
  "is_auto_reduced B \<equiv> (\<forall>b\<in>B. \<not> is_red (B - {b}) b)"

definition is_minimal_basis :: "('t \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool" where
  "is_minimal_basis B \<longleftrightarrow> (0 \<notin> B \<and> (\<forall>p q. p \<in> B \<longrightarrow> q \<in> B \<longrightarrow> p \<noteq> q \<longrightarrow> \<not> lt p adds\<^sub>t lt q))"

lemma is_auto_reducedD:
  assumes "is_auto_reduced B" and "b \<in> B"
  shows "\<not> is_red (B - {b}) b"
  using assms unfolding is_auto_reduced_def by auto

text \<open>The converse of the following lemma is only true if @{term B} is minimal!\<close>
lemma monic_set_is_auto_reduced:
  assumes "is_auto_reduced B"
  shows "is_auto_reduced (monic_set B)"
  unfolding is_auto_reduced_def
proof
  fix b
  assume "b \<in> monic_set B"
  then obtain b' where b_def: "b = monic b'" and "b' \<in> B" unfolding monic_set_def ..
  from assms \<open>b' \<in> B\<close> have nred: "\<not> is_red (B - {b'}) b'" by (rule is_auto_reducedD)
  show "\<not> is_red ((monic_set B) - {b}) b"
  proof
    assume red: "is_red ((monic_set B) - {b}) b"
    have "(monic_set B) - {b} \<subseteq> monic_set (B - {b'})"
      unfolding monic_set_def remove_def b_def by auto
    with red have "is_red (monic_set (B - {b'})) b" by (rule is_red_subset)
    hence "is_red (B - {b'}) b'" unfolding b_def is_red_monic_set is_red_monic .
    with nred show False ..
  qed
qed
  
lemma is_minimal_basisI:
  assumes "\<And>p. p \<in> B \<Longrightarrow> p \<noteq> 0" and "\<And>p q. p \<in> B \<Longrightarrow> q \<in> B \<Longrightarrow> p \<noteq> q \<Longrightarrow> \<not> lt p adds\<^sub>t lt q"
  shows "is_minimal_basis B"
  unfolding is_minimal_basis_def using assms by auto
    
lemma is_minimal_basisD1:
  assumes "is_minimal_basis B" and "p \<in> B"
  shows "p \<noteq> 0"
  using assms unfolding is_minimal_basis_def by auto
    
lemma is_minimal_basisD2:
  assumes "is_minimal_basis B" and "p \<in> B" and "q \<in> B" and "p \<noteq> q"
  shows "\<not> lt p adds\<^sub>t lt q"
  using assms unfolding is_minimal_basis_def by auto
  
lemma is_minimal_basisD3:
  assumes "is_minimal_basis B" and "p \<in> B" and "q \<in> B" and "p \<noteq> q"
  shows "\<not> lt q adds\<^sub>t lt p"
  using assms unfolding is_minimal_basis_def by auto
    
lemma is_minimal_basis_subset:
  assumes "is_minimal_basis B" and "A \<subseteq> B"
  shows "is_minimal_basis A"
proof (intro is_minimal_basisI)
  fix p
  assume "p \<in> A"
  with \<open>A \<subseteq> B\<close> have "p \<in> B" ..
  with \<open>is_minimal_basis B\<close> show "p \<noteq> 0" by (rule is_minimal_basisD1)
next
  fix p q
  assume "p \<in> A" and "q \<in> A" and "p \<noteq> q"
  from \<open>p \<in> A\<close> and \<open>q \<in> A\<close> have "p \<in> B" and "q \<in> B" using \<open>A \<subseteq> B\<close> by auto
  from \<open>is_minimal_basis B\<close> this \<open>p \<noteq> q\<close> show " \<not> lt p adds\<^sub>t lt q" by (rule is_minimal_basisD2)
qed
  
lemma nadds_red:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and red: "red B p r"
  shows "r \<noteq> 0 \<and> lt r = lt p"
proof -
  from red obtain q t where "q \<in> B" and rs: "red_single p r q t" by (rule red_setE)
  from rs have "q \<noteq> 0" and "lookup p (t \<oplus> lt q) \<noteq> 0"
    and r_def: "r = p - monom_mult (lookup p (t \<oplus> lt q) / lc q) t q" unfolding red_single_def by simp_all
  have "t \<oplus> lt q \<preceq>\<^sub>t lt p" by (rule lt_max, fact)
  moreover have "t \<oplus> lt q \<noteq> lt p"
  proof
    assume "t \<oplus> lt q = lt p"
    hence "lt q adds\<^sub>t lt p" by (metis adds_term_triv) 
    with nadds[OF \<open>q \<in> B\<close>] show False ..
  qed
  ultimately have "t \<oplus> lt q \<prec>\<^sub>t lt p" by simp
  let ?m = "monom_mult (lookup p (t \<oplus> lt q) / lc q) t q"
  from \<open>lookup p (t \<oplus> lt q) \<noteq> 0\<close> lc_not_0[OF \<open>q \<noteq> 0\<close>] have c0: "lookup p (t \<oplus> lt q) / lc q \<noteq> 0" by simp
  from \<open>q \<noteq> 0\<close> c0 have "?m \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  have "lt (-?m) = lt ?m" by (fact lt_uminus)
  also have lt1: "lt ?m = t \<oplus> lt q" by (rule lt_monom_mult, fact+)
  finally have lt2: "lt (-?m) = t \<oplus> lt q" .
  
  show ?thesis
  proof
    show "r \<noteq> 0"
    proof
      assume "r = 0"
      hence "p = ?m" unfolding r_def by simp
      with lt1 \<open>t \<oplus> lt q \<noteq> lt p\<close> show False by simp
    qed
  next
    have "lt (-?m + p) = lt p"
    proof (rule lt_plus_eqI)
      show "lt (-?m) \<prec>\<^sub>t lt p" unfolding lt2 by fact
    qed
    thus "lt r = lt p" unfolding r_def by simp
  qed
qed
    
lemma nadds_red_nonzero:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and "red B p r"
  shows "r \<noteq> 0"
  using nadds_red[OF assms] by simp
    
lemma nadds_red_lt:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and "red B p r"
  shows "lt r = lt p"
  using nadds_red[OF assms] by simp
  
lemma nadds_red_rtrancl_lt:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and rtrancl: "(red B)\<^sup>*\<^sup>* p r"
  shows "lt r = lt p"
  using rtrancl
proof (induct rule: rtranclp_induct)
  case base
  show ?case ..
next
  case (step y z)
  have "lt z = lt y"
  proof (rule nadds_red_lt)
    fix q
    assume "q \<in> B"
    thus "\<not> lt q adds\<^sub>t lt y" unfolding \<open>lt y = lt p\<close> by (rule nadds)
  qed fact
  with \<open>lt y = lt p\<close> show ?case by simp
qed
  
lemma nadds_red_rtrancl_nonzero:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and "p \<noteq> 0" and rtrancl: "(red B)\<^sup>*\<^sup>* p r"
  shows "r \<noteq> 0"
  using rtrancl
proof (induct rule: rtranclp_induct)
  case base
  show ?case by fact
next
  case (step y z)
  from nadds \<open>(red B)\<^sup>*\<^sup>* p y\<close> have "lt y = lt p" by (rule nadds_red_rtrancl_lt)
  show "z \<noteq> 0"
  proof (rule nadds_red_nonzero)
    fix q
    assume "q \<in> B"
    thus "\<not> lt q adds\<^sub>t lt y" unfolding \<open>lt y = lt p\<close> by (rule nadds)
  qed fact
qed
  
lemma minimal_basis_red_rtrancl_nonzero:
  assumes "is_minimal_basis B" and "p \<in> B" and "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "r \<noteq> 0"
proof (rule nadds_red_rtrancl_nonzero)
  fix q
  assume "q \<in> (B - {p})"
  hence "q \<in> B" and "q \<noteq> p" by auto
  show "\<not> lt q adds\<^sub>t lt p" by (rule is_minimal_basisD2, fact+)
next
  show "p \<noteq> 0" by (rule is_minimal_basisD1, fact+)
qed fact

lemma minimal_basis_red_rtrancl_lt:
  assumes "is_minimal_basis B" and "p \<in> B" and "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "lt r = lt p"
proof (rule nadds_red_rtrancl_lt)
  fix q
  assume "q \<in> (B - {p})"
  hence "q \<in> B" and "q \<noteq> p" by auto
  show "\<not> lt q adds\<^sub>t lt p" by (rule is_minimal_basisD2, fact+)
qed fact
  
lemma is_minimal_basis_replace:
  assumes major: "is_minimal_basis B" and "p \<in> B" and red: "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "is_minimal_basis (insert r (B - {p}))"
proof (rule is_minimal_basisI)
  fix q
  assume "q \<in> insert r (B - {p})"
  hence "q = r \<or> q \<in> B \<and> q \<noteq> p" by simp
  thus "q \<noteq> 0"
  proof
    assume "q = r"
    from assms show ?thesis unfolding \<open>q = r\<close> by (rule minimal_basis_red_rtrancl_nonzero)
  next
    assume "q \<in> B \<and> q \<noteq> p"
    hence "q \<in> B" ..
    with major show ?thesis by (rule is_minimal_basisD1)
  qed
next
  fix a b
  assume "a \<in> insert r (B - {p})" and "b \<in> insert r (B - {p})" and "a \<noteq> b"
  from assms have ltr: "lt r = lt p" by (rule minimal_basis_red_rtrancl_lt)
  from \<open>b \<in> insert r (B - {p})\<close> have b: "b = r \<or> b \<in> B \<and> b \<noteq> p" by simp
  from \<open>a \<in> insert r (B - {p})\<close> have "a = r \<or> a \<in> B \<and> a \<noteq> p" by simp
  thus "\<not> lt a adds\<^sub>t lt b"
  proof
    assume "a = r"
    hence lta: "lt a = lt p" using ltr by simp
    from b show ?thesis
    proof
      assume "b = r"
      with \<open>a \<noteq> b\<close> show ?thesis unfolding \<open>a = r\<close> by simp
    next
      assume "b \<in> B \<and> b \<noteq> p"
      hence "b \<in> B" and "p \<noteq> b" by auto
      with major \<open>p \<in> B\<close> have "\<not> lt p adds\<^sub>t lt b" by (rule is_minimal_basisD2)
      thus ?thesis unfolding lta .
    qed
  next
    assume "a \<in> B \<and> a \<noteq> p"
    hence "a \<in> B" and "a \<noteq> p" by simp_all
    from b show ?thesis
    proof
      assume "b = r"
      from major \<open>a \<in> B\<close> \<open>p \<in> B\<close> \<open>a \<noteq> p\<close> have "\<not> lt a adds\<^sub>t lt p" by (rule is_minimal_basisD2)
      thus ?thesis unfolding \<open>b = r\<close> ltr by simp
    next
      assume "b \<in> B \<and> b \<noteq> p"
      hence "b \<in> B" ..
      from major \<open>a \<in> B\<close> \<open>b \<in> B\<close> \<open>a \<noteq> b\<close> show ?thesis by (rule is_minimal_basisD2)
    qed
  qed
qed

subsection \<open>Computing Minimal Bases\<close>
  
primrec comp_min_basis_aux :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) list" where
  comp_min_basis_aux_base: "comp_min_basis_aux Nil ys = ys"|
  comp_min_basis_aux_rec: "comp_min_basis_aux (x # xs) ys =
    (if (\<exists>q\<in>(set xs \<union> set ys). lt q adds\<^sub>t lt x) then
      (comp_min_basis_aux xs ys)
    else
      (comp_min_basis_aux xs (x # ys))
    )"
  
lemma subset_comp_min_basis_aux: "set ys \<subseteq> set (comp_min_basis_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_min_basis_aux_base ..
next
  case (Cons a xs)
  have "set ys \<subseteq> set (a#ys)" by auto
  also have "set (a#ys) \<subseteq> set (comp_min_basis_aux xs (a#ys))" by (rule Cons.hyps)
  finally have "set ys \<subseteq> set (comp_min_basis_aux xs (a#ys))" .
  moreover have "set ys \<subseteq> set (comp_min_basis_aux xs ys)" by (rule Cons.hyps)
  ultimately show ?case unfolding comp_min_basis_aux_rec by simp
qed
    
lemma comp_min_basis_aux_subset: "set (comp_min_basis_aux xs ys) \<subseteq> set xs \<union> set ys"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_min_basis_aux_base by simp
next
  case (Cons a xs)
  from Cons.hyps have "set (comp_min_basis_aux xs ys) \<subseteq> set xs \<union> set ys" .
  also have "... \<subseteq> set (a#xs) \<union> set ys" by auto
  finally have c1: "set (comp_min_basis_aux xs ys) \<subseteq> set (a#xs) \<union> set ys" .
  
  from Cons.hyps have "set (comp_min_basis_aux xs (a#ys)) \<subseteq> set xs \<union> set (a#ys)" .
  also have "... = set (a#xs) \<union> set ys" by auto
  finally have c2: "set (comp_min_basis_aux xs (a#ys)) \<subseteq> set (a#xs) \<union> set ys" .
  
  from c1 c2 show ?case unfolding comp_min_basis_aux_rec by simp
qed

lemmas comp_min_basis_aux_Nil_subset = comp_min_basis_aux_subset[of _ "[]", simplified]
  
lemma comp_min_basis_aux_notin:
  assumes "x \<in> set xs \<union> set ys" and "x \<notin> set (comp_min_basis_aux xs ys)" and "x \<noteq> 0"
  shows "\<exists>y\<in>set xs \<union> set ys. y \<noteq> 0 \<and> lt y adds\<^sub>t lt x"
  using assms
proof (induct xs arbitrary: x ys)
  case Nil
  show ?case by (rule, intro conjI, fact, rule adds_term_refl, fact)
next
  case (Cons a xs)
  from Cons(3) show ?case unfolding comp_min_basis_aux_rec
  proof (simp only: split: if_splits)
    assume "\<exists>q\<in>set xs \<union> set ys. lt q adds\<^sub>t lt a" and "x \<notin> set (comp_min_basis_aux xs ys)"
    from Cons(2) have "x = a \<or> x \<in> set xs \<union> set ys" by simp
    thus ?thesis
    proof
      assume "x = a"
      show ?thesis by (rule, intro conjI, fact, rule adds_term_refl, fact)
    next
      assume "x \<in> set xs \<union> set ys"
      have "\<exists>y\<in>set xs \<union> set ys. y \<noteq> 0 \<and> lt y adds\<^sub>t lt x" by (rule Cons.hyps, fact+)
      then obtain y where "y \<in> set xs \<union> set ys" and "y \<noteq> 0 \<and> lt y adds\<^sub>t lt x" ..
      show ?thesis
      proof (rule, fact)
        from \<open>y \<in> set xs \<union> set ys\<close> show "y \<in> set (a # xs) \<union> set ys" by simp
      qed
    qed
  next
    assume "\<not> (\<exists>q\<in>set xs \<union> set ys. lt q adds\<^sub>t lt a)" and
      "x \<notin> set (comp_min_basis_aux xs (a # ys))"
    from Cons(2) have "x \<in> set xs \<union> set (a#ys)" by simp
    have "\<exists>y\<in>set xs \<union> set (a#ys). y \<noteq> 0 \<and> lt y adds\<^sub>t lt x" by (rule Cons.hyps, fact+)
    then obtain y where "y \<in> set xs \<union> set (a#ys)" and "y \<noteq> 0 \<and> lt y adds\<^sub>t lt x" ..
    show ?thesis
    proof (rule, fact)
      from \<open>y \<in> set xs \<union> set (a#ys)\<close> show "y \<in> set (a # xs) \<union> set ys" by simp
    qed
  qed
qed

lemma comp_min_basis_aux_adds:
  assumes pin: "p \<in> set xs"
    and "\<And>x. x \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> 0"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lt x adds\<^sub>t lt y"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
  shows "\<exists>q\<in>set (comp_min_basis_aux xs ys). lt q adds\<^sub>t lt p"
  using assms
proof (induct xs arbitrary: p ys)
  case Nil
  from \<open>p \<in> set []\<close> show ?case by simp
next
  case (Cons a xs)
  let ?A = "set (a # xs) \<union> set ys"
  let ?B = "set xs \<union> set ys"
  let ?C = "set xs \<union> set (a # ys)"
  have "?C = ?A" by simp
  have "?B \<subseteq> ?A" by auto
  have "\<And>x. x \<in> ?B \<Longrightarrow> x \<noteq> 0" by (auto simp add: \<open>?B \<subseteq> ?A\<close> Cons(3))
  have "\<And>x y. x \<in> ?B \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lt x adds\<^sub>t lt y"
    by (auto simp add: \<open>?B \<subseteq> ?A\<close> Cons(4))
  have "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
    by (auto simp add: \<open>?B \<subseteq> ?A\<close> Cons(5))
      
  from \<open>p \<in> set (a # xs)\<close> have "p \<in> ?A" ..
  hence "p \<noteq> 0" by (rule Cons(3))
  from \<open>p \<in> set (a#xs)\<close> have "p = a \<or> p \<in> set xs" by auto
  thus ?case
  proof
    assume "p = a"
    with \<open>p \<noteq> 0\<close> have "a \<noteq> 0" by simp
    show ?case
    proof (cases "\<exists>q\<in>?B. lt q adds\<^sub>t lt a")
      case True
      then obtain q where "q \<in> ?B" and "lt q adds\<^sub>t lt a" ..
      from True have eq: "comp_min_basis_aux (a # xs) ys = comp_min_basis_aux xs ys"
        unfolding comp_min_basis_aux_rec by simp
      from \<open>q \<in> ?B\<close> show ?thesis
      proof
        assume "q \<in> set xs"
        have "\<exists>q1\<in>set (comp_min_basis_aux xs ys). lt q1 adds\<^sub>t lt q" by (rule Cons.hyps, fact+)
        then obtain q1 where "q1 \<in> set (comp_min_basis_aux xs ys)" and "lt q1 adds\<^sub>t lt q" ..
        show ?thesis
        proof
          show "q1 \<in> set (comp_min_basis_aux (a # xs) ys)" unfolding eq by fact
        next
          from \<open>lt q1 adds\<^sub>t lt q\<close> \<open>lt q adds\<^sub>t lt a\<close> show "lt q1 adds\<^sub>t lt p" unfolding \<open>p = a\<close>
            by (rule adds_term_trans)
        qed
      next
        assume "q \<in> set ys"
        have "q \<in> set (comp_min_basis_aux xs ys)" by (rule, fact \<open>q \<in> set ys\<close>, rule subset_comp_min_basis_aux)
        show ?thesis
        proof
          show "q \<in> set (comp_min_basis_aux (a # xs) ys)" unfolding eq by fact
       next
          from \<open>lt q adds\<^sub>t lt a\<close> show "lt q adds\<^sub>t lt p" unfolding \<open>p = a\<close> .
        qed
      qed
    next
      case False
      show ?thesis
      proof
        have "a \<in> set (comp_min_basis_aux xs (a#ys))"
        proof
          show "a \<in> set (a#ys)" by simp
        next
          show "set (a # ys) \<subseteq> set (comp_min_basis_aux xs (a # ys))" by (rule subset_comp_min_basis_aux)
        qed
        with \<open>a \<noteq> 0\<close> False show "a \<in> set (comp_min_basis_aux (a # xs) ys)"
          unfolding comp_min_basis_aux_rec by auto
      next
        show "lt a adds\<^sub>t lt p" unfolding \<open>p = a\<close> by (rule adds_term_refl)
      qed
    qed
  next
    assume "p \<in> set xs"
    have "\<exists>q\<in>set (comp_min_basis_aux xs ys). lt q adds\<^sub>t lt p" by (rule Cons.hyps, fact+)
    then obtain q where qin: "q \<in> set (comp_min_basis_aux xs ys)" and "lt q adds\<^sub>t lt p" ..
    show ?case
    proof (cases "\<exists>q\<in>?B. lt q adds\<^sub>t lt a")
      case True
      hence eq: "comp_min_basis_aux (a # xs) ys = comp_min_basis_aux xs ys"
        unfolding comp_min_basis_aux_rec by simp
      show ?thesis unfolding eq by (rule, fact \<open>lt q adds\<^sub>t lt p\<close>, fact)
    next
      case False
      hence eq: "comp_min_basis_aux (a#xs) ys = comp_min_basis_aux xs (a#ys)"
        unfolding comp_min_basis_aux_rec by auto
      from False have rl: "\<And>q. q \<in> ?B \<Longrightarrow> \<not> lt q adds\<^sub>t lt a" by auto
      show ?thesis unfolding eq
      proof (rule Cons.hyps, fact)
        fix x
        assume "x \<in> ?C"
        thus "x \<noteq> 0" unfolding \<open>?C = ?A\<close> by (rule Cons(3))
      next
        fix x y
        assume "x \<in> ?C"
        hence "x \<in> ?A" unfolding \<open>?C = ?A\<close> .
        hence "x \<noteq> 0" by (rule Cons(3))
        assume "x \<noteq> y"
        assume "y \<in> set (a # ys)"
        hence "y = a \<or> y \<in> set ys" by simp
        thus "\<not> lt x adds\<^sub>t lt y"
        proof
          assume "y = a"
          show ?thesis unfolding \<open>y = a\<close>
          proof (rule rl)
            from \<open>x \<in> ?A\<close> have "x = a \<or> x \<in> ?B" by simp
            thus "x \<in> ?B"
            proof
              assume "x = a"
              with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>y = a\<close> ..
            qed
          qed
        next
          assume "y \<in> set ys"
          from \<open>x \<in> ?A\<close> this \<open>x \<noteq> y\<close> show ?thesis by (rule Cons(4))
        qed
      next
        fix x y
        assume "x \<in> ?C" and "y \<in> ?C" and "x \<noteq> y"
        thus "lt x \<noteq> lt y" unfolding \<open>?C = ?A\<close> by (rule Cons(5))
      qed
    qed
  qed
qed

lemma comp_min_basis_aux_Nil_adds:
  assumes "p \<in> set xs" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
  obtains q where "q \<in> set (comp_min_basis_aux xs [])" and "lt q adds\<^sub>t lt p"
proof -
  from assms(1) have "\<exists>q\<in>set (comp_min_basis_aux xs []). lt q adds\<^sub>t lt p"
  proof (rule comp_min_basis_aux_adds)
    fix x
    assume "x \<in> set xs \<union> set []"
    hence "x \<in> set xs" by simp
    with assms(2) show "x \<noteq> 0" by auto
  next
    fix x y :: "'t \<Rightarrow>\<^sub>0 'b"
    assume "y \<in> set []"
    thus "\<not> lt x adds\<^sub>t lt y" by simp
  next
    fix x y :: "'t \<Rightarrow>\<^sub>0 'b"
    assume "x \<in> set xs \<union> set []"
    hence x: "x \<in> set xs" by simp
    assume "y \<in> set xs \<union> set []"
    hence y: "y \<in> set xs" by simp
    assume "x \<noteq> y"
    from x y this show "lt x \<noteq> lt y" by (rule assms(3))
  qed
  then obtain q where "q \<in> set (comp_min_basis_aux xs [])" and "lt q adds\<^sub>t lt p" ..
  thus ?thesis ..
qed
  
lemma comp_min_basis_aux_distinct:
  assumes "distinct ys"
  shows "distinct (comp_min_basis_aux xs ys)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  thus ?case unfolding comp_min_basis_aux_base .
next
  case (Cons a xs)
  show ?case unfolding comp_min_basis_aux_rec
  proof (split if_split, intro conjI impI, rule Cons.hyps, rule Cons(2))
    assume a: "\<not> (\<exists>q\<in>set xs \<union> set ys. lt q adds\<^sub>t lt a)"
    show "distinct (comp_min_basis_aux xs (a # ys))"
    proof (rule Cons.hyps)
      have "a \<notin> set ys"
      proof
        assume "a \<in> set ys"
        hence "a \<in> set xs \<union> set ys" by simp
        have "\<exists>q\<in>set xs \<union> set ys. lt q adds\<^sub>t lt a"
        proof
          show "lt a adds\<^sub>t lt a" by (rule adds_term_refl)
        qed fact
        with a show False ..
      qed
      with Cons(2) show "distinct (a # ys)" by simp
    qed
  qed
qed

lemma comp_min_basis_aux_Nil_is_red:
  assumes "is_red (set xs) f" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
  shows "is_red (set (comp_min_basis_aux xs [])) f"
proof -
  from assms(1) obtain x t where "x \<in> set xs" and "t \<in> keys f" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> assms(2) assms(3) obtain y
    where yin: "y \<in> set (comp_min_basis_aux xs [])" and "lt y adds\<^sub>t lt x"
    by (rule comp_min_basis_aux_Nil_adds)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lt y adds\<^sub>t lt x\<close> \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" by (rule adds_term_trans)
  next
    from comp_min_basis_aux_Nil_subset yin have "y \<in> set xs" ..
    with assms(2) show "y \<noteq> 0" by auto
  qed fact+
qed
  
definition comp_min_basis_pre :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) list" where
  "comp_min_basis_pre xs = remdups_wrt lt (filter (\<lambda>x. x \<noteq> 0) xs)"
  
lemma comp_min_basis_pre_subset: "set (comp_min_basis_pre xs) \<subseteq> set xs"
  unfolding comp_min_basis_pre_def by (meson filter_is_subset subset_remdups_wrt subset_trans)

lemma comp_min_basis_pre_nonzero:
  assumes "p \<in> set (comp_min_basis_pre xs)"
  shows "p \<noteq> 0"
  using assms unfolding comp_min_basis_pre_def using subset_remdups_wrt by fastforce

lemma comp_min_basis_pre_nonzero': "0 \<notin> set (comp_min_basis_pre xs)"
  using comp_min_basis_pre_nonzero by fastforce

lemma comp_min_basis_pre_distinct_lt:
  assumes pin: "p \<in> set (comp_min_basis_pre xs)" and qin: "q \<in> set (comp_min_basis_pre xs)" and "p \<noteq> q"
  shows "lt p \<noteq> lt q"
  using assms unfolding comp_min_basis_pre_def by (rule remdups_wrt_distinct_wrt)

lemma comp_min_basis_pre_lt:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_min_basis_pre xs)" and "lt q = lt p"
proof -
  from assms have pin: "p \<in> set (filter (\<lambda>x. x \<noteq> 0) xs)" (is "p \<in> set ?ys") by simp
  hence "lt p \<in> lt ` set ?ys" by simp
  also have "... = lt ` set (remdups_wrt lt ?ys)" by (simp add: set_remdups_wrt)
  finally have "lt p \<in> lt ` set (remdups_wrt lt ?ys)" .
  then obtain q where qin: "q \<in> set (remdups_wrt lt ?ys)" and "lt q = lt p" by auto
  show ?thesis
  proof
    from qin show "q \<in> set (comp_min_basis_pre xs)" unfolding comp_min_basis_pre_def .
  qed fact
qed

lemma comp_min_basis_pre_is_red:
  assumes "is_red (set xs) f"
  shows "is_red (set (comp_min_basis_pre xs)) f"
proof -
  from assms obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_min_basis_pre xs)" and "lt y = lt x"
    by (rule comp_min_basis_pre_lt)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" by (simp only: \<open>lt y = lt x\<close>)
  next
    from yin show "y \<noteq> 0" by (rule comp_min_basis_pre_nonzero)
  qed fact+
qed

definition comp_min_basis :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) list" where
  "comp_min_basis xs = comp_min_basis_aux (comp_min_basis_pre xs) []"
  
lemma comp_min_basis_subset_comp_min_basis_pre: "set (comp_min_basis xs) \<subseteq> set (comp_min_basis_pre xs)"
  unfolding comp_min_basis_def by (rule comp_min_basis_aux_Nil_subset)
  
lemma comp_min_basis_subset: "set (comp_min_basis xs) \<subseteq> set xs"
proof -
  have "set (comp_min_basis xs) \<subseteq> set (comp_min_basis_pre xs)"
    by (rule comp_min_basis_subset_comp_min_basis_pre)
  also have "... \<subseteq> set xs" by (rule comp_min_basis_pre_subset)
  finally show ?thesis .
qed
    
lemma comp_min_basis_nonzero:
  assumes "p \<in> set (comp_min_basis xs)"
  shows "p \<noteq> 0"
by (rule comp_min_basis_pre_nonzero, rule, fact assms, fact comp_min_basis_subset_comp_min_basis_pre)

lemma comp_min_basis_adds:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_min_basis xs)" and "lt q adds\<^sub>t lt p"
proof -
  from assms obtain q1 where q1_in: "q1 \<in> set (comp_min_basis_pre xs)" and "lt q1 = lt p"
    by (rule comp_min_basis_pre_lt)
  have "0 \<notin> set (comp_min_basis_pre xs)" using comp_min_basis_pre_nonzero by auto
  with q1_in obtain q where "q \<in> set (comp_min_basis_aux (comp_min_basis_pre xs) [])" and "lt q adds\<^sub>t lt q1"
  proof (rule comp_min_basis_aux_Nil_adds)
    fix x y
    assume "x \<in> set (comp_min_basis_pre xs)" and "y \<in> set (comp_min_basis_pre xs)" and "x \<noteq> y"
    thus "lt x \<noteq> lt y" by (rule comp_min_basis_pre_distinct_lt)
  qed
  show ?thesis
  proof
    show "q \<in> set (comp_min_basis xs)" unfolding comp_min_basis_def by fact
  next
    from \<open>lt q adds\<^sub>t lt q1\<close> show "lt q adds\<^sub>t lt p" unfolding \<open>lt q1 = lt p\<close> .
  qed
qed
  
lemma comp_min_basis_is_red:
  assumes "is_red (set xs) f"
  shows "is_red (set (comp_min_basis xs)) f"
proof -
  from assms obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_min_basis xs)" and "lt y adds\<^sub>t lt x"
    by (rule comp_min_basis_adds)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lt y adds\<^sub>t lt x\<close> \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" by (rule adds_term_trans)
  next
    from yin show "y \<noteq> 0" by (rule comp_min_basis_nonzero)
  qed fact+
qed

end (* ordered_term *)

context gd_term
begin

(* Actually, we do not need "gd_term" here, but only "ulcs_powerprod". *)

lemma comp_min_basis_aux_nadds:
  assumes "p \<in> set (comp_min_basis_aux xs ys)" and "q \<in> set xs \<union> set ys" and "p \<noteq> q"
    and "\<And>x. x \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> 0"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lt x adds\<^sub>t lt y"
    and "\<And>x y. x \<in> set xs \<union> set ys \<Longrightarrow> y \<in> set xs \<union> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
  shows "\<not> lt q adds\<^sub>t lt p"
  using assms
proof (induct xs arbitrary: p q ys)
  case Nil
  from Nil(1) Nil(2) have "p \<in> set ys" "q \<in> set ys" unfolding comp_min_basis_aux_base by simp_all
  show ?case
  proof (rule Nil(5))
    from \<open>q \<in> set ys\<close> show "q \<in> set [] \<union> set ys" by simp
  next
    from \<open>p \<noteq> q\<close> show "q \<noteq> p" by simp
  qed fact
next
  case (Cons a xs)
  let ?A = "set (a#xs) \<union> set ys"
  let ?B = "set xs \<union> set ys"
  let ?C = "set xs \<union> set (a#ys)"
  from Cons(2) show ?case unfolding comp_min_basis_aux_rec
  proof (simp only: split: if_splits)
    assume a1: "\<exists>q\<in>?B. lt q adds\<^sub>t lt a"
      and "p \<in> set (comp_min_basis_aux xs ys)"
    have "\<And>x. x \<in> ?B \<Longrightarrow> x \<noteq> 0"
    proof -
      fix x
      assume "x \<in> ?B"
      hence "x \<in> ?A" by simp
      thus "x \<noteq> 0" by (rule Cons(5))
    qed
    have "\<And>x y. x \<in> ?B \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> lt x adds\<^sub>t lt y"
    proof -
      fix x y
      assume "x \<in> ?B"
      hence "x \<in> ?A" by simp
      assume "y \<in> set ys" and "x \<noteq> y"
      show "\<not> lt x adds\<^sub>t lt y" by (rule Cons(6), fact+)
    qed
    have "\<And>x y. x \<in> ?B \<Longrightarrow> y \<in> ?B \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
    proof -
      fix x y
      assume "x \<in> ?B"
      hence "x \<in> ?A" by simp
      assume "y \<in> ?B"
      hence "y \<in> ?A" by simp
      assume "x \<noteq> y"
      show "lt x \<noteq> lt y" by (rule Cons(7), fact+)
    qed
    have "q \<noteq> 0" by (rule Cons(5), fact)
    from Cons(3) have "q = a \<or> q \<in> set xs \<union> set ys" by simp
    thus ?thesis
    proof
      assume "q = a"
      from a1 show ?thesis
      proof
        fix q1
        assume "q1 \<in> set xs \<union> set ys" and "lt q1 adds\<^sub>t lt a"
        show ?thesis
        proof (cases "p = q1")
          case True
          from \<open>lt q1 adds\<^sub>t lt a\<close> have "lt p adds\<^sub>t lt q" unfolding True \<open>q = a\<close> .
          show ?thesis
          proof
            assume "lt q adds\<^sub>t lt p"
            with \<open>lt p adds\<^sub>t lt q\<close> have "lt p = lt q" by (rule adds_term_antisym)
            moreover have "lt p \<noteq> lt q"
            proof (rule Cons(7))
              from comp_min_basis_aux_subset Cons(2) show "p \<in> set (a # xs) \<union> set ys" by blast
            qed fact+
            ultimately show False by simp
          qed
        next
          case False
          have "\<not> lt q1 adds\<^sub>t lt p" by (rule Cons.hyps, fact+)
          show ?thesis
          proof
            from \<open>lt q1 adds\<^sub>t lt a\<close> have "lt q1 adds\<^sub>t lt q" unfolding \<open>q = a\<close> .
            also assume "lt q adds\<^sub>t lt p"
            finally show False using \<open>\<not> lt q1 adds\<^sub>t lt p\<close> by simp
          qed
        qed
      qed
    next
      assume "q \<in> set xs \<union> set ys"
      show ?thesis by (rule Cons.hyps, fact+)
    qed
  next
    assume a: "\<not> (\<exists>q\<in>?B. lt q adds\<^sub>t lt a)"
      and "p \<in> set (comp_min_basis_aux xs (a # ys))"
    show ?thesis
    proof (rule Cons.hyps, fact)
      from \<open>q \<in> ?A\<close> show "q \<in> ?C" by simp
    next
      fix x
      assume "x \<in> ?C"
      hence "x \<in> ?A" by simp
      thus "x \<noteq> 0" by (rule Cons(5))
    next
      fix x y
      assume "x \<in> ?C"
      hence "x \<in> ?A" by simp
      assume "x \<noteq> y"
      assume "y \<in> set (a # ys)"
      hence "y = a \<or> y \<in> set ys" by simp
      thus "\<not> lt x adds\<^sub>t lt y"
      proof
        assume "y = a"
        from \<open>x \<in> ?A\<close> have "x = a \<or> x \<in> ?B" by simp
        thus ?thesis
        proof
          assume "x = a"
          with \<open>x \<noteq> y\<close> show ?thesis unfolding \<open>y = a\<close> ..
        next
          assume "x \<in> ?B"
          from a have "\<And>q. q \<in> ?B \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> \<not> lt q adds\<^sub>t lt a" by auto
          thus ?thesis unfolding \<open>y = a\<close>
          proof this
            show "x \<in> ?B" by fact
          next
            show "x \<noteq> 0" by (rule Cons(5), fact)
          qed
        qed
      next
        assume "y \<in> set ys"
        show ?thesis by (rule Cons(6), fact+)
      qed
    next
      fix x y
      assume "x \<in> ?C"
      hence "x \<in> ?A" by simp
      assume "y \<in> ?C"
      hence "y \<in> ?A" by simp
      assume "x \<noteq> y"
      show "lt x \<noteq> lt y" by (rule Cons(7), fact+)
    qed fact
  qed
qed

lemma comp_min_basis_aux_Nil_nadds:
  assumes "p \<in> set (comp_min_basis_aux xs [])" and "q \<in> set xs" and "p \<noteq> q" and "0 \<notin> set xs"
    and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<noteq> y \<Longrightarrow> lt x \<noteq> lt y"
  shows "\<not> lt q adds\<^sub>t lt p"
  using assms(1) _ assms(3)
proof (rule comp_min_basis_aux_nadds)
  from assms(2) show "q \<in> set xs \<union> set []" by simp
next
  fix x
  assume "x \<in> set xs \<union> set []"
  with assms(4) show "x \<noteq> 0" by auto
next
  fix x y :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "y \<in> set []"
  thus "\<not> lt x adds\<^sub>t lt y" by simp
next
  fix x y
  assume "x \<in> set xs \<union> set []" and "y \<in> set xs \<union> set []"
  hence "x \<in> set xs" and "y \<in> set xs" by simp_all
  moreover assume "x \<noteq> y"
  ultimately show "lt x \<noteq> lt y" by (rule assms(5))
qed

lemma comp_min_basis_nadds:
  assumes "p \<in> set (comp_min_basis xs)" and "q \<in> set (comp_min_basis xs)" and "p \<noteq> q"
  shows "\<not> lt q adds\<^sub>t lt p"
proof (rule comp_min_basis_aux_Nil_nadds)
  from assms(1) show "p \<in> set (comp_min_basis_aux (comp_min_basis_pre xs) [])"
    unfolding comp_min_basis_def .
next
  show "q \<in> set (comp_min_basis_pre xs)"
    by (rule, fact assms(2), fact comp_min_basis_subset_comp_min_basis_pre)
qed (fact, fact comp_min_basis_pre_nonzero', fact comp_min_basis_pre_distinct_lt)

lemma comp_min_basis_is_minimal_basis: "is_minimal_basis (set (comp_min_basis xs))"
  by (rule is_minimal_basisI, rule comp_min_basis_nonzero, assumption, rule comp_min_basis_nadds,
      assumption+, simp)

lemma comp_min_basis_distinct: "distinct (comp_min_basis xs)"
  unfolding comp_min_basis_def by (rule comp_min_basis_aux_distinct, simp)

subsection \<open>Auto-Reduction\<close>

lemma is_minimal_basis_trd_is_minimal_basis:
  assumes "is_minimal_basis (set (x # xs))" and "x \<notin> set xs"
  shows "is_minimal_basis (set ((trd xs x) # xs))"
proof -
  from assms(1) have "is_minimal_basis (insert (trd xs x) (set (x # xs) - {x}))"
  proof (rule is_minimal_basis_replace, simp)
    from assms(2) have eq: "set (x # xs) - {x} = set xs" by simp
    show "(red (set (x # xs) - {x}))\<^sup>*\<^sup>* x (trd xs x)" unfolding eq by (rule trd_red_rtrancl)
  qed
  also from assms(2) have "... = set ((trd xs x) # xs)" by auto
  finally show ?thesis .
qed

lemma is_minimal_basis_trd_distinct:
  assumes min: "is_minimal_basis (set (x # xs))" and dist: "distinct (x # xs)"
  shows "distinct ((trd xs x) # xs)"
proof -
  let ?y = "trd xs x"
  from min have lty: "lt ?y = lt x"
  proof (rule minimal_basis_red_rtrancl_lt, simp)
    from dist have "x \<notin> set xs" by simp
    hence eq: "set (x # xs) - {x} = set xs" by simp
    show "(red (set (x # xs) - {x}))\<^sup>*\<^sup>* x (trd xs x)" unfolding eq by (rule trd_red_rtrancl)
  qed
  have "?y \<notin> set xs"
  proof
    assume "?y \<in> set xs"
    hence "?y \<in> set (x # xs)" by simp
    with min have "\<not> lt ?y adds\<^sub>t lt x"
    proof (rule is_minimal_basisD2, simp)
      show "?y \<noteq> x"
      proof
        assume "?y = x"
        from dist have "x \<notin> set xs" by simp
        with \<open>?y \<in> set xs\<close> show False unfolding \<open>?y = x\<close> by simp
      qed
    qed
    thus False unfolding lty by (simp add: adds_term_refl)
  qed
  moreover from dist have "distinct xs" by simp
  ultimately show ?thesis by simp
qed

primrec comp_red_basis_aux :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list" where
  comp_red_basis_aux_base: "comp_red_basis_aux Nil ys = ys"|
  comp_red_basis_aux_rec: "comp_red_basis_aux (x # xs) ys = comp_red_basis_aux xs ((trd (xs @ ys) x) # ys)"
  
lemma subset_comp_red_basis_aux: "set ys \<subseteq> set (comp_red_basis_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base ..
next
  case (Cons a xs)
  have "set ys \<subseteq> set ((trd (xs @ ys) a) # ys)" by auto
  also have "... \<subseteq> set (comp_red_basis_aux xs ((trd (xs @ ys) a) # ys))" by (rule Cons.hyps)
  finally show ?case unfolding comp_red_basis_aux_rec .
qed

lemma comp_red_basis_aux_nonzero:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)" and "p \<in> set (comp_red_basis_aux xs ys)"
  shows "p \<noteq> 0"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case
  proof (rule is_minimal_basisD1)
    from Nil(1) show "is_minimal_basis (set ys)" by simp
  next
    from Nil(3) show "p \<in> set ys" unfolding comp_red_basis_aux_base .
  qed
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  have "a \<in> set (a # xs @ ys)" by simp
  from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?ys = "trd (xs @ ys) a # ys"
  show ?case
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  next
    from Cons(4) show "p \<in> set (comp_red_basis_aux xs ?ys)" unfolding comp_red_basis_aux_rec .
  qed
qed
  
lemma comp_red_basis_aux_lt:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
  shows "lt ` set (xs @ ys) = lt ` set (comp_red_basis_aux xs ys)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a: "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  from Cons(2) have "lt ?b = lt a" unfolding eq
  proof (rule minimal_basis_red_rtrancl_lt, simp)
    from a have eq2: "set (a # xs @ ys) - {a} = set (xs @ ys)" by simp
    show "(red (set (a # xs @ ys) - {a}))\<^sup>*\<^sup>* a ?b" unfolding eq2 by (rule trd_red_rtrancl)
  qed
  hence "lt ` set ((a # xs) @ ys) = lt ` set ((?b # xs) @ ys)" by simp
  also have "... = lt ` set (xs @ (?b # ys))" by simp
  finally have eq2: "lt ` set ((a # xs) @ ys) = lt ` set (xs @ (?b # ys))" .
  show ?case unfolding comp_red_basis_aux_rec eq2
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  qed
qed
  
lemma comp_red_basis_aux_pmdl:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
  shows "pmdl (set (comp_red_basis_aux xs ys)) \<subseteq> pmdl (set (xs @ ys))"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a: "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  have "pmdl (set (comp_red_basis_aux xs ?ys)) \<subseteq> pmdl (set (xs @ ?ys))"
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  qed
  also have "... = pmdl (set (?b # xs @ ys))" by simp
  also from a have "... = pmdl (insert ?b (set (a # xs @ ys) - {a}))" by auto
  also have "... \<subseteq> pmdl (set (a # xs @ ys))"
  proof (rule pmdl.replace_module)
    have "a - (trd (xs @ ys) a) \<in> pmdl (set (xs @ ys))" by (rule trd_in_pmdl)
    have "a - (trd (xs @ ys) a) \<in> pmdl (set (a # xs @ ys))"
    proof
      show "pmdl (set (xs @ ys)) \<subseteq> pmdl (set (a # xs @ ys))" by (rule pmdl.module_mono, auto)
    qed fact
    hence "- (a - (trd (xs @ ys) a)) \<in> pmdl (set (a # xs @ ys))" by (rule pmdl.module_closed_uminus)
    hence "(trd (xs @ ys) a) - a \<in> pmdl (set (a # xs @ ys))" by simp
    hence "((trd (xs @ ys) a) - a) + a \<in> pmdl (set (a # xs @ ys))"
    proof (rule pmdl.module_closed_plus)
      show "a \<in> pmdl (set (a # xs @ ys))"
      proof
        show "a \<in> set (a # xs @ ys)" by simp
      qed (rule pmdl.generator_subset_module)
    qed
    thus "trd (xs @ ys) a \<in> pmdl (set (a # xs @ ys))" by simp
  qed
  also have "... = pmdl (set ((a # xs) @ ys))" by simp
  finally show ?case unfolding comp_red_basis_aux_rec .
qed
  
lemma comp_red_basis_aux_irred:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
    and "\<And>y. y \<in> set ys \<Longrightarrow> \<not> is_red (set (xs @ ys) - {y}) y"
    and "p \<in> set (comp_red_basis_aux xs ys)"
  shows "\<not> is_red (set (comp_red_basis_aux xs ys) - {p}) p"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  have "\<not> is_red (set ([] @ ys) - {p}) p"
  proof (rule Nil(3))
    from Nil(4) show "p \<in> set ys" unfolding comp_red_basis_aux_base .
  qed
  thus ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a_notin: "a \<notin> set (xs @ ys)" unfolding eq by simp
  from Cons(2) have is_min: "is_minimal_basis (set (a # xs @ ys))" unfolding eq .
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  have dist: "distinct (?b # (xs @ ys))"
  proof (rule is_minimal_basis_trd_distinct, fact is_min)
    from Cons(3) show "distinct (a # xs @ ys)" unfolding eq .
  qed
  
  show ?case unfolding comp_red_basis_aux_rec
  proof (rule Cons.hyps)
    from Cons(2) a_notin show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from dist show "distinct (xs @ ?ys)" unfolding distinct_reorder .
  next
    fix y
    assume "y \<in> set ?ys"
    hence "y = ?b \<or> y \<in> set ys" by simp
    thus "\<not> is_red (set (xs @ ?ys) - {y}) y"
    proof
      assume "y = ?b"
      from dist have "?b \<notin> set (xs @ ys)" by simp
      hence eq3: "set (xs @ ?ys) - {?b} = set (xs @ ys)" unfolding set_reorder by simp
      have "\<not> is_red (set (xs @ ys)) ?b" by (rule trd_irred)
      thus ?thesis unfolding \<open>y = ?b\<close> eq3 .
    next
      assume "y \<in> set ys"
      hence irred: "\<not> is_red (set ((a # xs) @ ys) - {y}) y" by (rule Cons(4))
      from \<open>y \<in> set ys\<close> a_notin have "y \<noteq> a" by auto
      hence eq3: "set ((a # xs) @ ys) - {y} = {a} \<union> (set (xs @ ys) - {y})" by auto
      from irred have i1: "\<not> is_red {a} y" and i2: "\<not> is_red (set (xs @ ys) - {y}) y"
        unfolding eq3 is_red_union by simp_all
      show ?thesis unfolding set_reorder
      proof (cases "y = ?b")
        case True
        from i2 show "\<not> is_red (set (?b # xs @ ys) - {y}) y" by (simp add: True)
      next
        case False
        hence eq4: "set (?b # xs @ ys) - {y} = {?b} \<union> (set (xs @ ys) - {y})" by auto
        show "\<not> is_red (set (?b # xs @ ys) - {y}) y" unfolding eq4
        proof
          assume "is_red ({?b} \<union> (set (xs @ ys) - {y})) y"
          thus False unfolding is_red_union
          proof
            have ltb: "lt ?b = lt a"
            proof (rule minimal_basis_red_rtrancl_lt, fact is_min)
              show "a \<in> set (a # xs @ ys)" by simp
            next
              from a_notin have eq: "set (a # xs @ ys) - {a} = set (xs @ ys)" by simp
              show "(red (set (a # xs @ ys) - {a}))\<^sup>*\<^sup>* a ?b" unfolding eq by (rule trd_red_rtrancl)
            qed
            assume "is_red {?b} y"
            then obtain t where "t \<in> keys y" and "lt ?b adds\<^sub>t t" unfolding is_red_adds_iff by auto
            with ltb have "lt a adds\<^sub>t t" by simp
            have "is_red {a} y"
              by (rule is_red_addsI, rule, rule is_minimal_basisD1, fact is_min, simp, fact+)
            with i1 show False ..
          next
            assume "is_red (set (xs @ ys) - {y}) y"
            with i2 show False ..
          qed
        qed
      qed
    qed
  next
    from Cons(5) show "p \<in> set (comp_red_basis_aux xs ?ys)" unfolding comp_red_basis_aux_rec .
  qed
qed

lemma comp_red_basis_aux_dgrad_p_set_le:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d (set (comp_red_basis_aux xs ys)) (set xs \<union> set ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by (simp, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (Cons x xs)
  let ?h = "trd (xs @ ys) x"
  have "dgrad_p_set_le d (set (comp_red_basis_aux xs (?h # ys))) (set xs \<union> set (?h # ys))"
    by (fact Cons)
  also have "... = insert ?h (set xs \<union> set ys)" by simp
  also have "dgrad_p_set_le d ... (insert x (set xs \<union> set ys))"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d (set xs \<union> set ys) (insert x (set xs \<union> set ys))"
      by (rule dgrad_p_set_le_subset, blast)
  next
    have "(red (set (xs @ ys)))\<^sup>*\<^sup>* x ?h" by (rule trd_red_rtrancl)
    with assms have "dgrad_p_set_le d {?h} (insert x (set (xs @ ys)))"
      by (rule dgrad_p_set_le_red_rtrancl)
    thus "dgrad_p_set_le d {?h} (insert x (set xs \<union> set ys))" by simp
  qed
  finally show ?case by simp
qed

definition comp_red_basis :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "comp_red_basis xs = comp_red_basis_aux (comp_min_basis xs) []"
  
lemma comp_red_basis_nonzero:
  assumes "p \<in> set (comp_red_basis xs)"
  shows "p \<noteq> 0"
proof -
  have "is_minimal_basis (set ((comp_min_basis xs) @ []))" by (simp add: comp_min_basis_is_minimal_basis)
  moreover have "distinct ((comp_min_basis xs) @ [])" by (simp add: comp_min_basis_distinct)
  moreover from assms have "p \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def .
  ultimately show ?thesis by (rule comp_red_basis_aux_nonzero)
qed

lemma pmdl_comp_red_basis_subset: "pmdl (set (comp_red_basis xs)) \<subseteq> pmdl (set xs)"
proof
  fix f
  assume fin: "f \<in> pmdl (set (comp_red_basis xs))"
  have "f \<in> pmdl (set (comp_min_basis xs))"
  proof
    from fin show  "f \<in> pmdl (set (comp_red_basis_aux (comp_min_basis xs) []))"
      unfolding comp_red_basis_def .
  next
    have "pmdl (set (comp_red_basis_aux (comp_min_basis xs) [])) \<subseteq> pmdl (set ((comp_min_basis xs) @ []))"
      by (rule comp_red_basis_aux_pmdl, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
    thus "pmdl (set (comp_red_basis_aux (comp_min_basis xs) [])) \<subseteq> pmdl (set (comp_min_basis xs))"
      by simp
  qed
  also from comp_min_basis_subset have "... \<subseteq> pmdl (set xs)" by (rule pmdl.module_mono)
  finally show "f \<in> pmdl (set xs)" .
qed

lemma comp_red_basis_adds:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_red_basis xs)" and "lt q adds\<^sub>t lt p"
proof -
  from assms obtain q1 where "q1 \<in> set (comp_min_basis xs)" and "lt q1 adds\<^sub>t lt p"
    by (rule comp_min_basis_adds)
  from \<open>q1 \<in> set (comp_min_basis xs)\<close> have "lt q1 \<in> lt ` set (comp_min_basis xs)" by simp
  also have "... = lt ` set ((comp_min_basis xs) @ [])" by simp
  also have "... = lt ` set (comp_red_basis_aux (comp_min_basis xs) [])"
    by (rule comp_red_basis_aux_lt, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
  finally obtain q where "q \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" and "lt q = lt q1"
    by auto
  show ?thesis
  proof
    show "q \<in> set (comp_red_basis xs)" unfolding comp_red_basis_def by fact
  next
    from \<open>lt q1 adds\<^sub>t lt p\<close> show "lt q adds\<^sub>t lt p" unfolding \<open>lt q = lt q1\<close> .
  qed
qed
  
lemma comp_red_basis_lt:
  assumes "p \<in> set (comp_red_basis xs)"
  obtains q where "q \<in> set xs" and "q \<noteq> 0" and "lt q = lt p"
proof -
  have eq: "lt ` set ((comp_min_basis xs) @ []) = lt ` set (comp_red_basis_aux (comp_min_basis xs) [])"
    by (rule comp_red_basis_aux_lt, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
  from assms have "lt p \<in> lt ` set (comp_red_basis xs)" by simp
  also have "... = lt ` set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def ..
  also have "... = lt ` set (comp_min_basis xs)" unfolding eq[symmetric] by simp
  finally obtain q where "q \<in> set (comp_min_basis xs)" and "lt q = lt p" by auto
  show ?thesis
  proof
    show "q \<in> set xs" by (rule, fact, rule comp_min_basis_subset)
  next
    show "q \<noteq> 0" by (rule comp_min_basis_nonzero, fact)
  qed fact
qed

lemma comp_red_basis_is_red: "is_red (set (comp_red_basis xs)) f \<longleftrightarrow> is_red (set xs) f"
proof
  assume "is_red (set (comp_red_basis xs)) f"
  then obtain x t where "x \<in> set (comp_red_basis xs)" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set (comp_red_basis xs)\<close> obtain y where yin: "y \<in> set xs" and "y \<noteq> 0" and "lt y = lt x"
    by (rule comp_red_basis_lt)
  show "is_red (set xs) f"
  proof (rule is_red_addsI)
    from \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" unfolding \<open>lt y = lt x\<close> .
  qed fact+
next
  assume "is_red (set xs) f"
  then obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_red_basis xs)" and "lt y adds\<^sub>t lt x"
    by (rule comp_red_basis_adds)
  show "is_red (set (comp_red_basis xs)) f"
  proof (rule is_red_addsI)
    from \<open>lt y adds\<^sub>t lt x\<close> \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" by (rule adds_term_trans)
  next
    from yin show "y \<noteq> 0" by (rule comp_red_basis_nonzero)
  qed fact+
qed
    
lemma comp_red_basis_is_auto_reduced: "is_auto_reduced (set (comp_red_basis xs))"
  unfolding is_auto_reduced_def remove_def
proof (intro ballI)
  fix x
  assume xin: "x \<in> set (comp_red_basis xs)"
  show "\<not> is_red (set (comp_red_basis xs) - {x}) x" unfolding comp_red_basis_def
  proof (rule comp_red_basis_aux_irred, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
    from xin show "x \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def .
  qed
qed

lemma comp_red_basis_dgrad_p_set_le:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d (set (comp_red_basis xs)) (set xs)"
proof -
  have "dgrad_p_set_le d (set (comp_red_basis xs)) (set (comp_min_basis xs) \<union> set [])"
    unfolding comp_red_basis_def using assms by (rule comp_red_basis_aux_dgrad_p_set_le)
  also have "... = set (comp_min_basis xs)" by simp
  also from comp_min_basis_subset have "dgrad_p_set_le d ... (set xs)"
    by (rule dgrad_p_set_le_subset)
  finally show ?thesis .
qed

subsection \<open>Auto-Reduction and Monicity\<close>

definition comp_red_monic_basis :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list" where
  "comp_red_monic_basis xs = map monic (comp_red_basis xs)"

lemma set_comp_red_monic_basis: "set (comp_red_monic_basis xs) = monic_set (set (comp_red_basis xs))"
  unfolding comp_red_monic_basis_def monic_set_def by simp

lemma comp_red_monic_basis_nonzero:
  assumes "p \<in> set (comp_red_monic_basis xs)"
  shows "p \<noteq> 0"
proof -
  from assms obtain p' where p_def: "p = monic p'" and p': "p' \<in> set (comp_red_basis xs)"
    unfolding set_comp_red_monic_basis monic_set_def ..
  from p' have "p' \<noteq> 0" by (rule comp_red_basis_nonzero)
  thus ?thesis unfolding p_def monic_0_iff .
qed

lemma comp_red_monic_basis_is_monic_set: "is_monic_set (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis by (rule monic_set_is_monic_set)

lemma pmdl_comp_red_monic_basis_subset: "pmdl (set (comp_red_monic_basis xs)) \<subseteq> pmdl (set xs)"
  unfolding set_comp_red_monic_basis monic_set_pmdl by (fact pmdl_comp_red_basis_subset)

lemma comp_red_monic_basis_is_auto_reduced: "is_auto_reduced (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis by (rule monic_set_is_auto_reduced, rule comp_red_basis_is_auto_reduced)

lemma comp_red_monic_basis_dgrad_p_set_le:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d (set (comp_red_monic_basis xs)) (set xs)"
proof -
  have "dgrad_p_set_le d (monic_set (set (comp_red_basis xs))) (set (comp_red_basis xs))"
    by (simp add: dgrad_p_set_le_def, fact dgrad_set_le_refl)
  also from assms have "dgrad_p_set_le d ... (set xs)" by (rule comp_red_basis_dgrad_p_set_le)
  finally show ?thesis by (simp add: set_comp_red_monic_basis)
qed

end (* gd_term *)

end (* theory *)
