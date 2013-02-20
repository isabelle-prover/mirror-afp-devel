theory "HOLCF-Join"
imports "HOLCF"
begin

subsubsection {* Binary Joins and compatibility *}

context cpo
begin
definition join :: "'a => 'a => 'a" (infix "\<squnion>" 80) where
  "x \<squnion> y = (if \<exists> z. {x, y} <<| z then lub {x, y} else x)"

definition compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "compatible x y = (\<exists> z. {x, y} <<| z)"

lemma compatibleI:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "compatible x y"
proof-
  from assms
  have "{x,y} <<| z"
    by (auto intro: is_lubI)
  thus ?thesis unfolding compatible_def by (metis)
qed

lemma is_joinI:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "x \<squnion> y = z"
proof-
  from assms
  have "{x,y} <<| z"
    by (auto intro: is_lubI)
  thus ?thesis unfolding join_def by (metis lub_eqI)
qed

lemma is_join_and_compatible:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "compatible x y \<and> x \<squnion> y = z"
by (metis compatibleI is_joinI assms)

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  unfolding compatible_def by (metis insert_commute)

lemma compatible_sym_iff: "compatible x y \<longleftrightarrow> compatible y x"
  unfolding compatible_def by (metis insert_commute)

lemma join_above1: "compatible x y \<Longrightarrow> x \<sqsubseteq> x \<squnion> y"
  unfolding compatible_def join_def
  apply auto
  by (metis is_lubD1 is_ub_insert lub_eqI)  

lemma join_above2: "compatible x y \<Longrightarrow> y \<sqsubseteq> x \<squnion> y"
  unfolding compatible_def join_def
  apply auto
  by (metis is_lubD1 is_ub_insert lub_eqI)  

lemma larger_is_join1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  unfolding join_def
  by (metis doubleton_eq_iff lub_bin)

lemma larger_is_join2: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  unfolding join_def
  by (metis is_lub_bin lub_bin)

lemma join_self[simp]: "x \<squnion> x = x"
  unfolding join_def  by auto
end

lemma join_commute:  "compatible x y \<Longrightarrow> x \<squnion> y = y \<squnion> x"
  unfolding compatible_def unfolding join_def by (metis insert_commute)

lemma lub_is_join:
  "{x, y} <<| z \<Longrightarrow> x \<squnion> y = z"
unfolding join_def by (metis lub_eqI)

lemma compatible_refl[simp]: "compatible x x"
  by (rule compatibleI[OF below_refl below_refl])

lemma join_mono:
  assumes "compatible a b"
  and "compatible c d"
  and "a \<sqsubseteq> c"
  and "b \<sqsubseteq> d"
  shows "a \<squnion> b \<sqsubseteq> c \<squnion> d"
proof-
  from assms obtain x y where "{a, b} <<| x" "{c, d} <<| y" unfolding compatible_def by auto
  with assms have "a \<sqsubseteq> y" "b \<sqsubseteq> y" by (metis below.r_trans is_lubD1 is_ub_insert)+
  with `{a, b} <<| x` have "x \<sqsubseteq> y" by (metis is_lub_below_iff is_lub_singleton is_ub_insert)
  moreover
  from `{a, b} <<| x` `{c, d} <<| y` have "a \<squnion> b = x" "c \<squnion> d = y" by (metis lub_is_join)+
  ultimately
  show ?thesis by simp
qed

lemma
  assumes "compatible x y"
  shows join_above1: "x \<sqsubseteq> x \<squnion> y" and join_above2: "y \<sqsubseteq> x \<squnion> y"
proof-
  from assms obtain z where "{x,y} <<| z" unfolding compatible_def by auto
  hence  "x \<squnion> y = z" and "x \<sqsubseteq> z" and "y \<sqsubseteq> z" apply (auto intro: lub_is_join) by (metis is_lubD1 is_ub_insert)+
  thus "x \<sqsubseteq> x \<squnion> y" and "y \<sqsubseteq> x \<squnion> y" by simp_all
qed

lemma
  assumes "compatible x y"
  shows compatible_above1: "compatible x (x \<squnion> y)" and compatible_above2: "compatible y (x \<squnion> y)"
proof-
  from assms obtain z where "{x,y} <<| z" unfolding compatible_def by auto
  hence  "x \<squnion> y = z" and "x \<sqsubseteq> z" and "y \<sqsubseteq> z" apply (auto intro: lub_is_join) by (metis is_lubD1 is_ub_insert)+
  thus  "compatible x (x \<squnion> y)" and  "compatible y (x \<squnion> y)" by (metis below.r_refl compatibleI)+
qed

lemma join_below:
  assumes "compatible x y"
  and "x \<sqsubseteq> a" and "y \<sqsubseteq> a"
  shows "x \<squnion> y \<sqsubseteq> a"
proof-
  from assms obtain z where z: "{x,y} <<| z" unfolding compatible_def by auto
  with assms have "z \<sqsubseteq> a" by (metis is_lub_below_iff is_ub_empty is_ub_insert)
  moreover
  from z have "x \<squnion> y = z" by (rule lub_is_join) 
  ultimately show ?thesis by simp
qed

lemma join_assoc:
  assumes "compatible x y"
  assumes "compatible x (y \<squnion> z)"
  assumes "compatible y z"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  apply (rule is_joinI)
  apply (rule join_mono[OF assms(1) assms(2) below_refl join_above1[OF assms(3)]])
  apply (rule below_trans[OF join_above2[OF assms(3)] join_above2[OF assms(2)]])
  apply (rule join_below[OF assms(2)])
  apply (erule rev_below_trans)
  apply (rule join_above1[OF assms(1)])
  apply (rule join_below[OF assms(3)])
  apply (erule rev_below_trans)
  apply (rule join_above2[OF assms(1)])
  apply assumption
  done

lemma join_idem[simp]: "compatible x y \<Longrightarrow> x \<squnion> (x \<squnion> y) = x \<squnion> y"
  apply (subst join_assoc[symmetric])
  apply (rule compatible_refl)
  apply (erule compatible_above1)
  apply assumption
  apply (subst join_self)
  apply rule
  done

lemma join_bottom[simp]: "x \<squnion> \<bottom> = x" "\<bottom> \<squnion> x = x"
  by (auto intro: is_joinI)

lemma compatible_adm2:
  shows "adm (\<lambda> y. compatible x y)"
proof(rule admI)
  fix Y
  assume c: "chain Y" and "\<forall>i.  compatible x (Y i)"
  hence a: "\<And> i. compatible x (Y i)" by auto
  show "compatible x (\<Squnion> i. Y i)"
  proof(rule compatibleI)
    have c2: "chain (\<lambda>i. x \<squnion> Y i)"
      apply (rule chainI)
      apply (rule join_mono[OF a a below_refl chainE[OF `chain Y`]])
      done
    show "x \<sqsubseteq> (\<Squnion> i. x \<squnion> Y i)"
      by (auto intro: admD[OF _ c2] join_above1[OF a])
    show "(\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. x \<squnion> Y i)"
      by (auto intro: admD[OF _ c] below_lub[OF c2 join_above2[OF a]])
    fix a
    assume "x \<sqsubseteq> a" and "(\<Squnion> i. Y i) \<sqsubseteq> a"
    show "(\<Squnion> i. x \<squnion> Y i) \<sqsubseteq> a"
      apply (rule lub_below[OF c2])
      apply (rule join_below[OF a `x \<sqsubseteq> a`])
      apply (rule below_trans[OF is_ub_thelub[OF c] `(\<Squnion> i. Y i) \<sqsubseteq> a`])
      done
  qed
qed

lemma compatible_adm1: "adm (\<lambda> x. compatible x y)"
  by (subst compatible_sym_iff, rule compatible_adm2)

lemma join_cont1:
  assumes "chain Y"
  assumes compat: "\<And> i. compatible (Y i) y"
  shows "(\<Squnion>i. Y i) \<squnion> y = (\<Squnion> i. Y i \<squnion> y)"
proof-
  have c: "chain (\<lambda>i. Y i \<squnion> y)"
    apply (rule chainI)
    apply (rule join_mono[OF compat compat chainE[OF `chain Y`] below_refl])
    done

  show ?thesis
    apply (rule is_joinI)
    apply (rule lub_mono[OF `chain Y` c join_above1[OF compat]])
    apply (rule below_lub[OF c join_above2[OF compat]])
    apply (rule lub_below[OF c])
    apply (rule join_below[OF compat])
    apply (metis lub_below_iff[OF `chain Y`])
    apply assumption
    done
qed

lemma join_cont2:
  assumes "chain Y"
  assumes compat: "\<And> i. compatible x (Y i)"
  shows "x \<squnion> (\<Squnion>i. Y i) = (\<Squnion> i. x \<squnion> Y i)"
proof-
  have c: "chain (\<lambda>i. x \<squnion> Y i)"
    apply (rule chainI)
    apply (rule join_mono[OF compat compat below_refl chainE[OF `chain Y`]])
    done

  show ?thesis
    apply (rule is_joinI)
    apply (rule below_lub[OF c join_above1[OF compat]])
    apply (rule lub_mono[OF `chain Y` c join_above2[OF compat]])
    apply (rule lub_below[OF c])
    apply (rule join_below[OF compat])
    apply assumption
    apply (metis lub_below_iff[OF `chain Y`])
    done
qed

lemma join_cont12:
  assumes "chain Y" and "chain Z"
  assumes compat: "\<And> i j. compatible (Y i) (Z j)"
  shows "(\<Squnion>i. Y i) \<squnion> (\<Squnion>i. Z i) = (\<Squnion> i. Y i  \<squnion> Z i)"
proof-
  have "(\<Squnion>i. Y i) \<squnion> (\<Squnion>i. Z i) = (\<Squnion>i. Y i \<squnion> (\<Squnion>j. Z j))"
    by (rule join_cont1[OF `chain Y` admD[OF compatible_adm2 `chain Z` compat]])
  also have "... = (\<Squnion>i j. Y i \<squnion> Z j)"
    by (subst join_cont2[OF `chain Z` compat], rule)
  also have "... = (\<Squnion>i. Y i \<squnion> Z i)"
    apply (rule diag_lub)
    apply (rule chainI, rule join_mono[OF compat compat chainE[OF `chain Y`] below_refl])
    apply (rule chainI, rule join_mono[OF compat compat below_refl chainE[OF `chain Z`]])
    done
  finally show ?thesis.
qed

context pcpo
begin
  lemma bot_compatible[simp]:
    "compatible x \<bottom>" "compatible \<bottom> x"
    unfolding compatible_def by (metis insert_commute is_lub_bin minimal)+
end

subsubsection {* Towards meets: Lower bounds *}

context po
begin
definition is_lb :: "'a set => 'a => bool" (infix ">|" 55) where
  "S >| x <-> (\<forall>y\<in>S. x \<sqsubseteq> y)"

lemma is_lbI: "(!!x. x \<in> S ==> l \<sqsubseteq> x) ==> S >| l"
  by (simp add: is_lb_def)

lemma is_lbD: "[|S >| l; x \<in> S|] ==> l \<sqsubseteq> x"
  by (simp add: is_lb_def)

lemma is_lb_empty [simp]: "{} >| l"
  unfolding is_lb_def by fast

lemma is_lb_insert [simp]: "(insert x A) >| y = (y \<sqsubseteq> x \<and> A >| y)"
  unfolding is_lb_def by fast

lemma is_lb_downward: "[|S >| l; y \<sqsubseteq> l|] ==> S >| y"
  unfolding is_lb_def by (fast intro: below_trans)

subsubsection {* Greatest lower bounds *}

definition is_glb :: "'a set => 'a => bool" (infix ">>|" 55) where
  "S >>| x <-> S >| x \<and> (\<forall>u. S >| u --> u \<sqsubseteq> x)"

definition glb :: "'a set => 'a" ("\<Sqinter>_" [60]60) where
  "glb S = (THE x. S >>| x)" 

text {* access to some definition as inference rule *}

lemma is_glbD1: "S >>| x ==> S >| x"
  unfolding is_glb_def by fast

lemma is_glbD2: "[|S >>| x; S >| u|] ==> u \<sqsubseteq> x"
  unfolding is_glb_def by fast

lemma (in po) is_glbI: "[|S >| x; !!u. S >| u ==> u \<sqsubseteq> x|] ==> S >>| x"
  unfolding is_glb_def by fast

lemma is_glb_above_iff: "S >>| x ==> u \<sqsubseteq> x <-> S >| u"
  unfolding is_glb_def is_lb_def by (metis below_trans)

text {* glbs are unique *}

lemma is_glb_unique: "[|S >>| x; S >>| y|] ==> x = y"
  unfolding is_glb_def is_lb_def by (blast intro: below_antisym)

text {* technical lemmas about @{term glb} and @{term is_glb} *}

lemma is_glb_glb: "M >>| x ==> M >>| glb M"
  unfolding glb_def by (rule theI [OF _ is_glb_unique])

lemma glb_eqI: "M >>| l ==> glb M = l"
  by (rule is_glb_unique [OF is_glb_glb])

lemma is_glb_singleton: "{x} >>| x"
  by (simp add: is_glb_def)

lemma glb_singleton [simp]: "glb {x} = x"
  by (rule is_glb_singleton [THEN glb_eqI])

lemma is_glb_bin: "x \<sqsubseteq> y ==> {x, y} >>| x"
  by (simp add: is_glb_def)

lemma glb_bin: "x \<sqsubseteq> y ==> glb {x, y} = x"
  by (rule is_glb_bin [THEN glb_eqI])

lemma is_glb_maximal: "[|S >| x; x \<in> S|] ==> S >>| x"
  by (erule is_glbI, erule (1) is_lbD)

lemma glb_maximal: "[|S >| x; x \<in> S|] ==> glb S = x"
  by (rule is_glb_maximal [THEN glb_eqI])
end

lemma (in cpo) Meet_insert: "S >>| l \<Longrightarrow> {x, l} >>| l2 \<Longrightarrow> insert x S >>| l2"
  apply (rule is_glbI)
  apply (metis is_glb_above_iff is_glb_def is_lb_insert)
  by (metis is_glb_above_iff is_glb_def is_glb_singleton is_lb_insert)

subsubsection {* Type classes for various kinds of meets *}

text {* Binary, hence finite meets. *}

class Finite_Meet_cpo = cpo +
  assumes binary_meet_exists: "\<exists> l. l \<sqsubseteq> x \<and> l \<sqsubseteq> y \<and> (\<forall> z. z \<sqsubseteq> x \<longrightarrow> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> l)"
begin

  lemma binary_meet_exists': "\<exists>l. {x, y} >>| l"
    using binary_meet_exists[of x y]
    unfolding is_glb_def is_lb_def
    by auto

  lemma finite_meet_exists:
    assumes "S \<noteq> {}"
    and "finite S"
    shows "\<exists>x. S >>| x"
  using `S \<noteq> {}`
  apply (induct rule: finite_induct[OF `finite S`])
  apply (erule notE, rule refl)[1]
  apply (case_tac "F = {}")
  apply (metis is_glb_singleton)
  apply (metis Meet_insert binary_meet_exists')
  done
end

text {* Meets for finite nonempty sets with a lower bound. *}

class Bounded_Nonempty_Meet_cpo = cpo +
  assumes bounded_nonempty_meet_exists: "S \<noteq> {} \<Longrightarrow> (\<exists>z. S >| z) \<Longrightarrow> \<exists>x. S >>| x"
begin
  lemma nonempty_ub_implies_lub_exists:
  assumes "S <| u"
  assumes "S \<noteq> {}"
  shows "\<exists> z. S <<| z"
  proof-
    have "{u. S <| u} \<noteq> {}" using assms(1) by auto
    hence "\<exists>x. {u. S <| u} >>| x"
      apply (rule bounded_nonempty_meet_exists)
      by (metis CollectE assms(2) equals0I is_lbI is_ub_def)
    then obtain lu where lb: "{u. S <| u} >>| lu" by auto
    hence "S <| lu"
      by (metis is_glb_above_iff is_lb_def is_ub_def mem_Collect_eq)
    hence "S <<| lu"
      by (metis (full_types) is_lubI is_glbD1 is_lb_def lb mem_Collect_eq)
    thus ?thesis ..
  qed

  lemma ub_implies_compatible:
    "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> compatible x y"
    unfolding compatible_def
    by (rule nonempty_ub_implies_lub_exists, auto)
end

text {* Meets for finite nonempty sets. *}

class Nonempty_Meet_cpo = cpo +
  assumes nonempty_meet_exists: "S \<noteq> {} \<Longrightarrow> \<exists>x. S >>| x"
begin
  lemma ub_implies_lub_exists:
  assumes "S <| u"
  shows "\<exists> z. S <<| z"
  proof-
    have "{u. S <| u} \<noteq> {}" using assms by auto
    from nonempty_meet_exists[OF this]
    obtain lu where lb: "{u. S <| u} >>| lu" by auto
    hence "S <| lu"
      by (metis is_glb_above_iff is_lb_def is_ub_def mem_Collect_eq)
    hence "S <<| lu"
      by (metis (full_types) is_lubI is_glbD1 is_lb_def lb mem_Collect_eq)
    thus ?thesis ..
  qed
end

context Nonempty_Meet_cpo
begin
  subclass Bounded_Nonempty_Meet_cpo
  apply default by (metis nonempty_meet_exists)
end

lemma (in Bounded_Nonempty_Meet_cpo) compatible_down_closed:
    assumes "compatible x y"
    and "z \<sqsubseteq> x"
    shows "compatible z y"
proof-
    from assms(1) obtain ub where "{x, y} <<| ub" by (metis compatible_def)
    hence "{x,y} <| ub" by (metis is_lubD1)
    hence "{z,y} <| ub" using assms(2) by (metis is_ub_insert rev_below_trans)
    thus ?thesis unfolding compatible_def by (metis insert_not_empty nonempty_ub_implies_lub_exists)
qed

lemma (in Bounded_Nonempty_Meet_cpo) compatible_down_closed2:
    assumes "compatible y x"
    and "z \<sqsubseteq> x"
    shows "compatible y z"
proof-
    from assms(1) obtain ub where "{y, x} <<| ub" by (metis compatible_def)
    hence "{y,x} <| ub" by (metis is_lubD1)
    hence "{y,z} <| ub" using assms(2) by (metis is_ub_insert rev_below_trans)
    thus ?thesis unfolding compatible_def by (metis insert_not_empty nonempty_ub_implies_lub_exists)
qed

lemma join_mono':
  assumes  "compatible (c::'a::Bounded_Nonempty_Meet_cpo) d"
  and "a \<sqsubseteq> c"
  and "b \<sqsubseteq> d"
  shows "a \<squnion> b \<sqsubseteq> c \<squnion> d"
  apply (rule join_mono[OF _ assms(1) assms(2) assms(3)])
  by (metis assms(1) assms(2) assms(3) compatible_down_closed2 compatible_sym)

subsubsection {* Bifinite domains with finite nonempty meets have arbitrary nonempty meets. *}

class Finite_Meet_bifinite_cpo = Finite_Meet_cpo + bifinite

lemma is_ub_range:
     "S >| u \<Longrightarrow> Rep_cfun f ` S >| f \<cdot> u"
  apply (rule is_lbI)
  apply (erule imageE)
  by (metis monofun_cfun_arg is_lbD)

lemma (in approx_chain) lub_approx_arg: "(\<Squnion>i. approx i \<cdot> u ) = u"
  by (metis chain_approx lub_ID_reach lub_approx)

instance Finite_Meet_bifinite_cpo \<subseteq> Nonempty_Meet_cpo
proof (default)
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" by auto
  fix S
  assume "(S :: 'a set) \<noteq> {}"
  have "\<And>i. \<exists> l . Rep_cfun (approx i) ` S >>|l"
    apply (rule finite_meet_exists)
    using `S \<noteq> {}` apply auto[1]
    using  finite_deflation.finite_range[OF approx_chain.finite_deflation_approx[OF `approx_chain approx`]]
    by (metis (full_types) image_mono rev_finite_subset top_greatest)
  then obtain Y where Y_is_glb: "\<And>i. Rep_cfun (approx i) ` S >>| Y i" by metis
  
  have "chain Y"
    apply (rule chainI)
    apply (subst is_glb_above_iff[OF Y_is_glb])
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule rev_below_trans[OF monofun_cfun_fun[OF chainE[OF approx_chain.chain_approx[OF `approx_chain approx`]]]])
    apply (rule is_lbD[OF is_glbD1[OF Y_is_glb]])
    apply (erule imageI)
    done
  
  have "S >| Lub Y"
  proof(rule is_lbI, rule lub_below[OF `chain Y`])
    fix x i
    assume "x \<in> S"
    hence "Y i \<sqsubseteq> approx i \<cdot> x"
      by (rule imageI[THEN is_lbD[OF is_glbD1[OF Y_is_glb]]])
    also have "approx i \<cdot> x \<sqsubseteq> x"
      by (rule  approx_chain.approx_below[OF `approx_chain approx`])
    finally
    show "Y i \<sqsubseteq> x".
  qed

  have "S >>| Lub Y"
  proof (rule is_glbI[OF `S >| Lub Y`])
    fix u
    assume "S >| u"
    hence "\<And> i. Rep_cfun (approx i) ` S >| approx i \<cdot> u"
      by (rule is_ub_range)
    hence "\<And> i.  approx i \<cdot> u \<sqsubseteq> Y i"
      by (rule is_glbD2[OF Y_is_glb])
    hence "(\<Squnion>i. approx i \<cdot> u ) \<sqsubseteq> Lub Y" 
      by (rule lub_mono[OF
            ch2ch_Rep_cfunL[OF approx_chain.chain_approx[OF `approx_chain approx`]]
            `chain Y`
            ])
    thus "u \<sqsubseteq> Lub Y" 
      by (metis approx_chain.lub_approx_arg[OF `approx_chain approx`])
  qed
  thus "\<exists>x. S >>| x"..
qed

end
