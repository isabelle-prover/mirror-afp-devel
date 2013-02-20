theory "Correctness-Counterexample"
imports "Denotational-Props" Launchbury
begin

text {* In this theory we show that Theorem 2 in Launchbury's original paper \cite{launchbury} does not hold if one
takes @{text "\<squnion>"} to mean the least upper bound, by giving a counter example. *}

theorem counterexample:
  assumes correct: "
    \<And> \<Gamma> e L \<Delta> z \<rho>.
    \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
     distinctVars \<Gamma>;
     fdom \<rho> - heapVars \<Gamma> \<subseteq> set L 
    \<rbrakk> \<Longrightarrow>
    \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
  shows False
proof-
  txt {* We need several variables; for two of them we require that they are different from each other. *}
  obtain x :: var where True by metis
  obtain a :: var where True by metis
  obtain b :: var where "atom b \<sharp> a" by (rule obtain_fresh)
    hence [simp]:"b \<noteq> a" by (simp add: fresh_at_base)

  txt {* Two distinct, but compatible elements of type @{typ Value}. *}  
  def id \<equiv> "Fn\<cdot>(\<Lambda> x. x)"
  def const \<equiv> "\<lambda> y. Fn\<cdot>(\<Lambda> x. y)"
  have "const id \<down>Fn id \<noteq> const \<bottom> \<down>Fn id"
    by (simp add: const_def id_def)
  hence "const id \<noteq> const \<bottom>" by auto
  have [simp]:"compatible (const id) (const \<bottom>)"
    by (auto intro: compatibleI[where z = "const id"] simp add: const_def id_def)


  txt {* This is how we instantiate the theorem. *}
  def e \<equiv> "Var x"
  def z \<equiv> "Lam [a]. let b be Var b in Var b"
  def \<Gamma> \<equiv> "[(x, z)]"
  def \<Delta> \<equiv> "[(x, z)]"
  def \<rho> \<equiv> "fempty( x f\<mapsto> const id )"

  txt {* Establish the denotation of our terms (this involves picking fresh variables). *}
  have [simp]: "\<And> \<rho>. \<lbrakk>let b be Var b in Var b\<rbrakk>\<^bsub>\<rho>\<^esub> = \<bottom>"
  proof-
    fix \<rho> :: Env

    obtain b' :: var where fresh: "atom b' \<sharp> (b,\<rho>)" by (rule obtain_fresh)
    hence "b' \<noteq> b" "atom b' \<sharp> \<rho>" and [simp]: "b' \<notin> fdom \<rho>"
      by (auto simp add: fresh_Pair fresh_at_base sharp_Env)

    have "let b be Var b in Var b = let b' be Var b' in Var b'"
      apply simp
      apply (subst Abs_swap2[where a = "atom b" and b = "atom b'"])
      apply (auto simp add: exp_assn.bn_defs exp_assn.supp supp_Pair supp_at_base)
      done
    hence "\<lbrakk>let b be Var b in Var b\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>let b' be Var b' in Var b'\<rbrakk>\<^bsub>\<rho>\<^esub>" by metis
    also
    have "\<dots> = \<lbrakk>Var b'\<rbrakk>\<^bsub>\<lbrace>[(b', Var b')]\<rbrace>\<rho>\<^esub>"
      using `atom b' \<sharp> \<rho>`
      by (auto simp add: fresh_star_def exp_assn.bn_defs)
    also have "\<dots> = \<lbrace>[(b', Var b')]\<rbrace>\<rho> f! b'" by simp
    also have "\<dots> = \<bottom>"
      apply (rule HSem_ind)
        apply (rule adm_is_adm_on)
        apply auto[1]
      apply (simp add: to_bot_fmap_def)
      apply (subst the_lookup_join[OF rho_F_compat_fjc], assumption)
      apply simp_all
      done
    finally
    show "\<lbrakk>let b be Var b in Var b\<rbrakk>\<^bsub>\<rho>\<^esub> = \<bottom>".
  qed

  have [simp]: "\<And> \<rho>.  \<lbrakk>z\<rbrakk>\<^bsub>\<rho>\<^esub> = const \<bottom>"
  proof-
    fix \<rho> :: Env
    obtain a' :: var where fresh: "atom a' \<sharp> (b,\<rho>)" by (rule obtain_fresh)
    hence [simp]:"b \<noteq> a'" "atom a' \<sharp> \<rho>"
      by (auto simp add: fresh_Pair fresh_at_base sharp_Env)

    have "Lam [a]. let b be Var b in Var b = Lam [a']. let b be Var b in Var b"
      apply (simp add: fresh_Pair)
      by (metis `b \<noteq> a'` `b \<noteq> a` flip_at_base_simps(3) not_self_fresh)
    hence "\<lbrakk>z\<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk>Lam [a']. let b be Var b in Var b\<rbrakk>\<^bsub>\<rho>\<^esub>" unfolding z_def by metis
    also have "\<dots> = const \<bottom>"
      by (simp add: const_def)
    finally show "\<lbrakk>z\<rbrakk>\<^bsub>\<rho>\<^esub> = const \<bottom>".
  qed

  txt {* Establish that all joins occuring in the proof are well-defined. *}
  have cond: "HSem_cond'' \<Gamma> \<rho>"
    apply (intro fix_join_condI cont_compose[OF fmap_expand_cont cont2cont_heapToEnv] ESem_cont)
    apply (rule compatible_fmapI)
    apply (auto simp add: \<rho>_def \<Gamma>_def)
    done

  txt {* On the one hand, we have an equality according to theorem 2. *}
  have "\<Gamma> : e \<Down>\<^bsub>[]\<^esub> \<Delta> : z"
    unfolding \<Gamma>_def \<Delta>_def e_def z_def
    by (auto intro!: reds.intros)
  moreover
  have "distinctVars \<Gamma>" by (simp add: \<Gamma>_def)
  moreover
  have "fdom \<rho> - heapVars \<Gamma> \<subseteq> set []" by (simp add: \<rho>_def \<Gamma>_def)
  ultimately
  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule correct)
  moreover

  txt {* On the other hand, we have an inequality between the same terms. *}
  {
  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrace>\<Gamma>\<rbrace>\<rho> f! x"
    by (simp add: e_def)
  also have "\<dots> = (\<rho> f! x) \<squnion> (\<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)"
    by (simp add: \<Gamma>_def \<rho>_def the_lookup_HSem_both[OF cond, unfolded \<Gamma>_def \<rho>_def])
  also have "\<dots> = const id \<squnion> const \<bottom>"
    by (simp add: \<rho>_def)
  also have "\<dots> = const id"
    by (auto intro: larger_is_join1 simp add: const_def)
  also have "\<dots> \<noteq> const \<bottom>"
    by fact
  also have "const \<bottom> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" by simp  
  finally
  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<noteq> \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>".
  }
  ultimately
  
  txt {* So clearly, this is a contradiction. *}
  show False by metis
qed

end
