
theory FixRestr
  imports HOLCF
begin

find_consts name:funpow
term Nat.funpow

definition chainFrom :: "('a => 'a) => ('a :: cpo) => bool"
  where "chainFrom F x = ((\<forall>n. (F^^n) x \<sqsubseteq> F ((F^^n) x)) \<and> (F (\<Squnion> i. ((F^^i) x)) = (\<Squnion> i. F ((F^^i) x))))"


lemma chainFrom_chain [simp]: "chainFrom F x \<Longrightarrow> chain (\<lambda>i. (F^^i) x)"
  by (rule chainI, auto simp add: chainFrom_def)

lemma iterate_stays_above: "chainFrom F x  \<Longrightarrow> x \<sqsubseteq> (F^^n) x"
  apply (drule chainFrom_chain)
  apply (rule nat_induct)
  apply (auto simp add: chain_def)
  by (metis rev_below_trans)

lemma lub_chainFrom_arg: "chainFrom F x \<Longrightarrow> F (\<Squnion> i. ((F^^i) x)) = (\<Squnion> i. F ((F^^i) x))" 
  by (simp add: chainFrom_def)


definition
  "fixR" :: "'a \<Rightarrow> ('a::cpo => 'a) \<Rightarrow> 'a" where
  "fixR x F = (if chainFrom F x then (\<Squnion>i. (F^^i) x) else x)"

lemma iterate_below_fix: "chainFrom F x  \<Longrightarrow> (F^^n) x \<sqsubseteq> fixR x F"
  unfolding fixR_def
  apply (subst if_P, assumption)
  using chainFrom_chain
  by (rule is_ub_thelub)

lemma fix_eq: "chainFrom F x \<Longrightarrow> fixR x F = F (fixR x F)"
  apply (simp add: fixR_def)
  apply (subst lub_range_shift [of _ 1, symmetric])
  apply (erule chainFrom_chain)
  thm contlub_cfun_arg
  apply (subst lub_chainFrom_arg, assumption)
  apply (drule chainFrom_chain)
  apply (simp add: chain_def)
  done

lemma fixR_ind: "\<lbrakk> adm P; P x; chainFrom F x; \<And>i. \<lbrakk>x \<sqsubseteq> (F^^i) x ; P ((F^^i) x)\<rbrakk> \<Longrightarrow> P (F ((F^^i) x)) \<rbrakk> \<Longrightarrow> P (fixR x F)"
  unfolding fixR_def
  apply (subst if_P, assumption)
  apply (erule admD)
  apply (erule chainFrom_chain)
  apply (rule nat_induct)
  apply (simp_all add: iterate_stays_above)
  done

lemma fixR_ind2:
  assumes adm: "adm P"
  assumes above: "chainFrom F x"
  assumes 0: "P x" and 1: "P (F x)"
  assumes step: "!!y. \<lbrakk>x \<sqsubseteq> y ; P y; P (F y)\<rbrakk> \<Longrightarrow> P (F (F y))"
  shows "P (fixR x F)"
  unfolding fixR_def
  apply (subst if_P, fact)
  apply (rule admD [OF adm chainFrom_chain[OF above]])
  apply (rule nat_less_induct)
  apply (case_tac n)
  apply (simp add: 0)
  apply (case_tac nat)
  apply (simp add: 1)
  apply (frule_tac x=nat in spec)
  apply (simp add: step iterate_stays_above[OF above])
done

lemma parallel_fixR_ind:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes aboveF: "chainFrom F x1"
  assumes aboveG: "chainFrom G x2"
  assumes base: "P x1 x2"
  assumes step: "!!y z. \<lbrakk> x1 \<sqsubseteq> y ; x2 \<sqsubseteq> z; P y z \<rbrakk> \<Longrightarrow> P (F y) (G z)"
  shows "P (fixR x1 F) (fixR x2 G)"
proof -
  from adm have adm': "adm (split P)"
    unfolding split_def .
  have "!!i. P ((F^^i) x1) ((G^^i) x2)"
    by (induct_tac i, simp add: base, simp add: step iterate_stays_above[OF aboveF] iterate_stays_above[OF aboveG])
  hence "!!i. split P ((F^^i) x1, (G^^i) x2)"
    by simp
  hence "split P (\<Squnion>i. ((F^^i) x1, (G^^i) x2))"
    apply - apply (rule admD [OF adm']) by(auto intro: ch2ch_Pair simp add: chainFrom_chain[OF aboveF] chainFrom_chain[OF aboveG])
  hence "split P (\<Squnion>i. ((F^^i) x1), \<Squnion>i. (G^^i) x2)"
    by (simp add: lub_Pair chainFrom_chain[OF aboveF] chainFrom_chain[OF aboveG])
  hence "P (\<Squnion>i. (F^^i) x1) (\<Squnion>i. (G^^i) x2)"
    by simp
  thus "P (fixR x1 F) (fixR x2 G)"
    using aboveF aboveG
    by (simp add: fixR_def)
qed


(*
lemma fix1_cont2cont[simp,cont2cont]:"\<lbrakk> cont F ; cont G ; \<And> y. G y \<sqsubseteq> (F y) \<cdot> (G y) \<rbrakk> \<Longrightarrow> cont (\<lambda>y. fix1 (G y) (F y))"
  unfolding fix1_def by auto
*)

lemma[simp]: "chainFrom (\<lambda>_. x) x"
  unfolding chainFrom_def
  by (metis funpow_swap1 lub_const po_eq_conv)

lemma[simp]: "(fixR x (\<lambda> _. x)) = x"
  by (rule fixR_ind, auto)

(*
lemma fix_least_below: "x \<sqsubseteq> F \<cdot> x \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> F\<cdot>y \<sqsubseteq> y \<Longrightarrow> fix1 x F \<sqsubseteq> y"
  apply (simp add: fix1_def)
  apply (rule lub_below)
  apply (erule chain_iterate_from)
  apply (induct_tac i)
  apply simp
  apply simp
  apply (erule rev_below_trans) back
  apply (erule monofun_cfun_arg)
  done

lemmas start_below_fix1[simp] = iterate_below_fix[where n = 0, simplified]

lemma fix1_alt_start:
  assumes "x \<sqsubseteq> y" and "y \<sqsubseteq> F \<cdot> x"
  shows "fix1 x F = fix1 y F"
proof(rule below_antisym)
  have "x \<sqsubseteq> F \<cdot> x" using assms by (metis below.r_trans)
  have "y \<sqsubseteq> F \<cdot> y" using assms by (metis monofun_cfun_arg rev_below_trans)
  show "fix1 x F \<sqsubseteq> fix1 y F"
    by (rule parallel_fix1_ind[OF _ `x \<sqsubseteq> F \<cdot> x` `y \<sqsubseteq> F \<cdot> y`], auto intro: monofun_cfun_arg assms(1))
  show "fix1 y F \<sqsubseteq> fix1 x F"
    apply (rule fix_least_below[OF `y \<sqsubseteq> F \<cdot> y`])    
    apply (subst fix_eq[OF `x \<sqsubseteq> F\<cdot>x`])
    apply (rule below_trans[OF  `y \<sqsubseteq> F \<cdot> x`])
    apply (rule monofun_cfun_arg)
    apply (rule start_below_fix1[OF `x \<sqsubseteq> F\<cdot>x`])
    apply (subst fix_eq[OF `x \<sqsubseteq> F\<cdot>x`, symmetric])
    apply (rule below_refl)
    done
qed
*)

end
