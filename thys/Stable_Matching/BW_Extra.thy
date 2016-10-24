theory BW_Extra
imports
  "~~/src/HOL/Library/Product_Order"
  "~~/src/HOL/Library/Bourbaki_Witt_Fixpoint"
  "~~/src/HOL/Library/While_Combinator"
begin

(* FIXME in Isabelle/hg fba08009ff3e (after Isabelle2016). Delete this file. *)

(* Inductive *)

lemma lfp_eqI:
  assumes "mono F"
  assumes "F x = x"
  assumes "\<And>z. F z = z \<Longrightarrow> x \<le> z"
  shows "lfp F = x"
by (rule antisym) (simp_all add: assms lfp_lowerbound lfp_unfold[symmetric])

lemma gfp_eqI:
  assumes "mono F"
  assumes "F x = x"
  assumes "\<And>z. F z = z \<Longrightarrow> z \<le> x"
  shows "gfp F = x"
by (rule antisym) (simp_all add: assms gfp_upperbound gfp_unfold[symmetric])

lemma gfp_const: "gfp (\<lambda>x. t) = t"
by (rule gfp_unfold) (simp add: mono_def)

(* Library/Product_Order *)

text \<open>
  Bekic's Theorem: Simultaneous fixed points over pairs
  can be written in terms of separate fixed points.
  Transliterated from HOLCF.Fix
\<close>

lemma lfp_prod:
  fixes F :: "'a::complete_lattice \<times> 'b::complete_lattice \<Rightarrow> 'a \<times> 'b"
  assumes "mono F"
  shows "lfp F = (lfp (\<lambda>x. fst (F (x, lfp (\<lambda>y. snd (F (x, y)))))),
                 (lfp (\<lambda>y. snd (F (lfp (\<lambda>x. fst (F (x, lfp (\<lambda>y. snd (F (x, y)))))), y)))))"
  (is "lfp F = (?x, ?y)")
proof(rule lfp_eqI[OF assms])
  have 1: "fst (F (?x, ?y)) = ?x"
    by (rule trans [symmetric, OF lfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono lfp_mono)+
  have 2: "snd (F (?x, ?y)) = ?y"
    by (rule trans [symmetric, OF lfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono lfp_mono)+
  from 1 2 show "F (?x, ?y) = (?x, ?y)" by (simp add: prod_eq_iff)
next
  fix z assume F_z: "F z = z"
  obtain x y where z: "z = (x, y)" by (rule prod.exhaust)
  from F_z z have F_x: "fst (F (x, y)) = x" by simp
  from F_z z have F_y: "snd (F (x, y)) = y" by simp
  let ?y1 = "lfp (\<lambda>y. snd (F (x, y)))"
  have "?y1 \<le> y" by (rule lfp_lowerbound, simp add: F_y)
  hence "fst (F (x, ?y1)) \<le> fst (F (x, y))"
    by (simp add: assms fst_mono monoD)
  hence "fst (F (x, ?y1)) \<le> x" using F_x by simp
  hence 1: "?x \<le> x" by (simp add: lfp_lowerbound)
  hence "snd (F (?x, y)) \<le> snd (F (x, y))"
    by (simp add: assms snd_mono monoD)
  hence "snd (F (?x, y)) \<le> y" using F_y by simp
  hence 2: "?y \<le> y" by (simp add: lfp_lowerbound)
  show "(?x, ?y) \<le> z" using z 1 2 by simp
qed

lemma gfp_prod:
  fixes F :: "'a::complete_lattice \<times> 'b::complete_lattice \<Rightarrow> 'a \<times> 'b"
  assumes "mono F"
  shows "gfp F = (gfp (\<lambda>x. fst (F (x, gfp (\<lambda>y. snd (F (x, y)))))),
                 (gfp (\<lambda>y. snd (F (gfp (\<lambda>x. fst (F (x, gfp (\<lambda>y. snd (F (x, y)))))), y)))))"
  (is "gfp F = (?x, ?y)")
proof(rule gfp_eqI[OF assms])
  have 1: "fst (F (?x, ?y)) = ?x"
    by (rule trans [symmetric, OF gfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono gfp_mono)+
  have 2: "snd (F (?x, ?y)) = ?y"
    by (rule trans [symmetric, OF gfp_unfold])
       (blast intro!: monoI monoD[OF assms(1)] fst_mono snd_mono Pair_mono gfp_mono)+
  from 1 2 show "F (?x, ?y) = (?x, ?y)" by (simp add: prod_eq_iff)
next
  fix z assume F_z: "F z = z"
  obtain x y where z: "z = (x, y)" by (rule prod.exhaust)
  from F_z z have F_x: "fst (F (x, y)) = x" by simp
  from F_z z have F_y: "snd (F (x, y)) = y" by simp
  let ?y1 = "gfp (\<lambda>y. snd (F (x, y)))"
  have "y \<le> ?y1" by (rule gfp_upperbound, simp add: F_y)
  hence "fst (F (x, y)) \<le> fst (F (x, ?y1))"
    by (simp add: assms fst_mono monoD)
  hence "x \<le> fst (F (x, ?y1))" using F_x by simp
  hence 1: "x \<le> ?x" by (simp add: gfp_upperbound)
  hence "snd (F (x, y)) \<le> snd (F (?x, y))"
    by (simp add: assms snd_mono monoD)
  hence "y \<le> snd (F (?x, y))" using F_y by simp
  hence 2: "y \<le> ?y" by (simp add: gfp_upperbound)
  show "z \<le> (?x, ?y)" using z 1 2 by simp
qed

(* Library/Complete_Partial_Order2 ? -- Chain-finite types. Need order hypotheses from somewhere. *)

lemma (in ccpo) admissible_chfin:
  assumes "(\<forall>S. Complete_Partial_Order.chain op \<le> S \<longrightarrow> finite S)"
  shows "ccpo.admissible Sup op \<le> P"
using assms in_chain_finite by (blast intro: ccpo.admissibleI)

(* Library/Bourbaki_Witt_Fixpoint *)

lemma in_ChainsD:
  assumes "M \<in> Chains r"
  assumes "x \<in> M" and "y \<in> M"
  shows "(x, y) \<in> r \<or> (y, x) \<in> r"
using assms unfolding Chains_def by fast

context bourbaki_witt_fixpoint
begin

(* from Isabelle/hg 7c56e4a1ad0c, soon after Isabelle2016 was released.
   later cleanup (delete assumption a) changes the def of fixp_above *)

lemma in_Chains_conv_chain: "M \<in> Chains r \<longleftrightarrow> Complete_Partial_Order.chain (\<lambda>x y. (x, y) \<in> r) M"
by(simp add: Chains_def chain_def)

lemma fixp_above_induct [case_names adm closed base step]:
  assumes adm: "ccpo.admissible lub (\<lambda>x y. (x, y) \<in> leq) P"
  and a: "a \<in> Field leq"
  and base: "P a"
  and step: "\<And>x. P x \<Longrightarrow> P (f x)"
  shows "P (fixp_above a)"
using adm chain_iterates_above[OF a] unfolding fixp_above_def in_Chains_conv_chain
proof(rule ccpo.admissibleD)
  have "a \<in> iterates_above a" ..
  then show "iterates_above a \<noteq> {}" by(auto)
  show "P x" if "x \<in> iterates_above a" for x using that
    by induction(auto intro: base step simp add: in_Chains_conv_chain dest: ccpo.admissibleD[OF adm])
qed

(* Connect with the while combinator for executability on chain-finite lattices. *)

(* Translation from Partial_Function. I don't think we can satisfy the ccpo class axioms. *)
lemma in_Chains_finite:
  assumes "M \<in> Chains leq"
  assumes "M \<noteq> {}"
  assumes "finite M"
  shows "lub M \<in> M"
using assms(3,1,2)
proof induction
  case empty thus ?case by simp
next
  case (insert x M)
  note chain = \<open>insert x M \<in> Chains leq\<close>
  show ?case
  proof(cases "M = {}")
    case True thus ?thesis
      using chain in_ChainsD leq_antisym lub_least lub_upper by fastforce
  next
    case False
    from chain have chain': "M \<in> Chains leq"
      using in_Chains_subset subset_insertI by blast
    hence "lub M \<in> M" using False by(rule insert.IH)
    show ?thesis
    proof(cases "(x, lub M) \<in> leq")
      case True
      have "(lub (insert x M), lub M) \<in> leq" using chain
        by (rule lub_least) (auto simp: True intro: lub_upper[OF chain'])
      with False have "lub (insert x M) = lub M"
        using lub_upper[OF chain] lub_least[OF chain'] by (blast intro: leq_antisym)
      with \<open>lub M \<in> M\<close> show ?thesis by simp
    next
      case False
      with in_ChainsD[OF chain, of x "lub M"] \<open>lub M \<in> M\<close>
      have "lub (insert x M) = x"
        by - (rule leq_antisym, (blast intro: FieldI2 chain chain' insert.prems(2) leq_refl leq_trans lub_least lub_upper)+)
      thus ?thesis by simp
    qed
  qed
qed

lemma fun_pow_iterates_above:
  shows "(f ^^ k) a \<in> iterates_above a"
using iterates_above.base iterates_above.step by (induct k) simp_all

lemma chfin_iterates_above_fun_pow:
  assumes "x \<in> iterates_above a"
  assumes "\<forall>M \<in> Chains leq. finite M"
  shows "\<exists>j. x = (f ^^ j) a"
using assms(1)
proof induct
  case base then show ?case by (simp add: exI[where x=0])
next
  case (step x) then obtain j where "x = (f ^^ j) a" by blast
  with step(1) show ?case by (simp add: exI[where x="Suc j"])
next
  case (Sup M) with in_Chains_finite assms(2) show ?case by blast
qed

lemma chfin_iterates_above_fun_pow_iff:
  assumes "\<forall>M \<in> Chains leq. finite M"
  shows "x \<in> iterates_above a \<longleftrightarrow> (\<exists>j. x = (f ^^ j) a)"
using chfin_iterates_above_fun_pow fun_pow_iterates_above assms by blast

lemma fixp_above_Kleene_iter_ex:
  assumes "a \<in> Field leq"
  assumes "(\<forall>M \<in> Chains leq. finite M)"
  obtains k where "fixp_above a = (f ^^ k) a"
using assms by atomize_elim (simp add: chfin_iterates_above_fun_pow fixp_iterates_above)

lemma funpow_Field_leq:
  assumes "a \<in> Field leq"
  shows "(f ^^ k) a \<in> Field leq"
using assms by (induct k) (auto intro: increasing FieldI2)

lemma funpow_prefix:
  assumes "j < k"
  assumes "a \<in> Field leq"
  shows "((f ^^ j) a, (f ^^ k) a) \<in> leq"
using \<open>j < k\<close>
proof(induct k)
  case (Suc k)
  with leq_trans[OF _ increasing[OF funpow_Field_leq]] funpow_Field_leq increasing \<open>a \<in> Field leq\<close>
  show ?case by simp (metis less_antisym)
qed simp

lemma funpow_suffix:
  assumes "a \<in> Field leq"
  assumes "(f ^^ Suc k) a = (f ^^ k) a"
  shows "((f ^^ (j + k)) a, (f ^^ k) a) \<in> leq"
using funpow_Field_leq[OF assms(1)] assms
by (induct j) (simp_all del: funpow.simps add: funpow_Suc_right funpow_add leq_refl)

lemma funpow_stability:
  assumes "a \<in> Field leq"
  assumes "(f ^^ Suc k) a = (f ^^ k) a"
  shows "((f ^^ j) a, (f ^^ k) a) \<in> leq"
using funpow_prefix funpow_suffix[where j="j - k" and k=k] assms by (cases "j < k") simp_all

lemma fixp_above_Kleene_iter:
  assumes "a \<in> Field leq"
  assumes "\<forall>M \<in> Chains leq. finite M" (* convenient but surely not necessary *)
  assumes "(f ^^ Suc k) a = (f ^^ k) a"
  shows "fixp_above a = (f ^^ k) a"
proof(rule leq_antisym)
  show "(fixp_above a, (f ^^ k) a) \<in> leq"
    unfolding fixp_above_def
    by (rule lub_least)
       (auto simp: assms chain_iterates_above chfin_iterates_above_fun_pow_iff funpow_stability[OF assms(1,3)]
            intro: iterates_above.base)
next
  show "((f ^^ k) a, fixp_above a) \<in> leq"
    unfolding fixp_above_def
    by (rule lub_upper) (simp_all add: assms(1) chain_iterates_above fun_pow_iterates_above)
qed

lemma funpow_in_Chains:
  assumes "a \<in> Field leq"
  shows "{(f ^^ k) a |k. True} \<in> Chains leq"
using chain_iterates_above[OF assms] fun_pow_iterates_above
by (blast intro: ChainsI dest: in_ChainsD)

lemma chfin_wf:
  assumes "a \<in> Field leq"
  assumes "\<forall>M \<in> Chains leq. finite M"
  shows "wf {(f ((f ^^ k) a), (f ^^ k) a) |k. f ((f ^^ k) a) \<noteq> (f ^^ k) a}"
apply (rule wf_measure[where f="\<lambda>b. card {(f ^^ j) a |j. (b, (f ^^ j) a) \<in> leq}", THEN wf_subset])
apply (auto simp: set_eq_iff intro!: psubset_card_mono[OF finite_subset[OF _ bspec[OF assms(2) funpow_in_Chains[OF assms(1)]]]])
  apply metis
 using assms(1) funpow_Field_leq increasing leq_trans apply metis
using assms(1) funpow_Field_leq increasing leq_antisym leq_refl apply metis
done

lemma while_option_finite_increasing:
  assumes "a \<in> Field leq"
  assumes "\<forall>M \<in> Chains leq. finite M"
  shows "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f a = Some P"
by (rule wf_rel_while_option_Some[OF chfin_wf[OF assms], where P="\<lambda>A. (\<exists>k. A = (f ^^ k) a) \<and> (A, f A) \<in> leq" and s="a"])
   (auto simp: increasing assms FieldI2 chfin_iterates_above_fun_pow fun_pow_iterates_above iterates_above.step
        intro: exI[where x=0])

lemma fixp_above_the_while_option:
  assumes "a \<in> Field leq"
  assumes "\<forall>M \<in> Chains leq. finite M"
  shows "fixp_above a = the(while_option (\<lambda>A. f A \<noteq> A) f a)"
proof -
  obtain P where "while_option (\<lambda>A. f A \<noteq> A) f a = Some P"
    using while_option_finite_increasing[OF assms(1,2)] by blast
  with while_option_stop2[OF this] fixp_above_Kleene_iter[OF assms]
  show ?thesis by fastforce
qed

lemma fixp_above_conv_while:
  assumes "a \<in> Field leq"
  assumes "\<forall>M \<in> Chains leq. finite M"
  shows "fixp_above a = while (\<lambda>A. f A \<noteq> A) f a"
unfolding while_def using assms by (rule fixp_above_the_while_option)

end

lemma bourbaki_witt_fixpoint_complete_latticeI:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "\<And>x. x \<le> f x"
  shows "bourbaki_witt_fixpoint Sup {(x, y). x \<le> y} f"
by (rule bourbaki_witt_fixpoint.intro)
   (auto simp: assms Sup_upper order_on_defs Field_def intro: refl_onI transI antisymI Sup_least)

end
