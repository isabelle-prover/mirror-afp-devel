theory "HOLCF-Set"
 imports HOLCF
begin

text {*
This theory provides variants of various HOLCF definitions with an explicit carrier set.
*}

default_sort cpo

subsubsection {* Sets forming (pointed) chain-complete partial orders *}

locale subcpo =
  fixes S :: "'a set"
  assumes cpo: "(\<forall>Y. (chain Y \<longrightarrow> (\<forall> i. Y i \<in> S) \<longrightarrow> (\<Squnion> i. Y i) \<in> S))"

lemma subcpoI:
  assumes "\<And> Y. \<lbrakk> chain Y; \<And> i. Y i \<in> S \<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  shows "subcpo S"
unfolding subcpo_def by (metis assms)

locale subpcpo = subcpo + 
  assumes bottom_exists: "\<exists> z \<in> S. \<forall> y \<in> S. z \<sqsubseteq> y"

lemma subpcpoI:
  assumes "\<And> Y. \<lbrakk> chain Y; \<And> i. Y i \<in> S \<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  assumes "b \<in> S"
  assumes "\<And> y. y \<in> S \<Longrightarrow> b \<sqsubseteq> y"
  shows "subpcpo S"
by (unfold_locales)(metis assms(1), metis assms(2,3))

lemma subpcpoI2:
  assumes "subcpo S"
  assumes "b \<in> S"
  assumes "\<And> y. y \<in> S \<Longrightarrow> b \<sqsubseteq> y"
  shows "subpcpo S"
by (unfold_locales)(metis subcpo_def assms(1), metis assms(2,3))

subsubsection {* Definitions *}

locale subpcpo_syn = 
  fixes S :: "'a set" 
begin

text {* This locale collects the definitions of various operations on subpcpo's without requiring that it is a subpcpo *}

definition chain_on :: "(nat => 'a) => bool" where
  "chain_on Y = (\<forall>i. Y i \<sqsubseteq> Y (Suc i) \<and> (\<forall>i. Y i \<in> S))"

definition
  adm_on :: "('a::cpo => bool) \<Rightarrow> bool" where
  "adm_on P = (\<forall>Y. chain_on Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i))"

definition bottom_of :: "'a"
  where "bottom_of = (THE x. x\<in>S \<and> (\<forall>y \<in> S. x \<sqsubseteq> y))"

definition
  monofun_on :: "('a => 'b) => bool" where
  "monofun_on f = (\<forall>x\<in>S. \<forall>y\<in>S. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

definition
  cont_on :: "('a::cpo => 'b::cpo) => bool"
where
  "cont_on f = (\<forall>Y. chain_on Y --> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i))"

definition 
  closed_on :: "('a::cpo => 'a::cpo) => bool"
where
  "closed_on f = (\<forall> x\<in> S. f x \<in> S)"

end

subsubsection {* Introduction and elimination rules *}

interpretation subpcpo_syn S for S.

lemma chain_onI:
  assumes  "\<And> i. Y i \<sqsubseteq> Y (Suc i)" and "\<And>i. Y i \<in> S"
  shows "chain_on S Y"
unfolding chain_on_def using assms by auto

lemma chain_on_is_on: "chain_on S Y \<Longrightarrow> Y i \<in> S"
  unfolding chain_on_def by auto

lemma chain_onE: "chain_on S Y \<Longrightarrow> Y i \<sqsubseteq> Y (Suc i)"
  unfolding chain_on_def by auto

lemma chain_on_is_chain: "chain_on S Y \<Longrightarrow> chain Y"
  unfolding chain_on_def chain_def by auto

lemma closed_onI[intro]:
  "[|\<And> x. x \<in> S \<Longrightarrow> f x \<in> S|] ==> closed_on S f"
by (simp add: closed_on_def)

lemma closed_onE[elim]: 
  "[|closed_on S f; x \<in> S|] ==> f x \<in> S"
by (simp add: closed_on_def)

lemma const_closed_on[simp,intro]:
  "x \<in> S \<Longrightarrow> closed_on S (\<lambda>_ . x)"
by (simp add: closed_on_def)

lemma iterate_closed_on: "closed_on S F \<Longrightarrow> closed_on S (F^^i)"
  unfolding closed_on_def
  by (induct i, auto)

lemma closed_on_Union:
  assumes "\<And> i. closed_on (S i) F"
  shows "closed_on (\<Union>i. S i) F"
  apply (rule closed_onI)
  apply (erule UN_E)
  apply (rule UN_I[OF UNIV_I])
  apply (erule closed_onE[OF assms])
  done

lemma monofun_onE: 
  "[|monofun_on S f; x\<in> S; y \<in> S; x \<sqsubseteq> y|] ==> f x \<sqsubseteq> f y"
by (simp add: monofun_on_def)

lemma monofun_onI: 
  "[|\<And>x y. \<lbrakk> x \<in> S; y \<in> S; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y|] ==> monofun_on S f"
by (simp add: monofun_on_def)

lemma monofun_on_cong:
  "\<lbrakk> \<And> x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> monofun_on S f = monofun_on S g"
  unfolding monofun_on_def by metis

lemma monofun_on_comp:
  assumes "monofun_on S1 f"
  and "monofun_on S2 g"
  and "f ` S1 \<subseteq> S2"
  shows "monofun_on S1 (\<lambda> x. g (f x))"
  using assms 
  unfolding monofun_on_def
  by (metis image_eqI in_mono)

lemma monofun_comp_monofun_on:
  "monofun f \<Longrightarrow> monofun_on S g \<Longrightarrow> monofun_on S (\<lambda> x. f (g x))"
  unfolding monofun_on_def
  by (auto elim:monofunE)

lemma monofun_comp_monofun_on2:
  assumes "monofun f"
  and "\<And> x. monofun (f x)"
  shows "monofun_on S g \<Longrightarrow> monofun_on S h \<Longrightarrow> monofun_on S (\<lambda> x. f (g x) (h x))"
  unfolding monofun_on_def
  by (auto intro: rev_below_trans[OF fun_belowD[OF monofunE[OF assms(1)]] monofunE[OF assms(2)]]) 

lemma cont_onI:
  "[|!!Y. chain_on S Y ==> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)|] ==> cont_on S f"
by (simp add: cont_on_def)

lemma ch2ch_monofun_on: "\<lbrakk>monofun_on S f; chain_on S Y\<rbrakk> \<Longrightarrow> chain (\<lambda>i. f (Y i))"
  apply (rule chainI)
  apply (erule monofun_onE)
  apply (erule chain_on_is_on)+
  apply (erule chain_onE)
  done

lemma cont_onE:
  "[|cont_on S f; chain_on S Y|] ==> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
by (simp add: cont_on_def)

lemma bin_chain_on: "\<lbrakk> x\<in>S; y\<in>S; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> chain_on S (\<lambda>i. if i=0 then x else y)"
  by (simp add: chain_on_def)

lemma binchain_cont_on:
  "\<lbrakk>cont_on S f; x \<in> S; y \<in> S ; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> range (\<lambda>i::nat. f (if i = 0 then x else y)) <<| f y"
apply (subgoal_tac "f (\<Squnion>i::nat. if i = 0 then x else y) = f y")
apply (erule subst)
apply (erule cont_onE)
apply (erule (2) bin_chain_on)
apply (rule_tac f=f in arg_cong)
apply (erule is_lub_bin_chain [THEN lub_eqI])
done

lemma cont_on2mono_on:
  "cont_on S F \<Longrightarrow> monofun_on S F"
apply (rule monofun_onI)
apply (drule (3) binchain_cont_on)
apply (drule_tac i=0 in is_lub_rangeD1)
apply simp
done

lemma cont_on2contlubE:
  "[|cont_on S f; chain_on S Y|] ==> f (\<Squnion> i. Y i) = (\<Squnion> i. f (Y i))"
apply (rule lub_eqI [symmetric])
apply (erule (1) cont_onE)
done

lemma cont_is_cont_on:
  "cont P \<Longrightarrow> cont_on S P"
  unfolding cont_on_def cont_def by (metis (full_types) chain_on_def po_class.chainI)

lemma cont_on_subset: "cont_on S1 f \<Longrightarrow> S2 \<subseteq> S1 \<Longrightarrow> cont_on S2 f"
  unfolding cont_on_def chain_on_def by (metis set_mp)

lemma adm_onD:
  assumes "adm_on S P"
  and "chain_on S Y"
  and"\<And>i. P (Y i)"
  shows "P (\<Squnion>i. Y i)"
using assms unfolding adm_on_def by auto

lemma adm_is_adm_on:
  "adm P \<Longrightarrow> adm_on S P"
  unfolding adm_def adm_on_def by (metis (full_types) chain_on_def po_class.chainI)

lemma ch2chain_on_monofun_on:
  shows "[|monofun_on S1 f; chain_on S1 Y; f ` S1 \<subseteq> S2 |] ==> chain_on S2 (\<lambda>i. f (Y i))"
proof-
  show "[|monofun_on S1 f; chain_on S1 Y; f ` S1 \<subseteq> S2 |] ==> chain_on S2 (\<lambda>i. f (Y i))"
    apply (rule chain_onI)
    apply (erule monofun_onE)
    apply (erule chain_on_is_on)+
    apply (erule chain_onE)
    apply (erule subsetD)
    apply (rule imageI)
    apply (erule chain_on_is_on)
    done
qed

lemma ch2ch_cont_on:
  assumes "cont_on S1 f" and "chain_on S1 Y" and "f ` S1 \<subseteq> S2"
  shows "chain_on S2 (\<lambda>i. f (Y i))"
  by (rule ch2chain_on_monofun_on[OF cont_on2mono_on[OF assms(1)] assms(2) assms(3)])

lemma ch2ch_cont_on':
  assumes "cont_on S1 f" and "chain_on S1 Y" and "closed_on S1 f"
  shows "chain_on S1 (\<lambda>i. f (Y i))"
  apply (rule ch2chain_on_monofun_on[OF cont_on2mono_on[OF assms(1)] assms(2)])
  by (metis assms(3) closed_on_def image_subsetI)

lemma adm_on_subst:
  assumes cont: "cont_on S1 t"  and closed: "t ` S1 \<subseteq> S2" and  adm: "adm_on S2 P" 
  shows "adm_on S1 (\<lambda>x. P (t x))"
proof-
  from cont closed adm
  show ?thesis
  by (auto simp add: adm_on_def cont_on2contlubE ch2ch_cont_on)
qed

lemma chain_on_product:
  assumes "chain_on S1 Y" and "chain_on S2 Z"
  shows "chain_on (S1 \<times> S2) (\<lambda> i. (Y i, Z i))"
  using assms by (auto simp add: chain_on_def)

subsubsection {* Locale relations *}

sublocale subpcpo < subpcpo_syn.

lemma subpcpo_is_subcpo: "subpcpo S \<Longrightarrow> subcpo S" unfolding subpcpo_def subcpo_def by simp

sublocale subpcpo < subcpo by (rule subpcpo_is_subcpo[OF subpcpo_axioms])

subsubsection {* Lemmas requiring chain-completeness *}

context subpcpo
begin

lemma shows bottom_of_there[simp]: "bottom_of \<in> S"
      and bottom_of_minimal[simp]: "\<And> x. x \<in> S \<Longrightarrow> bottom_of \<sqsubseteq> x"
proof-
  from bottom_exists obtain y where y: "y \<in> S \<and> (\<forall> x \<in> S. y \<sqsubseteq> x)" by auto
  hence "bottom_of \<in> S \<and> (\<forall>y \<in> S. bottom_of \<sqsubseteq> y)"
    unfolding bottom_of_def
    by (rule theI[where a = y], metis y po_eq_conv)
  thus "bottom_of \<in> S" and "\<And> x. x \<in> S \<Longrightarrow> bottom_of \<sqsubseteq> x" by metis+
qed

lemma bottom_ofI:
  assumes "x \<in> S"
  assumes "\<And> y . y \<in> S \<Longrightarrow> x \<sqsubseteq> y"
  shows "x = bottom_of"
  using assms 
  by (metis below_antisym bottom_of_minimal bottom_of_there)

lemma closed_is_chain [simp]: "closed_on F \<Longrightarrow> monofun_on F \<Longrightarrow> chain (\<lambda>i. (F^^i) bottom_of)"
  apply (rule chainI)
  apply (induct_tac i)
  apply (simp, erule bottom_of_minimal[OF closed_onE[OF _ bottom_of_there]])[1]
  apply simp
  apply (erule monofun_onE)
  apply (erule closed_onE[OF iterate_closed_on bottom_of_there])
  apply (rule closed_onE[OF _ closed_onE[OF iterate_closed_on bottom_of_there]], assumption, assumption)
  apply assumption
  done

lemma closed_is_chain_on: "closed_on F \<Longrightarrow> monofun_on F \<Longrightarrow> chain_on (\<lambda>i. (F^^i) bottom_of)"
  unfolding chain_on_def
  apply rule
  apply rule
  apply (drule closed_is_chain, assumption)
  apply (simp add: chain_def)
  apply (rule)
  apply (erule closed_onE[OF iterate_closed_on bottom_of_there])
  done

lemma chain_on_lub_on:
  "chain_on Y \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  unfolding chain_on_def by (metis chain_def cpo)

lemma cont_onI2:
  fixes f :: "'a::cpo => 'b::cpo"
  assumes mono: "monofun_on f"
  assumes below: "!!Y. [|chain_on Y; chain (\<lambda>i. f (Y i))|]
     ==> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
  shows "cont_on f"
proof (rule cont_onI)
  fix Y :: "nat => 'a"
  assume Y: "chain_on Y"
  with mono have fY: "chain (\<lambda>i. f (Y i))"
    by (rule ch2ch_monofun_on)
  have "(\<Squnion>i. f (Y i)) = f (\<Squnion>i. Y i)"
    apply (rule below_antisym)
    apply (rule lub_below [OF fY])
    apply (rule monofun_onE [OF mono])
    apply (rule chain_on_is_on[OF Y])
    apply (rule chain_on_lub_on[OF Y])
    apply (rule is_ub_thelub [OF chain_on_is_chain[OF Y]])
    apply (rule below [OF Y fY])
    done
  with fY show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
    by (rule thelubE)
qed

lemma cont_on_cong':
  "\<lbrakk> \<And> x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> cont_on g \<Longrightarrow> cont_on f"
proof (rule cont_onI2)
case goal1 thus ?case by -(drule cont_on2mono_on, metis monofun_on_def)
next
case goal2
  have "(\<Squnion> i. f (Y i)) = (\<Squnion> i. g (Y i)) "
    using goal2(1) chain_on_is_on[OF goal2(3)]
    by simp
  moreover
  have "f (\<Squnion> i. Y i) = g  (\<Squnion> i. Y i)"
    apply (rule goal2(1))
    by (rule chain_on_lub_on[OF goal2(3)])
  ultimately
  show ?case apply -apply (erule ssubst)+
    apply (subst cont_on2contlubE[OF goal2(2) goal2(3)]) 
    apply rule
    done
qed

lemma cont_on_cong:
  "\<lbrakk> \<And> x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> cont_on g = cont_on f"
  by (metis cont_on_cong')

lemma cont_comp_cont_on:
  "cont f \<Longrightarrow> cont_on g \<Longrightarrow> cont_on (\<lambda> x. f (g x))"
  apply (rule cont_onI2)
  apply (erule (1) monofun_comp_monofun_on[OF cont2mono cont_on2mono_on])
  by (metis ch2ch_monofun_on cont2contlubE cont_on2contlubE cont_on2mono_on eq_imp_below)

lemma cont_comp_cont_on2:
  "cont f \<Longrightarrow> (\<And>x. cont (f x)) \<Longrightarrow> cont_on g \<Longrightarrow> cont_on h \<Longrightarrow> cont_on (\<lambda> x. f (g x) (h x))"
proof (rule cont_onI2)
case goal1 thus ?case by (rule  monofun_comp_monofun_on2[OF cont2mono cont2mono cont_on2mono_on cont_on2mono_on])
next
case goal2
  have c1: "chain (\<lambda>i. h (Y i))" by (rule ch2ch_monofun_on[OF cont_on2mono_on[OF goal2(4)] goal2(5)])
  have c2: "chain (\<lambda>i. g (Y i))" by (rule ch2ch_monofun_on[OF cont_on2mono_on[OF goal2(3)] goal2(5)])
  have c3: "chain (\<lambda>i. f (g (Y i)))" by (rule ch2ch_cont[OF goal2(1) c2])
  have c4: "\<And>x. chain (\<lambda>i. f x (h (Y i)))" by (rule ch2ch_cont[OF goal2(2) c1])
  have c5: "\<And>x. chain (\<lambda>i. f (g (Y i)) x)" by (rule ch2ch_fun[OF c3])

  show ?case
  apply (subst cont_on2contlubE[OF goal2(3) goal2(5)])
  apply (subst cont_on2contlubE[OF goal2(4) goal2(5)])
  apply (subst cont2contlubE[OF goal2(2) c1])
  apply (subst cont2contlubE[OF goal2(1) c2])
  apply (subst lub_fun[OF c3])
  apply (subst diag_lub[OF c4 c5])
  apply rule
  done
qed
end


lemma cont_on_comp:
  assumes "subpcpo S1"
  and "subpcpo S2"
  and "cont_on S1 f"
  and "cont_on S2 g"
  and "f ` S1 \<subseteq> S2"
  shows "cont_on S1 (\<lambda> x. g (f x))"
proof-
  interpret subpcpo S1 by fact
  interpret s2!: subpcpo S2 by fact
  show ?thesis
  proof(rule cont_onI2)
  case goal1
    show ?case
      by (rule monofun_on_comp[OF cont_on2mono_on[OF assms(3)] cont_on2mono_on[OF assms(4)] assms(5)])
  case (goal2 Y)
    have c: "chain_on S2 (\<lambda>i. f (Y i))"
      apply (rule chain_onI)
      apply (metis assms(3) chain_on_def cont_on2mono_on goal2(1) monofun_onE)
      apply (metis (full_types) assms(5) chain_on_is_on goal2(1) imageI in_mono)
      done
    show ?case
      apply (subst cont_on2contlubE[OF assms(3) goal2(1)])
      apply (subst cont_on2contlubE[OF assms(4) c])
      apply (rule below_refl)
    done
  qed
qed

subsubsection {* Admissibility of various definitions from this theory *}

lemma subcpo_mem_adm:
  "subcpo S \<Longrightarrow> adm (\<lambda> x. x \<in> S)"
  by (rule admI, metis subcpo.cpo)

lemma adm_closed_on:
  assumes "subpcpo S"
  shows "adm (closed_on S)"
proof (rule admI[rule_format], rule closed_onI)
  case (goal1 Y x)
    have "chain (\<lambda> i. Y i x)"  by (rule ch2ch_fun[OF `chain Y`])
    with  closed_onE[OF goal1(2) `x\<in>S`]
    have "(\<Squnion> i. Y i x) \<in> S" by (metis assms subcpo.cpo subpcpo_is_subcpo)
    thus ?case by (metis lub_fun[OF `chain Y`])
qed

lemma adm_monofun_on:
  assumes "subpcpo S"
  shows "adm (monofun_on S)"
proof (rule admI[rule_format], rule monofun_onI)
  case (goal1 Y x y)
    have "(\<Squnion> i. Y i x) \<sqsubseteq> (\<Squnion> i. Y i y)"
      apply (rule lub_mono[OF ch2ch_fun[OF `chain Y`]  ch2ch_fun[OF `chain Y`]])
      apply (rule monofun_onE[OF goal1(2) goal1(3) goal1(4) goal1(5)])
      done
    thus "(\<Squnion> i. Y i) x \<sqsubseteq> (\<Squnion> i. Y i) y" by (metis lub_fun[OF `chain Y`])
qed

lemma adm_cont_on:
  assumes "subpcpo S"
  shows "adm (cont_on S)"
proof (rule admI[rule_format], rule subpcpo.cont_onI2[OF assms(1)])
case goal1 thus ?case by (metis admD[OF adm_monofun_on[OF assms]] cont_on2mono_on)
next
case (goal2 Y Z)
  have "(\<Squnion> i. Y i) (\<Squnion> j. Z j) = (\<Squnion> i. Y i (\<Squnion> j. Z j))" by (metis lub_fun[OF `chain Y`])
  also have "... = (\<Squnion> i. (\<Squnion> j. Y i (Z j)))" by (subst cont_on2contlubE[OF goal2(2) goal2(3)], rule)
  also have "... = (\<Squnion> i. Y i (Z i))"
    apply (rule diag_lub[OF ch2ch_fun[OF goal2(1)]])
    by (metis chain_on_is_chain[OF ch2ch_cont_on[OF goal2(2) goal2(3)]] subsetI)
  also have "... = (\<Squnion> j. (\<Squnion> i. Y i (Z j)))"
    apply (rule diag_lub[OF _ ch2ch_fun[OF goal2(1)], symmetric])
    by (metis chain_on_is_chain[OF ch2ch_cont_on[OF goal2(2) goal2(3)]] subsetI)
  also have "... = (\<Squnion> j. (\<Squnion> i. Y i) (Z j))" by (subst lub_fun[OF `chain Y`], rule)
  finally
  show "(\<Squnion> i. Y i) (\<Squnion> j. Z j) \<sqsubseteq> (\<Squnion> j. (\<Squnion> i. Y i) (Z j))" by simp
qed

subsubsection {* A locale with an explicit bottom element *}

text {*
This is only a notational convenience to assert the pcpo-property and the bottom element
in one step.
*}

locale subpcpo_bot = subpcpo S for S +
  fixes b
  assumes "bottom_of S = b"

lemmas subpcpo_bot_def' = subpcpo_bot_def[unfolded subpcpo_bot_axioms_def]

lemma subpcpo_bot_is_subpcpo:
  "subpcpo_bot S b \<Longrightarrow> subpcpo S"
  unfolding subpcpo_bot_def by auto

lemma bottom_of_subpcpo_bot:
  "subpcpo_bot S b \<Longrightarrow> bottom_of S = b"
  unfolding subpcpo_bot_def' by auto

lemma bottom_of_subpcpo_bot_there:
  "subpcpo_bot S b \<Longrightarrow> b \<in> S"
  unfolding subpcpo_bot_def' by (metis subpcpo.bottom_of_there)

lemma bottom_of_subpcpo_bot_minimal:
  "subpcpo_bot S b \<Longrightarrow> x \<in> S \<Longrightarrow> b \<sqsubseteq> x"
  unfolding subpcpo_bot_def' by (metis subpcpo.bottom_of_minimal)

lemma subpcpo_is_subpcpo_bot:
  "subpcpo S \<Longrightarrow> subpcpo_bot S (bottom_of S)"
  unfolding subpcpo_bot_def' by auto

lemma subpcpo_botI:
  assumes "\<And> Y. \<lbrakk> chain Y; \<And> i. Y i \<in> S \<rbrakk> \<Longrightarrow> (\<Squnion> i. Y i) \<in> S"
  assumes "b \<in> S"
  assumes "\<And> y. y \<in> S \<Longrightarrow> b \<sqsubseteq> y"
  shows "subpcpo_bot S b"
unfolding subpcpo_bot_def' 
proof
  show "subpcpo S" by (rule subpcpoI[OF assms])
  interpret subpcpo S by fact
  show "bottom_of S = b"
    by (rule bottom_ofI[symmetric, OF assms(2) assms(3)])
qed

subsubsection {* Various subpcpo's and their properties *}

lemma subpcpo_UNIV:
  shows "subpcpo (UNIV::'a::pcpo set)"
  by(rule subpcpoI, auto)

lemma subpcpo_cone_above:
  shows "subpcpo {y . x \<sqsubseteq> y}"
  by (rule subpcpoI,  auto intro:admD)

lemma bottom_of_cone_above[simp]:
  shows "bottom_of {y . x \<sqsubseteq> y} = x"
proof-
  interpret subpcpo "{y . x \<sqsubseteq> y}" by (rule subpcpo_cone_above)
  show ?thesis by (metis bottom_of_minimal bottom_of_there mem_Collect_eq po_eq_conv)
qed

lemma subpcpo_bot_cone_above:
  shows "subpcpo_bot {y . x \<sqsubseteq> y} x"
  by (metis bottom_of_cone_above subpcpo_is_subpcpo_bot[OF subpcpo_cone_above])

lemma subpcpo_bot_image:
  assumes "subpcpo_bot S b"
  and "cont f"
  and "cont g"
  and im: "g ` f ` S \<subseteq> S"
  and cut: "\<And> x. x \<in> f ` S \<Longrightarrow> f (g x) = x"
  shows "subpcpo_bot (f`S) (f b)"
proof(rule subpcpo_botI)
  interpret subpcpo S by (rule subpcpo_bot_is_subpcpo, fact)
{
  fix Y :: "nat \<Rightarrow> 'b"
  assume *: "\<And> i. Y i \<in> f ` S"
  have "\<And> i. g (Y i) \<in> S"
    by (metis (full_types) "*" im image_eqI set_mp)
  moreover
  assume "chain Y"
  hence "chain (\<lambda> i. g (Y i))"
    by (metis ch2ch_cont[OF `cont g`])
  ultimately
  have "(\<Squnion> i. g (Y i)) \<in> S" by (metis cpo)
  hence "f (\<Squnion> i. g (Y i)) \<in> f` S" by (rule imageI)
  hence "(\<Squnion> i. f (g (Y i))) \<in> f` S" by (metis cont2contlubE[OF `cont f` `chain (\<lambda>i. g (Y i))` ])
  thus "(\<Squnion> i. Y i) \<in> f` S" by (metis "*" cut lub_eq)
  next
  show "f b \<in> f ` S" by (rule imageI, rule bottom_of_subpcpo_bot_there, fact)
  next
  fix y
  assume "y \<in> f`S"
  hence "g y \<in> S" by (metis im imageI in_mono)
  hence "b \<sqsubseteq> g y" by (metis bottom_of_subpcpo_bot[OF assms(1)] bottom_of_minimal)
  hence "f b \<sqsubseteq> f (g y)" by (metis cont2monofunE[OF `cont f`])
  thus  "f b \<sqsubseteq> y" by (metis `y \<in> f\` S` cut)
}
qed

lemma subpcpo_product:
  assumes "subpcpo S1" and "subpcpo S2"
  shows "subpcpo (S1 \<times> S2)"
proof(rule subpcpoI)
  interpret subpcpo S1 by fact
  interpret s2!: subpcpo S2  by fact
{
  fix Y :: "nat \<Rightarrow> ('a \<times>'b)"
  assume "chain Y"
  hence "chain (\<lambda> i. (fst (Y i)))" and  "chain (\<lambda> i. (snd (Y i)))"
    by (auto simp add: chain_def fst_monofun snd_monofun)
  moreover
  assume "\<And> i. Y i \<in> S1 \<times> S2"
  hence "\<And> i. fst (Y i) \<in> S1" and  "\<And> i. snd (Y i) \<in> S2"
    by (metis mem_Sigma_iff surjective_pairing)+
  ultimately
  have "(\<Squnion> i. fst (Y i)) \<in> S1" and "(\<Squnion> i. snd (Y i)) \<in> S2" using cpo s2.cpo by auto
  thus "(\<Squnion> i. Y i) \<in> S1 \<times> S2" by (auto simp add: lub_prod[OF `chain Y`])
  next
  show "(bottom_of S1, bottom_of S2) \<in> S1 \<times> S2" by simp
  next
  fix y
  assume "y \<in> S1 \<times> S2"
  thus "(bottom_of S1, bottom_of S2) \<sqsubseteq> y"
    by (metis (full_types) Pair_below_iff bottom_of_minimal mem_Sigma_iff prod.exhaust s2.bottom_of_minimal)
}
qed

lemma subcpo_Inter:
  "(\<And>i. subcpo (S i)) \<Longrightarrow> subcpo (\<Inter> i. S i)"
  unfolding subcpo_def by (metis INT_iff UNIV_I)
lemma
  assumes "\<And>i. subpcpo (S i)"
  assumes "\<And> i j. bottom_of (S i) = bottom_of (S j)"
  shows subpcpo_Inter: "subpcpo (\<Inter> i. S i)" and bottom_of_Inter: "\<And>i. bottom_of (S i) = bottom_of (\<Inter> i. S i)"
proof-
  have *: "subpcpo_bot (\<Inter> i. S i) (bottom_of (S undefined))"
  proof(rule subpcpo_botI)
    case goal1
    thus ?case by (metis assms(1) subpcpo_is_subcpo subcpo_Inter subcpo_def)
  next
    case goal2
    show "bottom_of (S undefined) \<in> (\<Inter> i. S i)"
      by (rule, metis subpcpo.bottom_of_there[OF assms(1)] assms(2))
  next
    case goal3
    thus "bottom_of (S undefined) \<sqsubseteq> y"
      apply -
      apply (rule subpcpo.bottom_of_minimal[OF assms(1)])
      by (metis INT_iff UNIV_I)
 qed
 case goal1 show ?case using * by (metis subpcpo_bot_is_subpcpo)
 case goal2 show ?case using * by (metis assms(2) bottom_of_subpcpo_bot)
qed

lemma subpcpo_bot_inter:
  assumes "subpcpo_bot S1 b1" and "subcpo S2"
  and bot_in_2: "b1 \<in> S2"
  shows "subpcpo_bot (S1 \<inter> S2) b1"
proof(rule subpcpo_botI)
  interpret subpcpo S1 by (rule subpcpo_bot_is_subpcpo, fact)
  interpret s2!: subcpo S2  by (fact)
{
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
  moreover
  assume "\<And> i. Y i \<in> S1 \<inter> S2"
  hence "\<And> i. Y i \<in> S1" and  "\<And> i. Y i \<in> S2" by auto
  ultimately
  have "(\<Squnion> i. Y i) \<in> S1" and "(\<Squnion> i. Y i) \<in> S2" using cpo s2.cpo by auto
  thus "(\<Squnion> i. Y i) \<in> S1 \<inter> S2" by auto
  next
  show "b1 \<in> S1 \<inter> S2" by (auto simp add: bot_in_2 bottom_of_subpcpo_bot_there[OF assms(1)])
  next
  fix y
  assume "y \<in> S1 \<inter> S2"
  thus "b1 \<sqsubseteq> y"
    by (auto intro: bottom_of_subpcpo_bot_minimal[OF assms(1)])
}
qed

subsubsection {* Lemmas about function iteration *}

lemma chain_on_compow:
  assumes "chain Y"
  and cont: "\<And> i . cont_on S (Y i)"
  and closed: "\<And> i . closed_on S (Y i)"
  and "x \<in> S"
  shows "chain_on S (\<lambda>i. (Y i ^^ k) x)"
proof-
  { fix i k have "(Y i ^^ k) x \<in> S"
    by (induct k, simp_all add: `x \<in> S` closed_onE[OF closed])
  } note S = this
  show ?thesis
  proof(induct k)
  case 0 show ?case by (rule chain_onI[OF _ S], simp)
  case (Suc k)
    show ?case
    proof(rule chain_onI[OF _ S])
      case (goal1 i)
        have "Y i ((Y i ^^ k) x) \<sqsubseteq> Y (Suc i) ((Y i ^^ k) x)"
          using `chain Y` by (rule fun_belowD[OF chainE])
        also have "... \<sqsubseteq> Y (Suc i) ((Y (Suc i) ^^ k) x)"
          by (rule monofun_onE[OF cont_on2mono_on[OF cont] S S chainE[OF chain_on_is_chain[OF Suc]]])
        finally show ?case by simp
    qed
  qed
qed

lemma lub_on_compow:
  fixes  Y :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "chain Y"
  and cont: "\<And> i . cont_on S (Y i)"
  and closed: "\<And> i . closed_on S (Y i)"
  and "x \<in> S"
  shows "((\<Squnion>i. Y i) ^^ k) x = (\<Squnion>i. (Y i ^^ k) x)"
proof (induct k)
case 0 thus ?case by auto
next
{ fix i k have "(Y i ^^ k) x \<in> S"
  by (induct k, simp_all add: `x \<in> S` closed_onE[OF closed])
} note S = this

case (Suc k)
  have c2: "\<And> k. chain_on S (\<lambda>i. (Y i ^^ k) x)" by (rule chain_on_compow[OF assms])
  have c4: "\<And> j. \<And> x. chain (\<lambda>i. Y i ((Y j ^^ k) x))" by (rule ch2ch_fun[OF `chain Y`])
  have c5: "\<And> i. chain_on S (\<lambda>j. Y i ((Y j ^^ k) x))" apply (rule ch2ch_cont_on[OF cont c2]) using closed by (metis closed_on_def image_subsetI)

  have "((\<Squnion> i. Y i) ^^ Suc k) x = (\<Squnion> i. Y i) (((\<Squnion> i. Y i) ^^ k) x)" by simp
  also have "... = (\<Squnion> i. Y i) (\<Squnion> i. (Y i ^^k) x)" by (simp add: Suc)
  also have "... = (\<Squnion> i. (Y i (\<Squnion> j. (Y j ^^k) x)))" by (subst lub_fun[OF `chain Y`], rule)
  also have "... = (\<Squnion> i. (\<Squnion> j. Y i ((Y j ^^k) x)))" by (subst cont_on2contlubE[OF cont c2], rule) 
  also have "... = (\<Squnion> i.  Y i ((Y i ^^k) x))" by (rule diag_lub[OF c4 chain_on_is_chain[OF c5]])
  also have "... = (\<Squnion> i. (Y i ^^(Suc k)) x)" by simp
  finally show "((\<Squnion> i. Y i) ^^ Suc k) x = (\<Squnion> i. (Y i ^^ Suc k) x)".
qed


subsubsection {* Fixed points in unpointed chain-complete partial orders *}

text {* These fixed points take the initial value as an explicit argument, as there is no canonical bottom element. *}

definition
  "fix_on'" :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "fix_on' b F = 
    (if chain (\<lambda>i. (F^^i) b)
    then (\<Squnion>i. (F^^i) b)
    else b)"

lemmas fix_on_def = fix_on'_def

abbreviation fix_on where
  "fix_on S \<equiv> fix_on' (subpcpo_syn.bottom_of S)"

text {* The following definition identifies when @{term F} has a fixed point in @{term S}. *}

inductive fix_on_cond
  for S b F
  where fix_on_condI: "subpcpo S \<Longrightarrow> bottom_of S = b \<Longrightarrow> closed_on S F \<Longrightarrow> cont_on S F \<Longrightarrow> fix_on_cond S b F"

lemma fix_on_condD1:
  assumes "fix_on_cond S b F"
  shows "chain (\<lambda>i. (F ^^ i) b)"
proof-
  have "subpcpo S" and "closed_on S F" and "cont_on S F" and "b = bottom_of S"
    using fix_on_cond.cases[OF assms] by metis+
  interpret subpcpo S by fact
  have "chain (\<lambda>i. (F ^^ i) (subpcpo_syn.bottom_of S))"
    by (rule closed_is_chain[OF `closed_on _ _` cont_on2mono_on[OF `cont_on _ _`]])
  thus ?thesis by (simp add: `b = _`)
qed

lemma fix_on_def':
  assumes "fix_on_cond S b F"
  shows "fix_on' b F = (\<Squnion>i. (F^^i) b)"
  unfolding fix_on_def
  by (simp add: fix_on_def fix_on_condD1[OF assms])

lemma fix_on_ind:
  assumes "fix_on_cond S b F"
  assumes adm: "adm_on S P"
  assumes base: "P b"
  assumes step: "\<And>y. \<lbrakk> y \<in> S ; P y \<rbrakk> \<Longrightarrow> P (F y)"
  shows "P (fix_on' b F)"
proof -
  from assms(1)
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S by fact

  note chain = closed_is_chain_on[OF closed cont_on2mono_on[OF cont]] 

  { fix i
    have "P ((F^^i) (bottom_of S))"
      apply (induct i)
      apply (simp add: base[simplified])
      apply simp
      apply (erule step[rotated])
      by (metis (full_types) chain chain_on_def)
  }
  hence "P (\<Squnion>i. (F^^i) (bottom_of S))"
    by (rule adm_onD[OF adm chain])
  thus ?thesis
    using chain_on_is_chain[OF chain] subpcpo_axioms
    by (simp add: fix_on_def)
qed


lemma parallel_fix_on_ind:
  assumes "fix_on_cond S1 b1 F"
  assumes "fix_on_cond S2 b2 G"
  assumes adm: "adm_on (S1 \<times> S2) (\<lambda>x. P (fst x) (snd x))"
  assumes base: "P b1 b2"
  assumes step: "!!y z. \<lbrakk> y \<in> S1 ; z \<in> S2; P y z \<rbrakk> \<Longrightarrow> P (F y) (G z)"
  shows "P (fix_on' b1 F) (fix_on' b2 G)"
proof -
  from assms(1,2)
  have pcpo1: "subpcpo S1" and closedF: "closed_on S1 F" and chainF: "cont_on S1 F" and [simp]:"b1 = bottom_of S1"
  and  pcpo2: "subpcpo S2" and closedG: "closed_on S2 G" and chainG: "cont_on S2 G" and [simp]:"b2 = bottom_of S2"
     by (metis fix_on_cond.cases)+

  interpret subpcpo S1 by fact
  interpret s2!: subpcpo S2  by fact
  interpret sp!: subpcpo "(S1 \<times> S2)" by (rule subpcpo_product, fact+)

  note chain1 = closed_is_chain[OF closedF cont_on2mono_on[OF chainF]] 
  note chain2 = s2.closed_is_chain[OF closedG cont_on2mono_on[OF chainG]] 

  from adm have adm': "adm_on (S1 \<times> S2) (split P)"
    unfolding split_def .

  { fix i
    have "P ((F^^i) (bottom_of S1)) ((G^^i) (bottom_of S2))"
    proof(induct i)
    case 0 thus ?case by (simp add: base[simplified])
    next
    case (Suc i)
      have "((F ^^ i) (bottom_of S1)) \<in> S1" by (rule closed_onE[OF iterate_closed_on[OF closedF] bottom_of_there])
      moreover
      have "((G ^^ i) (bottom_of S2)) \<in> S2" by (rule closed_onE[OF iterate_closed_on[OF closedG] s2.bottom_of_there])
      ultimately
      show ?case using Suc by (simp add: step[simplified])
    qed
  }
  hence "!!i. split P ((F^^i) (bottom_of S1), (G^^i) (bottom_of S2))"
    by simp
  hence "split P (\<Squnion>i. ((F^^i) (bottom_of S1), (G^^i) (bottom_of S2)))"
    apply -
    apply (rule adm_onD [OF adm'
               chain_on_product[OF closed_is_chain_on[OF closedF cont_on2mono_on[OF chainF]]
                                   s2.closed_is_chain_on[OF closedG cont_on2mono_on[OF chainG]]]])
    apply (auto intro: ch2ch_Pair simp add: chain1 chain2)
    done
  hence "split P (\<Squnion>i. ((F^^i) (bottom_of S1)), \<Squnion>i. (G^^i) (bottom_of S2))"
    by (simp add: lub_Pair chain1 chain2)
  hence "P (\<Squnion>i. (F^^i) (bottom_of S1)) (\<Squnion>i. (G^^i) (bottom_of S2))"
    by simp
  thus "P (fix_on' b1 F) (fix_on' b2 G)"
    using chain1 chain2 subpcpo_axioms s2.subpcpo_axioms
    by (simp add: fix_on_def)
qed

lemma fix_on_mono2:
  assumes "fix_on_cond S1 b1 F"
  assumes "fix_on_cond S2 b2 G"
  and "b1 \<sqsubseteq> b2"
  and "\<And> x y. x \<in> S1 \<Longrightarrow> y \<in> S2 \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> F x \<sqsubseteq> G y"
  shows "fix_on' b1 F \<sqsubseteq> fix_on' b2 G"
  apply (rule parallel_fix_on_ind[OF assms(1) assms(2)])
  apply (rule adm_is_adm_on, simp)
  apply (rule assms(3))
  apply (metis assms(4))
  done

lemma fix_on_mono:
  assumes "fix_on_cond S b F"
  assumes "fix_on_cond S b G"
  assumes below: "\<And> x. x \<in> S \<Longrightarrow> F x \<sqsubseteq> G x"
  shows "fix_on' b F \<sqsubseteq> fix_on' b G"
proof-
  have "monofun_on S G" by (metis assms(2) cont_on2mono_on fix_on_cond.simps)
  show ?thesis
    by (rule fix_on_mono2[OF assms(1,2) below_refl below_trans[OF below monofun_onE[OF `monofun_on _ _`]]])
qed

lemma fix_on_cond_cong:
  assumes "fix_on_cond S b F"
  assumes eq: "\<And> x. x \<in> S \<Longrightarrow> F x = G x"
  shows "fix_on_cond S b G"
proof -
  from assms(1)
  have pcpo: "subpcpo S" and closedF: "closed_on S F" and contF: "cont_on S F" and [simp]:"b = bottom_of S"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S by fact
  show ?thesis
    apply (rule fix_on_condI)
    apply fact
    apply simp
    apply (metis closedF closed_on_def eq)
    apply (subst cont_on_cong[OF eq], assumption, fact)
  done
qed

lemma fix_on_cong:
  assumes "fix_on_cond S b F"
  assumes "\<And> x. x \<in> S \<Longrightarrow> F x = G x"
  shows "fix_on' b F = fix_on' b G"
  apply (rule below_antisym)
  apply (metis fix_on_mono assms fix_on_cond_cong[OF assms(1) assms(2)] eq_imp_below)+
  done

lemma fix_on_there:
  assumes "fix_on_cond S b F"
  shows "fix_on' b F \<in> S"
proof-
  from assms(1)
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S by fact

  note co = closed_is_chain_on[OF closed cont_on2mono_on[OF cont]] 
  note c = chain_on_is_chain[OF co] 

  have "(\<Squnion> i. (F ^^ i) (subpcpo_syn.bottom_of S)) \<in> S"
    by (metis chain_on_lub_on[OF co])
  thus ?thesis
    using c subpcpo_axioms
    by (simp add: fix_on_def)
qed

lemma fix_on_eq:
  assumes "fix_on_cond S b F"
  shows "fix_on' b F = F (fix_on' b F)"
proof-
  from assms(1)
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S by fact

  note co = closed_is_chain_on[OF closed cont_on2mono_on[OF cont]] 
  note c = chain_on_is_chain[OF co] 

  have "(\<Squnion> i. (F ^^ i) (subpcpo_syn.bottom_of S)) = F (\<Squnion> i. (F ^^ i) (subpcpo_syn.bottom_of S))"
    apply (subst lub_range_shift [of _ 1, symmetric, OF c])
    apply (subst cont_on2contlubE[OF `cont_on _ _` co])
    apply simp
    done

  thus ?thesis
    using c subpcpo_axioms
    by (simp add: fix_on_def)
qed
  
  
lemma fix_on_least_below:
  assumes "fix_on_cond S b F"
  assumes there: "x \<in> S"
  assumes below: "F x \<sqsubseteq> x"
  shows "fix_on' b F \<sqsubseteq> x"
proof-
  from assms(1)
  have pcpo1: "subpcpo S" and closed: "closed_on S F" and cont: "cont_on S F" and [simp]:"b = bottom_of S"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S by fact

  note co = closed_is_chain_on[OF closed cont_on2mono_on[OF cont]] 
  note c = chain_on_is_chain[OF co] 


  have "(\<Squnion> i. (F ^^ i) (subpcpo_syn.bottom_of S)) \<sqsubseteq> x"
    apply (rule lub_below[OF c])
    apply (induct_tac i)

    apply (simp_all add: there)
    apply (rule rev_below_trans[OF below])
    apply (erule monofun_onE[OF
          cont_on2mono_on[OF `cont_on _ _`]
          closed_onE[OF iterate_closed_on[OF `closed_on _ _`] bottom_of_there]
          `x \<in> S`])
    done

  thus ?thesis
    using c subpcpo_axioms
    by (simp add: fix_on_def)
qed

lemma fix_on_eqI:
  assumes "fix_on_cond S b F"
  assumes there: "x \<in> S"
  assumes fixed: "F x = x"
  assumes least: "\<And>z. z \<in> S \<Longrightarrow> F z = z \<Longrightarrow> x \<sqsubseteq> z"
  shows "fix_on' b F = x"
  apply (rule below_antisym)
  apply (rule fix_on_least_below [OF assms(1) there eq_imp_below[OF fixed]])
  apply (rule least[OF fix_on_there[OF assms(1)] fix_on_eq[OF assms(1), symmetric]])
done

lemma fix_on_roll:
  assumes "fix_on_cond S b (\<lambda> x. F (G x))"
  assumes "fix_on_cond S' b' (\<lambda> x. G (F x))"
  assumes "cont G"
  assumes "G b \<in> S'"
  assumes huh: "\<And> z. z \<in> S' \<Longrightarrow> F z \<in> S"

  shows "G (fix_on' b (\<lambda> x. F (G x))) = fix_on' b' (\<lambda>x. G (F x))"
proof(rule fix_on_eqI[OF assms(2), symmetric])
  from assms(1)
  have pcpo1: "subpcpo S" and closed: "closed_on S (\<lambda> x. F (G x))" and cont: "cont_on S (\<lambda> x. F (G x))" and [simp]:"b = bottom_of S"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S by fact

  from assms(2)
  have pcpo2: "subpcpo S'" and closed2: "closed_on S' (\<lambda> x. G (F x))" and cont2: "cont_on S' (\<lambda> x. G (F x))" and [simp]:"b' = bottom_of S'"
     by (metis fix_on_cond.cases)+
  interpret subpcpo S' by fact

  show "G (fix_on' b (\<lambda>x. F (G x))) \<in> S'"
    apply (rule fix_on_ind[OF assms(1)])
    apply (rule adm_is_adm_on[OF adm_subst[OF `cont G` subcpo_mem_adm[OF subpcpo_is_subcpo[OF pcpo2]]]])
    apply fact
    apply (erule closed_onE[OF closed2])
    done
  show "G (F (G (fix_on' b (\<lambda>x. F (G x))))) = G (fix_on' b (\<lambda>x. F (G x)))"
    by (subst fix_on_eq[OF assms(1), symmetric], rule)
  fix z
  assume "z \<in> S'" and "G (F z) = z"
  hence "F (G (F z)) = F z" by metis 
  hence "fix_on' b (\<lambda>x. F (G x)) \<sqsubseteq> F z"
    by (rule fix_on_least_below[OF assms(1) huh[OF `z \<in> _`] eq_imp_below])
  hence "G (fix_on' b (\<lambda>x. F (G x))) \<sqsubseteq> G (F z)"
    by (rule cont2monofunE[OF `cont G`])
  thus "G (fix_on' b (\<lambda>x. F (G x))) \<sqsubseteq> z" by (simp add: `_ = z`)
qed

lemma (in subpcpo) fix_on_const[simp]:
  assumes "x \<in> S"
  shows "fix_on S (\<lambda> _. x) = x"
proof-
  have "fix_on_cond S bottom_of (\<lambda>_ . x)"
    apply (rule fix_on_condI[OF subpcpo_axioms refl])
    apply (rule closed_onI[OF assms])
    apply (rule cont_is_cont_on[OF cont_const])
    done  
  thus ?thesis
    by (rule fix_on_eq)
qed

lemma fix_on_cond_adm:
  "adm (fix_on_cond S b)"
proof(rule admI)
  fix Y
  assume "chain Y" and "\<forall>i. fix_on_cond S b (Y i)"
  hence cond: "\<And> i. fix_on_cond S b (Y i)" by simp
  have "subpcpo S" 
    by (metis cond fix_on_cond.simps)

  show "fix_on_cond S b (\<Squnion> i. Y i)"
    apply (rule fix_on_condI[OF `subpcpo S`])
    apply (metis cond fix_on_cond.simps)
    apply (rule admD[OF adm_closed_on[OF `subpcpo S`] `chain Y`])
      apply (metis cond fix_on_cond.simps)
    apply (rule admD[OF adm_cont_on[OF `subpcpo S`] `chain Y`])
      apply (metis cond fix_on_cond.simps)
  done
qed

lemma fix_on_cont:
  fixes Y :: "nat => 'a"
  assumes "chain Y"
  and cond: "\<And> i. fix_on_cond S b (F (Y i))"
  and cont: "cont F"
  shows  "fix_on' b (F (\<Squnion> i. Y i)) = (\<Squnion> i. fix_on' b (F (Y i)))"
proof(rule below_antisym)
  have pcpo: "subpcpo S" by (metis cond fix_on_cond.simps)
  have closed: "\<And> i. closed_on S (F (Y i))" by (metis cond fix_on_cond.simps)
  have cont_on: "\<And> i. cont_on S (F (Y i))"  by (metis cond fix_on_cond.simps)
  have [simp]: "b = bottom_of S" by (metis cond fix_on_cond.simps)

  have closed_on_lub: "closed_on S (F (\<Squnion>i. Y i))"
   by (rule admD[OF adm_subst[OF cont adm_closed_on[OF pcpo]] `chain Y` closed])
  have cont_on_lub: "cont_on S (F (\<Squnion>i. Y i))"
   by (rule admD[OF adm_subst[OF cont adm_cont_on[OF pcpo]] `chain Y` cont_on])

  note chain = subpcpo.closed_is_chain[OF pcpo closed cont_on2mono_on[OF cont_on]]
  note chain_lub = subpcpo.closed_is_chain[OF pcpo closed_on_lub cont_on2mono_on[OF cont_on_lub]]
  interpret subpcpo S by fact

  { fix i k have "(F (Y i) ^^ k) (bottom_of S) \<in> S"
    by (induct k, simp_all add: closed_onE[OF closed])
  } note S = this

  have c2: "chain (\<lambda>i. F (Y i))" by (rule ch2ch_cont[OF cont `chain Y`])
  have c3: "\<And>i. chain (\<lambda>j. (F (Y j) ^^ i) (bottom_of S))"
    by (rule chain_on_is_chain[OF chain_on_compow[OF c2 cont_on closed bottom_of_there]])
  have c4: "\<And>j. chain (\<lambda>i. (F (Y j) ^^ i) (bottom_of S))"
    apply (rule chainI)
    apply (induct_tac i)
    apply simp
    apply (rule bottom_of_minimal)
    apply (rule closed_onE[OF closed bottom_of_there])
    apply simp
    apply (erule monofun_onE[OF cont_on2mono_on[OF cont_on] S closed_onE[OF closed S]])
    done

  have "(\<Squnion> k. ((F (\<Squnion> i. Y i)) ^^ k) (bottom_of S)) \<sqsubseteq> (\<Squnion> i k. (F (Y i) ^^ k) (bottom_of S))"
    apply (subst cont2contlubE[OF cont `chain Y`])
    apply (subst lub_on_compow[OF c2 cont_on closed bottom_of_there])
    apply (subst diag_lub[OF c4 c3])
    apply (subst diag_lub[OF c3 c4])
    apply (rule below_refl)
    done
    
  thus "fix_on' b (F (\<Squnion> i. Y i)) \<sqsubseteq> (\<Squnion> i. fix_on' b (F (Y i)))"
    using chain chain_lub pcpo
    unfolding fix_on'_def
    by simp

  have "chain (\<lambda>i. fix_on' b (F (Y i)))"
    apply (rule chainI)
    apply (rule fix_on_mono[OF cond cond])
    by (metis assms(1) cont cont2monofunE fun_belowD po_class.chainE)
  moreover
  { fix i
    have "fix_on' b (F (Y i)) \<sqsubseteq> fix_on' b (F (\<Squnion> i. Y i))"
      apply (rule fix_on_mono)
      apply fact
      apply (rule admD[OF adm_subst[OF `cont F` fix_on_cond_adm] `chain Y` cond])
      by (metis assms(1) cont cont2monofunE fun_belowD is_ub_thelub)
  }
  ultimately
  show "(\<Squnion> i. fix_on' b (F (Y i))) \<sqsubseteq> fix_on' b (F (\<Squnion> i. Y i))"
    by (rule lub_below)
qed

subsubsection {* Typeclass for types as disjoint union of pointed chain-complete partial orders *}

class subpcpo_partition =
  fixes to_bot :: "'a \<Rightarrow> 'a"
  assumes subpcpo: "\<And> x. subpcpo (to_bot -` {to_bot x})"
  and unrelated: "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> to_bot x = to_bot y"
  and to_bot_minimal: "\<And> x. to_bot x \<sqsubseteq> x"
begin
  lemma subcpo_cone_below:
    shows "subcpo {y . y \<sqsubseteq> x}"
    apply (rule subcpoI)
    apply (rule admD)
    apply auto
    done
  
  lemma subpcpo_cone_below:
    shows "subpcpo {y . y \<sqsubseteq> (x::'a)}"
    apply (rule subpcpoI2[OF subcpo_cone_below, of "to_bot x"])
    apply (simp add: to_bot_minimal)
    apply simp
    apply (drule unrelated)
    apply (erule subst)
    apply (rule to_bot_minimal)
    done

  lemma to_bot_adm: "adm (\<lambda> x. P (to_bot x))"
    apply (rule admI)
    apply (subst unrelated[OF is_ub_thelub, symmetric])
    apply assumption
    apply auto
    done

  lemma to_bot_idem[simp]:
    "to_bot (to_bot x) = to_bot x"
     by (metis to_bot_minimal unrelated)

  lemma to_bot_belowI[intro]:
    "to_bot x = to_bot y \<Longrightarrow> to_bot x \<sqsubseteq> y"
    by (metis to_bot_minimal)

  lemma to_bot_fix_on[simp]: "to_bot (fix_on' b F) = to_bot b"
    unfolding fix_on'_def
    apply auto
    apply (rule admD[OF to_bot_adm], assumption)
    apply (rule unrelated[OF chain_mono, of "\<lambda>i. (F ^^ i) b" 0, symmetric, simplified], assumption)
    done
end

end
