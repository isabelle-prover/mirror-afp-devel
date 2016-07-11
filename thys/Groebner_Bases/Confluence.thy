(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Properties of Binary Relations\<close>

theory Confluence
imports "../Abstract-Rewriting/Abstract_Rewriting"
begin

text \<open>This theory formalizes some general properties of binary relations, in particular a very weak
  sufficient condition for a relation to be Church-Rosser.
  Although \<close>

locale relation = fixes r::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>" 50)
begin

abbreviation rtc::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<^sup>*" 50) where
  "rtc a b \<equiv> r\<^sup>*\<^sup>* a b"
abbreviation sc::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<leftrightarrow>" 50) where
  "sc a b \<equiv> a \<rightarrow> b \<or> b \<rightarrow> a"

definition is_final::"'a \<Rightarrow> bool" where
  "is_final a \<equiv> \<not> (\<exists>b. r a b)"

definition srtc::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<leftrightarrow>\<^sup>*" 50) where
  "srtc a b \<equiv> sc\<^sup>*\<^sup>* a b"
definition cs::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<down>\<^sup>*" 50) where
  "cs a b \<equiv> (\<exists>s. (a \<rightarrow>\<^sup>* s) \<and> (b \<rightarrow>\<^sup>* s))"

definition is_confluent::bool where
  "is_confluent \<equiv> (\<forall>a b1 b2. (a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2) \<longrightarrow> b1 \<down>\<^sup>* b2)"
definition is_loc_confluent::bool where
  "is_loc_confluent \<equiv> (\<forall>a b1 b2. (a \<rightarrow> b1 \<and> a \<rightarrow> b2) \<longrightarrow> b1 \<down>\<^sup>* b2)"
definition is_ChurchRosser::bool where
  "is_ChurchRosser \<equiv> (\<forall>a b. a \<leftrightarrow>\<^sup>* b \<longrightarrow> a \<down>\<^sup>* b)"

subsection \<open>Setup for Connection to Theory @{theory Abstract_Rewriting}\<close>

abbreviation (input) relset::"('a * 'a) set" where
  "relset \<equiv> {(x, y). x \<rightarrow> y}"

lemma rtc_rtranclI:
  assumes "a \<rightarrow>\<^sup>* b"
  shows "(a, b) \<in> relset\<^sup>*"
using assms by (simp only: Enum.rtranclp_rtrancl_eq)

lemma final_NF:
  shows "(is_final a) = (a \<in> NF relset)"
unfolding is_final_def NF_def by simp

lemma sc_symcl:
  shows "(a \<leftrightarrow> b) = ((a, b) \<in> relset\<^sup>\<leftrightarrow>)"
by simp

lemma srtc_conversion:
  shows "(a \<leftrightarrow>\<^sup>* b) = ((a, b) \<in> relset\<^sup>\<leftrightarrow>\<^sup>*)"
proof -
  have "{(a, b). (a, b) \<in> {(x, y). x \<rightarrow> y}\<^sup>\<leftrightarrow>} = {(a, b). a \<rightarrow> b}\<^sup>\<leftrightarrow>" by auto
  thus ?thesis unfolding srtc_def conversion_def sc_symcl Enum.rtranclp_rtrancl_eq by simp
qed

lemma cs_join:
  shows "(a \<down>\<^sup>* b) = ((a, b) \<in> relset\<^sup>\<down>)"
unfolding cs_def join_def by (auto simp add: Enum.rtranclp_rtrancl_eq rtrancl_converse)

lemma confluent_CR:
  shows "is_confluent = CR relset"
unfolding is_confluent_def CR_defs by (auto simp add: Enum.rtranclp_rtrancl_eq cs_join)

lemma loc_confluent_WCR:
  shows "is_loc_confluent = WCR relset"
unfolding is_loc_confluent_def WCR_defs by (auto simp add: cs_join)

lemma wf_converse:
  shows "(wfP r^--1) = (wf (relset\<inverse>))"
unfolding wfP_def converse_def by simp

lemma wf_SN:
  shows "(wfP r^--1) = (SN relset)"
unfolding wf_converse wf_iff_no_infinite_down_chain SN_on_def by auto

subsection \<open>Simple Lemmas\<close>

lemma rtrancl_is_final:
  assumes "a \<rightarrow>\<^sup>* b" and "is_final a"
  shows "a = b"
proof -
  from rtranclpD[OF \<open>a \<rightarrow>\<^sup>* b\<close>] show ?thesis
  proof
    assume "a \<noteq> b \<and> (op \<rightarrow>)\<^sup>+\<^sup>+ a b"
    hence "(op \<rightarrow>)\<^sup>+\<^sup>+ a b" by simp
    from \<open>is_final a\<close> final_NF have "a \<in> NF relset" by simp
    from NF_no_trancl_step[OF this] have "(a, b) \<notin> {(x, y). x \<rightarrow> y}\<^sup>+" ..
    thus ?thesis using \<open>(op \<rightarrow>)\<^sup>+\<^sup>+ a b\<close> unfolding tranclp_unfold ..
  qed
qed

lemma cs_refl:
  shows "x \<down>\<^sup>* x"
unfolding cs_def
proof
  show "x \<rightarrow>\<^sup>* x \<and> x \<rightarrow>\<^sup>* x" by simp
qed

lemma cs_sym:
  assumes "x \<down>\<^sup>* y"
  shows "y \<down>\<^sup>* x"
using assms unfolding cs_def
proof
  fix z
  assume a: "x \<rightarrow>\<^sup>* z \<and> y \<rightarrow>\<^sup>* z"
  show "\<exists>s. y \<rightarrow>\<^sup>* s \<and> x \<rightarrow>\<^sup>* s"
  proof
    from a show "y \<rightarrow>\<^sup>* z \<and> x \<rightarrow>\<^sup>* z" by simp
  qed
qed

lemma rtc_implies_cs:
  assumes "x \<rightarrow>\<^sup>* y"
  shows "x \<down>\<^sup>* y"
proof -
  from joinI_left[OF rtc_rtranclI[OF assms]] cs_join show ?thesis by simp
qed

lemma rtc_implies_srtc:
  assumes "a \<rightarrow>\<^sup>* b"
  shows "a \<leftrightarrow>\<^sup>* b"
proof -
  from conversionI'[OF rtc_rtranclI[OF assms]] srtc_conversion show ?thesis by simp
qed

lemma srtc_symmetric:
  assumes "a \<leftrightarrow>\<^sup>* b"
  shows "b \<leftrightarrow>\<^sup>* a"
proof -
  from symD[OF conversion_sym[of relset], of a b] assms srtc_conversion show ?thesis by simp
qed

lemma srtc_transitive:
  assumes "a \<leftrightarrow>\<^sup>* b" and "b \<leftrightarrow>\<^sup>* c"
  shows "a \<leftrightarrow>\<^sup>* c"
proof -
  from rtranclp_trans[of "(op \<leftrightarrow>)" a b c] assms show "a \<leftrightarrow>\<^sup>* c" unfolding srtc_def .
qed

lemma cs_implies_srtc:
  assumes "a \<down>\<^sup>* b"
  shows "a \<leftrightarrow>\<^sup>* b"
proof -
  from assms cs_join have "(a, b) \<in> relset\<^sup>\<down>" by simp
  hence "(a, b) \<in> relset\<^sup>\<leftrightarrow>\<^sup>*" using join_imp_conversion by auto
  thus ?thesis using srtc_conversion by simp
qed

lemma confluence_implies_ChurchRosser:
  assumes is_confluent
  shows is_ChurchRosser
using assms unfolding is_confluent_def is_ChurchRosser_def
proof (intro allI)
  fix a b
  assume conf: "\<forall>a b1 b2. a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2 \<longrightarrow> b1 \<down>\<^sup>* b2"
  show "a \<leftrightarrow>\<^sup>* b \<longrightarrow> a \<down>\<^sup>* b"
  proof
    assume "a \<leftrightarrow>\<^sup>* b"
    thus "a \<down>\<^sup>* b" unfolding srtc_def
    proof (rule rtranclp_induct)
      from cs_refl show "a \<down>\<^sup>* a" .
    next
      fix y z
      assume "(op \<leftrightarrow>)\<^sup>*\<^sup>* a y" and "y \<leftrightarrow> z" and "a \<down>\<^sup>* y"
      from \<open>a \<down>\<^sup>* y\<close> obtain w where "a \<rightarrow>\<^sup>* w" and "y \<rightarrow>\<^sup>* w" unfolding cs_def by auto
      from \<open>y \<leftrightarrow> z\<close> show "a \<down>\<^sup>* z"
      proof
        assume "y \<rightarrow> z"
        hence "y \<rightarrow>\<^sup>* z" by simp
        from this \<open>y \<rightarrow>\<^sup>* w\<close> conf[rule_format, of y w z] have "w \<down>\<^sup>* z" by simp
        then obtain v where "w \<rightarrow>\<^sup>* v" and "z \<rightarrow>\<^sup>* v" unfolding cs_def by auto
        show ?thesis unfolding cs_def
        proof
          from rtranclp_trans[OF \<open>a \<rightarrow>\<^sup>* w\<close> \<open>w \<rightarrow>\<^sup>* v\<close>] \<open>z \<rightarrow>\<^sup>* v\<close> show "a \<rightarrow>\<^sup>* v \<and> z \<rightarrow>\<^sup>* v" by simp
        qed
      next
        assume "z \<rightarrow> y"
        hence "z \<rightarrow>\<^sup>* y" by simp
        show ?thesis unfolding cs_def
        proof
          from rtranclp_trans[OF \<open>z \<rightarrow>\<^sup>* y\<close> \<open>y \<rightarrow>\<^sup>* w\<close>] \<open>a \<rightarrow>\<^sup>* w\<close> show "a \<rightarrow>\<^sup>* w \<and> z \<rightarrow>\<^sup>* w" by simp
        qed
      qed
    qed
  qed
qed

lemma confluence_equiv_ChurchRosser:
  shows "is_confluent = is_ChurchRosser"
proof
  assume is_ChurchRosser
  thus is_confluent unfolding is_confluent_def is_ChurchRosser_def
  proof (intro allI, intro impI)
    fix a b1 b2
    assume cr: "\<forall>a b. a \<leftrightarrow>\<^sup>* b \<longrightarrow> a \<down>\<^sup>* b" and "a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2"
    hence "a \<rightarrow>\<^sup>* b1" and "a \<rightarrow>\<^sup>* b2" by auto
    show "b1 \<down>\<^sup>* b2"
    proof (rule cr[rule_format])
      show "b1 \<leftrightarrow>\<^sup>* b2"
      proof (induct rule: rtranclp_induct[OF \<open>a \<rightarrow>\<^sup>* b2\<close>])
        from srtc_symmetric[OF rtc_implies_srtc[OF \<open>a \<rightarrow>\<^sup>* b1\<close>]] show "b1 \<leftrightarrow>\<^sup>* a" .
      next
        fix y z
        assume "a \<rightarrow>\<^sup>* y" and "y \<rightarrow> z" and "b1 \<leftrightarrow>\<^sup>* y"
        hence "(op \<leftrightarrow>)\<^sup>*\<^sup>* b1 y" and "y \<leftrightarrow> z" unfolding srtc_def by simp_all
        from rtranclp.intros(2)[OF \<open>(op \<leftrightarrow>)\<^sup>*\<^sup>* b1 y\<close> \<open>y \<leftrightarrow> z\<close>] show "b1 \<leftrightarrow>\<^sup>* z" unfolding srtc_def .
      qed
    qed
  qed
qed (rule confluence_implies_ChurchRosser)

lemma loc_confluence_implies_confluence:
  assumes lc: "is_loc_confluent" and wf: "wfP (r^--1)"
  shows "is_confluent"
proof -
  from lc loc_confluent_WCR have "WCR relset" by simp
  from wf wf_SN have "SN relset" by simp
  from Newman[OF \<open>SN relset\<close> \<open>WCR relset\<close>] confluent_CR show ?thesis by simp
qed

lemma loc_confluence_equiv_confluence:
  assumes "wfP (r^--1)"
  shows "is_loc_confluent = is_confluent"
proof
  assume "is_loc_confluent"
  from loc_confluence_implies_confluence[OF this assms] show "is_confluent" .
next
  assume "is_confluent"
  thus "is_loc_confluent" unfolding is_loc_confluent_def is_confluent_def
  proof (intro allI, intro impI)
    fix a b1 b2
    assume conf: "\<forall>a b1 b2. a \<rightarrow>\<^sup>* b1 \<and> a \<rightarrow>\<^sup>* b2 \<longrightarrow> b1 \<down>\<^sup>* b2" and "a \<rightarrow> b1 \<and> a \<rightarrow> b2"
    hence "a \<rightarrow> b1" and "a \<rightarrow> b2" by auto
    show "b1 \<down>\<^sup>* b2"
    proof (rule conf[rule_format, of a], intro conjI)
      from \<open>a \<rightarrow> b1\<close> show "a \<rightarrow>\<^sup>* b1" ..
    next
      from \<open>a \<rightarrow> b2\<close> show "a \<rightarrow>\<^sup>* b2" ..
    qed
  qed
qed

lemma ChurchRosser_unique_final:
  assumes "is_ChurchRosser" and "a \<rightarrow>\<^sup>* b1" and "a \<rightarrow>\<^sup>* b2" and "is_final b1" and "is_final b2"
  shows "b1 = b2"
proof -
  from \<open>is_ChurchRosser\<close> confluence_equiv_ChurchRosser confluent_CR have "CR relset" by simp
  from CR_imp_UNF[OF this] assms show ?thesis unfolding UNF_defs normalizability_def
    by (auto simp add: Enum.rtranclp_rtrancl_eq final_NF)
qed

end (*relation*)

subsection \<open>Advanced Results and the Generalized Newman Lemma\<close>

definition relbelow :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
  "relbelow ord z rel a b \<equiv> (rel a b \<and> ord a z \<and> ord b z)"

definition cbelow_1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
  "cbelow_1 ord z rel \<equiv> (relbelow ord z rel)\<^sup>+\<^sup>+"

definition cbelow :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
  "cbelow ord z rel a b \<equiv> (a = b \<and> ord b z) \<or> cbelow_1 ord z rel a b"

text \<open>Note that @{const cbelow} cannot be defined as the reflexive-transitive closure of
  @{const relbelow}, since it is in general not reflexive!\<close>

lemma cbelow_first_below:
  assumes "cbelow ord z rel a b"
  shows "ord a z"
using assms unfolding cbelow_def
proof
  assume "a = b \<and> ord b z"
  thus "ord a z" by simp
next
  assume "cbelow_1 ord z rel a b"
  thus "ord a z" unfolding cbelow_1_def
  proof (induct rule: tranclp_induct)
    fix y
    assume "relbelow ord z rel a y"
    thus "ord a z" unfolding relbelow_def by simp
  next
    assume "ord a z"
    thus "ord a z" .
  qed
qed

lemma cbelow_second_below:
  assumes "cbelow ord z rel a b"
  shows "ord b z"
using assms unfolding cbelow_def
proof
  assume "a = b \<and> ord b z"
  thus "ord b z" by simp
next
  assume "cbelow_1 ord z rel a b"
  thus "ord b z" unfolding cbelow_1_def
  proof (induct rule: tranclp_induct)
    fix y
    assume "relbelow ord z rel a y"
    thus "ord y z" unfolding relbelow_def by simp
  next
    fix y b
    assume "relbelow ord z rel y b"
    thus "ord b z" unfolding relbelow_def by simp
  qed
qed

lemma cbelow_intro [intro]:
  assumes main: "cbelow ord z rel a b" and "rel b c" and "ord c z"
  shows "cbelow ord z rel a c"
using main unfolding cbelow_def
proof (intro disjI2)
  assume cases: "(a = b \<and> ord b z) \<or> cbelow_1 ord z rel a b"
  from \<open>rel b c\<close> \<open>ord c z\<close> cbelow_second_below[OF main] have bc: "relbelow ord z rel b c"
    unfolding relbelow_def by simp
  from cases show "cbelow_1 ord z rel a c"
  proof
    assume "a = b \<and> ord b z"
    from this bc have "relbelow ord z rel a c" by simp
    thus ?thesis unfolding cbelow_1_def by simp
  next
    assume "cbelow_1 ord z rel a b"
    from this bc show ?thesis unfolding cbelow_1_def by (rule tranclp.intros(2))
  qed
qed

lemma cbelow_induct [consumes 1, case_names base step]:
  assumes a: "cbelow ord z rel a b"
    and base: "ord a z \<Longrightarrow> P a"
    and ind: "\<And>b c. [| cbelow ord z rel a b; rel b c; ord c z; P b |] ==> P c"
  shows "P b"
using a unfolding cbelow_def
proof
  assume "a = b \<and> ord b z"
  from this base show "P b" by simp
next
  assume "cbelow_1 ord z rel a b"
  thus "P b" unfolding cbelow_1_def
  proof (induct x\<equiv>a b)
    fix b
    assume "relbelow ord z rel a b"
    hence "rel a b" and "ord a z" and "ord b z" unfolding relbelow_def by simp_all
    hence "cbelow ord z rel a a" unfolding cbelow_def by simp
    from ind[OF this \<open>rel a b\<close> \<open>ord b z\<close> base[OF \<open>ord a z\<close>]] show "P b" .
  next
    fix b c
    assume IH: "(relbelow ord z rel)\<^sup>+\<^sup>+ a b" and "P b" and "relbelow ord z rel b c"
    hence "rel b c" and "ord b z" and "ord c z" unfolding relbelow_def by simp_all
    from IH have "cbelow ord z rel a b" unfolding cbelow_def cbelow_1_def by simp
    from ind[OF this \<open>rel b c\<close> \<open>ord c z\<close> \<open>P b\<close>] show "P c" .
  qed
qed

lemma cbelow_symmetric:
  assumes main: "cbelow ord z rel a b" and "symp rel"
  shows "cbelow ord z rel b a"
using main unfolding cbelow_def
proof
  assume a1: "a = b \<and> ord b z"
  show "b = a \<and> ord a z \<or> cbelow_1 ord z rel b a"
  proof
    from a1 show "b = a \<and> ord a z" by simp
  qed
next
  assume a2: "cbelow_1 ord z rel a b"
  show "b = a \<and> ord a z \<or> cbelow_1 ord z rel b a"
  proof (rule disjI2)
    from \<open>symp rel\<close> have "symp (relbelow ord z rel)" unfolding symp_def
    proof (intro allI, intro impI)
      fix x y
      assume rel_sym: "\<forall>x y. rel x y \<longrightarrow> rel y x"
      assume "relbelow ord z rel x y"
      hence "rel x y" and "ord x z" and "ord y z" unfolding relbelow_def by auto
      show "relbelow ord z rel y x" unfolding relbelow_def
      proof (intro conjI)
        from rel_sym \<open>rel x y\<close> show "rel y x" by simp
      next
        from \<open>ord y z\<close> show "ord y z" .
      next
        from \<open>ord x z\<close> show "ord x z" .
      qed
    qed
    from sym_trancl[to_pred, OF this] a2 show "cbelow_1 ord z rel b a"
      unfolding symp_def cbelow_1_def by simp
  qed
qed

lemma cbelow_transitive:
  assumes "cbelow ord z rel a b" and "cbelow ord z rel b c"
  shows "cbelow ord z rel a c"
proof (induct rule: cbelow_induct[OF \<open>cbelow ord z rel b c\<close>])
  from \<open>cbelow ord z rel a b\<close> show "cbelow ord z rel a b" .
next
  fix c0 c
  assume "cbelow ord z rel b c0" and "rel c0 c" and "ord c z" and "cbelow ord z rel a c0"
  show "cbelow ord z rel a c"
  proof
    from \<open>cbelow ord z rel a c0\<close> show "cbelow ord z rel a c0" .
  next
    from \<open>rel c0 c\<close> show "rel c0 c" .
  next
    from \<open>ord c z\<close> show "ord c z" .
  qed
qed

locale relation_order = relation + order +
  assumes refines: "(op \<rightarrow>) \<le> less^--1" and wf: "wfP less"
begin

definition is_loc_connective::"bool" where
  "is_loc_connective \<equiv> (\<forall>a b1 b2. a \<rightarrow> b1 \<and> a \<rightarrow> b2 \<longrightarrow> cbelow less a (op \<leftrightarrow>) b1 b2)"

lemma relation_refines:
  fixes a b::'a
  assumes "a \<rightarrow> b"
  shows "less b a"
using refines assms by auto

lemma relation_wf:
  shows "wfP ((op \<rightarrow>)^--1)"
using wfP_subset[OF wf, of "(op \<rightarrow>)^--1"] conversep_mono[of r "less^--1"] refines by simp

lemma rtc_implies_cbelow:
  assumes main: "a \<rightarrow>\<^sup>* b" and "less a c"
  shows "cbelow less c (op \<leftrightarrow>) a b"
using main
proof (induct rule: rtranclp_induct)
  from \<open>less a c\<close> show "cbelow less c (op \<leftrightarrow>) a a" unfolding cbelow_def by simp
next
  fix b0 b
  assume "a \<rightarrow>\<^sup>* b0" and "b0 \<rightarrow> b" and IH: "cbelow less c (op \<leftrightarrow>) a b0"
  show "cbelow less c (op \<leftrightarrow>) a b"
  proof
    from IH show "cbelow less c (op \<leftrightarrow>) a b0" .
  next
    from \<open>b0 \<rightarrow> b\<close> show "b0 \<leftrightarrow> b" by simp
  next
    from cbelow_second_below[OF IH] relation_refines[OF \<open>b0 \<rightarrow> b\<close>] show "less b c" by simp
  qed
qed

lemma cs_implies_cbelow:
  assumes "a \<down>\<^sup>* b" and "less a c" and "less b c"
  shows "cbelow less c (op \<leftrightarrow>) a b"
proof -
  from \<open>a \<down>\<^sup>* b\<close> obtain s where "a \<rightarrow>\<^sup>* s" and "b \<rightarrow>\<^sup>* s" unfolding cs_def by auto
  have sym: "symp (op \<leftrightarrow>)" unfolding symp_def
  proof (intro allI, intro impI)
    fix x y
    assume "x \<leftrightarrow> y"
    thus "y \<leftrightarrow> x" by auto
  qed
  from cbelow_transitive[OF rtc_implies_cbelow[OF \<open>a \<rightarrow>\<^sup>* s\<close> \<open>less a c\<close>]
       cbelow_symmetric[OF rtc_implies_cbelow[OF \<open>b \<rightarrow>\<^sup>* s\<close> \<open>less b c\<close>] sym]]
    show ?thesis .
qed

text \<open>The generalized Newman lemma, taken from @{cite Winkler1983}:\<close>

lemma loc_connectivity_implies_confluence:
  assumes is_loc_connective
  shows "is_confluent"
using assms unfolding is_loc_connective_def relation.is_confluent_def
proof (intro allI, intro impI)
  fix z x y::'a
  assume "\<forall>a b1 b2. a \<rightarrow> b1 \<and> a \<rightarrow> b2 \<longrightarrow> cbelow less a (op \<leftrightarrow>) b1 b2"
  hence A: "\<And>a b1 b2. a \<rightarrow> b1 \<Longrightarrow> a \<rightarrow> b2 \<Longrightarrow> cbelow less a (op \<leftrightarrow>) b1 b2" by simp
  assume "z \<rightarrow>\<^sup>* x \<and> z \<rightarrow>\<^sup>* y"
  thus "x \<down>\<^sup>* y"
  proof (induct z arbitrary: x y rule: wfP_induct[OF wf])
    fix z x y::'a
    assume IH: "\<forall>z0. less z0 z \<longrightarrow> (\<forall>x0 y0. z0 \<rightarrow>\<^sup>* x0 \<and> z0 \<rightarrow>\<^sup>* y0 \<longrightarrow> x0 \<down>\<^sup>* y0)"
      and "z \<rightarrow>\<^sup>* x \<and> z \<rightarrow>\<^sup>* y"
    hence "z \<rightarrow>\<^sup>* x" and "z \<rightarrow>\<^sup>* y" by auto
    from converse_rtranclpE[OF \<open>z \<rightarrow>\<^sup>* x\<close>] obtain x1 where "x = z \<or> (z \<rightarrow> x1 \<and> x1 \<rightarrow>\<^sup>* x)" by auto
    thus "x \<down>\<^sup>* y"
    proof
      assume "x = z"
      show ?thesis unfolding cs_def
      proof
        from \<open>x = z\<close> \<open>z \<rightarrow>\<^sup>* y\<close> show "x \<rightarrow>\<^sup>* y \<and> y \<rightarrow>\<^sup>* y" by simp
      qed
    next
      assume "z \<rightarrow> x1 \<and> x1 \<rightarrow>\<^sup>* x"
      hence "z \<rightarrow> x1" and "x1 \<rightarrow>\<^sup>* x" by auto
      from converse_rtranclpE[OF \<open>z \<rightarrow>\<^sup>* y\<close>] obtain y1 where "y = z \<or> (z \<rightarrow> y1 \<and> y1 \<rightarrow>\<^sup>* y)" by auto
      thus ?thesis
      proof
        assume "y = z"
        show ?thesis unfolding cs_def
        proof
          from \<open>y = z\<close> \<open>z \<rightarrow>\<^sup>* x\<close> show "x \<rightarrow>\<^sup>* x \<and> y \<rightarrow>\<^sup>* x" by simp
        qed
      next
        assume "z \<rightarrow> y1 \<and> y1 \<rightarrow>\<^sup>* y"
        hence "z \<rightarrow> y1" and "y1 \<rightarrow>\<^sup>* y" by auto
        have "x1 \<down>\<^sup>* y1"
        proof (induct rule: cbelow_induct[OF A[OF \<open>z \<rightarrow> x1\<close> \<open>z \<rightarrow> y1\<close>]])
          from cs_refl[of x1] show "x1 \<down>\<^sup>* x1" .
        next
          fix b c
          assume "cbelow less z (op \<leftrightarrow>) x1 b" and "b \<leftrightarrow> c" and "less c z" and "x1 \<down>\<^sup>* b"
          from \<open>x1 \<down>\<^sup>* b\<close> obtain w1 where "x1 \<rightarrow>\<^sup>* w1" and "b \<rightarrow>\<^sup>* w1" unfolding cs_def by auto
          from \<open>b \<leftrightarrow> c\<close> show "x1 \<down>\<^sup>* c"
          proof
            assume "b \<rightarrow> c"
            hence "b \<rightarrow>\<^sup>* c" by simp
            from \<open>cbelow less z (op \<leftrightarrow>) x1 b\<close> have "less b z" by (rule cbelow_induct)
            from IH[rule_format, OF this, of c w1] \<open>b \<rightarrow>\<^sup>* c\<close> \<open>b \<rightarrow>\<^sup>* w1\<close> have "c \<down>\<^sup>* w1" by simp
            then obtain w2 where "c \<rightarrow>\<^sup>* w2" and "w1 \<rightarrow>\<^sup>* w2" unfolding cs_def by auto
            show ?thesis unfolding cs_def
            proof
              from rtranclp_trans[OF \<open>x1 \<rightarrow>\<^sup>* w1\<close> \<open>w1 \<rightarrow>\<^sup>* w2\<close>] \<open>c \<rightarrow>\<^sup>* w2\<close>
                show "x1 \<rightarrow>\<^sup>* w2 \<and> c \<rightarrow>\<^sup>* w2" by simp
            qed
          next
            assume "c \<rightarrow> b"
            hence "c \<rightarrow>\<^sup>* b" by simp
            show ?thesis unfolding cs_def
            proof
              from rtranclp_trans[OF \<open>c \<rightarrow>\<^sup>* b\<close> \<open>b \<rightarrow>\<^sup>* w1\<close>] \<open>x1 \<rightarrow>\<^sup>* w1\<close>
                show "x1 \<rightarrow>\<^sup>* w1 \<and> c \<rightarrow>\<^sup>* w1" by simp
            qed
          qed
        qed
        then obtain w1 where "x1 \<rightarrow>\<^sup>* w1" and "y1 \<rightarrow>\<^sup>* w1" unfolding cs_def by auto
        from IH[rule_format, OF relation_refines[OF \<open>z \<rightarrow> x1\<close>], of x w1] \<open>x1 \<rightarrow>\<^sup>* x\<close> \<open>x1 \<rightarrow>\<^sup>* w1\<close>
          have "x \<down>\<^sup>* w1" by simp
        then obtain v where "x \<rightarrow>\<^sup>* v" and "w1 \<rightarrow>\<^sup>* v" unfolding cs_def by auto
        from IH[rule_format, OF relation_refines[OF \<open>z \<rightarrow> y1\<close>], of v y]
             rtranclp_trans[OF \<open>y1 \<rightarrow>\<^sup>* w1\<close> \<open>w1 \<rightarrow>\<^sup>* v\<close>] \<open>y1 \<rightarrow>\<^sup>* y\<close>
          have "v \<down>\<^sup>* y" by simp
        then obtain w where "v \<rightarrow>\<^sup>* w" and "y \<rightarrow>\<^sup>* w" unfolding cs_def by auto
        show ?thesis unfolding cs_def
        proof
          from rtranclp_trans[OF \<open>x \<rightarrow>\<^sup>* v\<close> \<open>v \<rightarrow>\<^sup>* w\<close>] \<open>y \<rightarrow>\<^sup>* w\<close> show "x \<rightarrow>\<^sup>* w \<and> y \<rightarrow>\<^sup>* w" by simp
        qed
      qed
    qed
  qed
qed

theorem loc_connectivity_equiv_ChurchRosser:
  shows "is_ChurchRosser = is_loc_connective"
proof
  assume "is_ChurchRosser"
  show "is_loc_connective" unfolding is_loc_connective_def
  proof (intro allI, intro impI)
    fix a b1 b2
    assume "a \<rightarrow> b1 \<and> a \<rightarrow> b2"
    hence "a \<rightarrow> b1" and "a \<rightarrow> b2" by simp_all
    hence "a \<rightarrow>\<^sup>* b1" and "a \<rightarrow>\<^sup>* b2" by simp_all
    from rtc_implies_srtc[OF \<open>a \<rightarrow>\<^sup>* b1\<close>] srtc_symmetric have "b1 \<leftrightarrow>\<^sup>* a" by simp
    from srtc_transitive[OF this rtc_implies_srtc[OF \<open>a \<rightarrow>\<^sup>* b2\<close>]] have "b1 \<leftrightarrow>\<^sup>* b2" .
    with \<open>is_ChurchRosser\<close> have "b1 \<down>\<^sup>* b2" unfolding is_ChurchRosser_def by simp
    from cs_implies_cbelow[OF this] relation_refines[of a] \<open>a \<rightarrow> b1\<close> \<open>a \<rightarrow> b2\<close>
      show "cbelow less a (op \<leftrightarrow>) b1 b2" by simp
  qed
next
  assume "is_loc_connective"
  hence "is_confluent" using loc_connectivity_implies_confluence by simp
  thus is_ChurchRosser using confluence_equiv_ChurchRosser by simp
qed

end (* relation_order *)

end