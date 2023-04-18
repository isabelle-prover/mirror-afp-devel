text \<open>In this file, we prove most results of section V: hyper-triples subsume many other triples,
as well as example 4.\<close>

theory Expressivity
  imports ProgramHyperproperties
begin


subsection \<open>Hoare Logic (HL)~\cite{HoareLogic}\<close>

text \<open>Definition 8\<close>
definition HL where
  "HL P C Q \<longleftrightarrow> (\<forall>\<sigma> \<sigma>' l. (l, \<sigma>) \<in> P \<and> (\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>') \<longrightarrow> (l, \<sigma>') \<in> Q)"

lemma HLI:
  assumes "\<And>\<sigma> \<sigma>' l. (l, \<sigma>) \<in> P \<Longrightarrow> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>' \<Longrightarrow> (l, \<sigma>') \<in> Q"
  shows "HL P C Q"
  using assms HL_def by blast


lemma hoarifyI:
  assumes "\<And>\<sigma> \<sigma>'. (\<sigma>, \<sigma>') \<in> S \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> \<sigma>' \<in> Q"
  shows "hoarify P Q S"
  by (metis assms hoarify_def prod.collapse)

definition HL_hyperprop where
  "HL_hyperprop P Q S \<longleftrightarrow> (\<forall>l. \<forall>p \<in> S. (l, fst p) \<in> P \<longrightarrow> (l, snd p) \<in> Q)"

lemma connection_HL:
  "HL P C Q \<longleftrightarrow> HL_hyperprop P Q (set_of_traces C)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then show ?B
    by (simp add: HL_def HL_hyperprop_def set_of_traces_def)
next
  assume ?B
  show ?A
  proof (rule HLI)
    fix \<sigma> \<sigma>' l assume asm0: "(l, \<sigma>) \<in> P" "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    then have "(\<sigma>, \<sigma>') \<in> set_of_traces C"
      by (simp add: set_of_traces_def)
    then show "(l, \<sigma>') \<in> Q"
      using \<open>HL_hyperprop P Q (set_of_traces C)\<close> asm0(1) HL_hyperprop_def by fastforce
  qed
qed

text \<open>Proposition 1\<close>
theorem HL_expresses_hyperproperties:
  "\<exists>H. (\<forall>C. hypersat C H \<longleftrightarrow> HL P C Q) \<and> k_hypersafety 1 H"
proof -
  let ?H = "HL_hyperprop P Q"
  have "\<And>C. hypersat C ?H \<longleftrightarrow> HL P C Q"
    by (simp add: connection_HL hypersat_def)
  moreover have "k_hypersafety 1 ?H"
  proof (rule k_hypersafetyI)
    fix S assume asm0: "\<not> HL_hyperprop P Q S"
    then obtain l p where "p \<in> S" "(l, fst p) \<in> P" "(l, snd p) \<notin> Q"
      using HL_hyperprop_def by blast
    let ?S = "{p}"
    have "max_k 1 ?S \<and> (\<forall>S''. ?S \<subseteq> S'' \<longrightarrow> \<not> HL_hyperprop P Q S'')"
      by (metis (no_types, lifting) One_nat_def \<open>(l, fst p) \<in> P\<close> \<open>(l, snd p) \<notin> Q\<close> card.empty card.insert
          empty_iff finite.intros(1) finite.intros(2) le_numeral_extra(4) max_k_def HL_hyperprop_def singletonI subsetD)
    then show "\<exists>S'\<subseteq>S. max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> HL_hyperprop P Q S'')"
      by (meson \<open>p \<in> S\<close> empty_subsetI insert_subsetI)
  qed
  ultimately show ?thesis
    by blast
qed

text \<open>Proposition 2\<close>
theorem encoding_HL:
  "HL P C Q \<longleftrightarrow> (hyper_hoare_triple (over_approx P) C (over_approx Q))" (is "?A \<longleftrightarrow> ?B")
proof (rule iffI)
  show "?B \<Longrightarrow> ?A"
  proof -
    assume asm0: ?B
    show ?A
    proof (rule HLI)
      fix \<sigma> \<sigma>' l
      assume asm1: "(l, \<sigma>) \<in> P" "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
      then have "over_approx P {(l, \<sigma>)}"
        by (simp add: over_approx_def)
      then have "(over_approx Q) (sem C {(l, \<sigma>)})"
        using asm0 hyper_hoare_tripleE by auto
      then show "(l, \<sigma>') \<in> Q"
        by (simp add: asm1(2) in_mono in_sem over_approx_def)
    qed
  qed
next
  assume r: ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume asm0: "over_approx P S"
    then have "S \<subseteq> P"
      by (simp add: over_approx_def)
    then have "sem C S \<subseteq> sem C P"
      by (simp add: sem_monotonic)
    then have "sem C S \<subseteq> Q"
      using r HL_def[of P C Q]
      by (metis (no_types, lifting) fst_conv in_mono in_sem snd_conv subrelI)      
    then show "over_approx Q (sem C S)"
      by (simp add: over_approx_def)
  qed
qed

lemma entailment_order_hoare:
  assumes "P \<subseteq> P'"
  shows "entails (over_approx P) (over_approx P')"
  by (simp add: assms entails_def over_approx_def subset_trans)


subsection \<open>Cartesian Hoare Logic (CHL)~\cite{CHL16}\<close>

text \<open>Notation 3\<close>
definition k_sem where
  "k_sem C states states' \<longleftrightarrow> (\<forall>i. (fst (states i) = fst (states' i) \<and> single_sem C (snd (states i)) (snd (states' i))))"

lemma k_semI:
  assumes "\<And>i. (fst (states i) = fst (states' i) \<and> single_sem C (snd (states i)) (snd (states' i)))"
  shows "k_sem C states states'"
  by (simp add: assms k_sem_def)

lemma k_semE:
  assumes "k_sem C states states'"
  shows "fst (states i) = fst (states' i) \<and> single_sem C (snd (states i)) (snd (states' i))"
  using assms k_sem_def by fastforce

text \<open>Definition 9\<close>
definition CHL where
  "CHL P C Q \<longleftrightarrow> (\<forall>states. states \<in> P \<longrightarrow> (\<forall>states'. k_sem C states states' \<longrightarrow> states' \<in> Q))"

lemma CHLI:
  assumes "\<And>states states'. states \<in> P \<Longrightarrow> k_sem C states states' \<Longrightarrow> states' \<in> Q"
  shows "CHL P C Q"
  by (simp add: assms CHL_def)

lemma CHLE:
  assumes "CHL P C Q"
      and "states \<in> P"
      and "k_sem C states states'"
    shows "states' \<in> Q"
  using assms(1) assms(2) assms(3) CHL_def by fast

definition encode_CHL where
  "encode_CHL from_nat x P S \<longleftrightarrow> (\<forall>states. (\<forall>i. states i \<in> S \<and> fst (states i) x = from_nat i) \<longrightarrow> states \<in> P)"


lemma encode_CHLI:
  assumes "\<And>states. (\<forall>i. states i \<in> S \<and> fst (states i) x = from_nat i) \<Longrightarrow> states \<in> P"
    shows "encode_CHL from_nat x P S"
  using assms(1) encode_CHL_def by force

lemma encode_CHLE:
  assumes "encode_CHL from_nat x P S"
      and "\<And>i. states i \<in> S"
      and "\<And>i. fst (states i) x = from_nat i"
    shows "states \<in> P"
  by (metis assms(1) assms(2) assms(3) encode_CHL_def)

lemma equal_change_lvar:
  assumes "fst \<phi> x = y"
  shows "\<phi> = ((fst \<phi>)(x := y), snd \<phi>)"
  using assms by fastforce


text \<open>Proposition 3\<close>
theorem encoding_CHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
  shows "CHL P C Q \<longleftrightarrow> \<Turnstile> {encode_CHL from_nat x P} C {encode_CHL from_nat x Q}" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume "encode_CHL from_nat x P S"
    then obtain asm0: "\<And>states states'. (\<And>i. states i \<in> S) \<Longrightarrow> (\<And>i.  fst (states i) x = from_nat i) \<Longrightarrow> states \<in> P"
      by (simp add: encode_CHLE)

    show "encode_CHL from_nat x Q (sem C S)"
    proof (rule encode_CHLI)
      fix states'
      assume asm1: "\<forall>i. states' i \<in> sem C S \<and> fst (states' i) x = from_nat i"

      let ?states = "\<lambda>i. (fst (states' i), SOME \<sigma>. (fst (states' i), \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd (states' i)))"

      show "states' \<in> Q"
        using \<open>?A\<close>
      proof (rule CHLE)
        show "?states \<in> P"
        proof (rule asm0)
          fix i
          let ?\<sigma> = "SOME \<sigma>. ((fst (states' i), \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (states' i))"
          have r: "(fst (states' i), ?\<sigma>) \<in> S \<and> \<langle>C, ?\<sigma>\<rangle> \<rightarrow> snd (states' i)"
            using someI_ex[of "\<lambda>\<sigma>. (fst (states' i), \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (states' i)"] asm1 in_sem by blast
          then show "?states i \<in> S"
            by blast
          show "fst (?states i) x = from_nat i"
            by (simp add: asm1)
        qed
        show "k_sem C ?states states'"
        proof (rule k_semI)
          fix i
          let ?\<sigma> = "SOME \<sigma>. ((fst (states' i), \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (states' i))"
          have r: "(fst (states' i), ?\<sigma>) \<in> S \<and> \<langle>C, ?\<sigma>\<rangle> \<rightarrow> snd (states' i)"
            using someI_ex[of "\<lambda>\<sigma>. (fst (states' i), \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (states' i)"] asm1 in_sem by blast
          then show "fst (?states i) = fst (states' i) \<and> \<langle>C, snd (?states i)\<rangle> \<rightarrow> snd (states' i)"
            by simp
        qed
      qed
    qed
  qed
next
  assume asm0: "\<Turnstile> {encode_CHL from_nat x P} C {encode_CHL from_nat x Q}"

  show "CHL P C Q"
  proof (rule CHLI)
    fix states states'
    assume asm1: "states \<in> P" "k_sem C states states'"

    let ?states = "\<lambda>i. ((fst (states i))(x := from_nat i), snd (states i))"
    let ?states' = "\<lambda>i. ((fst (states i))(x := from_nat i), snd (states' i))"
    let ?S = "range ?states"

    have "encode_CHL from_nat x Q (sem C ?S)"
      using asm0
    proof (rule hyper_hoare_tripleE)
      show "encode_CHL from_nat x P ?S"
      proof (rule encode_CHLI)
        fix f assume asm2: "\<forall>i. f i \<in> ?S \<and> fst (f i) x = from_nat i"
        have "f = ?states"
        proof (rule ext)
          fix i
          obtain j where j_def: "f i = ((fst (states j))(x := from_nat j), snd (states j))"
            using asm2 by fastforce
          then have "from_nat j = from_nat i"
            by (metis asm2 fst_conv fun_upd_same)
          then show "f i = ((fst (states i))(x := from_nat i), snd (states i))"
            by (metis j_def assms(3) injective_def)
        qed
        moreover have "?states \<in> P"
          using assms(1)
        proof (rule not_free_var_ofE)
          show "states \<in> P"
            using asm1(1) by simp
          fix i
          show "differ_only_by (fst (states i)) (fst ((fst (states i))(x := from_nat i), snd (states i))) x"
            by (simp add: differ_only_by_def)
          show "snd (states i) = snd ((fst (states i))(x := from_nat i), snd (states i))"
            by simp
        qed
        ultimately show "f \<in> P"
          by meson
      qed
    qed
    then have "?states' \<in> Q"
    proof (rule encode_CHLE)
      fix i
      show "fst ((fst (states i))(x := from_nat i), snd (states' i)) x = from_nat i"
        by simp
      moreover have "single_sem C (snd (?states i)) (snd (?states' i))"
        using asm1(2) k_sem_def by fastforce
      ultimately show "((fst (states i))(x := from_nat i), snd (states' i)) \<in> sem C ?S"
        using in_sem by fastforce
    qed
    show "states' \<in> Q"
      using assms(2) 
    proof (rule not_free_var_ofE[of Q x])
      show "?states' \<in> Q"
        by (simp add: \<open>(\<lambda>i. ((fst (states i))(x := from_nat i), snd (states' i))) \<in> Q\<close>)
      fix i show "differ_only_by (fst ((fst (states i))(x := from_nat i), snd (states' i))) (fst (states' i)) x"
        by (metis asm1(2) diff_by_update fst_conv k_sem_def)
    qed (auto)
  qed
qed

definition CHL_hyperprop where
  "CHL_hyperprop P Q S \<longleftrightarrow> (\<forall>l p. (\<forall>i. p i \<in> S) \<and> (\<lambda>i. (l i, fst (p i))) \<in> P \<longrightarrow> (\<lambda>i. (l i, snd (p i))) \<in> Q)"

lemma CHL_hyperpropI:
  assumes "\<And>l p. (\<forall>i. p i \<in> S) \<and> (\<lambda>i. (l i, fst (p i))) \<in> P \<Longrightarrow> (\<lambda>i. (l i, snd (p i))) \<in> Q"
  shows "CHL_hyperprop P Q S"
  by (simp add: assms CHL_hyperprop_def)

lemma CHL_hyperpropE:
  assumes "CHL_hyperprop P Q S"
      and "\<And>i. p i \<in> S"
      and "(\<lambda>i. (l i, fst (p i))) \<in> P"
    shows "(\<lambda>i. (l i, snd (p i))) \<in> Q"
  using assms(1) assms(2) assms(3) CHL_hyperprop_def by blast

text \<open>Proposition 10\<close>
theorem CHL_hyperproperty:
  "hypersat C (CHL_hyperprop P Q) \<longleftrightarrow> CHL P C Q" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule CHLI)
    fix states states'
    assume asm0: "states \<in> P" "k_sem C states states'"
    let ?p = "\<lambda>i. (snd (states i), snd (states' i))"
    let ?l = "\<lambda>i. fst (states i)"

    have "range ?p \<subseteq> set_of_traces C"
    proof (rule subsetI)
      fix x assume "x \<in> range ?p"
      then obtain i where "x = (snd (states i), snd (states' i))"
        by blast
      then show "x \<in> set_of_traces C"
        by (metis (mono_tags, lifting) CollectI asm0(2) k_sem_def set_of_traces_def)
    qed
    have "(\<lambda>i. (?l i, snd (?p i))) \<in> Q"
    proof (rule CHL_hyperpropE)
      show "CHL_hyperprop P Q (range ?p)"
      proof (rule CHL_hyperpropI)
        fix l p assume asm1: "(\<forall>i. p i \<in> range (\<lambda>i. (snd (states i), snd (states' i)))) \<and> (\<lambda>i. (l i, fst (p i))) \<in> P"
        then show "(\<lambda>i. (l i, snd (p i))) \<in> Q"
          using CHL_hyperprop_def[of P Q "set_of_traces C"] \<open>hypersat C (CHL_hyperprop P Q)\<close>
            \<open>range (\<lambda>i. (snd (states i), snd (states' i))) \<subseteq> set_of_traces C\<close> hypersat_def subset_iff
          by blast
      qed          
      show "(\<lambda>i. (fst (states i), fst (snd (states i), snd (states' i)))) \<in> P"
        by (simp add: asm0(1))
      fix i show "(snd (states i), snd (states' i)) \<in> range (\<lambda>i. (snd (states i), snd (states' i)))"
        by blast
    qed
    moreover have "states' = (\<lambda>i. (?l i, snd (?p i)))"
    proof (rule ext)
      fix i show "states' i = (fst (states i), snd (snd (states i), snd (states' i)))"
        by (metis asm0(2) k_sem_def prod.exhaust_sel sndI)
    qed
    ultimately show "states' \<in> Q"
      by auto
  qed
next
  assume asm0: "CHL P C Q"
  have "CHL_hyperprop P Q (set_of_traces C)"
  proof (rule CHL_hyperpropI)
    fix l p assume asm1: "(\<forall>i. p i \<in> set_of_traces C) \<and> (\<lambda>i. (l i, fst (p i))) \<in> P"

    show "(\<lambda>i. (l i, snd (p i))) \<in> Q"
      using asm0
    proof (rule CHLE)
      show "(\<lambda>i. (l i, fst (p i))) \<in> P"
        by (simp add: asm1)
      show "k_sem C (\<lambda>i. (l i, fst (p i))) (\<lambda>i. (l i, snd (p i)))"
      proof (rule k_semI)
        fix i show "fst (l i, fst (p i)) = fst (l i, snd (p i)) \<and> \<langle>C, snd (l i, fst (p i))\<rangle> \<rightarrow> snd (l i, snd (p i))"
          using asm1 in_set_of_traces by fastforce
      qed
    qed
  qed
  then show "hypersat C (CHL_hyperprop P Q)"
    by (simp add: hypersat_def)
qed



theorem k_hypersafety_HL_hyperprop:
  fixes P :: "('i \<Rightarrow> ('lvar, 'lval, 'pvar, 'pval) state) set"
  assumes "finite (UNIV :: 'i set)"
      and "card (UNIV :: 'i set) = k"
    shows "k_hypersafety k (CHL_hyperprop P Q)"
proof (rule k_hypersafetyI)
  fix S
  assume "\<not> CHL_hyperprop P Q S"
  then obtain l p where asm0: "\<forall>i. p i \<in> S" "(\<lambda>i. (l i, fst (p i))) \<in> P"
    "(\<lambda>i. (l i, snd (p i))) \<notin> Q"
    using CHL_hyperprop_def by blast
  let ?S = "range p"
  have "max_k k ?S"
    by (metis assms(1) assms(2) card_image_le finite_imageI max_k_def)
  moreover have "\<And>S''. ?S \<subseteq> S'' \<Longrightarrow> \<not> CHL_hyperprop P Q S''"
    by (meson asm0(2) asm0(3) CHL_hyperprop_def range_subsetD)
  ultimately show "\<exists>S'\<subseteq>S. max_k k S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> CHL_hyperprop P Q S'')"
    by (meson asm0(1) image_subsetI)
qed



subsection \<open>Incorrectness Logic~\cite{IncorrectnessLogic} or Reverse Hoare Logic~\cite{ReverseHL} (IL))\<close>

text \<open>Definition 11\<close>

definition IL where
  "IL P C Q \<longleftrightarrow> Q \<subseteq> sem C P"

lemma equiv_def_incorrectness:
  "IL P C Q \<longleftrightarrow> (\<forall>l \<sigma>'. (l, \<sigma>') \<in> Q \<longrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> P \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'))"
  by (simp add: in_sem IL_def subset_iff)

definition IL_hyperprop where
  "IL_hyperprop P Q S \<longleftrightarrow> (\<forall>l \<sigma>'. (l, \<sigma>') \<in> Q \<longrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> P \<and> (\<sigma>, \<sigma>') \<in> S))"


lemma IL_hyperpropI:
  assumes "\<And>l \<sigma>'. (l, \<sigma>') \<in> Q \<Longrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> P \<and> (\<sigma>, \<sigma>') \<in> S)"
  shows "IL_hyperprop P Q S"
  by (simp add: assms IL_hyperprop_def)

text \<open>Proposition 11\<close>
lemma IL_expresses_hyperproperties:
  "IL P C Q \<longleftrightarrow> IL_hyperprop P Q (set_of_traces C)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule IL_hyperpropI)
    fix l \<sigma>' assume asm0: "(l, \<sigma>') \<in> Q"
    then obtain \<sigma> where "(l, \<sigma>) \<in> P" "single_sem C \<sigma> \<sigma>'"
      using \<open>IL P C Q\<close> equiv_def_incorrectness by blast
    then show "\<exists>\<sigma>. (l, \<sigma>) \<in> P \<and> (\<sigma>, \<sigma>') \<in> set_of_traces C"
      using set_of_traces_def by auto
  qed
next
  assume ?B
  have "Q \<subseteq> sem C P"
  proof (rule subsetPairI)
    fix l \<sigma>' assume "(l, \<sigma>') \<in> Q"
    then obtain \<sigma> where "(\<sigma>, \<sigma>') \<in> set_of_traces C" "(l, \<sigma>) \<in> P"
      by (meson \<open>IL_hyperprop P Q (set_of_traces C)\<close> IL_hyperprop_def)
    then show "(l, \<sigma>') \<in> sem C P"
      using in_set_of_traces_then_in_sem by blast
  qed
  then show ?A
    by (simp add: IL_def)
qed


lemma IL_consequence:
  assumes "IL P C Q"
      and "(l, \<sigma>') \<in> Q"
    shows "\<exists>\<sigma>. (l, \<sigma>) \<in> P \<and> single_sem C \<sigma> \<sigma>'"
  using assms(1) assms(2) equiv_def_incorrectness by blast

text \<open>Proposition 4\<close>
theorem encoding_IL:
  "IL P C Q \<longleftrightarrow> (hyper_hoare_triple (under_approx P) C (under_approx Q))" (is "?A \<longleftrightarrow> ?B")
proof (rule iffI)
  show "?B \<Longrightarrow> ?A"
  proof -
    assume ?B
    then have "under_approx Q (sem C P)"
      by (simp add: hyper_hoare_triple_def under_approx_def)
    then show ?A
      by (simp add: IL_def under_approx_def)
  qed
  assume ?A
  then show ?B
    by (simp add: hyper_hoare_triple_def sem_monotonic IL_def under_approx_def subset_trans)
qed

lemma entailment_order_reverse_hoare:
  assumes "P \<subseteq> P'"
  shows "entails (under_approx P') (under_approx P)"
  by (simp add: assms dual_order.trans entails_def under_approx_def)

definition incorrectify where
  "incorrectify p = under_approx { \<sigma> |\<sigma>. p \<sigma>}"

lemma incorrectifyI:
  assumes "\<And>\<sigma>. p \<sigma> \<Longrightarrow> \<sigma> \<in> S"
  shows "incorrectify p S"
  by (metis assms incorrectify_def mem_Collect_eq subsetI under_approx_def)

lemma incorrectifyE:
  assumes "incorrectify p S"
      and "p \<sigma>"
    shows "\<sigma> \<in> S"
  by (metis CollectI assms(1) assms(2) in_mono incorrectify_def under_approx_def)

lemma simple_while_incorrectness:
  assumes "\<And>n. hyper_hoare_triple (incorrectify (p n)) C (incorrectify (p (Suc n)))"
  shows "hyper_hoare_triple (incorrectify (p 0)) (While C) (incorrectify (\<lambda>\<sigma>. \<exists>n. p n \<sigma>))" 
proof (rule consequence_rule)
  show "entails (incorrectify (p 0)) (incorrectify (p 0))"
    by (simp add: entailsI)
  show "hyper_hoare_triple (incorrectify (p 0)) (While C) (natural_partition (\<lambda>n. incorrectify (p n)))"
    by (meson assms while_rule)

  have "entails (incorrectify (\<lambda>\<sigma>. \<exists>n. p n \<sigma>)) (natural_partition (\<lambda>n. incorrectify (p n)))"
  proof (rule entailsI)
    fix S assume asm0: "incorrectify (\<lambda>\<sigma>. \<exists>n. p n \<sigma>) S"
    then have "under_approx { \<sigma> |\<sigma> n. p n \<sigma>} S"
      by (metis incorrectify_def)
    let ?F = "\<lambda>n. S"
    show "natural_partition (\<lambda>n. incorrectify (p n)) S"
    proof (rule natural_partitionI)
      show "\<And>n. incorrectify (p n) (?F n)"
        by (metis asm0 incorrectifyE incorrectifyI)
      show "S = \<Union> (range ?F)"
        by simp
    qed
  qed


  show "entails (natural_partition (\<lambda>n. incorrectify (p n))) (incorrectify (\<lambda>\<sigma>. \<exists>n. p n \<sigma>))"
  proof (rule entailsI)
    fix S assume asm0: "natural_partition (\<lambda>n. incorrectify (p n)) S"
    then obtain F where "S = (\<Union>n. F n)" "\<And>n. incorrectify (p n) (F n)"
      using natural_partitionE by blast
    show "incorrectify (\<lambda>\<sigma>. \<exists>n. p n \<sigma>) S"
    proof (rule incorrectifyI)
      fix \<sigma> assume "\<exists>n. p n \<sigma>"
      then obtain n where "p n \<sigma>"
        by blast
      then have "\<sigma> \<in> F n"
        by (meson \<open>\<And>n. incorrectify (p n) (F n)\<close> incorrectifyE)
      then show "\<sigma> \<in> S"
        using \<open>S = \<Union> (range F)\<close> by blast
    qed
  qed
qed

definition sat_for_l where
  "sat_for_l l P \<longleftrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> P)"

theorem incorrectness_hyperliveness:
  assumes "\<And>l. sat_for_l l Q \<Longrightarrow> sat_for_l l P"
  shows "hyperliveness (IL_hyperprop P Q)"
proof (rule hyperlivenessI)
  fix S
  let ?S = "S \<union> {(\<sigma>, \<sigma>') |\<sigma> \<sigma>' l. (l, \<sigma>') \<in> Q \<and> (l, \<sigma>) \<in> P }"
  have "IL_hyperprop P Q ?S"
  proof (rule IL_hyperpropI)
    fix l \<sigma>'
    assume asm0: "(l, \<sigma>') \<in> Q"
    then obtain \<sigma> where "(l, \<sigma>) \<in> P"
      by (meson assms sat_for_l_def)
    then show "\<exists>\<sigma>. (l, \<sigma>) \<in> P \<and> (\<sigma>, \<sigma>') \<in> ?S"
      using asm0 by auto
  qed
  then show "\<exists>S'. S \<subseteq> S' \<and> IL_hyperprop P Q S'"
    by auto
qed


subsection \<open>Relational Incorrectness Logic~\cite{InsecurityLogic} (RIL)\<close>

text \<open>Definition 11\<close>
definition RIL where
  "RIL P C Q \<longleftrightarrow> (\<forall>states' \<in> Q. \<exists>states \<in> P. k_sem C states states')"

lemma RILI:
  assumes "\<And>states'. states' \<in> Q \<Longrightarrow> (\<exists>states \<in> P. k_sem C states states')"
  shows "RIL P C Q"
  by (simp add: assms RIL_def)

lemma RILE:
  assumes "RIL P C Q"
      and "states' \<in> Q"
    shows "\<exists>states \<in> P. k_sem C states states'"
  using assms(1) assms(2) RIL_def by blast


definition RIL_hyperprop where
  "RIL_hyperprop P Q S \<longleftrightarrow> (\<forall>l states'. (\<lambda>i. (l i, states' i)) \<in> Q
         \<longrightarrow> (\<exists>states. (\<lambda>i. (l i, states i)) \<in> P \<and> (\<forall>i. (states i, states' i) \<in> S)))"

lemma RIL_hyperpropI:
  assumes "\<And>l states'. (\<lambda>i. (l i, states' i)) \<in> Q \<Longrightarrow> (\<exists>states. (\<lambda>i. (l i, states i)) \<in> P \<and> (\<forall>i. (states i, states' i) \<in> S))"
  shows "RIL_hyperprop P Q S"
  by (simp add: assms RIL_hyperprop_def)


lemma RIL_hyperpropE:
  assumes "RIL_hyperprop P Q S"
      and "(\<lambda>i. (l i, states' i)) \<in> Q"
    shows "\<exists>states. (\<lambda>i. (l i, states i)) \<in> P \<and> (\<forall>i. (states i, states' i) \<in> S)"
  using assms(1) assms(2) RIL_hyperprop_def by blast

lemma useful:
  "states' = (\<lambda>i. ((fst \<circ> states') i, (snd \<circ> states') i))"
proof (rule ext)
  fix i show "states' i = ((fst \<circ> states') i, (snd \<circ> states') i)"
    by auto
qed

text \<open>Proposition 12\<close>
theorem RIL_expresses_hyperproperties:
  "hypersat C (RIL_hyperprop P Q) \<longleftrightarrow> RIL P C Q" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule RILI)
    fix states' assume asm0: "states' \<in> Q"
    then obtain states where asm0: "(\<lambda>i. ((fst \<circ> states') i, states i)) \<in> P \<and> (\<forall>i. (states i, (snd \<circ> states') i) \<in> set_of_traces C)"
      using RIL_hyperpropE[of P Q "set_of_traces C" "fst \<circ> states'" "snd \<circ> states'"] \<open>?A\<close>
      using hypersat_def by auto

    moreover have "k_sem C (\<lambda>i. ((fst \<circ> states') i, states i)) states'"
    proof (rule k_semI)
      fix i 
      have "\<langle>C, snd ((fst \<circ> states') i, states i)\<rangle> \<rightarrow> snd (states' i)"
        using calculation set_of_traces_def by auto
      then show "fst ((fst \<circ> states') i, states i) = fst (states' i) \<and> \<langle>C, snd ((fst \<circ> states') i, states i)\<rangle> \<rightarrow> snd (states' i)"
        by simp
    qed
    ultimately show "\<exists>states\<in>P. k_sem C states states'"
      by fast
  qed
next
  assume ?B
  have "RIL_hyperprop P Q (set_of_traces C)"
  proof (rule RIL_hyperpropI)
    fix l states'
    assume asm0: "(\<lambda>i. (l i, states' i)) \<in> Q"
    then obtain states where "states \<in> P" "k_sem C states (\<lambda>i. (l i, states' i))"
      using \<open>RIL P C Q\<close> RILE by blast
    moreover have "(\<lambda>i. (l i, (snd \<circ> states) i)) = states"
    proof (rule ext)
      fix i show "(l i, (snd \<circ> states) i) = states i"
        by (metis calculation(2) comp_apply fst_conv k_sem_def surjective_pairing)
    qed
    moreover have "\<And>i. ((snd \<circ> states) i, states' i) \<in> set_of_traces C"
      by (metis (mono_tags, lifting) calculation(2) comp_apply in_set_of_traces k_sem_def snd_conv)
    ultimately show "\<exists>states. (\<lambda>i. (l i, states i)) \<in> P \<and> (\<forall>i. (states i, states' i) \<in> set_of_traces C)"
      by force
  qed
  then show ?A
    using hypersat_def by blast
qed

definition k_sat_for_l where
  "k_sat_for_l l P \<longleftrightarrow> (\<exists>\<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P)"

theorem RIL_hyperprop_hyperlive:
  assumes "\<And>l. k_sat_for_l l Q \<Longrightarrow> k_sat_for_l l P"
  shows "hyperliveness (RIL_hyperprop P Q)"
proof (rule hyperlivenessI)
  fix S
  have "RIL_hyperprop P Q UNIV"
    by (meson assms RIL_hyperpropI iso_tuple_UNIV_I k_sat_for_l_def)
  then show "\<exists>S'. S \<subseteq> S' \<and> RIL_hyperprop P Q S'"
    by blast
qed


definition strong_pre_insec where
  "strong_pre_insec from_nat x c P S \<longleftrightarrow> (\<forall>states \<in> P.
(\<forall>i. fst (states i) x = from_nat i) \<longrightarrow> (\<exists>r. \<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S)) \<and>
(\<forall>states. (\<forall>i. states i \<in> S) \<and> (\<forall>i. fst (states i) x = from_nat i) \<and>
(\<forall>i j. fst (states i) c = fst (states j) c) \<longrightarrow> states \<in> P)"

lemma strong_pre_insecI:
  assumes "\<And>states. states \<in> P \<Longrightarrow> (\<forall>i. fst (states i) x = from_nat i)
  \<Longrightarrow> (\<exists>r. \<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S)"
      and "\<And>states. (\<forall>i. states i \<in> S) \<Longrightarrow> (\<forall>i. fst (states i) x = from_nat i) \<Longrightarrow> (\<forall>i j. fst (states i) c = fst (states j) c) \<Longrightarrow> states \<in> P"
    shows "strong_pre_insec from_nat x c P S"
  by (simp add: assms(1) assms(2) strong_pre_insec_def)

lemma strong_pre_insecE:
  assumes "strong_pre_insec from_nat x c P S"
      and "\<And>i. states i \<in> S"
      and "\<And>i. fst (states i) x = from_nat i"
      and "\<And>i j. fst (states i) c = fst (states j) c"
    shows "states \<in> P"
  by (meson assms(1) assms(2) assms(3) assms(4) strong_pre_insec_def)


definition pre_insec where
  "pre_insec from_nat x c P S \<longleftrightarrow> (\<forall>states \<in> P.
(\<forall>i. fst (states i) x = from_nat i)
  \<longrightarrow> (\<exists>r. \<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S))"

lemma pre_insecI:
  assumes "\<And>states. states \<in> P \<Longrightarrow> (\<forall>i. fst (states i) x = from_nat i)
  \<Longrightarrow> (\<exists>r. \<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S)"
    shows "pre_insec from_nat x c P S"
  by (simp add: assms(1) pre_insec_def)

lemma strong_pre_implies_pre:
  assumes "strong_pre_insec from_nat x c P S"
  shows "pre_insec from_nat x c P S"
  by (meson assms pre_insecI strong_pre_insec_def)

lemma pre_insecE:
  assumes "pre_insec from_nat x c P S"
      and "states \<in> P"
      and "\<And>i. fst (states i) x = from_nat i"
    shows "\<exists>r. \<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S"
  by (meson assms(1) assms(2) assms(3) pre_insec_def)




definition post_insec where
  "post_insec from_nat x c Q S \<longleftrightarrow> (\<forall>states \<in> Q. (\<forall>i. fst (states i) x = from_nat i)
  \<longrightarrow> (\<exists>r. (\<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S)))"

lemma post_insecE:
  assumes "post_insec from_nat x c Q S"
      and "states \<in> Q"
      and "\<And>i. fst (states i) x = from_nat i"
    shows "\<exists>r. (\<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S)"
  by (meson assms(1) assms(2) assms(3) post_insec_def)

lemma post_insecI:
  assumes "\<And>states. states \<in> Q \<Longrightarrow> (\<forall>i. fst (states i) x = from_nat i)
  \<Longrightarrow> (\<exists>r. (\<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> S))"
  shows "post_insec from_nat x c Q S"
  by (simp add: assms post_insec_def)

lemma same_pre_post:
  "pre_insec from_nat x c Q S \<longleftrightarrow> post_insec from_nat x c Q S"
  by (simp add: post_insec_def pre_insec_def)

theorem can_be_sat:
  fixes x :: "'lvar"
  assumes "\<And>l l' \<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P \<longleftrightarrow> (\<lambda>i. (l' i, \<sigma> i)) \<in> P"  (* P does not depend on logical variables *)
      and "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))" (* |lval| \<ge> |PStates^k| *)
      and "x \<noteq> c"
      and "injective from_nat"
    shows "sat (strong_pre_insec from_nat x c (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set))"
proof -

  let ?S = "\<Union>states\<in>P. { (((fst (states i))(x := from_nat i))(c := indexify (\<lambda>i. snd (states i))), snd (states i)) |i. True}"

  have "strong_pre_insec from_nat x c P ?S"
  proof (rule strong_pre_insecI)
    fix states
    assume asm0: "states \<in> P" "\<forall>i. fst (states i) x = from_nat i"
    define r where "r = indexify (\<lambda>i. snd (states i))"
    have "\<And>i. ((fst (states i))(c := r), snd (states i)) \<in> { (((fst (states i))(x := from_nat i))(c := indexify (\<lambda>i. snd (states i))), snd (states i)) |i. True}"
    proof -
      fix i
      show "((fst (states i))(c := r), snd (states i)) \<in> { (((fst (states i))(x := from_nat i))(c := indexify (\<lambda>i. snd (states i))), snd (states i)) |i. True}"
        using asm0(2) r_def by fastforce
    qed
    then show "\<exists>r. \<forall>i. ((fst (states i))(c := r), snd (states i)) \<in> ?S"
      by (meson UN_I asm0(1))
  next
    fix states
    
    assume asm0: "\<forall>i. states i \<in> ?S" "\<forall>i. fst (states i) x = from_nat i" "\<forall>i j. fst (states i) c = fst (states j) c"

    let ?P = "\<lambda>i states'. states' \<in> P \<and> states i \<in> { (((fst (states' i))(x := from_nat i))(c := indexify (\<lambda>i. snd (states' i))), snd (states' i)) |i. True}"

    let ?states = "\<lambda>i. SOME states'. ?P i states'"
    have r: "\<And>i. ?P i (?states i)"
    proof -
      fix i 
      show "?P i (?states i)"
      proof (rule someI_ex[of "?P i"])
        show "\<exists>states'. states' \<in> P \<and> states i \<in> { (((fst (states' i))(x := from_nat i))(c := indexify (\<lambda>i. snd (states' i))), snd (states' i)) |i. True}"
          using asm0(1) by fastforce
      qed
    qed
    moreover have rr: "\<And>i. fst (states i) c = indexify (\<lambda>j. snd (?states i j)) \<and> snd (?states i i) = snd (states i)"
    proof -
      fix i
      obtain j where j_def: "states i = (((fst ((?states i) j))(x := from_nat j))(c := indexify (\<lambda>k. snd ((?states i) k))), snd ((?states i) j))"
        using r[of i] by blast
      then have r1: "snd (?states i j) = snd (states i)"
        by (metis (no_types, lifting) snd_conv)
      then have "from_nat i = from_nat j"
        by (metis (no_types, lifting) j_def asm0(2) assms(3) fst_conv fun_upd_same fun_upd_twist)
      then have "i = j"
        by (meson assms(4) injective_def)
      show "fst (states i) c = indexify (\<lambda>j. snd (?states i j)) \<and> snd (?states i i) = snd (states i)"
      proof
        show "fst (states i) c = indexify (\<lambda>j. snd (?states i j))"
          by (metis (no_types, lifting) j_def fst_conv fun_upd_same)
        show "snd (?states i i) = snd (states i)"
          using \<open>i = j\<close> r1 by blast
      qed
    qed
    moreover have r0: "\<And>i j. (\<lambda>n. snd (?states i n)) = (\<lambda>n. snd (?states j n))"
    proof -
      fix i j
      have "indexify (\<lambda>n. snd (?states i n)) = indexify (\<lambda>n. snd (?states j n))"
        using asm0(3) rr by fastforce
      then show "(\<lambda>n. snd (?states i n)) = (\<lambda>n. snd (?states j n))"
        by (meson assms(2) injective_def)
    qed
    obtain k :: 'a where "True" by blast
    then have "?states k \<in> P"
      using UN_iff[of _ "\<lambda>states. {((fst (states i))(x := from_nat i, c := indexify (\<lambda>i. snd (states i))), snd (states i)) |i. True}" P]
        asm0(1) someI_ex[of "\<lambda>y. y \<in> P \<and> states k \<in> {((fst (y i))(x := from_nat i, c := indexify (\<lambda>i. snd (y i))), snd (y i)) |i. True}"]
      by fast
    moreover have "\<And>i. snd (?states k i) = snd (states i)"
    proof -
      fix i 
      have "snd (?states i i) = snd (states i)"
        using rr by blast
      moreover have "(\<lambda>n. snd (?states i n)) i = (\<lambda>n. snd (?states k n)) i"
        by (metis r0)
      ultimately show "snd (?states k i) = snd (states i)"
        by auto
    qed
    moreover have "(\<lambda>i. ((\<lambda>i. fst (?states k i)) i, (\<lambda>i. snd (states i)) i)) \<in> P \<longleftrightarrow> (\<lambda>i. ((\<lambda>i. fst (states i)) i, (\<lambda>i. snd (states i)) i)) \<in> P" 
      using assms(1) by fast
    moreover have "(\<lambda>i. ((\<lambda>i. fst (states i)) i, (\<lambda>i. snd (states i)) i)) = states"
    proof (rule ext)
      fix i show "(fst (states i), snd (states i)) = states i"
        by simp
    qed
    moreover have "(\<lambda>i. ((\<lambda>i. fst (?states k i)) i, (\<lambda>i. snd (states i)) i)) = ?states k"
    proof (rule ext)
      fix i show "(\<lambda>i. ((\<lambda>i. fst (?states k i)) i, (\<lambda>i. snd (states i)) i)) i = ?states k i"
        by (metis (no_types, lifting) calculation(4) prod.exhaust_sel)
    qed
    ultimately show "states \<in> P" by argo
  qed
  then show "sat (strong_pre_insec from_nat x c P)"
    by (meson sat_def)
qed

theorem encode_insec:
  assumes "injective from_nat"
      and "sat (strong_pre_insec from_nat x c (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set))"
      and "not_free_var_of P x \<and> not_free_var_of P c"
      and "not_free_var_of Q x \<and> not_free_var_of Q c"
      and "c \<noteq> x"

    shows "RIL P C Q \<longleftrightarrow> \<Turnstile> {pre_insec from_nat x c P} C {post_insec from_nat x c Q}" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume asm0: "pre_insec from_nat x c P S"

    show "post_insec from_nat x c Q (sem C S)"
    proof (rule post_insecI)
      fix states' assume asm1: "states' \<in> Q" "\<forall>i. fst (states' i) x = from_nat i"
      then obtain states where "states \<in> P" "k_sem C states states'"
        using \<open>RIL P C Q\<close> RILE by blast
      then obtain r where asm2: "\<And>i. ((fst (states i))(c := r), snd (states i)) \<in> S"
        using pre_insecE[of from_nat x c P S states]
        by (metis asm0 asm1(2) k_sem_def)
      then show "\<exists>r. \<forall>i. ((fst (states' i))(c := r), snd (states' i)) \<in> sem C S"
        by (metis (mono_tags, opaque_lifting) \<open>k_sem C states states'\<close> k_sem_def single_step_then_in_sem)
    qed
  qed
next
  assume asm0: ?B
  show ?A
  proof (rule RILI)
    fix states' assume asm1: "states' \<in> Q"
    obtain S where asm2: "strong_pre_insec from_nat x c P S"
      by (meson assms(2) sat_def)
    then have asm3: "post_insec from_nat x c Q (sem C S)"
      by (meson asm0 hyper_hoare_tripleE strong_pre_implies_pre)

    let ?states' = "\<lambda>i. ((fst (states' i))(x := from_nat i), snd (states' i))"
    have "?states' \<in> Q"
      by (metis (no_types, lifting) asm1 assms(4) diff_by_update fstI not_free_var_of_def snd_conv)
    then obtain r where r_def: "\<And>i. ((fst (?states' i))(c := r), snd (?states' i)) \<in> sem C S"
      using asm3 post_insecE[of from_nat x c Q] by fastforce

    let ?states = "\<lambda>i. SOME \<sigma>. ((fst (?states' i))(c := r), \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd (?states' i))"

    have asm4: "\<And>i. ((fst (?states' i))(c := r), (?states i)) \<in> S \<and> single_sem C (?states i) (snd (?states' i))"
    proof -
      fix i 
      have "\<exists>\<sigma>. ((fst (?states' i))(c := r), \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd (?states' i))"
        by (metis r_def fst_conv in_sem snd_conv)
      then show "((fst (?states' i))(c := r), (?states i)) \<in> S \<and> single_sem C (?states i) (snd (?states' i))"
        using someI_ex[of "\<lambda>\<sigma>. ((fst (?states' i))(c := r), \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd (?states' i))"]
        by blast
    qed
    moreover have r0: "(\<lambda>i. ((fst (?states' i))(c := r), (?states i))) \<in> P"
      using asm2
    proof (rule strong_pre_insecE)
      fix i
      show "(\<lambda>i. ((fst (?states' i))(c := r), (?states i))) i \<in> S"
        using calculation by blast
      show "fst ((\<lambda>i. ((fst (?states' i))(c := r), (?states i))) i) x = from_nat i"
        using assms(5) by auto
      fix j
      show "fst ((\<lambda>i. ((fst (?states' i))(c := r), (?states i))) i) c = fst ((\<lambda>i. ((fst (?states' i))(c := r), (?states i))) j) c"
        by fastforce
    qed
    have r1: "(\<lambda>i. (((fst (?states' i))(c := r))(x := fst (states' i) x), (?states i))) \<in> P"
    proof (rule not_free_var_ofE[of P x])
      show "(\<lambda>i. ((fst (?states' i))(c := r), (?states i))) \<in> P"
        using r0 by fastforce
      show "not_free_var_of P x"
        by (simp add: assms(3))
      fix i
      show "differ_only_by
          (fst ((fst ((fst (states' i))(x := from_nat i), snd (states' i)))(c := r), ?states i))
          (fst ((fst ((fst (states' i))(x := from_nat i), snd (states' i)))(c := r, x := fst (states' i) x), ?states i)) x"
        by (metis (mono_tags, lifting) diff_by_comm diff_by_update fst_conv)
    qed (auto)
    have "(\<lambda>i. ((((fst (?states' i))(c := r))(x := fst (states' i) x))(c := fst (states' i) c), (?states i))) \<in> P"
    proof (rule not_free_var_ofE)
      show "(\<lambda>i. (((fst (?states' i))(c := r))(x := fst (states' i) x), (?states i))) \<in> P"
        using r1 by fastforce
      show "not_free_var_of P c"
        by (simp add: assms(3))
      fix i show "differ_only_by
          (fst ((fst ((fst (states' i))(x := from_nat i), snd (states' i)))(c := r, x := fst (states' i) x), ?states i))
          (fst ((fst ((fst (states' i))(x := from_nat i), snd (states' i)))(c := r, x := fst (states' i) x, c := fst (states' i) c), ?states i))
          c"
        by (metis (mono_tags, lifting) diff_by_comm diff_by_update fst_conv)
    qed (auto)
    moreover have "(\<lambda>i. ((((fst (?states' i))(c := r))(x := fst (states' i) x))(c := fst (states' i) c), (?states i)))
      = (\<lambda>i. (fst (states' i), (?states i)))"
    proof (rule ext)
      fix i show "(\<lambda>i. ((((fst (?states' i))(c := r))(x := fst (states' i) x))(c := fst (states' i) c), (?states i))) i
      = (\<lambda>i. (fst (states' i), (?states i))) i"
        by force
    qed
    moreover have "k_sem C (\<lambda>i. (fst (states' i), (?states i))) states'"
    proof (rule k_semI)
      fix i
      show "(fst ((\<lambda>i. (fst (states' i), (?states i))) i) = fst (states' i) \<and>
      single_sem C (snd ((\<lambda>i. (fst (states' i), (?states i))) i)) (snd (states' i)))"
        using asm4 by auto
    qed
    ultimately show "\<exists>states\<in>P. k_sem C states states'"
      by auto
  qed
qed


text \<open>Proposition 5\<close>

theorem encoding_RIL:
  fixes x :: "'lvar"
  assumes "\<And>l l' \<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P \<longleftrightarrow> (\<lambda>i. (l' i, \<sigma> i)) \<in> P"  (* P does not depend on logical variables *)
      and "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))" (* |lval| \<ge> |PStates^k| *)
      and "c \<noteq> x"
      and "injective from_nat"
      and "not_free_var_of (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set) x \<and> not_free_var_of P c"
      and "not_free_var_of Q x \<and> not_free_var_of Q c"
    shows "RIL P C Q \<longleftrightarrow> \<Turnstile> {pre_insec from_nat x c P} C {post_insec from_nat x c Q}" (is "?A \<longleftrightarrow> ?B")
proof (rule encode_insec)
  show "sat (strong_pre_insec from_nat x c (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set))"
  proof (rule can_be_sat)
    show "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))"
      by (simp add: assms(2))
    show "x \<noteq> c"
      using assms(3) by auto
  qed (auto simp add: assms)
qed (auto simp add: assms)


subsection \<open>Forward Underapproximation (FU)\<close>

text \<open>As employed by Outcome Logic~\cite{OutcomeLogic}\<close>

text \<open>Definition 12\<close>
definition FU where
  "FU P C Q \<longleftrightarrow> (\<forall>l. \<forall>\<sigma>. (l, \<sigma>) \<in> P \<longrightarrow> (\<exists>\<sigma>'. single_sem C \<sigma> \<sigma>' \<and> (l, \<sigma>') \<in> Q))"

lemma FUI:
  assumes "\<And>\<sigma> l. (l, \<sigma>) \<in> P \<Longrightarrow> (\<exists>\<sigma>'. single_sem C \<sigma> \<sigma>' \<and> (l, \<sigma>') \<in> Q)"
  shows "FU P C Q"
  by (simp add: assms FU_def)

definition encode_FU where
  "encode_FU P S \<longleftrightarrow> P \<inter> S \<noteq> {}"

text \<open>Proposition 6\<close>
theorem encoding_FU:
  "FU P C Q \<longleftrightarrow> \<Turnstile> {encode_FU P} C {encode_FU Q}" (is "?A \<longleftrightarrow> ?B")
proof
  show "?B \<Longrightarrow> ?A"
  proof -
    assume ?B
    show ?A
    proof (rule FUI)
      fix \<sigma> l
      assume asm: "(l, \<sigma>) \<in> P"
      then have "encode_FU P {(l, \<sigma>)}"
        by (simp add: encode_FU_def)
      then have "Q \<inter> sem C {(l, \<sigma>)} \<noteq> {}"
        using \<open>\<Turnstile> {encode_FU P} C {encode_FU Q}\<close> hyper_hoare_tripleE encode_FU_def by blast
      then obtain \<phi>' where "\<phi>' \<in> Q" "\<phi>' \<in> sem C {(l, \<sigma>)}"
        by blast
      then show "\<exists>\<sigma>'. single_sem C \<sigma> \<sigma>' \<and> (l, \<sigma>') \<in> Q"
        by (metis fst_conv in_sem prod.collapse singletonD snd_conv)
    qed
  qed
  assume ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume "encode_FU P S"
    then obtain l \<sigma> where "(l, \<sigma>) \<in> P \<inter> S"
      by (metis Expressivity.encode_FU_def ex_in_conv surj_pair)
    then obtain \<sigma>' where "single_sem C \<sigma> \<sigma>' \<and> (l, \<sigma>') \<in> Q"
      by (meson IntD1 \<open>FU P C Q\<close> FU_def)
    then show "encode_FU Q (sem C S)"
      using Expressivity.encode_FU_def \<open>(l, \<sigma>) \<in> P \<inter> S\<close> sem_def by fastforce
  qed
qed

definition hyperprop_FU where
  "hyperprop_FU P Q S \<longleftrightarrow> (\<forall>l \<sigma>. (l, \<sigma>) \<in> P \<longrightarrow> (\<exists>\<sigma>'. (l, \<sigma>') \<in> Q \<and> (\<sigma>, \<sigma>') \<in> S))"

lemma hyperprop_FUI:
  assumes "\<And>l \<sigma>. (l, \<sigma>) \<in> P \<Longrightarrow> (\<exists>\<sigma>'. (l, \<sigma>') \<in> Q \<and> (\<sigma>, \<sigma>') \<in> S)"
  shows "hyperprop_FU P Q S"
  by (simp add: hyperprop_FU_def assms)

lemma hyperprop_FUE:
  assumes "hyperprop_FU P Q S"
      and "(l, \<sigma>) \<in> P"
    shows "\<exists>\<sigma>'. (l, \<sigma>') \<in> Q \<and> (\<sigma>, \<sigma>') \<in> S"
  using hyperprop_FU_def assms(1) assms(2) by fastforce

theorem FU_expresses_hyperproperties:
  "hypersat C (hyperprop_FU P Q) \<longleftrightarrow> FU P C Q" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule FUI)
    fix \<sigma> l assume "(l, \<sigma>) \<in> P"
    then obtain \<sigma>' where asm0: "(l, \<sigma>') \<in> Q \<and> (\<sigma>, \<sigma>') \<in> set_of_traces C"
      by (meson \<open>hypersat C (hyperprop_FU P Q)\<close> hyperprop_FUE hypersat_def)
    then show "\<exists>\<sigma>'. (\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>') \<and> (l, \<sigma>') \<in> Q"
      using in_set_of_traces by blast
  qed
next
  assume ?B
  have "hyperprop_FU P Q (set_of_traces C)"
  proof (rule hyperprop_FUI)
    fix l \<sigma>
    assume asm0: "(l, \<sigma>) \<in> P"
    then show "\<exists>\<sigma>'. (l, \<sigma>') \<in> Q \<and> (\<sigma>, \<sigma>') \<in> set_of_traces C"
      by (metis (mono_tags, lifting) CollectI \<open>FU P C Q\<close> FU_def set_of_traces_def)
  qed
  then show ?A
    by (simp add: hypersat_def)
qed

theorem hyperliveness_hyperprop_FU:
  assumes "\<And>l. sat_for_l l P \<Longrightarrow> sat_for_l l Q"
  shows "hyperliveness (hyperprop_FU P Q)"
proof (rule hyperlivenessI)
  fix S show "\<exists>S'. S \<subseteq> S' \<and> hyperprop_FU P Q S'"
    by (meson UNIV_I hyperprop_FU_def assms sat_for_l_def subsetI)
qed


text \<open>No relationship between incorrectness and forward underapproximation\<close>

lemma incorrectness_does_not_imply_FU:
  assumes "injective from_nat"
  assumes "P = {(l, \<sigma>) |\<sigma> l. \<sigma> x = from_nat (0 :: nat) \<or> \<sigma> x = from_nat 1}"
      and "Q = {(l, \<sigma>) |\<sigma> l. \<sigma> x = from_nat 1}"
      and "C = Assume (\<lambda>\<sigma>. \<sigma> x = from_nat 1)"
  shows "IL P C Q"
    and "\<not> FU P C Q"
proof -
  have "Q \<subseteq> sem C P"
  proof (rule subsetPairI)
    fix l \<sigma> assume "(l, \<sigma>) \<in> Q"
    then have "\<sigma> x = from_nat 1"
      using assms(3) by blast
    then have "(l, \<sigma>) \<in> P"
      by (simp add: assms(2))
    then show "(l, \<sigma>) \<in> sem C P"
      by (simp add: \<open>\<sigma> x = from_nat 1\<close> assms(4) sem_assume)
  qed
  then show "IL P C Q"
    by (simp add: IL_def)
  show "\<not> FU P C Q"
  proof (rule ccontr)
    assume "\<not> \<not> FU P C Q"
    then have "FU P C Q"
      by blast
    obtain \<sigma> where "\<sigma> x = from_nat 0"
      by simp
    then obtain l where "(l, \<sigma>) \<in> P"
      using assms(2) by blast
    then obtain \<sigma>' where "single_sem C \<sigma> \<sigma>'" "(l, \<sigma>') \<in> Q"
      by (meson \<open>FU P C Q\<close> FU_def)
    then have "\<sigma>' x = from_nat 0"
      using \<open>\<sigma> x = from_nat 0\<close> assms(4) by blast
    then have "from_nat 0 = from_nat 1"
      using \<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close> assms(4) by force
    then show False
      using assms(1) injective_def[of from_nat] by auto
  qed
qed

lemma FU_does_not_imply_incorrectness:
  assumes "P = {(l, \<sigma>) |\<sigma> l. \<sigma> x = from_nat (0 :: nat) \<or> \<sigma> x = from_nat 1}"
      and "Q = {(l, \<sigma>) |\<sigma> l. \<sigma> x = from_nat 1}"
  assumes "injective from_nat"
  shows "\<not> IL Q Skip P"
    and "FU Q Skip P"
proof -
  show "FU Q Skip P"
  proof (rule FUI)
    fix \<sigma> l
    assume "(l, \<sigma>) \<in> Q"
    then show "\<exists>\<sigma>'. (\<langle>Skip, \<sigma>\<rangle> \<rightarrow> \<sigma>') \<and> (l, \<sigma>') \<in> P"
      using SemSkip assms(1) assms(2) by fastforce
  qed
  obtain \<sigma> where "\<sigma> x = from_nat 0"
    by simp
  then obtain l where "(l, \<sigma>) \<in> P"
    using assms(1) by blast
  moreover have "\<sigma> x \<noteq> from_nat 1"
    by (metis \<open>\<sigma> x = from_nat 0\<close> assms(3) injective_def one_neq_zero)
  then have "(l, \<sigma>) \<notin> Q"
    using assms(2) by blast
  ultimately show "\<not> IL Q Skip P"
    using IL_consequence by blast
qed


subsection \<open>Relational Forward Underapproximate logic\<close>

text \<open>Definition 13\<close>
definition RFU where
  "RFU P C Q \<longleftrightarrow> (\<forall>states \<in> P. \<exists>states' \<in> Q. k_sem C states states')"

lemma RFUI:
  assumes "\<And>states. states \<in> P \<Longrightarrow> (\<exists>states' \<in> Q. k_sem C states states')"
  shows "RFU P C Q"
  by (simp add: assms RFU_def)

lemma RFUE:
  assumes "RFU P C Q"
      and "states \<in> P"
    shows "\<exists>states' \<in> Q. k_sem C states states'"
  using assms(1) assms(2) RFU_def by blast

definition encode_RFU where
  "encode_RFU from_nat x P S \<longleftrightarrow> (\<exists>states \<in> P. (\<forall>i. states i \<in> S \<and> fst (states i) x = from_nat i))"

text \<open>Proposition 7\<close>
theorem encode_RFU:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "RFU P C Q \<longleftrightarrow> \<Turnstile> {encode_RFU from_nat x P} C {encode_RFU from_nat x Q}"
(is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume "encode_RFU from_nat x P S"
    then obtain states where asm0: "states \<in> P" "\<And>i. states i \<in> S \<and> fst (states i) x = from_nat i"
      by (meson encode_RFU_def)
    then obtain states' where "states' \<in> Q" "k_sem C states states'"
      using \<open>RFU P C Q\<close> RFUE by blast
    then have "\<And>i. states' i \<in> sem C S \<and> fst (states' i) x = from_nat i"
      by (metis (mono_tags, lifting) asm0(2) in_sem k_sem_def prod.collapse)
    then show "encode_RFU from_nat x Q (sem C S)"
      by (meson \<open>states' \<in> Q\<close> encode_RFU_def)
  qed
next
  assume ?B
  show ?A
  proof (rule RFUI)
    fix states assume asm0: "states \<in> P"
    let ?states = "\<lambda>i. ((fst (states i))(x := from_nat i), snd (states i))"

    have "?states \<in> P"
      using assms(1)
    proof (rule not_free_var_ofE)
      show "states \<in> P" using asm0 by simp
      fix i show "differ_only_by (fst (states i)) (fst ((fst (states i))(x := from_nat i), snd (states i))) x"
        using diff_by_comm diff_by_update by fastforce
    qed (auto)
    then have "encode_RFU from_nat x P (range ?states)"
      using encode_RFU_def by fastforce
    then have "encode_RFU from_nat x Q (sem C (range ?states))"
      using \<open>\<Turnstile> {encode_RFU from_nat x P} C {encode_RFU from_nat x Q}\<close> hyper_hoare_tripleE by blast
    then obtain states' where states'_def: "states' \<in> Q" "\<And>i. states' i \<in> sem C (range ?states) \<and> fst (states' i) x = from_nat i"
      by (meson encode_RFU_def)

    let ?states' = "\<lambda>i. ((fst (states' i))(x := fst (states i) x), snd (states' i))"

    have "?states' \<in> Q"
      using assms(2)
    proof (rule not_free_var_ofE)
      show "states' \<in> Q" using \<open>states' \<in> Q\<close> by simp
      fix i show "differ_only_by (fst (states' i)) (fst ((fst (states' i))(x := fst (states i) x), snd (states' i))) x"
        using diff_by_comm diff_by_update by fastforce
    qed (auto)
    moreover obtain to_pvar where to_pvar_def: "\<And>i. to_pvar (from_nat i) = i"
      using assms(3) injective_then_exists_inverse by blast
    then have inj: "\<And>i j. from_nat i = from_nat j \<Longrightarrow> i = j"
      by metis

    moreover have "k_sem C states ?states'"
    proof (rule k_semI)
      fix i 
      obtain \<sigma> where "(fst (states' i), \<sigma>) \<in> range (\<lambda>i. ((fst (states i))(x := from_nat i), snd (states i))) \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (states' i)"
        using states'_def(2) in_sem by blast
      moreover have "fst (states' i) x = from_nat i"
        by (simp add: states'_def)
      then have r: "((fst (states (inv ?states (fst (states' i), \<sigma>))))
      (x := from_nat (inv ?states (fst (states' i), \<sigma>))), snd (states (inv ?states (fst (states' i), \<sigma>))))
        = (fst (states' i), \<sigma>)"
        by (metis (mono_tags, lifting) calculation f_inv_into_f)
      then have "single_sem C (snd (states i)) (snd (states' i))"
        using \<open>fst (states' i) x = from_nat i\<close> calculation inj by fastforce
      moreover have "fst (?states i) = fst (states' i)"
        by (metis (mono_tags, lifting)r \<open>fst (states' i) x = from_nat i\<close> fst_conv fun_upd_same inj)
      ultimately show "fst (states i) = fst ((fst (states' i))(x := fst (states i) x), snd (states' i)) \<and>
         \<langle>C, snd (states i)\<rangle> \<rightarrow> snd ((fst (states' i))(x := fst (states i) x), snd (states' i))"
        by (metis (mono_tags, lifting) fst_conv fun_upd_triv fun_upd_upd snd_conv)
    qed
    ultimately show "\<exists>states'\<in>Q. k_sem C states states'" by blast
  qed
qed

definition RFU_hyperprop where
  "RFU_hyperprop P Q S \<longleftrightarrow> (\<forall>l states. (\<lambda>i. (l i, states i)) \<in> P
         \<longrightarrow> (\<exists>states'. (\<lambda>i. (l i, states' i)) \<in> Q \<and> (\<forall>i. (states i, states' i) \<in> S)))"

lemma RFU_hyperpropI:
  assumes "\<And>l states. (\<lambda>i. (l i, states i)) \<in> P \<Longrightarrow> (\<exists>states'. (\<lambda>i. (l i, states' i)) \<in> Q \<and> (\<forall>i. (states i, states' i) \<in> S))"
  shows "RFU_hyperprop P Q S"
  by (simp add: assms RFU_hyperprop_def)

lemma RFU_hyperpropE:
  assumes "RFU_hyperprop P Q S"
      and "(\<lambda>i. (l i, states i)) \<in> P"
    shows "\<exists>states'. (\<lambda>i. (l i, states' i)) \<in> Q \<and> (\<forall>i. (states i, states' i) \<in> S)"
  using assms(1) assms(2) RFU_hyperprop_def by blast

text \<open>Proposition 13\<close>
theorem RFU_captures_hyperproperties:
  "hypersat C (RFU_hyperprop P Q) \<longleftrightarrow> RFU P C Q" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule RFUI)
    fix states assume "states \<in> P"
    moreover have "(\<lambda>i. ((fst \<circ> states) i, (snd \<circ> states) i)) = states" by simp
    ultimately obtain states' where asm0: "(\<lambda>i. ((fst \<circ> states) i, states' i)) \<in> Q" "\<And>i. ((snd \<circ> states) i, states' i) \<in> set_of_traces C"
      using RFU_hyperpropE[of P Q "set_of_traces C" "fst \<circ> states" "snd \<circ> states"]
      using \<open>hypersat C (RFU_hyperprop P Q)\<close> hypersat_def by auto

    moreover have "k_sem C states (\<lambda>i. ((fst \<circ> states) i, states' i))"
    proof (rule k_semI)
      fix i 
      have "\<langle>C, snd (states i)\<rangle> \<rightarrow> states' i"
        using calculation(2) in_set_of_traces by fastforce
      then show "fst (states i) = fst ((fst \<circ> states) i, states' i) \<and> \<langle>C, snd (states i)\<rangle> \<rightarrow> snd ((fst \<circ> states) i, states' i)"
        by simp
    qed
    ultimately show "\<exists>states'\<in>Q. k_sem C states states'"
      by fast
  qed
next
  assume ?B
  have "RFU_hyperprop P Q (set_of_traces C)"
  proof (rule RFU_hyperpropI)
    fix l states
    assume "(\<lambda>i. (l i, states i)) \<in> P"
    then obtain states' where asm0: "states' \<in> Q" "k_sem C (\<lambda>i. (l i, states i)) states'"
      using \<open>RFU P C Q\<close> RFUE by blast
    then have "\<And>i. fst (states' i) = l i"
      by (simp add: k_sem_def)
    moreover have "(\<lambda>i. (l i, (snd \<circ> states') i)) = states'"
    proof (rule ext)
      fix i show "(l i, (snd \<circ> states') i) = states' i"
        by (metis calculation comp_apply surjective_pairing)
    qed
    moreover have "\<And>i. (states i, (snd \<circ> states') i) \<in> set_of_traces C"
    proof -
      fix i show "(states i, (snd \<circ> states') i) \<in> set_of_traces C"
        using asm0(2) comp_apply[of snd states'] in_set_of_traces k_sem_def[of C "\<lambda>i. (l i, states i)" states'] snd_conv
        by fastforce
    qed
    ultimately show "\<exists>states'. (\<lambda>i. (l i, states' i)) \<in> Q \<and> (\<forall>i. (states i, states' i) \<in> set_of_traces C)"
      using asm0(1) by force
  qed
  then show ?A
    by (simp add: hypersat_def)
qed

theorem hyperliveness_encode_RFU:
  assumes "\<And>l. k_sat_for_l l P \<Longrightarrow> k_sat_for_l l Q"
  shows "hyperliveness (RFU_hyperprop P Q)"
proof (rule hyperlivenessI)
  fix S 
  have "RFU_hyperprop P Q UNIV"
  proof (rule RFU_hyperpropI)
    fix l states assume asm0: "(\<lambda>i. (l i, states i)) \<in> P"
    then obtain states' where "(\<lambda>i. (l i, states' i)) \<in> Q"
      by (metis assms k_sat_for_l_def)
    then show "\<exists>states'. (\<lambda>i. (l i, states' i)) \<in> Q \<and> (\<forall>i. (states i, states' i) \<in> UNIV)"
      by blast
  qed
  then show "\<exists>S'. S \<subseteq> S' \<and> RFU_hyperprop P Q S'"
    by blast
qed


subsection \<open>Relational Universal Existential (RUE)~\cite{RHLE}\<close>

text \<open>Definition 14\<close>

definition RUE where
  "RUE P C Q \<longleftrightarrow> (\<forall>(\<sigma>1, \<sigma>2) \<in> P. \<forall>\<sigma>1'. k_sem C \<sigma>1 \<sigma>1' \<longrightarrow> (\<exists>\<sigma>2'. k_sem C \<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q))"

lemma RUE_I:
  assumes "\<And>\<sigma>1 \<sigma>2 \<sigma>1'. (\<sigma>1, \<sigma>2) \<in> P \<Longrightarrow> k_sem C \<sigma>1 \<sigma>1' \<Longrightarrow> (\<exists>\<sigma>2'. k_sem C \<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q)"
  shows "RUE P C Q"
  using assms RUE_def by fastforce

lemma RUE_E:
  assumes "RUE P C Q"
      and "(\<sigma>1, \<sigma>2) \<in> P"
      and "k_sem C \<sigma>1 \<sigma>1'"
    shows "\<exists>\<sigma>2'. k_sem C \<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q"
  using RUE_def assms(1) assms(2) assms(3) by blast

text \<open>Hyperproperty\<close>

definition hyperprop_RUE where
  "hyperprop_RUE P Q S \<longleftrightarrow> (\<forall>l1 l2 \<sigma>1 \<sigma>2 \<sigma>1'. (\<lambda>i. (l1 i, \<sigma>1 i), \<lambda>k. (l2 k, \<sigma>2 k)) \<in> P \<and>
  (\<forall>i. (\<sigma>1 i, \<sigma>1' i) \<in> S) \<longrightarrow> (\<exists>\<sigma>2'. (\<forall>k. (\<sigma>2 k, \<sigma>2' k) \<in> S) \<and> (\<lambda>i. (l1 i, \<sigma>1' i), \<lambda>k. (l2 k, \<sigma>2' k)) \<in> Q))"

lemma hyperprop_RUE_I:
  assumes "\<And>l1 l2 \<sigma>1 \<sigma>2 \<sigma>1'. (\<lambda>i. (l1 i, \<sigma>1 i), \<lambda>k. (l2 k, \<sigma>2 k)) \<in> P \<Longrightarrow>
  (\<forall>i. (\<sigma>1 i, \<sigma>1' i) \<in> S) \<Longrightarrow> (\<exists>\<sigma>2'. (\<forall>k. (\<sigma>2 k, \<sigma>2' k) \<in> S) \<and> (\<lambda>i. (l1 i, \<sigma>1' i), \<lambda>k. (l2 k, \<sigma>2' k)) \<in> Q)"
  shows "hyperprop_RUE P Q S"
  using assms hyperprop_RUE_def[of P Q S]
  by force

lemma hyperprop_RUE_E:
  assumes "hyperprop_RUE P Q S"
      and "(\<lambda>i. (l1 i, \<sigma>1 i), \<lambda>k. (l2 k, \<sigma>2 k)) \<in> P"
      and "\<And>i. (\<sigma>1 i, \<sigma>1' i) \<in> S"
    shows "\<exists>\<sigma>2'. (\<forall>k. (\<sigma>2 k, \<sigma>2' k) \<in> S) \<and> (\<lambda>i. (l1 i, \<sigma>1' i), \<lambda>k. (l2 k, \<sigma>2' k)) \<in> Q"
  using assms(1) assms(2) assms(3) hyperprop_RUE_def by blast


text \<open>Proposition 14\<close>
theorem RUE_express_hyperproperties:
  "RUE P C Q \<longleftrightarrow> hypersat C (hyperprop_RUE P Q)" (is "?A \<longleftrightarrow> ?B")
proof
  assume asm0: ?A
  have "hyperprop_RUE P Q (set_of_traces C)"
  proof (rule hyperprop_RUE_I)
    fix l1 l2 \<sigma>1 \<sigma>2 \<sigma>1'
    assume asm1: "(\<lambda>i. (l1 i, \<sigma>1 i), \<lambda>k. (l2 k, \<sigma>2 k)) \<in> P" "\<forall>i. (\<sigma>1 i, \<sigma>1' i) \<in> set_of_traces C"

    let ?x1 = "\<lambda>i. (l1 i, \<sigma>1 i)"
    let ?x2 = "\<lambda>k. (l2 k, \<sigma>2 k)"

    let ?x1' = "\<lambda>i. (l1 i, \<sigma>1' i)"

    have "\<exists>\<sigma>2'. k_sem C (\<lambda>k. (l2 k, \<sigma>2 k)) \<sigma>2' \<and> (?x1', \<sigma>2') \<in> Q"
      using asm0 asm1(1)
    proof (rule RUE_E)
      show "k_sem C (\<lambda>i. (l1 i, \<sigma>1 i)) (\<lambda>i. (l1 i, \<sigma>1' i))"
      proof (rule k_semI)
        fix i 
        have "single_sem C (\<sigma>1 i) (\<sigma>1' i)" using asm1(2)
          by (simp add: set_of_traces_def)
        then show "fst (l1 i, \<sigma>1 i) = fst (l1 i, \<sigma>1' i) \<and> \<langle>C, snd (l1 i, \<sigma>1 i)\<rangle> \<rightarrow> snd (l1 i, \<sigma>1' i)"
          by simp
      qed
    qed
    then obtain \<sigma>2' where asm2: "k_sem C (\<lambda>k. (l2 k, \<sigma>2 k)) \<sigma>2'" "(?x1', \<sigma>2') \<in> Q"
      by blast
    let ?\<sigma>2' = "\<lambda>k. snd (\<sigma>2' k)"

    have "\<And>k. (\<sigma>2 k, ?\<sigma>2' k) \<in> set_of_traces C"
      by (metis (mono_tags, lifting) asm2(1) in_set_of_traces k_sem_def snd_conv)
    moreover have "(\<lambda>k. (l2 k, ?\<sigma>2' k)) = \<sigma>2'"
    proof (rule ext)
      fix k show "(l2 k, snd (\<sigma>2' k)) = \<sigma>2' k"
        by (metis (mono_tags, lifting) asm2(1) fst_eqD k_sem_def surjective_pairing)
    qed
    ultimately show "\<exists>\<sigma>2'. (\<forall>k. (\<sigma>2 k, \<sigma>2' k) \<in> set_of_traces C) \<and> (\<lambda>i. (l1 i, \<sigma>1' i), \<lambda>k. (l2 k, \<sigma>2' k)) \<in> Q"
      using asm2(2) by fastforce
  qed
  then show ?B
    by (simp add: hypersat_def)
next
  assume ?B then have asm0: "hyperprop_RUE P Q (set_of_traces C)"
    by (simp add: hypersat_def)
  show ?A
  proof (rule RUE_I)
    fix \<sigma>1 \<sigma>2 \<sigma>1'
    assume asm1: "(\<sigma>1, \<sigma>2) \<in> P" "k_sem C \<sigma>1 \<sigma>1'"
    then have "\<And>i. fst (\<sigma>1 i) = fst (\<sigma>1' i)"
      by (simp add: k_sem_def)
    have "\<exists>\<sigma>2'. (\<forall>k. (snd (\<sigma>2 k), \<sigma>2' k) \<in> set_of_traces C) \<and> (\<lambda>i. (fst (\<sigma>1 i), snd (\<sigma>1' i)), \<lambda>k. (fst (\<sigma>2 k), \<sigma>2' k)) \<in> Q"
      using asm0
    proof (rule hyperprop_RUE_E[of P Q "set_of_traces C" "\<lambda>i. fst (\<sigma>1 i)" "\<lambda>i. snd (\<sigma>1 i)" "\<lambda>k. fst (\<sigma>2 k)" "\<lambda>k. snd (\<sigma>2 k)" "\<lambda>i. snd (\<sigma>1' i)"])
      show "(\<lambda>i. (fst (\<sigma>1 i), snd (\<sigma>1 i)), \<lambda>k. (fst (\<sigma>2 k), snd (\<sigma>2 k))) \<in> P"        
        by (simp add: asm1(1))
      fix i show "(snd (\<sigma>1 i), snd (\<sigma>1' i)) \<in> set_of_traces C"
        by (metis (mono_tags, lifting) CollectI asm1(2) k_sem_def set_of_traces_def)
    qed
    then obtain \<sigma>2' where asm2: "\<And>k. (snd (\<sigma>2 k), \<sigma>2' k) \<in> set_of_traces C" "(\<lambda>i. (fst (\<sigma>1 i), snd (\<sigma>1' i)), \<lambda>k. (fst (\<sigma>2 k), \<sigma>2' k)) \<in> Q"
      by blast
    moreover have "k_sem C \<sigma>2 (\<lambda>k. (fst (\<sigma>2 k), \<sigma>2' k))"
    proof (rule k_semI)
      fix i show "fst (\<sigma>2 i) = fst (fst (\<sigma>2 i), \<sigma>2' i) \<and> \<langle>C, snd (\<sigma>2 i)\<rangle> \<rightarrow> snd (fst (\<sigma>2 i), \<sigma>2' i)"
        using calculation(1) in_set_of_traces by auto
    qed
    ultimately show "\<exists>\<sigma>2'. k_sem C \<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q"
      using \<open>\<And>i. fst (\<sigma>1 i) = fst (\<sigma>1' i)\<close> by auto
  qed
qed

definition is_type where
  "is_type type fn x t S \<sigma> \<longleftrightarrow> (\<forall>i. \<sigma> i \<in> S \<and> fst (\<sigma> i) t = type \<and> fst (\<sigma> i) x = fn i)"

lemma is_typeI:
  assumes "\<And>i. \<sigma> i \<in> S"
      and "\<And>i. fst (\<sigma> i) t = type"
      and "\<And>i. fst (\<sigma> i) x = fn i"
    shows "is_type type fn x t S \<sigma>"
  by (simp add: assms(1) assms(2) assms(3) is_type_def)

lemma is_type_E:
  assumes "is_type type fn x t S \<sigma>"
  shows "\<sigma> i \<in> S \<and> fst (\<sigma> i) t = type \<and> fst (\<sigma> i) x = fn i"
  by (meson assms is_type_def)


definition encode_RUE_1 where
  "encode_RUE_1 fn fn1 fn2 x t P S \<longleftrightarrow> (\<forall>k. \<exists>\<sigma> \<in> S. fst \<sigma> x = fn2 k \<and> fst \<sigma> t = fn 2)
  \<and> (\<forall>\<sigma> \<sigma>'. is_type (fn 1) fn1 x t S \<sigma> \<and> is_type (fn 2) fn2 x t S \<sigma>'
  \<longrightarrow> (\<sigma>, \<sigma>') \<in> P)"

lemma encode_RUE_1_I:
  assumes "\<And>k. \<exists>\<sigma> \<in> S. fst \<sigma> x = fn2 k \<and> fst \<sigma> t = fn 2"
      and "\<And>\<sigma> \<sigma>'. is_type (fn 1) fn1 x t S \<sigma> \<and> is_type (fn 2) fn2 x t S \<sigma>'
  \<Longrightarrow> (\<sigma>, \<sigma>') \<in> P"
    shows "encode_RUE_1 fn fn1 fn2 x t P S"
  by (simp add: assms(1) assms(2) encode_RUE_1_def)

lemma encode_RUE_1_E1:
  assumes "encode_RUE_1 fn fn1 fn2 x t P S"
  shows "\<exists>\<sigma> \<in> S. fst \<sigma> x = fn2 k \<and> fst \<sigma> t = fn 2"
  by (meson assms encode_RUE_1_def)

lemma encode_RUE_1_E2:
  assumes "encode_RUE_1 fn fn1 fn2 x t P S"
      and "is_type (fn 1) fn1 x t S \<sigma>"
      and "is_type (fn 2) fn2 x t S \<sigma>'"
    shows "(\<sigma>, \<sigma>') \<in> P"
  by (meson assms encode_RUE_1_def)


definition encode_RUE_2 where
  "encode_RUE_2 fn fn1 fn2 x t Q S \<longleftrightarrow> (\<forall>\<sigma>. is_type (fn 1) fn1 x t S \<sigma> \<longrightarrow> (\<exists>\<sigma>'. is_type (fn 2) fn2 x t S \<sigma>' \<and> (\<sigma>, \<sigma>') \<in> Q))"

lemma encode_RUE_2I:
  assumes "\<And>\<sigma>. is_type (fn 1) fn1 x t S \<sigma> \<Longrightarrow> (\<exists>\<sigma>'. is_type (fn 2) fn2 x t S \<sigma>' \<and> (\<sigma>, \<sigma>') \<in> Q)"
  shows "encode_RUE_2 fn fn1 fn2 x t Q S"
  by (simp add: assms encode_RUE_2_def)

lemma encode_RUE_2_E:
  assumes "encode_RUE_2 fn fn1 fn2 x t Q S"
      and "is_type (fn 1) fn1 x t S \<sigma>"
    shows "\<exists>\<sigma>'. is_type (fn 2) fn2 x t S \<sigma>' \<and> (\<sigma>, \<sigma>') \<in> Q"
  by (meson assms(1) assms(2) encode_RUE_2_def)

definition differ_only_by_set where
  "differ_only_by_set vars a b \<longleftrightarrow> (\<forall>x. x \<notin> vars \<longrightarrow> a x = b x)"

definition differ_only_by_lset where
  "differ_only_by_lset vars a b \<longleftrightarrow> (\<forall>i. snd (a i) = snd (b i) \<and> differ_only_by_set vars (fst (a i)) (fst (b i)))"

lemma differ_only_by_lsetI:
  assumes "\<And>i. snd (a i) = snd (b i)"
      and "\<And>i. differ_only_by_set vars (fst (a i)) (fst (b i))"
    shows "differ_only_by_lset vars a b"
  using assms(1) assms(2) differ_only_by_lset_def by blast

definition not_in_free_vars_double where
  "not_in_free_vars_double vars P \<longleftrightarrow> (\<forall>\<sigma> \<sigma>'. differ_only_by_lset vars (fst \<sigma>) (fst \<sigma>') \<and>
  differ_only_by_lset vars (snd \<sigma>) (snd \<sigma>') \<longrightarrow> (\<sigma> \<in> P \<longleftrightarrow> \<sigma>' \<in> P))"

lemma not_in_free_vars_doubleE:
  assumes "not_in_free_vars_double vars P"
      and "differ_only_by_lset vars (fst \<sigma>) (fst \<sigma>')"
      and "differ_only_by_lset vars (snd \<sigma>) (snd \<sigma>')"
      and "\<sigma> \<in> P"
    shows "\<sigma>' \<in> P"
  by (meson assms not_in_free_vars_double_def)


text \<open>Proposition 8\<close>

theorem encoding_RUE:
  assumes "injective fn \<and> injective fn1 \<and> injective fn2"
      and "t \<noteq> x"

    and "injective (fn :: nat \<Rightarrow> 'a)"
    and "injective fn1"
    and "injective fn2"

    and "not_in_free_vars_double {x, t} P"
    and "not_in_free_vars_double {x, t} Q"

    shows "RUE P C Q \<longleftrightarrow> \<Turnstile> {encode_RUE_1 fn fn1 fn2 x t P} C {encode_RUE_2 fn fn1 fn2 x t Q}"
(is "?A \<longleftrightarrow> ?B")
proof
  assume asm0: ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume asm1: "encode_RUE_1 fn fn1 fn2 x t P S"

    show "encode_RUE_2 fn fn1 fn2 x t Q (sem C S)"
    proof (rule encode_RUE_2I)
      fix \<sigma>1' assume asm2: "is_type (fn 1) fn1 x t (sem C S) \<sigma>1'"

      let ?\<sigma>2 = "\<lambda>k. SOME \<sigma>'. \<sigma>'\<in>S \<and> fst \<sigma>' x = fn2 k \<and> fst \<sigma>' t = fn 2"
      have r2: "\<And>k. ?\<sigma>2 k \<in>S \<and> fst (?\<sigma>2 k) x = fn2 k \<and> fst (?\<sigma>2 k) t = fn 2"
      proof -
        fix k
        show "?\<sigma>2 k \<in>S \<and> fst (?\<sigma>2 k) x = fn2 k \<and> fst (?\<sigma>2 k) t = fn 2"
        proof (rule someI_ex)
          show "\<exists>xa. xa \<in> S \<and> fst xa x = fn2 k \<and> fst xa t = fn 2"
            by (meson asm1 encode_RUE_1_E1)
        qed
      qed
      let ?\<sigma>1 = "\<lambda>i. SOME \<sigma>. (fst (\<sigma>1' i), \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd (\<sigma>1' i))"
      have r1: "\<And>i. (fst (\<sigma>1' i), ?\<sigma>1 i) \<in> S \<and> single_sem C (?\<sigma>1 i) (snd (\<sigma>1' i))"
      proof -
        fix i
        show "(fst (\<sigma>1' i), ?\<sigma>1 i) \<in> S \<and> single_sem C (?\<sigma>1 i) (snd (\<sigma>1' i))"
        proof (rule someI_ex[of "\<lambda>\<sigma>. (fst (\<sigma>1' i), \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd (\<sigma>1' i))"])
          show "\<exists>\<sigma>. (fst (\<sigma>1' i), \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (\<sigma>1' i)"
            by (meson asm2 in_sem is_type_def)
        qed
      qed
      have "(\<lambda>i. (fst (\<sigma>1' i), ?\<sigma>1 i), ?\<sigma>2) \<in> P"
        using asm1
      proof (rule encode_RUE_1_E2)
        show "is_type (fn 1) fn1 x t S (\<lambda>i. (fst (\<sigma>1' i), ?\<sigma>1 i))"
          using asm2 fst_conv is_type_def[of "fn 1" fn1 x t S] is_type_def[of "fn 1" fn1 x t "sem C S"] r1
          by force
        show "is_type (fn 2) fn2 x t S ?\<sigma>2"
          by (simp add: is_type_def r2)
      qed
      moreover have "\<exists>\<sigma>2'. k_sem C ?\<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q"
        using asm0
      proof (rule RUE_E)
        show "(\<lambda>i. (fst (\<sigma>1' i), ?\<sigma>1 i), ?\<sigma>2) \<in> P"
          using calculation by auto
        show "k_sem C (\<lambda>i. (fst (\<sigma>1' i), SOME \<sigma>. (fst (\<sigma>1' i), \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> snd (\<sigma>1' i))) \<sigma>1'"
          by (simp add: k_sem_def r1)
      qed
      then obtain \<sigma>2' where \<sigma>2'_def: "k_sem C ?\<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q" by blast
      then have "is_type (fn 2) fn2 x t (sem C S) \<sigma>2'"
        using in_sem[of _ C S] k_semE[of C ?\<sigma>2 \<sigma>2']
          prod.collapse r2 is_type_def[of "fn 2" fn2 x t S] is_type_def[of "fn 2" fn2 x t "sem C S"]
        by (metis (no_types, lifting))
      then show "\<exists>\<sigma>2'. is_type (fn 2) fn2 x t (sem C S) \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q"
        using \<sigma>2'_def by blast
    qed
  qed
next
  assume asm0: "\<Turnstile> {encode_RUE_1 fn fn1 fn2 x t P} C {encode_RUE_2 fn fn1 fn2 x t Q}"
  show ?A
  proof (rule RUE_I)
    fix \<sigma>1 \<sigma>2 \<sigma>1'
    assume asm1: "(\<sigma>1, \<sigma>2) \<in> P" "k_sem C \<sigma>1 \<sigma>1'"

    let ?\<sigma>1 = "\<lambda>i. ((((fst (\<sigma>1 i))(t := fn 1))(x := fn1 i)), snd (\<sigma>1 i))"
    let ?\<sigma>2 = "\<lambda>k. ((((fst (\<sigma>2 k))(t := fn 2))(x := fn2 k)), snd (\<sigma>2 k))"

    let ?S1 = "{ ?\<sigma>1 i |i. True }"
    let ?S2 = "{ ?\<sigma>2 k |k. True }"
    let ?S = "?S1 \<union> ?S2"

    let ?\<sigma>1' = "\<lambda>i. ((((fst (\<sigma>1' i))(t := fn 1))(x := fn1 i)), snd (\<sigma>1' i))"

    have "encode_RUE_2 fn fn1 fn2 x t Q (sem C ?S)"
      using asm0       
    proof (rule hyper_hoare_tripleE)
      show "encode_RUE_1 fn fn1 fn2 x t P ?S"
      proof (rule encode_RUE_1_I)
        fix k
        let ?\<sigma> = "((((fst (\<sigma>2 k))(t := fn 2))(x := fn2 k)), snd (\<sigma>2 k))"
        have "?\<sigma> \<in> ?S2"
          by auto
        moreover have "fst ?\<sigma> x = fn2 k"
          by simp
        moreover have "fst ?\<sigma> t = fn 2"
          by (simp add: assms(2))
        ultimately show "\<exists>\<sigma>\<in>?S1 \<union> ?S2. fst \<sigma> x = fn2 k \<and> fst \<sigma> t = fn 2"
          by blast
      next
        fix \<sigma> \<sigma>'
        assume asm2: "is_type (fn (1 :: nat)) fn1 x t (?S1 \<union> ?S2) \<sigma> \<and> is_type (fn 2) fn2 x t (?S1 \<union> ?S2) \<sigma>'"
        moreover have r1: "\<And>i. \<sigma> i = ((fst (\<sigma>1 i))(t := fn 1, x := fn1 i), snd (\<sigma>1 i))"
        proof -
          fix i
          have "fst (\<sigma> i) t = fn 1"
            by (meson calculation is_type_def)
          moreover have "\<sigma> i \<in> ?S1"
          proof (rule ccontr)
            assume "\<not> \<sigma> i \<in> ?S1"
            moreover have "\<sigma> i \<in> ?S1 \<union> ?S2"
              using asm2 is_type_def[of "fn 1" fn1 x t]
              by (metis (no_types, lifting))
            ultimately have "\<sigma> i \<in> ?S2" by simp
            then have "fst (\<sigma> i) t = fn 2"
              using assms(2) by auto
            then show False
              by (metis Suc_1 Suc_eq_numeral \<open>fst (\<sigma> i) t = fn 1\<close> assms(3) injective_def numeral_One one_neq_zero pred_numeral_simps(1))
          qed
          then obtain j where "\<sigma> i = ((fst (\<sigma>1 j))(t := fn 1, x := fn1 j), snd (\<sigma>1 j))"
            by blast
          moreover have "i = j"
            by (metis (mono_tags, lifting) asm2 assms(4) calculation(2) fst_conv fun_upd_same injective_def is_type_def)
          ultimately show "\<sigma> i = ((fst (\<sigma>1 i))(t := fn 1, x := fn1 i), snd (\<sigma>1 i))"
            by blast
        qed
        moreover have "\<And>i. \<sigma>' i = ((fst (\<sigma>2 i))(t := fn 2, x := fn2 i), snd (\<sigma>2 i))"
        proof -
          fix i
          have "fst (\<sigma>' i) t = fn 2"
            by (meson calculation is_type_def)
          moreover have "\<sigma>' i \<in> ?S2"
          proof (rule ccontr)
            assume "\<not> \<sigma>' i \<in> ?S2"
            moreover have "\<sigma>' i \<in> ?S1 \<union> ?S2"
              using asm2 is_type_def[of "fn 2" fn2 x t]
              by (metis (no_types, lifting))
            ultimately have "\<sigma>' i \<in> ?S1" by simp
            then have "fst (\<sigma>' i) t = fn 1"
              using assms(2) by auto
            then show False
              by (metis Suc_1 Suc_eq_numeral \<open>fst (\<sigma>' i) t = fn 2\<close> assms(3) injective_def numeral_One one_neq_zero pred_numeral_simps(1))
          qed
          then obtain j where "\<sigma>' i = ((fst (\<sigma>2 j))(t := fn 2, x := fn2 j), snd (\<sigma>2 j))"
            by blast
          moreover have "i = j"
            by (metis (mono_tags, lifting) asm2 assms(5) calculation(2) fst_conv fun_upd_same injective_def is_type_def)
          ultimately show "\<sigma>' i = ((fst (\<sigma>2 i))(t := fn 2, x := fn2 i), snd (\<sigma>2 i))"
            by blast
        qed
        moreover have "(?\<sigma>1, ?\<sigma>2) \<in> P"
          using assms(6)
        proof (rule not_in_free_vars_doubleE)
          show "(\<sigma>1, \<sigma>2) \<in> P"
            by (simp add: asm1(1))
          show "differ_only_by_lset {x, t} (fst (\<sigma>1, \<sigma>2)) (fst (?\<sigma>1, ?\<sigma>2))"
            by (rule differ_only_by_lsetI) (simp_all add: differ_only_by_set_def)
          show "differ_only_by_lset {x, t} (snd (\<sigma>1, \<sigma>2)) (snd (?\<sigma>1, ?\<sigma>2))"
            by (rule differ_only_by_lsetI) (simp_all add: differ_only_by_set_def)
        qed
        ultimately show "(\<sigma>, \<sigma>') \<in> P"
          by presburger
      qed
    qed
    then have "\<exists>\<sigma>'. is_type (fn 2) fn2 x t (sem C ?S) \<sigma>' \<and> (?\<sigma>1', \<sigma>') \<in> Q"
    proof (rule encode_RUE_2_E)
      show "is_type (fn 1) fn1 x t (sem C ?S) ?\<sigma>1'"
      proof (rule is_typeI)
        fix i show "fst ((fst (\<sigma>1' i))(t := fn 1, x := fn1 i), snd (\<sigma>1' i)) t = fn 1"
          by (simp add: assms(2))
        show " ((fst (\<sigma>1' i))(t := fn 1, x := fn1 i), snd (\<sigma>1' i)) \<in> sem C ?S"
          using UnI1[of _ ?S1 ?S2]
            asm1(2) k_semE[of C \<sigma>1 \<sigma>1' i]
            single_step_then_in_sem[of C "snd (\<sigma>1 i)" "snd (\<sigma>1' i)" _ ?S]
          by force
      qed (auto)
    qed
    then obtain \<sigma>2' where r: "is_type (fn 2) fn2 x t (sem C ?S) \<sigma>2' \<and> (?\<sigma>1', \<sigma>2') \<in> Q"
      by blast
    let ?\<sigma>2' = "\<lambda>k. ((fst (\<sigma>2' k))(x := fst (\<sigma>2 k) x, t := fst (\<sigma>2 k) t), snd (\<sigma>2' k))"
    have "(\<sigma>1', ?\<sigma>2') \<in> Q"
      using assms(7)
    proof (rule not_in_free_vars_doubleE)
      show "(?\<sigma>1', \<sigma>2') \<in> Q"
        using r by blast
      show "differ_only_by_lset {x, t} (fst (?\<sigma>1', \<sigma>2')) (fst (\<sigma>1', ?\<sigma>2'))"
        by (rule differ_only_by_lsetI) (simp_all add: differ_only_by_set_def)
      show "differ_only_by_lset {x, t} (snd (?\<sigma>1', \<sigma>2')) (snd (\<sigma>1', ?\<sigma>2'))"
        by (rule differ_only_by_lsetI) (simp_all add: differ_only_by_set_def)
    qed
    moreover have "k_sem C \<sigma>2 ?\<sigma>2'"
    proof (rule k_semI)
      fix i
      obtain y where y_def: "y \<in> ?S" "fst y = fst (\<sigma>2' i)" "single_sem C (snd y) (snd (\<sigma>2' i))"
        using r in_sem[of "\<sigma>2' i" C ?S]
          is_type_E[of "fn 2" fn2 x t "sem C ?S" \<sigma>2' i]
        by (metis (no_types, lifting) fst_conv snd_conv)
      then have "fst y t = fn 2"
        by (metis (no_types, lifting) is_type_def r)
      moreover have "fn 1 \<noteq> fn 2"
        by (metis Suc_1 assms(3) injective_def n_not_Suc_n)
      then have "y \<notin> ?S1"
        using assms(2) calculation by fastforce
      then have "y \<in> ?S2"
        using y_def(1) by blast
      show "fst (\<sigma>2 i) = fst ((fst (\<sigma>2' i))(x := fst (\<sigma>2 i) x, t := fst (\<sigma>2 i) t), snd (\<sigma>2' i)) \<and>
         \<langle>C, snd (\<sigma>2 i)\<rangle> \<rightarrow> snd ((fst (\<sigma>2' i))(x := fst (\<sigma>2 i) x, t := fst (\<sigma>2 i) t), snd (\<sigma>2' i))"
      proof
        have r1: "\<sigma>2' i \<in> sem C ?S \<and> fst (\<sigma>2' i) t = fn 2 \<and> fst (\<sigma>2' i) x = fn2 i"
        proof (rule is_type_E[of "fn 2" fn2 x t "sem C ?S" \<sigma>2' i])
          show "is_type (fn 2) fn2 x t (sem C ?S) \<sigma>2'"
            using r by blast
        qed
        then obtain \<sigma> where "(fst (\<sigma>2' i), \<sigma>) \<in> ?S" "single_sem C \<sigma> (snd (\<sigma>2' i))"
          by (meson in_sem)
        then have "(fst (\<sigma>2' i), \<sigma>) \<in> ?S2"
          using r1 \<open>fn 1 \<noteq> fn 2\<close> assms(2) by fastforce
        then obtain k where "fst (\<sigma>2' i) = (fst (\<sigma>2 k))(t := fn 2, x := fn2 k)" and "\<sigma> = snd (\<sigma>2 k)"
          by blast
        then have "k = i"
          by (metis r1 assms(5) fun_upd_same injective_def)
        then show "\<langle>C, snd (\<sigma>2 i)\<rangle> \<rightarrow> snd ((fst (\<sigma>2' i))(x := fst (\<sigma>2 i) x, t := fst (\<sigma>2 i) t), snd (\<sigma>2' i))"
          using \<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> snd (\<sigma>2' i)\<close> \<open>\<sigma> = snd (\<sigma>2 k)\<close> by auto
        show "fst (\<sigma>2 i) = fst ((fst (\<sigma>2' i))(x := fst (\<sigma>2 i) x, t := fst (\<sigma>2 i) t), snd (\<sigma>2' i))"
          by (simp add: \<open>fst (\<sigma>2' i) = (fst (\<sigma>2 k))(t := fn 2, x := fn2 k)\<close> \<open>k = i\<close>)
      qed
    qed
    ultimately show "\<exists>\<sigma>2'. k_sem C \<sigma>2 \<sigma>2' \<and> (\<sigma>1', \<sigma>2') \<in> Q"
      by blast
  qed
qed

subsection \<open>Program Refinement\<close>

lemma sem_assign_single:
  "sem (Assign x e) {(l, \<sigma>)} = {(l, \<sigma>(x := e \<sigma>))}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix la \<sigma>'
    assume "(la, \<sigma>') \<in> sem (Assign x e) {(l, \<sigma>)}"
    then show "(la, \<sigma>') \<in> {(l, \<sigma>(x := e \<sigma>))}"
      by (metis (mono_tags, lifting) in_sem prod.sel(1) prod.sel(2) single_sem_Assign_elim singleton_iff)
  qed
  show "?B \<subseteq> ?A"
    by (simp add: SemAssign in_sem)
qed

definition refinement where
  "refinement C1 C2 \<longleftrightarrow> (set_of_traces C1 \<subseteq> set_of_traces C2)"

definition not_free_var_stmt where
  "not_free_var_stmt x C \<longleftrightarrow> (\<forall>\<sigma> \<sigma>' v. (\<sigma>, \<sigma>') \<in> set_of_traces C \<longrightarrow> (\<sigma>(x := v), \<sigma>'(x := v)) \<in> set_of_traces C)
\<and> (\<forall>\<sigma> \<sigma>'. single_sem C \<sigma> \<sigma>' \<longrightarrow> \<sigma> x = \<sigma>' x)"

lemma not_free_var_stmtE_1:
  assumes "not_free_var_stmt x C"
      and "(\<sigma>, \<sigma>') \<in> set_of_traces C"
    shows "(\<sigma>(x := v), \<sigma>'(x := v)) \<in> set_of_traces C"
  using assms(1) assms(2) not_free_var_stmt_def by force

lemma not_free_in_sem_same_val:
  assumes "not_free_var_stmt x C"
      and "single_sem C \<sigma> \<sigma>'"
    shows "\<sigma> x = \<sigma>' x"
  using assms(1) assms(2) not_free_var_stmt_def by fastforce

lemma not_free_in_sem_equiv:
  assumes "not_free_var_stmt x C"
      and "single_sem C \<sigma> \<sigma>'"
    shows "single_sem C (\<sigma>(x := v)) (\<sigma>'(x := v))"
  by (meson assms(1) assms(2) in_set_of_traces not_free_var_stmtE_1)
      

text \<open>Example 4\<close>
theorem encoding_refinement:
  fixes P :: "(('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set \<Rightarrow> bool"
  assumes "(a :: 'pval) \<noteq> b"
    (* and x free var *)
      and "P = (\<lambda>S. card S = 1)"
      and "Q = (\<lambda>S.
  \<forall>\<phi>\<in>S. snd \<phi> x = a \<longrightarrow> (fst \<phi>, (snd \<phi>)(x := b)) \<in> S)"
      and "not_free_var_stmt x C1"
      and "not_free_var_stmt x C2"
  shows "refinement C1 C2 \<longleftrightarrow>
  \<Turnstile> { P } If (Seq (Assign (x :: 'pvar) (\<lambda>_. a)) C1) (Seq (Assign x (\<lambda>_. b)) C2) { Q }"
(is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  show ?B
  proof (rule hyper_hoare_tripleI)
    fix S assume "P (S :: (('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set)"

    then obtain \<sigma> l where asm0: "S = {(l, \<sigma>)}"
      by (metis assms(2) card_1_singletonE surj_pair)

    let ?C = "If (Seq (Assign x (\<lambda>_. a)) C1) (Seq (Assign x (\<lambda>_. b)) C2)"
    let ?a = "(l, \<sigma>(x := a))"
    let ?b = "(l, \<sigma>(x := b))"

    have if_sem: "sem ?C S = sem C1 {?a} \<union> sem C2 {?b}"
      by (simp add: asm0 sem_assign_single sem_if sem_seq)
    then have "\<And>\<phi>. \<phi> \<in> sem ?C S \<Longrightarrow> snd \<phi> x = a \<Longrightarrow> (fst \<phi>, (snd \<phi>)(x := b)) \<in> sem ?C S"
    proof -
      fix \<phi> assume asm1: "\<phi> \<in> sem ?C S" "snd \<phi> x = a"
      have "\<phi> \<in> sem C1 {?a}"
      proof (rule ccontr)
        assume "\<phi> \<notin> sem C1 {(l, \<sigma>(x := a))}"
        then have "\<phi> \<in> sem C2 {(l, \<sigma>(x := b))}"
          using if_sem asm1(1) by force
        then have "snd \<phi> x = b"
          using assms(5) fun_upd_same in_sem not_free_in_sem_same_val[of x C2 "\<sigma>(x := b)" "snd \<phi>"] singletonD snd_conv
          by metis
        then show False
          using asm1(2) assms(1) by blast
      qed
      then have "(\<sigma>(x := a), snd \<phi>) \<in> set_of_traces C1"
        by (simp add: in_sem set_of_traces_def)
      then have "(\<sigma>(x := a), snd \<phi>) \<in> set_of_traces C2"
        using \<open>refinement C1 C2\<close> refinement_def by fastforce
      then have "((\<sigma>(x := a))(x := b), (snd \<phi>)(x := b)) \<in> set_of_traces C2"
        by (meson assms(5) not_free_var_stmtE_1)
      then have "single_sem C2 (\<sigma>(x := b)) ((snd \<phi>)(x := b))"
        by (simp add: set_of_traces_def)
      then have "(fst \<phi>, (snd \<phi>)(x := b)) \<in> sem C2 {?b}"
        by (metis \<open>\<phi> \<in> sem C1 {(l, \<sigma>(x := a))}\<close> fst_eqD in_sem singleton_iff snd_eqD)
      then show "(fst \<phi>, (snd \<phi>)(x := b)) \<in> sem ?C S"
        by (simp add: if_sem)
    qed
    then show "Q (sem ?C S)"
      using assms(3) by blast
  qed
next
  assume asm0: ?B

  have "set_of_traces C1 \<subseteq> set_of_traces C2"
  proof (rule subsetPairI)
    fix \<sigma> \<sigma>' assume asm1: "(\<sigma>, \<sigma>') \<in> set_of_traces C1"
    obtain l S where "(S :: (('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set) = { (l, \<sigma>) }"      
      by simp

    let ?a = "(l, \<sigma>(x := a))"
    let ?b = "(l, \<sigma>(x := b))"

    let ?C = "If (Seq (Assign (x :: 'pvar) (\<lambda>_. a)) C1) (Seq (Assign x (\<lambda>_. b)) C2)"
    have "Q (sem ?C S)"
    proof (rule hyper_hoare_tripleE)
      show "P S"
        by (simp add: \<open>S = {(l, \<sigma>)}\<close> assms(2))
      show ?B using asm0 by simp
    qed
    moreover have "(l, \<sigma>'(x := a)) \<in> sem ?C S"
    proof -
      have "single_sem (Seq (Assign x (\<lambda>_. a)) C1) \<sigma> (\<sigma>'(x := a))"
        by (meson SemAssign SemSeq asm1 assms(4) in_set_of_traces not_free_in_sem_equiv)
      then show ?thesis
        by (simp add: SemIf1 \<open>S = {(l, \<sigma>)}\<close> in_sem)
    qed
    then have "(l, \<sigma>'(x := b)) \<in> sem ?C S"
      using assms(3) calculation by fastforce
    moreover have "(l, \<sigma>'(x := b)) \<in> sem (Seq (Assign x (\<lambda>_. b)) C2) S"
    proof (rule ccontr)
      assume "\<not> (l, \<sigma>'(x := b)) \<in> sem (Seq (Assign x (\<lambda>_. b)) C2) S"
      then have "(l, \<sigma>'(x := b)) \<in> sem (Seq (Assign x (\<lambda>_. a)) C1) S"
        using calculation(2) sem_if by auto
      then have "(l, \<sigma>'(x := b)) \<in> sem C1 {?a}"
        by (simp add: \<open>S = {(l, \<sigma>)}\<close> sem_assign_single sem_seq)
      then show False
        using assms(1) assms(4) fun_upd_same in_sem not_free_in_sem_same_val[of x C1  "\<sigma>(x := a)" "\<sigma>'(x := b)"] singletonD snd_conv
        by metis
    qed
    then have "single_sem (Seq (Assign x (\<lambda>_. b)) C2) \<sigma> (\<sigma>'(x := b))"
      by (simp add: \<open>S = {(l, \<sigma>)}\<close> in_sem)
    then have "single_sem C2 (\<sigma>(x := b)) (\<sigma>'(x := b))"
      by blast
    then have "(\<sigma>(x := b), \<sigma>'(x := b)) \<in> set_of_traces C2"
      by (simp add: set_of_traces_def)
    then have "((\<sigma>(x := b))(x := \<sigma> x), (\<sigma>'(x := b))(x := \<sigma> x)) \<in> set_of_traces C2"
      by (meson assms(5) not_free_var_stmtE_1)
    then show "(\<sigma>, \<sigma>') \<in> set_of_traces C2"
      by (metis asm1 assms(4) fun_upd_triv fun_upd_upd in_set_of_traces not_free_in_sem_same_val)
  qed
  then show ?A
    by (simp add: refinement_def)
qed

end