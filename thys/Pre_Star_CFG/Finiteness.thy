(* Authors: Tassilo Lemke; Tobias Nipkow *)

section\<open>Finiteness of Context-Free Languages\<close>

theory Finiteness
  imports Applications
begin

(* TODO mv *)

lemma derive_Nts_iff: "P \<turnstile> \<alpha> \<Rightarrow> \<beta> \<Longrightarrow> Nts_syms \<beta> \<subseteq> Nts P \<longleftrightarrow> Nts_syms \<alpha> \<subseteq> Nts P"
  apply(frule derive_Nts_syms_subset) 
  by (auto simp: derive.simps Nts_Lhss_Rhs_Nts intro: in_LhssI)

lemma derives_Nts_iff: "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> Nts_syms \<alpha> \<subseteq> Nts P \<longleftrightarrow> Nts_syms \<beta> \<subseteq> Nts P"
apply(induction rule: derives_induct)
 apply simp
by (meson derive.intros derive_Nts_iff)


text \<open>An alternative way of expressing that all Nts are useful:\<close>

definition useful_all :: "('n,'y)Prods \<Rightarrow> 'n \<Rightarrow> bool" where
"useful_all P S = (\<forall>X \<in> Nts P. reachable P S X \<and> productive P X)"

lemma useful_all_iff:
  "S \<in> Nts P \<Longrightarrow> useful_all P S = (\<forall>X \<in> Nts P. useful P S X)"
unfolding useful_all_def by (metis productive_if_useful useful_reachable)

text \<open>NB: \<open>is_useful_all\<close> is more efficient than \<^prop>\<open>\<forall>X \<in> Nts P. useful P S X\<close>
because the former needs to check only once for each symbol if it is productive.\<close>

(* This theory could be generalized from CNF to arbitrary grammars (with some work) *)
(* The dependence on theory Applications could be minimized in the process
   (only a few defs are needed, eg \<open>is_useful\<close>) *)

text\<open>
  Another interesting application, particularly for context-free grammars in
  chomsky normal-form (CNF), is the detection of ``cyclic'' non-terminals.
\<close>

text\<open>
  Particularly, if all non-terminals are reachable (can be reached from the starting symbol)
  and productive (i.e., a terminal word can be derived from each symbol), the following holds:
\<close>

text\<open>\<open>L(C) = \<infinity> \<longleftrightarrow> \<exists>X \<alpha> \<beta>. X \<Rightarrow>\<^sup>* \<alpha>X\<beta> \<and> a\<beta> \<noteq> \<epsilon>\<close>\<close>

text\<open>
  Since we have a decision-procedure for derivability, we can work towards also automating this process.
  However, to keep proofs simple, this theory only focuses on grammars in CNF, meaning a conversion
  is required a priori.
\<close>

subsection\<open>Preliminaries and Assumptions\<close>

locale CFG =
  fixes P :: "('n, 't) Prods" and S :: 'n
  assumes cnf: "\<And>p. p \<in> P \<Longrightarrow> (\<exists>A a. p = (A, [Tm a]) \<or> (\<exists>A B C. p = (A, [Nt B, Nt C])))"
  and S_in_P: "S \<in> Nts P"
begin \<comment>\<open>begin-context CFG\<close>

definition is_non_nullable_all :: "bool" where
  "is_non_nullable_all \<equiv> (\<forall>X \<in> Nts P. \<not> is_nullable P X)"

lemma derives_concat:
  assumes "P \<turnstile> X\<^sub>1 \<Rightarrow>* w\<^sub>1" and "P \<turnstile> X\<^sub>2 \<Rightarrow>* w\<^sub>2"
  shows "P \<turnstile> (X\<^sub>1@X\<^sub>2) \<Rightarrow>* (w\<^sub>1@w\<^sub>2)"
  using assms derives_appendD by blast

lemma derives_split:
  assumes "P \<turnstile> X \<Rightarrow>* w"
  shows "\<exists>X\<^sub>1 X\<^sub>2 w\<^sub>1 w\<^sub>2. X = X\<^sub>1@X\<^sub>2 \<and> w = w\<^sub>1@w\<^sub>2 \<and> P \<turnstile> X\<^sub>1 \<Rightarrow>* w\<^sub>1 \<and> P \<turnstile> X\<^sub>2 \<Rightarrow>* w\<^sub>2"
  using assms by blast

lemma derives_step:
  assumes "P \<turnstile> X \<Rightarrow>* (\<alpha>@w\<^sub>1@\<beta>)" and "P \<turnstile> w\<^sub>1 \<Rightarrow>* w\<^sub>2"
  shows "P \<turnstile> X \<Rightarrow>* (\<alpha>@w\<^sub>2@\<beta>)"
proof -
  have "P \<turnstile> w\<^sub>1@\<beta> \<Rightarrow>* w\<^sub>2@\<beta>"
    using assms(2) by (simp add: derives_concat)
  then have "P \<turnstile> \<alpha>@w\<^sub>1@\<beta> \<Rightarrow>* \<alpha>@w\<^sub>2@\<beta>"
    by (simp add: derives_concat)
  then show ?thesis
    using assms(1) by simp
qed

lemma is_useful_all_derive:
  "\<lbrakk> useful_all P S; Nts_syms xs \<subseteq> Nts P \<rbrakk> \<Longrightarrow> productives P xs"
  unfolding useful_all_def
  by (meson productives_if_Productive subset_eq)

lemma is_non_nullable_all_derive:
  assumes "is_non_nullable_all" "Nts_syms xs \<subseteq> Nts P" and "P \<turnstile> xs \<Rightarrow>* w"
  shows "xs = [] \<longleftrightarrow> w = []"
proof -
  have "\<And>X. X \<in> Nts P \<Longrightarrow> \<not> P \<turnstile> [Nt X] \<Rightarrow>* []"
    using assms(1) by (simp add: is_non_nullable_all_def is_nullable_def)
  moreover have "\<And>c. \<not> P \<turnstile> [Tm c] \<Rightarrow>* []"
    by simp
  ultimately have nonNullAll: "\<And>x. \<not> P \<turnstile> [x] \<Rightarrow>* []"
    by (metis Nts_Lhss_Rhs_Nts Un_iff derives_Cons_Nil in_LhssI)

  have 1: "xs = [] \<Longrightarrow> w = []"
    using assms(3) by auto

  have 2: "xs \<noteq> [] \<Longrightarrow> w \<noteq> []"
  proof
    assume "xs \<noteq> []"
    then obtain x xs' where "xs = x#xs'"
      using list.exhaust by blast
    moreover have "P \<turnstile> ([x]@xs') \<Rightarrow>* [] \<Longrightarrow> (P \<turnstile> [x] \<Rightarrow>* [] \<and> P \<turnstile> xs' \<Rightarrow>* [])"
      using derives_split by (metis Nil_is_append_conv derives_appendD)
    moreover have "\<not> P \<turnstile> [x] \<Rightarrow>* []"
      by (simp add: nonNullAll)
    ultimately show "w = [] \<Longrightarrow> False"
      using assms(3) by simp
  qed

  show ?thesis
    using 1 2 by blast
qed

subsection\<open>Criterion of Finiteness\<close>

text\<open>
  Finally, we introduce the definition @{term is_infinite}, which instead of making use
  of the language set, uses the criterion introduced above.
\<close>

definition is_reachable_step :: "'n \<Rightarrow> 'n \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>?" 80) where
  "(X \<rightarrow>\<^sup>? Y) \<equiv> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt X] \<Rightarrow>* (\<alpha>@[Nt Y]@\<beta>) \<and> \<alpha>@\<beta> \<noteq> [])"

lemma in_Nts_if_is_reachable_step1: "X \<rightarrow>\<^sup>? Y \<Longrightarrow> X \<in> Nts P"
by(auto simp add: is_reachable_step_def Nts_Lhss_Rhs_Nts neq_Nil_conv derives_Cons_iff in_LhssI)

lemma in_Nts_if_is_reachable_step2: "X \<rightarrow>\<^sup>? Y \<Longrightarrow> Y \<in> Nts P"
by (metis append_Cons in_Nts_if_is_reachable_step1 in_Nts_iff_if_derives in_set_conv_decomp
      is_reachable_step_def reachable_def)

definition is_infinite :: "bool" where
  "is_infinite \<equiv> (\<exists>X \<in> Nts P. X \<rightarrow>\<^sup>? X)"

fun is_infinite_derives :: "'n \<Rightarrow> ('n, 't) sym list \<Rightarrow> ('n, 't) sym list \<Rightarrow> nat \<Rightarrow> ('n, 't) sym list" where
  "is_infinite_derives X \<alpha> \<beta> (Suc n) = \<alpha>@(is_infinite_derives X \<alpha> \<beta> n)@\<beta>" |
  "is_infinite_derives X \<alpha> \<beta> 0 = [Nt X]"

fun is_infinite_words :: "'t list \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> 't list" where
  "is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta> (Suc n) = w\<^sub>\<alpha>@(is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta> n)@w\<^sub>\<beta>" |
  "is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta> 0 = w\<^sub>X"

definition reachable_rel :: "('n \<times> 'n) set" where
  "reachable_rel \<equiv> {(X\<^sub>2, X\<^sub>1). \<exists>\<alpha> \<beta>. (X\<^sub>1, \<alpha>@[Nt X\<^sub>2]@\<beta>) \<in> P}"

lemma cnf_implies_pumping:
  assumes "(Y, \<alpha>@[Nt X]@\<beta>) \<in> P"
  shows "Y \<rightarrow>\<^sup>? X"
proof -
  consider "\<exists>a. (\<alpha>@[Nt X]@\<beta>) = [Tm a]" | "\<exists>B C. (\<alpha>@[Nt X]@\<beta>) = [Nt B, Nt C]"
    using assms cnf by blast
  then show ?thesis
  proof (cases)
    case 1
    then have "False"
      by (simp add: append_eq_Cons_conv)
    then show ?thesis
      by simp
  next
    case 2
    then obtain B C where BC_def: "(\<alpha>@[Nt X]@\<beta>) = [Nt B, Nt C]"
      by blast
    then have "X = B \<or> X = C"
      by (metis Nil_is_append_conv append_Cons in_set_conv_decomp in_set_conv_decomp_first set_ConsD sym.inject(1))
    then have "P \<turnstile> [Nt Y] \<Rightarrow> []@[Nt X]@[Nt C] | P \<turnstile> [Nt Y] \<Rightarrow> [Nt B]@[Nt X]@[]"
      using BC_def assms(1) derive_singleton by force
    then show ?thesis
      unfolding is_reachable_step_def by (rule disjE) blast+
  qed
qed

lemma reachable_rel_tran: "(X, Y) \<in> reachable_rel\<^sup>+ \<Longrightarrow> Y \<rightarrow>\<^sup>? X"
proof (induction rule: trancl.induct)
  case (r_into_trancl X Y)
  then show "Y \<rightarrow>\<^sup>? X"
    using cnf cnf_implies_pumping by (auto simp: reachable_rel_def)
next
  case (trancl_into_trancl X Y Z)
  then have "Z \<rightarrow>\<^sup>? Y"
    using cnf cnf_implies_pumping by (auto simp: reachable_rel_def)
  with trancl_into_trancl(3) have "Z \<rightarrow>\<^sup>? X"
  proof -
    assume "Z \<rightarrow>\<^sup>? Y" and "Y \<rightarrow>\<^sup>? X"

    obtain \<alpha>\<^sub>Z \<beta>\<^sub>Z where z_der: "P \<turnstile> [Nt Z] \<Rightarrow>* (\<alpha>\<^sub>Z@[Nt Y]@\<beta>\<^sub>Z)" and "\<alpha>\<^sub>Z@\<beta>\<^sub>Z \<noteq> []"
      using \<open>Z \<rightarrow>\<^sup>? Y\<close>[unfolded is_reachable_step_def] by blast
    obtain \<alpha>\<^sub>Y \<beta>\<^sub>Y where y_der: "P \<turnstile> [Nt Y] \<Rightarrow>* (\<alpha>\<^sub>Y@[Nt X]@\<beta>\<^sub>Y)" and "\<alpha>\<^sub>Y@\<beta>\<^sub>Y \<noteq> []"
      using \<open>Y \<rightarrow>\<^sup>? X\<close>[unfolded is_reachable_step_def] by blast

    have "P \<turnstile> [Nt Z] \<Rightarrow>* (\<alpha>\<^sub>Z@\<alpha>\<^sub>Y@[Nt X]@\<beta>\<^sub>Y@\<beta>\<^sub>Z)"
      using z_der y_der by (metis append.assoc derives_step)
    moreover have "\<alpha>\<^sub>Z@\<alpha>\<^sub>Y@\<beta>\<^sub>Y@\<beta>\<^sub>Z \<noteq> []"
      using \<open>\<alpha>\<^sub>Z@\<beta>\<^sub>Z \<noteq> []\<close> \<open>\<alpha>\<^sub>Y@\<beta>\<^sub>Y \<noteq> []\<close> by simp
    ultimately show "Z \<rightarrow>\<^sup>? X"
      unfolding is_reachable_step_def by (metis append.assoc)
  qed
  then show ?case
    by simp
qed

lemma reachable_rel_wf:
  assumes "finite P"
    and cnf: "\<And>p. p \<in> P \<Longrightarrow> (\<exists>A a. p = (A, [Tm a]) \<or> (\<exists>A B C. p = (A, [Nt B, Nt C])))"
    and loopfree: "\<And>X. X \<in> Nts P \<Longrightarrow> \<not> X \<rightarrow>\<^sup>? X"
  shows "wf reachable_rel"
proof -
  define Nt2 :: "'n \<times> 'n \<Rightarrow> ('n, 't) sym \<times> ('n, 't) sym"
    where "Nt2 \<equiv> (\<lambda>(a,b). (Nt a, Nt b))"
  define S :: "(('n, 't) sym \<times> ('n, 't) sym) set"
    where "S \<equiv> \<Union>(set ` snd ` P) \<times> (Nt ` fst ` P)"

  have "finite (\<Union>(set ` snd ` P))"
    by (rule finite_Union; use assms(1) in blast)
  moreover have "finite (fst ` P)"
    using assms(1) by simp
  ultimately have "finite S"
    unfolding S_def by blast
  moreover have "(Nt2 ` reachable_rel) \<subseteq> S"
    unfolding reachable_rel_def Nt2_def S_def by (auto split: prod.splits sym.splits, force)
  ultimately have "finite (Nt2 ` reachable_rel)"
    using finite_subset by blast
  moreover have "inj_on Nt2 reachable_rel"
    unfolding inj_on_def Nt2_def by fast
  ultimately have finite: "finite reachable_rel"
    using finite_image_iff by blast

  have "acyclic reachable_rel"
  unfolding acyclic_def using loopfree reachable_rel_tran in_Nts_if_is_reachable_step1 by blast

  from finite_acyclic_wf[OF finite this] show "wf reachable_rel" .
qed

lemma is_infinite_implies_finite:
  assumes "finite P" "X \<in> Nts P"
    and loopfree: "\<And>X. X \<in> Nts P \<Longrightarrow> \<not> X \<rightarrow>\<^sup>? X"
  shows "finite {w. P \<turnstile> [Nt X] \<Rightarrow>* w}"
proof -
  have "wf reachable_rel"
    using assms cnf by (simp add: reachable_rel_wf)
  then show ?thesis
  proof (induction)
    case (less X)

    have "{w. \<exists>a. (X, [Tm a]) \<in> P \<and> P \<turnstile> [Tm a] \<Rightarrow>* w} = snd ` {(Y, \<beta>) \<in> P. X = Y \<and> (\<exists>a. \<beta> = [Tm a])}"
      by force
    then have finA: "finite {w. \<exists>a. (X, [Tm a]) \<in> P \<and> P \<turnstile> [Tm a] \<Rightarrow>* w}"
      using assms(1) by (metis (no_types, lifting) case_prod_conv finite_imageI mem_Collect_eq old.prod.exhaust rev_finite_subset subsetI)

    have "\<And>B C. (X, [Nt B, Nt C]) \<in> P \<Longrightarrow> finite {w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}"
    proof -
      fix B and C
      assume "(X, [Nt B, Nt C]) \<in> P"
      then have "(X, []@[Nt B]@[Nt C]) \<in> P" and "(X, [Nt B]@[Nt C]@[]) \<in> P"
        by simp+
      then have "(B, X) \<in> reachable_rel" and "(C, X) \<in> reachable_rel"
        unfolding reachable_rel_def by blast+
      then have "finite {w. P \<turnstile> [Nt B] \<Rightarrow>* w}" and "finite {w. P \<turnstile> [Nt C] \<Rightarrow>* w}"
        using less by simp+
      moreover have "{w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w} = (\<lambda>(b,c). b@c) ` ({w. P \<turnstile> [Nt B] \<Rightarrow>* w} \<times> {w. P \<turnstile> [Nt C] \<Rightarrow>* w})"
      proof (standard; standard)
        fix w
        assume "w \<in> {w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}"
        then have "P \<turnstile> [Nt B]@[Nt C] \<Rightarrow>* w"
          by simp
        then obtain b c where "P \<turnstile> [Nt B] \<Rightarrow>* b" and "P \<turnstile> [Nt C] \<Rightarrow>* c" and "w = b@c"
          using derives_appendD by blast
        then show "w \<in> (\<lambda>(b,c). b@c) ` ({w. P \<turnstile> [Nt B] \<Rightarrow>* w} \<times> {w. P \<turnstile> [Nt C] \<Rightarrow>* w})"
          by blast
      next
        fix w
        assume "w \<in> (\<lambda>(b,c). b@c) ` ({w. P \<turnstile> [Nt B] \<Rightarrow>* w} \<times> {w. P \<turnstile> [Nt C] \<Rightarrow>* w})"
        then obtain b c where "P \<turnstile> [Nt B] \<Rightarrow>* b" and "P \<turnstile> [Nt C] \<Rightarrow>* c" and "w = b@c"
          by fast
        then have "P \<turnstile> [Nt B]@[Nt C] \<Rightarrow>* w"
          using derives_concat by blast
        then show "w \<in> {w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}"
          by simp
      qed
      ultimately show "finite {w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}"
        by simp
    qed
    moreover have "finite {(B, C). (X, [Nt B, Nt C]) \<in> P}"
    proof -
      define S :: "('n \<times> ('n, 't) sym list) set" where
          "S \<equiv> ((\<lambda>(B,C). (X, [Nt B, Nt C])) ` {(B, C). (X, [Nt B, Nt C]) \<in> P})"
      have subP: "S \<subseteq> P"
        unfolding S_def by fast
      with assms(1) have "finite S"
        by (elim finite_subset)
      then show ?thesis
        unfolding S_def by (rule finite_imageD, simp add: inj_on_def)
    qed
    ultimately have "finite (\<Union>((\<lambda>(B,C). {w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}) ` {(B,C). (X, [Nt B, Nt C]) \<in> P}))"
      by (intro finite_Union; fast)
    moreover have "{w. \<exists>B C. (X, [Nt B, Nt C]) \<in> P \<and> P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}
        = (\<Union>((\<lambda>(B,C). {w. P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}) ` {(B,C). (X, [Nt B, Nt C]) \<in> P}))"
      by blast
    ultimately have finB: "finite {w. \<exists>B C. (X, [Nt B, Nt C]) \<in> P \<and> P \<turnstile> [Nt B, Nt C] \<Rightarrow>* w}"
      by simp

    let ?P = "\<lambda>w \<beta>. (X, \<beta>) \<in> P \<and> P \<turnstile> \<beta> \<Rightarrow>* w"
    have un: "{w. \<exists>\<beta>. ?P w \<beta>} = {w. \<exists>a. ?P w [Tm a]} \<union> {w. \<exists>B C. ?P w [Nt B, Nt C]}"
      using cnf by blast
    have "finite {w. \<exists>\<beta>. (X, \<beta>) \<in> P \<and> P \<turnstile> \<beta> \<Rightarrow>* w}"
      unfolding un by (intro finite_UnI; use finA finB in simp)
    moreover have "\<And>X. {w. P \<turnstile> [Nt X] \<Rightarrow>* w} = {[Nt X]} \<union> {w. \<exists>\<beta>. (X, \<beta>) \<in> P \<and> P \<turnstile> \<beta> \<Rightarrow>* w}"
      by (auto split: prod.splits simp: derives_Cons_iff)
    ultimately show ?case
      by simp
  qed
qed

theorem is_infinite_correct:
  assumes "useful_all P S" and "is_non_nullable_all" and "finite P"
  shows "\<not> finite (Lang P S) \<longleftrightarrow> is_infinite"
proof (standard, erule contrapos_pp)
  assume "\<not> is_infinite"
  then have finA: "finite {w. P \<turnstile> [Nt S] \<Rightarrow>* w}"
    using is_infinite_implies_finite assms(3) S_in_P by (simp add: is_infinite_def)
  have "finite (map Tm ` {w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w}::('n, 't) sym list set)"
    by (rule finite_subset[where B="{w. P \<turnstile> [Nt S] \<Rightarrow>* w}"]; use finA in blast)
  moreover have "inj_on (map Tm) {w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w}"
    by (simp add: inj_on_def)
  ultimately have "finite {w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w}"
    using finite_image_iff[where f="map Tm"] by blast
  then show "\<not> infinite (Lang P S)"
    by (simp add: Lang_def)
next
  assume "is_infinite"
  then obtain X where "X \<in> Nts P" "X \<rightarrow>\<^sup>? X"
    unfolding is_infinite_def by blast
  then obtain \<alpha> \<beta> where deriveX: "P \<turnstile> [Nt X] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>)" and "\<alpha>@\<beta> \<noteq> []"
    and Nts\<alpha>\<beta>: "Nts_syms \<alpha> \<subseteq> Nts P \<and> Nts_syms \<beta> \<subseteq> Nts P"
    unfolding is_reachable_step_def Nts_syms_def
    using in_Nts_iff_if_derives reachable_def by fastforce

  obtain w\<^sub>X where w\<^sub>X_def: "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w\<^sub>X"
    using assms(1) is_useful_all_derive \<open>X \<in> Nts P\<close> by fastforce

  obtain w\<^sub>\<alpha> w\<^sub>\<beta> where w\<^sub>\<alpha>_def: "P \<turnstile> \<alpha> \<Rightarrow>* map Tm w\<^sub>\<alpha>" and w\<^sub>\<beta>_def: "P \<turnstile> \<beta> \<Rightarrow>* map Tm w\<^sub>\<beta>"
    using assms(1) is_useful_all_derive \<open>X \<in> Nts P\<close> Nts\<alpha>\<beta> by blast
  then have "w\<^sub>\<alpha>@w\<^sub>\<beta> \<noteq> []"
    using \<open>\<alpha>@\<beta> \<noteq> []\<close> by (simp add: Nts\<alpha>\<beta> assms(2) is_non_nullable_all_derive)

  define f\<^sub>d where "f\<^sub>d \<equiv> is_infinite_derives X \<alpha> \<beta>"
  define f\<^sub>w where "f\<^sub>w \<equiv> is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta>"

  have "reachable P S X"
    using assms(1) \<open>X \<in> Nts P\<close> by (simp add: useful_all_def)
  then obtain p s where "P \<turnstile> [Nt S] \<Rightarrow>* (p@[Nt X]@s)"
    and Ntsps: "Nts_syms p \<subseteq> Nts P \<and> Nts_syms s \<subseteq> Nts P"
    unfolding reachable_def using split_list[of "Nt X"] S_in_P derives_Nts_iff[of P "[Nt S]"]
    by force
  moreover obtain w\<^sub>p where w\<^sub>p_def: "P \<turnstile> p \<Rightarrow>* map Tm w\<^sub>p"
    using assms(1) \<open>X \<in> Nts P\<close> is_useful_all_derive Ntsps by blast
  moreover obtain w\<^sub>s where w\<^sub>s_def: "P \<turnstile> s \<Rightarrow>* map Tm w\<^sub>s"
    using assms(1) is_useful_all_derive Ntsps by blast
  ultimately have fromS: "P \<turnstile> [Nt S] \<Rightarrow>* (map Tm w\<^sub>p@[Nt X]@map Tm w\<^sub>s)"
    by (meson local.derives_concat rtranclp.rtrancl_refl rtranclp_trans)

  have "\<And>i. P \<turnstile> [Nt X] \<Rightarrow>* f\<^sub>d i"
    subgoal for i
      apply (induction i; simp_all add: f\<^sub>d_def)
      apply (meson deriveX local.derives_concat rtranclp.rtrancl_refl rtranclp_trans)
      done
    done
  moreover have "\<And>i. P \<turnstile> f\<^sub>d i \<Rightarrow>* map Tm (f\<^sub>w i)"
    subgoal for i
      by (induction i; simp add: f\<^sub>d_def f\<^sub>w_def w\<^sub>X_def w\<^sub>\<alpha>_def w\<^sub>\<beta>_def derives_concat)
    done
  ultimately have "\<And>i. P \<turnstile> [Nt X] \<Rightarrow>* map Tm (f\<^sub>w i)"
    using rtranclp_trans by fast
  then have "\<And>i. P \<turnstile> [Nt S] \<Rightarrow>* (map Tm w\<^sub>p@map Tm (f\<^sub>w i)@map Tm w\<^sub>s)"
    using fromS derives_step by presburger
  then have "\<And>i. P \<turnstile> [Nt S] \<Rightarrow>* (map Tm (w\<^sub>p@(f\<^sub>w i)@w\<^sub>s))"
    by simp
  moreover define f\<^sub>w' where f\<^sub>w'_def: "f\<^sub>w' = (\<lambda>i. w\<^sub>p @ (f\<^sub>w i) @ w\<^sub>s)"
  ultimately have "\<And>i. P \<turnstile> [Nt S] \<Rightarrow>* map Tm (f\<^sub>w' i)"
    by simp
  then have "\<And>i. f\<^sub>w' i \<in> Lang P S"
    by (simp add: Lang_def)
  then have "range f\<^sub>w' \<subseteq> Lang P S"
    by blast

  have "\<And>i. length (f\<^sub>w i) < length (f\<^sub>w (i+1))"
    subgoal for i
      by (induction i; use f\<^sub>w_def \<open>w\<^sub>\<alpha>@w\<^sub>\<beta> \<noteq> []\<close> in simp)
    done
  then have x: "\<And>i. length (f\<^sub>w' i) < length (f\<^sub>w' (i+1))"
    by (simp add: f\<^sub>w'_def)
  then have "\<And>i n. 0 < n \<Longrightarrow> length (f\<^sub>w' i) < length (f\<^sub>w' (i+n))"
    subgoal for i n
      apply (induction n, auto)
      apply (metis Suc_lessD add_cancel_left_right gr_zeroI less_trans_Suc)
      done
    done
  then have f\<^sub>w'_order: "\<And>i\<^sub>1 i\<^sub>2. i\<^sub>1 < i\<^sub>2 \<Longrightarrow> length (f\<^sub>w' i\<^sub>1) < length (f\<^sub>w' i\<^sub>2)"
    using less_imp_add_positive by blast

  then have "inj f\<^sub>w'"
    unfolding inj_def by (metis nat_neq_iff)

  have "infinite (Lang P S)"
    using \<open>range f\<^sub>w' \<subseteq> Lang P S\<close> \<open>inj f\<^sub>w'\<close> infinite_iff_countable_subset by blast
  then show "\<not> finite (Lang P S)"
    by simp
qed

\<comment>\<open>Notation only used in this theory.\<close>
no_notation is_reachable_step (infix "\<rightarrow>\<^sup>?" 80)

subsection\<open>Finiteness Problem\<close>

lemma is_infinite_check:
  "is_infinite \<longleftrightarrow> (\<exists>X \<in> Nts P. [Nt X] \<in> pre_star P { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. \<alpha>@\<beta> \<noteq> [] })"
  unfolding is_infinite_def is_reachable_step_def by (auto simp: pre_star_term)

theorem is_infinite_by_prestar:
  assumes "useful_all P S" and "is_non_nullable_all" and "finite P"
  shows "finite (Lang P S) \<longleftrightarrow> (\<forall>X \<in> Nts P. [Nt X] \<notin> pre_star P { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. \<alpha>@\<beta> \<noteq> [] })"
  using assms is_infinite_correct is_infinite_check by blast

end \<comment>\<open>end-context CFG\<close>

end
 