section\<open>The Delta System Lemma, Relativized\label{sec:dsl-rel}\<close>

theory Delta_System_Relative
  imports
    Cardinal_Library_Relative
begin

(* FIXME: The following code (definition and 3 lemmas) is extracted
   from Delta_System where it is unnecesarily under the context of AC *)
definition
  delta_system :: "i \<Rightarrow> o" where
  "delta_system(D) \<equiv> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"

lemma delta_systemI[intro]:
  assumes "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  shows "delta_system(D)"
  using assms unfolding delta_system_def by simp

lemma delta_systemD[dest]:
  "delta_system(D) \<Longrightarrow> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  unfolding delta_system_def by simp

lemma delta_system_root_eq_Inter:
  assumes "delta_system(D)"
  shows "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = \<Inter>D"
proof (clarify, intro equalityI, auto)
  fix A' B' x C
  assume hyp:"A'\<in>D" "B'\<in> D" "A'\<noteq>B'" "x\<in>A'" "x\<in>B'" "C\<in>D"
  with assms
  obtain r where delta:"\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
    by auto
  show "x \<in> C"
  proof (cases "C=A'")
    case True
    with hyp and assms
    show ?thesis by simp
  next
    case False
    moreover
    note hyp
    moreover from calculation and delta
    have "r = C \<inter> A'" "A' \<inter> B' = r" "x\<in>r" by auto
    ultimately
    show ?thesis by simp
  qed
qed

relativize functional "delta_system" "delta_system_rel" external

locale M_delta = M_cardinal_library +
  assumes
    countable_lepoll_assms:
    "M(G) \<Longrightarrow> M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow> separation(M, \<lambda>y. \<exists>x\<in>A.
                          y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. {xa \<in> G . x \<in> xa}, b, f, i)\<rangle>)"
begin

lemmas cardinal_replacement = lam_replacement_cardinal_rel[unfolded lam_replacement_def]

lemma disjoint_separation: "M(c) \<Longrightarrow> separation(M, \<lambda> x. \<exists>a. \<exists>b. x=\<langle>a,b\<rangle> \<and> a \<inter> b = c)"
  using separation_pair separation_eq lam_replacement_constant lam_replacement_Int
  by simp

lemma insnd_ball: "M(G) \<Longrightarrow> separation(M, \<lambda>p. \<forall>x\<in>G. x \<in> snd(p) \<longleftrightarrow> fst(p) \<in> x)"
  using separation_ball separation_iff' lam_replacement_fst lam_replacement_snd
    separation_in lam_replacement_hcomp
  by simp

lemma (in M_trans) mem_F_bound6:
  fixes F G
  defines "F \<equiv> \<lambda>_ x. Collect(G, (\<in>)(x))"
  shows "x\<in>F(G,c) \<Longrightarrow> c \<in> (range(f) \<union> \<Union>G)"
  using apply_0 unfolding F_def
  by (cases "M(c)", auto simp:F_def)

lemma delta_system_Aleph_rel1:
  assumes "\<forall>A\<in>F. Finite(A)" "F \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(F)"
  shows "\<exists>D[M]. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  have "M(G) \<Longrightarrow> M(p) \<Longrightarrow> M({A\<in>G . p \<in> A})" for G p
  proof -
    assume "M(G)" "M(p)"
    have "{A\<in>G . p \<in> A} = G \<inter> (Memrel({p} \<union> G) `` {p})"
      unfolding Memrel_def by auto
    with \<open>M(G)\<close> \<open>M(p)\<close>
    show ?thesis by simp
  qed
  from \<open>M(F)\<close>
  have "M(\<lambda>A\<in>F. |A|\<^bsup>M\<^esup>)"
    using cardinal_replacement
    by (rule_tac lam_closed) (auto dest:transM)
  text\<open>Since all members are finite,\<close>
  with \<open>\<forall>A\<in>F. Finite(A)\<close> \<open>M(F)\<close>
  have "(\<lambda>A\<in>F. |A|\<^bsup>M\<^esup>) : F \<rightarrow>\<^bsup>M\<^esup> \<omega>" (is "?cards : _")
    by (simp add:mem_function_space_rel_abs, rule_tac lam_type)
      (force dest:transM)
  moreover from this
  have a:"?cards -`` {n} = { A\<in>F . |A|\<^bsup>M\<^esup> = n }" for n
    using vimage_lam by auto
  moreover
  note \<open>F \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(F)\<close>
  moreover from calculation
  text\<open>there are uncountably many have the same cardinal:\<close>
  obtain n where "n\<in>\<omega>" "|?cards -`` {n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using eqpoll_rel_Aleph_rel1_cardinal_rel_vimage[of F ?cards] by auto
  moreover
  define G where "G \<equiv> ?cards -`` {n}"
  moreover from calculation and \<open>M(?cards)\<close>
  have "M(G)" by blast
  moreover from calculation
  have "G \<subseteq> F" by auto
  ultimately
  text\<open>Therefore, without loss of generality, we can assume that all
  elements of the family have cardinality \<^term>\<open>n\<in>\<omega>\<close>.\<close>
  have "A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = n" and "G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" and "M(G)" for A
    using cardinal_rel_Card_rel_eqpoll_rel_iff by auto
  with \<open>n\<in>\<omega>\<close>
  text\<open>So we prove the result by induction on this \<^term>\<open>n\<close> and
  generalizing \<^term>\<open>G\<close>, since the argument requires changing the
  family in order to apply the inductive hypothesis.\<close>
  have "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  proof (induct arbitrary:G)
    case 0 \<comment> \<open>This case is impossible\<close>
    then
    have "G \<subseteq> {0}"
      using cardinal_rel_0_iff_0 by (blast dest:transM)
    with \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(G)\<close>
    show ?case
      using nat_lt_Aleph_rel1 subset_imp_le_cardinal_rel[of G "{0}"]
        lt_trans2 cardinal_rel_Card_rel_eqpoll_rel_iff by auto
  next
    case (succ n)
    have "\<forall>a\<in>G. Finite(a)"
    proof
      fix a
      assume "a \<in> G"
      moreover
      note \<open>M(G)\<close> \<open>n\<in>\<omega>\<close>
      moreover from calculation
      have "M(a)" by (auto dest: transM)
      moreover from succ and \<open>a\<in>G\<close>
      have "|a|\<^bsup>M\<^esup> = succ(n)" by simp
      ultimately
      show "Finite(a)"
        using Finite_cardinal_rel_iff' nat_into_Finite[of "succ(n)"]
        by fastforce
    qed
    show "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    proof (cases "\<exists>p[M]. {A\<in>G . p \<in> A} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>")
      case True \<comment> \<open>the positive case, uncountably many sets with a
                    common element\<close>
      then
      obtain p where "{A\<in>G . p \<in> A} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(p)" by blast
      moreover
      note 1=\<open>M(G)\<close> \<open>M(G) \<Longrightarrow> M(p) \<Longrightarrow> M({A\<in>G . p \<in> A})\<close> singleton_closed[OF \<open>M(p)\<close>]
      moreover from this
      have "M({x - {p} . x \<in> {x \<in> G . p \<in> x}})"
        using RepFun_closed[OF lam_replacement_Diff'[THEN
              lam_replacement_imp_strong_replacement]]
          Diff_closed[OF transM[OF _ 1(2)]] by auto
      moreover from 1
      have "M(converse(\<lambda>x\<in>{x \<in> G . p \<in> x}. x - {p}))" (is "M(converse(?h))")
        using converse_closed[of ?h] lam_closed[OF diff_Pair_replacement]
          Diff_closed[OF transM[OF _ 1(2)]]
        by auto
      moreover from calculation
      have "{A-{p} . A\<in>{X\<in>G. p\<in>X}} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" (is "?F \<approx>\<^bsup>M\<^esup> _")
        using Diff_bij_rel[of "{A\<in>G . p \<in> A}" "{p}", THEN
            comp_bij_rel[OF bij_rel_converse_bij_rel, where C="\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>",
              THEN bij_rel_imp_eqpoll_rel, of _ _ ?F]]
        unfolding eqpoll_rel_def
        by (auto simp del:mem_bij_abs)
      text\<open>Now using the hypothesis of the successor case,\<close>
      moreover from \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup>=succ(n)\<close> \<open>\<forall>a\<in>G. Finite(a)\<close>
        and this \<open>M(G)\<close>
      have "p\<in>A \<Longrightarrow> A\<in>G \<Longrightarrow> |A - {p}|\<^bsup>M\<^esup> = n" for A
        using Finite_imp_succ_cardinal_rel_Diff[of _ p] by (force dest: transM)
      moreover
      have "\<forall>a\<in>?F. Finite(a)"
      proof (clarsimp)
        fix A
        assume "p\<in>A" "A\<in>G"
        with \<open>\<And>A. p \<in> A \<Longrightarrow> A \<in> G \<Longrightarrow> |A - {p}|\<^bsup>M\<^esup> = n\<close> and \<open>n\<in>\<omega>\<close> \<open>M(G)\<close>
        have "Finite(|A - {p}|\<^bsup>M\<^esup>)"
          using nat_into_Finite by simp
        moreover from \<open>p\<in>A\<close> \<open>A\<in>G\<close> \<open>M(G)\<close>
        have "M(A - {p})" by (auto dest: transM)
        ultimately
        show "Finite(A - {p})"
          using Finite_cardinal_rel_iff' by simp
      qed
      moreover
      text\<open>we may apply the inductive hypothesis to the new family \<^term>\<open>?F\<close>:\<close>
      note \<open>(\<And>A. A \<in> ?F \<Longrightarrow> |A|\<^bsup>M\<^esup> = n) \<Longrightarrow> ?F \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> M(?F) \<Longrightarrow>
             \<exists>D[M]. D \<subseteq> ?F \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
      moreover
      note 1=\<open>M(G)\<close> \<open>M(G) \<Longrightarrow> M(p) \<Longrightarrow> M({A\<in>G . p \<in> A})\<close> singleton_closed[OF \<open>M(p)\<close>]
      moreover from this
      have "M({x - {p} . x \<in> {x \<in> G . p \<in> x}})"
        using RepFun_closed[OF lam_replacement_Diff'[THEN
              lam_replacement_imp_strong_replacement]]
          Diff_closed[OF transM[OF _ 1(2)]] by auto
      ultimately
      obtain D where "D\<subseteq>{A-{p} . A\<in>{X\<in>G. p\<in>X}}" "delta_system(D)" "D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(D)"
        by auto
      moreover from this
      obtain r where "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
        by fastforce
      then
      have "\<forall>A\<in>D.\<forall>B\<in>D. A\<union>{p} \<noteq> B\<union>{p}\<longrightarrow>(A \<union> {p}) \<inter> (B \<union> {p}) = r\<union>{p}"
        by blast
      ultimately
      have "delta_system({B \<union> {p} . B\<in>D})" (is "delta_system(?D)")
        by fastforce
      moreover from \<open>M(D)\<close> \<open>M(p)\<close>
      have "M(?D)"
        using RepFun_closed un_Pair_replacement transM[of _ D] by auto
      moreover from \<open>D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(D)\<close>
      have "Infinite(D)" "|D|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1[THEN iffD2,
            THEN uncountable_rel_imp_Infinite, of D]
          cardinal_rel_eqpoll_rel_iff[of D "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"] \<open>M(D)\<close> \<open>D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
        by auto
      moreover from this \<open>M(?D)\<close> \<open>M(D)\<close> \<open>M(p)\<close>
      have "?D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using cardinal_rel_map_Un[of D "{p}"] naturals_lt_nat
          cardinal_rel_eqpoll_rel_iff[THEN iffD1] by simp
      moreover
      note \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
      have "?D \<subseteq> G"
      proof -
        {
          fix A
          assume "A\<in>G" "p\<in>A"
          moreover from this
          have "A = A - {p} \<union> {p}"
            by blast
          ultimately
          have "A -{p} \<union> {p} \<in> G"
            by auto
        }
        with \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
        show ?thesis
          by blast
      qed
      moreover
      note \<open>M(?D)\<close>
      ultimately
      show "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" by auto
    next
      case False
      note \<open>\<not> (\<exists>p[M]. {A \<in> G . p \<in> A} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close> \<comment> \<open>the other case\<close>
        \<open>M(G)\<close> \<open>\<And>p. M(G) \<Longrightarrow> M(p) \<Longrightarrow> M({A\<in>G . p \<in> A})\<close>
      moreover from \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> and this
      have "M(p) \<Longrightarrow> {A \<in> G . p \<in> A} \<lesssim>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" (is "_ \<Longrightarrow> ?G(p) \<lesssim>\<^bsup>M\<^esup> _") for p
        by (auto intro!:lepoll_rel_eq_trans[OF subset_imp_lepoll_rel] dest:transM)
      moreover from calculation
      have "M(p) \<Longrightarrow> ?G(p) \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" for p
        using \<open>M(G) \<Longrightarrow> M(p) \<Longrightarrow> M({A\<in>G . p \<in> A})\<close>
        unfolding lesspoll_rel_def by simp
      moreover from calculation
      have "M(p) \<Longrightarrow> ?G(p) \<lesssim>\<^bsup>M\<^esup> \<omega>" for p
        using lesspoll_rel_Aleph_rel_succ[of 0] Aleph_rel_zero by auto
      moreover
      have "{A \<in> G . S \<inter> A \<noteq> 0} = (\<Union>p\<in>S. ?G(p))" for S
        by auto
      moreover from calculation
      have "M(S) \<Longrightarrow> i \<in> S \<Longrightarrow> M({x \<in> G . i \<in> x})" for i S
        by (auto dest: transM)
      moreover
      have "M(S) \<Longrightarrow> countable_rel(M,S) \<Longrightarrow> countable_rel(M,{A \<in> G . S \<inter> A \<noteq> 0})" for S
      proof -
        from \<open>M(G)\<close>
        interpret M_replacement_lepoll M "\<lambda>_ x. Collect(G, (\<in>)(x))"
          using countable_lepoll_assms lam_replacement_inj_rel separation_in_rev
            lam_replacement_Collect[OF _ _ insnd_ball] mem_F_bound6[of _ G]
          by unfold_locales
            (auto dest:transM intro:lam_Least_assumption_general[of _  _ _ _ Union])
        fix S
        assume "M(S)"
        with \<open>M(G)\<close> \<open>\<And>i. M(S) \<Longrightarrow> i \<in> S \<Longrightarrow> M({x \<in> G . i \<in> x})\<close>
        interpret M_cardinal_UN_lepoll _ ?G S
          using lepoll_assumptions
          by unfold_locales (auto dest:transM)
        assume "countable_rel(M,S)"
        with \<open>M(S)\<close> calculation(6) calculation(7,8)[of S]
        show "countable_rel(M,{A \<in> G . S \<inter> A \<noteq> 0})"
          using InfCard_rel_nat Card_rel_nat
            le_Card_rel_iff[THEN iffD2, THEN [3] leqpoll_rel_imp_cardinal_rel_UN_le,
              THEN [4] le_Card_rel_iff[THEN iffD1], of \<omega>] j.UN_closed
          unfolding countable_rel_def by (auto dest: transM)
      qed
      define Disjoint where "Disjoint = {<A,B> \<in> G\<times>G . B \<inter> A = 0}"
      have "Disjoint = {x \<in> G\<times>G . \<exists> a b. x=<a,b> \<and> a\<inter>b=0}"
        unfolding Disjoint_def by force
      with \<open>M(G)\<close>
      have "M(Disjoint)"
        using disjoint_separation by simp
      text\<open>For every countable\_rel subfamily of \<^term>\<open>G\<close> there is another some
      element disjoint from all of them:\<close>
      have "\<exists>A\<in>G. \<forall>S\<in>X. <S,A>\<in>Disjoint" if "|X|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "X \<subseteq> G" "M(X)" for X
      proof -
        note \<open>n\<in>\<omega>\<close> \<open>M(G)\<close>
        moreover from this and \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = succ(n)\<close>
        have "|A|\<^bsup>M\<^esup>= succ(n)" "M(A)" if "A\<in>G" for A
          using that Finite_cardinal_rel_eq_cardinal[of A] Finite_cardinal_rel_iff'[of A]
            nat_into_Finite transM[of A G] by (auto dest:transM)
        ultimately
        have "A\<in>G \<Longrightarrow> Finite(A)" for A
          using cardinal_rel_Card_rel_eqpoll_rel_iff[of "succ(n)" A]
            Finite_cardinal_rel_eq_cardinal[of A] nat_into_Card_rel[of "succ(n)"]
            nat_into_M[of n] unfolding Finite_def eqpoll_rel_def by (auto)
        with \<open>X\<subseteq>G\<close> \<open>M(X)\<close>
        have "A\<in>X \<Longrightarrow> countable_rel(M,A)" for A
          using Finite_imp_countable_rel by (auto dest: transM)
        moreover from \<open>M(X)\<close>
        have "M(\<Union>X)" by simp
        moreover
        note \<open>|X|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(X)\<close>
        ultimately
        have "countable_rel(M,\<Union>X)"
          using Card_rel_nat[THEN cardinal_rel_lt_csucc_rel_iff, of X]
            countable_rel_union_countable_rel[of X]
            countable_rel_iff_cardinal_rel_le_nat[of X] Aleph_rel_succ
            Aleph_rel_zero by simp
        with \<open>M(\<Union>X)\<close> \<open>M(_) \<Longrightarrow> countable_rel(M,_) \<Longrightarrow> countable_rel(M,{A \<in> G . _  \<inter> A \<noteq> 0})\<close>
        have "countable_rel(M,{A \<in> G . (\<Union>X) \<inter> A \<noteq> 0})" by simp
        with \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(G)\<close>
        obtain B where "B\<in>G" "B \<notin> {A \<in> G . (\<Union>X) \<inter> A \<noteq> 0}"
          using nat_lt_Aleph_rel1 cardinal_rel_Card_rel_eqpoll_rel_iff[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
            uncountable_rel_not_subset_countable_rel
            [of "{A \<in> G . (\<Union>X) \<inter> A \<noteq> 0}" G]
            uncountable_rel_iff_nat_lt_cardinal_rel[of G]
          by force
        then
        have "\<exists>A\<in>G. \<forall>S\<in>X. A \<inter> S = 0" by auto
        with \<open>X\<subseteq>G\<close>
        show "\<exists>A\<in>G. \<forall>S\<in>X. <S,A>\<in>Disjoint" unfolding Disjoint_def
          using subsetD by simp
      qed
      moreover from \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(G)\<close>
      obtain b where "b\<in>G"
        using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1
          uncountable_rel_not_empty by blast
      ultimately
      text\<open>Hence, the hypotheses to perform a bounded-cardinal selection
      are satisfied,\<close>
      obtain S where "S:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<^bsup>M\<^esup>G" "\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<beta>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> <S`\<alpha>, S`\<beta>> \<in>Disjoint"
        for \<alpha> \<beta>
        using bounded_cardinal_rel_selection[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G Disjoint] \<open>M(Disjoint)\<close>
        by force
      moreover from this \<open>n\<in>\<omega>\<close> \<open>M(G)\<close>
      have inM:"M(S)" "M(n)" "\<And>x. x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> S ` x \<in> G" "\<And>x. x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> M(x)"
        using function_space_rel_char by (auto dest: transM)
      ultimately
      have "\<alpha> \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<beta> \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0" for \<alpha> \<beta>
        unfolding Disjoint_def
        using lt_neq_symmetry[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<inter> S`\<beta> = 0"] Card_rel_is_Ord
        by auto (blast)
      text\<open>and a symmetry argument shows that obtained \<^term>\<open>S\<close> is
      an injective  \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>-sequence of disjoint elements of \<^term>\<open>G\<close>.\<close>
      moreover from this and \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = succ(n)\<close> inM
        \<open>S : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow>\<^bsup>M\<^esup> G\<close> \<open>M(G)\<close>
      have "S \<in> inj_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, G)"
        using def_inj_rel[OF Aleph_rel_closed \<open>M(G)\<close>, of 1]
      proof (clarsimp)
        fix w x
        from inM
        have "a \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> b \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> a \<noteq> b \<Longrightarrow> S ` a \<noteq> S ` b" for a b
          using \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = succ(n)\<close>[THEN [4] cardinal_rel_succ_not_0[THEN [4]
                Int_eq_zero_imp_not_eq[OF calculation, of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<lambda>x. x"],
                of "\<lambda>_.n"], OF _ _ _ _ apply_closed] by auto
        moreover
        assume "w \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "S ` w = S ` x"
        ultimately
        show "w = x" by blast
      qed
      moreover from this \<open>M(G)\<close>
      have "range(S) \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using inj_rel_bij_rel_range eqpoll_rel_sym unfolding eqpoll_rel_def
        by (blast dest: transM)
      moreover
      note \<open>M(G)\<close>
      moreover from calculation
      have "range(S) \<subseteq> G"
        using inj_rel_is_fun range_fun_subset_codomain
        by (fastforce dest: transM)
      moreover
      note \<open>M(S)\<close>
      ultimately
      show "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using inj_rel_is_fun ZF_Library.range_eq_image[of S "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
          image_function[OF fun_is_function, OF inj_rel_is_fun, of S "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
          domain_of_fun[OF inj_rel_is_fun, of S "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G] apply_replacement[of S]
        by (rule_tac x="S``\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" in rexI) (auto dest:transM intro!:RepFun_closed)
      text\<open>This finishes the successor case and hence the proof.\<close>
    qed
  qed
  with \<open>G \<subseteq> F\<close>
  show ?thesis by blast
qed

lemma delta_system_uncountable_rel:
  assumes "\<forall>A\<in>F. Finite(A)" "uncountable_rel(M,F)" "M(F)"
  shows "\<exists>D[M]. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  from assms
  obtain S where "S \<subseteq> F" "S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(S)"
    using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1[of F] by auto
  moreover from \<open>\<forall>A\<in>F. Finite(A)\<close> and this
  have "\<forall>A\<in>S. Finite(A)" by auto
  ultimately
  show ?thesis using delta_system_Aleph_rel1[of S]
    by (auto dest:transM)
qed

end \<comment> \<open>\<^locale>\<open>M_delta\<close>\<close>

end