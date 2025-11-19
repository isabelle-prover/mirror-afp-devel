(* Title:      Kolmgorov_Chentsov/Stochastic_Processes.thy
   Author:     Christian Pardillo Laursen, University of York
*)

section "Stochastic processes"

theory Stochastic_Processes
  imports Kolmogorov_Chentsov_Extras Dyadic_Interval
begin

text \<open> A stochastic process is an indexed collection of random variables. For compatibility with 
  \texttt{product\_prob\_space} we don't enforce conditions on the index set $I$ in the assumptions. \<close>

locale stochastic_process = prob_space +
  fixes M' :: "'b measure"
    and I :: "'t set"
    and X :: "'t \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes random_process[measurable]: "\<And>i. random_variable M' (X i)"

sublocale stochastic_process \<subseteq> product: product_prob_space "(\<lambda>t. distr M M' (X t))"
  using prob_space_distr random_process by (blast intro: product_prob_spaceI)

lemma (in prob_space) stochastic_processI:
  assumes "\<And>i. random_variable M' (X i)"
  shows "stochastic_process M M' X"
  by (simp add: assms prob_space_axioms stochastic_process_axioms.intro stochastic_process_def)

typedef ('t, 'a, 'b) stochastic_process =
  "{(M :: 'a measure, M' :: 'b measure, I :: 't set, X :: 't \<Rightarrow> 'a \<Rightarrow> 'b).
   stochastic_process M M' X}"
proof
  show "(return (sigma UNIV {{}, UNIV}) x, sigma UNIV UNIV, UNIV, \<lambda>_ _. c) \<in>
       {(M, M', I, X). stochastic_process M M' X}" for x :: 'a and c :: 'b
    by (simp add: prob_space_return prob_space.stochastic_processI)
qed

setup_lifting type_definition_stochastic_process

lift_definition proc_source :: "('t,'a,'b) stochastic_process \<Rightarrow> 'a measure"
  is "fst" .

interpretation proc_source: prob_space "proc_source X"
  by (induction, simp add: proc_source_def Abs_stochastic_process_inverse case_prod_beta' stochastic_process_def)

lift_definition proc_target :: "('t,'a,'b) stochastic_process \<Rightarrow> 'b measure"
  is "fst \<circ> snd" .

lift_definition proc_index :: "('t,'a,'b) stochastic_process \<Rightarrow> 't set"
  is "fst \<circ> snd \<circ> snd" .

lift_definition process :: "('t,'a,'b) stochastic_process \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> 'b"
  is "snd \<circ> snd \<circ> snd" .

declare [[coercion process]]

lemma stochastic_process_construct [simp]: "stochastic_process (proc_source X) (proc_target X) (process X)"
  by (transfer, force)

interpretation stochastic_process "proc_source X" "proc_target X" "proc_index X" "process X"
  by simp

lemma stochastic_process_measurable [measurable]: "process X t \<in> (proc_source X) \<rightarrow>\<^sub>M (proc_target X)"
  by (meson random_process)
text \<open> Here we construct a process on a given index set. For this we need to produce measurable
  functions for indices outside the index set; we use the constant function, but it needs to point at
  an element of the target set to be measurable. \<close>

context prob_space
begin

lift_definition process_of :: "'b measure \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('t,'a,'b) stochastic_process"
  is "\<lambda> M' I X \<omega>. if (\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M') \<and> \<omega> \<in> space M'
  then (M, M', I, (\<lambda>t. if t \<in> I then X t else (\<lambda>_. \<omega>)))
  else (return (sigma UNIV {{}, UNIV}) (SOME x. True), sigma UNIV UNIV, I, \<lambda>_ _. \<omega>)"
  by (simp add: stochastic_processI prob_space_return prob_space.stochastic_processI)

lemma index_process_of[simp]: "proc_index (process_of M' I X \<omega>) = I"
  by (transfer, auto)

lemma
  assumes "\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'" "\<omega> \<in> space M'"
  shows
    source_process_of[simp]: "proc_source (process_of M' I X \<omega>) = M" and
    target_process_of[simp]: "proc_target (process_of M' I X \<omega>) = M'" and
    process_process_of[simp]: "process (process_of M' I X \<omega>) = (\<lambda>t. if t \<in> I then X t else (\<lambda>_. \<omega>))"
  using assms by (transfer, auto)+

lemma process_of_apply:
  assumes "\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'" "\<omega> \<in> space M'" "t \<in> I"
  shows "process (process_of M' I X \<omega>) t = X t"
  using assms by (meson process_process_of)
end

text \<open> We define the finite-dimensional distributions of our process. \<close>

lift_definition distributions :: "('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'b) measure"
  is "\<lambda>(M, M', _, X) T. (\<Pi>\<^sub>M t\<in>T. distr M M' (X t))" .

lemma distributions_altdef: "distributions X T = (\<Pi>\<^sub>M t\<in>T. distr (proc_source X) (proc_target X) (X t))"
  by (transfer, auto)

lemma prob_space_distributions: "prob_space (distributions X J)"
  unfolding distributions_altdef
  by (simp add: prob_space_PiM proc_source.prob_space_distr random_process)

lemma sets_distributions: "sets (distributions X J) = sets (PiM J (\<lambda>_. (proc_target X)))"
  by (transfer, auto cong: sets_PiM_cong)

lemma space_distributions: "space (distributions X J) = (\<Pi>\<^sub>E i\<in>J. space (proc_target X))"
  by (transfer, auto simp add: space_PiM)

lemma emeasure_distributions:
  assumes "finite J" "\<And>j. j\<in>J \<Longrightarrow> A j \<in> sets (proc_target X)"
  shows "emeasure (distributions X J) (Pi\<^sub>E J A) = (\<Prod>j\<in>J. emeasure (distr (proc_source X) (proc_target X) (X j)) (A j))"
  by (simp add: assms(1) assms(2) distributions_altdef product.emeasure_PiM)

interpretation projective_family "(proc_index X)" "distributions X" "(\<lambda>_. proc_target X)"
proof (intro projective_family.intro)
  fix J and H
  let ?I = "proc_index X"
    and ?M = "proc_source X"
    and ?M' = "proc_target X"
  assume *: "J \<subseteq> H" "finite H" "H \<subseteq> ?I"
  then have "J \<subseteq> ?I"
    by simp
  show "distributions X J = distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)"
  proof (rule measure_eqI)
    show "sets (distributions X J) = sets (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J))"
      by (simp add: sets_distributions)
    fix S assume "S \<in> sets (distributions X J)"
    then have in_sets: "S \<in> sets (PiM J (\<lambda>_. ?M'))"
      by (simp add: sets_distributions)
    have prod_emb_distr: "(prod_emb H (\<lambda>_. ?M') J S) = (prod_emb H (\<lambda>t. distr ?M ?M' (X t)) J S)"
      by (simp add: prod_emb_def)
    have "emeasure (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)) S =
          emeasure (distributions X H) (prod_emb H (\<lambda>_. ?M') J S)"
      apply (rule emeasure_distr_restrict)
      by (simp_all add: "*" sets_distributions in_sets)
    also have "... = emeasure (distributions X J) S"
      unfolding distributions_altdef
      using *(1,2) in_sets prod_emb_distr by force
    finally show "emeasure (distributions X J) S 
                = emeasure (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)) S"
      by argo
  qed
qed (rule prob_space_distributions)

locale polish_stochastic = stochastic_process M "borel :: 'b::polish_space measure" I X
  for M and I and X

(*
sublocale polish_stochastic \<subseteq> polish_projective I distributions
  by (simp add: polish_projective.intro projective_family_axioms) *)

lemma distributed_cong_random_variable:
  assumes "M = K" "N = L" "AE x in M. X x = Y x" "X \<in> M \<rightarrow>\<^sub>M N" "Y \<in> K \<rightarrow>\<^sub>M L" "f \<in> borel_measurable N"
  shows "distributed M N X f \<longleftrightarrow> distributed K L Y f"
  using assms by (auto simp add: distributed_def distr_cong_AE)

text \<open> For all sorted lists of indices, the increments specified by this list are independent \<close>

lift_definition indep_increments :: "('t :: linorder, 'a, 'b :: minus) stochastic_process \<Rightarrow> bool" is
  "\<lambda>(M, M', I, X).
  (\<forall>l. set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2 \<longrightarrow>
     prob_space.indep_vars M (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l})" .

lemma indep_incrementsE:
  assumes "indep_increments X"
    and "set l \<subseteq> proc_index X \<and> sorted l \<and> length l \<ge> 2"
  shows "prob_space.indep_vars (proc_source X) (\<lambda>_. proc_target X)
         (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}"
  using assms by (transfer, auto)

lemma indep_incrementsI:
  assumes "\<And>l. set l \<subseteq> proc_index X \<Longrightarrow> sorted l \<Longrightarrow> length l \<ge> 2 \<Longrightarrow>
   prob_space.indep_vars (proc_source X) (\<lambda>_. proc_target X) (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}"
  shows "indep_increments X"
  using assms by (transfer, auto)

lemma indep_increments_indep_var:
  assumes "indep_increments X" "h \<in> proc_index X" "j \<in> proc_index X" "k \<in> proc_index X" "h \<le> j" "j \<le> k"
  shows "prob_space.indep_var (proc_source X) (proc_target X) (\<lambda>v. X j v - X h v) (proc_target X) (\<lambda>v. X k v - X j v)"
proof -
  let ?l = "[h,j,k]"
  have "set ?l \<subseteq> proc_index X \<and> sorted ?l \<and> 2 \<le> length ?l"
    using assms by auto
  then have "prob_space.indep_vars (proc_source X) (\<lambda>_. proc_target X) (\<lambda>k v. X (?l!k) v - X (?l!(k-1)) v) {1..<length ?l}"
    by (rule indep_incrementsE[OF assms(1)])
  then show ?thesis
    using proc_source.indep_vars_indep_var by fastforce
qed

definition "stationary_increments X \<longleftrightarrow> (\<forall>t1 t2 k. t1 > 0 \<and> t2 > 0 \<and> k > 0 \<longrightarrow> 
     distr (proc_source X) (proc_target X) (\<lambda>v. X (t1 + k) v - X t1 v) =
     distr (proc_source X) (proc_target X) (\<lambda>v. X (t2 + k) v - X t2 v))"

text \<open> Processes on the same source measure space, with the same index space, but not necessarily the same
  target measure since we only care about the measurable target space, not the measure \<close>

lift_definition compatible :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool"
  is "\<lambda>(Mx, M'x, Ix, X) (My, M'y, Iy, _). Mx = My \<and> sets M'x = sets M'y \<and> Ix = Iy" .

lemma compatibleI:
  assumes "proc_source X = proc_source Y" "sets (proc_target X) = sets (proc_target Y)"
    "proc_index X = proc_index Y"
  shows "compatible X Y"
  using assms by (transfer, auto)

lemma
  assumes "compatible X Y"
  shows
    compatible_source [dest]: "proc_source X = proc_source Y" and
    compatible_target [dest]: "sets (proc_target X) = sets (proc_target Y)" and
    compatible_index [dest]: "proc_index X = proc_index Y"
  using assms by (transfer, auto)+

lemma compatible_refl [simp]: "compatible X X"
  by (transfer, auto)

lemma compatible_sym: "compatible X Y \<Longrightarrow> compatible Y X"
  by (transfer, auto)

lemma compatible_trans:
  assumes "compatible X Y" "compatible Y Z"
  shows "compatible X Z"
  using assms by (transfer, auto)

lemma (in prob_space) compatible_process_of:
  assumes measurable: "\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'" "\<forall>t \<in> I. Y t \<in> M \<rightarrow>\<^sub>M M'" 
    and "a \<in> space M'" "b \<in> space M'"
  shows "compatible (process_of M' I X a) (process_of M' I Y b)"
  using assms by (transfer, auto)

definition modification :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
  "modification X Y \<longleftrightarrow> compatible X Y \<and> (\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x)"

lemma modificationI [intro]:
  assumes "compatible X Y" "\<And>t. t \<in> proc_index X \<Longrightarrow> AE x in proc_source X. X t x = Y t x"
  shows "modification X Y"
  unfolding modification_def using assms by blast

lemma modificationD [dest]:
  assumes "modification X Y"
  shows "compatible X Y"
    and "\<And>t. t \<in> proc_index X \<Longrightarrow> AE x in proc_source X. X t x = Y t x"
  using assms unfolding modification_def by blast+

lemma modification_null_set:
  assumes "modification X Y" "t \<in> proc_index X"
  obtains N where "{x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N" "N \<in> null_sets (proc_source X)"
proof -
  from assms have "AE x in proc_source X. X t x = Y t x"
    by (rule modificationD(2))
  then have "\<exists>N\<in>null_sets (proc_source X). {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N"
    by (simp add: eventually_ae_filter)
  then show ?thesis
    using that by blast
qed

lemma modification_refl [simp]: "modification X X"
  by (simp add: modificationI)

lemma modification_sym: "modification X Y \<Longrightarrow> modification Y X"
proof (rule modificationI)
  assume *: "modification X Y"
  then show compat: "compatible Y X"
    using compatible_sym modificationD(1) by blast
  fix t assume "t \<in> proc_index Y"
  then have "t \<in> proc_index X"
    using compatible_index[OF compat] by blast
  have "AE x in proc_source Y. X t x = Y t x"
    using modificationD(2)[OF * \<open>t \<in> proc_index X\<close>]
      compatible_source[OF compat] by argo
  then show "AE x in proc_source Y. Y t x = X t x"
    by force
qed

lemma modification_trans:
  assumes "modification X Y" "modification Y Z"
  shows "modification X Z"
proof (intro modificationI)
  show "compatible X Z"
    using compatible_trans modificationD(1) assms by blast
  fix t assume t: "t \<in> proc_index X"
  have XY: "AE x in proc_source X. process X t x = process Y t x"
    by (fact modificationD(2)[OF assms(1) t])
  have "t \<in> proc_index Y" "proc_source X = proc_source Y"
    using compatible_index compatible_source assms(1) modificationD(1) t by blast+
  then have "AE x in proc_source X. process Y t x = process Z t x"
    using modificationD(2)[OF assms(2)] by presburger
  then show "AE x in proc_source X. process X t x = process Z t x"
    using XY by fastforce
qed

lemma modification_imp_identical_distributions:
  assumes modification: "modification X Y"
    and index: "T \<subseteq> proc_index X"
  shows "distributions X T = distributions Y T"
proof -
  have "proc_source X = proc_source Y"
    using modification by blast
  moreover have "sets (proc_target X) = sets (proc_target Y)"
    using modification by blast
  ultimately have "distr (proc_source X) (proc_target X) (X x) =
         distr (proc_source Y) (proc_target Y) (Y x)"
    if "x \<in> T" for x
    apply (rule distr_cong_AE)
      apply (metis assms modificationD(2) subset_eq that)
     apply simp_all
    done
  then show ?thesis
    by (auto simp: distributions_altdef cong: PiM_cong)
qed

definition indistinguishable :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
  "indistinguishable X Y \<longleftrightarrow> compatible X Y \<and>
 (\<exists>N \<in> null_sets (proc_source X). \<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)"

lemma indistinguishableI:
  assumes "compatible X Y" 
    and "\<exists>N \<in> null_sets (proc_source X). (\<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)"
  shows "indistinguishable X Y"
  unfolding indistinguishable_def using assms by blast

lemma indistinguishable_null_set:
  assumes "indistinguishable X Y"
  obtains N where 
    "N \<in> null_sets (proc_source X)"
    "\<And>t. t \<in> proc_index X \<Longrightarrow> {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N"
  using assms unfolding indistinguishable_def by force

lemma indistinguishableD:
  assumes "indistinguishable X Y"
  shows "compatible X Y"
    and "\<exists>N \<in> null_sets (proc_source X). (\<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)"
  using assms unfolding indistinguishable_def by blast+

lemma indistinguishable_eq_AE:
  assumes "indistinguishable X Y"
  shows "AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Y t x"
  using assms[THEN indistinguishableD(2)] by (auto simp add: eventually_ae_filter)

lemma indistinguishable_null_ex:
  assumes "indistinguishable X Y"
  shows "\<exists>N \<in> null_sets (proc_source X). {x \<in> space (proc_source X).\<exists>t \<in> proc_index X. X t x \<noteq> Y t x} \<subseteq> N"
  using indistinguishableD(2)[OF assms] by blast

lemma indistinguishable_refl [simp]: "indistinguishable X X"
  by (auto intro: indistinguishableI)

lemma indistinguishable_sym: "indistinguishable X Y \<Longrightarrow> indistinguishable Y X"
  unfolding indistinguishable_def apply (simp add: compatible_sym)
  by (smt (verit, ccfv_SIG) Collect_cong compatible_index compatible_source indistinguishable_def)

lemma indistinguishable_trans:
  assumes "indistinguishable X Y" "indistinguishable Y Z" 
  shows "indistinguishable X Z"
proof (intro indistinguishableI)
  show "compatible X Z"
    using assms indistinguishableD(1) compatible_trans by blast
  have eq: "proc_index X = proc_index Y" "proc_source X = proc_source Y"
    using compatible_index compatible_source indistinguishableD(1)[OF assms(1)] by blast+
  have "AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Y t x"
    by (fact indistinguishable_eq_AE[OF assms(1)])
  moreover have "AE x in proc_source X. \<forall>t \<in> proc_index X. Y t x = Z t x"
    apply (subst eq)+
    by (fact indistinguishable_eq_AE[OF assms(2)])
  ultimately have "AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Z t x"
    using assms by fastforce
  then obtain N where "N \<in> null_sets (proc_source X)" 
    "{x \<in> space (proc_source X).\<exists>t\<in>proc_index X. process X t x \<noteq> process Z t x} \<subseteq> N"
    using eventually_ae_filter by (smt (verit) Collect_cong eventually_ae_filter)
  then show "\<exists>N\<in>null_sets (proc_source X). \<forall>t\<in>proc_index X. {x \<in> space (proc_source X). process X t x \<noteq> process Z t x} \<subseteq> N"
    by blast
qed

lemma indistinguishable_modification: "indistinguishable X Y \<Longrightarrow> modification X Y"
  apply (intro modificationI)
   apply (erule indistinguishableD(1))
  apply (drule indistinguishableD(2))
  using eventually_ae_filter by blast

text \<open> Klenke 21.5(i) \<close>

lemma modification_countable:
  assumes "modification X Y" "countable (proc_index X)"
  shows "indistinguishable X Y"
proof (rule indistinguishableI)
  show "compatible X Y"
    using assms(1) modification_def by auto
  let ?N = "(\<lambda>t. {x \<in> space (proc_source X). X t x \<noteq> Y t x})"
  from assms(1) have "\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x"
    unfolding modification_def by argo
  then have "\<And>t. t \<in> proc_index X \<Longrightarrow> \<exists>N \<in> null_sets (proc_source X). ?N t \<subseteq> N"
    by (subst eventually_ae_filter[symmetric], blast)
  then have "\<exists>N. \<forall>t \<in> proc_index X. N t \<in> null_sets (proc_source X) \<and> ?N t \<subseteq> N t"
    by meson
  then obtain N where N: "\<forall>t \<in> proc_index X. (N t) \<in> null_sets (proc_source X) \<and> ?N t \<subseteq> N t"
    by blast
  then have null: "(\<Union>t \<in> proc_index X. N t) \<in> null_sets (proc_source X)"
    by (simp add: null_sets_UN' assms(2))
  moreover have "\<forall>t\<in>proc_index X. ?N t \<subseteq> (\<Union>t \<in> proc_index X. N t)"
    using N by blast 
  ultimately show "\<exists>N\<in> null_sets (proc_source X). (\<forall>t\<in>proc_index X. ?N t \<subseteq> N)"
    by blast
qed

text \<open> Klenke 21.5(ii). The textbook statement is more general - we reduce right continuity to regular continuity \<close>

lemma modification_continuous_indistinguishable:
  fixes X :: "(real, 'a, 'b :: metric_space) stochastic_process"
  assumes modification: "modification X Y"
    and interval: "\<exists>T > 0. proc_index X = {0..T}"
    and rc: "AE \<omega> in proc_source X. continuous_on (proc_index X) (\<lambda>t. X t \<omega>)"
    (is "AE \<omega> in proc_source X. ?cont_X \<omega>")
    "AE \<omega> in proc_source Y. continuous_on (proc_index Y) (\<lambda>t. Y t \<omega>)"
    (is "AE \<omega> in proc_source Y. ?cont_Y \<omega>")
  shows "indistinguishable X Y"
proof (rule indistinguishableI)
  show "compatible X Y"
    using modification modification_def by blast
  obtain T where T: "proc_index X = {0..T}" "T > 0"
    using interval by blast
  define N where "N \<equiv> \<lambda>t. {x \<in> space (proc_source X). X t x \<noteq> Y t x}"
  have 1: "\<forall>t \<in> proc_index X. \<exists>S. N t \<subseteq> S \<and> S \<in> null_sets (proc_source X)"
    using modificationD(2)[OF modification] by (auto simp add: N_def eventually_ae_filter)
  text \<open> $S$ is a null set such that $X_t(x) \neq Y_t(x) \Longrightarrow x \in S_t$ \<close>
  obtain S where S: "\<forall>t \<in> proc_index X. N t \<subseteq> S t \<and> S t \<in> null_sets (proc_source X)"
    using bchoice[OF 1] by blast
  have eq: "proc_source X = proc_source Y" "proc_index X = proc_index Y"
    using \<open>compatible X Y\<close> compatible_source compatible_index by blast+
  have "AE p in proc_source X. ?cont_X p \<and> ?cont_Y p"
    apply (rule AE_conjI)
    using eq rc by argo+
  text \<open> $R$ is a set of measure 1 such that if $x \in R$ then the paths at $x$ are continuous for $X$ and $Y$ \<close>
  then obtain R where R: "R \<subseteq> {p \<in> space (proc_source X). ?cont_X p \<and> ?cont_Y p}"
    "R \<in> sets (proc_source X)" "measure (proc_source X) R = 1"
    using proc_source.AE_E_prob by blast
  text \<open> We use an interval of dyadic rationals because we need to produce a countable dense set
  for $\{0..T\}$, which we have by @{thm dyadic_interval_dense}. \<close>
  let ?I = "dyadic_interval 0 T"
  let ?N' = "\<Union>n \<in> ?I. N n"
  have N_subset: "\<And>t. t \<in> proc_index X \<Longrightarrow> N t \<inter> R \<subseteq> ?N'"
  proof
    fix t assume "t \<in> proc_index X"
    fix p assume *: "p \<in> N t \<inter> R"
    then obtain \<epsilon> where \<epsilon>: "0 < \<epsilon>" "\<epsilon> = dist (X t p) (Y t p)"
      by (simp add: N_def)
    have cont_p: "continuous_on {0..T} (\<lambda>t. Y t p)" "continuous_on {0..T} (\<lambda>t. X t p)"
      using R *(1) T(1)[symmetric] eq(2) by auto
    then have continuous_dist: "continuous_on {0..T} (\<lambda>t. dist (X t p) (Y t p))"
      using continuous_on_dist by fast
    {
      assume "\<forall>r\<in> ?I. X r p = Y r p"
      then have dist_0: "\<And>r. r \<in> ?I \<Longrightarrow> dist (X r p) (Y r p) = 0"
        by auto
      have "dist (X t p) (Y t p) = 0"
      proof -
        have dist_tendsto_0: "((\<lambda>t. dist (X t p) (Y t p)) \<longlongrightarrow> 0)(at t within ?I)"
          using dist_0 continuous_dist
          by (smt (verit, best) Lim_transform_within \<epsilon> tendsto_const)
        have XY: "((\<lambda>t. X t p) \<longlongrightarrow> X t p)(at t within ?I)" "((\<lambda>t. Y t p) \<longlongrightarrow> Y t p)(at t within ?I)"
          by (metis cont_p T(1) \<open>t \<in> proc_index X\<close> continuous_on_def tendsto_within_subset dyadic_interval_subset_interval)+
        show ?thesis
          apply (rule tendsto_unique[of "at t within ?I"])
            apply (simp add: trivial_limit_within)
            apply (metis T(1) T(2) \<open>t \<in> proc_index X\<close> dyadic_interval_dense islimpt_Icc limpt_of_closure)
          using tendsto_dist[OF XY] dist_tendsto_0 
          by simp_all
      qed
      then have False
        using \<epsilon> by force
    }
    then have "\<exists>r\<in>dyadic_interval 0 T. p \<in> N r"
      unfolding N_def using * R(2) sets.sets_into_space by auto
    then show "p \<in> \<Union> (N ` ?I)"
      by simp
  qed
  have null: "(space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. S r) \<in> null_sets (proc_source X)"
    apply (rule null_sets.Un)
     apply (smt (verit) R(2,3) AE_iff_null_sets proc_source.prob_compl proc_source.prob_eq_0 sets.Diff sets.top)
    by (metis (no_types, lifting) S T(1) dyadic_interval_countable dyadic_interval_subset_interval in_mono null_sets_UN')
  have "(\<Union>r \<in> proc_index X. N r) \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> proc_index X. N r)"
    by blast
  also have "... \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. N r)"
    using N_subset N_def by blast
  also have "... \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. S r)"
    by (smt (verit, ccfv_threshold)S T(1) UN_iff Un_iff dyadic_interval_subset_interval in_mono subsetI)
  finally show "\<exists>N\<in>null_sets (proc_source X). \<forall>t\<in>proc_index X. {x \<in> space (proc_source X). process X t x \<noteq> process Y t x} \<subseteq> N"
    by (smt (verit) N_def null S SUP_le_iff order_trans)
qed

lift_definition restrict_index :: "('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t, 'a, 'b) stochastic_process"
  is "\<lambda>(M, M', I, X) T. (M, M', T, X)" by fast

lemma
  shows
    restrict_index_source[simp]: "proc_source (restrict_index X T) = proc_source X" and
    restrict_index_target[simp]: "proc_target (restrict_index X T) = proc_target X" and
    restrict_index_index[simp]:  "proc_index (restrict_index X T) = T" and
    restrict_index_process[simp]: "process (restrict_index X T) = process X"
  by (transfer, force)+

lemma restrict_index_override[simp]: "restrict_index (restrict_index X T) S = restrict_index X S"
  by (transfer, auto)

lemma compatible_restrict_index:
  assumes "compatible X Y"
  shows "compatible (restrict_index X S) (restrict_index Y S)"
  using assms unfolding compatible_def by (transfer, auto)

lemma modification_restrict_index:
  assumes "modification X Y" "S \<subseteq> proc_index X"
  shows "modification (restrict_index X S) (restrict_index Y S)"
  using assms unfolding modification_def
  apply (simp add: compatible_restrict_index)
  apply (metis restrict_index_source subsetD)
  done

lemma indistinguishable_restrict_index:
  assumes "indistinguishable X Y" "S \<subseteq> proc_index X"
  shows "indistinguishable (restrict_index X S) (restrict_index Y S)"
  using assms unfolding indistinguishable_def by (auto simp: compatible_restrict_index)

lemma AE_eq_minus [intro]:
  fixes a :: "'a \<Rightarrow> ('b :: real_normed_vector)"
  assumes "AE x in M. a x = b x" "AE x in M. c x = d x"
  shows "AE x in M. a x - c x = b x - d x"
  using assms by fastforce

lemma modification_indep_increments:
  fixes X Y :: "('a :: linorder, 'b, 'c :: {second_countable_topology, real_normed_vector}) stochastic_process"
  assumes "modification X Y" "sets (proc_target Y) = sets borel"
  shows "indep_increments X \<Longrightarrow> indep_increments Y"
proof (intro indep_incrementsI, subst proc_source.indep_vars_iff_distr_eq_PiM, goal_cases)
  case (1 l)
  then show ?case by simp
next
  case (2 l i)
  then show ?case
    using assms apply measurable
    using modificationD(1)[OF assms(1), THEN compatible_source] assms(2)
    by (metis measurable_cong_sets random_process)+
next
  case (3 l)
  have target_X [measurable]: "sets (proc_target X) = sets borel"
    using assms by auto
  then have measurable_target: "f \<in> M \<rightarrow>\<^sub>M proc_target X = (f \<in> borel_measurable M)" for f and M :: "'b measure"
    using measurable_cong_sets by blast
  have "AE \<omega> in proc_source X. X (l ! i) \<omega> = Y (l ! i) \<omega>"
    if "i \<in> {0..<length l}" for i
    apply (rule assms(1)[THEN modificationD(2)])
    by (metis 3(2) that assms(1) atLeastLessThan_iff basic_trans_rules(31) 
        compatible_index modificationD(1) nth_mem)
  then have AE_eq: "AE \<omega> in proc_source X. X (l!i) \<omega> - X (l!(i-1)) \<omega> = Y (l!i) \<omega> - Y (l!(i-1)) \<omega>"
    if "i \<in> {1..<length l}" for i
    using AE_eq_minus that by auto
  have AE_eq': "AE x in proc_source X. (\<lambda>i\<in>{1..<length l}. X (l ! i) x - X (l ! (i - 1)) x) = 
        (\<lambda>i\<in>{1..<length l}. Y (l ! i) x - Y (l ! (i - 1)) x)"
  proof (rule AE_mp)
    show "AE \<omega> in proc_source X. \<forall>i \<in>{1..<length l}. X (l!i) \<omega> - X (l!(i-1)) \<omega> = Y (l!i) \<omega> - Y (l!(i-1)) \<omega>"
    proof -
      {
        fix i assume *: "i \<in> {1..<length l}"
        obtain N where 
          "{\<omega> \<in> space (proc_source X). X (l!i) \<omega> - X (l!(i-1)) \<omega> \<noteq> Y (l!i) \<omega> - Y (l!(i-1)) \<omega>} \<subseteq> N"
          "N \<in> proc_source X" "emeasure (proc_source X) N = 0"
          using AE_eq[OF *, THEN AE_E] .
        then have "\<exists>N \<in> null_sets (proc_source X).
         {\<omega> \<in> space (proc_source X). X (l!i) \<omega> - X (l!(i-1)) \<omega> \<noteq> Y (l!i) \<omega> - Y (l!(i-1)) \<omega>} \<subseteq> N"
          by blast
      } then obtain N where N: "N i \<in> null_sets (proc_source X)"
        "{\<omega> \<in> space (proc_source X). X (l!i) \<omega> - X (l!(i-1)) \<omega> \<noteq> Y (l!i) \<omega> - Y (l!(i-1)) \<omega>} \<subseteq> N i"
      if "i \<in> {1..< length l}" for i
        by (metis (lifting) ext)
      have "{\<omega> \<in> space (proc_source X). \<not> (\<forall>i\<in>{1..<length l}. X (l ! i) \<omega> - X (l ! (i - 1)) \<omega> = Y (l ! i) \<omega> - Y (l ! (i - 1)) \<omega>)} \<subseteq> (\<Union> i \<in> {1..< length l}. N i)"
        using N by blast
      moreover have "(\<Union>i \<in> {1..< length l}. N i) \<in> null_sets (proc_source X)"
        apply (rule null_sets.finite_UN)
        using 3 N by simp_all
      ultimately show ?thesis
        by (blast intro: AE_I)
    qed
    show "AE x in proc_source
             X. (\<forall>i\<in>{1..<length l}. process X (l ! i) x - process X (l ! (i - 1)) x = process Y (l ! i) x - process Y (l ! (i - 1)) x) \<longrightarrow>
                (\<lambda>i\<in>{1..<length l}. process X (l ! i) x - process X (l ! (i - 1)) x) = (\<lambda>i\<in>{1..<length l}. process Y (l ! i) x - process Y (l ! (i - 1)) x)"
      by (rule AE_I2, auto)
  qed                                            
  have "distr (proc_source Y) (Pi\<^sub>M {1..<length l} (\<lambda>i. proc_target Y))
                (\<lambda>x. \<lambda>i\<in>{1..<length l}. Y (l ! i) x - Y (l ! (i - 1)) x) =
            distr (proc_source X) (Pi\<^sub>M {1..<length l} (\<lambda>i. proc_target X))
              (\<lambda>x. \<lambda>i\<in>{1..<length l}. X (l ! i) x - X (l ! (i - 1)) x)"
    apply (rule sym)
    apply (rule distr_cong_AE)
    using assms(1) apply blast
       apply (metis assms(2) sets_PiM_cong target_X)
      apply (fact AE_eq')
     apply simp
     apply (rule measurable_restrict)
     apply (simp add: measurable_target)
    subgoal by measurable (meson measurable_target random_process)+
    apply (rule measurable_restrict)
    by (metis (full_types) assms(2) borel_measurable_diff measurable_cong_sets stochastic_process_measurable)
  also have "... = Pi\<^sub>M {1..<length l} (\<lambda>i. distr (proc_source X) (proc_target X) (\<lambda>v. X (l ! i) v - X (l ! (i - 1)) v))"
    apply (subst proc_source.indep_vars_iff_distr_eq_PiM[symmetric])
    subgoal using 3 by simp
     apply simp
     apply (metis (full_types) borel_measurable_diff measurable_cong_sets stochastic_process_measurable target_X)
    apply (rule indep_incrementsE)
     apply (fact 3(1))
    using 3(2-) assms(1) by blast
  also have "... = Pi\<^sub>M {1..<length l} (\<lambda>i. distr (proc_source Y) (proc_target Y) (\<lambda>v. Y (l ! i) v - Y (l ! (i - 1)) v))"
    apply (safe intro!: PiM_cong)
    apply (rule distr_cong_AE)
    subgoal using assms(1) by blast
    subgoal using assms(1) by blast
    subgoal using AE_eq by presburger
    subgoal by (metis (mono_tags) borel_measurable_diff measurable_target random_process)
    by (metis (full_types) assms(2) borel_measurable_diff measurable_cong_sets random_process)
  finally show ?case .
qed

end
