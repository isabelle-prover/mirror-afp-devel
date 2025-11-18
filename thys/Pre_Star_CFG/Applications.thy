(* Authors: Tassilo Lemke, Tobias Nipkow *)

section \<open>Application to Elementary CFG Problems\<close>
text\<open>\label{sec:applications}\<close>

theory Applications
imports Pre_Star
begin

text\<open>This theory turns @{const pre_star_auto} into executable decision procedures
for different CFG problems. The methos: @{const pre_star_auto} is applied to different
suitable automata/languages. This happens behind the scenes via code equations.\<close>

text\<open>These lemmas link @{const pre_star} to different properties of context-free grammars:\<close>

lemma pre_star_term:
  "x \<in> pre_star P L \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> x \<Rightarrow>* w)"
  unfolding pre_star_def by blast

lemma pre_star_word:
  "[Nt S] \<in> pre_star P (map Tm ` L) \<longleftrightarrow> (\<exists>w. w \<in> L \<and> w \<in> Lang P S)"
  unfolding Lang_def pre_star_def by blast

lemma pre_star_lang:
  "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map Tm ` L)"
  using pre_star_word[where P=P] by blast

(* TODO: rm with next release: rename tms_syms \<rightarrow> Tms_syms elsewehere; rm tms_syms *)
subsection\<open>Preliminaries\<close>

lemma tms_syms_code[code]:
  "tms_syms w = \<Union>((\<lambda>A. case A of Tm x \<Rightarrow> {x} | _ \<Rightarrow> {}) ` set w)"
  by (auto simp: tms_syms_def split: sym.splits)


subsection\<open>Derivability\<close>

text\<open>A decision procedure for derivability can be constructed.\<close>

definition is_derivable :: "('n, 't) Prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
[simp]: "is_derivable P \<alpha> \<beta> = (P \<turnstile> \<alpha> \<Rightarrow>* \<beta>)"

declare is_derivable_def[symmetric, code_unfold]

theorem pre_star_derivability:
  shows "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<longleftrightarrow> \<alpha> \<in> pre_star P {\<beta>}"
  by (simp add: Lang_def pre_star_def)

lemma pre_star_derivability_code[code]:
  fixes P :: "('n, 't) prods"
  shows "is_derivable (set P) \<alpha> \<beta> = (\<alpha> \<in> Lang_auto (pre_star_auto (set P) (word_auto \<beta>)))"
proof -
  define M where [simp]: "M \<equiv> word_auto \<beta>"
  have "Lang_auto (pre_star_auto (set P) M) = pre_star (set P) (Lang_auto M)"
    by (intro pre_star_auto_correct; simp add: word_auto_finite_lts)
  then show ?thesis
    using pre_star_derivability by force
qed


subsection\<open>Membership Problem\<close>

\<comment> \<open>Directly follows from derivability:\<close>
lemma pre_star_membership[code_unfold]: "(w \<in> Lang P S) = (P \<turnstile> [Nt S] \<Rightarrow>* map Tm w)"
  by (simp add: Lang_def)


subsection\<open>Nullable Variables\<close>

definition is_nullable :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> bool" where
  "is_nullable P X \<equiv> (P \<turnstile> [Nt X] \<Rightarrow>* [])"

\<comment> \<open>Directly follows from derivability:\<close>
lemma pre_star_nullable[code]: "is_nullable P X = (P \<turnstile> [Nt X] \<Rightarrow>* [])"
  by (simp add: is_nullable_def)


subsection\<open>Emptiness Problem\<close>

definition is_empty :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> bool" where
[simp]:  "is_empty P S = (Lang P S = {})"

lemma cfg_derives_Syms:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>* \<beta>" and "set \<alpha> \<subseteq> Syms P"
  shows "set \<beta> \<subseteq> Syms P"
  using assms proof (induction rule: converse_rtranclp_induct[where r="derive P"])
  case base
  then show ?case
    by simp
next
  case (step y z)
  then have "set z \<subseteq> Syms P"
    using derives_set_subset by blast
  then show ?case
    using step by simp
qed

lemma cfg_Lang_univ: "P \<turnstile> [Nt X] \<Rightarrow>* map Tm \<beta> \<Longrightarrow> set \<beta> \<subseteq> Tms P"
proof -
  assume "P \<turnstile> [Nt X] \<Rightarrow>* map Tm \<beta>"
  moreover have "Nt X \<in> Syms P"
    using Syms_def calculation derives_start1 by fastforce
  ultimately have "set (map Tm \<beta>) \<subseteq> Syms P"
    using cfg_derives_Syms by force
  moreover have "\<And>t. (t \<in> Tms P) \<longleftrightarrow> Tm t \<in> Syms P"
    unfolding Tms_def Syms_def tms_syms_def by blast
  ultimately show "set \<beta> \<subseteq> Tms P"
    by force
qed

lemma inj_Tm: "inj Tm"
  by (simp add: inj_def)

(* TODO: rm with next release *)
lemma finite_tms_syms: "finite (tms_syms w)"
proof -
  have "Tm ` {A. Tm A \<in> set w} \<subseteq> set w"
    by auto
  from finite_inverse_image[OF _ inj_Tm] show ?thesis
    unfolding tms_syms_def using finite_inverse_image[OF _ inj_Tm] by auto
qed

lemma finite_Tms: "finite P \<Longrightarrow> finite (Tms P)"
  unfolding Tms_def by (rule finite_Union; auto simp: finite_tms_syms)

definition pre_star_emptiness_auto :: "('n, 't) Prods \<Rightarrow> (unit, ('n, 't) sym) auto" where
  "pre_star_emptiness_auto P \<equiv>
    let T = Tm ` \<Union>((\<lambda>A. case A of Nt X \<Rightarrow> {} | Tm x \<Rightarrow> {x}) ` \<Union>(set ` snd ` P)) :: ('n, 't) sym set in
    \<lparr> auto.lts = {()} \<times> T \<times> {()}, start = (), finals = {()} \<rparr>"

theorem pre_star_emptiness:
  fixes P :: "('n, 't) Prods"
  shows "Lang P S = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P {w. set w \<subseteq> Tm ` Tms P}"
proof -
  have "Lang P S = {} \<longleftrightarrow> (\<nexists>w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w)"
    by (simp add: Lang_def)
  also have "... \<longleftrightarrow> (\<nexists>w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w \<and> set w \<subseteq> Tms P)"
    using cfg_Lang_univ by fast
  also have "... \<longleftrightarrow> (\<nexists>w. P \<turnstile> [Nt S] \<Rightarrow>* w \<and> set w \<subseteq> Tm ` Tms P)"
    by (smt (verit, best) cfg_Lang_univ ex_map_conv imageE image_mono list.set_map subset_iff)
  also have "... \<longleftrightarrow> [Nt S] \<notin> pre_star P {w. set w \<subseteq> Tm ` Tms P}"
    unfolding pre_star_def by blast
  finally show ?thesis .
qed

lemma pre_star_emptiness_code[code]:
  fixes P :: "('n, 't) prods"
  shows "is_empty (set P) S = ([Nt S] \<notin> Lang_auto (pre_star_auto (set P) (auto_univ (Tm ` Tms (set P)))))"
proof -
  define M :: "(unit, ('n, 't) sym) auto" where [simp]: "M \<equiv> auto_univ (Tm ` Tms (set P))"
  have "finite (Tm ` Tms (set P))"
    using finite_Tms by blast
  then have "Lang_auto (pre_star_auto (set P) M) = pre_star (set P) (Lang_auto M)"
    by (intro pre_star_auto_correct; auto simp: auto_univ_def intro: loop_lts_fin)
  then show ?thesis
    using pre_star_emptiness unfolding M_def auto_univ_lang by fastforce
qed


subsection\<open>Useless Variables\<close>

definition is_reachable_from :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool"
    ("(2_ \<turnstile>/ (_/ \<Rightarrow>\<^sup>? / _))" [50, 0, 50] 50) where
  "(P \<turnstile> X \<Rightarrow>\<^sup>? Y) \<equiv> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt X] \<Rightarrow>* (\<alpha>@[Nt Y]@\<beta>))"

\<comment>\<open>\<open>X \<in> V\<close> is useful, iff \<open>V\<close> can be reached from \<open>S\<close> and it is productive:\<close>
definition is_useful :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "is_useful P S X \<equiv> (P \<turnstile> S \<Rightarrow>\<^sup>? X) \<and> Lang P X \<noteq> {}"

definition pre_star_reachable_auto :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> (nat, ('n, 't) sym) auto" where
  "pre_star_reachable_auto P X \<equiv> (
    let T = \<Union>(set ` snd ` P) in
    \<lparr> auto.lts = ({0} \<times> T \<times> {0}) \<union> ({1} \<times> T \<times> {1}) \<union> {(0, Nt X, 1)}, start = 0, finals = {1} \<rparr>
  )"

theorem pre_star_reachable:
  fixes P :: "('n, 't) Prods"
  shows "(P \<turnstile> S \<Rightarrow>\<^sup>? X) \<longleftrightarrow> [Nt S] \<in> pre_star P { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P }"
proof -
  define L where "L \<equiv> { (\<alpha>::('n, 't) syms)@[Nt X]@\<beta> | \<alpha> \<beta>. set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P }"
  have "[Nt S] \<in> pre_star P L  \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> [Nt S] \<Rightarrow>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>) \<and> set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P)"
    unfolding L_def by blast
  also have "... \<longleftrightarrow> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>))"
  proof -
    have "\<And>w. P \<turnstile> [Nt S] \<Rightarrow> w \<Longrightarrow> set w \<subseteq> Syms P"
      by (smt (verit, best) Syms_def UN_I UnCI case_prod_conv derive_singleton subset_eq)
    then have "\<And>w. w \<noteq> [Nt S] \<Longrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w \<Longrightarrow> set w \<subseteq> Syms P"
      by (metis cfg_derives_Syms converse_rtranclpE)
    then have "\<And>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>) \<Longrightarrow> set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P"
      by (smt (verit) Cons_eq_append_conv append_is_Nil_conv empty_set empty_subsetI le_supE list.discI set_append)
    then show ?thesis
      by blast
  qed
  finally show ?thesis
    by (simp add: is_reachable_from_def L_def)
qed

lemma pre_star_reachable_code[code]:
  fixes P :: "('n, 't) prods"
  shows "(set P \<turnstile> S \<Rightarrow>\<^sup>? X) = ([Nt S] \<in> Lang_auto (pre_star_auto (set P) (cps_auto (Nt X) (Syms (set P)))))"
proof -
  define M :: "(nat, ('n, 't) sym) auto" where [simp]: "M \<equiv> cps_auto (Nt X) (Syms (set P))"
  have "finite (Syms (set P))"
    unfolding Syms_def by fast
  then have "Lang_auto (pre_star_auto (set P) M) = pre_star (set P) (Lang_auto M)"
    by (intro pre_star_auto_correct; auto simp: cps_auto_def intro: pcs_lts_fin)
  then show ?thesis
    using pre_star_reachable unfolding M_def cps_auto_lang by fastforce
qed


subsection\<open>Disjointness and Subset Problem\<close>

theorem pre_star_disjointness: "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map Tm ` L)"
  by (simp add: pre_star_lang)

theorem pre_star_subset: "Lang P S \<subseteq> L \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map Tm ` (-L))"
proof -
  have "Lang P S \<subseteq> L \<longleftrightarrow> Lang P S \<inter> -L = {}"
    by blast
  then show ?thesis
    by (simp add: pre_star_disjointness)
qed

end
