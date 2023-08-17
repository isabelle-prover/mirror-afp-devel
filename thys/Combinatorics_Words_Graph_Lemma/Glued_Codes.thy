(*  Title:      Glued Codes
    File:       Combinatorics_Words_Graph_Lemma.Glued_Codes
    Author:     Martin Raška, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Glued_Codes
  imports Combinatorics_Words.Submonoids
begin

chapter "Glued codes"

section \<open>Lists that do not end with a fixed letter\<close>

lemma append_last_neq:
  "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> vs = \<epsilon> \<or> last vs \<noteq> w \<Longrightarrow> us \<cdot> vs = \<epsilon> \<or> last (us \<cdot> vs) \<noteq> w"
  by (auto simp only: last_append split: if_split)

lemma last_neq_induct [consumes 1, case_names emp hd_eq hd_neq]:
  assumes invariant: "us = \<epsilon> \<or> last us \<noteq> w"
      and emp: "P \<epsilon>"
      and hd_eq: "\<And>us. us \<noteq> \<epsilon> \<Longrightarrow> last us \<noteq> w \<Longrightarrow> P us \<Longrightarrow> P (w # us)"
      and hd_neq: "\<And>u us. u \<noteq> w \<Longrightarrow> us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> P us \<Longrightarrow> P (u # us)"
  shows "P us"
using invariant proof (induction us)
  case (Cons u us)
    have inv: "us = \<epsilon> \<or> last us \<noteq> w"
      using Cons.prems by (intro disjI) simp
    show "P (u # us)"
    proof (cases)
      assume "u = w"
      have *: "us \<noteq> \<epsilon>" and "last us \<noteq> w"
        using Cons.prems unfolding \<open>u = w\<close> by auto
      then show "P (u # us)" unfolding \<open>u = w\<close> using Cons.IH[OF inv] by (fact hd_eq)
    qed (use inv Cons.IH[OF inv] in \<open>fact hd_neq\<close>)
qed (rule \<open>P \<epsilon>\<close>)

lemma last_neq_blockE:
  assumes last_neq: "us \<noteq> \<epsilon>" and "last us \<noteq> w"
  obtains k u us' where "u \<noteq> w" and "us' = \<epsilon> \<or> last us' \<noteq> w" and "[w] \<^sup>@ k \<cdot> u # us' = us"
using disjI2[OF \<open>last us \<noteq> w\<close>] \<open>us \<noteq> \<epsilon>\<close> proof (induction us rule: last_neq_induct)
  case (hd_eq us)
    from \<open>us \<noteq> \<epsilon>\<close> show ?case
      by (rule hd_eq.IH[rotated]) (intro hd_eq.prems(1)[of _ _ "Suc _"], assumption+, simp)
next
  case (hd_neq u us)
    from hd_neq.hyps show ?case
     by (rule hd_neq.prems(1)[of _ _ 0]) simp
qed blast

lemma last_neq_block_induct [consumes 1, case_names emp block]:
  assumes last_neq: "us = \<epsilon> \<or> last us \<noteq> w"
      and emp: "P \<epsilon>"
      and block: "\<And>k u us. u \<noteq> w \<Longrightarrow> us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> P us \<Longrightarrow> P ([w] \<^sup>@ k \<cdot> (u # us))"
  shows "P us"
using last_neq proof (induction us rule: ssuf_induct)
  case (ssuf us)
    show ?case proof (cases "us = \<epsilon>")
      assume "us \<noteq> \<epsilon>"
      obtain k u us' where "u \<noteq> w" and "us' = \<epsilon> \<or> last us' \<noteq> w" and "[w] \<^sup>@ k \<cdot> u # us' = us"
        using \<open>us \<noteq> \<epsilon>\<close> \<open>us = \<epsilon> \<or> last us \<noteq> w\<close> by (elim last_neq_blockE) (simp add: \<open>us \<noteq> \<epsilon>\<close>)
      have "us' <s us" and "us' = \<epsilon> \<or> last us' \<noteq> w"
        using \<open>us = \<epsilon> \<or> last us \<noteq> w\<close> by (auto simp flip: \<open>[w] \<^sup>@ k \<cdot> u # us' = us\<close>)
      from \<open>u \<noteq> w\<close> \<open>us' = \<epsilon> \<or> last us' \<noteq> w\<close> ssuf.IH[OF this]
      show "P us" unfolding \<open>[w] \<^sup>@ k \<cdot> u # us' = us\<close>[symmetric] by (fact block)
    qed (simp only: emp)
qed

section \<open>Glue a list element with its successors/predecessors\<close>

function glue :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  glue_emp:  "glue w \<epsilon> = \<epsilon>" |
  glue_Cons: "glue w (u # us) =
    (let glue_tl = glue w us in
      if u = w then (u \<cdot> hd glue_tl) # tl glue_tl
      else u # glue_tl)"
  unfolding prod_eq_iff prod.sel by (cases rule: list.exhaust[of "snd _"]) blast+
  termination by (relation "measure (length \<circ> snd)") simp_all

lemma no_gluing: "w \<notin> set us \<Longrightarrow> glue w us = us"
  by (induction us) auto

lemma glue_nemp [simp, intro!]: "us \<noteq> \<epsilon> \<Longrightarrow> glue w us \<noteq> \<epsilon>"
  by (elim hd_tlE) (auto simp only: glue.simps Let_def split!: if_split)

lemma glue_is_emp_iff [simp]: "glue w us = \<epsilon> \<longleftrightarrow> us = \<epsilon>"
  using glue_nemp glue_emp by blast

lemma len_glue: "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> \<^bold>|glue w us\<^bold>| + count_list us w = \<^bold>|us\<^bold>|"
  by (induction rule: last_neq_induct) (auto simp add: Let_def)

lemma len_glue_le: assumes "us = \<epsilon> \<or> last us \<noteq> w" shows "\<^bold>|glue w us\<^bold>| \<le> \<^bold>|us\<^bold>|"
  using len_glue[OF assms] unfolding nat_le_iff_add eq_commute[of "\<^bold>|us\<^bold>|"] by blast

lemma len_glue_less []: "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> w \<in> set us \<Longrightarrow> \<^bold>|glue w us\<^bold>| < \<^bold>|us\<^bold>|"
  by (simp add: count_list_gr_0_iff flip: len_glue[of us])

lemma assumes "us = \<epsilon> \<or> last us \<noteq> w" and "\<epsilon> \<notin> set us"
  shows emp_not_in_glue: "\<epsilon> \<notin> set (glue w us)"
    and glued_not_in_glue: "w \<notin> set (glue w us)"
  unfolding atomize_conj using assms by (induction us rule: last_neq_induct)
    (auto simp: Let_def dest!: tl_set lists_hd_in_set[OF glue_nemp[of _ w]])

lemma glue_glue: "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> \<epsilon> \<notin> set us \<Longrightarrow> glue w (glue w us) = glue w us"
  using no_gluing[OF glued_not_in_glue].

lemma glue_block_append: assumes "u \<noteq> w"
  shows "glue w ([w] \<^sup>@ k \<cdot> (u # us)) = (w \<^sup>@ k \<cdot> u) # glue w us"
  by (induction k) (simp_all add: \<open>u \<noteq> w\<close>)

lemma concat_glue [simp]: "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> concat (glue w us) = concat us"
  by (induction us rule: last_neq_block_induct) (simp_all add: glue_block_append)

lemma glue_append:
  "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> glue w (us \<cdot> vs) = glue w us \<cdot> glue w vs"
  by (induction us rule: last_neq_block_induct) (simp_all add: glue_block_append)

lemma glue_pow:
  assumes "us = \<epsilon> \<or> last us \<noteq> w"
  shows "glue w (us \<^sup>@ k) = (glue w us) \<^sup>@ k"
  by (induction k) (simp_all add: assms glue_append)

lemma glue_in_lists_hull [intro]:
  "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> us \<in> lists G \<Longrightarrow> glue w us \<in> lists \<langle>G\<rangle>"
  by (induction rule: last_neq_induct) (simp_all add: Let_def tl_in_lists prod_cl gen_in)

\<comment> \<open>Gluing from the right (gluing a letter with its predecessor)\<close>
function gluer :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  gluer_emp:  "gluer w \<epsilon> = \<epsilon>" |
  gluer_Cons: "gluer w (u # us) =
    (let gluer_butlast = gluer w (butlast (u # us)) in
      if last (u # us) = w then (butlast gluer_butlast) \<cdot> [last gluer_butlast \<cdot> last (u # us)]
      else gluer_butlast \<cdot> [last (u # us)])"
  unfolding prod_eq_iff prod.sel by (cases rule: list.exhaust[of "snd _"]) blast+
  termination by (relation "measure (length \<circ> snd)") simp_all

lemma gluer_nemp_def: assumes "us \<noteq> \<epsilon>"
  shows "gluer w us =
    (let gluer_butlast = gluer w (butlast us) in
      if last us = w then (butlast gluer_butlast) \<cdot> [last gluer_butlast \<cdot> last us]
      else gluer_butlast \<cdot> [last us])"
  using gluer_Cons[of w "hd us" "tl us"] unfolding hd_Cons_tl[OF \<open>us \<noteq> \<epsilon>\<close>].

lemma gluer_nemp: assumes "us \<noteq> \<epsilon>" shows "gluer w us \<noteq> \<epsilon>"
  unfolding gluer_nemp_def[OF \<open>us \<noteq> \<epsilon>\<close>]
  by (simp only: Let_def split!: if_split)

lemma hd_neq_induct [consumes 1, case_names emp snoc_eq snoc_neq]:
  assumes invariant: "us = \<epsilon> \<or> hd us \<noteq> w"
      and emp: "P \<epsilon>"
      and snoc_eq: "\<And>us. us \<noteq> \<epsilon> \<Longrightarrow> hd us \<noteq> w \<Longrightarrow> P us \<Longrightarrow> P (us \<cdot> [w])"
      and snoc_neq: "\<And>u us. u \<noteq> w \<Longrightarrow> us = \<epsilon> \<or> hd us \<noteq> w \<Longrightarrow> P us \<Longrightarrow> P (us \<cdot> [u])"
  shows "P us"
using last_neq_induct[where P="\<lambda>x. P (rev x)" for P, reversed, unfolded rev_rev_ident, OF assms].

lemma gluer_rev [reversal_rule]: assumes "us = \<epsilon> \<or> last us \<noteq> w"
  shows "gluer (rev w) (rev (map rev us)) =  rev (map rev (glue w us))"
  using assms by (induction us rule: last_neq_induct)
    (simp_all add: gluer_nemp_def Let_def map_tl last_rev hd_map)

lemma glue_rev [reversal_rule]: assumes "us = \<epsilon> \<or> hd us \<noteq> w"
  shows "glue (rev w) (rev (map rev us)) =  rev (map rev (gluer w us))"
  using assms by (induction us rule: hd_neq_induct)
    (simp_all add: gluer_nemp_def Let_def map_tl last_rev hd_map)

section \<open>Generators with glued element\<close>

text \<open>The following set will turn out to be the generating set of all words whose
 decomposition into a generating code does not end with w\<close>

inductive_set glued_gens :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
  for w G where
    other_gen: "g \<in> G \<Longrightarrow> g \<noteq> w \<Longrightarrow> g \<in> glued_gens w G"
  | glued [intro!]: "u \<in> glued_gens w G \<Longrightarrow>  w \<cdot> u \<in> glued_gens w G"

lemma in_glued_gensI: assumes "g \<in> G" "g \<noteq> w"
  shows "w \<^sup>@ k \<cdot> g = u \<Longrightarrow> u \<in> glued_gens w G"
  by (induction k arbitrary: u) (auto simp: other_gen[OF \<open>g \<in> G\<close> \<open>g \<noteq> w\<close>])

lemma in_glued_gensE:
  assumes "u \<in> glued_gens w G"
  obtains k g where "g \<in> G" and "g \<noteq> w" and "w \<^sup>@ k \<cdot> g = u"
using assms proof (induction)
  case (glued u)
    show ?case by (auto intro!: glued.IH[OF glued.prems[of _ "Suc _"]])
qed (use pow_zero in blast)

lemma glued_gens_alt_def: "glued_gens w C = {w \<^sup>@ k \<cdot> g | k g. g \<in> C \<and> g \<noteq> w}"
  by (blast elim!: in_glued_gensE intro: in_glued_gensI)

lemma glued_hull_sub_hull [simp, intro!]: "w \<in> G \<Longrightarrow> \<langle>glued_gens w G\<rangle> \<subseteq> \<langle>G\<rangle>"
  by (rule hull_mono') (auto elim!: in_glued_gensE)

lemma glued_hull_sub_hull': "w \<in> G \<Longrightarrow> u \<in> \<langle>glued_gens w G\<rangle> \<Longrightarrow> u \<in> \<langle>G\<rangle>"
  using set_mp[OF glued_hull_sub_hull].

lemma in_glued_hullE:
  assumes "w \<in> G" and "u \<in> \<langle>glued_gens w G\<rangle>"
  obtains us where "concat us = u" and "us \<in> lists G" and "us = \<epsilon> \<or> last us \<noteq> w"
using \<open>u \<in> \<langle>glued_gens w G\<rangle>\<close> proof (induction arbitrary: thesis)
  case (prod_cl v u)
    obtain k g where "g \<in> G" and "g \<noteq> w" and "concat ([w] \<^sup>@ k \<cdot> [g]) = v"
      using \<open>v \<in> glued_gens w G\<close> by simp (elim in_glued_gensE)
    obtain us where u: "concat us = u" and "us \<in> lists G" and "(us = \<epsilon> \<or> last us \<noteq> w)" by fact
    have "concat ([w] \<^sup>@ k \<cdot> [g] \<cdot> us) = v \<cdot> u"
      by (simp flip: \<open>concat ([w] \<^sup>@ k \<cdot> [g]) = v\<close> \<open>concat us = u\<close>)
    with \<open>(us = \<epsilon> \<or> last us \<noteq> w)\<close> show thesis
      by (elim prod_cl.prems, intro lists.intros
          append_in_lists pow_in_lists \<open>w \<in> G\<close> \<open>g \<in> G\<close> \<open>us \<in> lists G\<close>)
         (auto simp: \<open>g \<noteq> w\<close>)
qed (use concat.simps(1) in blast)

lemma glue_in_lists [simp, intro!]:
  assumes "us = \<epsilon> \<or> last us \<noteq> w"
  shows "us \<in> lists G \<Longrightarrow> glue w us \<in> lists (glued_gens w G)"
  using assms by (induction rule: last_neq_block_induct)
    (auto simp: glue_block_append intro: in_glued_gensI)

lemma concat_in_glued_hull[intro]:
  "us \<in> lists G \<Longrightarrow> us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> concat us \<in> \<langle>glued_gens w G\<rangle>"
  unfolding concat_glue[symmetric] by (intro concat_in_hull' glue_in_lists)

lemma glued_hull_conv: assumes "w \<in> G"
  shows "\<langle>glued_gens w G\<rangle> = {concat us | us. us \<in> lists G \<and> (us = \<epsilon> \<or> last us \<noteq> w)}"
  by (blast elim!: in_glued_hullE[OF \<open>w \<in> G\<close>])

section \<open>Bounded gluing\<close>

lemma bounded_glue_in_lists:
  assumes "us = \<epsilon> \<or> last us \<noteq> w" and "\<not> [w] \<^sup>@ n \<le>f us"
  shows "us \<in> lists G \<Longrightarrow> glue w us \<in> lists {w \<^sup>@ k \<cdot> g | k g. g \<in> G \<and> g \<noteq> w \<and> k < n}"
using assms proof (induction us rule: last_neq_block_induct)
  case (block k u us)
    have "k < n" and "\<not> [w] \<^sup>@ n \<le>f us"
      using \<open>\<not> [w] \<^sup>@ n \<le>f [w] \<^sup>@ k \<cdot> u # us\<close>
      by (blast intro!: not_le_imp_less le_exps_pref, blast intro!: fac_ext_pref fac_ext_hd)
    then show ?case
      using \<open>[w] \<^sup>@ k \<cdot> u # us \<in> lists G\<close> \<open>u \<noteq> w\<close> unfolding glue_block_append[OF \<open>u \<noteq> w\<close>]
      by (blast intro!: block.IH del: in_listsD in_listsI)
qed simp

subsection \<open>Gluing on binary alphabet\<close>

lemma bounded_bin_glue_in_lists: \<comment> \<open>meaning: a binary code\<close>
  assumes "us = \<epsilon> \<or> last us \<noteq> x"
      and "\<not> [x] \<^sup>@ n \<le>f us"
      and "us \<in> lists {x, y}"
  shows "glue x us \<in> lists {x \<^sup>@ k \<cdot> y | k. k < n}"
using bounded_glue_in_lists[OF assms] by blast

lemma single_bin_glue_in_lists: \<comment> \<open>meaning: a single occurrence\<close>
  assumes "us = \<epsilon> \<or> last us \<noteq> x"
      and "\<not> [x,x] \<le>f us"
      and "us \<in> lists {x, y}"
  shows "glue x us \<in> lists {x \<cdot> y, y}"
  using bounded_bin_glue_in_lists[of _ _ 2, simplified, OF assms] unfolding numeral_nat
  by (auto elim!: sub_lists_mono[rotated] less_SucE)

lemma count_list_single_bin_glue:
  assumes "x \<noteq> \<epsilon>" and "x \<noteq> y"
      and "us = \<epsilon> \<or> last us \<noteq> x"
      and "us \<in> lists {x,y}"
      and "\<not> [x,x] \<le>f us"
  shows "count_list (glue x us) (x \<cdot> y) = count_list us x"
    and "count_list (glue x us) y + count_list us x = count_list us y"
using assms(3-5) unfolding atomize_conj pow_Suc[symmetric]
proof (induction us rule: last_neq_block_induct)
  case (block k u us)
    have "u = y" using \<open>[x] \<^sup>@ k \<cdot> u # us \<in> lists {x, y}\<close> \<open>u \<noteq> x\<close> by simp
    have IH: "count_list (glue x us) (x \<cdot> y) = count_list us x \<and>
              count_list (glue x us) y + count_list us x = count_list us y"
      using block.prems by (intro block.IH) (simp, blast intro!: fac_ext_pref fac_ext_hd)
    have "\<not> [x] \<^sup>@ Suc (Suc 0) \<le>f [x] \<^sup>@ k \<cdot> u # us"
      using block.prems(2) by auto
    then have "k < Suc (Suc 0)"
      by (blast intro!: not_le_imp_less le_exps_pref)
    then show ?case unfolding \<open>u = y\<close> glue_block_append[OF \<open>x \<noteq> y\<close>[symmetric]]
      by (elim less_SucE less_zeroE) (simp_all add: \<open>x \<noteq> y\<close> \<open>x \<noteq> y\<close>[symmetric] \<open>x \<noteq> \<epsilon>\<close> IH)
qed simp

section \<open>Code with glued element\<close>

context code
begin

text \<open>If the original generating set is a code, then also the glued generators form a code\<close>

lemma glued_hull_last_dec: assumes "w \<in> \<C>" and  "u \<in> \<langle>glued_gens w \<C>\<rangle>" and "u \<noteq> \<epsilon>"
  shows "last (Dec \<C> u) \<noteq> w"
  using \<open>u \<in> \<langle>glued_gens w \<C>\<rangle>\<close>
  by (elim in_glued_hullE[OF \<open>w \<in> \<C>\<close>]) (auto simp: code_unique_dec \<open>u \<noteq> \<epsilon>\<close>)

lemma in_glued_hullI [intro]:
  assumes "u \<in> \<langle>\<C>\<rangle>" and "(u = \<epsilon> \<or> last (Dec \<C> u) \<noteq> w)"
  shows "u \<in> \<langle>glued_gens w \<C>\<rangle>"
  using concat_in_glued_hull[OF dec_in_lists[OF \<open>u \<in> \<langle>\<C>\<rangle>\<close>], of w]
  by (simp add: \<open>u \<in> \<langle>\<C>\<rangle>\<close> \<open>u = \<epsilon> \<or> last (Dec \<C> u) \<noteq> w\<close>)

lemma code_glued_hull_conv: assumes "w \<in> \<C>"
  shows "\<langle>glued_gens w \<C>\<rangle> = {u \<in> \<langle>\<C>\<rangle>. u = \<epsilon> \<or> last (Dec \<C> u) \<noteq> w}"
proof
  show "\<langle>glued_gens w \<C>\<rangle> \<subseteq> {u \<in> \<langle>\<C>\<rangle>. u = \<epsilon> \<or> last (Dec \<C> u) \<noteq> w}"
    using glued_hull_sub_hull'[OF \<open>w \<in> \<C>\<close>] glued_hull_last_dec[OF \<open>w \<in> \<C>\<close>] by blast
  show "{u \<in> \<langle>\<C>\<rangle>. u = \<epsilon> \<or> last (Dec \<C> u) \<noteq> w} \<subseteq> \<langle>glued_gens w \<C>\<rangle>"
    using in_glued_hullI by blast
qed

lemma in_glued_hull_iff:
  assumes "w \<in> \<C>" and "u \<in> \<langle>\<C>\<rangle>"
  shows "u \<in> \<langle>glued_gens w \<C>\<rangle> \<longleftrightarrow> u = \<epsilon> \<or> last (Dec \<C> u) \<noteq> w"
  by (simp add: \<open>w \<in> \<C>\<close> \<open>u \<in> \<langle>\<C>\<rangle>\<close> code_glued_hull_conv)

lemma glued_not_in_glued_hull: "w \<in> \<C> \<Longrightarrow> w \<notin> \<langle>glued_gens w \<C>\<rangle>"
  unfolding in_glued_hull_iff[OF _ gen_in] code_el_dec
  by (simp add: nemp)

lemma glued_gens_nemp: assumes "u \<in> glued_gens w \<C>" shows "u \<noteq> \<epsilon>"
  using assms by (induction) (auto simp add: nemp)

lemma glued_gens_code: assumes "w \<in> \<C>" shows "code (glued_gens w \<C>)"
proof
  show "us = vs" if "us \<in> lists (glued_gens w \<C>)" and "vs \<in> lists (glued_gens w \<C>)"
    and "concat us = concat vs" for us vs
  using that proof (induction rule: list_induct2')
    case (4 u us v vs)
      have *: "us \<in> lists (glued_gens w \<C>) \<Longrightarrow> us \<in> lists \<langle>\<C>\<rangle>" for us
        using sub_lists_mono[OF subset_trans[OF genset_sub glued_hull_sub_hull[OF \<open>w \<in> \<C>\<close>]]].
      obtain k u' l v'
        where "u' \<in> \<C>" "u' \<noteq> w" "w \<^sup>@ k \<cdot> u' = u"
          and "v' \<in> \<C>" "v' \<noteq> w" "w \<^sup>@ l \<cdot> v' = v"
        using "4.prems"(1-2) by simp (elim conjE in_glued_gensE)
      from this(3, 6) "4.prems" \<open>w \<in> \<C>\<close>
      have "concat (([w] \<^sup>@ k \<cdot> [u']) \<cdot> (Ref \<C> us)) = concat (([w] \<^sup>@ l \<cdot> [v']) \<cdot> (Ref \<C> vs))"
        by (simp add: concat_ref * lassoc)
      with \<open>w \<in> \<C>\<close> \<open>u' \<in> \<C>\<close> \<open>v' \<in> \<C>\<close> "4.prems"(1-2)
      have "[w] \<^sup>@ k \<cdot> [u'] \<bowtie> [w] \<^sup>@ l \<cdot> [v']"
        by (elim eqd_comp[OF is_code, rotated 2])
        (simp_all add: "*" pow_in_lists ref_in')
      with \<open>u' \<noteq> w\<close> \<open>v' \<noteq> w\<close> \<open>w \<^sup>@ k \<cdot> u' = u\<close> \<open>w \<^sup>@ l \<cdot> v' = v\<close>
      have "u = v"
        by (elim sing_pref_comp_mismatch[rotated 2, elim_format]) blast+
      then show "u # us = v # vs"
        using "4.IH" "4.prems"(1-3) by simp
  qed (auto dest!: glued_gens_nemp)
qed

text \<open>A crucial lemma showing the relation between gluing and the decomposition into generators\<close>

lemma dec_glued_gens: assumes "w \<in> \<C>" and "u \<in> \<langle>glued_gens w \<C>\<rangle>"
  shows "Dec (glued_gens w \<C>) u = glue w (Dec \<C> u)"
  using \<open>u \<in> \<langle>glued_gens w \<C>\<rangle>\<close> glued_hull_sub_hull'[OF \<open>w \<in> \<C>\<close> \<open>u \<in> \<langle>glued_gens w \<C>\<rangle>\<close>]
  by (intro code.code_unique_dec glued_gens_code)
     (simp_all add: in_glued_hull_iff \<open>w \<in> \<C>\<close>)

lemma ref_glue: "us = \<epsilon> \<or> last us \<noteq> w \<Longrightarrow> us \<in> lists \<C> \<Longrightarrow> Ref \<C> (glue w us) = us"
  by (intro refI glue_in_lists_hull) simp_all

end
theorem glued_code:
  assumes "code C" and "w \<in> C"
  shows "code {w \<^sup>@ k \<cdot> u |k u. u \<in> C \<and> u \<noteq> w}"
  using code.glued_gens_code[OF \<open>code C\<close> \<open>w \<in> C\<close>] unfolding glued_gens_alt_def.

section \<open>Gluing is primitivity preserving\<close>

text \<open>It is easy to obtain that gluing lists of code elements preserves primitivity.
We provide the result under weaker condition where glue blocks of the list
have unique concatenation.\<close>

lemma (in code) code_prim_glue:
  assumes last_neq: "us = \<epsilon> \<or> last us \<noteq> w"
      and "us \<in> lists \<C>"
  shows "primitive us \<Longrightarrow> primitive (glue w us)"
  using prim_map_prim[OF prim_concat_prim, of "decompose \<C>" "glue w us"]
  unfolding refine_def[symmetric] ref_glue[OF assms].

\<comment> \<open>In the context of code the inverse to the glue function is the @{const refine} function,
i.e. @{term "\<lambda>vs. concat (map (decompose \<C>) vs)"}, see @{thm code.ref_glue}.
The role of the @{const decompose} function outside the code context supply the 'unglue' function,
which maps glued blocks to its unique preimages (see below).\<close>

definition glue_block :: "'a list \<Rightarrow>'a list list \<Rightarrow> 'a list list \<Rightarrow> bool"
  where "glue_block w us bs =
    (\<exists>ps k u ss. (ps = \<epsilon> \<or> last ps \<noteq> w) \<and> u \<noteq> w \<and> ps \<cdot> [w] \<^sup>@ k \<cdot> u # ss = us \<and> [w] \<^sup>@ k \<cdot> [u] = bs)"

lemma glue_blockI [intro]:
  "ps = \<epsilon> \<or> last ps \<noteq> w \<Longrightarrow> u \<noteq> w \<Longrightarrow> ps \<cdot> [w] \<^sup>@ k \<cdot> u # ss = us \<Longrightarrow> [w] \<^sup>@ k \<cdot> [u] = bs
    \<Longrightarrow> glue_block w us bs"
  unfolding glue_block_def by (intro exI conjI)

lemma glue_blockE:
  assumes "glue_block w us bs"
  obtains ps k u ss where "ps = \<epsilon> \<or> last ps \<noteq> w" and "u \<noteq> w" "ps \<cdot> [w] \<^sup>@ k \<cdot> u # ss = us"
      and "[w] \<^sup>@ k \<cdot> [u] = bs"
  using assms unfolding glue_block_def by (elim exE conjE)

lemma assumes "glue_block w us bs"
  shows glue_block_of_appendL: "glue_block w (us \<cdot> vs) bs"
    and glue_block_of_appendR: "vs = \<epsilon> \<or> last vs \<noteq> w \<Longrightarrow> glue_block w (vs \<cdot> us) bs"
  using \<open>glue_block w us bs\<close> by (elim glue_blockE, use nothing in \<open>
    intro glue_blockI[of _ w _ _ "_ \<cdot> vs" "us \<cdot> vs" bs]
          glue_blockI[OF append_last_neq, of "vs"  w _ _ _ _ "vs \<cdot> us" bs],
    simp_all only: eq_commute[of _ us] rassoc append_Cons refl not_False_eq_True\<close>)+

lemma glue_block_of_block_append:
  "u \<noteq> w \<Longrightarrow> glue_block w us bs \<Longrightarrow> glue_block w ([w] \<^sup>@ k \<cdot> u # us) bs"
  by (simp only: hd_word[of _ us] lassoc) (elim glue_block_of_appendR, simp_all)

lemma in_set_glueE:
  assumes last_neq: "us = \<epsilon> \<or> last us \<noteq> w"
      and "b \<in> set (glue w us)"
  obtains bs where "glue_block w us bs" and "concat bs = b"
using assms proof (induction us rule: last_neq_block_induct)
  case (block k u us)
    show thesis using \<open>b \<in> set (glue w ([w] \<^sup>@ k \<cdot> u # us))\<close>
      proof (auto simp add: glue_block_append \<open>u \<noteq> w\<close>)
        show "b = w \<^sup>@ k \<cdot> u \<Longrightarrow> thesis"
          by (auto  intro!: block.prems(1) glue_blockI[OF _ \<open>u \<noteq> w\<close> _ refl])
        show "b \<in> set (glue w us) \<Longrightarrow> thesis"
          by (auto intro!: block.IH[OF block.prems(1)] glue_block_of_block_append \<open>u \<noteq> w\<close>)
      qed
qed simp

definition unglue :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where "unglue w us b = (THE bs. glue_block w us bs \<and> concat bs = b)"

lemma unglueI:
  assumes unique_blocks: "\<And>bs\<^sub>1 bs\<^sub>2. glue_block w us bs\<^sub>1 \<Longrightarrow> glue_block w us bs\<^sub>2
            \<Longrightarrow> concat bs\<^sub>1 = concat bs\<^sub>2 \<Longrightarrow> bs\<^sub>1 = bs\<^sub>2"
  shows "glue_block w us bs \<Longrightarrow> concat bs = b \<Longrightarrow> unglue w us b = bs"
  unfolding unglue_def by (blast intro: unique_blocks)

lemma concat_map_unglue_glue:
  assumes last_neq: "us = \<epsilon> \<or> last us \<noteq> w"
      and unique_blocks: "\<And>vs\<^sub>1 vs\<^sub>2. glue_block w us vs\<^sub>1 \<Longrightarrow> glue_block w us vs\<^sub>2
            \<Longrightarrow> concat vs\<^sub>1 = concat vs\<^sub>2 \<Longrightarrow> vs\<^sub>1 = vs\<^sub>2"
  shows "concat (map (unglue w us) (glue w us)) = us"
using assms proof (induction us rule: last_neq_block_induct)
  case (block k u us)
    have IH: "concat (map (unglue w us) (glue w us)) = us"
      using block.IH[OF block.prems] by (blast intro!: glue_block_of_block_append \<open>u \<noteq> w\<close>)
    have *: "map (unglue w ([w] \<^sup>@ k \<cdot> u # us)) (glue w us) = map (unglue w us) (glue w us)"
      by (auto simp only: map_eq_conv unglue_def del: the_equality
          elim!: in_set_glueE[OF \<open>us = \<epsilon> \<or> last us \<noteq> w\<close>], intro the_equality)
         (simp_all only: the_equality block.prems glue_block_of_block_append[OF \<open>u \<noteq> w\<close>])
    show "concat (map (unglue w ([w] \<^sup>@ k \<cdot> u # us)) (glue w ([w] \<^sup>@ k \<cdot> u # us))) = [w] \<^sup>@ k \<cdot> u # us"
      by (auto simp add: glue_block_append[OF \<open>u \<noteq> w\<close>] * IH
          intro!: unglueI intro: glue_blockI[OF _ \<open>u \<noteq> w\<close>] block.prems)
qed simp

lemma prim_glue:
  assumes last_neq: "us = \<epsilon> \<or> last us \<noteq> w"
      and unique_blocks: "\<And>bs\<^sub>1 bs\<^sub>2. glue_block w us bs\<^sub>1 \<Longrightarrow> glue_block w us bs\<^sub>2
            \<Longrightarrow> concat bs\<^sub>1 = concat bs\<^sub>2 \<Longrightarrow> bs\<^sub>1 = bs\<^sub>2"
  shows "primitive us \<Longrightarrow> primitive (glue w us)"
  using prim_map_prim[OF prim_concat_prim, of "unglue w us" "glue w us"]
  by (simp only: concat_map_unglue_glue assms)

subsection \<open>Gluing on binary alphabet\<close>

lemma bin_glue_blockE:
  assumes "us \<in> lists {x, y}"
      and "glue_block x us bs"
  obtains k where "[x] \<^sup>@ k \<cdot> [y] = bs"
  using assms by (auto simp only: glue_block_def del: in_listsD)

lemma unique_bin_glue_blocks:
  assumes "us \<in> lists {x, y}" and "x \<noteq> \<epsilon>"
  shows "glue_block x us bs\<^sub>1 \<Longrightarrow> glue_block x us bs\<^sub>2 \<Longrightarrow> concat bs\<^sub>1 = concat bs\<^sub>2 \<Longrightarrow> bs\<^sub>1 = bs\<^sub>2"
  by (auto simp: eq_pow_exp[OF \<open>x \<noteq> \<epsilon>\<close>] elim!: bin_glue_blockE[OF \<open>us \<in> lists {x, y}\<close>])

lemma prim_bin_glue:
  assumes "us \<in> lists {x, y}" and "x \<noteq> \<epsilon>"
      and "us = \<epsilon> \<or> last us \<noteq> x"
  shows "primitive us \<Longrightarrow> primitive (glue x us)"
  using prim_glue[OF \<open>us = \<epsilon> \<or> last us \<noteq> x\<close> unique_bin_glue_blocks[OF assms(1-2)]].

end
