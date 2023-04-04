subsection \<open>Safety and Hoare Triples\<close>

theory Safety
  imports Guards
begin

subsubsection \<open>Preliminaries\<close>

(* Enforces no-guard *)
definition sat_inv :: "store \<Rightarrow> ('i, 'a) heap \<Rightarrow> ('i, 'a, nat) single_context \<Rightarrow> bool" where
  "sat_inv s hj \<Gamma> \<longleftrightarrow> (s, hj), (s, hj) \<Turnstile> invariant \<Gamma> \<and> no_guard hj"

lemma sat_invI:
  assumes "(s, hj), (s, hj) \<Turnstile> invariant \<Gamma>"
      and "no_guard hj"
    shows "sat_inv s hj \<Gamma>"
  by (simp add: assms(1) assms(2) sat_inv_def)


text \<open>s and s' can differ on variables outside of vars, does not change anything.
upper-fvs S vars means that vars is an upper-bound of "fv S"\<close>

definition upper_fvs :: "(store \<times> ('i, 'a) heap) set \<Rightarrow> var set \<Rightarrow> bool" where
  "upper_fvs S vars \<longleftrightarrow> (\<forall>s s' h. (s, h) \<in> S \<and> agrees vars s s' \<longrightarrow> (s', h) \<in> S)"

text \<open>Only need to agree on vars\<close>
definition upperize where
  "upperize S vars = { \<sigma>' |\<sigma> \<sigma>'. \<sigma> \<in> S \<and> snd \<sigma> = snd \<sigma>' \<and> agrees vars (fst \<sigma>) (fst \<sigma>')}"

definition close_var where
  "close_var S x = { ((fst \<sigma>)(x := v), snd \<sigma>) |\<sigma> v. \<sigma> \<in> S  }"

lemma upper_fvsI:
  assumes "\<And>s s' h. (s, h) \<in> S \<and> agrees vars s s' \<Longrightarrow> (s', h) \<in> S"
  shows "upper_fvs S vars"
  using assms upper_fvs_def by blast

lemma pair_sat_comm:
  assumes "pair_sat S S' A"
  shows "pair_sat S' S A"
proof (rule pair_satI)
  fix s h s' h' assume "(s, h) \<in> S' \<and> (s', h') \<in> S"
  then show "(s, h), (s', h') \<Turnstile> A"
    using assms pair_sat_def sat_comm by blast
qed

lemma in_upperize:
  "(s', h) \<in> upperize S vars \<longleftrightarrow> (\<exists>s. (s, h) \<in> S \<and> agrees vars s s')" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (simp add: upperize_def)
  show "?B \<Longrightarrow> ?A"
    using upperize_def by fastforce
qed

lemma upper_fvs_upperize:
  "upper_fvs (upperize S vars) vars"
proof (rule upper_fvsI)
  fix s s' h
  assume "(s, h) \<in> upperize S vars \<and> agrees vars s s'"
  then obtain s'' where "(s'', h) \<in> S \<and> agrees vars s'' s"
    by (meson in_upperize)
  then have "agrees vars s'' s'"
    using \<open>(s, h) \<in> upperize S vars \<and> agrees vars s s'\<close> agrees_def[of vars s s']
    agrees_def[of vars s'' s] agrees_def[of vars s'' s']
    by simp
  then show "(s', h) \<in> upperize S vars"
    using \<open>(s'', h) \<in> S \<and> agrees vars s'' s\<close> upperize_def by fastforce
qed

lemma upperize_larger:
  "S \<subseteq> upperize S vars"
proof
  fix x assume "x \<in> S"
  moreover have "agrees vars (fst x) (fst x)"
    using agrees_def by blast
  ultimately show "x \<in> upperize S vars"
    by (metis (mono_tags, lifting) CollectI upperize_def)
qed

lemma pair_sat_upperize:
  assumes "pair_sat S S' A"
  shows "pair_sat (upperize S (fvA A)) S' A"
proof (rule pair_satI)
  fix s h s' h'
  assume asm0: "(s, h) \<in> upperize S (fvA A) \<and> (s', h') \<in> S'"
  then obtain s'' where "agrees (fvA A) s s''" "(s'', h) \<in> S"
    using agrees_def[of "fvA A" s s'] in_upperize[of s h S "fvA A"]
    by (metis agrees_def)
  then show "(s, h), (s', h') \<Turnstile> A"
    using agrees_same asm0 assms pair_sat_def by blast
qed

lemma in_close_var:
  "(s', h) \<in> close_var S x \<longleftrightarrow> (\<exists>s v. (s, h) \<in> S \<and> s' = s(x := v))" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    using close_var_def[of S x] mem_Collect_eq prod.inject surjective_pairing
    by auto
  show "?B \<Longrightarrow> ?A"
    using close_var_def by fastforce
qed

lemma pair_sat_close_var:
  assumes "x \<notin> fvA A"
      and "pair_sat S S' A"
  shows "pair_sat (close_var S x) S' A"
proof (rule pair_satI)
  fix s h s' h'
  assume "(s, h) \<in> close_var S x \<and> (s', h') \<in> S'"
  then show "(s, h), (s', h') \<Turnstile> A"
    by (metis (no_types, lifting) agrees_same agrees_update assms in_close_var pair_sat_def)
qed

lemma pair_sat_close_var_double:
  assumes "pair_sat S S' A"
      and "x \<notin> fvA A"
  shows "pair_sat (close_var S x) (close_var S' x) A"
  using assms pair_sat_close_var pair_sat_comm by blast

lemma close_var_subset:
  "S \<subseteq> close_var S x"
proof
  fix y assume "y \<in> S"
  then have "fst y = (fst y)(x := (fst y x))"
    by simp
  then show "y \<in> close_var S x"
    by (metis \<open>y \<in> S\<close> in_close_var prod.exhaust_sel)
qed

lemma upper_fvs_close_vars:
  "upper_fvs (close_var S x) (- {x})"
proof (rule upper_fvsI)
  fix s s' h
  assume "(s, h) \<in> close_var S x \<and> agrees (- {x}) s s'"
  have "s(x := s' x) = s'"
  proof (rule ext)
    fix y show "(s(x := s' x)) y = s' y"
      by (metis (mono_tags, lifting) ComplI \<open>(s, h) \<in> close_var S x \<and> agrees (- {x}) s s'\<close> agrees_def fun_upd_apply singleton_iff)
  qed
  then show "(s', h) \<in> close_var S x"
    by (metis \<open>(s, h) \<in> close_var S x \<and> agrees (- {x}) s s'\<close> fun_upd_upd in_close_var)
qed

lemma sat_inv_agrees:
  assumes "sat_inv s hj \<Gamma>"
      and "agrees (fvA (invariant \<Gamma>)) s s'"
    shows "sat_inv s' hj \<Gamma>"
  by (meson agrees_same assms sat_comm sat_inv_def)

lemma abort_iff_fvC:
  assumes "agrees (fvC C) s s'"
  shows "aborts C (s, h) \<longleftrightarrow> aborts C (s', h)"
  using aborts_agrees assms fst_conv snd_eqD
  by (metis (mono_tags, lifting) agrees_def)

lemma view_function_of_invE:
  assumes "view_function_of_inv \<Gamma>"
      and "sat_inv s h \<Gamma>"
      and "(h' :: ('i, 'a) heap) \<succeq> h"
    shows "view \<Gamma> (normalize (get_fh h)) = view \<Gamma> (normalize (get_fh h'))"
  using assms(1) assms(2) assms(3) sat_inv_def view_function_of_inv_def by blast



subsubsection Safety

fun no_abort :: "('i, 'a, nat) cont \<Rightarrow> cmd \<Rightarrow> store \<Rightarrow> ('i, 'a) heap \<Rightarrow> bool" where
  "no_abort None C s h \<longleftrightarrow> (\<forall>hf H. Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H
  \<longrightarrow> \<not> aborts C (s, normalize (get_fh H)))"
| "no_abort (Some \<Gamma>) C s h \<longleftrightarrow> (\<forall>hf H hj v0. Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and>
  semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>
  \<longrightarrow> \<not> aborts C (s, normalize (get_fh H)))"

lemma no_abortI:
  assumes "\<And>(hf :: ('i, 'a) heap) (H :: ('i, 'a) heap). Some H = Some h \<oplus> Some hf \<and> \<Delta> = None \<and> full_ownership (get_fh H) \<and> no_guard H \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
      and "\<And>H hf hj v0 \<Gamma>. \<Delta> = Some \<Gamma> \<and> Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>
  \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
    shows "no_abort \<Delta> C s (h :: ('i, 'a) heap)"
  apply (cases \<Delta>)
  using assms(1) no_abort.simps(1) apply blast
  using assms(2) no_abort.simps(2) by blast

lemma no_abortSomeI:
  assumes "\<And>H hf hj v0. Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>
  \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
  shows "no_abort (Some \<Gamma>) C s (h :: ('i, 'a) heap)"
  using assms no_abort.simps(2) by blast

lemma no_abortNoneI:
  assumes "\<And>(hf :: ('i, 'a) heap) (H :: ('i, 'a) heap). Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
  shows "no_abort (None :: ('i, 'a, nat) cont) C s (h :: ('i, 'a) heap)"
  using assms no_abort.simps(1) by blast

lemma no_abortE:
  assumes "no_abort \<Delta> C s h"
  shows "Some H = Some h \<oplus> Some hf \<Longrightarrow> \<Delta> = None \<Longrightarrow> full_ownership (get_fh H) \<Longrightarrow> no_guard H \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
    and "\<Delta> = Some \<Gamma> \<Longrightarrow> Some H = Some h \<oplus> Some hj \<oplus> Some hf \<Longrightarrow> sat_inv s hj \<Gamma> \<Longrightarrow> full_ownership (get_fh H) \<Longrightarrow> semi_consistent \<Gamma> v0 H
  \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
  using assms no_abort.simps(1) apply blast
  by (metis assms no_abort.simps(2))

fun safe :: "nat \<Rightarrow> ('i, 'a, nat) cont \<Rightarrow> cmd \<Rightarrow> (store \<times> ('i, 'a) heap) \<Rightarrow> (store \<times> ('i, 'a) heap) set \<Rightarrow> bool" where
  "safe 0 _ _ _ _ \<longleftrightarrow> True"

| "safe (Suc n) None C (s, h) S \<longleftrightarrow> (C = Cskip \<longrightarrow> (s, h) \<in> S) \<and> no_abort (None :: ('i, 'a, nat) cont)  C s h \<and>
(\<forall>H hf C' s' h'. Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H
 \<and> red C (s, normalize (get_fh H)) C' (s', h')
\<longrightarrow> (\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S))"

| "safe (Suc n) (Some \<Gamma>) C (s, h) S \<longleftrightarrow> (C = Cskip \<longrightarrow> (s, h) \<in> S) \<and> no_abort (Some \<Gamma>) C s h \<and>
(\<forall>H hf C' s' h' hj v0. Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>
 \<and> red C (s, normalize (get_fh H)) C' (s', h')
\<longrightarrow> (\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma>
 \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S))"

lemma safeNoneI:
  assumes "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "no_abort None C s h"
      and "\<And>H hf C' s' h'. Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, normalize (get_fh H)) C' (s', h')
  \<Longrightarrow> (\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S)"
shows "safe (Suc n) (None :: ('i, 'a, nat) cont) C (s, h :: ('i, 'a) heap) S"
  using assms by auto

lemma safeSomeI:
  assumes "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "no_abort (Some \<Gamma>) C s h"
      and "\<And>H hf C' s' h' hj v0. Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H)
        \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red C (s, normalize (get_fh H)) C' (s', h')
\<Longrightarrow> (\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma>
 \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S)"
shows "safe (Suc n) (Some \<Gamma>) C (s, h :: ('i, 'a) heap) S"
  using assms by auto

lemma safeI:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "no_abort \<Delta> C s h"
      and "\<And>H hf C' s' h'. \<Delta> = None \<Longrightarrow> Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, normalize (get_fh H)) C' (s', h')
  \<Longrightarrow> (\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S)"
      and "\<And>H hf C' s' h' hj v0 \<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H)
        \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red C (s, normalize (get_fh H)) C' (s', h')
\<Longrightarrow> (\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma>
 \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S)"
    shows "safe (Suc n) \<Delta> C (s, h :: ('i, 'a) heap) S"
proof (cases \<Delta>)
  case None
  then show ?thesis
    using assms(1) assms(2) assms(3) by auto
next
  case (Some \<Gamma>)
  then show ?thesis using safeSomeI assms(1) assms(2) assms(4)
    by simp
qed


lemma safeSomeAltI:
  assumes "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "\<And>H hf hj v0. Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>
  \<Longrightarrow> \<not> aborts C (s, normalize (get_fh H))"
      and "\<And>H hf C' s' h' hj v0. Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H)
        \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<Longrightarrow> red C (s, normalize (get_fh H)) C' (s', h')
\<Longrightarrow> (\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma>
 \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S)"
    shows "safe (Suc n) (Some \<Gamma>) C (s, h :: ('i, 'a) heap) S"
  using assms(1)
proof (rule safeSomeI)
  show "no_abort (Some \<Gamma>) C s h" using assms(2) no_abortSomeI by blast
  show "\<And>H hf C' s' h' hj v0.
       Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h') \<Longrightarrow>
       (\<exists>h'' H' hj'.
           full_ownership (get_fh H') \<and>
           semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S)"
    using assms(3) by blast
qed (simp)


lemma safeSomeE:
  assumes "safe (Suc n) (Some \<Gamma>) C (s, h :: ('i, 'a) heap) S"
  shows "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "no_abort (Some \<Gamma>) C s h"
      and "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<Longrightarrow> full_ownership (get_fh H)
        \<Longrightarrow> semi_consistent \<Gamma> v0 H \<Longrightarrow> sat_inv s hj \<Gamma> \<Longrightarrow> red C (s, normalize (get_fh H)) C' (s', h')
\<Longrightarrow> (\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma>
 \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S)"
  using assms safe.simps(3)[of n \<Gamma> C s h S] by blast+

lemma safeNoneE:
  assumes "safe (Suc n) (None :: ('i, 'a, nat) cont) C (s, h :: ('i, 'a) heap) S"
    shows "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "no_abort (None :: ('i, 'a, nat) cont) C s h"
      and "Some H = Some h \<oplus> Some hf \<Longrightarrow> full_ownership (get_fh H) \<Longrightarrow> no_guard H \<Longrightarrow> red C (s, normalize (get_fh H)) C' (s', h')
  \<Longrightarrow> (\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S)"
  using assms safe.simps(2)[of n C s h S] by blast+

lemma safeNoneE_bis:
  fixes no_cont :: "('i, 'a, nat) cont"
  assumes "safe (Suc n) no_cont C (s, h :: ('i, 'a) heap) S"
      and "no_cont = None"
    shows "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      and "no_abort no_cont C s h"
      and "Some H = Some h \<oplus> Some hf \<Longrightarrow> full_ownership (get_fh H) \<Longrightarrow> no_guard H \<Longrightarrow> red C (s, normalize (get_fh H)) C' (s', h')
  \<Longrightarrow> (\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n no_cont C' (s', h'') S)"
  using assms safe.simps(2)[of n C s h S] by blast+


subsubsection \<open>Useful results about safety\<close>


lemma no_abort_larger:
  assumes "h' \<succeq> h"
    and "no_abort \<Gamma> C s h"
  shows "no_abort \<Gamma> C s h'"
proof (rule no_abortI)
  show "\<And>hf H. Some H = Some h' \<oplus> Some hf \<and> \<Gamma> = None \<and> full_ownership (get_fh H) \<and> no_guard H \<Longrightarrow> \<not> aborts C (s, FractionalHeap.normalize (get_fh H))"
    using assms(1) assms(2) larger_def larger_trans no_abort.simps(1) by blast
  show "\<And>H hf hj v0 \<Gamma>'.
       \<Gamma> = Some \<Gamma>' \<and> Some H = Some h' \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma>' v0 H \<and> sat_inv s hj \<Gamma>' \<Longrightarrow>
       \<not> aborts C (s, FractionalHeap.normalize (get_fh H))"
  proof -
    fix H hf hj v0 \<Gamma>'
    assume asm0: "\<Gamma> = Some \<Gamma>' \<and> Some H = Some h' \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma>' v0 H \<and> sat_inv s hj \<Gamma>'"
    moreover obtain r where "Some h' = Some h \<oplus> Some r"
      using assms(1) larger_def by blast
    then obtain hf' where "Some hf' = Some hf \<oplus> Some r"
      by (metis (no_types, opaque_lifting) calculation not_None_eq plus.simps(1) plus_asso plus_comm)
    then have "Some H = Some h \<oplus> Some hj \<oplus> Some hf'"
      by (metis (no_types, opaque_lifting) \<open>Some h' = Some h \<oplus> Some r\<close> calculation plus_asso plus_comm)
    then show "\<not> aborts C (s, FractionalHeap.normalize (get_fh H))"
      using assms(2) calculation no_abortE(2) by blast
  qed
qed

lemma safe_larger_set_aux:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "safe n \<Delta> C (s, h) S"
      and "S \<subseteq> S'"
    shows "safe n \<Delta> C (s, h) S'"
  using assms
proof (induct n arbitrary: s h C)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (s, h) \<in> S'"
      by (metis (no_types, opaque_lifting) Suc.prems(1) assms(2) not_Some_eq safeNoneE_bis(1) safeSomeE(1) subset_iff)
    show "no_abort \<Delta> C s h"
      apply (cases \<Delta>)
      using Suc.prems(1) safeNoneE_bis(2) apply blast
      using Suc.prems(1) safeSomeE(2) by blast

    show "\<And>H hf C' s' h'.
       \<Delta> = None \<Longrightarrow>
       Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h') \<Longrightarrow>
       \<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S'"
      using Suc.hyps Suc.prems(1) assms(2) safeNoneE(3)[of n C s h] by blast

    show "\<And>H hf C' s' h' hj v0 \<Gamma>.
       \<Delta> = Some \<Gamma> \<Longrightarrow>
       Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h') \<Longrightarrow>
       \<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S'"
    proof -
      fix H hf C' s' h' hj v0 \<Gamma>
      assume asm0: "\<Delta> = Some \<Gamma>" "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
      then show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma>
      \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S'"
        using safeSomeE(3)[of n \<Gamma> C s h S] Suc.hyps Suc.prems(1) assms(2) by blast
    qed
  qed
qed (simp)

lemma safe_larger_set:
  assumes "safe n \<Delta> C \<sigma> S"
      and "S \<subseteq> S'"
    shows "safe n \<Delta> C \<sigma> S'"
  using assms safe_larger_set_aux[of n \<Delta> C "fst \<sigma>" "snd \<sigma>" S S']
  by auto

lemma safe_smaller_aux:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "m \<le> n"
      and "safe n \<Delta> C (s, h) S"
    shows "safe m \<Delta> C (s, h) S"
  using assms
proof (induct n arbitrary: s h C m)
  case (Suc n)
  show ?case
  proof (cases m)
    case (Suc k)
    then have "k \<le> n"
      using Suc.prems(1) by fastforce
    moreover have "safe (Suc k) \<Delta> C (s, h) S"
    proof (rule safeI)
      show "C = Cskip \<Longrightarrow> (s, h) \<in> S"
        using Suc.prems(2) safe.elims(2) by blast
      show "no_abort \<Delta> C s h"
        apply (cases \<Delta>)
        using Suc.prems(2) safeNoneE(2) apply blast
        using Suc.prems(2) safeSomeE(2) by blast
      show "\<And>H hf C' s' h'.
       \<Delta> = None \<Longrightarrow>
       Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h') \<Longrightarrow>
       \<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe k (None :: ('i, 'a, nat) cont) C' (s', h'') S"
      proof -
        fix H hf C' s' h'
        assume asm0: "\<Delta> = None" "Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        then obtain h'' H' where "full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S"
          using Suc.prems(2) safeNoneE(3) by blast
        then show "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe k (None :: ('i, 'a, nat) cont) C' (s', h'') S"
          using Suc.hyps asm0(1) calculation by blast
      qed
      fix H hf C' s' h' hj v0 \<Gamma>
      assume asm0: "\<Delta> = Some \<Gamma>" "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
      then show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe k (Some \<Gamma>) C' (s', h'') S"
        using Suc.prems(2) safeSomeE(3)[of n \<Gamma> C s h S H hj hf v0 C' s' h'] Suc.hyps
        using calculation by blast
    qed
    ultimately show ?thesis
      using Suc by auto
  qed (simp)
qed (simp)

lemma safe_smaller:
  assumes "m \<le> n"
      and "safe n \<Delta> C \<sigma> S"
    shows "safe m \<Delta> C \<sigma> S"
  by (metis assms(1) assms(2) safe_smaller_aux surj_pair)

lemma safe_free_vars_aux:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "safe n \<Delta> C (s0, h) S"
      and "agrees (fvC C \<union> vars) s0 s1"
      and "upper_fvs S vars"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> agrees (fvA (invariant \<Gamma>)) s0 s1"
    shows "safe n \<Delta> C (s1, h) S"
  using assms
proof (induct n arbitrary: s0 h s1 C)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (s1, h) \<in> S"
      by (metis Suc.prems(1) Suc.prems(2) agrees_union assms(3) not_Some_eq safeNoneE_bis(1) safeSomeE(1) upper_fvs_def)
    show "no_abort \<Delta> C s1 h"
    proof (rule no_abortI)
      show "\<And>hf H. Some H = Some h \<oplus> Some hf \<and> \<Delta> = None \<and> full_ownership (get_fh H) \<and> no_guard H \<Longrightarrow> \<not> aborts C (s1, FractionalHeap.normalize (get_fh H))"
        using Suc.prems(1) Suc.prems(2) abort_iff_fvC agrees_union no_abortE(1) safeNoneE(2) by blast
      show "\<And>H hf hj v0 \<Gamma>. \<Delta> = Some \<Gamma> \<and> Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s1 hj \<Gamma> \<Longrightarrow>
       \<not> aborts C (s1, FractionalHeap.normalize (get_fh H))"
      proof -
        fix H hf hj v0 \<Gamma>
        assume asm0: "\<Delta> = Some \<Gamma> \<and> Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s1 hj \<Gamma>"
        then have "sat_inv s0 hj \<Gamma>"
          using Suc.prems(4) agrees_def sat_inv_agrees
          by (metis (mono_tags, opaque_lifting))
        then have "\<not> aborts C (s0, FractionalHeap.normalize (get_fh H))"
          using Suc.prems(1) asm0 no_abort.simps(2) safeSomeE(2) by blast
        then show "\<not> aborts C (s1, FractionalHeap.normalize (get_fh H))"
          using Suc.prems(2) abort_iff_fvC agrees_union by blast
      qed
    qed
    show "\<And>H hf C' s1' h'.
       \<Delta> = None \<Longrightarrow>
       Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s1, FractionalHeap.normalize (get_fh H)) C' (s1', h') \<Longrightarrow>
       \<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s1', h'') S"
    proof -
      fix H hf C' s1' h'
      assume asm0: "\<Delta> = None"
        "Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s1, FractionalHeap.normalize (get_fh H)) C' (s1', h')"
      then obtain s0' where "red C (s0, FractionalHeap.normalize (get_fh H)) C' (s0', h')" "agrees (fvC C \<union> vars) s1' s0'"
        using red_agrees[of C "(s1, FractionalHeap.normalize (get_fh H))" C' "(s1', h')" "fvC C \<union> vars"]
        using Suc.prems(2) agrees_def fst_conv snd_conv sup_ge1
        by (metis (mono_tags, lifting))
      then obtain h'' H' where
        r: "full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s0', h'') S"
        using Suc.prems(1) asm0(1) asm0(2) safeNoneE(3) by blast
      then have "safe n (None :: ('i, 'a, nat) cont) C' (s1', h'') S"
        using Suc.hyps[of C'  s0' h'' s1']
        using \<open>agrees (fvC C \<union> vars) s1' s0'\<close> agrees_union asm0(1) asm0(2) assms(3) option.distinct(1) red_properties(1)
        by (metis (mono_tags, lifting) agrees_def subset_iff)
      then show "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s1', h'') S"
        using r by blast
    qed
    fix H hf C' s1' h' hj v0 \<Gamma>
    assume asm0: "\<Delta> = Some \<Gamma>"
      "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s1 hj \<Gamma> \<and> red C (s1, normalize (get_fh H)) C' (s1', h')"
    then obtain s0' where "red C (s0, FractionalHeap.normalize (get_fh H)) C' (s0', h')" "agrees (fvC C \<union> vars \<union> fvA (invariant \<Gamma>)) s1' s0'"
      using red_agrees[of C "(s1, FractionalHeap.normalize (get_fh H))" C' "(s1', h')" "fvC C \<union> vars \<union> fvA (invariant \<Gamma>)"]
      using Suc.prems(2) Suc.prems(4) agrees_comm agrees_union fst_conv snd_conv sup_assoc sup_ge1
      by (metis (no_types, lifting))
    moreover have "sat_inv s0 hj \<Gamma>"
      using Suc.prems(4) agrees_comm asm0(1) asm0(2) sat_inv_agrees by blast
    ultimately obtain h'' H' hj' where r: "full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s0' hj' \<Gamma>
  \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s0', h'') S"
      using Suc.prems(1) asm0(1) asm0(2) safeSomeE(3)[of n \<Gamma> C s0 h S H hj hf]
      by blast
    then have "sat_inv s1' hj' \<Gamma>"
      using \<open>agrees (fvC C \<union> vars \<union> fvA (invariant \<Gamma>)) s1' s0'\<close> agrees_comm agrees_union sat_inv_agrees by blast
    moreover have "safe n (Some \<Gamma>) C' (s1', h'') S"
      using Suc.hyps[of C' s0' h'' s1'] \<open>agrees (fvC C \<union> vars \<union> fvA (invariant \<Gamma>)) s1' s0'\<close> \<open>red C (s0, FractionalHeap.normalize (get_fh H)) C' (s0', h')\<close>
        agrees_def agrees_union asm0(1) assms(3) option.inject r red_properties
      by (metis (mono_tags, lifting) subset_Un_eq)
    ultimately show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv s1' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s1', h'') S"
      using r by blast
  qed
qed (simp)


lemma safe_free_vars_None:
  assumes "safe n (None :: ('i, 'a, nat) cont) C (s, h) S"
      and "agrees (fvC C \<union> vars) s s'"
      and "upper_fvs S vars"
    shows "safe n (None :: ('i, 'a, nat) cont) C (s', h) S"
  by (meson assms(1) assms(2) assms(3) not_Some_eq safe_free_vars_aux)

lemma safe_free_vars_Some:
  assumes "safe n (Some \<Gamma>) C (s, h) S"
      and "agrees (fvC C \<union> vars \<union> fvA (invariant \<Gamma>)) s s'"
      and "upper_fvs S vars"
    shows "safe n (Some \<Gamma>) C (s', h) S"
  by (metis agrees_union assms(1) assms(2) assms(3) option.inject safe_free_vars_aux)

lemma safe_free_vars:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "safe n \<Delta> C (s, h) S"
      and "agrees (fvC C \<union> vars) s s'"
      and "upper_fvs S vars"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> agrees (fvA (invariant \<Gamma>)) s s'"
    shows "safe n \<Delta> C (s', h) S"
proof (cases \<Delta>)
  case None
  then show ?thesis
    using assms(1) assms(2) assms(3) safe_free_vars_None by blast
next
  case (Some \<Gamma>)
  then show ?thesis
    using agrees_union assms(1) assms(2) assms(3) assms(4) safe_free_vars_Some by blast
qed



subsubsection \<open>Hoare triples\<close>

definition hoare_triple_valid :: "('i, 'a, nat) cont \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> cmd \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> bool"
  ("_ \<Turnstile> {_} _ {_}" [51,0,0] 81) where
  "hoare_triple_valid \<Gamma> P C Q \<longleftrightarrow> (\<exists>\<Sigma>. (\<forall>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<longrightarrow> safe n \<Gamma> C \<sigma> (\<Sigma> \<sigma>)) \<and>
  (\<forall>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q))"

lemma hoare_triple_validI:
  assumes "\<And>s h n. (s, h), (s, h) \<Turnstile> P \<Longrightarrow> safe n \<Gamma> C (s, h) (\<Sigma> (s, h))"
      and "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma> (s, h)) (\<Sigma> (s', h')) Q"
    shows "hoare_triple_valid \<Gamma> P C Q"
  by (metis assms(1) assms(2) hoare_triple_valid_def prod.collapse)

lemma hoare_triple_valid_smallerI:
  assumes "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n \<Gamma> C \<sigma> (\<Sigma> \<sigma>)"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q"
    shows "hoare_triple_valid \<Gamma> P C Q"
  using assms hoare_triple_valid_def by metis

lemma hoare_triple_validE:
  assumes "hoare_triple_valid \<Gamma> P C Q"
  shows "\<exists>\<Sigma>.(\<forall>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<longrightarrow> safe n \<Gamma> C \<sigma> (\<Sigma> \<sigma>)) \<and>
  (\<forall>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q)"
  using assms hoare_triple_valid_def by blast

lemma hoare_triple_valid_simplerE:
  assumes "hoare_triple_valid \<Gamma> P C Q"
      and "\<sigma>, \<sigma>' \<Turnstile> P"
    shows "\<exists>S S'. safe n \<Gamma> C \<sigma> S \<and> safe n \<Gamma> C \<sigma>' S' \<and> pair_sat S S' Q"
  by (meson always_sat_refl assms(1) assms(2) hoare_triple_validE sat_comm)


end