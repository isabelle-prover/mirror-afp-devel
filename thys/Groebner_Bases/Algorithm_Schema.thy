(* Author: Alexander Maletzky *)

section \<open>A General Algorithm Schema for Computing Gr\"obner Bases\<close>

theory Algorithm_Schema
  imports General Groebner_Bases
begin

text \<open>This theory formalizes a general algorithm schema for computing Gr\"obner bases, generalizing
  Buchberger's original critical-pair/completion algorithm. The algorithm schema depends on several
  functional parameters that can be instantiated by a variety of concrete functions. Possible instances
  yield Buchberger's algorithm, Faug\`ere's F4 algorithm, and (as it seems) even his F5
  algorithm.\<close>

subsection \<open>@{term processed}\<close>

definition processed :: "('a \<times> 'a) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"
  where "processed p xs ps \<longleftrightarrow> fst p \<in> set xs \<and> snd p \<in> set xs \<and> p \<notin> set ps \<and> (snd p, fst p) \<notin> set ps"

lemma processed_alt:
  "processed (a, b) xs ps \<longleftrightarrow> ((a \<in> set xs) \<and> (b \<in> set xs) \<and> (a, b) \<notin> set ps \<and> (b, a) \<notin> set ps)"
  unfolding processed_def by auto

lemma processedI:
  assumes "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin> set ps" and "(b, a) \<notin> set ps"
  shows "processed (a, b) xs ps"
  unfolding processed_alt using assms by simp

lemma processedD1:
  assumes "processed (a, b) xs ps"
  shows "a \<in> set xs"
  using assms by (simp add: processed_alt)

lemma processedD2:
  assumes "processed (a, b) xs ps"
  shows "b \<in> set xs"
  using assms by (simp add: processed_alt)

lemma processedD3:
  assumes "processed (a, b) xs ps"
  shows "(a, b) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processedD4:
  assumes "processed (a, b) xs ps"
  shows "(b, a) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processed_Nil: "processed (a, b) xs [] \<longleftrightarrow> (a \<in> set xs \<and> b \<in> set xs)"
  by (simp add: processed_alt)

lemma processed_Cons:
  assumes "processed (a, b) xs ps"
    and a1: "a = p \<Longrightarrow> b = q \<Longrightarrow> thesis"
    and a2: "a = q \<Longrightarrow> b = p \<Longrightarrow> thesis"
    and a3: "processed (a, b) xs ((p, q) # ps) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin> set ps" and "(b, a) \<notin> set ps"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(a, b) = (p, q)")
    case True
    hence "a = p" and "b = q" by simp_all
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(a, b) \<notin> set ps\<close> have *: "(a, b) \<notin> set ((p, q) # ps)" by auto
    show ?thesis
    proof (cases "(b, a) = (p, q)")
      case True
      hence "a = q" and "b = p" by simp_all
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(b, a) \<notin> set ps\<close> have "(b, a) \<notin> set ((p, q) # ps)" by auto
      with \<open>a \<in> set xs\<close> \<open>b \<in> set xs\<close> * have "processed (a, b) xs ((p, q) # ps)"
        by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

lemma processed_minus:
  assumes "processed (a, b) xs (ps -- qs)"
    and a1: "(a, b) \<in> set qs \<Longrightarrow> thesis"
    and a2: "(b, a) \<in> set qs \<Longrightarrow> thesis"
    and a3: "processed (a, b) xs ps \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin> set (ps -- qs)"
    and "(b, a) \<notin> set (ps -- qs)"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(a, b) \<in> set qs")
    case True
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(a, b) \<notin> set (ps -- qs)\<close> have *: "(a, b) \<notin> set ps" by (auto simp add: set_diff_list)
    show ?thesis
    proof (cases "(b, a) \<in> set qs")
      case True
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(b, a) \<notin> set (ps -- qs)\<close> have "(b, a) \<notin> set ps" by (auto simp add: set_diff_list)
      with \<open>a \<in> set xs\<close> \<open>b \<in> set xs\<close> * have "processed (a, b) xs ps"
        by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

subsection \<open>Algorithm Schema\<close>

subsubsection \<open>@{term is_nonzero_const_monomial}\<close>

context comm_powerprod
begin

definition is_nonzero_const_monomial :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool"
  where "is_nonzero_const_monomial p \<longleftrightarrow> (\<exists>c. c \<noteq> 0 \<and> p = monomial c 0)"

lemma is_nonzero_const_monomialI:
  assumes "c \<noteq> 0"
  shows "is_nonzero_const_monomial (monomial c 0)"
  unfolding is_nonzero_const_monomial_def using assms by blast

lemma is_nonzero_const_monomialE:
  assumes "is_nonzero_const_monomial p"
  obtains c where "c \<noteq> 0" and "p = monomial c 0"
  using assms unfolding is_nonzero_const_monomial_def by blast

lemma is_nonzero_const_monomial_not_zero:
  assumes "is_nonzero_const_monomial p"
  shows "p \<noteq> 0"
proof -
  from assms obtain c where "c \<noteq> 0" and p: "p = monomial c 0" by (rule is_nonzero_const_monomialE)
  from \<open>c \<noteq> 0\<close> show ?thesis by (simp add: p monomial_0_iff)
qed

lemma is_nonzero_const_monomial_alt_keys [code]:
  "is_nonzero_const_monomial p \<longleftrightarrow> (keys p = {0})"
proof
  assume "is_nonzero_const_monomial p"
  then obtain c where "c \<noteq> 0" and p: "p = monomial c 0" by (rule is_nonzero_const_monomialE)
  thus "keys p = {0}" by simp
next
  assume "keys p = {0}"
  define c where "c = lookup p 0"
  from \<open>keys p = {0}\<close> have "c \<noteq> 0" by (simp add: c_def)
  have p: "p = monomial c 0"
    by (rule poly_mapping_keys_eqI, simp add: \<open>keys p = {0}\<close> \<open>c \<noteq> 0\<close>, simp add: \<open>keys p = {0}\<close> c_def)
  from \<open>c \<noteq> 0\<close> show "is_nonzero_const_monomial p" unfolding p by (rule is_nonzero_const_monomialI)
qed

end (* comm_powerprod *)

context ordered_powerprod
begin

lemma is_nonzero_const_monomial_lp:
  assumes "is_nonzero_const_monomial p"
  shows "lp p = 0"
proof -
  from assms obtain c where "c \<noteq> 0" and p: "p = monomial c 0" by (rule is_nonzero_const_monomialE)
  from \<open>c \<noteq> 0\<close> show ?thesis by (simp add: p lp_monomial)
qed

lemma is_nonzero_const_monomial_alt: "is_nonzero_const_monomial p \<longleftrightarrow> (p \<noteq> 0 \<and> lp p = 0)"
proof
  assume "is_nonzero_const_monomial p"
  hence "p \<noteq> 0" and "lp p = 0"
    by (rule is_nonzero_const_monomial_not_zero, rule is_nonzero_const_monomial_lp)
  thus "p \<noteq> 0 \<and> lp p = 0" ..
next
  assume "p \<noteq> 0 \<and> lp p = 0"
  hence "p \<noteq> 0" and "lp p = 0" by simp_all
  have "is_nonzero_const_monomial (monomial (lc p) (0::'a))"
    by (rule is_nonzero_const_monomialI, rule lc_not_0, fact)
  moreover have "monomial (lc p) (lp p) = p"
  proof (rule monomial_eq_itself)
    have "keys p = {lp p}"
    proof (rule set_eqI, rule, simp_all)
      fix t
      assume "t \<in> keys p"
      hence "t \<preceq> lp p" by (rule lp_max_keys)
      moreover have "lp p \<preceq> t" unfolding \<open>lp p = 0\<close> by (fact zero_min)
      ultimately show "t = lp p" by simp
    next
      from \<open>p \<noteq> 0\<close> show "lp p \<in> keys p" by (rule lp_in_keys)
    qed
    thus "is_monomial p" by (simp add: is_monomial_def)
  qed
  ultimately show "is_nonzero_const_monomial p" by (simp add: \<open>lp p = 0\<close>)
qed

lemma pideal_eq_UNIV_if_contains_nonzero_const_monomial:
  assumes "p \<in> pideal F" and "is_nonzero_const_monomial (p::'a::comm_powerprod \<Rightarrow>\<^sub>0 'b::field)"
  shows "pideal F = UNIV"
proof (simp only: ideal_eq_UNIV_iff_contains_one)
  from assms(2) obtain c where "c \<noteq> 0" and p: "p = monomial c 0" by (rule is_nonzero_const_monomialE)
  from assms(1) have "monom_mult (1 / c) 0 p \<in> pideal F" by (rule pideal_closed_monom_mult)
  moreover from \<open>c \<noteq> 0\<close> have "monom_mult (1 / c) 0 p = 1" by (simp add: p monom_mult_monomial)
  ultimately show "1 \<in> pideal F" by simp
qed

end (* ordered_powerprod *)

subsubsection \<open>Type synonyms\<close>

type_synonym ('a, 'b, 'c) pdata' = "('a \<Rightarrow>\<^sub>0 'b) \<times> 'c"
type_synonym ('a, 'b, 'c) pdata = "('a \<Rightarrow>\<^sub>0 'b) \<times> nat \<times> 'c"
type_synonym ('a, 'b, 'c) pdata_pair = "('a, 'b, 'c) pdata \<times> ('a, 'b, 'c) pdata"
type_synonym ('a, 'b, 'c, 'd) selT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c, 'd) complT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                    nat \<times> 'd \<Rightarrow> (('a, 'b, 'c) pdata' list \<times> 'd)"
type_synonym ('a, 'b, 'c, 'd) apT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c, 'd) abT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list"

subsubsection \<open>Specification of the @{emph \<open>selector\<close>} parameter\<close>

definition sel_spec :: "('a, 'b, 'c, 'd) selT \<Rightarrow> bool"
  where "sel_spec sel \<longleftrightarrow>
          (\<forall>gs bs ps data. ps \<noteq> [] \<longrightarrow> (sel gs bs ps data \<noteq> [] \<and> set (sel gs bs ps data) \<subseteq> set ps))"

lemma sel_specI:
  assumes "\<And>gs bs ps data. ps \<noteq> [] \<Longrightarrow> (sel gs bs ps data \<noteq> [] \<and> set (sel gs bs ps data) \<subseteq> set ps)"
  shows "sel_spec sel"
  unfolding sel_spec_def using assms by blast

lemma sel_specD1:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "sel gs bs ps data \<noteq> []"
  using assms unfolding sel_spec_def by blast

lemma sel_specD2:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "set (sel gs bs ps data) \<subseteq> set ps"
  using assms unfolding sel_spec_def by blast

subsubsection \<open>Specification of the @{emph \<open>add-pairs\<close>} parameter\<close>

definition ap_spec :: "('a, 'b, 'c, 'd) apT \<Rightarrow> bool"
  where "ap_spec ap \<longleftrightarrow> (\<forall>gs bs ps ns data.
      set (ap gs bs ps ns data) \<subseteq> set ps \<union> (set ns \<times> (set gs \<union> set bs \<union> set ns)) \<and>
      set ps \<union> (set ns \<times> (set gs \<union> set bs)) \<subseteq> set (ap gs bs ps ns data) \<and>
      (\<forall>h1\<in>set ns. \<forall>h2\<in> set ns. h1 \<noteq> h2 \<longrightarrow>
        ((h1, h2) \<in> set (ap gs bs ps ns data) \<or> (h2, h1) \<in> set (ap gs bs ps ns data))))"

lemma ap_specI:
  assumes "\<And>gs bs ps ns data.
                set (ap gs bs ps ns data) \<subseteq> set ps \<union> (set ns \<times> (set gs \<union> set bs \<union> set ns))"
  assumes "\<And>gs bs ps ns data. set ps \<union> (set ns \<times> (set gs \<union> set bs)) \<subseteq> set (ap gs bs ps ns data)"
  assumes "\<And>gs bs ps ns h1 h2 data. h1 \<in> set ns \<Longrightarrow> h2 \<in> set ns \<Longrightarrow> h1 \<noteq> h2 \<Longrightarrow>
                   ((h1, h2) \<in> set (ap gs bs ps ns data) \<or> (h2, h1) \<in> set (ap gs bs ps ns data))"
  shows "ap_spec ap"
  unfolding ap_spec_def using assms by auto

lemma ap_specD1:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps ns data) \<subseteq> set ps \<union> (set ns \<times> (set gs \<union> set bs \<union> set ns))"
  using assms unfolding ap_spec_def by blast

lemma ap_specD2:
  assumes "ap_spec ap"
  shows "set ps \<union> (set ns \<times> (set gs \<union> set bs)) \<subseteq> set (ap gs bs ps ns data)"
  using assms unfolding ap_spec_def by blast

lemma ap_specE:
  assumes "ap_spec ap" and "h1 \<in> set ns" and "h2 \<in> set ns" and "h1 \<noteq> h2"
  obtains "(h1, h2) \<in> set (ap gs bs ps ns data)"|"(h2, h1) \<in> set (ap gs bs ps ns data)"
  using assms unfolding ap_spec_def by blast

lemma ap_spec_Nil_new:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps [] data) = set ps"
proof
  from ap_specD1[OF assms] show "set (ap gs bs ps [] data) \<subseteq> set ps" by fastforce
next
  from ap_specD2[OF assms] show "set ps \<subseteq> set (ap gs bs ps [] data)" by blast
qed

lemma ap_spec_inI1:
  assumes "ap_spec ap" and "p \<in> set ps"
  shows "p \<in> set (ap gs bs ps ns data)"
  using ap_specD2[OF assms(1)] assms(2) by blast

lemma ap_spec_inI2:
  assumes "ap_spec ap" and "h \<in> set ns" and "g \<in> set gs \<union> set bs"
  shows "(h, g) \<in> set (ap gs bs ps ns data)"
  using ap_specD2[OF assms(1)] assms(2, 3) by blast

lemma ap_spec_fst_subset:
  assumes "ap_spec ap"
  shows "fst ` set (ap gs bs ps ns data) \<subseteq> fst ` set ps \<union> set ns"
proof -
  from ap_specD1[OF assms]
  have "fst ` set (ap gs bs ps ns data) \<subseteq> fst ` (set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_snd_subset:
  assumes "ap_spec ap"
  shows "snd ` set (ap gs bs ps ns data) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set ns"
proof -
  from ap_specD1[OF assms]
  have "snd ` set (ap gs bs ps ns data) \<subseteq> snd ` (set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_fst_superset:
  assumes "ap_spec ap"
  shows "fst ` set ps \<subseteq> fst ` set (ap gs bs ps ns data)"
proof -
  from ap_specD2[OF assms]
  have "fst ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> fst ` set (ap gs bs ps ns data)"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_fst:
  assumes "ap_spec ap" and "set gs \<union> set bs \<noteq> {}"
  shows "fst ` set (ap gs bs ps ns data) = fst ` set ps \<union> set ns"
proof
  from assms(1) show "fst ` set (ap gs bs ps ns data) \<subseteq> fst ` set ps \<union> set ns"
    by (rule ap_spec_fst_subset)
next
  show "fst ` set ps \<union> set ns \<subseteq> fst ` set (ap gs bs ps ns data)"
  proof (simp only: Un_subset_iff, rule conjI, rule ap_spec_fst_superset, fact)
    from ap_specD2[OF assms(1)]
    have "fst ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> fst ` set (ap gs bs ps ns data)"
      by (rule image_mono)
    hence "fst ` (set ns \<times> (set gs \<union> set bs)) \<subseteq> fst ` set (ap gs bs ps ns data)" by blast
    with assms(2) show "set ns \<subseteq> fst ` set (ap gs bs ps ns data)" by auto
  qed
qed

lemma ap_spec_snd_superset1:
  assumes "ap_spec ap"
  shows "snd ` set ps \<subseteq> snd ` set (ap gs bs ps ns data)"
proof -
  from ap_specD2[OF assms]
  have "snd ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> snd ` set (ap gs bs ps ns data)"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_snd_superset2:
  assumes "ap_spec ap" and "ns \<noteq> []"
  shows "snd ` set ps \<union> set gs \<union> set bs \<subseteq> snd ` set (ap gs bs ps ns data)"
proof -
  from ap_specD2[OF assms(1)]
  have "snd ` (set ps \<union> set ns \<times> (set gs \<union> set bs)) \<subseteq> snd ` set (ap gs bs ps ns data)"
    by (rule image_mono)
  with assms(2) show ?thesis by (simp add: image_Un)
qed

lemma ap_spec_inE:
  assumes "ap_spec ap" and "(p, q) \<in> set (ap gs bs ps ns data)"
  assumes 1: "(p, q) \<in> set ps \<Longrightarrow> thesis"
  assumes 2: "p \<in> set ns \<Longrightarrow> q \<in> set gs \<union> set bs \<union> set ns \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(2) ap_specD1[OF assms(1)] have "(p, q) \<in> set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns)" ..
  thus ?thesis
  proof
    assume "(p, q) \<in> set ps"
    thus ?thesis by (rule 1)
  next
    assume "(p, q) \<in> set ns \<times> (set gs \<union> set bs \<union> set ns)"
    hence "p \<in> set ns" and "q \<in> set gs \<union> set bs \<union> set ns" by blast+
    thus ?thesis by (rule 2)
  qed
qed

subsubsection \<open>Specification of the @{emph \<open>add-basis\<close>} parameter\<close>

definition ab_spec :: "('a, 'b, 'c, 'd) abT \<Rightarrow> bool"
  where "ab_spec ab \<longleftrightarrow>
              (\<forall>gs bs ns data. ns \<noteq> [] \<longrightarrow> set (ab gs bs ns data) = set bs \<union> set ns) \<and>
              (\<forall>gs bs data. ab gs bs [] data = bs)"

lemma ab_specI:
  assumes "\<And>gs bs ns data. ns \<noteq> [] \<Longrightarrow> set (ab gs bs ns data) = set bs \<union> set ns"
    and "\<And>gs bs data. ab gs bs [] data = bs"
  shows "ab_spec ab"
  unfolding ab_spec_def using assms by blast

lemma ab_specD1:
  assumes "ab_spec ab"
  shows "set (ab gs bs ns data) = set bs \<union> set ns"
  using assms unfolding ab_spec_def by (metis empty_set sup_bot.right_neutral)

lemma ab_specD2:
  assumes "ab_spec ab"
  shows "ab gs bs [] data = bs"
  using assms unfolding ab_spec_def by blast

lemma subset_Times_ap:
  assumes "ap_spec ap" and "ab_spec ab" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "set (ap gs bs (ps -- sps) ns data) \<subseteq> set (ab gs bs ns data) \<times> (set gs \<union> set (ab gs bs ns data))"
proof
  fix p q
  assume "(p, q) \<in> set (ap gs bs (ps -- sps) ns data)"
  with assms(1) show "(p, q) \<in> set (ab gs bs ns data) \<times> (set gs \<union> set (ab gs bs ns data))"
  proof (rule ap_spec_inE)
    assume "(p, q) \<in> set (ps -- sps)"
    hence "(p, q) \<in> set ps" by (simp add: set_diff_list)
    from this assms(3) have "(p, q) \<in> set bs \<times> (set gs \<union> set bs)" ..
    hence "p \<in> set bs" and "q \<in> set gs \<union> set bs" by blast+
    thus ?thesis by (auto simp add: ab_specD1[OF assms(2)])
  next
    assume "p \<in> set ns" and "q \<in> set gs \<union> set bs \<union> set ns"
    thus ?thesis by (simp add: ab_specD1[OF assms(2)])
  qed
qed

lemma processed_apE:
  assumes "ap_spec ap" and "ab_spec ab" and "processed (f, g) (gs @ (ab gs bs ns data)) (ap gs bs ps ns data)"
  assumes 1: "processed (f, g) (gs @ bs) ps \<Longrightarrow> thesis"
  assumes 2: "f \<in> set ns \<Longrightarrow> g \<in> set ns \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(3) have d1: "f \<in> set gs \<union> set bs \<or> f \<in> set ns" and d2: "g \<in> set gs \<union> set bs \<or> g \<in> set ns"
    and a: "(f, g) \<notin> set (ap gs bs ps ns data)" and b: "(g, f) \<notin> set (ap gs bs ps ns data)"
    by (simp_all add: processed_def ab_specD1[OF assms(2)])
  from d1 show ?thesis
  proof
    assume "f \<in> set ns"
    from d2 show ?thesis
    proof
      assume "g \<in> set ns"
      with \<open>f \<in> set ns\<close> show ?thesis by (rule 2)
    next
      assume "g \<in> set gs \<union> set bs"
      with assms(1) \<open>f \<in> set ns\<close> have "(f, g) \<in> set (ap gs bs ps ns data)" by (rule ap_spec_inI2)
      with a show ?thesis ..
    qed
  next
    assume "f \<in> set gs \<union> set bs"
    hence "f \<in> set (gs @ bs)" by simp
    from d2 show ?thesis
    proof
      assume "g \<in> set ns"
      from assms(1) this \<open>f \<in> set gs \<union> set bs\<close> have "(g, f) \<in> set (ap gs bs ps ns data)"
        by (rule ap_spec_inI2)
      with b show ?thesis ..
    next
      assume "g \<in> set gs \<union> set bs"
      hence "g \<in> set (gs @ bs)" by simp
      from \<open>f \<in> set (gs @ bs)\<close> this have "processed (f, g) (gs @ bs) ps"
      proof (rule processedI)
        show "(f, g) \<notin> set ps"
        proof
          assume "(f, g) \<in> set ps"
          with assms(1) have "(f, g) \<in> set (ap gs bs ps ns data)" by (rule ap_spec_inI1)
          with a show False ..
        qed
      next
        show "(g, f) \<notin> set ps"
        proof
          assume "(g, f) \<in> set ps"
          with assms(1) have "(g, f) \<in> set (ap gs bs ps ns data)" by (rule ap_spec_inI1)
          with b show False ..
        qed
      qed
      thus ?thesis by (rule 1)
    qed
  qed
qed

subsubsection \<open>Function @{term args_to_set}\<close>

context gd_powerprod
begin

definition args_to_set :: "('a, 'b::field, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) set"
  where "args_to_set x = fst ` (set (fst x) \<union> set (fst (snd x)) \<union> fst ` set (snd (snd x)) \<union> snd ` set (snd (snd x)))"

lemma args_to_set_alt:
  "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs \<union> fst ` fst ` set ps \<union> fst ` snd ` set ps"
  by (simp add: args_to_set_def image_Un)

lemma args_to_set_subset_Times:
  assumes "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs"
  unfolding args_to_set_alt using assms by auto

lemma args_to_set_alt2:
  assumes "ap_spec ap" and "ab_spec ab"
  shows "args_to_set (gs, ab gs bs ns data, ap gs bs ps ns data) = fst ` (set gs \<union> set bs \<union>
              fst ` set ps \<union> snd ` set ps \<union> set ns)" (is "?l = fst ` ?r")
proof
  show "?l \<subseteq> fst ` ?r"
  proof (simp only: args_to_set_alt Un_subset_iff, intro conjI image_mono)
    show "set (ab gs bs ns data) \<subseteq> ?r" by (auto simp add: ab_specD1[OF assms(2)])
  next
    from assms(1) have "fst ` set (ap gs bs ps ns data) \<subseteq> fst ` set ps \<union> set ns"
      by (rule ap_spec_fst_subset)
    thus "fst ` set (ap gs bs ps ns data) \<subseteq> ?r" by blast
  next
    from assms(1) have "snd ` set (ap gs bs ps ns data) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set ns"
      by (rule ap_spec_snd_subset)
    thus "snd ` set (ap gs bs ps ns data) \<subseteq> ?r" by blast
  qed blast
next
  let ?u = "set gs \<union> set (ab gs bs ns data) \<union> fst ` set (ap gs bs ps ns data) \<union> snd ` set (ap gs bs ps ns data)"
  show "fst ` ?r \<subseteq> ?l"
  proof (simp only: args_to_set_alt image_Un[symmetric], rule image_mono, simp only: Un_subset_iff, intro conjI)
    show "set gs \<subseteq> ?u" by blast
  next
    from assms(2) have "set bs \<subseteq> set (ab gs bs ns data)" by (simp add: ab_specD1)
    thus "set bs \<subseteq> ?u" by blast
  next
    from assms(1) have "fst ` set ps \<subseteq> fst ` set (ap gs bs ps ns data)"
      by (rule ap_spec_fst_superset)
    thus "fst ` set ps \<subseteq> ?u" by blast
  next
    from assms(1) have "snd ` set ps \<subseteq> snd ` set (ap gs bs ps ns data)"
      by (rule ap_spec_snd_superset1)
    thus "snd ` set ps \<subseteq> ?u" by blast
  next
    from assms(2) have "set ns \<subseteq> set (ab gs bs ns data)" by (simp add: ab_specD1)
    thus "set ns \<subseteq> ?u" by blast
  qed
qed

lemma args_to_set_subset1:
  assumes "set gs1 \<subseteq> set gs2"
  shows "args_to_set (gs1, bs, ps) \<subseteq> args_to_set (gs2, bs, ps)"
  using assms by (auto simp add: args_to_set_alt)

lemma args_to_set_subset2:
  assumes "set bs1 \<subseteq> set bs2"
  shows "args_to_set (gs, bs1, ps) \<subseteq> args_to_set (gs, bs2, ps)"
  using assms by (auto simp add: args_to_set_alt)

lemma args_to_set_subset3:
  assumes "set ps1 \<subseteq> set ps2"
  shows "args_to_set (gs, bs, ps1) \<subseteq> args_to_set (gs, bs, ps2)"
  using assms unfolding args_to_set_alt by blast

subsubsection \<open>Specification of the @{emph \<open>completion\<close>} parameter\<close>

definition compl_struct :: "('a, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_struct compl \<longleftrightarrow>
          (\<forall>gs bs ps sps data. sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              (\<forall>d. dickson_grading (+) d \<longrightarrow>
                  dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))) \<and>
              0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data)) \<and>
              (\<forall>h\<in>set (fst (compl gs bs (ps -- sps) sps data)). \<forall>b\<in>set bs. fst b \<noteq> 0 \<longrightarrow> \<not> lp (fst b) adds lp (fst h)))"

lemma compl_structI:
  assumes "\<And>d gs bs ps sps data. dickson_grading (+) d \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps sps data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow> 0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
  assumes "\<And>gs bs ps sps h b data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow> h \<in> set (fst (compl gs bs (ps -- sps) sps data)) \<Longrightarrow>
              b \<in> set bs \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> \<not> lp (fst b) adds lp (fst h)"
  shows "compl_struct compl"
  unfolding compl_struct_def using assms by auto

lemma compl_structD1:
  assumes "compl_struct compl" and "dickson_grading (+) d" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD2:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD3:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
    and "h \<in> set (fst (compl gs bs (ps -- sps) sps data))" and "b \<in> set bs" and "fst b \<noteq> 0"
  shows "\<not> lp (fst b) adds lp (fst h)"
  using assms unfolding compl_struct_def by blast

definition struct_spec :: "('a, 'b::field, 'c, 'd) selT \<Rightarrow> ('a, 'b, 'c, 'd) apT \<Rightarrow> ('a, 'b, 'c, 'd) abT \<Rightarrow>
                            ('a, 'b, 'c, 'd) complT \<Rightarrow> bool"
  where "struct_spec sel ap ab compl \<longleftrightarrow> (sel_spec sel \<and> ap_spec ap \<and> ab_spec ab \<and> compl_struct compl)"

lemma struct_specI:
  assumes "sel_spec sel" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  shows "struct_spec sel ap ab compl"
  unfolding struct_spec_def using assms by (intro conjI)

lemma struct_specD1:
  assumes "struct_spec sel ap ab compl"
  shows "sel_spec sel"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD2:
  assumes "struct_spec sel ap ab compl"
  shows "ap_spec ap"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD3:
  assumes "struct_spec sel ap ab compl"
  shows "ab_spec ab"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD4:
  assumes "struct_spec sel ap ab compl"
  shows "compl_struct compl"
  using assms unfolding struct_spec_def by (elim conjE)

lemmas struct_specD = struct_specD1 struct_specD2 struct_specD3 struct_specD4

definition unique_idx :: "('a, 'b, 'c) pdata list \<Rightarrow> (nat \<times> 'd) \<Rightarrow> bool"
  where "unique_idx bs data \<longleftrightarrow>
                         (\<forall>f\<in>set bs. \<forall>g\<in>set bs. fst (snd f) = fst (snd g) \<longrightarrow> f = g) \<and>
                         (\<forall>f\<in>set bs. fst (snd f) < fst data)"

lemma unique_idxI:
  assumes "\<And>f g. f \<in> set bs \<Longrightarrow> g \<in> set bs \<Longrightarrow> fst (snd f) = fst (snd g) \<Longrightarrow> f = g"
    and "\<And>f. f \<in> set bs \<Longrightarrow> fst (snd f) < fst data"
  shows "unique_idx bs data"
  unfolding unique_idx_def using assms by blast

lemma unique_idxD1:
  assumes "unique_idx bs data" and "f \<in> set bs" and "g \<in> set bs" and "fst (snd f) = fst (snd g)"
  shows "f = g"
  using assms unfolding unique_idx_def by blast

lemma unique_idxD2:
  assumes "unique_idx bs data" and "f \<in> set bs"
  shows "fst (snd f) < fst data"
  using assms unfolding unique_idx_def by blast

lemma unique_idx_Nil: "unique_idx [] data"
  by (simp add: unique_idx_def)

definition compl_pideal :: "('a, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_pideal compl \<longleftrightarrow>
          (\<forall>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<longrightarrow> sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              unique_idx (gs @ bs) data \<longrightarrow>
              fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pideal (args_to_set (gs, bs, ps)))"

lemma compl_pidealI:
  assumes "\<And>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              unique_idx (gs @ bs) data \<Longrightarrow>
              fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pideal (args_to_set (gs, bs, ps))"
  shows "compl_pideal compl"
  unfolding compl_pideal_def using assms by blast

lemma compl_pidealD:
  assumes "compl_pideal compl" and "is_Groebner_basis (fst ` set gs)"
    and "sps \<noteq> []" and "set sps \<subseteq> set ps" and "unique_idx (gs @ bs) data"
  shows "fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pideal (args_to_set (gs, bs, ps))"
  using assms unfolding compl_pideal_def by blast

definition compl_conn :: "('a, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_conn compl \<longleftrightarrow>
            (\<forall>d m gs bs ps sps p q data. dickson_grading (+) d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
              is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
              set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              unique_idx (gs @ bs) data \<longrightarrow>
              (\<forall>p' q'. processed (p', q') (gs @ bs) ps \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')) \<longrightarrow>
              (p, q) \<in> set sps \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q))"

text \<open>Informally, @{term "compl_conn compl"} means that, for suitable arguments @{term gs}, @{term bs},
  @{term ps} and @{term sps}, the value of @{term "compl gs bs ps sps"} is a list @{term ns} such that
  the critical pairs of all elements in @{term sps} can be connected modulo @{term "set gs \<union> set bs \<union> set ns"},
  provided that the critical pairs of all elements that have been processed already can be connected
  modulo the smaller set @{term "set gs \<union> set bs"}.\<close>

lemma compl_connI:
  assumes "\<And>d m gs bs ps sps p q data. dickson_grading (+) d \<Longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<Longrightarrow>
            is_Groebner_basis (fst ` set gs) \<Longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<Longrightarrow>
            set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
            unique_idx (gs @ bs) data \<Longrightarrow>
            (\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                      crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')) \<Longrightarrow>
            (p, q) \<in> set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q)"
  shows "compl_conn compl"
  unfolding compl_conn_def using assms by presburger

lemma compl_connD:
  assumes "compl_conn compl" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
    and "unique_idx (gs @ bs) data"
    and "\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
    and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q)"
  using assms unfolding compl_conn_def Un_assoc by blast

subsubsection \<open>Function @{term gb_schema_aux}\<close>

definition (in -) add_indices :: "(('a, 'b, 'c) pdata' list \<times> 'd) \<Rightarrow> (nat \<times> 'd) \<Rightarrow> (('a, 'b, 'c) pdata list \<times> nat \<times> 'd)"
  where [code del]: "add_indices ns data =
        (map_idx (\<lambda>h i. (fst h, i, snd h)) (fst ns) (fst data), fst data + length (fst ns), snd ns)"

lemma (in -) add_indices_code [code]:
  "add_indices (ns, data) (n, data') = (map_idx (\<lambda>(h, d) i. (h, i, d)) ns n, n + length ns, data)"
  by (simp add: add_indices_def case_prod_beta')

lemma fst_add_indices: "map fst (fst (add_indices ns data')) = map fst (fst ns)"
  by (simp add: add_indices_def map_map_idx map_idx_no_idx)

corollary fst_set_add_indices: "fst ` set (fst (add_indices ns data')) = fst ` set (fst ns)"
  using fst_add_indices by (metis set_map)

lemma in_set_add_indicesE:
  assumes "f \<in> set (fst (add_indices aux data))"
  obtains i where "i < length (fst aux)" and "f = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))"
proof -
  let ?hs = "fst (add_indices aux data)"
  from assms obtain i where "i < length ?hs" and "f = ?hs ! i" by (metis in_set_conv_nth)
  from this(1) have "i < length (fst aux)" by (simp add: add_indices_def)
  hence "?hs ! i = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))"
    unfolding add_indices_def fst_conv by (rule map_idx_nth)
  hence "f = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))" by (simp add: \<open>f = ?hs ! i\<close>)
  with \<open>i < length (fst aux)\<close> show ?thesis ..
qed

definition gb_schema_aux_term1 ::
    "('a \<Rightarrow> nat) \<Rightarrow> ((('a, 'b::field, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list) \<times>
                    (('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term1 d = (measure length) <*lex*>
                              {(a, b::('a, 'b, 'c) pdata list). (fst ` set a) \<sqsupset>p (fst ` set b)} <*lex*>
                              (measure (card \<circ> set))"

definition gb_schema_aux_term2 ::
    "('a \<Rightarrow> nat) \<Rightarrow> ((('a, 'b::field, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list) \<times>
                    (('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata list \<times> ('a, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term2 d = {(a, b). dgrad_p_set_le d (args_to_set a) (args_to_set b)}"

definition gb_schema_aux_term where "gb_schema_aux_term d = gb_schema_aux_term1 d \<inter> gb_schema_aux_term2 d"

text \<open>@{const gb_schema_aux_term} is needed for proving termination of function @{term gb_schema_aux}.\<close>

lemma gb_schema_aux_term1_wf_on:
  assumes "dickson_grading (+) d"
  shows "wfP_on {x::(('a, 'b, 'c) pdata list) \<times> ('a, 'b, 'c) pdata list \<times> ((('a, 'b::field, 'c) pdata_pair list)). args_to_set x \<subseteq> dgrad_p_set d m} (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_p_set d m"
  let ?A = "{x::(('a, 'b, 'c) pdata list) \<times> ('a, 'b, 'c) pdata list \<times> ((('a, 'b, 'c) pdata_pair list)). args_to_set x \<subseteq> ?B}"
  have A_sub_Pow: "(image fst) ` set ` fst ` snd ` ?A \<subseteq> Pow ?B"
  proof
    fix x
    assume "x \<in> (image fst) ` set ` fst ` snd ` ?A"
    then obtain x1 where "x1 \<in> set ` fst ` snd ` ?A" and x: "x = fst ` x1" by auto
    from this(1) obtain x2 where "x2 \<in> fst ` snd ` ?A" and x1: "x1 = set x2" by auto
    from this(1) obtain x3 where "x3 \<in> snd ` ?A" and x2: "x2 = fst x3" by auto
    from this(1) obtain x4 where "x4 \<in> ?A" and x3: "x3 = snd x4" by auto
    from this(1) have "args_to_set x4 \<subseteq> ?B" by simp
    thus "x \<in> Pow ?B" by (simp add: args_to_set_def x x1 x2 x3 image_Un)
  qed

  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  have "fst x \<in> fst ` Q" by (rule, fact refl, fact)
  with wf_measure obtain z0 where "z0 \<in> fst ` Q"
    and 1: "\<And>y. (y, z0) \<in> measure length \<Longrightarrow> y \<notin> fst ` Q" by (rule wfE_min, blast)
  from this(1) obtain x0 where "x0 \<in> Q" and z0: "z0 = fst x0" ..

  let ?Q1 = "{q \<in> Q. fst q = z0}"
  have "?Q1 \<subseteq> Q" by blast
  have "(image fst) ` set ` fst ` snd ` ?Q1 \<subseteq> (image fst) ` set ` fst ` snd ` Q"
    by ((rule image_mono)+, fact)
  also have "... \<subseteq> (image fst) ` set ` fst ` snd ` ?A"
    by ((rule image_mono)+, fact)
  finally have Q_sub_A: "(image fst) ` set ` fst ` snd ` ?Q1 \<subseteq> (image fst) ` set ` fst ` snd ` ?A" .
  from assms have "wfP_on (Pow ?B) (\<sqsupset>p)" by (rule red_supset_wf_on)
  moreover have "fst ` set (fst (snd x0)) \<in> (image fst) ` set ` fst ` snd ` ?Q1"
    by (rule, fact refl, rule, fact refl, rule, fact refl, rule, fact refl, simp add: \<open>x0 \<in> Q\<close> z0)
  moreover from Q_sub_A A_sub_Pow have "(image fst) ` set ` fst ` snd ` ?Q1 \<subseteq> Pow ?B" by (rule subset_trans)
  ultimately obtain z1 where "z1 \<in> (image fst) ` set ` fst ` snd ` ?Q1"
    and 2: "\<And>y. y \<sqsupset>p z1 \<Longrightarrow> y \<notin> (image fst) ` set ` fst ` snd ` ?Q1" by (rule wfP_onE_min, auto)
  from this(1) obtain x1 where "x1 \<in> ?Q1" and z1: "z1 = fst ` set (fst (snd x1))" by auto
  from this(1) have "x1 \<in> Q" and x1: "fst x1 = z0" by simp_all

  let ?Q2 = "{q \<in> ?Q1. fst ` set (fst (snd q)) = z1}"
  have "snd (snd x1) \<in> snd ` snd ` ?Q2"
    by (rule, fact refl, rule, fact refl, simp add: \<open>x1 \<in> ?Q1\<close> \<open>x1 \<in> Q\<close> z1 x1)
  with wf_measure obtain z2 where "z2 \<in> snd ` snd ` ?Q2"
    and 3: "\<And>y. (y, z2) \<in> measure (card \<circ> set) \<Longrightarrow> y \<notin> snd ` snd ` ?Q2"
    by (rule wfE_min, blast)
  from this(1) obtain z3 where "z3 \<in> snd ` ?Q2" and z2: "z2 = snd z3" ..
  from this(1) obtain z where "z \<in> ?Q2" and z3: "z3 = snd z" by auto
  from this(1) have "z \<in> ?Q1" and eq1: "fst ` set (fst (snd z)) = z1" by blast+
  from this(1) have "z \<in> Q" and eq2: "fst z = z0" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>?A. (y, z) \<in> gb_schema_aux_term1 d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>?A. (y, z) \<in> gb_schema_aux_term1 d \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI)
      fix y
      assume "y \<in> ?A"
      assume "(y, z) \<in> gb_schema_aux_term1 d"
      hence "(fst y, z0) \<in> measure length \<or>
              (fst y = z0 \<and> (fst ` set (fst (snd y)) \<sqsupset>p z1 \<or>
                (fst (snd y) = fst z3 \<and> (snd (snd y), z2) \<in> measure (card \<circ> set))))"
        by (simp add: gb_schema_aux_term1_def eq1[symmetric] eq2[symmetric] z2 z3 in_lex_prod_alt)
      thus "y \<notin> Q"
      proof (elim disjE conjE)
        assume "(fst y, z0) \<in> measure length"
        hence "fst y \<notin> fst ` Q" by (rule 1)
        thus ?thesis by blast
      next
        assume "fst ` set (fst (snd y)) \<sqsupset>p z1"
        hence "fst ` set (fst (snd y)) \<notin> (image fst) ` set ` fst ` snd ` ?Q1" by (rule 2)
        moreover assume "fst y = z0"
        ultimately show ?thesis by auto
      next
        assume "(snd (snd y), z2) \<in> measure (card \<circ> set)"
        hence "snd (snd y) \<notin> snd ` snd ` ?Q2" by (rule 3)
        hence "y \<notin> ?Q2" by blast
        moreover assume "fst y = z0" and "fst (snd y) = fst z3"
        ultimately show ?thesis by (simp add: eq1 z3)
      qed
    qed
  qed
qed

lemma gb_schema_aux_term_wf:
  assumes "dickson_grading (+) d"
  shows "wf (gb_schema_aux_term d)"
proof (rule wfI_min)
  fix x::"(('a, 'b, 'c) pdata list) \<times> ('a, 'b, 'c) pdata list \<times> (('a, 'b, 'c) pdata_pair list)" and Q
  assume "x \<in> Q"
  let ?A = "args_to_set x"
  have "finite ?A" by (simp add: args_to_set_def)
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. args_to_set q \<subseteq> ?B}"
  from assms have "wfP_on {x. args_to_set x \<subseteq> ?B} (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1 d)"
    by (rule gb_schema_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. args_to_set x \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> gb_schema_aux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "args_to_set z \<subseteq> ?B" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> gb_schema_aux_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> gb_schema_aux_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> gb_schema_aux_term d"
      hence "(y, z) \<in> gb_schema_aux_term1 d" and "(y, z) \<in> gb_schema_aux_term2 d"
        by (simp_all add: gb_schema_aux_term_def)
      from this(2) have "dgrad_p_set_le d (args_to_set y) (args_to_set z)"
        by (simp add: gb_schema_aux_term2_def)
      from this \<open>args_to_set z \<subseteq> ?B\<close> have "args_to_set y \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      moreover from \<open>(y, z) \<in> gb_schema_aux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

lemma dgrad_p_set_le_args_to_set_ab:
  assumes "dickson_grading (+) d" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  assumes "sps \<noteq> []" and "set sps \<subseteq> set ps" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
  unfolding args_to_set_alt2[OF assms(2, 3)] image_Un
proof (intro dgrad_p_set_leI_Un)
  show "dgrad_p_set_le d (fst ` set gs) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
next
  show "dgrad_p_set_le d (fst ` set bs) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
next
  show "dgrad_p_set_le d (fst ` fst ` set (ps -- sps)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_diff_list)
next
  show "dgrad_p_set_le d (fst ` snd ` set (ps -- sps)) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_diff_list)
next
  note assms(4, 1)
  from assms(4, 1, 5, 6) show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
    unfolding assms(7) fst_set_add_indices by (rule compl_structD1)
qed

corollary dgrad_p_set_le_args_to_set_struct:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl" and "ps \<noteq> []"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
proof -
  from assms(2) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(3) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding assms(4) by (rule sel_specD1, rule sel_specD2)
  from assms(1) ap ab compl this assms(5) show ?thesis by (rule dgrad_p_set_le_args_to_set_ab)
qed

lemma struct_spec_red_supset:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []" and "sps = sel gs bs ps data"
    and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)" and "hs \<noteq> []"
  shows "(fst ` set (ab gs bs hs data')) \<sqsupset>p (fst ` set bs)"
proof -
  from assms(5) have "set hs \<noteq> {}" by simp
  then obtain h' where "h' \<in> set hs" by fastforce
  let ?h = "fst h'"
  let ?m = "monomial (lc ?h) (lp ?h)"
  from \<open>h' \<in> set hs\<close> have h_in: "?h \<in> fst ` set hs" by simp
  hence "?h \<in> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
    by (simp only: assms(4) fst_set_add_indices)
  then obtain h'' where h''_in: "h'' \<in> set (fst (compl gs bs (ps -- sps) sps data))"
    and "?h = fst h''" ..
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(2) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding assms(3)
    by (rule sel_specD1, rule sel_specD2)
  from h_in compl_structD2[OF compl this] have "?h \<noteq> 0" unfolding assms(4) fst_set_add_indices
    by metis
  show ?thesis
  proof (simp add: ab_specD1[OF ab] image_Un, rule)
    fix q
    assume "is_red (fst ` set bs) q"
    moreover have "fst ` set bs \<subseteq> fst ` set bs \<union> fst ` set hs" by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set hs) q" by (rule is_red_subset)
  next
    from \<open>?h \<noteq> 0\<close> have "lc ?h \<noteq> 0" by (rule lc_not_0)
    moreover have "?h \<in> {?h}" ..
    ultimately have "is_red {?h} ?m" using \<open>?h \<noteq> 0\<close> adds_refl by (rule is_red_monomialI)
    moreover have "{?h} \<subseteq> fst ` set bs \<union> fst ` set hs" using h_in by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set hs) ?m" by (rule is_red_subset)
  next
    show "\<not> is_red (fst ` set bs) ?m"
    proof
      assume "is_red (fst ` set bs) ?m"
      then obtain b' where "b' \<in> fst ` set bs" and "b' \<noteq> 0" and "lp b' adds lp ?h"
        by (rule is_red_monomialE)
      from this(1) obtain b where "b \<in> set bs" and b': "b' = fst b" ..
      from \<open>b' \<noteq> 0\<close> have "fst b \<noteq> 0" by (simp add: b')
      thm compl_structD3
      with compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> h''_in \<open>b \<in> set bs\<close> have "\<not> lp (fst b) adds lp ?h"
        unfolding \<open>?h = fst h''\<close> by (rule compl_structD3)
      from this \<open>lp b' adds lp ?h\<close> show False by (simp add: b')
    qed
  qed
qed

lemma unique_idx_append:
  assumes "unique_idx gs data" and "(hs, data') = add_indices aux data"
  shows "unique_idx (gs @ hs) data'"
proof -
  from assms(2) have hs: "hs = fst (add_indices aux data)" and data': "data' = snd (add_indices aux data)"
    by (metis fst_conv, metis snd_conv)
  have len: "length hs = length (fst aux)" by (simp add: hs add_indices_def)
  have eq: "fst data' = fst data + length hs" by (simp add: data' add_indices_def hs)
  show ?thesis
  proof (rule unique_idxI)
    fix f g
    assume "f \<in> set (gs @ hs)" and "g \<in> set (gs @ hs)"
    hence d1: "f \<in> set gs \<union> set hs" and d2: "g \<in> set gs \<union> set hs" by simp_all
    assume id_eq: "fst (snd f) = fst (snd g)"
    from d1 show "f = g"
    proof
      assume "f \<in> set gs"
      from d2 show ?thesis
      proof
        assume "g \<in> set gs"
        from assms(1) \<open>f \<in> set gs\<close> this id_eq show ?thesis by (rule unique_idxD1)
      next
        assume "g \<in> set hs"
        then obtain j where "g = (fst (fst aux ! j), fst data + j, snd (fst aux ! j))" unfolding hs
          by (rule in_set_add_indicesE)
        hence "fst (snd g) = fst data + j" by simp
        moreover from assms(1) \<open>f \<in> set gs\<close> have "fst (snd f) < fst data"
          by (rule unique_idxD2)
        ultimately show ?thesis by (simp add: id_eq)
      qed
    next
      assume "f \<in> set hs"
      then obtain i where f: "f = (fst (fst aux ! i), fst data + i, snd (fst aux ! i))" unfolding hs
        by (rule in_set_add_indicesE)
      hence *: "fst (snd f) = fst data + i" by simp
      from d2 show ?thesis
      proof
        assume "g \<in> set gs"
        with assms(1) have "fst (snd g) < fst data" by (rule unique_idxD2)
        with * show ?thesis by (simp add: id_eq)
      next
        assume "g \<in> set hs"
        then obtain j where g: "g = (fst (fst aux ! j), fst data + j, snd (fst aux ! j))" unfolding hs
          by (rule in_set_add_indicesE)
        hence "fst (snd g) = fst data + j" by simp
        with * have "i = j" by (simp add: id_eq)
        thus ?thesis by (simp add: f g)
      qed
    qed
  next
    fix f
    assume "f \<in> set (gs @ hs)"
    hence "f \<in> set gs \<union> set hs" by simp
    thus "fst (snd f) < fst data'"
    proof
      assume "f \<in> set gs"
      with assms(1) have "fst (snd f) < fst data" by (rule unique_idxD2)
      also have "... \<le> fst data'" by (simp add: eq)
      finally show ?thesis .
    next
      assume "f \<in> set hs"
      then obtain i where "i < length (fst aux)"
        and "f = (fst (fst aux ! i), fst data + i, snd (fst aux ! i))" unfolding hs
        by (rule in_set_add_indicesE)
      from this(2) have "fst (snd f) = fst data + i" by simp
      also from \<open>i < length (fst aux)\<close> have "... < fst data + length (fst aux)" by simp
      finally show ?thesis by (simp only: eq len)
    qed
  qed
qed

corollary unique_idx_ab:
  assumes "ab_spec ab" and "unique_idx (gs @ bs) data" and "(hs, data') = add_indices aux data"
  shows "unique_idx (gs @ ab gs bs hs data') data'"
proof -
  from assms(2, 3) have "unique_idx ((gs @ bs) @ hs) data'" by (rule unique_idx_append)
  thus ?thesis by (simp add: unique_idx_def ab_specD1[OF assms(1)])
qed

function (domintros) gb_schema_aux :: "('a, 'b, 'c, 'd) selT \<Rightarrow> ('a, 'b, 'c, 'd) apT \<Rightarrow> ('a, 'b, 'c, 'd) abT \<Rightarrow>
                        ('a, 'b, 'c, 'd) complT \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                        ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b::zero_neq_one, 'c::default) pdata list"
  where
    "gb_schema_aux sel ap ab compl data gs bs ps =
        (if ps = [] then
          gs @ bs
        else
          (let sps = sel gs bs ps data; ps0 = ps -- sps; aux = compl gs bs ps0 sps data in
            (if (\<exists>h\<in>set (fst aux). is_nonzero_const_monomial (fst h)) then
              [(1, 0, default)]
            else
              let (hs, data') = add_indices aux data in
                gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )
        )"
  by pat_completeness auto

lemma gb_schema_aux_domI1: "gb_schema_aux_dom (sel, ap, ab, compl, data, gs, bs, [])"
  by (rule gb_schema_aux.domintros, simp)

lemma gb_schema_aux_domI2:
  assumes "struct_spec sel ap ab compl"
  shows "gb_schema_aux_dom (sel, ap, ab, compl, data, args)"
proof -
  from assms have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gb_schema_aux_term d"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  thus ?thesis
  proof (induct args arbitrary: data rule: wf_induct_rule)
    fix x data
    assume IH: "\<And>y data'. (y, x) \<in> ?R \<Longrightarrow> gb_schema_aux_dom (sel, ap, ab, compl, data', y)"
    obtain gs bs0 where x: "x = (gs, bs0)" by (meson case_prodE case_prodI2)
    obtain bs ps where bs0: "bs0 = (bs, ps)" by (meson case_prodE case_prodI2)
    show "gb_schema_aux_dom (sel, ap, ab, compl, data, x)" unfolding x bs0
    proof (rule gb_schema_aux.domintros)
      fix n0 data0 hs n1 data1
      assume "ps \<noteq> []"
        and hs_data': "(hs, n1, data1) = add_indices (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                               (sel gs bs ps (n0, data0)) (n0, data0)) (n0, data0)"
        and data: "data = (n0, data0)"
      define sps where "sps = sel gs bs ps (n0, data0)"
      define data' where "data' = (n1, data1)"
      from hs_data' have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
        unfolding sps_def data by (metis fstI)
      show "gb_schema_aux_dom (sel, ap, ab, compl, data', gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')"
      proof (rule IH, simp add: x bs0 gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, rule)
        show "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs \<or>
                ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
        proof (cases "hs = []")
          case True
          have "ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
          proof (simp only: True ap_spec_Nil_new[OF ap], rule)
            from ab show "ab gs bs [] data' = bs" by (rule ab_specD2)
          next
            from sel \<open>ps \<noteq> []\<close> have "sps \<noteq> []" and "set sps \<subseteq> set ps"
              unfolding sps_def by (rule sel_specD1, rule sel_specD2)
            moreover from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
            ultimately have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
            hence "set (ps -- sps) \<subset> set ps" unfolding set_diff_list by fastforce
            thus "card (set (ps -- sps)) < card (set ps)" by (simp add: psubset_card_mono)
          qed
          thus ?thesis ..
        next
          case False
          with assms \<open>ps \<noteq> []\<close> sps_def hs have "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs"
            unfolding data[symmetric] by (rule struct_spec_red_supset)
          thus ?thesis ..
        qed
      next
        from dg assms \<open>ps \<noteq> []\<close> sps_def hs
        show "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
          unfolding data[symmetric] by (rule dgrad_p_set_le_args_to_set_struct)
      qed
    qed
  qed
qed

lemmas gb_schema_aux_simp = gb_schema_aux.psimps[OF gb_schema_aux_domI2]

lemma gb_schema_aux_Nil [simp, code]: "gb_schema_aux sel ap ab compl data gs bs [] = gs @ bs"
  by (simp add: gb_schema_aux.psimps[OF gb_schema_aux_domI1])

lemma gb_schema_aux_not_Nil:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []"
  shows "gb_schema_aux sel ap ab compl data gs bs ps =
          (let sps = sel gs bs ps data; ps0 = ps -- sps; aux = compl gs bs ps0 sps data in
            (if (\<exists>h\<in>set (fst aux). is_nonzero_const_monomial (fst h)) then
              [(1, 0, default)]
            else
              let (hs, data') = add_indices aux data in
                gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )"
  by (simp add: gb_schema_aux_simp[OF assms(1)] assms(2))

text \<open>In order to prove the following lemma we again have to employ well-founded induction, since
  @{thm gb_schema_aux.pinduct} does not treat the first arguments of @{const gb_schema_aux} in the proper way.\<close>
lemma gb_schema_aux_induct [consumes 1, case_names base rec1 rec2]:
  assumes "struct_spec sel ap ab compl"
  assumes base: "\<And>bs data. P data bs [] (gs @ bs)"
    and rec1: "\<And>bs ps sps h data. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps data \<Longrightarrow>
                h \<in> set (fst (add_indices (compl gs bs (ps -- sps) sps data) data)) \<Longrightarrow>
                is_nonzero_const_monomial (fst h) \<Longrightarrow> P data bs ps [(1, 0, default)]"
    and rec2: "\<And>bs ps sps hs data data'. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps data \<Longrightarrow>
                (hs, data') = add_indices (compl gs bs (ps -- sps) sps data) data \<Longrightarrow>
                (\<And>h. h \<in> set hs \<Longrightarrow> \<not> is_nonzero_const_monomial (fst h)) \<Longrightarrow>
                P data' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')) \<Longrightarrow>
                P data bs ps (gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
  shows "P data bs ps (gb_schema_aux sel ap ab compl data gs bs ps)"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    by (rule struct_specD)+
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gb_schema_aux_term d"
  define args where "args = (gs, bs, ps)"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  hence "fst args = gs \<Longrightarrow> P data (fst (snd args)) (snd (snd args))
              (gb_schema_aux sel ap ab compl data gs (fst (snd args)) (snd (snd args)))"
  proof (induct arbitrary: data)
    fix x data
    assume IH': "\<And>y data'. (y, x) \<in> gb_schema_aux_term d \<Longrightarrow> fst y = gs \<Longrightarrow>
                   P data' (fst (snd y)) (snd (snd y)) (gb_schema_aux sel ap ab compl data' gs (fst (snd y)) (snd (snd y)))"
    assume "fst x = gs"
    then obtain bs0 where x: "x = (gs, bs0)" by (meson eq_fst_iff)
    obtain bs ps where bs0: "bs0 = (bs, ps)" by (meson case_prodE case_prodI2)
    from IH' have IH: "\<And>bs' ps' data'. ((gs, bs', ps'), (gs, bs, ps)) \<in> gb_schema_aux_term d \<Longrightarrow>
                   P data' bs' ps' (gb_schema_aux sel ap ab compl data' gs bs' ps')" unfolding x bs0 by auto
    show "P data (fst (snd x)) (snd (snd x))
              (gb_schema_aux sel ap ab compl data gs (fst (snd x)) (snd (snd x)))"
    proof (simp add: x bs0, cases "ps = []")
      case True
      from base show "P data bs ps (gb_schema_aux sel ap ab compl data gs bs ps)" by (simp add: True)
    next
      case False
      show "P data bs ps (gb_schema_aux sel ap ab compl data gs bs ps)"
      proof (simp add: gb_schema_aux_not_Nil[OF assms(1) False] Let_def case_prod_beta, intro conjI impI)
        define sps where "sps = sel gs bs ps data"
        assume "\<exists>h\<in>set (fst (compl gs bs (ps -- sps) sps data)). is_nonzero_const_monomial (fst h)"
        then obtain h where "h \<in> set (fst (compl gs bs (ps -- sps) sps data))"
          and "is_nonzero_const_monomial (fst h)" ..
        from this(1) have "fst h \<in> fst ` set (fst (compl gs bs (ps -- sps) sps data))" by simp
        also have "... = fst ` set (fst (add_indices (compl gs bs (ps -- sps) sps data) data))"
          by (simp only: fst_set_add_indices)
        finally obtain h' where "h' \<in> set (fst (add_indices (compl gs bs (ps -- sps) sps data) data))"
          and "fst h = fst h'" ..
        from False sps_def this(1) \<open>is_nonzero_const_monomial (fst h)\<close> show "P data bs ps [(1, 0, default)]"
          unfolding \<open>fst h = fst h'\<close> by (rule rec1)
      next
        define sps where "sps = sel gs bs ps data"
        define aux where "aux = compl gs bs (ps -- sps) sps data"
        define hs where "hs = fst (add_indices aux data)"
        define data' where "data' = snd (add_indices aux data)"
        assume a: "\<forall>h\<in>set (fst aux). \<not> is_nonzero_const_monomial (fst h)"
        have *: "h \<in> set hs \<Longrightarrow> \<not> is_nonzero_const_monomial (fst h)" for h
        proof -
          assume "h \<in> set hs"
          hence "fst h \<in> fst ` set hs" by simp
          also have "... = fst ` set (fst aux)" by (simp only: hs_def fst_set_add_indices)
          finally obtain h' where "h' \<in> set (fst aux)" and "fst h = fst h'" ..
          from a this(1) have "\<not> is_nonzero_const_monomial (fst h')" ..
          thus "\<not> is_nonzero_const_monomial (fst h)" by (simp add: \<open>fst h = fst h'\<close>)
        qed
        have "(hs, data') = add_indices (compl gs bs (ps -- sps) sps data) data"
          by (simp add: hs_def data'_def aux_def)
        with False sps_def
        show "P data bs ps (gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
        proof (rule rec2)
          fix h
          assume "h \<in> set hs"
          thus "\<not> is_nonzero_const_monomial (fst h)" by (rule *)
        next
          show "P data' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                    (gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
          proof (rule IH, simp add: x bs0 gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, rule)
            show "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs \<or>
                      ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
            proof (cases "hs = []")
              case True
              have "ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
              proof (simp only: True ap_spec_Nil_new[OF ap], rule)
                from ab show "ab gs bs [] data' = bs" by (rule ab_specD2)
              next
                from sel False have "sps \<noteq> []" and "set sps \<subseteq> set ps"
                  unfolding sps_def by (rule sel_specD1, rule sel_specD2)
                moreover from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
                ultimately have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
                hence "set (ps -- sps) \<subset> set ps" unfolding set_diff_list by fastforce
                thus "card (set (ps -- sps)) < card (set ps)" by (simp add: psubset_card_mono)
              qed
              thus ?thesis ..
            next
              case False
              with assms(1) \<open>ps \<noteq> []\<close> sps_def hs_def have "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs"
                unfolding aux_def by (rule struct_spec_red_supset)
              thus ?thesis ..
            qed
          next
            from dg assms(1) False sps_def hs_def
            show "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
              unfolding aux_def by (rule dgrad_p_set_le_args_to_set_struct)
          qed
        qed
      qed
    qed
  qed
  thus ?thesis by (simp add: args_def)
qed

lemma gb_schema_aux_dgrad_p_set_le:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) (args_to_set (gs, bs, ps))"
  using assms(2)
proof (induct rule: gb_schema_aux_induct)
  case (base bs data)
  thus ?case by (simp add: args_to_set_def, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (rec1 bs ps sps h data)
  define hs where "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  define data' where "data' = snd (add_indices (compl gs bs (ps -- sps) sps data) data)"
  from assms(2) have ab: "ab_spec ab" by (rule struct_specD)
  from rec1(3) have "fst h \<in> fst ` set hs" by (simp add: hs_def)
  hence "fst h \<in> fst ` set (ab gs bs hs data')" by (auto simp add: ab_specD1[OF ab])
  have "dgrad_p_set_le d {1} {fst h}"
  proof (simp add: dgrad_p_set_le_def Keys_insert, rule dgrad_set_leI, simp)
    from rec1(4) have "0 \<in> keys (fst h)" by (simp add: is_nonzero_const_monomial_alt_keys)
    moreover have "d 0 \<le> d 0" ..
    ultimately show "\<exists>t\<in>keys (fst h). d 0 \<le> d t" ..
  qed
  also have "dgrad_p_set_le d ... (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data'))"
    by (rule dgrad_p_set_le_subset, simp add: args_to_set_alt \<open>fst h \<in> fst ` set (ab gs bs hs data')\<close>)
  also from assms rec1(1, 2) hs_def
  have "dgrad_p_set_le d ... (args_to_set (gs, bs, ps))" by (rule dgrad_p_set_le_args_to_set_struct)
  finally show ?case by simp
next
  case (rec2 bs ps sps hs data data')
  from rec2(3) have "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)" by (metis fstI)
  with assms rec2(1, 2)
  have "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_args_to_set_struct)
  with rec2(5) show ?case by (rule dgrad_p_set_le_trans)
qed

lemma gb_schema_aux_pideal:
  assumes "struct_spec sel ap ab compl" and "compl_pideal compl" and "is_Groebner_basis (fst ` set gs)"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) data"
  shows "pideal (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) = pideal (fst ` set (gs @ bs))"
  using assms(1, 4, 5)
proof (induct bs ps rule: gb_schema_aux_induct)
  case (base bs data)
  show ?case ..
next
  case (rec1 bs ps sps h data)
  let ?ns = "fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  from rec1(3) have "fst h \<in> fst ` set ?ns" by simp
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3)
  from sel rec1(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding rec1(2) by (rule sel_specD1, rule sel_specD2)
  with assms(2, 3) have "fst ` set ?ns \<subseteq> pideal (args_to_set (gs, bs, ps))" using rec1.prems(2)
    unfolding fst_set_add_indices by (rule compl_pidealD)
  hence "fst ` set ?ns \<subseteq> pideal (fst ` (set (gs @ bs)))"
    by (simp add: args_to_set_subset_Times[OF rec1(5)] image_Un)
  with \<open>fst h \<in> fst ` set ?ns\<close> have "fst h \<in> pideal (fst ` (set (gs @ bs)))" ..
  from this rec1(4) have "pideal (fst ` (set (gs @ bs))) = UNIV"
    by (rule pideal_eq_UNIV_if_contains_nonzero_const_monomial)
  moreover have "pideal (fst ` set [(1::'a \<Rightarrow>\<^sub>0 'b, default::'c)]) = UNIV"
    by (simp add: ideal.generator_in_module ideal_eq_UNIV_iff_contains_one)
  ultimately show ?case by simp
next
  case (rec2 bs ps sps hs data data')
  from rec2(3) have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
    by (metis fstI)
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3)
  have "pideal (fst ` set (gb_schema_aux sel ap ab compl data' gs (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))) =
        pideal (fst ` set (gs @ ab gs bs hs data'))"
  proof (rule rec2(5))
    from ap ab rec2(6) show "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
      by (rule subset_Times_ap)
  next
    from ab rec2.prems(2) rec2(3) show "unique_idx (gs @ ab gs bs hs data') data'" by (rule unique_idx_ab)
  qed
  also have "... = pideal (fst ` set (gs @ bs))"
  proof -
    have eq: "fst ` (set gs \<union> set (ab gs bs hs data')) = fst ` (set gs \<union> set bs) \<union> fst ` set hs"
      by (auto simp add: ab_specD1[OF ab])
    show ?thesis
    proof (simp add: eq, rule)
      show "pideal (fst ` (set gs \<union> set bs) \<union> fst ` set hs) \<subseteq> pideal (fst ` (set gs \<union> set bs))"
      proof (rule ideal.module_subset_moduleI, simp only: Un_subset_iff, rule)
        show "fst ` (set gs \<union> set bs) \<subseteq> pideal (fst ` (set gs \<union> set bs))"
          by (fact ideal.generator_subset_module)
      next
        from sel rec2(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
          unfolding rec2(2) by (rule sel_specD1, rule sel_specD2)
        with assms(2, 3) have "fst ` set hs \<subseteq> pideal (args_to_set (gs, bs, ps))"
          unfolding hs fst_set_add_indices using rec2.prems(2) by (rule compl_pidealD)
        thus "fst ` set hs \<subseteq> pideal (fst ` (set gs \<union> set bs))"
          by (simp only: args_to_set_subset_Times[OF rec2(6)] image_Un)
      qed
    next
      show "pideal (fst ` (set gs \<union> set bs)) \<subseteq> pideal (fst ` (set gs \<union> set bs) \<union> fst ` set hs)"
        by (rule ideal.module_mono, blast)
    qed
  qed
  finally show ?case .
qed

lemma gb_schema_aux_connectible:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "dickson_grading (+) d"
    and "fst ` set gs \<subseteq> dgrad_p_set d m" and "is_Groebner_basis (fst ` set gs)"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)"
    and "unique_idx (gs @ bs) data"
    and "\<And>p q. processed (p, q) (gs @ bs) ps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)"
  assumes "f \<in> set (gb_schema_aux sel ap ab compl data gs bs ps)"
    and "g \<in> set (gb_schema_aux sel ap ab compl data gs bs ps)" and "fst f \<noteq> 0" and "fst g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` set (gb_schema_aux sel ap ab compl data gs bs ps)) (fst f) (fst g)"
  using assms(1, 6, 7, 8, 9, 10, 11)
proof (induct rule: gb_schema_aux_induct)
  case (base bs data)
  show ?case
  proof (cases "f \<in> set gs")
    case True
    show ?thesis
    proof (cases "g \<in> set gs")
      case True
      note assms(3, 4, 5)
      moreover from \<open>f \<in> set gs\<close> have "fst f \<in> fst ` set gs" by simp
      moreover from \<open>g \<in> set gs\<close> have "fst g \<in> fst ` set gs" by simp
      ultimately have "crit_pair_cbelow_on d m (fst ` set gs) (fst f) (fst g)"
        using assms(12, 13) by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
      moreover have "fst ` set gs \<subseteq> fst ` set (gs @ bs)" by auto
      ultimately show ?thesis by (rule crit_pair_cbelow_mono)
    next
      case False
      from this base(5, 6) have "processed (g, f) (gs @ bs) []" by (simp add: processed_Nil)
      from this \<open>fst g \<noteq> 0\<close> \<open>fst f \<noteq> 0\<close> have "crit_pair_cbelow_on d m (fst ` set (gs @ bs)) (fst g) (fst f)"
        unfolding set_append by (rule base(4))
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  next
    case False
    from this base(5, 6) have "processed (f, g) (gs @ bs) []" by (simp add: processed_Nil)
    from this \<open>fst f \<noteq> 0\<close> \<open>fst g \<noteq> 0\<close> show ?thesis unfolding set_append by (rule base(4))
  qed
next
  case (rec1 bs ps sps h data)
  define hs where "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  define data' where "data' = snd (add_indices (compl gs bs (ps -- sps) sps data) data)"
  from rec1(9, 10) have "fst f = 1" and "fst g = 1" by simp_all
  from assms(1) have ab: "ab_spec ab" by (rule struct_specD)
  from rec1(3) have "fst h \<in> fst ` set hs" by (simp add: hs_def)
  hence "fst h \<in> fst ` set (ab gs bs hs data')" by (auto simp add: ab_specD1[OF ab])
  have "dgrad_p_set_le d {1} {fst h}"
  proof (simp add: dgrad_p_set_le_def Keys_insert, rule dgrad_set_leI, simp)
    from rec1(4) have "0 \<in> keys (fst h)" by (simp add: is_nonzero_const_monomial_alt_keys)
    moreover have "d 0 \<le> d 0" ..
    ultimately show "\<exists>t\<in>keys (fst h). d 0 \<le> d t" ..
  qed
  also have "dgrad_p_set_le d ... (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data'))"
    by (rule dgrad_p_set_le_subset, simp add: args_to_set_alt \<open>fst h \<in> fst ` set (ab gs bs hs data')\<close>)
  also from assms(3, 1) rec1(1, 2) hs_def
  have "dgrad_p_set_le d ... (args_to_set (gs, bs, ps))" by (rule dgrad_p_set_le_args_to_set_struct)
  also have "dgrad_p_set_le d ... (fst ` set gs \<union> fst ` set bs)"
    by (rule dgrad_p_set_le_subset, simp add: args_to_set_subset_Times[OF rec1(6)])
  finally have "dgrad_p_set_le d {1} (fst ` set gs \<union> fst ` set bs)" .
  moreover from assms(4) rec1(5) have "... \<subseteq> dgrad_p_set d m" by simp
  ultimately have "{1::'a \<Rightarrow>\<^sub>0 'b} \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_le_dgrad_p_set)
  hence "(1::'a \<Rightarrow>\<^sub>0 'b) \<in> dgrad_p_set d m" by simp
  with assms(3) show ?case unfolding \<open>fst f = 1\<close> \<open>fst g = 1\<close> by (rule crit_pair_cbelow_same)
next
  case (rec2 bs ps sps hs data data')
  from rec2(3) have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)" by (metis fstI)
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from sel rec2(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding rec2(2) by (rule sel_specD1, rule sel_specD2)
  from ap ab rec2(7) have ap_sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq>
                                    set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  have ns_sub: "fst ` set hs \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from compl assms(3) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
    show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
      unfolding hs fst_set_add_indices by (rule compl_structD1)
  next
    from assms(4) rec2(6) show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF rec2(7)])
  qed
  with rec2(6) have ab_sub: "fst ` set (ab gs bs hs data') \<subseteq> dgrad_p_set d m"
    by (auto simp add: ab_specD1[OF ab])

  have cpq: "(p, q) \<in> set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)" for p q
  proof -
    assume "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    with assms(2, 3, 4, 5) rec2(6, 7) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> rec2.prems(3) _
    have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data)))
            (fst p) (fst q)"
    proof (rule compl_connD)
      fix p' q'
      assume "processed (p', q') (gs @ bs) ps" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
        by (rule rec2(9))
    qed
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)"
      by (simp add: ab_specD1[OF ab] hs fst_set_add_indices image_Un Un_assoc)
  qed

  from ab_sub ap_sub _ _ rec2(10, 11) show ?case
  proof (rule rec2(5))
    from ab rec2.prems(3) rec2(3) show "unique_idx (gs @ ab gs bs hs data') data'" by (rule unique_idx_ab)
  next
    fix p q :: "('a, 'b, 'c) pdata"
    assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
    assume proc: "processed (p, q) (gs @ (ab gs bs hs data')) (ap gs bs (ps -- sps) hs data')"
    with ap ab show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)"
    proof (rule processed_apE)
      assume "processed (p, q) (gs @ bs) (ps -- sps)"
      thus ?thesis
      proof (rule processed_minus)
        assume "(p, q) \<in> set sps"
        from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show ?thesis by (rule cpq)
      next
        assume "(q, p) \<in> set sps"
        from this \<open>fst q \<noteq> 0\<close> \<open>fst p \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst q) (fst p)"
          by (rule cpq)
        thus ?thesis by (rule crit_pair_cbelow_sym)
      next
        assume "processed (p, q) (gs @ bs) ps"
        from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)" by (rule rec2(9))
        moreover have "fst ` (set gs \<union> set bs) \<subseteq> fst ` (set gs \<union> set (ab gs bs hs data'))"
          by (auto simp add: ab_specD1[OF ab])
        ultimately show ?thesis by (rule crit_pair_cbelow_mono)
      qed
    next
      assume "p \<in> set hs" and "q \<in> set hs"
      show ?thesis
      proof (cases "p = q")
        case True
        from \<open>q \<in> set hs\<close> have "fst q \<in> fst ` set hs" by simp
        from this ns_sub have "fst q \<in> dgrad_p_set d m" ..
        with assms(3) show ?thesis unfolding True by (rule crit_pair_cbelow_same)
      next
        case False
        with ap \<open>p \<in> set hs\<close> \<open>q \<in> set hs\<close>
        have "\<not> processed (p, q) (gs @ (ab gs bs hs data')) (ap gs bs (ps -- sps) hs data')"
        proof (rule ap_specE)
          assume "(p, q) \<in> set (ap gs bs (ps -- sps) hs data')"
          thus ?thesis by (simp add: processed_def)
        next
          assume "(q, p) \<in> set (ap gs bs (ps -- sps) hs data')"
          thus ?thesis by (simp add: processed_def)
        qed
        from this proc show ?thesis ..
      qed
    qed
  qed
qed

lemma gb_schema_aux_dgrad_p_set_le_init:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data)))
                          (fst ` (set gs \<union> set bs))"
proof -
  let ?bs = "ab gs [] bs data"
  from assms(2) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ap_specD1[OF ap, of gs "[]" "[]" bs] have *: "set (ap gs [] [] bs data) \<subseteq> set ?bs \<times> (set gs \<union> set ?bs)"
    by (simp add: ab_specD1[OF ab])
  from assms
  have "dgrad_p_set_le d
         (fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data)))
         (args_to_set (gs, (ab gs [] bs data), (ap gs [] [] bs data)))"
    by (rule gb_schema_aux_dgrad_p_set_le)
  also have "... = fst ` (set gs \<union> set bs)"
    by (simp add: args_to_set_subset_Times[OF *] image_Un ab_specD1[OF ab])
  finally show ?thesis .
qed

lemma gb_schema_aux_dgrad_p_set_init:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
    and "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data)) \<subseteq> dgrad_p_set d m"
proof (rule dgrad_p_set_le_dgrad_p_set)
  from assms(1, 2)
  show "dgrad_p_set_le d
          (fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data)))
          (fst ` (set gs \<union> set bs))"
    by (rule gb_schema_aux_dgrad_p_set_le_init)
qed fact

lemma gb_schema_aux_pideal_init:
  assumes "struct_spec sel ap ab compl" and "compl_pideal compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ ab gs [] bs data) data"
  shows "pideal (fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data))) =
          pideal (fst ` (set (gs @ bs)))" (is "?l = ?r")
proof -
  from assms(1) have ab: "ab_spec ab" by (rule struct_specD3) 
  from assms(1, 2, 3) _ assms(4) have "?l = pideal (fst ` (set (gs @ (ab gs [] bs data))))"
  proof (rule gb_schema_aux_pideal)
    from assms(1) have "ap_spec ap" by (rule struct_specD2)
    from ap_specD1[OF this, of gs "[]" "[]" bs]
    show "set (ap gs [] [] bs data) \<subseteq> set (ab gs [] bs data) \<times> (set gs \<union> set (ab gs [] bs data))"
      by (simp add: ab_specD1[OF ab])
  qed
  also have "... = ?r" by (simp add: ab_specD1[OF ab])
  finally show ?thesis .
qed

lemma gb_schema_aux_isGB_init:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ ab gs [] bs data) data"
  shows "is_Groebner_basis (fst ` set (gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data)))"
proof -
  let ?res = "gb_schema_aux sel ap ab compl data gs (ab gs [] bs data) (ap gs [] [] bs data)"
  from assms(1) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD2, rule struct_specD3)
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  have "finite (fst ` (set gs \<union> set bs))" by (rule, rule finite_UnI, fact finite_set, fact finite_set)
  then obtain m where "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  with dg assms(1) have "fst ` set ?res \<subseteq> dgrad_p_set d m"
    by (rule gb_schema_aux_dgrad_p_set_init)
  with dg show ?thesis
  proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
    fix p0 q0
    assume p0_in: "p0 \<in> fst ` set ?res" and q0_in: "q0 \<in> fst ` set ?res"
    assume "p0 \<noteq> 0" and "q0 \<noteq> 0"
    from \<open>fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m\<close>
    have "fst ` set gs \<subseteq> dgrad_p_set d m" and "fst ` set bs \<subseteq> dgrad_p_set d m"
      by (simp_all add: image_Un)
    from p0_in obtain p where p_in: "p \<in> set ?res" and p0: "p0 = fst p" ..
    from q0_in obtain q where q_in: "q \<in> set ?res" and q0: "q0 = fst q" ..
    from assms(1, 2) dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(3) _ _ assms(4) _ p_in q_in \<open>p0 \<noteq> 0\<close> \<open>q0 \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` set ?res) p0 q0" unfolding p0 q0
    proof (rule gb_schema_aux_connectible)
      from \<open>fst ` set bs \<subseteq> dgrad_p_set d m\<close> show "fst ` set (ab gs [] bs data) \<subseteq> dgrad_p_set d m"
        by (simp add: ab_specD1[OF ab])
    next
      from ap_specD1[OF ap, of gs "[]" "[]" bs]
      show "set (ap gs [] [] bs data) \<subseteq> set (ab gs [] bs data) \<times> (set gs \<union> set (ab gs [] bs data))"
        by (simp add: ab_specD1[OF ab])
    next
      fix p' q'
      assume "processed (p', q') (gs @ ab gs [] bs data) (ap gs [] [] bs data)"
      hence proc: "processed (p', q') (gs @ bs) (ap gs [] [] bs data)"
        by (simp add: processed_alt ab_specD1[OF ab])
      hence "p' \<in> set gs \<union> set bs" and "q' \<in> set gs \<union> set bs" by (auto dest: processedD1 processedD2)
      assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
      proof (cases "p' = q'")
        case True
        from dg show ?thesis unfolding True
        proof (rule crit_pair_cbelow_same)
          from \<open>q' \<in> set gs \<union> set bs\<close> have "fst q' \<in> fst ` (set gs \<union> set bs)" by simp
          from this \<open>fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m\<close> show "fst q' \<in> dgrad_p_set d m" ..
        qed
      next
        case False
        from ap_specD2[OF ap, of "[]" bs gs "[]" data]
        have sub: "set bs \<times> set gs \<subseteq> set (ap gs [] [] bs data)" by simp
        from \<open>p' \<in> set gs \<union> set bs\<close> show ?thesis
        proof
          assume "p' \<in> set gs"
          from \<open>q' \<in> set gs \<union> set bs\<close> show ?thesis
          proof
            assume "q' \<in> set gs"
            note dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(3)
            moreover from \<open>p' \<in> set gs\<close> have "fst p' \<in> fst ` set gs" by simp
            moreover from \<open>q' \<in> set gs\<close> have "fst q' \<in> fst ` set gs" by simp
            ultimately have "crit_pair_cbelow_on d m (fst ` set gs) (fst p') (fst q')"
              using \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
            moreover have "fst ` set gs \<subseteq> fst ` (set gs \<union> set bs)" by blast
            ultimately show ?thesis by (rule crit_pair_cbelow_mono)
          next
            assume "q' \<in> set bs"
            from this \<open>p' \<in> set gs\<close> have "(q', p') \<in> set bs \<times> set gs" ..
            with sub have "(q', p') \<in> set (ap gs [] [] bs data)" ..
            hence "\<not> processed (p', q') (gs @ bs) (ap gs [] [] bs data)"
              by (simp add: processed_alt)
            from this proc show ?thesis ..
          qed
        next
          assume "p' \<in> set bs"
          from \<open>q' \<in> set gs \<union> set bs\<close> show ?thesis
          proof
            assume "q' \<in> set gs"
            with \<open>p' \<in> set bs\<close> have "(p', q') \<in> set bs \<times> set gs" ..
            with sub have "(p', q') \<in> set (ap gs [] [] bs data)" ..
            hence "\<not> processed (p', q') (gs @ bs) (ap gs [] [] bs data)"
              by (simp add: processed_alt)
            from this proc show ?thesis ..
          next
            assume "q' \<in> set bs"
            from ap \<open>p' \<in> set bs\<close> this False
            have "\<not> processed (p', q') (gs @ bs) (ap gs [] [] bs data)"
            proof (rule ap_specE)
              assume "(p', q') \<in> set (ap gs [] [] bs data)"
              thus ?thesis by (simp add: processed_alt)
            next
              assume "(q', p') \<in> set (ap gs [] [] bs data)"
              thus ?thesis by (simp add: processed_alt)
            qed
            from this proc show ?thesis ..
          qed
        qed
      qed
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs [] bs data))) (fst p') (fst q')"
        by (simp add: ab_specD1[OF ab])
    qed
  qed
qed

subsubsection \<open>Functions @{term gb_schema_direct} and @{term gb_schema_incr}\<close>

definition gb_schema_direct :: "('a, 'b, 'c, 'd) selT \<Rightarrow> ('a, 'b, 'c, 'd) apT \<Rightarrow> ('a, 'b, 'c, 'd) abT \<Rightarrow>
                                ('a, 'b, 'c, 'd) complT \<Rightarrow> ('a, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow>
                                ('a, 'b::field, 'c::default) pdata' list"
  where "gb_schema_direct sel ap ab compl bs0 data0 =
            (let data = (length bs0, data0); bs = fst (add_indices (bs0, data0) (0, data0)) in
              map (\<lambda>(f, _, d). (f, d))
                    (gb_schema_aux sel ap ab compl data [] (ab [] [] bs data) (ap [] [] [] bs data))
            )"

primrec gb_schema_incr :: "('a, 'b, 'c, 'd) selT \<Rightarrow> ('a, 'b, 'c, 'd) apT \<Rightarrow> ('a, 'b, 'c, 'd) abT \<Rightarrow>
                                ('a, 'b, 'c, 'd) complT \<Rightarrow>
                                (('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
                                ('a, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('a, 'b::field, 'c::default) pdata' list"
  where
    "gb_schema_incr _ _ _ _ _ [] _ = []"|
    "gb_schema_incr sel ap ab compl upd (b0 # bs) data =
      (let (gs, n, data') = add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data);
           b = (fst b0, n, snd b0); data'' = upd gs b data' in
        map (\<lambda>(f, _, d). (f, d))
          (gb_schema_aux sel ap ab compl (Suc n, data'') gs (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))
      )"

lemma (in -) fst_set_drop_indices:
  "fst ` (\<lambda>(f, _, d). (f, d)) ` A = fst ` A" for A::"('x \<times> 'y \<times> 'z) set"
  by (simp add: image_image, rule image_cong, fact refl, simp add: prod.case_eq_if)

lemma fst_gb_schema_direct:
  "fst ` set (gb_schema_direct sel ap ab compl bs0 data0) =
      (let data = (length bs0, data0); bs = fst (add_indices (bs0, data0) (0, data0)) in
        fst ` set (gb_schema_aux sel ap ab compl data [] (ab [] [] bs data) (ap [] [] [] bs data))
      )"
  by (simp add: gb_schema_direct_def Let_def fst_set_drop_indices)

lemma gb_schema_direct_dgrad_p_set:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl" and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_direct sel ap ab compl bs data) \<subseteq> dgrad_p_set d m"
  unfolding fst_gb_schema_direct Let_def using assms(1, 2)
proof (rule gb_schema_aux_dgrad_p_set_init)
  show "fst ` (set [] \<union> set (fst (add_indices (bs, data) (0, data)))) \<subseteq> dgrad_p_set d m"
    using assms(3) by (simp add: image_Un fst_set_add_indices)
qed

theorem gb_schema_direct_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_direct sel ap ab compl bs data))"
  unfolding fst_gb_schema_direct Let_def using assms
proof (rule gb_schema_aux_isGB_init)
  from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
next
  let ?data = "(length bs, data)"
  from assms(1) have "ab_spec ab" by (rule struct_specD)
  moreover have "unique_idx ([] @ []) (0, data)" by (simp add: unique_idx_Nil)
  ultimately show "unique_idx ([] @ ab [] [] (fst (add_indices (bs, data) (0, data))) ?data) ?data"
  proof (rule unique_idx_ab)
    show "(fst (add_indices (bs, data) (0, data)), length bs, data) = add_indices (bs, data) (0, data)"
      by (simp add: add_indices_def)
  qed
qed

theorem gb_schema_direct_pideal:
  assumes "struct_spec sel ap ab compl" and "compl_pideal compl"
  shows "pideal (fst ` set (gb_schema_direct sel ap ab compl bs data)) = pideal (fst ` set bs)"
proof -
  have "pideal (fst ` set (gb_schema_direct sel ap ab compl bs data)) =
          pideal (fst ` set ([] @ (fst (add_indices (bs, data) (0, data)))))"
    unfolding fst_gb_schema_direct Let_def using assms
  proof (rule gb_schema_aux_pideal_init)
    from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
  next
    let ?data = "(length bs, data)"
    from assms(1) have "ab_spec ab" by (rule struct_specD)
    moreover have "unique_idx ([] @ []) (0, data)" by (simp add: unique_idx_Nil)
    ultimately show "unique_idx ([] @ ab [] [] (fst (add_indices (bs, data) (0, data))) ?data) ?data"
    proof (rule unique_idx_ab)
      show "(fst (add_indices (bs, data) (0, data)), length bs, data) = add_indices (bs, data) (0, data)"
        by (simp add: add_indices_def)
    qed
  qed
  thus ?thesis by (simp add: fst_set_add_indices)
qed

lemma fst_gb_schema_incr:
  "fst ` set (gb_schema_incr sel ap ab compl upd (b0 # bs) data) =
      (let (gs, n, data') = add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data);
            b = (fst b0, n, snd b0); data'' = upd gs b data' in
        fst ` set (gb_schema_aux sel ap ab compl (Suc n, data'') gs (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))
      )"
  by (simp only: gb_schema_incr.simps Let_def prod.case_distrib[of set]
        prod.case_distrib[of "image fst"] set_map fst_set_drop_indices)

lemma gb_schema_incr_dgrad_p_set:
  assumes "dickson_grading (+) d" and "struct_spec sel ap ab compl"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_incr sel ap ab compl upd bs data) \<subseteq> dgrad_p_set d m"
  using assms(3)
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b0 bs)
  from Cons(2) have 1: "fst b0 \<in> dgrad_p_set d m" and 2: "fst ` set bs \<subseteq> dgrad_p_set d m" by simp_all
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1, 2)
    show "fst ` set (gb_schema_aux sel ap ab compl (Suc n, data'') gs (ab gs [] [b] (Suc n, data''))
                (ap gs [] [] [b] (Suc n, data''))) \<subseteq> dgrad_p_set d m"
    proof (rule gb_schema_aux_dgrad_p_set_init)
      from 1 Cons(1)[OF 2] show "fst ` (set gs \<union> set [b]) \<subseteq> dgrad_p_set d m"
        by (simp add: gs fst_set_add_indices b_def)
    qed
  qed
qed

theorem gb_schema_incr_dgrad_p_set_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_incr sel ap ab compl upd bs data))"
proof (induct bs)
  case Nil
  from is_Groebner_basis_empty show ?case by simp
next
  case (Cons b0 bs)
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume *: "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from Cons have "is_Groebner_basis (fst ` set gs)" by (simp add: gs fst_set_add_indices)
    with assms
    show "is_Groebner_basis (fst ` set (gb_schema_aux sel ap ab compl (Suc n, data'') gs
                                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data''))))"
    proof (rule gb_schema_aux_isGB_init)
      from assms(1) have "ab_spec ab" by (rule struct_specD3)
      thus "unique_idx (gs @ ab gs [] [b] (Suc n, data'')) (Suc n, data'')"
      proof (rule unique_idx_ab)
        from unique_idx_Nil *[symmetric] have "unique_idx ([] @ gs) (n, data')"
          by (rule unique_idx_append)
        thus "unique_idx (gs @ []) (n, data')" by simp
      next
        show "([b], Suc n, data'') = add_indices ([b0], data'') (n, data')"
          by (simp add: add_indices_def b_def)
      qed
    qed
  qed
qed

theorem gb_schema_incr_pideal:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" "compl_pideal compl"
  shows "pideal (fst ` set (gb_schema_incr sel ap ab compl upd bs data)) = pideal (fst ` set bs)"
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b0 bs)
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume *: "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1, 2) have "is_Groebner_basis (fst ` set gs)" unfolding gs fst_conv fst_set_add_indices
      by (rule gb_schema_incr_dgrad_p_set_isGB)
    with assms(1, 3)
    have eq: "pideal (fst ` set (gb_schema_aux sel ap ab compl (Suc n, data'') gs
                          (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))) =
              pideal (fst ` set (gs @ [b]))"
    proof (rule gb_schema_aux_pideal_init)
      from assms(1) have "ab_spec ab" by (rule struct_specD3)
      thus "unique_idx (gs @ ab gs [] [b] (Suc n, data'')) (Suc n, data'')"
      proof (rule unique_idx_ab)
        from unique_idx_Nil *[symmetric] have "unique_idx ([] @ gs) (n, data')"
          by (rule unique_idx_append)
        thus "unique_idx (gs @ []) (n, data')" by simp
      next
        show "([b], Suc n, data'') = add_indices ([b0], data'') (n, data')"
          by (simp add: add_indices_def b_def)
      qed
    qed
    also have "... = pideal (insert (fst b) (fst ` set gs))" by simp
    also from Cons have "... = pideal (insert (fst b) (fst ` set bs))"
      unfolding gs fst_conv fst_set_add_indices by (rule ideal.module_insert_cong)
    finally show "pideal (fst ` set (gb_schema_aux sel ap ab compl (Suc n, data'') gs
                              (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))) =
                  pideal (insert (fst b0) (fst ` set bs))" by (simp add: b_def)
  qed
qed

subsection \<open>Suitable Instances of the @{emph \<open>completion\<close>} Parameter\<close>

subsubsection \<open>Specification of the @{emph \<open>crit\<close>} parameter\<close>

type_synonym (in -) ('a, 'b, 'c, 'd) critT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                          ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow>
                                          ('a, 'b, 'c) pdata \<Rightarrow> bool"

definition crit_spec :: "('a, 'b::field, 'c, 'd) critT \<Rightarrow> bool"
  where "crit_spec crit \<longleftrightarrow>
            (\<forall>d m gs bs ps F data p q. dickson_grading (+) d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
              is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
              F \<subseteq> dgrad_p_set d m \<longrightarrow> set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> unique_idx (gs @ bs) data \<longrightarrow>
              (\<forall>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')) \<longrightarrow>
              p \<in> set bs \<longrightarrow> q \<in> set gs \<union> set bs \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow> crit gs bs ps data p q \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q))"

text \<open>Informally, @{term "crit_spec crit"} expresses that @{term crit} is a predicate such that
  whenever @{term "crit gs bs ps p q"} holds (for suitable arguments @{term gs}, @{term bs},
  @{term ps}, @{term p} and @{term q}), then the critical pair of polynomials @{term p} and
  @{term q} is connectible modulo any superset @{term G} of @{term "set gs \<union> set bs"}, provided
  that the critical pairs of all polynomials that have been processed already are connectible
  modulo @{term G}.\<close>

lemma crit_specI:
  assumes "\<And>d m gs bs ps F data p q. dickson_grading (+) d \<Longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<Longrightarrow>
              is_Groebner_basis (fst ` set gs) \<Longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<Longrightarrow>
              F \<subseteq> dgrad_p_set d m \<Longrightarrow> set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> unique_idx (gs @ bs) data \<Longrightarrow>
              (\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')) \<Longrightarrow>
              p \<in> set bs \<Longrightarrow> q \<in> set gs \<union> set bs \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow> crit gs bs ps data p q \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  shows "crit_spec crit"
  unfolding crit_spec_def using assms by meson

lemma crit_specD:
  assumes "crit_spec crit" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) data"
    and "\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "p \<in> set bs" and "q \<in> set gs \<union> set bs" and "fst p \<noteq> 0" and "fst q \<noteq> 0" and "crit gs bs ps data p q"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  using assms unfolding crit_spec_def by blast

subsubsection \<open>Suitable Instances of the @{emph \<open>crit\<close>} parameter: chain criterion and product criterion\<close>

definition product_crit :: "('a, 'b::zero, 'c, 'd) critT"
  where "product_crit gs bs ps data p q \<longleftrightarrow> (gcs (lp (fst p)) (lp (fst q)) = 0)"

lemma crit_spec_product_crit: "crit_spec product_crit"
proof (rule crit_specI)
  fix d m gs bs ps and F::"('a \<Rightarrow>\<^sub>0 'b) set" and data::"nat \<times> 'd" and p q::"('a, 'b, 'c) pdata"
  assume "product_crit gs bs ps data p q"
  hence *: "gcs (lp (fst p)) (lp (fst q)) = 0" by (simp only: product_crit_def)
  assume gs: "fst ` set gs \<subseteq> dgrad_p_set d m" and bs: "fst ` set bs \<subseteq> dgrad_p_set d m"
    and F: "F \<subseteq> dgrad_p_set d m" and "p \<in> set bs" and "q \<in> set gs \<union> set bs"
  assume "dickson_grading (+) d"
  moreover from gs bs F have "fst ` (set gs \<union> set bs) \<union> F \<subseteq> dgrad_p_set d m" (is "?F \<subseteq> _")
    by (simp add: image_Un)
  moreover from \<open>p \<in> set bs\<close> have "fst p \<in> ?F" by simp
  moreover from \<open>q \<in> set gs \<union> set bs\<close> have "fst q \<in> ?F" by simp
  moreover assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
  ultimately show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
    using * by (rule product_criterion)
qed

fun (in -) pairs_not_in_list :: "('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "pairs_not_in_list [] _ _ _ = True"|
  "pairs_not_in_list (((_, (a, _)), (_, (b, _))) # ps) i j k =
    (if a = k then
      if b = i \<or> b = j then False else pairs_not_in_list ps i j k
    else if b = k then
      if a = i \<or> a = j then False else pairs_not_in_list ps i j k
    else
      pairs_not_in_list ps i j k
    )"

lemma (in -) pairs_not_in_listD:
  assumes "pairs_not_in_list ps i j k" and "(p, q) \<in> set ps"
  shows "(fst (snd p), fst (snd q)) \<noteq> (i, k) \<and> (fst (snd p), fst (snd q)) \<noteq> (k, i) \<and>
         (fst (snd p), fst (snd q)) \<noteq> (j, k) \<and> (fst (snd p), fst (snd q)) \<noteq> (k, j)"
  using assms
proof (induct i j k rule: pairs_not_in_list.induct)
  case (1 uu uv uw)
  from 1(2) show ?case by simp
next
  case (2 ux a uy uz b va ps i j k)
  from 2(4) have a: "a = k \<Longrightarrow> \<not> (b = i \<or> b = j)" and b: "a \<noteq> k \<Longrightarrow> b = k \<Longrightarrow> \<not> (a = i \<or> a = j)"
    and *: "pairs_not_in_list ps i j k" by (simp_all split: if_split_asm)
  from 2(5) have "(p, q) = ((ux, a, uy), (uz, b, va)) \<or> (p, q) \<in> set ps" by simp
  thus ?case
  proof
    assume "(p, q) = ((ux, a, uy), (uz, b, va))"
    hence p: "fst (snd p) = a" and q: "fst (snd q) = b" by auto
    from a b show ?thesis unfolding p q by blast
  next
    assume "(p, q) \<in> set ps"
    show ?thesis
    proof (cases "a = k")
      case True
      moreover from True have "\<not> (b = i \<or> b = j)" by (rule a)
      ultimately show ?thesis using * \<open>(p, q) \<in> set ps\<close> by (rule 2(1))
    next
      case False
      show ?thesis
      proof (cases "b = k")
        note False
        moreover assume "b = k"
        moreover from False this have "\<not> (a = i \<or> a = j)" by (rule b)
        ultimately show ?thesis using * \<open>(p, q) \<in> set ps\<close> by (rule 2(2))
      next
        note False
        moreover assume "b \<noteq> k"
        ultimately show ?thesis using * \<open>(p, q) \<in> set ps\<close> by (rule 2(3))
      qed
    qed
  qed
qed

definition chain_crit :: "('a, 'b::zero, 'c, 'd) critT"
  where "chain_crit gs bs ps data p q \<longleftrightarrow>
          (let l = lcs (lp (fst p)) (lp (fst q)); i = fst (snd p); j = fst (snd q) in
            (\<exists>r\<in>set (gs @ bs). let k = fst (snd r) in
                  k \<noteq> i \<and> k \<noteq> j \<and> lp (fst r) adds l \<and> pairs_not_in_list ps i j k \<and> fst r \<noteq> 0)
          )"

text \<open>@{const product_crit} and @{const chain_crit} ignore the @{term data} parameter.\<close>

lemma chain_critE:
  assumes "chain_crit gs bs ps data p q" and "p \<in> set bs" and "q \<in> set gs \<union> set bs"
  obtains r where "r \<in> set (gs @ bs)" and "fst r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and "lp (fst r) adds lcs (lp (fst p)) (lp (fst q))"
    and "processed (p, r) (gs @ bs) ps" and "processed (r, q) (gs @ bs) ps"
proof -
  let ?l = "lcs (lp (fst p)) (lp (fst q))"
  from assms(1) obtain r where "r \<in> set (gs @ bs)" and "fst r \<noteq> 0" and rp: "fst (snd r) \<noteq> fst (snd p)"
    and rq: "fst (snd r) \<noteq> fst (snd q)" and "lp (fst r) adds ?l"
    and *: "pairs_not_in_list ps (fst (snd p)) (fst (snd q)) (fst (snd r))"
    unfolding chain_crit_def Let_def by blast
  from rp have "r \<noteq> p" by auto
  from rq have "r \<noteq> q" by auto
  from \<open>r \<in> set (gs @ bs)\<close> \<open>fst r \<noteq> 0\<close> \<open>r \<noteq> p\<close> \<open>r \<noteq> q\<close> \<open>lp (fst r) adds ?l\<close> show ?thesis
  proof
    from assms(2) have "p \<in> set (gs @ bs)" by simp
    moreover note \<open>r \<in> set (gs @ bs)\<close>
    moreover have "(p, r) \<notin> set ps"
    proof
      assume "(p, r) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    moreover have "(r, p) \<notin> set ps"
    proof
      assume "(r, p) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    ultimately show "processed (p, r) (gs @ bs) ps" by (rule processedI)
  next
    note \<open>r \<in> set (gs @ bs)\<close>
    moreover from assms(3) have "q \<in> set (gs @ bs)" by simp
    moreover have "(r, q) \<notin> set ps"
    proof
      assume "(r, q) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    moreover have "(q, r) \<notin> set ps"
    proof
      assume "(q, r) \<in> set ps"
      from pairs_not_in_listD[OF * this] show False by simp
    qed
    ultimately show "processed (r, q) (gs @ bs) ps" by (rule processedI)
  qed
qed

text \<open>For proving the following lemma, @{const unique_idx} is not needed at all.\<close>

lemma crit_spec_chain_crit: "crit_spec chain_crit"
proof (rule crit_specI)
  fix d m gs bs ps F and data::"nat \<times> 'd" and p q::"('a, 'b, 'c) pdata"
  assume dg: "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "fst ` set bs \<subseteq> dgrad_p_set d m" and "F \<subseteq> dgrad_p_set d m"
    and *: "\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
           crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  assume "chain_crit gs bs ps data p q" and "p \<in> set bs" and "q \<in> set gs \<union> set bs"
  then obtain r where "fst r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and adds: "lp (fst r) adds lcs (lp (fst p)) (lp (fst q))"
    and "processed (p, r) (gs @ bs) ps" and "processed (r, q) (gs @ bs) ps" by (rule chain_critE)
  define G where "G = fst ` (set gs \<union> set bs) \<union> F"
  note dg
  moreover have "G \<subseteq> dgrad_p_set d m" unfolding G_def image_Un by (intro Un_least, fact+)
  moreover from \<open>p \<in> set bs\<close> \<open>q \<in> set gs \<union> set bs\<close> have "fst p \<in> G" and "fst q \<in> G"
    by (simp_all add: G_def)
  ultimately show "crit_pair_cbelow_on d m G (fst p) (fst q)"
    using \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> adds
  proof (rule chain_criterion)
    from \<open>processed (p, r) (gs @ bs) ps\<close> have "processed (p, r) (gs @ bs) ((p, q) # ps)"
    proof (rule processed_Cons)
      assume "r = q"
      with \<open>r \<noteq> q\<close> show ?thesis ..
    next
      assume "r = p"
      with \<open>r \<noteq> p\<close> show ?thesis ..
    qed
    from this \<open>fst p \<noteq> 0\<close> \<open>fst r \<noteq> 0\<close> show "crit_pair_cbelow_on d m G (fst p) (fst r)"
      unfolding G_def by (rule *)
  next
    from \<open>processed (r, q) (gs @ bs) ps\<close> have "processed (r, q) (gs @ bs) ((p, q) # ps)"
    proof (rule processed_Cons)
      assume "r = p"
      with \<open>r \<noteq> p\<close> show ?thesis ..
    next
      assume "r = q"
      with \<open>r \<noteq> q\<close> show ?thesis ..
    qed
    from this \<open>fst r \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show "crit_pair_cbelow_on d m G (fst r) (fst q)"
      unfolding G_def by (rule *)
  qed
qed

definition comb_crit :: "('a, 'b::zero, 'c, 'd) critT \<Rightarrow> ('a, 'b, 'c, 'd) critT \<Rightarrow> ('a, 'b, 'c, 'd) critT"
  where "comb_crit c1 c2 gs bs ps data p q \<longleftrightarrow> (c1 gs bs ps data p q \<or> c2 gs bs ps data p q)"

lemma crit_spec_comb_crit:
  assumes "crit_spec c1" and "crit_spec c2"
  shows "crit_spec (comb_crit c1 c2)"
proof (rule crit_specI)
  fix d m gs bs ps and F::"('a \<Rightarrow>\<^sub>0 'b) set" and data::"nat \<times> 'd" and p q::"('a, 'b, 'c) pdata"
  assume 1: "dickson_grading (+) d" and 2: "fst ` set gs \<subseteq> dgrad_p_set d m"
    and 3: "is_Groebner_basis (fst ` set gs)" and 4: "fst ` set bs \<subseteq> dgrad_p_set d m"
    and 5: "F \<subseteq> dgrad_p_set d m" and 6: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and 7: "unique_idx (gs @ bs) data"
    and 8: "\<And>p' q'. processed (p', q') (gs @ bs) ((p, q) # ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and 9: "p \<in> set bs" and 10: "q \<in> set gs \<union> set bs" and 11: "fst p \<noteq> 0" and 12: "fst q \<noteq> 0"
  assume "comb_crit c1 c2 gs bs ps data p q"
  hence "c1 gs bs ps data p q \<or> c2 gs bs ps data p q" by (simp only: comb_crit_def)
  thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  proof
    assume "c1 gs bs ps data p q"
    with assms(1) 1 2 3 4 5 6 7 8 9 10 11 12 show ?thesis by (rule crit_specD)
  next
    assume "c2 gs bs ps data p q"
    with assms(2) 1 2 3 4 5 6 7 8 9 10 11 12 show ?thesis by (rule crit_specD)
  qed
qed

definition pc_crit :: "('a, 'b::zero, 'c, 'd) critT"
  where "pc_crit = comb_crit product_crit chain_crit"

corollary crit_spec_pc_crit: "crit_spec pc_crit"
  by (simp only: pc_crit_def, rule crit_spec_comb_crit, fact crit_spec_product_crit, fact crit_spec_chain_crit)

subsubsection \<open>Function @{term discard_crit_pairs}\<close>

primrec discard_crit_pairs_dummy :: "('a, 'b, 'c, 'd) critT \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                      ((('a, 'b, 'c) pdata_pair list) \<times> (('a, 'b, 'c) pdata_pair list))"
  where
    "discard_crit_pairs_dummy _ _ _ _ [] _ ks ds = (ks, ds)"|
    "discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds =
      (if crit gs bs (sps @ ps) data (fst p) (snd p) then
        discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds)
      else
        discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds
      )"

text \<open>The last argument of @{const discard_crit_pairs_dummy} is a ``dummy'' argument that is only
  needed for proving properties of the function, but that does not contribute to the final result
  we are interested in.\<close>

lemma set_discard_crit_pairs_dummy_partition:
  "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) \<union>
    set (snd (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) =
  set sps \<union> set ks \<union> set ds"
  by (induct sps arbitrary: ks ds, simp_all)

lemma fst_discard_crit_pairs_dummy_subset:
  "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) \<subseteq> set sps \<union> set ks"
proof (induct sps arbitrary: ks ds)
  case Nil
  show ?case by simp
next
  case (Cons p sps)
  show ?case
  proof (simp, intro conjI impI)
    have "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds))) \<subseteq> set sps \<union> set ks"
      by (rule Cons)
    also have "... \<subseteq> insert p (set sps \<union> set ks)" by blast
    finally show "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds))) \<subseteq>
                    insert p (set sps \<union> set ks)" .
  next
    have "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds)) \<subseteq> set sps \<union> set (p # ks)"
      by (rule Cons)
    thus "set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds)) \<subseteq>
            insert p (set sps \<union> set ks)" by simp
  qed
qed

lemma fst_discard_crit_pairs_dummy_sublist:
  obtains ks' where "fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds) = ks' @ ks"
proof (induct sps arbitrary: thesis ks ds)
  case Nil
  show ?case
  proof (rule Nil)
    show "fst (discard_crit_pairs_dummy crit gs bs ps [] data ks ds) = [] @ ks" by simp
  qed
next
  case (Cons p sps)
  show ?case
  proof (cases "crit gs bs (sps @ ps) data (fst p) (snd p)")
    case True
    obtain ks' where *: "fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds)) = ks' @ ks"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from True * show "fst (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = ks' @ ks"
        by simp
    qed
  next
    case False
    obtain ks' where *: "fst (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds) = ks' @ (p # ks)"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from False * show "fst (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = (ks' @ [p]) @ ks"
        by simp
    qed
  qed
qed

lemma snd_discard_crit_pairs_dummy_sublist:
  obtains ds' where "snd (discard_crit_pairs_dummy crit gs bs ps sps data ks ds) = ds' @ ds"
proof (induct sps arbitrary: thesis ks ds)
  case Nil
  show ?case
  proof (rule Nil)
    show "snd (discard_crit_pairs_dummy crit gs bs ps [] data ks ds) = [] @ ds" by simp
  qed
next
  case (Cons p sps)
  show ?case
  proof (cases "crit gs bs (sps @ ps) data (fst p) (snd p)")
    case True
    obtain ds' where *: "snd (discard_crit_pairs_dummy crit gs bs ps sps data ks (p # ds)) = ds' @ (p # ds)"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from True * show "snd (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = (ds' @ [p]) @ ds"
        by simp
    qed
  next
    case False
    obtain ds' where *: "snd (discard_crit_pairs_dummy crit gs bs ps sps data (p # ks) ds) = ds' @ ds"
      by (rule Cons(1))
    show ?thesis
    proof (rule Cons(2))
      from False * show "snd (discard_crit_pairs_dummy crit gs bs ps (p # sps) data ks ds) = ds' @ ds"
        by simp
    qed
  qed
qed

lemma discard_crit_pairs_dummy_connectible:
  assumes "crit_spec crit" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) data"
    and "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "\<And>p' q'. processed (p', q') (gs @ bs) (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set ds \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)) \<Longrightarrow>
            fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
  assumes "(p, q) \<in> set (snd (discard_crit_pairs_dummy crit gs bs ps sps data ks ds))"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
  using assms(9, 10, 11, 12, 13)
proof (induct sps arbitrary: ks ds)
  case Nil
  from Nil(5) have "(p, q) \<in> set ds" by simp
  from this assms(14, 15) show ?case by (rule Nil(3))
next
  case (Cons s sps)
  from Cons(2) have "s \<in> set bs \<times> (set gs \<union> set bs)" and sps_sub: "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    by simp_all
  from this(1) have "fst s \<in> set bs" and "snd s \<in> set gs \<union> set bs" by auto
  let ?res = "discard_crit_pairs_dummy crit gs bs ps (s # sps) data ks ds"

  have *: "fst (fst s) \<noteq> 0 \<Longrightarrow> fst (snd s) \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
  proof -
    assume "fst (fst s) \<noteq> 0" and "fst (snd s) \<noteq> 0"
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
    proof (cases "crit gs bs (sps @ ps) data (fst s) (snd s)")
      case True
      with assms(1, 2, 3, 4, 5, 6) _ assms(8) _ \<open>fst s \<in> set bs\<close> \<open>snd s \<in> set gs \<union> set bs\<close>
          \<open>fst (fst s) \<noteq> 0\<close> \<open>fst (snd s) \<noteq> 0\<close>
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst (fst s)) (fst (snd s))"
      proof (rule crit_specD)
        from sps_sub assms(7) show "set (sps @ ps) \<subseteq> set bs \<times> (set gs \<union> set bs)" by auto
      next
        fix p' q'
        assume "processed (p', q') (gs @ bs) ((fst s, snd s) # sps @ ps)"
        hence "processed (p', q') (gs @ bs) ((s # sps) @ ps)" by simp
        moreover assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
        ultimately show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
          by (rule Cons(3))
      qed
      thus ?thesis by simp
    next
      case False
      show ?thesis
      proof (rule Cons(5), simp add: False)
        obtain ks' where "fst (discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds) = ks' @ (s # ks)"
          by (rule fst_discard_crit_pairs_dummy_sublist)
        thus "s \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds))" by simp
      qed fact+
    qed
  qed

  have **: "processed (p', q') (gs @ bs) (sps @ ps) \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" for p' q'
  proof -
    assume proc: "processed (p', q') (gs @ bs) (sps @ ps)"
    assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    proof (cases "s = (p', q')")
      case True
      hence p': "p' = fst s" and q': "q' = snd s" by simp_all
      from \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis unfolding p' q' by (rule *)
    next
      case False
      show ?thesis
      proof (cases "s = (q', p')")
        case True
        hence p': "p' = snd s" and q': "q' = fst s" by simp_all
        from \<open>fst q' \<noteq> 0\<close> \<open>fst p' \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst q') (fst p')"
          unfolding p' q' by (rule *)
        thus ?thesis by (rule crit_pair_cbelow_sym)
      next
        case False
        from _ \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis
        proof (rule Cons(3))
          from proc have "processed (p', q') (gs @ bs) (s # (sps @ ps))"
          proof (rule processed_Cons)
            assume "p' = fst s" and "q' = snd s"
            hence "s = (p', q')" by simp
            with \<open>s \<noteq> (p', q')\<close> show ?thesis ..
          next
            assume "p' = snd s" and "q' = fst s"
            hence "s = (q', p')" by simp
            with \<open>s \<noteq> (q', p')\<close> show ?thesis ..
          qed simp
          thus "processed (p', q') (gs @ bs) ((s # sps) @ ps)" by simp
        qed
      qed
    qed
  qed

  from Cons(6) show ?case
  proof (simp split: if_splits)
    let ?a = "discard_crit_pairs_dummy crit gs bs ps sps data ks (s # ds)"
    assume crit: "crit gs bs (sps @ ps) data (fst s) (snd s)"
    hence "?res = ?a" by simp
    assume "(p, q) \<in> set (snd ?a)"
    with sps_sub _ _ _ show ?thesis
    proof (rule Cons(1))
      fix p' q'
      assume "processed (p', q') (gs @ bs) (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule **)
    next
      fix p' q'
      assume "(p', q') \<in> set (s # ds)"
      hence disj: "s = (p', q') \<or> (p', q') \<in> set ds" by auto
      assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      from disj show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      proof
        assume "s = (p', q')"
        hence p': "p' = fst s" and q': "q' = snd s" by simp_all
        from \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis unfolding p' q' by (rule *)
      next
        assume "(p', q') \<in> set ds"
        from this \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> show ?thesis by (rule Cons(4))
      qed
    next
      fix p' q'
      assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data ks (s # ds)))"
        and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
        by (rule Cons(5), simp only: \<open>?res = ?a\<close>, fact+)
    qed
  next
    let ?a = "discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds"
    assume "\<not> crit gs bs (sps @ ps) data (fst s) (snd s)"
    hence "?res = ?a" by simp
    assume "(p, q) \<in> set (snd ?a)"
    with sps_sub _ _ _ show ?thesis
    proof (rule Cons(1))
      fix p' q'
      assume "processed (p', q') (gs @ bs) (sps @ ps)" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule **)
    next
      fix p' q'
      assume "(p', q') \<in> set ds" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by (rule Cons(4))
    next
      fix p' q'
      assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs ps sps data (s # ks) ds))"
        and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
        by (rule Cons(5), simp only: \<open>?res = ?a\<close>, fact+)
    qed
  qed
qed

primrec discard_crit_pairs_aux :: "('a, 'b, 'c, 'd) critT \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
  where
    "discard_crit_pairs_aux _ _ _ _ [] _ ks = ks"|
    "discard_crit_pairs_aux crit gs bs ps (p # sps) data ks =
      (if crit gs bs (sps @ ps) data (fst p) (snd p) then
        discard_crit_pairs_aux crit gs bs ps sps data ks
      else
        discard_crit_pairs_aux crit gs bs ps sps data (p # ks)
      )"

text \<open>Function @{const discard_crit_pairs_aux} is like @{const discard_crit_pairs_dummy}, but lacks
  the dummy argument. Therefore, it is the method of choice for doing actual computations.\<close>

lemma discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy':
  "discard_crit_pairs_aux crit gs bs ps sps data ks =
              fst (discard_crit_pairs_dummy crit gs bs ps sps data ks ds)"
  by (induct sps arbitrary: ks ds, simp_all)

lemmas discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy =
          discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy'[where ds="[]"]

definition discard_crit_pairs :: "('a, 'b, 'c, 'd) critT \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                      ('a, 'b, 'c) pdata_pair list"
  where "discard_crit_pairs crit gs bs ps sps data = discard_crit_pairs_aux crit gs bs ps sps data []"

lemma discard_crit_pairs_alt:
  "discard_crit_pairs crit gs bs ps sps data = fst (discard_crit_pairs_dummy crit gs bs ps sps data [] [])"
  by (simp only: discard_crit_pairs_def discard_crit_pairs_aux_eq_fst_discard_crit_pairs_dummy)

lemma set_discard_crit_pairs_partition:
  "set sps = set (discard_crit_pairs crit gs bs ps sps data) \<union>
              set (snd (discard_crit_pairs_dummy crit gs bs ps sps data [] []))"
  by (simp add: discard_crit_pairs_alt set_discard_crit_pairs_dummy_partition)

corollary discard_crit_pairs_subset: "set (discard_crit_pairs crit gs bs ps sps data) \<subseteq> set sps"
  using set_discard_crit_pairs_partition by fastforce

lemma discard_crit_pairs_connectible:
  assumes "crit_spec crit" and "dickson_grading (+) d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "F \<subseteq> dgrad_p_set d m" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "unique_idx (gs @ bs) data" and "set sps \<subseteq> set ps"
    and "\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
    and "\<And>p' q'. (p', q') \<in> set (discard_crit_pairs crit gs bs (ps -- sps) sps data) \<Longrightarrow>
            fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
  assumes "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p) (fst q)"
proof (cases "(p, q) \<in> set (discard_crit_pairs crit gs bs (ps -- sps) sps data)")
  case True
  from this assms(13, 14) show ?thesis by (rule assms(11))
next
  case False
  note assms(1, 2, 3, 4, 5, 6)
  moreover from assms(7) have "set (ps -- sps) \<subseteq> set bs \<times> (set gs \<union> set bs)" by (auto simp add: set_diff_list)
  moreover note assms(8)
  moreover from assms(9, 7) have "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)" by (rule subset_trans)
  moreover note _ _ _
  moreover from False assms(12) have "(p, q) \<in> set (snd (discard_crit_pairs_dummy crit gs bs (ps -- sps) sps data [] []))"
    using set_discard_crit_pairs_partition[of sps crit gs bs "ps -- sps"] by blast
  ultimately show ?thesis using assms(13, 14)
  proof (rule discard_crit_pairs_dummy_connectible)
    fix p' q'
    assume "processed (p', q') (gs @ bs) (sps @ (ps -- sps))"
    hence "processed (p', q') (gs @ bs) ps"
      by (simp only: processed_alt subset_append_diff_cancel[OF assms(9)], simp)
    moreover assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    ultimately show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      by (rule assms(10))
  next
    fix p' q' :: "('a, 'b, 'c) pdata"
    assume "(p', q') \<in> set []"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')" by simp
  next
    fix p' q'
    assume "(p', q') \<in> set (fst (discard_crit_pairs_dummy crit gs bs (ps -- sps) sps data [] []))"
      and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> F) (fst p') (fst q')"
      unfolding discard_crit_pairs_alt[symmetric] by (rule assms(11))
  qed
qed

subsubsection \<open>Specification of the @{emph \<open>reduce-critical-pairs\<close>} parameter\<close>

type_synonym (in -) ('a, 'b, 'c, 'd) rcpT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                          ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                          (('a, 'b, 'c) pdata' list \<times> 'd)"

definition rcp_spec :: "('a, 'b::field, 'c, 'd) rcpT \<Rightarrow> bool"
  where "rcp_spec rcp \<longleftrightarrow>
            (\<forall>gs bs ps data.
              0 \<notin> fst ` set (fst (rcp gs bs ps data)) \<and>
              (\<forall>h b. h \<in> set (fst (rcp gs bs ps data)) \<longrightarrow> b \<in> set bs \<longrightarrow> fst b \<noteq> 0 \<longrightarrow>
                     \<not> lp (fst b) adds lp (fst h)) \<and>
              (\<forall>d. dickson_grading (+) d \<longrightarrow>
                     dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps data))) (args_to_set (gs, bs, ps))) \<and>
              (is_Groebner_basis (fst ` set gs) \<longrightarrow> unique_idx (gs @ bs) data \<longrightarrow>
                (fst ` set (fst (rcp gs bs ps data)) \<subseteq> pideal (args_to_set (gs, bs, ps)) \<and>
                (\<forall>(p, q)\<in>set ps.  set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                  (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0))))"

text \<open>Informally, @{term "rcp_spec rcp"} expresses that, for suitable @{term gs}, @{term bs} and @{term ps},
  the value of @{term "rcp gs bs ps"}
  \begin{itemize}
    \item is a list consisting exclusively of non-zero polynomials contained in the ideal generated
      by @{term "set bs \<union> set gs"}, whose leading power-products are not divisible by the leading
      power-product of any non-zero @{prop "b \<in> set bs"}, and
    \item contains sufficiently many new polynomials such that all S-polynomials originating from
      @{term ps} can be reduced to @{term 0} modulo the enlarged list of polynomials.
  \end{itemize}\<close>

lemma rcp_specI:
  assumes "\<And>gs bs ps data. 0 \<notin> fst ` set (fst (rcp gs bs ps data))"
  assumes "\<And>gs bs ps h b data. h \<in> set (fst (rcp gs bs ps data)) \<Longrightarrow> b \<in> set bs \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
                          \<not> lp (fst b) adds lp (fst h)"
  assumes "\<And>gs bs ps d data. dickson_grading (+) d \<Longrightarrow>
                         dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps data))) (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps data. is_Groebner_basis (fst ` set gs) \<Longrightarrow> unique_idx (gs @ bs) data \<Longrightarrow>
                (fst ` set (fst (rcp gs bs ps data)) \<subseteq> pideal (args_to_set (gs, bs, ps)) \<and>
                (\<forall>(p, q)\<in>set ps.  set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                  (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0))"
  shows "rcp_spec rcp"
  unfolding rcp_spec_def using assms by auto

lemma rcp_specD1:
  assumes "rcp_spec rcp"
  shows "0 \<notin> fst ` set (fst (rcp gs bs ps data))"
  using assms unfolding rcp_spec_def by blast

lemma rcp_specD2:
  assumes "rcp_spec rcp"
    and "h \<in> set (fst (rcp gs bs ps data))" and "b \<in> set bs" and "fst b \<noteq> 0"
  shows "\<not> lp (fst b) adds lp (fst h)"
  using assms unfolding rcp_spec_def by blast

lemma rcp_specD3:
  assumes "rcp_spec rcp" and "dickson_grading (+) d"
  shows "dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps data))) (args_to_set (gs, bs, ps))"
  using assms unfolding rcp_spec_def by blast

lemma rcp_specD4:
  assumes "rcp_spec rcp" and "is_Groebner_basis (fst ` set gs)" and "unique_idx (gs @ bs) data"
  shows "fst ` set (fst (rcp gs bs ps data)) \<subseteq> pideal (args_to_set (gs, bs, ps))"
  using assms unfolding rcp_spec_def by blast

lemma rcp_specD5:
  assumes "rcp_spec rcp" and "is_Groebner_basis (fst ` set gs)" and "unique_idx (gs @ bs) data"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "(p, q) \<in> set ps"
  shows "(red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
  using assms unfolding rcp_spec_def by blast

subsubsection \<open>Function @{term discard_red_cp}\<close>

definition discard_red_cp :: "('a, 'b, 'c, 'd) critT \<Rightarrow> ('a, 'b, 'c, 'd) rcpT \<Rightarrow> ('a, 'b::field, 'c, 'd) complT"
  where "discard_red_cp crit rcp gs bs ps sps data =
                rcp gs bs (discard_crit_pairs crit gs bs ps sps data) data"

lemma discard_red_cp_dgrad_p_set_le:
  assumes "rcp_spec rcp" and "dickson_grading (+) d" and "set sps \<subseteq> set ps"
  shows "dgrad_p_set_le d (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)))
                          (args_to_set (gs, bs, ps))"
proof -
  from assms(1, 2)
  have "dgrad_p_set_le d (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)))
                          (args_to_set (gs, bs, discard_crit_pairs crit gs bs (ps -- sps) sps data))"
    unfolding discard_red_cp_def by (rule rcp_specD3)
  also have "dgrad_p_set_le d ... (args_to_set (gs, bs, ps))"
  proof (rule dgrad_p_set_le_subset, rule args_to_set_subset3)
    from discard_crit_pairs_subset \<open>set sps \<subseteq> set ps\<close>
    show "set (discard_crit_pairs crit gs bs (ps -- sps) sps data) \<subseteq> set ps" by (rule subset_trans)
  qed
  finally show ?thesis .
qed

lemma compl_struct_discard_red_cp:
  assumes "rcp_spec rcp"
  shows "compl_struct (discard_red_cp crit rcp)"
proof (rule compl_structI)
  fix d::"'a \<Rightarrow> nat" and gs bs ps and sps::"('a, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "dickson_grading (+) d" and "set sps \<subseteq> set ps"
  with assms show "dgrad_p_set_le d (fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)))
                                    (args_to_set (gs, bs, ps))"
    by (rule discard_red_cp_dgrad_p_set_le)
next
  fix gs bs ps and sps::"('a, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  from assms show "0 \<notin> fst ` set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data))"
    unfolding discard_red_cp_def by (rule rcp_specD1)
next
  fix gs bs ps sps h b data
  assume "h \<in> set (fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data))"
    and "b \<in> set bs" and "fst b \<noteq> 0"
  with assms show "\<not> lp (fst b) adds lp (fst h)" unfolding discard_red_cp_def by (rule rcp_specD2)
qed

lemma compl_pideal_discard_red_cp:
  assumes "rcp_spec rcp"
  shows "compl_pideal (discard_red_cp crit rcp)"
proof (rule compl_pidealI)
  fix gs bs :: "('a, 'b, 'c) pdata list" and ps sps :: "('a, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume gb: "is_Groebner_basis (fst ` set gs)" and "set sps \<subseteq> set ps"
    and un: "unique_idx (gs @ bs) data"
  let ?res = "fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)"
  let ?ks = "discard_crit_pairs crit gs bs (ps -- sps) sps data"
  from assms gb un have "fst ` set ?res \<subseteq> pideal (args_to_set (gs, bs, ?ks))"
    unfolding discard_red_cp_def by (rule rcp_specD4)
  also have "... \<subseteq> pideal (args_to_set (gs, bs, ps))"
  proof (rule ideal.module_mono)
    from discard_crit_pairs_subset \<open>set sps \<subseteq> set ps\<close> have "set ?ks \<subseteq> set ps"
      by (rule subset_trans)
    thus "args_to_set (gs, bs, ?ks) \<subseteq> args_to_set (gs, bs, ps)" by (rule args_to_set_subset3)
  qed
  finally show "fst ` set ?res \<subseteq> pideal (args_to_set (gs, bs, ps))" .
qed

lemma compl_conn_discard_red_cp:
  assumes "crit_spec crit" and "rcp_spec rcp"
  shows "compl_conn (discard_red_cp crit rcp)"
proof (rule compl_connI)
  fix d::"'a \<Rightarrow> nat" and m gs bs ps sps p and q::"('a, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume dg: "dickson_grading (+) d" and gs_sub: "fst ` set gs \<subseteq> dgrad_p_set d m"
    and gb: "is_Groebner_basis (fst ` set gs)" and bs_sub: "fst ` set bs \<subseteq> dgrad_p_set d m"
    and ps_sub: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "set sps \<subseteq> set ps"
    and un: "unique_idx (gs @ bs) data"
    and *: "\<And>p' q'. processed (p', q') (gs @ bs) ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
    and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"

  let ?res = "fst (discard_red_cp crit rcp gs bs (ps -- sps) sps data)"
  have res_sub: "fst ` set ?res \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set, rule discard_red_cp_dgrad_p_set_le, fact+)
    show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF ps_sub], rule, fact+)
  qed

  have gs_bs_sub: "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m" by (simp add: image_Un, rule, fact+)

  from assms(1) dg gs_sub gb bs_sub res_sub ps_sub un \<open>set sps \<subseteq> set ps\<close> _ _ \<open>(p, q) \<in> set sps\<close>
      \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
  show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p) (fst q)"
  proof (rule discard_crit_pairs_connectible)
    fix p' q'
    assume "processed (p', q') (gs @ bs) ps" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    hence "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')" by (rule *)
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p') (fst q')"
      by (rule crit_pair_cbelow_mono, simp)
  next
    fix p' q'
    assume p'q'_in: "(p', q') \<in> set (discard_crit_pairs crit gs bs (ps -- sps) sps data)" (is "_ \<in> set ?ks")
      and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    
    have "set ?ks \<subseteq> set sps" by (fact discard_crit_pairs_subset)
    also have "... \<subseteq> set ps" by fact
    also have "... \<subseteq> set bs \<times> (set gs \<union> set bs)" by fact
    finally have ks_sub: "set ?ks \<subseteq> set bs \<times> (set gs \<union> set bs)" .
    hence "fst ` set ?ks \<subseteq> set bs" by fastforce
    from this bs_sub have "fst ` fst ` set ?ks \<subseteq> dgrad_p_set d m" by blast
    with p'q'_in have "fst p' \<in> dgrad_p_set d m"
      by (meson bs_sub contra_subsetD imageI ks_sub mem_Sigma_iff)
    from ks_sub have "snd ` set ?ks \<subseteq> set gs \<union> set bs" by fastforce
    from this gs_bs_sub have "fst ` snd ` set ?ks \<subseteq> dgrad_p_set d m" by blast
    with p'q'_in have "fst q' \<in> dgrad_p_set d m"
      by (metis (no_types, lifting) contra_subsetD imageI snd_conv)

    from assms(2) gb un ks_sub p'q'_in have "(red (fst ` (set gs \<union> set bs) \<union> fst ` set ?res))\<^sup>*\<^sup>*
                                            (spoly (fst p') (fst q')) 0"
      unfolding discard_red_cp_def by (rule rcp_specD5)
    hence "(red (fst ` (set gs \<union> set bs) \<union> fst ` set ?res))\<^sup>*\<^sup>* (spoly (fst p') (fst q')) 0"
      by (simp only: image_Un)
    with dg _ \<open>fst p' \<in> dgrad_p_set d m\<close> \<open>fst q' \<in> dgrad_p_set d m\<close> \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p') (fst q')"
    proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
      from gs_bs_sub res_sub show "fst ` (set gs \<union> set bs) \<union> fst ` set ?res \<subseteq> dgrad_p_set d m"
        by simp
    qed
  qed
qed

end (* gd_powerprod *)

subsection \<open>Suitable Instances of the @{emph \<open>add-pairs\<close>} Parameter\<close>

type_synonym ('a, 'b, 'c, 'd) apsT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list"

definition add_pairs_single_naive :: "'d \<Rightarrow> ('a, 'b, 'c, 'd) apsT"
  where "add_pairs_single_naive data gs bs h ps \<equiv> ps @ (map (Pair h) gs) @ (map (Pair h) bs)"

lemma set_add_pairs_single_naive:
  "set (add_pairs_single_naive data gs bs h ps) = set ps \<union> {h} \<times> (set gs \<union> set bs)"
  by (simp add: add_pairs_single_naive_def, blast)

fun add_pairs_single_sorted :: "(('a, 'b, 'c) pdata_pair \<Rightarrow> ('a, 'b, 'c) pdata_pair \<Rightarrow> bool) \<Rightarrow>
                                    ('a, 'b, 'c, 'd) apsT"
    where
  "add_pairs_single_sorted _ [] [] _ ps = ps"|
  "add_pairs_single_sorted rel [] (b # bs) h ps =
    add_pairs_single_sorted rel [] bs h (insort_wrt rel (h, b) ps)"|
  "add_pairs_single_sorted rel (g # gs) bs h ps =
    add_pairs_single_sorted rel gs bs h (insort_wrt rel (h, g) ps)"

lemma set_add_pairs_single_sorted:
  "set (add_pairs_single_sorted rel gs bs h ps) = set ps \<union> {h} \<times> (set gs \<union> set bs)"
proof (induct gs arbitrary: ps)
  case Nil
  show ?case
  proof (induct bs arbitrary: ps)
    case Nil
    show ?case by simp
  next
    case (Cons b bs)
    show ?case by (simp add: Cons)
  qed
next
  case (Cons g gs)
  show ?case by (simp add: Cons)
qed

primrec pairs :: "('a, 'b, 'c, 'd) apsT \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
  where
  "pairs _ [] = []"|
  "pairs aps (x # xs) = aps [] xs x (pairs aps xs)"

lemma pairs_subset:
  assumes "\<And>gs bs h ps. set (aps gs bs h ps) = set ps \<union> {h} \<times> (set gs \<union> set bs)"
  shows "set (pairs aps xs) \<subseteq> set xs \<times> set xs"
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons have "set (pairs aps xs) \<subseteq> set (x # xs) \<times> set (x # xs)" by fastforce
  moreover have "{x} \<times> set xs \<subseteq> set (x # xs) \<times> set (x # xs)" by fastforce
  ultimately show ?case by (simp add: assms)
qed

lemma in_pairsI:
  assumes "\<And>gs bs h ps. set (aps gs bs h ps) = set ps \<union> {h} \<times> (set gs \<union> set bs)"
    and "a \<noteq> b" and "a \<in> set xs" and "b \<in> set xs"
  shows "(a, b) \<in> set (pairs aps xs) \<or> (b, a) \<in> set (pairs aps xs)"
  using assms(3, 4)
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons(3) have d: "b = x \<or> b \<in> set xs" by simp
  from Cons(2) have "a = x \<or> a \<in> set xs" by simp
  thus ?case
  proof
    assume "a = x"
    with assms(2) have "b \<noteq> x" by simp
    with d have "b \<in> set xs" by simp
    hence "(a, b) \<in> set (pairs aps (x # xs))" by (simp add: \<open>a = x\<close> assms(1))
    thus ?thesis ..
  next
    assume "a \<in> set xs"
    from d show ?thesis
    proof
      assume "b = x"
      from \<open>a \<in> set xs\<close> have "(b, a) \<in> set (pairs aps (x # xs))" by (simp add: \<open>b = x\<close> assms(1))
      thus ?thesis ..
    next
      assume "b \<in> set xs"
      with \<open>a \<in> set xs\<close> have "(a, b) \<in> set (pairs aps xs) \<or> (b, a) \<in> set (pairs aps xs)"
        by (rule Cons(1))
      thus ?thesis
      proof
        assume "(a, b) \<in> set (pairs aps xs)"
        hence "(a, b) \<in> set (pairs aps (x # xs))" by (simp add: assms(1))
        thus ?thesis ..
      next
        assume "(b, a) \<in> set (pairs aps xs)"
        hence "(b, a) \<in> set (pairs aps (x # xs))" by (simp add: assms(1))
        thus ?thesis ..
      qed
    qed
  qed
qed

definition add_pairs_naive :: "('a, 'b, 'c, 'd) apT"
  where "add_pairs_naive gs bs ps ns data =
          fold (add_pairs_single_naive data gs bs) ns (ps @ (pairs (add_pairs_single_naive data) ns))"

definition add_pairs_sorted :: "(nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata_pair \<Rightarrow> ('a, 'b, 'c) pdata_pair \<Rightarrow> bool) \<Rightarrow>
                                ('a, 'b, 'c, 'd) apT"
  where "add_pairs_sorted rel gs bs ps ns data =
          fold (add_pairs_single_sorted (rel data) gs bs) ns
                (merge_wrt (rel data) ps (pairs (add_pairs_single_sorted (rel data)) ns))"

lemma set_fold_aps:
  assumes "\<And>gs bs h ps. set (aps gs bs h ps) = set ps \<union> {h} \<times> (set gs \<union> set bs)"
  shows "set (fold (aps gs bs) ns ps) = set ns \<times> (set gs \<union> set bs) \<union> set ps"
proof (induct ns arbitrary: ps)
  case Nil
  show ?case by simp
next
  case (Cons n ns)
  show ?case by (simp add: Cons assms, blast)
qed

lemma set_add_pairs_naive:
  "set (add_pairs_naive gs bs ps ns data) =
      set ps \<union> set ns \<times> (set gs \<union> set bs) \<union> set (pairs (add_pairs_single_naive data) ns)"
proof -
  have "set (add_pairs_naive gs bs ps ns data) =
          set ns \<times> (set gs \<union> set bs) \<union>
             set (ps @ (pairs (add_pairs_single_naive data) ns))"
    unfolding add_pairs_naive_def by (rule set_fold_aps, fact set_add_pairs_single_naive)
  thus ?thesis by (simp add: ac_simps)
qed

lemma ap_spec_add_pairs_naive: "ap_spec add_pairs_naive"
proof (rule ap_specI)
  fix gs bs :: "('a, 'b, 'c) pdata list" and ps ns and data::"nat \<times> 'd"
  show "set (add_pairs_naive gs bs ps ns data) \<subseteq> set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns)"
  proof (simp add: set_add_pairs_naive, rule, blast)
    have "set (pairs (add_pairs_single_naive data) ns) \<subseteq> set ns \<times> set ns"
      by (rule pairs_subset, fact set_add_pairs_single_naive)
    thus "set (pairs (add_pairs_single_naive data) ns) \<subseteq>
          set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns)" by blast
  qed
next
  fix gs bs :: "('a, 'b, 'c) pdata list" and ps ns and h1 h2 :: "('a, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume "h1 \<noteq> h2" and "h1 \<in> set ns" and "h2 \<in> set ns"
  with set_add_pairs_single_naive
  have "(h1, h2) \<in> set (pairs (add_pairs_single_naive data) ns) \<or>
        (h2, h1) \<in> set (pairs (add_pairs_single_naive data) ns)" by (rule in_pairsI)
  thus "(h1, h2) \<in> set (add_pairs_naive gs bs ps ns data) \<or>
        (h2, h1) \<in> set (add_pairs_naive gs bs ps ns data)"
    by (auto simp add: set_add_pairs_naive)
qed (simp add: set_add_pairs_naive)

lemma set_add_pairs_sorted:
  "set (add_pairs_sorted rel gs bs ps ns data) =
      set ps \<union> set ns \<times> (set gs \<union> set bs) \<union> set (pairs (add_pairs_single_sorted (rel data)) ns)"
proof -
  have "set (add_pairs_sorted rel gs bs ps ns data) =
          set ns \<times> (set gs \<union> set bs) \<union>
             set (merge_wrt (rel data) ps (pairs (add_pairs_single_sorted (rel data)) ns))"
    unfolding add_pairs_sorted_def by (rule set_fold_aps, fact set_add_pairs_single_sorted)
  thus ?thesis by (simp add: set_merge_wrt ac_simps)
qed

lemma ap_spec_add_pairs_sorted: "ap_spec (add_pairs_sorted rel)"
proof (rule ap_specI)
  fix gs bs ps ns data
  show "set (add_pairs_sorted rel gs bs ps ns data) \<subseteq> set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns)"
  proof (simp add: set_add_pairs_sorted, rule, blast)
    have "set (pairs (add_pairs_single_sorted (rel data)) ns) \<subseteq> set ns \<times> set ns"
      by (rule pairs_subset, fact set_add_pairs_single_sorted)
    thus "set (pairs (add_pairs_single_sorted (rel data)) ns) \<subseteq>
          set ps \<union> set ns \<times> (set gs \<union> set bs \<union> set ns)" by blast
  qed
next
  fix gs bs :: "('a, 'b, 'c) pdata list" and ps ns and h1 h2 :: "('a, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume "h1 \<noteq> h2" and "h1 \<in> set ns" and "h2 \<in> set ns"
  with set_add_pairs_single_sorted
  have "(h1, h2) \<in> set (pairs (add_pairs_single_sorted (rel data)) ns) \<or>
        (h2, h1) \<in> set (pairs (add_pairs_single_sorted (rel data)) ns)" by (rule in_pairsI)
  thus "(h1, h2) \<in> set (add_pairs_sorted rel gs bs ps ns data) \<or>
        (h2, h1) \<in> set (add_pairs_sorted rel gs bs ps ns data)"
    by (auto simp add: set_add_pairs_sorted)
qed (simp add: set_add_pairs_sorted)

definition (in gd_powerprod) canon_pair_order :: "'d \<Rightarrow> ('a, 'b::zero, 'c) pdata_pair \<Rightarrow>
                                                        ('a, 'b, 'c) pdata_pair \<Rightarrow> bool"
  where "canon_pair_order data p q \<longleftrightarrow>
          (lcs (lp (fst (fst p))) (lp (fst (snd p))) \<preceq> lcs (lp (fst (fst q))) (lp (fst (snd q))))"

subsection \<open>Suitable Instances of the @{emph \<open>add-basis\<close>} Parameter\<close>

definition add_basis_naive :: "('a, 'b, 'c, 'd) abT"
  where "add_basis_naive gs bs ns data = bs @ ns"

lemma ab_spec_add_basis_naive: "ab_spec add_basis_naive"
  by (rule ab_specI, simp_all add: add_basis_naive_def)

definition add_basis_sorted :: "(nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd) abT"
  where "add_basis_sorted rel gs bs ns data = merge_wrt (rel data) bs ns"

lemma ab_spec_add_basis_sorted: "ab_spec (add_basis_sorted rel)"
  by (rule ab_specI, simp_all add: add_basis_sorted_def set_merge_wrt)

definition card_keys :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> nat"
  where "card_keys = card \<circ> keys"

definition (in ordered_powerprod) canon_basis_order :: "'d \<Rightarrow> ('a, 'b::zero, 'c) pdata \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> bool"
  where "canon_basis_order data p q \<longleftrightarrow>
          (let cp = card_keys (fst p); cq = card_keys (fst q) in
            cp < cq \<or> (cp = cq \<and> lp (fst p) \<prec> lp (fst q))
          )"

end (* theory *)
