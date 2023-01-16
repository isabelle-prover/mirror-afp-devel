theory Girth_Independence imports Connectivity
begin

section \<open> Girth and Independence \<close>
text \<open> We translate and extend on a number of definitions and lemmas on girth and independence
from Noschinski's ugraph representation \<^cite>\<open>"noschinski_2012"\<close>. \<close>

context sgraph
begin

definition girth :: "enat" where
  "girth \<equiv> INF p\<in> cycles. enat (walk_length p)"

lemma girth_acyclic: "cycles = {} \<Longrightarrow> girth = \<infinity>"
  unfolding girth_def using top_enat_def by simp

lemma girth_lte: "c \<in> cycles \<Longrightarrow> girth \<le> walk_length c"
  using girth_def INF_lower by auto

lemma girth_obtains: 
  assumes "girth \<noteq> top"
  obtains c where "c \<in> cycles" and "walk_length c = girth"
  using enat_in_INF girth_def assms by (metis (full_types) the_enat.simps)

lemma girthI:
  assumes "c' \<in> cycles"
  assumes "\<And> c . c \<in> cycles \<Longrightarrow> walk_length c' \<le> walk_length c"
  shows "girth = walk_length c'"
proof (rule ccontr)
  assume "girth \<noteq> walk_length c'"
  then have "girth < walk_length c'"
    using  assms girth_lte by fastforce
  then obtain c where "c \<in> cycles" and "walk_length c < walk_length c'"
    using girth_def by (metis enat_ord_simps(2) girth_obtains infinity_ilessE top_enat_def) 
  thus False using assms(2) less_imp_le_nat le_antisym
    by fastforce
qed

lemma (in fin_sgraph) girth_min_alt: 
  assumes "cycles \<noteq> {}"
  shows "girth = Min ((\<lambda> c . enat (walk_length c)) ` cycles)" (is "girth = Min ?A")
  unfolding girth_def using finite_cycles assms Min_Inf
  by (metis (full_types) INF_le_SUP bot_enat_def ccInf_empty ccSup_empty enat_ord_code(5) finite_imageI top_enat_def zero_enat_def) 

definition is_independent_set :: "'a set \<Rightarrow> bool" where
"is_independent_set vs \<equiv> vs \<subseteq> V \<and> (all_edges vs) \<inter> E = {}"

text \<open> A More mathematical way of thinking about it \<close>
lemma is_independent_alt: "is_independent_set vs \<longleftrightarrow> vs \<subseteq> V \<and> (\<forall> v \<in> vs. \<forall> u \<in> vs. \<not> vert_adj v u)"
  unfolding is_independent_set_def
proof (auto)
  fix v u assume ss: "vs \<subseteq> V" and inter: "all_edges vs \<inter> E = {}" and vin: "v \<in> vs" and uin: "u \<in> vs" and adj: "vert_adj v u"
  then have inE: "{v, u} \<in> E" using vert_adj_def by simp
  then have imp: "{v, u} \<in> all_edges vs" using vin uin e_in_all_edges_ss vin uin
    by (simp add: ss)
  then show False
    using inE inter by blast 
next
  fix x assume "vs \<subseteq> V" "\<forall>v\<in>vs. \<forall>u\<in>vs. \<not> vert_adj v u"  "x \<in> all_edges vs" "x \<in> E"
  then have "\<And> u v. {u, v} \<subseteq> vs \<Longrightarrow> {u, v} \<notin> E" by (simp add: vert_adj_def)
  then have "\<And> x . x \<subseteq> vs \<Longrightarrow> card x = 2 \<Longrightarrow> x \<notin> E" by (metis card_2_iff) 
  then show False using all_edges_def
    by (metis (mono_tags, lifting) \<open>x \<in> E\<close> \<open>x \<in> all_edges vs\<close> mem_Collect_eq) 
qed

lemma singleton_independent_set: "v \<in> V \<Longrightarrow> is_independent_set {v}"
  by (metis empty_subsetI insert_absorb2 insert_subset is_independent_alt
      singletonD singleton_not_edge vert_adj_def) 

definition independent_sets :: "'a set set" where
  "independent_sets \<equiv> {vs. is_independent_set vs}"

definition independence_number :: "enat"  where
   "independence_number \<equiv> SUP vs \<in> independent_sets. enat (card vs)"

abbreviation "\<alpha> \<equiv> independence_number"

lemma independent_sets_mono:
  "vs \<in> independent_sets  \<Longrightarrow> us \<subseteq> vs \<Longrightarrow> us \<in> independent_sets "
  using Int_mono[OF all_edges_mono, of us vs "E" "E"]
  unfolding independent_sets_def is_independent_set_def by auto

lemma le_independence_iff:
  assumes "0 < k"
  shows "k \<le> \<alpha> \<longleftrightarrow> k \<in> card ` independent_sets " (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain vs where "vs \<in> independent_sets " and klt: "k \<le> card vs"
    using assms unfolding independence_number_def enat_le_Sup_iff by auto
  moreover
  obtain us where "us \<subseteq> vs" and "k = card us"
    using card_Ex_subset  klt by auto
  ultimately
  have "us \<in> independent_sets "  by (auto intro: independent_sets_mono)
  then show ?R using \<open>k = card us\<close> by auto
qed (auto intro: SUP_upper simp: independence_number_def)

lemma zero_less_independence:
  assumes "V \<noteq> {}"
  shows "0 < \<alpha>"
proof -
  from assms obtain a where "a \<in> V" by auto
  then have "0 < enat (card {a})" "{a} \<in> independent_sets"
    using independent_sets_def is_independent_set_def all_edges_def singleton_independent_set by simp_all
  then show ?thesis unfolding independence_number_def less_SUP_iff ..
qed

end

context fin_sgraph
begin
lemma fin_independent_sets: "finite (independent_sets)" 
  unfolding independent_sets_def is_independent_set_def using finV by auto

lemma independence_le_card:
  shows "\<alpha>  \<le> card V"
proof -
  { fix x assume "x \<in> independent_sets "
    then have "x \<subseteq> V" by (auto simp: independent_sets_def is_independent_set_def) }
  with finV show ?thesis unfolding independence_number_def
    by (intro SUP_least) (auto intro: card_mono)
qed

lemma independence_fin: "\<alpha> \<noteq> \<infinity>"
  using independence_le_card by (cases "\<alpha>") auto

lemma independence_max_alt: "V \<noteq> {} \<Longrightarrow> \<alpha> = Max ((\<lambda> vs . enat (card vs)) ` independent_sets)"
  unfolding independence_number_def using Sup_enat_def zero_less_independence
  by (metis i0_less independence_fin independence_number_def)

lemma independent_sets_ne: 
  assumes "V \<noteq> {}"
  shows "independent_sets \<noteq> {}"
proof - 
  from assms obtain a where "a \<in> V" by auto
  then have "{a} \<in> independent_sets" using independent_sets_def singleton_independent_set by simp
  thus ?thesis by blast
qed

lemma independence_obtains: 
  assumes "V \<noteq> {}"
  obtains vs where "is_independent_set vs" and "card vs = \<alpha>"
proof -
  have "\<alpha> = Max ((\<lambda> vs . enat (card vs)) ` independent_sets)" using independence_max_alt assms by simp
  then obtain vs where "vs \<in> independent_sets" and "enat (card vs) = \<alpha>" 
    using obtains_MIN[of "independent_sets" "\<lambda> vs . enat (card vs)"] assms fin_independent_sets independent_sets_ne
    by (metis (no_types, lifting) Max_in finite_imageI imageE image_is_empty) 
  thus ?thesis using independent_sets_def that by simp
qed
end
end