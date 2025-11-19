(*<*)
theory Regex
  imports
    Trace
begin

unbundle lattice_syntax
(*>*)

section \<open>Regular expressions\<close>

context begin

qualified datatype (atms: 'a) regex = Skip nat | Test 'a
  | Plus "'a regex" "'a regex" | Times "'a regex" "'a regex"  | Star "'a regex"

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) auto

definition "Wild = Skip 1"

lemma size_regex_estimation[termination_simp]: "x \<in> atms r \<Longrightarrow> y < f x \<Longrightarrow> y < size_regex f r"
  by (induct r) auto

lemma size_regex_estimation'[termination_simp]: "x \<in> atms r \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_regex f r"
  by (induct r) auto

qualified definition "TimesL r S = Times r ` S"
qualified definition "TimesR R s = (\<lambda>r. Times r s) ` R"

qualified primrec collect where
  "collect f (Skip n) = {}"
| "collect f (Test \<phi>) = f \<phi>"
| "collect f (Plus r s) = collect f r \<union> collect f s"
| "collect f (Times r s) = collect f r \<union> collect f s"
| "collect f (Star r) = collect f r"

lemma collect_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>z. z \<in> atms r \<Longrightarrow> f z = f' z) \<Longrightarrow> collect f r = collect f' r'"
  by (induct r arbitrary: r') auto

lemma finite_collect[simp]: "(\<And>z. z \<in> atms r \<Longrightarrow> finite (f z)) \<Longrightarrow> finite (collect f r)"
  by (induct r) auto

lemma collect_commute:
  "(\<And>z. z \<in> atms r \<Longrightarrow> x \<in> f z \<longleftrightarrow> g x \<in> f' z) \<Longrightarrow> x \<in> collect f r \<longleftrightarrow> g x \<in> collect f' r"
  by (induct r) auto

lemma collect_alt: "collect f r = (\<Union>z \<in> atms r. f z)"
  by (induct r) auto

qualified definition ncollect where
  "ncollect f r = Max (insert 0 (Suc ` collect f r))"

lemma insert_Un: "insert x (A \<union> B) = insert x A \<union> insert x B"
  by auto

lemma ncollect_simps[simp]:
  assumes [simp]: "(\<And>z. z \<in> atms r \<Longrightarrow> finite (f z))" "(\<And>z. z \<in> atms s \<Longrightarrow> finite (f z))"
  shows
  "ncollect f (Skip n) = 0"
  "ncollect f (Test \<phi>) = Max (insert 0 (Suc ` f \<phi>))"
  "ncollect f (Plus r s) = max (ncollect f r) (ncollect f s)"
  "ncollect f (Times r s) = max (ncollect f r) (ncollect f s)"
  "ncollect f (Star r) = ncollect f r"
  unfolding ncollect_def
  by (auto simp add: image_Un Max_Un insert_Un simp del: Un_insert_right Un_insert_left)

abbreviation "min_regex_default f r j \<equiv> (if atms r = {} then j else Min ((\<lambda>z. f z j) ` atms r))"

qualified primrec match :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "match test (Skip n) = (\<lambda>i j. j = i + n)"
| "match test (Test \<phi>) = (\<lambda>i j. i = j \<and> test i \<phi>)"
| "match test (Plus r s) = match test r \<squnion> match test s"
| "match test (Times r s) = match test r OO match test s"
| "match test (Star r) = (match test r)\<^sup>*\<^sup>*"

lemma match_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>i z. z \<in> atms r \<Longrightarrow> t i z = t' i z) \<Longrightarrow> match t r = match t' r'"
  by (induct r arbitrary: r') auto

lemma match_le: "match test r i j \<Longrightarrow> i \<le> j"
proof (induction r arbitrary: i j)
  case (Times r s)
  then show ?case using order.trans by fastforce
next
  case (Star r)
  from Star.prems show ?case
    unfolding match.simps by (induct i j rule: rtranclp.induct) (force dest: Star.IH)+
qed auto

lemma match_rtranclp_le: "(match test r)\<^sup>*\<^sup>* i j \<Longrightarrow> i \<le> j"
  by (metis match.simps(5) match_le)

lemma match_map_regex: "match t (map_regex f r) = match (\<lambda>k z. t k (f z)) r"
  by (induct r) auto

lemma match_mono_strong:
  "(\<And>k z. k \<in> {i ..< j + 1} \<Longrightarrow> z \<in> atms r \<Longrightarrow> t k z \<Longrightarrow> t' k z) \<Longrightarrow> match t r i j \<Longrightarrow> match t' r i j"
proof (induction r arbitrary: i j)
  case (Times r s)
  from Times.prems show ?case
    by (auto 0 4 simp: relcompp_apply intro: le_less_trans match_le less_Suc_eq_le
      dest: Times.IH[rotated -1] match_le)
next
  case (Star r)
  from Star(3) show ?case unfolding match.simps
  proof -
    assume *: "(match t r)\<^sup>*\<^sup>* i j"
    then have "i \<le> j" unfolding match.simps(5)[symmetric]
      by (rule match_le)
    with * show "(match t' r)\<^sup>*\<^sup>* i j" using Star.prems
    proof (induction i j rule: rtranclp.induct)
      case (rtrancl_into_rtrancl a b c)
      from rtrancl_into_rtrancl(1,2,4,5) show ?case
        by (intro rtranclp.rtrancl_into_rtrancl[OF rtrancl_into_rtrancl.IH])
          (auto dest!: Star.IH[rotated -1]
            dest: match_le match_rtranclp_le simp: less_Suc_eq_le)
    qed simp
  qed
qed auto

lemma match_cong_strong:
  "(\<And>k z. k \<in> {i ..< j + 1} \<Longrightarrow> z \<in> atms r \<Longrightarrow> t k z = t' k z) \<Longrightarrow> match t r i j = match t' r i j"
  using match_mono_strong[of i j r t t'] match_mono_strong[of i j r t' t] by blast

end

(*<*)
end
(*>*)
