theory MLSS_Realisation
  imports HereditarilyFinite.Finitary Graph_Theory.Graph_Theory
begin

section \<open>The Realisation Function\<close>
text \<open>
  This theory contains an abstract formulation of a model
  for membership relations.
\<close>

abbreviation parents :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "parents G s \<equiv> {u. u \<rightarrow>\<^bsub>G\<^esub> s}"

abbreviation ancestors :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "ancestors G s \<equiv> {u. u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> s}"

lemma (in fin_digraph) parents_subs_verts: "parents G s \<subseteq> verts G"
  using reachable_in_verts by blast

lemma (in fin_digraph) finite_parents[intro]: "finite (parents G s)"
  using finite_subset[OF parents_subs_verts finite_verts] .

lemma (in fin_digraph) finite_ancestors[intro]: "finite (ancestors G s)"
  using reachable_in_verts
  by (auto intro: rev_finite_subset[where ?A="ancestors G s", OF finite_verts])

lemma (in wf_digraph) in_ancestors_if_dominates[simp, intro]:
  assumes "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "s \<in> ancestors G t"
  using assms by blast

lemma (in wf_digraph) ancestors_mono:
  assumes "s \<in> ancestors G t"
  shows "ancestors G s \<subseteq> ancestors G t"
  using assms by fastforce

locale dag = digraph G for G +
  assumes acyclic: "\<nexists>c. cycle c"
begin

lemma ancestors_asym:
  assumes "s \<in> ancestors G t"
  shows "t \<notin> ancestors G s"
proof
  assume "t \<in> ancestors G s"
  then obtain p1 p2 where "awalk t p1 s" "p1 \<noteq> []" "awalk s p2 t" "p2 \<noteq> []"
    using assms reachable1_awalk by auto
  then have "closed_w (p1 @ p2)"
    unfolding closed_w_def by auto
  with closed_w_imp_cycle acyclic show False
    by blast
qed

lemma ancestors_strict_mono:
  assumes "s \<in> ancestors G t"
  shows "ancestors G s \<subset> ancestors G t"
  using assms ancestors_mono ancestors_asym by blast

lemma card_ancestors_strict_mono:
  assumes "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "card (ancestors G s) < card (ancestors G t)"
  using assms finite_ancestors ancestors_strict_mono
  by (metis in_ancestors_if_dominates psubset_card_mono)

end

text \<open>
  The realisation assumes that the terms can be split into
  a set of base terms \<open>B\<close> that are realised with the function \<open>I\<close>
  and set terms \<open>T\<close> that are realised according to the structure
  of the membership relation (represented as a graph \<open>G\<close>).
\<close>
locale realisation = dag G for G +
  fixes B T :: "'a set"
  fixes I :: "'a \<Rightarrow> hf"
  fixes eq :: "'a rel"
  assumes B_T_partition_verts: "B \<inter> T = {}" "verts G = B \<union> T"
  assumes P_urelems: "\<And>p t. p \<in> B \<Longrightarrow> \<not> t \<rightarrow>\<^bsub>G\<^esub> p"
begin

lemma
  shows finite_B: "finite B"
    and finite_T: "finite T"
    and finite_B_un_T: "finite (B \<union> T)"
  using finite_verts B_T_partition_verts by auto

abbreviation "eq_class x \<equiv> eq `` {x}"

function realise :: "'a \<Rightarrow> hf" where
  "x \<in> B \<Longrightarrow> realise x = HF (realise ` parents G x) \<squnion> HF (I ` eq_class x)"
| "t \<in> T \<Longrightarrow> realise t = HF (realise ` parents G t)"
| "x \<notin> B \<union> T \<Longrightarrow> realise x = 0"
  using B_T_partition_verts by auto
termination
  by (relation "measure (\<lambda>t. card (ancestors G t))") (simp_all add: card_ancestors_strict_mono)

lemma finite_realisation_parents[simp, intro!]: "finite (realise ` parents G t)"
  by auto
 
function height :: "'a \<Rightarrow> nat" where
  "\<forall>s. \<not> s \<rightarrow>\<^bsub>G\<^esub> t \<Longrightarrow> height t = 0"
| "s \<rightarrow>\<^bsub>G\<^esub> t \<Longrightarrow> height t = Max (height ` parents G t) + 1"
  using P_urelems by force+
termination
  by (relation "measure (\<lambda>t. card (ancestors G t))") (simp_all add: card_ancestors_strict_mono)

lemma height_cases':
  obtains
      (Zero) "height t = 0"
    | (Suc_Max) s where "s \<rightarrow>\<^bsub>G\<^esub> t" "height t = height s + 1"
  apply(cases t rule: height.cases)
  using Max_in[OF finite_imageI[where ?h=height, OF finite_parents]]
  by auto

lemma lemma1_1:
  assumes "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "height s < height t"
proof(cases t rule: height_cases')
  case Zero
  with assms show ?thesis by simp
next
  case (Suc_Max s')
  note finite_imageI[where ?h=height, OF finite_parents]
  note Max_ge[OF this, of "height s" t]
  with assms Suc_Max show ?thesis
    by simp
qed

lemma dominates_if_mem_realisation:
  assumes "\<And>x y. I x \<noteq> realise y"
  assumes "realise s \<^bold>\<in> realise t"
  obtains s' where "s' \<rightarrow>\<^bsub>G\<^esub> t" "realise s = realise s'"
  using assms(2-)
proof(induction t rule: realise.induct)
  case (1 x)
  with assms(1) show ?case
    by simp (metis (no_types, lifting) image_iff mem_Collect_eq)
qed auto

lemma (in -) Max_le_if_All_Ex_le:
  assumes "finite A" "finite B"
      and "A \<noteq> {}"
      and "\<forall>a \<in> A. \<exists>b \<in> B. a \<le> b"
    shows "Max A \<le> Max B"
  using assms
proof(induction rule: finite_induct)
  case (insert a A)
  then obtain b B' where "B = insert b B'"
    by (metis equals0I insert_absorb)
  with insert show ?case
    by (meson Max_ge_iff Max_in finite.insertI insert_not_empty)
qed blast

lemma lemma1_2':
  assumes "\<And>x y. I x \<noteq> realise y"
  assumes "t1 \<in> B \<union> T" "t2 \<in> B \<union> T" "realise t1 = realise t2"
  shows "height t1 \<le> height t2"
  using assms(2-)
proof(induction "height t1" arbitrary: t1 t2 rule: less_induct)
  case less
  then show ?case
  proof(cases "height t1")
    case (Suc h)
    then obtain s1 where "s1 \<rightarrow>\<^bsub>G\<^esub> t1"
      by (cases t1 rule: height.cases) auto
    have Ex_approx: "\<exists>v. v \<rightarrow>\<^bsub>G\<^esub> t2 \<and> realise w = realise v" if "w \<rightarrow>\<^bsub>G\<^esub> t1" for w
    proof -
      from that less(2) have "realise w \<^bold>\<in> realise t1"
        by (induction t1 rule: realise.induct) auto
      with "less.prems" have "realise w \<^bold>\<in> realise t2"
        by metis
      with dominates_if_mem_realisation assms(1) obtain v
        where "v \<rightarrow>\<^bsub>G\<^esub> t2" "realise w = realise v"
        by blast
      with less.prems show ?thesis
        by auto
    qed
    moreover
    have "height w \<le> height v"
      if "w \<rightarrow>\<^bsub>G\<^esub> t1" "v \<in> B \<union> T" "realise w = realise v" for w v
    proof -
      have "w \<in> B \<union> T"
        using adj_in_verts[OF that(1)] B_T_partition_verts(2) by blast
      from "less.hyps"[OF lemma1_1, OF that(1) this that(2,3)] show ?thesis .
    qed
    ultimately have IH': "\<exists>v \<in> parents G t2. height w \<le> height v"
      if "w \<in> parents G t1" for w
      by (metis that adj_in_verts(1) mem_Collect_eq B_T_partition_verts(2))
    then have Max_le: "Max (height ` parents G t1) \<le> Max (height ` parents G t2)"
    proof -
      have "finite (height ` parents G t1)"
           "finite (height ` parents G t2)"
           "height ` parents G t1 \<noteq> {}"
        using finite_parents \<open>s1 \<rightarrow>\<^bsub>G\<^esub> t1\<close> by blast+
      with Max_le_if_All_Ex_le[OF this] IH' show ?thesis by blast
    qed
    show ?thesis 
    proof -
      note s1 = \<open>s1 \<rightarrow>\<^bsub>G\<^esub> t1\<close>
      with Ex_approx obtain s2 where "s2 \<rightarrow>\<^bsub>G\<^esub> t2"
        by blast
      with s1 Max_le show ?thesis by simp
    qed
  qed simp
qed

lemma lemma1_2:
  assumes "\<And>x y. I x \<noteq> realise y"
  assumes "t1 \<in> B \<union> T" "t2 \<in> B \<union> T" "realise t1 = realise t2"
  shows "height t1 = height t2"
  using assms lemma1_2' le_antisym by metis

lemma lemma1_3:
  assumes "\<And>x y. I x \<noteq> realise y"
  assumes "s \<in> B \<union> T" "t \<in> B \<union> T" "realise s \<^bold>\<in> realise t"
  shows "height s < height t"
proof -
  from dominates_if_mem_realisation[OF assms(1,4)] obtain s'
    where "s' \<rightarrow>\<^bsub>G\<^esub> t" "realise s' = realise s"
    by metis
  then have "height s = height s'"
    using lemma1_2[OF assms(1,2)]
    by (metis adj_in_verts(1) B_T_partition_verts(2))
  also have "\<dots> < height t"
    using \<open>s' \<rightarrow>\<^bsub>G\<^esub> t\<close> lemma1_1 by blast
  finally show ?thesis .
qed

end

end