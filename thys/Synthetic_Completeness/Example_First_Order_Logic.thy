(*
  Title:  Example Completeness Proof for a Natural Deduction Calculus for First-Order Logic
  Author: Asta Halkjær From
*)

chapter \<open>Example: First-Order Logic\<close>

theory Example_First_Order_Logic imports Derivations begin

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<bullet>\<close>)

abbreviation Const (\<open>\<^bold>\<star>\<close>) where \<open>\<^bold>\<star>a \<equiv> \<^bold>\<bullet>a []\<close>

datatype (params_fm: 'f, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Exi \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<exists>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

type_synonym ('a, 'f, 'p) model = \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> ('p \<Rightarrow> 'a list \<Rightarrow> bool)\<close>

fun semantics_tm :: \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'f tm \<Rightarrow> 'a\<close> (\<open>\<lparr>_\<rparr>\<close>) where
  \<open>\<lparr>(E, _)\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>(E, F)\<rparr> (\<^bold>\<bullet>f ts) = F f (map \<lparr>(E, F)\<rparr> ts)\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<Zsemi>\<close> 0) where
  \<open>(t \<Zsemi> s) 0 = t\<close>
| \<open>(t \<Zsemi> s) (Suc n) = s n\<close>

fun semantics_fm :: \<open>('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<exists>\<close> 50) where
  \<open>_ \<Turnstile>\<^sub>\<exists> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<exists> \<^bold>\<cdot>P ts \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<exists> p \<^bold>\<longrightarrow> q \<longleftrightarrow> (E, F, G) \<Turnstile>\<^sub>\<exists> p \<longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<exists> q\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<exists> \<^bold>\<exists>p \<longleftrightarrow> (\<exists>x. (x \<Zsemi> E, F, G) \<Turnstile>\<^sub>\<exists> p)\<close>

section \<open>Operations\<close>

primrec lift_tm :: \<open>'f tm \<Rightarrow> 'f tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<bullet>f ts) = \<^bold>\<bullet>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm s (\<^bold>\<bullet>f ts) = \<^bold>\<bullet>f (map (sub_tm s) ts)\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>sub_fm _ \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>sub_fm s (\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map (sub_tm s) ts)\<close>
| \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close>
| \<open>sub_fm s (\<^bold>\<exists>p) = \<^bold>\<exists>(sub_fm (\<^bold>#0 \<Zsemi> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>'f tm \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<Zsemi> \<^bold>#)\<close>

abbreviation \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

abbreviation \<open>params' l \<equiv> params (set l)\<close>

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>(E, F(f := x))\<rparr> t = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> (E, F(f := x), G) \<Turnstile>\<^sub>\<exists> p \<longleftrightarrow> (E, F, G)\<Turnstile>\<^sub>\<exists> p\<close>
  by (induct p arbitrary: E) (auto cong: map_cong)

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all

lemma env [simp]: \<open>P ((x \<Zsemi> E) n) = (P x \<Zsemi> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma: \<open>\<lparr>(x \<Zsemi> E, F)\<rparr> (lift_tm t) = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics: \<open>\<lparr>(E, F)\<rparr> (sub_tm s t) = \<lparr>(\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]: \<open>(E, F, G) \<Turnstile>\<^sub>\<exists> sub_fm s p \<longleftrightarrow> (\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F, G) \<Turnstile>\<^sub>\<exists> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong simp: sub_tm_semantics lift_lemma)

lemma sub_tm_Var [simp]: \<open>sub_tm \<^bold># t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma reduce_Var [simp]: \<open>(\<^bold># 0 \<Zsemi> \<lambda>n. \<^bold># (Suc n)) = \<^bold>#\<close>
proof (rule ext)
  fix n
  show \<open>(\<^bold># 0 \<Zsemi> \<lambda>n. \<^bold># (Suc n)) n = \<^bold>#n\<close>
    by (induct n) simp_all
qed

lemma sub_fm_Var [simp]:
  fixes p :: \<open>('f, 'p) fm\<close>
  shows \<open>sub_fm \<^bold># p = p\<close>
proof (induct p)
  case (Pre P ts)
  then show ?case
    by (auto cong: map_cong)
qed simp_all

lemma semantics_tm_id [simp]: \<open>\<lparr>(\<^bold>#, \<^bold>\<bullet>)\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>(\<^bold>#, \<^bold>\<bullet>)\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm :: \<open>('f, 'p) fm \<Rightarrow> nat\<close> where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<cdot>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<exists>p) = 1 + size_fm p\<close>

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

section \<open>Calculus\<close>

inductive Calculus :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<^sub>\<exists>\<close> 50) where
  Assm [simp]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p\<close>
| FlsE [elim]: \<open>A \<turnstile>\<^sub>\<exists> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p\<close>
| ImpI [intro]: \<open>p # A \<turnstile>\<^sub>\<exists> q \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p \<^bold>\<longrightarrow> q\<close>
| ImpE [dest]: \<open>A \<turnstile>\<^sub>\<exists> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> A \<turnstile>\<^sub>\<exists> q\<close>
| ExiI [intro]: \<open>A \<turnstile>\<^sub>\<exists> \<langle>t\<rangle>p \<Longrightarrow> A \<turnstile>\<^sub>\<exists> \<^bold>\<exists>p\<close>
| ExiE [elim]: \<open>A \<turnstile>\<^sub>\<exists> \<^bold>\<exists>p \<Longrightarrow> a \<notin> params (set (p # q # A)) \<Longrightarrow> \<langle>\<^bold>\<star>a\<rangle>p # A \<turnstile>\<^sub>\<exists> q \<Longrightarrow> A \<turnstile>\<^sub>\<exists> q\<close>
| Clas: \<open>(p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p\<close>

subsection \<open>Weakening\<close>

abbreviation \<open>psub f \<equiv> map_fm f id\<close>

lemma map_tm_sub_tm [simp]: \<open>map_tm f (sub_tm g t) = sub_tm (map_tm f o g) (map_tm f t)\<close>
  by (induct t) simp_all

lemma map_tm_lift_tm [simp]: \<open>map_tm f (lift_tm t) = lift_tm (map_tm f t)\<close>
  by (induct t) simp_all

lemma psub_sub_fm: \<open>psub f (sub_fm g p) = sub_fm (map_tm f o g) (psub f p)\<close>
  by (induct p arbitrary: g) (simp_all add: comp_def)

lemma map_tm_inst_single: \<open>(map_tm f o (u \<Zsemi> \<^bold>#)) t = (map_tm f u \<Zsemi> \<^bold>#) t\<close>
  by (induct t) auto

lemma psub_inst_single [simp]: \<open>psub f (\<langle>t\<rangle>p) = \<langle>map_tm f t\<rangle>(psub f p)\<close>
  unfolding psub_sub_fm map_tm_inst_single ..

lemma map_tm_upd [simp]: \<open>a \<notin> params_tm t \<Longrightarrow> map_tm (f(a := b)) t = map_tm f t\<close>
  by (induct t) auto

lemma psub_upd [simp]: \<open>a \<notin> params_fm p \<Longrightarrow> psub (f(a := b)) p = psub f p\<close>
  by (induct p) auto

class inf_univ =
  fixes itself :: \<open>'a itself\<close>
  assumes infinite_UNIV: \<open>infinite (UNIV :: 'a set)\<close>

lemma Calculus_psub:
  fixes f :: \<open>'f \<Rightarrow> 'g :: inf_univ\<close>
  shows \<open>A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> map (psub f) A \<turnstile>\<^sub>\<exists> psub f p\<close>
proof (induct A p arbitrary: f pred: Calculus)
  case (Assm p A)
  then show ?case
    by simp
next
  case (FlsE A p)
  then show ?case
    by force
next
  case (ImpI p A q)
  then show ?case
    by auto
next
  case (ImpE A p q)
  then show ?case
    by auto
next
  case (ExiI A t p)
  then show ?case
    by (metis Calculus.ExiI fm.simps(27) psub_inst_single)
next
  case (ExiE A p a q)
  let ?params = \<open>params' (p # q # A)\<close>
  have \<open>finite ?params\<close>
    by simp
  then obtain b where b: \<open>b \<notin> {f a} \<union> f ` ?params\<close>
    using ex_new_if_finite infinite_UNIV
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI)

  define g where \<open>g \<equiv> f(a := b)\<close>

  have \<open>a \<notin> params' (p # q # A)\<close>
    using ExiE by simp
  then have b': \<open>b \<notin> params' (map (psub g) (p # q # A))\<close>
    unfolding g_def using b ExiE(3) by (auto simp: fm.set_map(1))

  have \<open>map (psub g) A \<turnstile>\<^sub>\<exists> psub g (\<^bold>\<exists>p)\<close>
    using ExiE by blast
  then have \<open>map (psub g) A \<turnstile>\<^sub>\<exists> \<^bold>\<exists>(psub g p)\<close>
    by simp
  moreover have \<open>map (psub g) (\<langle>\<^bold>\<star>a\<rangle>p # A) \<turnstile>\<^sub>\<exists> psub g q\<close>
    using ExiE by blast
  then have \<open>\<langle>\<^bold>\<star>b\<rangle>(psub g p) # map (psub g) A \<turnstile>\<^sub>\<exists> psub g q\<close>
    unfolding g_def by simp
  ultimately have \<open>map (psub g) A \<turnstile>\<^sub>\<exists> psub g q\<close>
    using b' by fastforce
  moreover have \<open>psub g q = psub f q\<close> \<open>map (psub g) A = map (psub f) A\<close>
    unfolding g_def using ExiE.hyps(3) by simp_all
  ultimately show ?case
    by metis
next
  case (Clas p q A)
  then show ?case
    using Calculus.Clas by auto
qed

lemma Weaken:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  shows \<open>A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> B \<turnstile>\<^sub>\<exists> p\<close>
proof (induct A p arbitrary: B pred: Calculus)
  case (Assm p A)
  then show ?case
    by auto
next
  case (FlsE A p)
  then show ?case
    using Calculus.FlsE by blast
next
  case (ImpI p A q)
  then show ?case
    by (simp add: Calculus.ImpI subset_code(1))
next
  case (ImpE A p q)
  then show ?case
    by blast
next
  case (ExiI A t p)
  then show ?case
    by blast
next
  case (ExiE A p a q)
  let ?params = \<open>params' (p # q # B)\<close>
  have \<open>finite ?params\<close>
    by simp
  then obtain b where b: \<open>b \<notin> ?params\<close>
    using ex_new_if_finite infinite_UNIV by blast
  then have b': \<open>b \<notin> params' A\<close>
    using ExiE by auto

  define f where \<open>f \<equiv> id(a := b, b := a)\<close>
  let ?B = \<open>map (psub f) B\<close>

  have f: \<open>\<forall>p \<in> set A. psub f p = p\<close>
    using ExiE(3) b' by (simp add: fm.map_id f_def)
  then have \<open>set A \<subseteq> set ?B\<close>
    using ExiE.prems by force
  then have \<open>?B \<turnstile>\<^sub>\<exists> \<^bold>\<exists> p\<close>
    using ExiE.hyps by blast

  moreover have \<open>\<langle>\<^bold>\<star>a\<rangle>p \<in> set (\<langle>\<^bold>\<star>a\<rangle>p # ?B)\<close>
    using ExiE(3) b by (auto simp: fm.map_id0)
  then have \<open>set (\<langle>\<^bold>\<star> a\<rangle> p # A) \<subseteq> set (\<langle>\<^bold>\<star>a\<rangle>p # ?B)\<close>
    using \<open>set A \<subseteq> set ?B\<close> by auto
  then have \<open>\<langle>\<^bold>\<star>a\<rangle>p # ?B \<turnstile>\<^sub>\<exists> q\<close>
    using ExiE(5) by blast

  moreover have \<open>a \<notin> params' (p # q # ?B)\<close>
    using ExiE(3) b by (simp add: fm.set_map(1) image_iff f_def)

  ultimately have \<open>?B \<turnstile>\<^sub>\<exists> q\<close>
    by fast
  then have \<open>map (psub f) ?B \<turnstile>\<^sub>\<exists> psub f q\<close>
    using Calculus_psub by blast
  moreover have \<open>psub f q = q\<close>
    using ExiE.hyps(3) b fm.map_id unfolding f_def by auto
  moreover have \<open>f o f = id\<close>
    unfolding f_def by auto
  then have \<open>psub f o psub f = id\<close>
    by (auto simp: fm.map_comp fm.map_id0)
  then have \<open>map (psub f) ?B = B\<close>
    unfolding map_map by (metis list.map_id)
  ultimately show ?case
    by simp
next
  case (Clas p q A)
  then show ?case
    using Calculus.Clas
    by (metis insert_mono list.simps(15))
qed

section \<open>Soundness\<close>

theorem soundness: \<open>A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> \<forall>q \<in> set A. (E, F, G) \<Turnstile>\<^sub>\<exists> q \<Longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<exists> p\<close>
proof (induct p arbitrary: F pred: Calculus)
  case (ExiE A p a q)
  then obtain x where \<open>(x \<Zsemi> E, F, G) \<Turnstile>\<^sub>\<exists> p\<close>
    by fastforce
  then have \<open>(E, F(a := \<lambda>_. x), G) \<Turnstile>\<^sub>\<exists> \<langle>\<^bold>\<star>a\<rangle>p\<close>
    using ExiE(3) by simp
  moreover have \<open>\<forall>q \<in> set A. (E, F(a := \<lambda>_. x), G) \<Turnstile>\<^sub>\<exists> q\<close>
    using ExiE(3, 6) by simp
  ultimately have \<open>(E, F(a := \<lambda>_. x), G) \<Turnstile>\<^sub>\<exists> q\<close>
    using ExiE(5) by simp
  then show ?case
    using ExiE(3) by simp
qed auto

corollary soundness': \<open>[] \<turnstile>\<^sub>\<exists> p \<Longrightarrow> M \<Turnstile>\<^sub>\<exists> p\<close>
  using soundness by (cases M) fastforce

corollary \<open>\<not> ([] \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>)\<close>
  using soundness' by fastforce

section \<open>Admissible Rules\<close>

lemma Assm_head: \<open>p # A \<turnstile>\<^sub>\<exists> p\<close>
  by auto

lemma Boole: \<open>(\<^bold>\<not> p) # A \<turnstile>\<^sub>\<exists> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p\<close>
  using Clas FlsE by blast

corollary Weak:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  shows \<open>A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> q # A \<turnstile>\<^sub>\<exists> p\<close>
  using Weaken[where B=\<open>q # A\<close>] by auto

lemma deduct1:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  shows \<open>A \<turnstile>\<^sub>\<exists> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # A \<turnstile>\<^sub>\<exists> q\<close>
  using Assm_head Weak by blast

lemma Weak':
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  shows \<open>A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> B @ A \<turnstile>\<^sub>\<exists> p\<close>
  by (induct B) (simp_all add: Weak)

interpretation Derivations \<open>Calculus :: ('f :: inf_univ, 'p) fm list \<Rightarrow> _\<close>
proof
  show \<open>\<And>A p. p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<exists> p\<close>
    by simp
next
  show \<open>\<And>A B. A \<turnstile>\<^sub>\<exists> r \<Longrightarrow> set A = set B \<Longrightarrow> B \<turnstile>\<^sub>\<exists> r\<close> for r :: \<open>('f, 'p) fm\<close>
    using Weaken by blast
qed

section \<open>Maximal Consistent Sets\<close>

definition consistent :: \<open>('f, 'p) fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>

fun witness :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm set \<Rightarrow> ('f, 'p) fm set\<close> where
  \<open>witness (\<^bold>\<exists>p) S = (let a = SOME a. a \<notin> params ({p} \<union> S) in {\<langle>\<^bold>\<star>a\<rangle>p})\<close>
| \<open>witness _ _ = {}\<close>

lemma consistent_add_witness:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  assumes \<open>consistent S\<close> \<open>\<^bold>\<exists>p \<in> S\<close> \<open>a \<notin> params S\<close>
  shows \<open>consistent ({\<langle>\<^bold>\<star>a\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof safe
  fix A
  assume \<open>set A \<subseteq> {\<langle>\<^bold>\<star>a\<rangle>p} \<union> S\<close> \<open>A \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>
  then obtain A' where \<open>set A' \<subseteq> S\<close> \<open>(\<langle>\<^bold>\<star>a\<rangle>p) # A' \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>
    using assms derive_split1 by (metis consistent_def insert_is_Un subset_insert)
  then have \<open>\<langle>\<^bold>\<star>a\<rangle>p # A' \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>
    using Boole by blast
  then have \<open>\<langle>\<^bold>\<star>a\<rangle>p # \<^bold>\<exists>p # A' \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>
    using Weak deduct1 by blast
  moreover have \<open>a \<notin> params_fm p\<close> \<open>\<forall>p \<in> set (\<^bold>\<exists>p # A'). a \<notin> params_fm p\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2-3) by auto
  then have \<open>a \<notin> params ({p} \<union> {\<^bold>\<bottom>} \<union> set (\<^bold>\<exists>p # A'))\<close>
    using calculation by simp
  moreover have \<open>\<^bold>\<exists>p # A' \<turnstile>\<^sub>\<exists> \<^bold>\<exists>p\<close>
    by simp
  ultimately have \<open>\<^bold>\<exists>p # A' \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>
    by fastforce
  moreover have \<open>set (\<^bold>\<exists>p # A') \<subseteq> S\<close>
    using \<open>set A' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_witness':
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  assumes \<open>consistent ({p} \<union> S)\<close> \<open>infinite (UNIV - params S)\<close>
  shows \<open>consistent (witness p S \<union> {p} \<union> S)\<close>
  using assms
proof (induct p S rule: witness.induct)
  case (1 p S)
  have \<open>infinite (UNIV - params ({p} \<union> S))\<close>
    using 1(2) finite_params_fm by (simp add: infinite_Diff_fin_Un)
  then have \<open>\<exists>a. a \<notin> params ({p} \<union> S)\<close>
    by (simp add: not_finite_existsD set_diff_eq)
  then have \<open>(SOME a. a \<notin> params ({p} \<union> S)) \<notin> params ({p} \<union> S)\<close>
    by (rule someI_ex)
  then obtain a where a: \<open>witness (\<^bold>\<exists>p) S = {\<langle>\<^bold>\<star>a\<rangle>p}\<close> \<open>a \<notin> params ({\<^bold>\<exists>p} \<union> S)\<close>
    by simp
  then show ?case
    using 1(1-2) a(1) consistent_add_witness[where S=\<open>{\<^bold>\<exists>p} \<union> S\<close>] by auto
qed (auto simp: assms)

interpretation MCS_Witness_UNIV consistent witness \<open>params_fm :: ('f :: inf_univ, 'p) fm \<Rightarrow> _\<close>
proof
  fix p and S :: \<open>('f, 'p) fm set\<close>
  show \<open>finite (params (witness p S))\<close>
    by (induct p S rule: witness.induct) simp_all
next
  fix p and S :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent ({p} \<union> S)\<close> \<open>infinite (UNIV - params S)\<close>
  then show \<open>consistent ({p} \<union> S \<union> witness p S)\<close>
    using consistent_witness' by (simp add: sup_commute)
next
  show \<open>infinite (UNIV :: ('f, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed (auto simp: consistent_def)

interpretation Derivations_Cut_MCS consistent \<open>Calculus :: ('f :: inf_univ, 'p) fm list \<Rightarrow> _\<close>
proof
  show \<open>\<And>S. consistent S = (\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile>\<^sub>\<exists> q))\<close>
    unfolding consistent_def using FlsE by blast
next
  show \<open>\<And>A B p. A \<turnstile>\<^sub>\<exists> p \<Longrightarrow> p # B \<turnstile>\<^sub>\<exists> q \<Longrightarrow> A @ B \<turnstile>\<^sub>\<exists> q\<close> for q :: \<open>('f, 'p) fm\<close>
    by (metis ImpE ImpI Un_upper1 Weak' Weaken set_append)
qed

interpretation Derivations_Bot consistent Calculus \<open>\<^bold>\<bottom> :: ('f :: inf_univ, 'p) fm\<close>
proof
qed fast

interpretation Derivations_Imp consistent Calculus \<open>\<lambda>p q. p \<^bold>\<longrightarrow> q :: ('f :: inf_univ, 'p) fm\<close>
proof qed fast+

interpretation Derivations_Exi consistent witness params_fm Calculus \<open>\<^bold>\<exists>\<close> \<open>\<lambda>t p. \<langle>t\<rangle>p :: ('f :: inf_univ, 'p) fm\<close>
proof qed auto

section \<open>Truth Lemma\<close>

abbreviation canonical :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model\<close> (\<open>\<M>\<^sub>\<exists>\<close>) where
  \<open>\<M>\<^sub>\<exists>(S) \<equiv> (\<^bold>#, \<^bold>\<bullet>, \<lambda>P ts. \<^bold>\<cdot>P ts \<in> S)\<close>

fun semics ::
  \<open>('a, 'f, 'p) model \<Rightarrow> (('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close>
  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<exists> _)\<close> [55, 0, 55] 55) where
  \<open>_ \<lbrakk>_\<rbrakk>\<^sub>\<exists> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(E, F, G) \<lbrakk>_\<rbrakk>\<^sub>\<exists> \<^bold>\<cdot>P ts \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>(E, F, G) \<lbrakk>\<R>\<rbrakk>\<^sub>\<exists> p \<^bold>\<longrightarrow> q \<longleftrightarrow> \<R> (E, F, G) p \<longrightarrow> \<R> (E, F, G) q\<close>
| \<open>(E, F, G) \<lbrakk>\<R>\<rbrakk>\<^sub>\<exists> \<^bold>\<exists>p \<longleftrightarrow> (\<exists>x. \<R> (x \<Zsemi> E, F, G) p)\<close>

fun rel :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>\<R>\<^sub>\<exists>\<close>) where
  \<open>\<R>\<^sub>\<exists>(S) (E, _, _) p \<longleftrightarrow> sub_fm E p \<in> S\<close>

theorem saturated_model:
  assumes \<open>\<And>p. \<forall>M \<in> {\<M>\<^sub>\<exists>(S)}. M \<lbrakk>\<R>\<^sub>\<exists>(S)\<rbrakk>\<^sub>\<exists> p \<longleftrightarrow> \<R>\<^sub>\<exists>(S) M p\<close> \<open>M \<in> {\<M>\<^sub>\<exists>(S)}\<close>
  shows \<open>\<R>\<^sub>\<exists>(S) M p \<longleftrightarrow> M \<Turnstile>\<^sub>\<exists> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms(1)[of x] assms(2) by (cases x) simp_all
qed

theorem saturated_MCS:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  assumes \<open>MCS S\<close>
  shows \<open>\<R>\<^sub>\<exists>(S) (\<M>\<^sub>\<exists>(S)) p \<longleftrightarrow> \<M>\<^sub>\<exists>(S) \<lbrakk>\<R>\<^sub>\<exists>(S)\<rbrakk>\<^sub>\<exists> p\<close>
  using assms by (cases p) (auto cong: map_cong)

interpretation Truth_Witness semics semantics_fm \<open>\<lambda>S. {\<M>\<^sub>\<exists>(S)}\<close> rel consistent witness
  \<open>params_fm :: ('f :: inf_univ, 'p) fm \<Rightarrow> _\<close>
proof
  fix p and M :: \<open>('f tm, 'f, 'p) model\<close>
  show \<open>M \<Turnstile>\<^sub>\<exists> p \<longleftrightarrow> M \<lbrakk>(\<Turnstile>\<^sub>\<exists>)\<rbrakk>\<^sub>\<exists> p\<close>
    by (cases M, induct p) auto
qed (use saturated_model saturated_MCS in blast)+

section \<open>Cardinalities\<close>

datatype marker = VarM | FunM | TmM | FlsM | PreM | ImpM | ExiM

type_synonym ('f, 'p) enc = \<open>('f + 'p) + marker \<times> nat\<close>

abbreviation \<open>FUNS f \<equiv> Inl (Inl f)\<close>
abbreviation \<open>PRES p \<equiv> Inl (Inr p)\<close>

abbreviation \<open>VAR n \<equiv> Inr (VarM, n)\<close>
abbreviation \<open>FUN n \<equiv> Inr (FunM, n)\<close>
abbreviation \<open>TM n \<equiv> Inr (TmM, n)\<close>

abbreviation \<open>PRE n \<equiv> Inr (PreM, n)\<close>
abbreviation \<open>FLS \<equiv> Inr (FlsM, 0)\<close>
abbreviation \<open>IMP n \<equiv> Inr (FlsM, n)\<close>
abbreviation \<open>EXI \<equiv> Inr (ExiM, 0)\<close>

primrec
  encode_tm :: \<open>'f tm \<Rightarrow> ('f, 'p) enc list\<close> and
  encode_tms :: \<open>'f tm list \<Rightarrow> ('f, 'p) enc list\<close> where
  \<open>encode_tm (\<^bold>#n) = [VAR n]\<close>
| \<open>encode_tm (\<^bold>\<bullet>f ts) = FUN (length ts) # FUNS f # encode_tms ts\<close>
| \<open>encode_tms [] = []\<close>
| \<open>encode_tms (t # ts) = TM (length (encode_tm t)) # encode_tm t @ encode_tms ts\<close>

lemma encode_tm_ne [simp]: \<open>encode_tm t \<noteq> []\<close>
  by (induct t) auto

lemma inj_encode_tm':
  \<open>(encode_tm t :: ('f, 'p) enc list) = encode_tm s \<Longrightarrow> t = s\<close>
  \<open>(encode_tms ts :: ('f, 'p) enc list) = encode_tms ss \<Longrightarrow> ts = ss\<close>
proof (induct t and ts arbitrary: s and ss rule: encode_tm.induct encode_tms.induct)
  case (Var n)
  then show ?case
    by (cases s) auto
next
  case (Fun f fts)
  then show ?case
    by (cases s) auto
next
  case Nil_tm
  then show ?case
    by (cases ss) auto
next
  case (Cons_tm t ts)
  then show ?case
    by (cases ss) auto
qed

lemma inj_encode_tm: \<open>inj encode_tm\<close>
  unfolding inj_def using inj_encode_tm' by blast

primrec encode_fm :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) enc list\<close> where
  \<open>encode_fm \<^bold>\<bottom> = [FLS]\<close>
| \<open>encode_fm (\<^bold>\<cdot>P ts) = PRE (length ts) # PRES P # encode_tms ts\<close>
| \<open>encode_fm (p \<^bold>\<longrightarrow> q) = IMP (length (encode_fm p)) # encode_fm p @ encode_fm q\<close>
| \<open>encode_fm (\<^bold>\<exists>p) = EXI # encode_fm p\<close>

lemma encode_fm_ne [simp]: \<open>encode_fm p \<noteq> []\<close>
  by (induct p) auto

lemma inj_encode_fm': \<open>encode_fm p = encode_fm q \<Longrightarrow> p = q\<close>
proof (induct p arbitrary: q)
  case Fls
  then show ?case
    by (cases q) auto
next
  case (Pre P ts)
  then show ?case
    by (cases q) (auto simp: inj_encode_tm')
next
  case (Imp p1 p2)
  then show ?case
    by (cases q) auto
next
  case (Exi p)
  then show ?case
    by (cases q) auto
qed

lemma inj_encode_fm: \<open>inj encode_fm\<close>
  unfolding inj_def using inj_encode_fm' by blast

lemma finite_marker: \<open>finite (UNIV :: marker set)\<close>
proof -
  have \<open>p \<in> {VarM, FunM, TmM, FlsM, PreM, ImpM, ExiM}\<close> for p
    by (cases p) auto
  then show ?thesis
    by (meson ex_new_if_finite finite.emptyI finite_insert)
qed

lemma card_of_fm:
  \<open>|UNIV :: ('f :: inf_univ, 'p) fm set| \<le>o |UNIV :: 'f set| +c |UNIV :: 'p set|\<close>
proof -
  have \<open>|UNIV :: marker set| \<le>o |UNIV :: nat set|\<close>
    using finite_marker by (simp add: ordLess_imp_ordLeq)
  moreover have \<open>infinite (UNIV :: ('f + 'p) set)\<close>
    by (simp add: inf_univ_class.infinite_UNIV)
  ultimately have \<open>|UNIV :: ('f, 'p) enc list set| \<le>o |UNIV :: ('f + 'p) set|\<close>
    using card_of_params_marker_lists by blast
  moreover have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: ('f, 'p) enc list set|\<close>
    using card_of_ordLeq inj_encode_fm by blast
  ultimately have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: ('f + 'p) set|\<close>
    using ordLeq_transitive by blast
  then show ?thesis
    unfolding csum_def by simp
qed

section \<open>Completeness\<close>

theorem strong_completeness:
  assumes \<open>\<forall>M :: ('f tm, 'f :: inf_univ, 'p) model. (\<forall>q \<in> X. M \<Turnstile>\<^sub>\<exists> q) \<longrightarrow> M \<Turnstile>\<^sub>\<exists> p\<close>
    \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params X|\<close>
  shows \<open>\<exists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<exists> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> X \<and> A \<turnstile>\<^sub>\<exists> p\<close>
  then have *: \<open>\<forall>A. set A \<subseteq> {\<^bold>\<not> p} \<union> X \<longrightarrow> \<not> A \<turnstile>\<^sub>\<exists> \<^bold>\<bottom>\<close>
    using Boole FlsE by (metis derive_split1 insert_is_Un subset_insert)

  let ?X = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?S = \<open>Extend ?X\<close>

  have \<open>consistent ?X\<close>
    unfolding consistent_def using * by blast
  moreover have \<open>infinite (UNIV - params X)\<close>
    using assms(2) inf_univ_class.infinite_UNIV
    by (metis Cinfinite_csum Cnotzero_UNIV Field_card_of cinfinite_def cinfinite_mono)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params X - params_fm (\<^bold>\<not> p)|\<close>
    using assms(2) finite_params_fm card_of_infinite_diff_finite
    by (metis ordIso_iff_ordLeq ordLeq_transitive)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - (params X \<union> params_fm (\<^bold>\<not> p))|\<close>
    by (metis Set_Diff_Un)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params ?X|\<close>
    by (metis UN_insert insert_is_Un sup_commute)
  then have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV - params ?X|\<close>
    using assms card_of_fm ordLeq_transitive by blast
  ultimately have \<open>MCS ?S\<close>
    using MCS_Extend by fast
  then have \<open>p \<in> ?S \<longleftrightarrow> \<M>\<^sub>\<exists>(?S) \<Turnstile>\<^sub>\<exists> p\<close> for p
    using truth_lemma by fastforce
  then have \<open>p \<in> ?X \<longrightarrow> \<M>\<^sub>\<exists>(?S) \<Turnstile>\<^sub>\<exists> p\<close> for p
    using Extend_subset by blast
  then have \<open>\<M>\<^sub>\<exists>(?S) \<Turnstile>\<^sub>\<exists> \<^bold>\<not> p\<close> \<open>\<forall>q \<in> X. \<M>\<^sub>\<exists>(?S) \<Turnstile>\<^sub>\<exists> q\<close>
    by blast+
  moreover from this have \<open>\<M>\<^sub>\<exists>(?S) \<Turnstile>\<^sub>\<exists> p\<close>
    using assms(1) by blast
  ultimately show False
    by simp
qed

abbreviation valid :: \<open>('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>M :: ('f tm, _, _) model. M \<Turnstile>\<^sub>\<exists> p\<close>

theorem completeness:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  assumes \<open>valid p\<close> \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
  shows \<open>[] \<turnstile>\<^sub>\<exists> p\<close>
proof -
  have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
    using assms(2)
    by (simp add: inf_univ_class.infinite_UNIV cinfinite_def csum_absorb1 ordIso_imp_ordLeq)
  then show ?thesis
    using assms strong_completeness[where X=\<open>{}\<close>] infinite_UNIV_listI by auto
qed

corollary completeness':
  fixes p :: \<open>('f :: inf_univ, 'f) fm\<close>
  assumes \<open>valid p\<close>
  shows \<open>[] \<turnstile>\<^sub>\<exists> p\<close>
  using assms completeness[of p] by simp

theorem main:
  fixes p :: \<open>('f :: inf_univ, 'p) fm\<close>
  assumes \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
  shows \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>\<exists> p\<close>
  using assms completeness soundness' by blast

corollary main':
  fixes p :: \<open>('f :: inf_univ, 'f) fm\<close>
  shows \<open>valid p \<longleftrightarrow> [] \<turnstile>\<^sub>\<exists> p\<close>
  using completeness' soundness' by blast

end
