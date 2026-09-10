theory Consistency
  imports Completeness
begin

section \<open>Consistency\<close>

text \<open>Consistency, in the typical variants: a concrete \<open>\<Sigma>\<close>-standard model over
  finite domains is exhibited (so the model class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> is non-empty), whence by
  soundness \<open>NK\<close> does not derive \<open>\<^bold>\<bottom>\<close>, and no sentence is derivable together with
  its negation.\<close>

subsection \<open>A concrete \<open>\<Sigma>\<close>-standard model over finite domains\<close>

text \<open>The carrier: an individual, the two truth values, and functions as finite graphs.
  With a one-element domain of individuals every domain \<open>D\<^bsub>\<tau>\<^esub>\<close> is finite, so the full
  function spaces of BKK Definition 3.5 are representable by graphs; \<open>en \<tau>\<close> enumerates
  \<open>D\<^bsub>\<tau>\<^esub>\<close> without repetition.\<close>

datatype mval = MI | MB bool | MF "(mval \<times> mval) list"

fun en :: "ty \<Rightarrow> mval list" where
  "en \<iota> = [MI]"
| "en \<o> = [MB True, MB False]"
| "en (\<sigma> \<^bold>\<Rightarrow> \<tau>) = map (\<lambda>vs. MF (zip (en \<sigma>) vs))
                     (List.n_lists (length (en \<sigma>)) (en \<tau>))"

definition cD :: "ty \<Rightarrow> mval \<Rightarrow> bool" where "cD \<tau> v \<equiv> v \<in> set (en \<tau>)"

fun cAp :: "mval \<Rightarrow> mval \<Rightarrow> mval" where
  "cAp (MF G) x = (case map_of G x of Some y \<Rightarrow> y | None \<Rightarrow> MI)"
| "cAp v x = MI"

definition cLm :: "ty \<Rightarrow> (mval \<Rightarrow> mval) \<Rightarrow> mval" where
 "cLm \<sigma> h \<equiv> MF (zip (en \<sigma>) (map h (en \<sigma>)))"

lemma en_nonempty: "en \<tau> \<noteq> []"
proof (induction \<tau>)
  case (Fun \<sigma> \<tau>)
  have "replicate (length (en \<sigma>)) (hd (en \<tau>)) \<in> set (List.n_lists
      (length (en \<sigma>)) (en \<tau>))" 
      using Fun.IH(2) by (auto simp: set_n_lists)
  thus ?case by auto
qed auto

lemma distinct_en: "distinct (en \<tau>)"
proof (induction \<tau>)
  case (Fun \<sigma> \<tau>)
  have "inj_on (\<lambda>vs. MF (zip (en \<sigma>) vs)) (set (List.n_lists (length (en \<sigma>)) (en \<tau>)))"
  proof
    fix vs ws
    assume "vs \<in> set (List.n_lists (length (en \<sigma>)) (en \<tau>))"
       and "ws \<in> set (List.n_lists (length (en \<sigma>)) (en \<tau>))"
    hence "vs = map snd (zip (en \<sigma>) vs)" and
          "ws = map snd (zip (en \<sigma>) ws)"
      by (auto simp: set_n_lists)
    moreover assume "MF (zip (en \<sigma>) vs) = MF (zip (en \<sigma>) ws)"
    ultimately show "vs = ws" by simp
  qed
  thus ?case
    by (simp add: distinct_map distinct_n_lists Fun.IH(2))
qed simp_all

lemma cD_fun: "cD (\<sigma> \<^bold>\<Rightarrow> \<tau>) v \<longleftrightarrow> (\<exists>vs.
  length vs = length (en \<sigma>) \<and> (\<forall>x \<in> set vs. cD \<tau> x) \<and> v = MF (zip (en \<sigma>) vs))"
  by (auto simp: cD_def set_n_lists subset_iff)

lemma cAp_cLm [simp]: "cD \<sigma> a \<Longrightarrow> cAp (cLm \<sigma> h) a = h a"
  by (simp add: cLm_def cD_def map_of_zip_map)

lemma cLm_dom: "(\<And>d. cD \<sigma> d \<Longrightarrow> cD \<tau> (h d)) \<Longrightarrow> cD (\<sigma> \<^bold>\<Rightarrow> \<tau>) (cLm \<sigma> h)"
  unfolding cD_fun cLm_def
  by (rule exI[of _ "map h (en \<sigma>)"]) (auto simp: cD_def)

lemma cAp_dom: "cD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f \<Longrightarrow> cD \<sigma> a \<Longrightarrow> cD \<tau> (cAp f a)"
proof -
  assume "cD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f" and a: "cD \<sigma> a"
  then obtain vs where vs: "length vs = length (en \<sigma>)" "\<forall>x \<in> set vs. cD \<tau> x"
    and f: "f = MF (zip (en \<sigma>) vs)" unfolding cD_fun by blast
  obtain b where "map_of (zip (en \<sigma>) vs) a = Some b" using a vs(1)
    unfolding cD_def by (metis map_of_zip_is_Some)
  moreover from this have "b \<in> set vs"
    by (metis map_of_SomeD set_zip_rightD)
  ultimately show ?thesis using vs(2) f by simp
qed

lemma cAp_ext:
  assumes f: "cD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f" and g: "cD (\<sigma> \<^bold>\<Rightarrow> \<tau>) g"
      and ag: "\<And>a. cD \<sigma> a \<Longrightarrow> cAp f a = cAp g a"
    shows "f = g"
proof -
  obtain vs where vs: "length vs = length (en \<sigma>)" and fv: "f = MF (zip (en \<sigma>) vs)"  
    using f unfolding cD_fun by blast
  obtain ws where ws: "length ws = length (en \<sigma>)" and gw: "g = MF (zip (en \<sigma>) ws)" 
    using g unfolding cD_fun by blast
  have "vs ! i = ws ! i" if i: "i < length (en \<sigma>)" for i
  proof -
    have d: "cD \<sigma> (en \<sigma> ! i)" using i by (simp add: cD_def)
    have iv: "i < length vs" and iw: "i < length ws" using i vs ws
      by simp_all
    have "cAp f (en \<sigma> ! i) = vs ! i"
      using map_of_zip_nth[OF vs[symmetric] distinct_en iv] fv
      by simp
    moreover have "cAp g (en \<sigma> ! i) = ws ! i"
      using map_of_zip_nth[OF ws[symmetric] distinct_en iw] gw
      by simp
    ultimately show ?thesis using ag[OF d] by simp
  qed
  hence "vs = ws" using vs ws by (intro nth_equalityI) auto
  thus ?thesis using fv gw by simp
qed

text \<open>The denotations of the logical constants, and a canonical parameter
    and assignment interpretation.\<close>

definition cNg :: mval where "cNg \<equiv> cLm \<o> (\<lambda>a. MB (a = MB False))"
definition cDs :: mval where
  "cDs \<equiv> cLm \<o> (\<lambda>a. cLm \<o> (\<lambda>b. MB (a = MB True \<or> b = MB True)))"
definition cPi :: "ty \<Rightarrow> mval" where
  "cPi \<sigma> \<equiv> cLm (\<sigma> \<^bold>\<Rightarrow> \<o>) (\<lambda>f. MB (\<forall>d. cD \<sigma> d \<longrightarrow> cAp f d = MB True))"
definition cEv :: "ty \<Rightarrow> mval" where
  "cEv \<sigma> \<equiv> cLm \<sigma> (\<lambda>a. cLm \<sigma> (\<lambda>b. MB (a = b)))"
definition cIv :: "ty \<Rightarrow> mval" where
  "cIv \<sigma> \<equiv> cLm (\<sigma> \<^bold>\<Rightarrow> \<o>)
    (\<lambda>f. if \<exists>a. cD \<sigma> a \<and> (\<forall>b. cD \<sigma> b \<longrightarrow> (cAp f b = MB True) = (b = a))
         then SOME a. cD \<sigma> a \<and> (\<forall>b. cD \<sigma> b \<longrightarrow> (cAp f b = MB True) = (b = a))
         else hd (en \<sigma>))"

abbreviation cJv :: "'p \<Rightarrow> ty \<Rightarrow> mval" where "cJv p \<sigma> \<equiv> hd (en \<sigma>)"
abbreviation cXi :: "nat \<Rightarrow> ty \<Rightarrow> mval" where "cXi n \<sigma> \<equiv> hd (en \<sigma>)"

lemma cD_bool: "cD \<o> v \<longleftrightarrow> v = MB True \<or> v = MB False"
  by (simp add: cD_def)

lemma hd_en_dom: "cD \<sigma> (hd (en \<sigma>))" by (simp add: cD_def en_nonempty)

lemma cIv_desc:
  assumes f: "cD (\<sigma> \<^bold>\<Rightarrow> \<o>) f" and a: "cD \<sigma> a"
      and sing: "\<forall>b. cD \<sigma> b \<longrightarrow> (cAp f b = MB True) = (b = a)"
    shows "cAp (cIv \<sigma>) f = a"
proof -
  let ?P = "\<lambda>x. cD \<sigma> x \<and> (\<forall>b. cD \<sigma> b \<longrightarrow> (cAp f b = MB True) = (b = x))"
  have ex: "\<exists>x. ?P x" using a sing by blast
  have "cAp (cIv \<sigma>) f = (SOME x. ?P x)"
    unfolding cIv_def using cAp_cLm[OF f] ex by simp
  moreover have "(SOME x. ?P x) = a"
  proof (rule someI2_ex[OF ex])
    fix x assume x: "?P x"
    have "cAp f a = MB True" using a sing by blast
    thus "x = a" using x a by blast
  qed
  ultimately show ?thesis by simp
qed

theorem concrete_standard_model:
  "standard_model cD cAp cLm (MB True) (MB False) cNg cDs cIv cEv cPi (cJv :: 'p \<Rightarrow> ty \<Rightarrow> mval)"
proof
  show \<open>cD ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>) (cIv \<sigma>)\<close> for \<sigma>
    unfolding cIv_def
    by (rule cLm_dom) (auto simp: hd_en_dom intro: someI2_ex)
next
  fix a b
  assume 13: \<open>cD \<o> a\<close> \<open>cD \<o> b\<close>
  have inner: "cAp cDs d = cLm \<o> (\<lambda>b. MB (d = MB True \<or> b = MB True))"
    if "cD \<o> d" for d unfolding cDs_def by (rule cAp_cLm[OF that])
  have ds: "cAp (cAp cDs d) e = MB (d = MB True \<or> e = MB True)"
    if d: "cD \<o> d" and e: "cD \<o> e" for d e unfolding inner[OF d]
    by (rule cAp_cLm[OF e])
  show \<open>(cAp (cAp cDs a) b = MB True) = (a = MB True \<or> b = MB True)\<close>
    unfolding ds[OF 13(1) 13(2)] by simp
qed(auto simp: cAp_ext cDs_def cIv_desc cEv_def cPi_def cNg_def cD_bool hd_en_dom
         intro!: cLm_dom cAp_dom)

subsection \<open>Consistency of \<open>NK\<close>\<close>

text \<open>The \<open>\<Sigma>\<close>-model predicate of the canonical construction, exported from the
  sublocale chain \<open>standard_model \<subseteq> general_model \<subseteq> bkk_model\<close>.\<close>

lemma (in general_model) bkk_model_pred:
  "bkk_model Dm Ap (\<lambda>\<xi> A. \<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>) (\<lambda>a. a = Tv)" by intro_locales

text \<open>Consistency of \<open>NK\<close> (the deep embedding): \<open>\<^bold>\<bottom>\<close> is not derivable --- by soundness
  (BKK Theorem 7.3) it would have to be \<open>\<upsilon>\<close>-true in the concrete model, contradicting
  BKK Lemma 3.43.\<close>

theorem nk_consistent: "\<not> (\<turnstile> (\<^bold>\<bottom> :: 'p tm))"
proof
  assume d: "\<turnstile> (\<^bold>\<bottom> :: 'p tm)"
  interpret standard_model cD cAp cLm "MB True" "MB False" cNg cDs cIv cEv cPi
                           "cJv :: 'p \<Rightarrow> ty \<Rightarrow> mval"
    by (rule concrete_standard_model)
  have xi: "bkkA.asg cXi" by (simp add: bkkA.asg_def hd_en_dom)
  have "den (\<^bold>\<bottom> :: 'p tm) cXi = MB True"
    using soundness_bkk[OF d bkk_model_pred xi] by simp
  thus False using bkk.vl_TF[OF xi] by simp
qed

text \<open>No sentence is derivable together with its negation.\<close>

theorem nk_not_both: assumes "\<turnstile> (A :: 'p tm)" shows "\<not>\<turnstile> \<^bold>\<not> A"
  using bprov.NegE[OF _ assms wff_FalseB] nk_consistent by blast

text \<open>In the terminology of the completeness development: the empty set is consistent
  (BKK Definition 7.4).\<close>

corollary con_empty: "con ({} :: 'p tm set)"
  unfolding con_def by (rule nk_consistent)

end
