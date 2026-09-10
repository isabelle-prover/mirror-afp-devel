theory Consistency
  imports Soundness
begin

section \<open>Consistency\<close>

text \<open>Is \<open>NK\<close> consistent, and at what cost? It is, and cheaply: the proof stays within
  Isabelle/HOL and needs only \<open>Soundness\<close>. A concrete \<open>\<Sigma>\<close>-standard model over finite domains
  is exhibited --- so the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> is non-empty --- whence by soundness \<open>NK\<close> does
  not derive \<open>\<^bold>\<bottom>\<close>, and no sentence is derivable together with its negation. Since \<open>NK\<close>
  carries no axiom of infinity it admits finite models, so neither an infinite carrier nor a
  set-theoretic meta-theory is needed, and the parameter type stays unconstrained.  The
  statement is purely syntactic --- non-derivability of \<open>\<^bold>\<bottom>\<close> in the calculus --- with a
  standard model as its witness; that witness lies in the larger class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> only
  because soundness is proved there.

  The model is built once, for every finite size \<open>k > 0\<close> of the individual domain and with a
  parameter interpretation that can distinguish any prescribed finite family of parameters.
  Consistency needs only the one-element instance \<open>k = 1\<close>; the arbitrarily large instances
  feed the compactness route to the infinity scheme in \<open>NK_Infinity\<close>.\<close>

subsection \<open>A parametric family of finite standard models\<close>

text \<open>The carrier: individuals \<open>VI 0, \<dots>, VI (k-1)\<close>, the two truth values, and functions as
  finite graphs.  With a finite domain of individuals every domain \<open>D\<^bsub>\<tau>\<^esub>\<close> is finite, so the
  full function spaces of BKK Definition 3.5 are representable by graphs; \<open>en k \<tau>\<close> enumerates
  \<open>D\<^bsub>\<tau>\<^esub>\<close> without repetition.\<close>

datatype ival = VI nat | VB bool | VF "(ival \<times> ival) list"

fun en :: "nat \<Rightarrow> ty \<Rightarrow> ival list" where
  "en k \<iota> = map VI [0..<k]"
| "en k \<o> = [VB True, VB False]"
| "en k (\<sigma> \<^bold>\<Rightarrow> \<tau>) = map (\<lambda>vs. VF (zip (en k \<sigma>) vs))
                       (List.n_lists (length (en k \<sigma>)) (en k \<tau>))"

definition cD :: "nat \<Rightarrow> ty \<Rightarrow> ival \<Rightarrow> bool" where "cD k \<tau> v \<equiv> v \<in> set (en k \<tau>)"

fun cAp :: "ival \<Rightarrow> ival \<Rightarrow> ival" where
  "cAp (VF G) x = (case map_of G x of Some y \<Rightarrow> y | None \<Rightarrow> VB False)"
| "cAp v x = VB False"

definition cLm :: "nat \<Rightarrow> ty \<Rightarrow> (ival \<Rightarrow> ival) \<Rightarrow> ival" where
 "cLm k \<sigma> h \<equiv> VF (zip (en k \<sigma>) (map h (en k \<sigma>)))"

lemma en_nonempty: "0 < k \<Longrightarrow> en k \<tau> \<noteq> []"
proof (induction \<tau>)
  case Ind then show ?case by simp
next
  case Bool then show ?case by simp
next
  case (Fun \<sigma> \<tau>)
  have "replicate (length (en k \<sigma>)) (hd (en k \<tau>)) \<in> set (List.n_lists
      (length (en k \<sigma>)) (en k \<tau>))"
      using Fun by (auto simp: set_n_lists)
  thus ?case by auto
qed

lemma distinct_en: "distinct (en k \<tau>)"
proof (induction \<tau>)
  case (Fun \<sigma> \<tau>)
  have "inj_on (\<lambda>vs. VF (zip (en k \<sigma>) vs)) (set (List.n_lists (length (en k \<sigma>)) (en k \<tau>)))"
  proof
    fix vs ws
    assume "vs \<in> set (List.n_lists (length (en k \<sigma>)) (en k \<tau>))"
       and "ws \<in> set (List.n_lists (length (en k \<sigma>)) (en k \<tau>))"
    hence "vs = map snd (zip (en k \<sigma>) vs)" and
          "ws = map snd (zip (en k \<sigma>) ws)"
      by (auto simp: set_n_lists)
    moreover assume "VF (zip (en k \<sigma>) vs) = VF (zip (en k \<sigma>) ws)"
    ultimately show "vs = ws" by simp
  qed
  thus ?case
    by (simp add: distinct_map distinct_n_lists Fun.IH(2))
qed (auto simp: distinct_map inj_on_def)

lemma cD_fun: "cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) v \<longleftrightarrow> (\<exists>vs.
  length vs = length (en k \<sigma>) \<and> (\<forall>x \<in> set vs. cD k \<tau> x) \<and> v = VF (zip (en k \<sigma>) vs))"
  by (auto simp: cD_def set_n_lists subset_iff)

lemma cAp_cLm [simp]: "cD k \<sigma> a \<Longrightarrow> cAp (cLm k \<sigma> h) a = h a"
  by (simp add: cLm_def cD_def map_of_zip_map)

lemma cLm_dom: "(\<And>d. cD k \<sigma> d \<Longrightarrow> cD k \<tau> (h d)) \<Longrightarrow> cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) (cLm k \<sigma> h)"
  unfolding cD_fun cLm_def
  by (rule exI[of _ "map h (en k \<sigma>)"]) (auto simp: cD_def)

lemma cAp_dom: "cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) f \<Longrightarrow> cD k \<sigma> a \<Longrightarrow> cD k \<tau> (cAp f a)"
proof -
  assume "cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) f" and a: "cD k \<sigma> a"
  then obtain vs where vs: "length vs = length (en k \<sigma>)" "\<forall>x \<in> set vs. cD k \<tau> x"
    and f: "f = VF (zip (en k \<sigma>) vs)" unfolding cD_fun by blast
  obtain b where "map_of (zip (en k \<sigma>) vs) a = Some b" using a vs(1)
    unfolding cD_def by (metis map_of_zip_is_Some)
  moreover from this have "b \<in> set vs"
    by (metis map_of_SomeD set_zip_rightD)
  ultimately show ?thesis using vs(2) f by simp
qed

lemma cAp_ext:
  assumes f: "cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) f" and g: "cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) g"
      and ag: "\<And>a. cD k \<sigma> a \<Longrightarrow> cAp f a = cAp g a"
    shows "f = g"
proof -
  obtain vs where vs: "length vs = length (en k \<sigma>)" and fv: "f = VF (zip (en k \<sigma>) vs)"
    using f unfolding cD_fun by blast
  obtain ws where ws: "length ws = length (en k \<sigma>)" and gw: "g = VF (zip (en k \<sigma>) ws)"
    using g unfolding cD_fun by blast
  have "vs ! i = ws ! i" if i: "i < length (en k \<sigma>)" for i
  proof -
    have d: "cD k \<sigma> (en k \<sigma> ! i)" using i by (simp add: cD_def)
    have iv: "i < length vs" and iw: "i < length ws" using i vs ws by simp_all
    have "cAp f (en k \<sigma> ! i) = vs ! i"
      using map_of_zip_nth[OF vs[symmetric] distinct_en iv] fv by simp
    moreover have "cAp g (en k \<sigma> ! i) = ws ! i"
      using map_of_zip_nth[OF ws[symmetric] distinct_en iw] gw by simp
    ultimately show ?thesis using ag[OF d] by simp
  qed
  hence "vs = ws" using vs ws by (intro nth_equalityI) auto
  thus ?thesis using fv gw by simp
qed

subsection \<open>Parameters (with a prescribed diagram), assignment, and the model\<close>

text \<open>The logical constants need not be built by hand: the frame just constructed is a
  @{locale lambda_universe} (Section 2), so negation, disjunction, quantification, equality
  and description come from that interface --- description by definite description
  (\<open>THE\<close>), so no Hilbert choice enters the model construction.  The parameter
  interpretation is prescribed by an index map \<open>ix\<close>: parameter \<open>p\<close> denotes the individual
  \<open>VI (ix p)\<close> at type \<open>\<iota>\<close> (and a canonical value elsewhere), so that parameters with
  distinct indices denote distinct individuals.\<close>

definition cJv :: "nat \<Rightarrow> ('p \<Rightarrow> nat) \<Rightarrow> 'p \<Rightarrow> ty \<Rightarrow> ival" where
  "cJv k ix p \<sigma> \<equiv> (if \<sigma> = \<iota> then VI (ix p) else hd (en k \<sigma>))"

definition cXi :: "nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ival" where "cXi k n \<sigma> \<equiv> hd (en k \<sigma>)"

lemma cD_bool: "cD k \<o> v \<longleftrightarrow> v = VB True \<or> v = VB False"
  by (simp add: cD_def)

lemma hd_en_dom: "0 < k \<Longrightarrow> cD k \<sigma> (hd (en k \<sigma>))" by (simp add: cD_def en_nonempty)

theorem concrete_lambda_universe:
  assumes k: "0 < k" and ix: "\<And>p. ix p < k"
  shows "lambda_universe (cD k) cAp (cLm k) (VB True) (VB False)
           (cJv k ix :: 'p \<Rightarrow> ty \<Rightarrow> ival)"
proof
  show "\<And>\<sigma> \<tau> h a. (\<And>d. cD k \<sigma> d \<Longrightarrow> cD k \<tau> (h d)) \<Longrightarrow> cD k \<sigma> a \<Longrightarrow> cAp (cLm k \<sigma> h) a = h a"
    by simp
  show "\<And>\<sigma> \<tau> h. (\<And>d. cD k \<sigma> d \<Longrightarrow> cD k \<tau> (h d)) \<Longrightarrow> cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) (cLm k \<sigma> h)"
    by (rule cLm_dom)
  show "\<And>\<sigma> \<tau> f a. cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) f \<Longrightarrow> cD k \<sigma> a \<Longrightarrow> cD k \<tau> (cAp f a)" by (rule cAp_dom)
  show "\<And>\<sigma> \<tau> g h. cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) g \<Longrightarrow> cD k (\<sigma> \<^bold>\<Rightarrow> \<tau>) h \<Longrightarrow>
         (\<And>a. cD k \<sigma> a \<Longrightarrow> cAp g a = cAp h a) \<Longrightarrow> g = h" by (rule cAp_ext)
  show "VB True \<noteq> VB False" by simp
  show "\<And>a. cD k \<o> a \<longleftrightarrow> a = VB True \<or> a = VB False" by (rule cD_bool)
  show "\<And>p \<sigma>. cD k \<sigma> (cJv k ix p \<sigma>)"
    unfolding cJv_def using k ix hd_en_dom by (auto simp: cD_def)
qed

lemmas concrete_standard_model =
  lambda_universe.is_standard_model[OF concrete_lambda_universe]

subsection \<open>Consistency of \<open>NK\<close>\<close>

text \<open>Consistency of \<open>NK\<close> (the deep embedding): \<open>\<^bold>\<bottom>\<close> is not derivable --- by soundness
  (BKK Theorem 7.3) it would have to be \<open>\<upsilon>\<close>-true in the one-element instance \<open>k = 1\<close> of the
  finite model, contradicting BKK Lemma 3.43. The argument uses only soundness and one finite
  model; it needs neither the completeness development nor an infinite carrier.\<close>

theorem nk_consistent: "\<not> (\<turnstile> (\<^bold>\<bottom> :: 'p tm))"
proof
  assume d: "\<turnstile> (\<^bold>\<bottom> :: 'p tm)"
  define k :: nat where "k = 1"
  have kpos: "0 < k" by (simp add: k_def)
  interpret U: lambda_universe "cD k" cAp "cLm k" "VB True" "VB False"
    "cJv k (\<lambda>_. 0) :: 'p \<Rightarrow> ty \<Rightarrow> ival"
    by (rule concrete_lambda_universe[OF kpos]) (simp add: k_def)
  interpret standard_model "cD k" cAp "cLm k" "VB True" "VB False"
    U.Ngv U.Dsv U.Iv U.Ev U.Piv "cJv k (\<lambda>_. 0) :: 'p \<Rightarrow> ty \<Rightarrow> ival"
    by (rule U.is_standard_model)
  have xi: "bkkA.asg (cXi k)" by (simp add: bkkA.asg_def cXi_def hd_en_dom[OF kpos])
  have "con ({} :: 'p tm set)" by (rule model_con[OF xi]) simp
  thus False using d by (simp add: con_def)
qed

text \<open>No sentence is derivable together with its negation.\<close>

theorem nk_not_both: assumes "\<turnstile> (A :: 'p tm)" shows "\<not>\<turnstile> \<^bold>\<not> A"
  using bprov.NegE[OF _ assms wff_FalseB] nk_consistent by blast

text \<open>The same, in the \<open>con\<close>sistency terminology of BKK Definition 7.4 (\<open>con\<close> lives in
  \<open>Calculus\<close>): the empty set is consistent.  That this theory imports only \<open>Soundness\<close>
  makes the dependency graph itself witness that consistency is independent of the
  completeness development.\<close>

corollary con_empty: "con ({} :: 'p tm set)"
  unfolding con_def by (rule nk_consistent)

end
