header{*Relations, Families, Ordinals*}

theory Ordinal imports HF
begin

section{*Relations and Functions*}

definition is_hpair :: "hf \<Rightarrow> bool"
  where "is_hpair z = (\<exists>x y. z = \<langle>x,y\<rangle>)"

definition hconverse :: "hf \<Rightarrow> hf"
  where "hconverse(r) = \<lbrace>z. w \<^bold>\<in> r, \<exists>x y. w = \<langle>x,y\<rangle> & z = \<langle>y,x\<rangle>\<rbrace>"

definition hdomain :: "hf \<Rightarrow> hf"
  where "hdomain(r) = \<lbrace>x. w \<^bold>\<in> r, \<exists>y. w = \<langle>x,y\<rangle>\<rbrace>"

definition hrange :: "hf \<Rightarrow> hf"
  where "hrange(r) = hdomain(hconverse(r))"

definition hrelation :: "hf \<Rightarrow> bool"
  where "hrelation(r) = (\<forall>z. z \<^bold>\<in> r \<longrightarrow> is_hpair z)"

definition hrestrict :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  --{* Restrict the relation r to the domain A *}
  where "hrestrict r A = \<lbrace>z \<^bold>\<in> r. \<exists>x \<^bold>\<in> A. \<exists>y. z = \<langle>x,y\<rangle>\<rbrace>"

definition nonrestrict :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "nonrestrict r A = \<lbrace>z \<^bold>\<in> r. \<forall>x \<^bold>\<in> A. \<forall>y. z \<noteq> \<langle>x,y\<rangle>\<rbrace>"

definition hfunction :: "hf \<Rightarrow> bool"
  where "hfunction(r) = (\<forall>x y. \<langle>x,y\<rangle> \<^bold>\<in> r \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle> \<^bold>\<in> r \<longrightarrow> y=y'))"

definition app :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "app f x = (THE y. \<langle>x, y\<rangle> \<^bold>\<in> f)"

lemma hrestrict_iff [iff]:
    "z \<^bold>\<in> hrestrict r A \<longleftrightarrow> z \<^bold>\<in> r & (\<exists> x y. z = \<langle>x, y\<rangle> & x \<^bold>\<in> A)"
  by (auto simp: hrestrict_def)

lemma hrelation_0 [simp]: "hrelation 0"
  by (force simp add: hrelation_def)

lemma hrelation_restr [iff]: "hrelation (hrestrict r x)"
  by (metis hrelation_def hrestrict_iff is_hpair_def)

lemma hrelation_hunion [simp]: "hrelation (f \<squnion> g) \<longleftrightarrow> hrelation f \<and> hrelation g"
  by (auto simp: hrelation_def)

lemma hfunction_restr: "hfunction r \<Longrightarrow> hfunction (hrestrict r x)"
  by (auto simp: hfunction_def hrestrict_def)

lemma hdomain_restr [simp]: "hdomain (hrestrict r x) = hdomain r \<sqinter> x"
  by (force simp add: hdomain_def hrestrict_def)

lemma hdomain_0 [simp]: "hdomain 0 = 0"
  by (force simp add: hdomain_def)

lemma hdomain_ins [simp]: "hdomain (r \<triangleleft> \<langle>x, y\<rangle>) = hdomain r \<triangleleft> x"
  by (force simp add: hdomain_def)

lemma hdomain_hunion [simp]: "hdomain (f \<squnion> g) = hdomain f \<squnion> hdomain g"
  by (simp add: hdomain_def)

lemma hdomain_not_mem [iff]: "\<not> \<langle>hdomain r, a\<rangle> \<^bold>\<in> r"
  by (metis hdomain_ins hinter_hinsert_right hmem_hinsert hmem_not_refl
            hunion_hinsert_right sup_inf_absorb)

lemma app_singleton [simp]: "app \<lbrace>\<langle>x, y\<rangle>\<rbrace> x = y"
  by (simp add: app_def)

lemma app_equality: "hfunction f \<Longrightarrow> \<langle>x, y\<rangle> <: f \<Longrightarrow> app f x = y"
  by (auto simp: app_def hfunction_def intro: the1I2)

lemma app_ins2: "x' \<noteq> x \<Longrightarrow> app (f \<triangleleft> \<langle>x, y\<rangle>) x' = app f x'"
  by (simp add: app_def)

lemma hfunction_0 [simp]: "hfunction 0"
  by (force simp add: hfunction_def)

lemma hfunction_ins: "hfunction f \<Longrightarrow> ~ x <: hdomain f \<Longrightarrow> hfunction (f\<triangleleft> \<langle>x, y\<rangle>)"
  by (auto simp: hfunction_def hdomain_def)

lemma hdomainI: "\<langle>x, y\<rangle> \<^bold>\<in> f \<Longrightarrow> x \<^bold>\<in> hdomain f"
  by (auto simp: hdomain_def)

lemma hfunction_hunion: "hdomain f \<sqinter> hdomain g = 0
            \<Longrightarrow> hfunction (f \<squnion> g) \<longleftrightarrow> hfunction f \<and> hfunction g"
  by (auto simp: hfunction_def) (metis hdomainI hinter_iff hmem_hempty)+

lemma app_hrestrict [simp]: "x \<^bold>\<in> A \<Longrightarrow> app (hrestrict f A) x = app f x"
  by (simp add: hrestrict_def app_def)

section{*Operations on families of sets*}

definition HLambda :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "HLambda A b = RepFun A (\<lambda>x. \<langle>x, b x\<rangle>)"

definition HSigma :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "HSigma A B = (\<Squnion>x\<^bold>\<in>A. \<Squnion>y\<^bold>\<in>B(x). \<lbrace>\<langle>x,y\<rangle>\<rbrace>)"

definition HPi :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "HPi A B = \<lbrace> f \<^bold>\<in> HPow(HSigma A B). A \<le> hdomain(f) & hfunction(f)\<rbrace>"


syntax
  "_PROD"     :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3PROD _<:_./ _)" 10)
  "_SUM"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3SUM _<:_./ _)" 10)
  "_lam"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3lam _<:_./ _)" 10)

syntax (xsymbols)
  "_PROD"     :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<Pi>_\<^bold>\<in>_./ _)" 10)
  "_SUM"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<Sigma>_\<^bold>\<in>_./ _)" 10)
  "_lam"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<lambda>_\<^bold>\<in>_./ _)" 10)

syntax (HTML output)
  "_PROD"     :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<Pi>_\<^bold>\<in>_./ _)" 10)
  "_SUM"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<Sigma>_\<^bold>\<in>_./ _)" 10)
  "_lam"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<lambda>_\<^bold>\<in>_./ _)" 10)

translations
  "PROD x<:A. B" == "CONST HPi A (%x. B)"
  "SUM x<:A. B"  == "CONST HSigma A (%x. B)"
  "lam x<:A. f"  == "CONST HLambda A (%x. f)"

subsection{*Rules for Unions and Intersections of families*}

lemma HUN_iff [simp]: "b \<^bold>\<in> (\<Squnion>x\<^bold>\<in>A. B(x)) \<longleftrightarrow> (\<exists>x\<^bold>\<in>A. b \<^bold>\<in> B(x))"
  by auto

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma HUN_I: "\<lbrakk> a \<^bold>\<in> A;  b \<^bold>\<in> B(a) \<rbrakk>  \<Longrightarrow> b \<^bold>\<in> (\<Squnion>x\<^bold>\<in>A. B(x))"
  by auto

lemma HUN_E [elim!]: assumes "b \<^bold>\<in> (\<Squnion>x\<^bold>\<in>A. B(x))" obtains x where "x \<^bold>\<in> A"  "b \<^bold>\<in> B(x)"
  using assms  by blast

lemma HINT_iff: "b \<^bold>\<in> (\<Sqinter>x\<^bold>\<in>A. B(x)) \<longleftrightarrow> (\<forall>x\<^bold>\<in>A. b \<^bold>\<in> B(x)) & A\<noteq>0"
  by (simp add: HInter_def HBall_def) (metis foundation hmem_hempty)

lemma HINT_I: "\<lbrakk> !!x. x \<^bold>\<in> A \<Longrightarrow> b \<^bold>\<in> B(x);  A\<noteq>0 \<rbrakk> \<Longrightarrow> b \<^bold>\<in> (\<Sqinter>x\<^bold>\<in>A. B(x))"
  by (simp add: HINT_iff)

lemma HINT_E: "\<lbrakk> b \<^bold>\<in> (\<Sqinter>x\<^bold>\<in>A. B(x));  a \<^bold>\<in> A \<rbrakk> \<Longrightarrow> b \<^bold>\<in> B(a)"
  by (auto simp: HINT_iff)


subsection{*Generalized Cartesian product*}

lemma HSigma_iff [simp]: "\<langle>a,b\<rangle> \<^bold>\<in> HSigma A B \<longleftrightarrow> a \<^bold>\<in> A & b \<^bold>\<in> B(a)"
  by (force simp add: HSigma_def)

lemma HSigmaI [intro!]: "\<lbrakk> a \<^bold>\<in> A;  b \<^bold>\<in> B(a) \<rbrakk>  \<Longrightarrow> \<langle>a,b\<rangle> \<^bold>\<in> HSigma A B"
  by simp

lemmas HSigmaD1 = HSigma_iff [THEN iffD1, THEN conjunct1]
lemmas HSigmaD2 = HSigma_iff [THEN iffD1, THEN conjunct2]

text{*The general elimination rule*}
lemma HSigmaE [elim!]:
  assumes "c \<^bold>\<in> HSigma A B"
  obtains x y where "x \<^bold>\<in> A" "y \<^bold>\<in> B(x)" "c=\<langle>x,y\<rangle>"
  using assms  by (force simp add: HSigma_def)

lemma HSigmaE2 [elim!]:
  assumes "\<langle>a,b\<rangle> \<^bold>\<in> HSigma A B" obtains "a \<^bold>\<in> A" and "b \<^bold>\<in> B(a)"
  using assms  by auto

lemma HSigma_empty1 [simp]: "HSigma 0 B = 0"
  by blast

instantiation hf :: times
begin
definition times_hf where
  "times A B = HSigma A (\<lambda>x. B)"
instance proof qed
end

lemma times_iff [simp]: "\<langle>a,b\<rangle> \<^bold>\<in> A * B \<longleftrightarrow> a \<^bold>\<in> A & b \<^bold>\<in> B"
  by (simp add: times_hf_def)

lemma timesI [intro!]: "\<lbrakk> a \<^bold>\<in> A;  b \<^bold>\<in> B \<rbrakk>  \<Longrightarrow> \<langle>a,b\<rangle> \<^bold>\<in> A * B"
  by simp

lemmas timesD1 = times_iff [THEN iffD1, THEN conjunct1]
lemmas timesD2 = times_iff [THEN iffD1, THEN conjunct2]

text{*The general elimination rule*}
lemma timesE [elim!]:
  assumes c: "c \<^bold>\<in> A * B"
  obtains x y where "x \<^bold>\<in> A" "y \<^bold>\<in> B" "c=\<langle>x,y\<rangle>" using c
  by (auto simp: times_hf_def)

text{*...and a specific one*}
lemma timesE2 [elim!]:
  assumes "\<langle>a,b\<rangle> \<^bold>\<in> A * B" obtains "a \<^bold>\<in> A" and "b \<^bold>\<in> B"
using assms
  by auto

lemma times_empty1 [simp]: "0 * B = (0::hf)"
  by auto

lemma times_empty2 [simp]: "A*0 = (0::hf)"
  by blast

lemma times_empty_iff: "A*B=0 \<longleftrightarrow> A=0 | B=(0::hf)"
  by (auto simp: times_hf_def hf_ext)

instantiation hf :: mult_zero
begin
instance proof qed auto
end

section {*Disjoint Sum*}

instantiation hf :: zero_neq_one
begin

definition
  One_hf_def: "1 = \<lbrace>0\<rbrace>"
instance proof
  qed (auto simp: One_hf_def)
end

instantiation hf :: plus
begin
definition plus_hf where
  "plus A B = (\<lbrace>0\<rbrace> * A) \<squnion> (\<lbrace>1\<rbrace> * B)"
instance proof qed
end

definition Inl :: "hf=>hf" where
     "Inl(a) \<equiv> \<langle>0,a\<rangle>"

definition Inr :: "hf=>hf" where
     "Inr(b) \<equiv> \<langle>1,b\<rangle>"

lemmas sum_defs = plus_hf_def Inl_def Inr_def

lemma Inl_nonzero [simp]:"Inl x \<noteq> 0"
  by (metis Inl_def hpair_nonzero)

lemma Inr_nonzero [simp]:"Inr x \<noteq> 0"
  by (metis Inr_def hpair_nonzero)

text{* Introduction rules for the injections (as equivalences) *}

lemma Inl_in_sum_iff [iff]: "Inl(a) \<^bold>\<in> A+B \<longleftrightarrow> a \<^bold>\<in> A"
  by (auto simp: sum_defs)

lemma Inr_in_sum_iff [iff]: "Inr(b) \<^bold>\<in> A+B \<longleftrightarrow> b \<^bold>\<in> B"
  by (auto simp: sum_defs)

text{*Elimination rule*}

lemma sumE [elim!]:
  assumes u: "u \<^bold>\<in> A+B"
  obtains x where "x \<^bold>\<in> A" "u=Inl(x)" | y where "y \<^bold>\<in> B" "u=Inr(y)" using u
  by (auto simp: sum_defs)

text{* Injection and freeness equivalences, for rewriting *}

lemma Inl_iff [iff]: "Inl(a)=Inl(b) \<longleftrightarrow> a=b"
  by (simp add: sum_defs)

lemma Inr_iff [iff]: "Inr(a)=Inr(b) \<longleftrightarrow> a=b"
  by (simp add: sum_defs)

lemma Inl_Inr_iff [iff]: "Inl(a)=Inr(b) \<longleftrightarrow> False"
  by (simp add: sum_defs)

lemma Inr_Inl_iff [iff]: "Inr(b)=Inl(a) \<longleftrightarrow> False"
  by (simp add: sum_defs)

lemma sum_empty [simp]: "0+0 = (0::hf)"
  by (auto simp: sum_defs)

lemma sum_iff: "u \<^bold>\<in> A+B \<longleftrightarrow> (\<exists>x. x \<^bold>\<in> A & u=Inl(x)) | (\<exists>y. y \<^bold>\<in> B & u=Inr(y))"
  by blast

lemma sum_subset_iff:
  fixes A :: hf shows "A+B \<le> C+D \<longleftrightarrow> A\<le>C & B\<le>D"
  by blast

lemma sum_equal_iff:
  fixes A :: hf shows "A+B = C+D \<longleftrightarrow> A=C & B=D"
  by (auto simp: hf_ext sum_subset_iff)


section{*Ordinals*}

subsection{*Basic Definitions*}

text{*Definition 2.1. We say that x is transitive if every element of x is a subset of x.*}
definition
  Transset  :: "hf \<Rightarrow> bool"  where
    "Transset(x) \<equiv> \<forall>y. y \<^bold>\<in> x \<longrightarrow> y \<le> x"

lemma Transset_sup: "Transset x \<Longrightarrow> Transset y \<Longrightarrow> Transset (x \<squnion> y)"
  by (auto simp: Transset_def)

lemma Transset_inf: "Transset x \<Longrightarrow> Transset y \<Longrightarrow> Transset (x \<sqinter> y)"
  by (auto simp: Transset_def)

lemma Transset_hinsert: "Transset x \<Longrightarrow> y \<le> x \<Longrightarrow> Transset (x \<triangleleft> y)"
  by (auto simp: Transset_def)


text{*In HF, the ordinals are simply the natural numbers. But the definitions are the same
      as for transfinite ordinals.*}
definition
  Ord  :: "hf \<Rightarrow> bool"  where
    "Ord(k)      \<equiv> Transset(k) & (\<forall>x \<^bold>\<in> k. Transset(x))"

subsection {*Definition 2.2 (Successor).*}
definition
  succ  :: "hf \<Rightarrow> hf"  where
    "succ(x)      \<equiv> hinsert x x"

lemma succ_iff [simp]: "x \<^bold>\<in> succ y \<longleftrightarrow> x=y \<or> x \<^bold>\<in> y"
  by (simp add: succ_def)

lemma succ_ne_self [simp]: "i \<noteq> succ i"
  by (metis hmem_ne succ_iff)

lemma succ_notin_self: "~ succ i <: i"
  by (metis hmem_ne succ_iff)

lemma succE [elim?]: assumes "x \<^bold>\<in> succ y" obtains "x=y" | "x \<^bold>\<in> y"
  by (metis assms succ_iff)

lemma hmem_succ_ne: "succ x <: y \<Longrightarrow> x \<noteq> y"
  by (metis hmem_not_refl succ_iff)

lemma hball_succ [simp]: "(\<forall>x \<^bold>\<in> succ k. P x) \<longleftrightarrow> P k & (\<forall>x \<^bold>\<in> k. P x)"
  by (auto simp: HBall_def)

lemma hbex_succ [simp]: "(\<exists>x \<^bold>\<in> succ k. P x) \<longleftrightarrow> P k | (\<exists>x \<^bold>\<in> k. P x)"
  by (auto simp: HBex_def)

lemma One_hf_eq_succ: "1 = succ 0"
  by (metis One_hf_def succ_def)

lemma zero_hmem_one [iff]: "x \<^bold>\<in> 1 \<longleftrightarrow> x = 0"
  by (metis One_hf_eq_succ hmem_hempty succ_iff)

lemma hball_One [simp]: "(\<forall>x\<^bold>\<in>1. P x) = P 0"
  by (simp add: One_hf_eq_succ)

lemma hbex_One [simp]: "(\<exists>x\<^bold>\<in>1. P x) = P 0"
  by (simp add: One_hf_eq_succ)

lemma hpair_neq_succ [simp]: "\<langle>x,y\<rangle> \<noteq> succ k"
  by (auto simp: succ_def hpair_def) (metis hemptyE hmem_hinsert hmem_ne)

lemma succ_neq_hpair [simp]: "succ k \<noteq> \<langle>x,y\<rangle> "
  by (metis hpair_neq_succ)

lemma hpair_neq_one [simp]: "\<langle>x,y\<rangle> \<noteq> 1"
  by (metis One_hf_eq_succ hpair_neq_succ)

lemma one_neq_hpair [simp]: "1 \<noteq> \<langle>x,y\<rangle>"
  by (metis hpair_neq_one)

lemma hmem_succ_self [simp]: "k \<^bold>\<in> succ k"
  by (metis succ_iff)

lemma hmem_succ: "l \<^bold>\<in> k \<Longrightarrow> l \<^bold>\<in> succ k"
  by (metis succ_iff)

text{*Theorem 2.3.*}
lemma Ord_0 [iff]: "Ord 0"
  by (simp add: Ord_def Transset_def)

lemma Ord_succ: "Ord(k) \<Longrightarrow> Ord(succ(k))"
  by (simp add: Ord_def Transset_def succ_def less_eq_insert2_iff HBall_def)

lemma Ord_1 [iff]: "Ord 1"
  by (metis One_hf_def Ord_0 Ord_succ succ_def)

lemma OrdmemD: "Ord(k) \<Longrightarrow> j \<^bold>\<in> k \<Longrightarrow> j \<le> k"
  by (simp add: Ord_def Transset_def HBall_def)

lemma Ord_trans: "\<lbrakk> i\<^bold>\<in>j;  j\<^bold>\<in>k;  Ord(k) \<rbrakk>  \<Longrightarrow> i\<^bold>\<in>k"
  by (blast dest: OrdmemD)

lemma hmem_0_Ord:
  assumes k: "Ord(k)" and knz: "k \<noteq> 0" shows "0 \<^bold>\<in> k"
  by (metis foundation [OF knz] Ord_trans hempty_iff hinter_iff k)

lemma Ord_in_Ord: "\<lbrakk> Ord(k);  m \<^bold>\<in> k \<rbrakk>  \<Longrightarrow> Ord(m)"
  by (auto simp: Ord_def Transset_def)

subsection{*Induction, Linearity, etc.*}

lemma Ord_induct [consumes 1, case_names step]:
  assumes k: "Ord(k)"
      and step: "!!x.\<lbrakk> Ord(x);  \<And>y. y \<^bold>\<in> x \<Longrightarrow> P(y) \<rbrakk>  \<Longrightarrow> P(x)"
  shows "P(k)"
proof -
  have "\<forall>m \<^bold>\<in> k. Ord(m) \<longrightarrow> P(m)"
    proof (induct k rule: hf_induct)
      case 0 thus ?case  by simp
    next
      case (hinsert a b)
      thus ?case
        by (auto intro: Ord_in_Ord step)
    qed
  thus ?thesis using k
    by (auto intro: Ord_in_Ord step)
qed

text{*Theorem 2.4 (Comparability of ordinals).*}
lemma Ord_linear: "Ord(k) \<Longrightarrow> Ord(l) \<Longrightarrow> k\<^bold>\<in>l | k=l | l\<^bold>\<in>k"
proof (induct k arbitrary: l rule: Ord_induct)
  case (step k)
  note step_k = step
  show ?case using `Ord(l)`
    proof (induct l rule: Ord_induct)
      case (step l)
      thus ?case using step_k
        by (metis Ord_trans hf_equalityI)
    qed
qed

text{*The trichotomy law for ordinals*}
lemma Ord_linear_lt:
  assumes o: "Ord(k)" "Ord(l)"
  obtains (lt) "k\<^bold>\<in>l" | (eq) "k=l" | (gt) "l\<^bold>\<in>k"
by (metis Ord_linear o)

lemma Ord_linear2:
  assumes o: "Ord(k)" "Ord(l)"
  obtains (lt) "k\<^bold>\<in>l" | (ge) "l \<le> k"
by (metis Ord_linear OrdmemD order_eq_refl o)

lemma Ord_linear_le:
  assumes o: "Ord(k)" "Ord(l)"
  obtains (le) "k \<le> l" | (ge) "l \<le> k"
by (metis Ord_linear2 OrdmemD o)

lemma hunion_less_iff [simp]: "\<lbrakk>Ord i; Ord j\<rbrakk> \<Longrightarrow> i \<squnion> j < k \<longleftrightarrow> i<k \<and> j<k"
  by (metis Ord_linear_le le_iff_sup sup.order_iff sup.strict_boundedE)

text{*Theorem 2.5*}
lemma Ord_mem_iff_lt: "Ord(k) \<Longrightarrow> Ord(l) \<Longrightarrow> k\<^bold>\<in>l \<longleftrightarrow> k < l"
  by (metis Ord_linear OrdmemD hmem_not_refl less_hf_def less_le_not_le)

lemma le_succE: "succ i \<le> succ j \<Longrightarrow> i \<le> j"
  by (simp add: less_eq_hf_def) (metis hmem_not_sym)

lemma le_succ_iff: "Ord i \<Longrightarrow> Ord j \<Longrightarrow> succ i \<le> succ j \<longleftrightarrow> i \<le> j"
  by (metis Ord_linear_le Ord_succ le_succE order_antisym)

lemma succ_inject_iff [iff]: "succ i = succ j \<longleftrightarrow> i = j"
  by (metis succ_def hmem_hinsert hmem_not_sym)

lemma mem_succ_iff [simp]: "Ord j \<Longrightarrow> succ i \<^bold>\<in> succ j \<longleftrightarrow> i \<^bold>\<in> j"
  by (metis Ord_in_Ord Ord_mem_iff_lt Ord_succ succ_def less_eq_insert1_iff less_hf_def succ_iff)

lemma Ord_mem_succ_cases:
  assumes "Ord(k)" "l \<^bold>\<in> k"
  shows "succ l = k \<or> succ l \<^bold>\<in> k"
  by (metis assms mem_succ_iff succ_iff)

subsection{*Supremum and Infimum*}

lemma Ord_Union [intro,simp]: "\<lbrakk> !!i. i\<^bold>\<in>A \<Longrightarrow> Ord(i) \<rbrakk>  \<Longrightarrow> Ord(\<Squnion> A)"
  by (auto simp: Ord_def Transset_def) blast

lemma Ord_Inter [intro,simp]: "\<lbrakk> !!i. i\<^bold>\<in>A \<Longrightarrow> Ord(i) \<rbrakk>  \<Longrightarrow> Ord(\<Sqinter> A)"
  apply (case_tac "A=0", auto simp: Ord_def Transset_def)
  apply (force simp add: hf_ext)+
  done

text{*Theorem 2.7. Every set x of ordinals is ordered by the binary relation <.
      Moreover if x = 0 then x has a smallest and a largest element.*}

lemma hmem_Sup_Ords: "\<lbrakk>A\<noteq>0; !!i. i\<^bold>\<in>A \<Longrightarrow> Ord(i)\<rbrakk> \<Longrightarrow> \<Squnion>A \<^bold>\<in> A"
proof (induction A rule: hf_induct)
  case 0 thus ?case  by simp
next
  case (hinsert x A)
  show ?case
    proof (cases A rule: hf_cases)
      case 0 thus ?thesis by simp
    next
      case (hinsert y A')
      hence UA: "\<Squnion>A \<^bold>\<in> A"
        by (metis hinsert.IH(2) hinsert.prems(2) hinsert_nonempty hmem_hinsert)
      hence "\<Squnion>A \<le> x | x \<le> \<Squnion>A"
        by (metis Ord_linear2 OrdmemD hinsert.prems(2) hmem_hinsert)
      thus ?thesis
        by (metis HUnion_hinsert UA le_iff_sup less_eq_insert1_iff order_refl sup.commute)
    qed
qed

lemma hmem_Inf_Ords: "\<lbrakk>A\<noteq>0; !!i. i\<^bold>\<in>A \<Longrightarrow> Ord(i)\<rbrakk> \<Longrightarrow> \<Sqinter>A \<^bold>\<in> A"
proof (induction A rule: hf_induct)
  case 0 thus ?case  by simp
next
  case (hinsert x A)
  show ?case
    proof (cases A rule: hf_cases)
      case 0 thus ?thesis by auto
    next
      case (hinsert y A')
      hence IA: "\<Sqinter>A \<^bold>\<in> A"
        by (metis hinsert.IH(2) hinsert.prems(2) hinsert_nonempty hmem_hinsert)
      hence "\<Sqinter>A \<le> x | x \<le> \<Sqinter>A"
        by (metis Ord_linear2 OrdmemD hinsert.prems(2) hmem_hinsert)
      thus ?thesis
        by (metis HInter_hinsert IA hmem_hempty hmem_hinsert inf_absorb2 le_iff_inf)
    qed
qed

lemma Ord_pred: "\<lbrakk>Ord(k); k \<noteq> 0\<rbrakk> \<Longrightarrow> succ(\<Squnion>k) = k"
by (metis (full_types) HUnion_iff Ord_in_Ord Ord_mem_succ_cases hmem_Sup_Ords hmem_ne succ_iff)

lemma Ord_cases [cases type: hf, case_names 0 succ]:
  assumes Ok: "Ord(k)"
  obtains "k = 0" | l where "Ord l" "succ l = k"
by (metis Ok Ord_in_Ord Ord_pred succ_iff)

lemma Ord_induct2 [consumes 1, case_names 0 succ, induct type: hf]:
  assumes k: "Ord(k)"
      and P: "P 0" "\<And>k. Ord k \<Longrightarrow> P k \<Longrightarrow> P (succ k)"
  shows "P k"
using k
proof (induction k rule: Ord_induct)
  case (step k) thus ?case
    by (metis Ord_cases P hmem_succ_self)
qed

lemma Ord_succ_iff [iff]: "Ord (succ k) = Ord k"
  by (metis Ord_in_Ord Ord_succ less_eq_insert1_iff order_refl succ_def)

lemma [simp]: "succ k \<noteq> 0"
  by (metis hinsert_nonempty succ_def)

lemma Ord_Sup_succ_eq [simp]: "Ord k \<Longrightarrow> \<Squnion>(succ k) = k"
  by (metis Ord_pred Ord_succ_iff succ_inject_iff hinsert_nonempty succ_def)

lemma Ord_lt_succ_iff_le: "Ord k \<Longrightarrow> Ord l \<Longrightarrow> k < succ l \<longleftrightarrow> k \<le> l"
  by (metis Ord_mem_iff_lt Ord_succ_iff less_le_not_le order_eq_iff succ_iff)

lemma zero_in_Ord: "Ord k \<Longrightarrow> k=0 \<or> 0 \<^bold>\<in> k"
  by (induct k) auto

lemma hpair_neq_Ord: "Ord k \<Longrightarrow> \<langle>x,y\<rangle> \<noteq> k"
  by (cases k) auto

lemma hpair_neq_Ord': assumes k: "Ord k" shows "k \<noteq> \<langle>x,y\<rangle>"
  by (metis k hpair_neq_Ord)

lemma Not_Ord_hpair [iff]: "~ Ord \<langle>x,y\<rangle>"
  by (metis hpair_neq_Ord)

lemma is_hpair [simp]: "is_hpair \<langle>x,y\<rangle>"
  by (force simp add: is_hpair_def)

lemma Ord_not_hpair: "Ord x \<Longrightarrow> \<not> is_hpair x"
  by (metis Not_Ord_hpair is_hpair_def)

lemma zero_in_succ [simp,intro]: "Ord i \<Longrightarrow> 0 \<^bold>\<in> succ i"
  by (metis succ_iff zero_in_Ord)

subsection{*Converting Between Ordinals and Natural Numbers*}

fun ord_of :: "nat \<Rightarrow> hf"
  where
   "ord_of 0 = 0"
 | "ord_of (Suc k) = succ (ord_of k)"

lemma Ord_ord_of [simp]: "Ord (ord_of k)"
  by (induct k, auto)

lemma ord_of_inject [iff]: "ord_of i = ord_of j \<longleftrightarrow> i=j"
proof (induct i arbitrary: j)
  case 0 show ?case
    by (metis Zero_neq_Suc hempty_iff hmem_succ_self ord_of.elims)
next
  case (Suc i) show ?case
    by (cases j) (auto simp: Suc)
qed

lemma ord_of_minus_1: "n > 0 \<Longrightarrow> ord_of n = succ (ord_of (n - 1))"
  by (metis Suc_diff_1 ord_of.simps(2))

definition nat_of_ord :: "hf \<Rightarrow> nat"
  where "nat_of_ord x = (THE n. x = ord_of n)"

lemma nat_of_ord_ord_of [simp]: "nat_of_ord (ord_of n) = n"
  by (auto simp: nat_of_ord_def)

lemma nat_of_ord_0 [simp]: "nat_of_ord 0 = 0"
  by (metis (mono_tags) nat_of_ord_ord_of ord_of.simps(1))

lemma ord_of_nat_of_ord [simp]: "Ord x \<Longrightarrow> ord_of (nat_of_ord x) = x"
  apply (erule Ord_induct2, simp)
  apply (metis nat_of_ord_ord_of ord_of.simps(2))
  done

lemma nat_of_ord_inject: "Ord x \<Longrightarrow> Ord y \<Longrightarrow> nat_of_ord x = nat_of_ord y \<longleftrightarrow> x = y"
  by (metis ord_of_nat_of_ord)

lemma nat_of_ord_succ [simp]: "Ord x \<Longrightarrow> nat_of_ord (succ x) = Suc (nat_of_ord x)"
  by (metis nat_of_ord_ord_of ord_of.simps(2) ord_of_nat_of_ord)


section{*Sequences and Ordinal Recursion*}

text{*Definition 3.2 (Sequence).*}

definition Seq :: "hf \<Rightarrow> hf \<Rightarrow> bool"
  where "Seq s k \<longleftrightarrow> hrelation s & hfunction s & k \<le> hdomain s"

lemma Seq_0 [iff]: "Seq 0 0"
  by (auto simp: Seq_def hrelation_def hfunction_def)

lemma Seq_succ_D: "Seq s (succ k) \<Longrightarrow> Seq s k"
  by (simp add: Seq_def succ_def)

lemma Seq_Ord_D: "Seq s k \<Longrightarrow> l \<^bold>\<in> k \<Longrightarrow> Ord k \<Longrightarrow> Seq s l"
  by (auto simp: Seq_def intro: Ord_trans)

lemma Seq_restr: "Seq s (succ k) \<Longrightarrow> Seq (hrestrict s k) k"
  by (simp add: Seq_def hfunction_restr succ_def)

lemma Seq_Ord_restr: "\<lbrakk>Seq s k; l \<^bold>\<in> k; Ord k\<rbrakk> \<Longrightarrow> Seq (hrestrict s l) l"
  by (auto simp: Seq_def hfunction_restr intro: Ord_trans)

lemma Seq_ins: "\<lbrakk>Seq s k; ~ k <: hdomain s\<rbrakk> \<Longrightarrow> Seq (s \<triangleleft> \<langle>k, y\<rangle>) (succ k)"
  by (auto simp: Seq_def hrelation_def succ_def hfunction_def hdomainI)

definition insf :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf"
  where "insf s k y \<equiv> nonrestrict s \<lbrace>k\<rbrace> \<triangleleft> \<langle>k, y\<rangle>"

lemma hfunction_insf: "hfunction s \<Longrightarrow> hfunction (insf s k y)"
  by (auto simp: insf_def hfunction_def nonrestrict_def hmem_not_refl)

lemma Seq_insf: "Seq s k \<Longrightarrow> Seq (insf s k y) (succ k)"
  apply (auto simp: Seq_def hrelation_def insf_def hfunction_def nonrestrict_def)
  apply (force simp add: hdomain_def)
  done

lemma Seq_succ_iff: "Seq s (succ k) \<longleftrightarrow> Seq s k \<and> (\<exists>y. \<langle>k, y\<rangle> <: s)"
  apply (auto simp: Seq_def hdomain_def)
  apply (metis hfst_conv, blast)
  done

lemma nonrestrictD: "a \<^bold>\<in> nonrestrict s X \<Longrightarrow> a \<^bold>\<in> s"
  by (auto simp: nonrestrict_def)

lemma hpair_in_nonrestrict_iff [simp]: "\<langle>a,b\<rangle> \<^bold>\<in> nonrestrict s X \<longleftrightarrow> \<langle>a,b\<rangle> \<^bold>\<in> s \<and> \<not> a \<^bold>\<in> X"
  by (auto simp: nonrestrict_def)

lemma app_nonrestrict_Seq: "Seq s k \<Longrightarrow> ~ z <: X \<Longrightarrow> app (nonrestrict s X) z = app s z"
  by (auto simp: Seq_def nonrestrict_def app_def)

lemma app_insf_Seq: "Seq s k \<Longrightarrow> app (insf s k y) k = y"
  by (metis Seq_def hfunction_insf app_equality hmem_hinsert insf_def)

lemma app_insf2_Seq: "Seq s k \<Longrightarrow> k' \<noteq> k \<Longrightarrow> app (insf s k y) k' = app s k'"
  by (simp add: app_nonrestrict_Seq insf_def app_ins2)

lemma app_insf_Seq_if: "Seq s k \<Longrightarrow> app (insf s k y) k' = (if k' = k then y else app s k')"
  by (metis app_insf2_Seq app_insf_Seq)

lemma Seq_imp_eq_app: "\<lbrakk>Seq s d; \<langle>x,y\<rangle> \<^bold>\<in> s\<rbrakk> \<Longrightarrow> app s x = y"
  by (metis Seq_def app_equality)

lemma Seq_iff_app: "\<lbrakk>Seq s d; x \<^bold>\<in> d\<rbrakk> \<Longrightarrow> \<langle>x,y\<rangle> \<^bold>\<in> s \<longleftrightarrow> app s x = y"
  by (auto simp: Seq_def hdomain_def app_equality)

lemma Exists_iff_app: "Seq s d \<Longrightarrow> x \<^bold>\<in> d \<Longrightarrow> (\<exists>y. \<langle>x, y\<rangle> \<^bold>\<in> s & P y) = P (app s x)"
  by (metis Seq_iff_app)

lemma Ord_trans2: "\<lbrakk>i2 \<^bold>\<in> i; i \<^bold>\<in> j;  j \<^bold>\<in> k;  Ord k\<rbrakk> \<Longrightarrow> i2\<^bold>\<in>k"
  by (metis Ord_trans)

definition ord_rec_Seq :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where
   "ord_rec_Seq T G s k y \<longleftrightarrow>
        (Seq s k & y = G (app s (\<Squnion>k)) & app s 0 = T &
                   (\<forall>n. succ n \<^bold>\<in> k \<longrightarrow> app s (succ n) = G (app s n)))"

lemma Seq_succ_insf:
  assumes s: "Seq s (succ k)"  shows "\<exists> y. s = insf s k y"
proof -
  obtain y where y: "\<langle>k, y\<rangle> <: s" by (metis Seq_succ_iff s)
  hence yuniq: "\<forall> y'. \<langle>k, y'\<rangle> <: s \<longrightarrow> y' = y" using s
    by (simp add: Seq_def hfunction_def)
  { fix z
    assume z: "z <: s"
    then obtain u v where uv: "z = \<langle>u, v\<rangle>" using s
      by (metis Seq_def hrelation_def is_hpair_def)
    hence "z <: insf s k y"
      by (metis hemptyE hmem_hinsert hpair_in_nonrestrict_iff insf_def yuniq z)
  }
  note left2right = this
  show ?thesis
    proof
      show "s = insf s k y"
        by (rule hf_equalityI) (metis hmem_hinsert insf_def left2right nonrestrictD y)
    qed
qed

lemma ord_rec_Seq_succ_iff:
  assumes k: "Ord k" and knz: "k \<noteq> 0"
  shows "ord_rec_Seq T G s (succ k) z \<longleftrightarrow> (\<exists> s' y. ord_rec_Seq T G s' k y & z = G y & s = insf s' k y)"
proof
  assume os: "ord_rec_Seq T G s (succ k) z"
  show "\<exists>s' y. ord_rec_Seq T G s' k y \<and> z = G y \<and> s = insf s' k y"
    apply (rule_tac x=s in exI)  using os k knz
    apply (auto simp: Seq_insf ord_rec_Seq_def app_insf_Seq app_insf2_Seq
                          hmem_succ_ne hmem_ne hmem_Sup_ne Seq_succ_iff hmem_0_Ord)
    apply (metis Ord_pred)
    apply (metis Ord_pred Seq_succ_iff Seq_succ_insf app_insf_Seq)
    done
next
  assume ok: "\<exists>s' y. ord_rec_Seq T G s' k y \<and> z = G y \<and> s = insf s' k y"
  thus "ord_rec_Seq T G s (succ k) z" using ok k knz
    by (auto simp: ord_rec_Seq_def app_insf_Seq_if hmem_ne hmem_succ_ne Seq_insf)
qed

lemma ord_rec_Seq_functional:
   "Ord k \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> ord_rec_Seq T G s k y \<Longrightarrow> ord_rec_Seq T G s' k y' \<Longrightarrow> y' = y"
proof (induct k arbitrary: y y' s s' rule: Ord_induct2)
  case 0 thus ?case
    by (simp add: ord_rec_Seq_def)
next
  case (succ k) show ?case
    proof (cases "k=0")
      case True thus ?thesis using succ
        by (auto simp: ord_rec_Seq_def)
    next
      case False
      thus ?thesis using succ
        by (auto simp: ord_rec_Seq_succ_iff)
    qed
qed

definition ord_recp :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where
   "ord_recp T G H x y =
    (if x=0 then y = T
     else
       if Ord(x) then \<exists> s. ord_rec_Seq T G s x y
       else y = H x)"

lemma ord_recp_functional: "ord_recp T G H x y \<Longrightarrow> ord_recp T G H x y' \<Longrightarrow> y' = y"
  by (auto simp: ord_recp_def ord_rec_Seq_functional split: split_if_asm)

lemma ord_recp_succ_iff:
  assumes k: "Ord k" shows "ord_recp T G H (succ k) z \<longleftrightarrow> (\<exists>y. z = G y & ord_recp T G H k y)"
proof (cases "k=0")
  case True thus ?thesis
    by (simp add: ord_recp_def ord_rec_Seq_def) (metis Seq_0 Seq_insf app_insf_Seq)
next
  case False
  thus ?thesis using k
    by (auto simp: ord_recp_def ord_rec_Seq_succ_iff)
qed

definition ord_rec :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf \<Rightarrow> hf"
  where
   "ord_rec T G H x = (THE y. ord_recp T G H x y)"

lemma ord_rec_0 [simp]: "ord_rec T G H 0 = T"
  by (simp add: ord_recp_def ord_rec_def)

lemma ord_recp_total: "\<exists>y. ord_recp T G H x y"
proof (cases "Ord x")
  case True thus ?thesis
  proof (induct x rule: Ord_induct2)
    case 0 thus ?case
      by (simp add: ord_recp_def)
  next
    case (succ x) thus ?case
      by (metis ord_recp_succ_iff)
  qed
next
  case False thus ?thesis
    by (auto simp: ord_recp_def)
qed

lemma ord_rec_succ [simp]:
  assumes k: "Ord k" shows "ord_rec T G H (succ k) = G (ord_rec T G H k)"
proof -
  from ord_recp_total [of T G H k]
  obtain y where "ord_recp T G H k y" by auto
  thus ?thesis using k
    apply (simp add: ord_rec_def ord_recp_succ_iff)
    apply (rule theI2)
    apply (auto dest: ord_recp_functional)
    done
qed

lemma ord_rec_non [simp]: "~ Ord x \<Longrightarrow> ord_rec T G H x = H x"
  by (metis Ord_0 ord_rec_def ord_recp_def the_equality)

end
