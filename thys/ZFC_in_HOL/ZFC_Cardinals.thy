section \<open>Cartesian products, Disjoint Sums, Ranks, Cardinals\<close>

theory ZFC_Cardinals
  imports ZFC_in_HOL

begin

declare [[coercion_enabled]]
declare [[coercion "ord_of_nat :: nat \<Rightarrow> V"]]

subsection \<open>Ordered Pairs\<close>

lemma singleton_eq_iff [iff]: "set {a} = set {b} \<longleftrightarrow> a=b"
  by simp

lemma doubleton_eq_iff: "set {a,b} = set {c,d} \<longleftrightarrow> (a=c \<and> b=d) \<or> (a=d \<and> b=c)"
  by (simp add: Set.doubleton_eq_iff)

definition vpair :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vpair a b = set {set {a},set {a,b}}"

definition vfst :: "V \<Rightarrow> V"
  where "vfst p \<equiv> THE x. \<exists>y. p = vpair x y"

definition vsnd :: "V \<Rightarrow> V"
  where "vsnd p \<equiv> THE y. \<exists>x. p = vpair x y"

definition vsplit :: "[[V, V] \<Rightarrow> 'a, V] \<Rightarrow> 'a::{}"  \<comment> \<open>for pattern-matching\<close>
  where "vsplit c \<equiv> \<lambda>p. c (vfst p) (vsnd p)"

nonterminal Vs
syntax (ASCII)
  "_Tuple"    :: "[V, Vs] \<Rightarrow> V"              (\<open><(_,/ _)>\<close>)
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   (\<open><_,/ _>\<close>)
syntax
  ""          :: "V \<Rightarrow> Vs"                    (\<open>_\<close>)
  "_Enum"     :: "[V, Vs] \<Rightarrow> Vs"             (\<open>_,/ _\<close>)
  "_Tuple"    :: "[V, Vs] \<Rightarrow> V"              (\<open>\<langle>(_,/ _)\<rangle>\<close>)
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   (\<open>\<langle>_,/ _\<rangle>\<close>)
syntax_consts
  "_Enum" "_Tuple" \<rightleftharpoons> vpair and
  "_hpattern" \<rightleftharpoons> vsplit
translations
  "<x, y, z>"    \<rightleftharpoons> "<x, <y, z>>"
  "<x, y>"       \<rightleftharpoons> "CONST vpair x y"
  "<x, y, z>"    \<rightleftharpoons> "<x, <y, z>>"
  "\<lambda><x,y,zs>. b" \<rightleftharpoons> "CONST vsplit(\<lambda>x <y,zs>. b)"
  "\<lambda><x,y>. b"    \<rightleftharpoons> "CONST vsplit(\<lambda>x y. b)"


lemma vpair_def': "vpair a b = set {set {a,a},set {a,b}}"
  by (simp add: vpair_def)

lemma vpair_iff [simp]: "vpair a b = vpair a' b' \<longleftrightarrow> a=a' \<and> b=b'"
  unfolding vpair_def' doubleton_eq_iff by auto

lemmas vpair_inject = vpair_iff [THEN iffD1, THEN conjE, elim!]

lemma vfst_conv [simp]: "vfst \<langle>a,b\<rangle> = a"
  by (simp add: vfst_def)

lemma vsnd_conv [simp]: "vsnd \<langle>a,b\<rangle> = b"
  by (simp add: vsnd_def)

lemma vsplit [simp]: "vsplit c \<langle>a,b\<rangle> = c a b"
  by (simp add: vsplit_def)

lemma vpair_neq_fst: "\<langle>a,b\<rangle> \<noteq> a"
  by (metis elts_of_set insertI1 mem_not_sym small_upair vpair_def')

lemma vpair_neq_snd: "\<langle>a,b\<rangle> \<noteq> b"
  by (metis elts_of_set insertI1 mem_not_sym small_upair subsetD subset_insertI vpair_def')

lemma vpair_nonzero [simp]: "\<langle>x,y\<rangle> \<noteq> 0"
  by (metis elts_0 elts_of_set empty_not_insert small_upair vpair_def)

lemma zero_notin_vpair: "0 \<notin> elts \<langle>x,y\<rangle>"
  by (auto simp: vpair_def)

lemma inj_on_vpair [simp]: "inj_on (\<lambda>(x, y). \<langle>x, y\<rangle>) A"
  by (auto simp: inj_on_def)


subsection \<open>Generalized Cartesian product\<close>

definition VSigma :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "VSigma A B \<equiv> set(\<Union>x \<in> elts A. \<Union>y \<in> elts (B x). {\<langle>x,y\<rangle>})"

abbreviation vtimes where "vtimes A B \<equiv> VSigma A (\<lambda>x. B)"

definition pairs :: "V \<Rightarrow> (V * V)set"
  where "pairs r \<equiv> {(x,y). \<langle>x,y\<rangle> \<in> elts r} "

lemma pairs_iff_elts: "(x,y) \<in> pairs z \<longleftrightarrow> \<langle>x,y\<rangle> \<in> elts z"
  by (simp add: pairs_def)

lemma VSigma_iff [simp]: "\<langle>a,b\<rangle> \<in> elts (VSigma A B) \<longleftrightarrow> a \<in> elts A \<and> b \<in> elts (B a)"
  by (auto simp: VSigma_def UNION_singleton_eq_range)

lemma VSigmaI [intro!]: "\<lbrakk> a \<in> elts A;  b \<in> elts (B a)\<rbrakk>  \<Longrightarrow> \<langle>a,b\<rangle> \<in> elts (VSigma A B)"
  by simp

lemmas VSigmaD1 = VSigma_iff [THEN iffD1, THEN conjunct1]
lemmas VSigmaD2 = VSigma_iff [THEN iffD1, THEN conjunct2]

text \<open>The general elimination rule\<close>
lemma VSigmaE [elim!]:
  assumes "c \<in> elts (VSigma A B)"
  obtains x y where "x \<in> elts A" "y \<in> elts (B x)" "c=\<langle>x,y\<rangle>"
  using assms by (auto simp: VSigma_def split: if_split_asm)

lemma VSigmaE2 [elim!]:
  assumes "\<langle>a,b\<rangle> \<in> elts (VSigma A B)" obtains "a \<in> elts A" and "b \<in> elts (B a)"
  using assms  by auto

lemma VSigma_empty1 [simp]: "VSigma 0 B = 0"
  by auto

lemma times_iff [simp]: "\<langle>a,b\<rangle> \<in> elts (vtimes A B) \<longleftrightarrow> a \<in> elts A \<and> b \<in> elts B"
  by simp

lemma timesI [intro!]: "\<lbrakk>a \<in> elts A;  b \<in> elts B\<rbrakk>  \<Longrightarrow> \<langle>a,b\<rangle> \<in> elts (vtimes A B)"
  by simp

lemma times_empty2 [simp]: "vtimes A 0 = 0"
  using elts_0 by blast

lemma times_empty_iff: "VSigma A B = 0 \<longleftrightarrow> A=0 \<or> (\<forall>x \<in> elts A. B x = 0)"
  by (metis VSigmaE VSigmaI elts_0 empty_iff trad_foundation)

lemma elts_VSigma: "elts (VSigma A B) = (\<lambda>(x,y). vpair x y) ` Sigma (elts A) (\<lambda>x. elts (B x))"
  by auto
    
lemma small_Sigma [simp]:
  assumes A: "small A" and B: "\<And>x. x \<in> A \<Longrightarrow> small (B x)"
  shows "small (Sigma A B)"
proof -
  obtain a where "elts a \<approx> A" 
    by (meson assms small_eqpoll)
  then obtain f where f: "bij_betw f (elts a) A"
    using eqpoll_def by blast
  have "\<exists>y. elts y \<approx> B x" if "x \<in> A" for x
    using B small_eqpoll that by blast
  then obtain g where g: "\<And>x. x \<in> A \<Longrightarrow> elts (g x) \<approx> B x"
    by metis 
  with f have "elts (VSigma a (g \<circ> f)) \<approx> Sigma A B"
    by (simp add: elts_VSigma Sigma_eqpoll_cong bij_betwE)
  then show ?thesis
    using small_eqpoll by blast
qed

lemma small_Times [simp]:
  assumes "small A" "small B"  shows "small (A \<times> B)"
  by (simp add: assms)

lemma small_Times_iff: "small (A \<times> B) \<longleftrightarrow> small A \<and> small B \<or> A={} \<or> B={}"  (is "_ = ?rhs")
proof
  assume *: "small (A \<times> B)"
  { have "small A \<and> small B" if "x \<in> A" "y \<in> B" for x y
    proof -
      have "A \<subseteq> fst ` (A \<times> B)" "B \<subseteq> snd ` (A \<times> B)"
        using that by auto
      with that show ?thesis
        by (metis * replacement smaller_than_small)
    qed    }
  then show ?rhs
    by (metis equals0I)
next
  assume ?rhs
  then show "small (A \<times> B)"
    by auto
qed

subsection \<open>Disjoint Sum\<close>

definition vsum :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<Uplus>\<close> 65) where
 "A \<Uplus> B \<equiv> (VSigma (set {0}) (\<lambda>x. A)) \<squnion> (VSigma (set {1}) (\<lambda>x. B))"

definition Inl :: "V\<Rightarrow>V" where
     "Inl a \<equiv> \<langle>0,a\<rangle>"

definition Inr :: "V\<Rightarrow>V" where
     "Inr b \<equiv> \<langle>1,b\<rangle>"

lemmas sum_defs = vsum_def Inl_def Inr_def

lemma Inl_nonzero [simp]:"Inl x \<noteq> 0"
  by (metis Inl_def vpair_nonzero)

lemma Inr_nonzero [simp]:"Inr x \<noteq> 0"
  by (metis Inr_def vpair_nonzero)

subsubsection\<open>Equivalences for the injections and an elimination rule\<close>

lemma Inl_in_sum_iff [iff]: "Inl a \<in> elts (A \<Uplus> B) \<longleftrightarrow> a \<in> elts A"
  by (auto simp: sum_defs)

lemma Inr_in_sum_iff [iff]: "Inr b \<in> elts (A \<Uplus> B) \<longleftrightarrow> b \<in> elts B"
  by (auto simp: sum_defs)

lemma sumE [elim!]:
  assumes u: "u \<in> elts (A \<Uplus> B)"
  obtains x where "x \<in> elts A" "u=Inl x" | y where "y \<in> elts B" "u=Inr y" using u
  by (auto simp: sum_defs)

subsubsection \<open>Injection and freeness equivalences, for rewriting\<close>

lemma Inl_iff [iff]: "Inl a=Inl b \<longleftrightarrow> a=b"
  by (simp add: sum_defs)

lemma Inr_iff [iff]: "Inr a=Inr b \<longleftrightarrow> a=b"
  by (simp add: sum_defs)

lemma inj_on_Inl [simp]: "inj_on Inl A"
  by (simp add: inj_on_def)

lemma inj_on_Inr [simp]: "inj_on Inr A"
  by (simp add: inj_on_def)

lemma Inl_Inr_iff [iff]: "Inl a=Inr b \<longleftrightarrow> False"
  by (simp add: sum_defs)

lemma Inr_Inl_iff [iff]: "Inr b=Inl a \<longleftrightarrow> False"
  by (simp add: sum_defs)

lemma sum_empty [simp]: "0 \<Uplus> 0 = 0"
  by auto

lemma elts_vsum: "elts (a \<Uplus> b) = Inl ` (elts a) \<union> Inr ` (elts b)"
  by auto

lemma sum_iff: "u \<in> elts (A \<Uplus> B) \<longleftrightarrow> (\<exists>x. x \<in> elts A \<and> u=Inl x) \<or> (\<exists>y. y \<in> elts B \<and> u=Inr y)"
  by blast

lemma sum_subset_iff: "A\<Uplus>B \<le> C\<Uplus>D \<longleftrightarrow> A\<le>C \<and> B\<le>D"
  by (auto simp: less_eq_V_def)

lemma sum_equal_iff:
  fixes A :: V shows "A\<Uplus>B = C\<Uplus>D \<longleftrightarrow> A=C \<and> B=D"
  by (simp add: eq_iff sum_subset_iff)

definition is_sum :: "V \<Rightarrow> bool"
  where "is_sum z = (\<exists>x. z = Inl x \<or> z = Inr x)"

definition sum_case  :: "(V \<Rightarrow> 'a) \<Rightarrow> (V \<Rightarrow> 'a) \<Rightarrow> V \<Rightarrow> 'a"
  where
  "sum_case f g a \<equiv>
    THE z. (\<forall>x. a = Inl x \<longrightarrow> z = f x) \<and> (\<forall>y. a = Inr y \<longrightarrow> z = g y) \<and> (\<not> is_sum a \<longrightarrow> z = undefined)"

lemma sum_case_Inl [simp]: "sum_case f g (Inl x) = f x"
  by (simp add: sum_case_def is_sum_def)

lemma sum_case_Inr [simp]: "sum_case f g (Inr y) = g y"
  by (simp add: sum_case_def is_sum_def)

lemma sum_case_non [simp]: "\<not> is_sum a \<Longrightarrow> sum_case f g a = undefined"
  by (simp add: sum_case_def is_sum_def)

lemma is_sum_cases: "(\<exists>x. z = Inl x \<or> z = Inr x) \<or> \<not> is_sum z"
  by (auto simp: is_sum_def)

lemma sum_case_split:
  "P (sum_case f g a) \<longleftrightarrow> (\<forall>x. a = Inl x \<longrightarrow> P(f x)) \<and> (\<forall>y. a = Inr y \<longrightarrow> P(g y)) \<and> (\<not> is_sum a \<longrightarrow> P undefined)"
  by (cases "is_sum a") (auto simp: is_sum_def)

lemma sum_case_split_asm:
  "P (sum_case f g a) \<longleftrightarrow> \<not> ((\<exists>x. a = Inl x \<and> \<not> P(f x)) \<or> (\<exists>y. a = Inr y \<and> \<not> P(g y)) \<or> (\<not> is_sum a \<and> \<not> P undefined))"
  by (auto simp: sum_case_split)

subsubsection \<open>Applications of disjoint sums and pairs: general union theorems for small sets\<close>

lemma small_Un:
  assumes X: "small X" and Y: "small Y"
  shows "small (X \<union> Y)"
proof -
  obtain x y where "elts x \<approx> X" "elts y \<approx> Y"
    by (meson assms small_eqpoll)
  then have "X \<union> Y \<lesssim> Inl ` (elts x) \<union> Inr ` (elts y)"
    by (metis (mono_tags, lifting) Inr_Inl_iff Un_lepoll_mono disjnt_iff eqpoll_imp_lepoll eqpoll_sym f_inv_into_f inj_on_Inl inj_on_Inr inj_on_image_lepoll_2)
  then show ?thesis
    by (metis lepoll_iff replacement small_elts small_sup_iff smaller_than_small)
qed

lemma small_UN [simp,intro]:
  assumes A: "small A" and B: "\<And>x. x \<in> A \<Longrightarrow> small (B x)"
  shows "small (\<Union>x\<in>A. B x)"
proof -
  obtain a where "elts a \<approx> A" 
    by (meson assms small_eqpoll)
  then obtain f where f: "bij_betw f (elts a) A"
    using eqpoll_def by blast
  have "\<exists>y. elts y \<approx> B x" if "x \<in> A" for x
    using B small_eqpoll that by blast
  then obtain g where g: "\<And>x. x \<in> A \<Longrightarrow> elts (g x) \<approx> B x" 
    by metis
  have sm: "small (Sigma (elts a) (elts \<circ> g \<circ> f))"
    by simp
  have "(\<Union>x\<in>A. B x) \<lesssim> Sigma A B"
    by (metis image_lepoll snd_image_Sigma)
  also have "...  \<lesssim> Sigma (elts a) (elts \<circ> g \<circ> f)"
    by (smt (verit) Sigma_eqpoll_cong bij_betw_iff_bijections comp_apply eqpoll_imp_lepoll eqpoll_sym f g)
  finally show ?thesis
    using lepoll_small sm by blast
qed

lemma small_Union [simp,intro]:
  assumes "\<A> \<subseteq> Collect small" "small \<A>"
  shows "small (\<Union> \<A>)"
  using small_UN [of \<A> "\<lambda>x. x"] assms by (simp add: subset_iff)

subsection\<open>Generalised function space and lambda\<close>

definition VLambda :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "VLambda A b \<equiv> set ((\<lambda>x. \<langle>x,b x\<rangle>) ` elts A)"

definition app :: "[V,V] \<Rightarrow> V"
  where "app f x \<equiv> THE y. \<langle>x,y\<rangle> \<in> elts f"

lemma beta [simp]:
  assumes "x \<in> elts A"
  shows "app (VLambda A b) x = b x"
  using assms by (auto simp: VLambda_def app_def)

definition VPi :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "VPi A B \<equiv> set {f \<in> elts (VPow(VSigma A B)). elts A \<le> Domain (pairs f) \<and> single_valued (pairs f)}"

lemma VPi_I:
  assumes "\<And>x. x \<in> elts A \<Longrightarrow> b x \<in> elts (B x)"
  shows "VLambda A b \<in> elts (VPi A B)"
  proof (clarsimp simp: VPi_def, intro conjI impI)
  show "VLambda A b \<le> VSigma A B"
    by (auto simp: assms VLambda_def split: if_split_asm)
  show "elts A \<subseteq> Domain (pairs (VLambda A b))"
    by (force simp: VLambda_def pairs_iff_elts)
  show "single_valued (pairs (VLambda A b))"
    by (auto simp: VLambda_def single_valued_def pairs_iff_elts)
  show "small {f. f \<le> VSigma A B \<and> elts A \<subseteq> Domain (pairs f) \<and> single_valued (pairs f)}"
    by (metis (mono_tags, lifting) down VPow_iff mem_Collect_eq subsetI)
qed

lemma apply_pair:
  assumes f: "f \<in> elts (VPi A B)" and x: "x \<in> elts A"
  shows "\<langle>x, app f x\<rangle> \<in> elts f"
proof -
  have "x \<in> Domain (pairs f)"
    by (metis (no_types, lifting) VPi_def assms elts_of_set empty_iff mem_Collect_eq subsetD)
  then obtain y where y: "\<langle>x,y\<rangle> \<in> elts f"
    using pairs_iff_elts by auto
  show ?thesis
    unfolding app_def
  proof (rule theI)
    show "\<langle>x, y\<rangle> \<in> elts f"
      by (rule y)
    show "z = y" if "\<langle>x, z\<rangle> \<in> elts f" for z
      using f unfolding VPi_def
      by (metis (mono_tags, lifting) that elts_of_set empty_iff mem_Collect_eq pairs_iff_elts single_valued_def y)
  qed
qed

lemma VPi_D:
  assumes f: "f \<in> elts (VPi A B)" and x: "x \<in> elts A"
  shows "app f x \<in> elts (B x)"
proof -
  have "f \<le> VSigma A B"
    by (metis (no_types, lifting) VPi_def elts_of_set empty_iff f VPow_iff mem_Collect_eq)
  then show ?thesis
    using apply_pair [OF assms] by blast
qed

lemma VPi_memberD:
  assumes f: "f \<in> elts (VPi A B)" and p: "p \<in> elts f"
  obtains x where "x \<in> elts A" "p = \<langle>x, app f x\<rangle>"
proof -
  have "f \<le> VSigma A B"
    by (metis (no_types, lifting) VPi_def elts_of_set empty_iff f VPow_iff mem_Collect_eq)
  then obtain x y where "p = \<langle>x,y\<rangle>" "x \<in> elts A"
    using p by blast
  then have "y = app f x"
    by (metis (no_types, lifting) VPi_def apply_pair elts_of_set equals0D f mem_Collect_eq p pairs_iff_elts single_valuedD)
  then show thesis
    using \<open>p = \<langle>x, y\<rangle>\<close> \<open>x \<in> elts A\<close> that by blast
qed

lemma fun_ext:
  assumes "f \<in> elts (VPi A B)" "g \<in> elts (VPi A B)" "\<And>x. x \<in> elts A \<Longrightarrow> app f x = app g x"
  shows "f = g"
  by (metis VPi_memberD V_equalityI apply_pair assms)

lemma eta[simp]:
  assumes "f \<in> elts (VPi A B)"
  shows "VLambda A ((app)f) = f"
  proof (rule fun_ext [OF _ assms])
  show "VLambda A (app f) \<in> elts (VPi A B)"
    using VPi_D VPi_I assms by auto
qed auto


lemma fst_pairs_VLambda: "fst ` pairs (VLambda A f) = elts A"
  by (force simp: VLambda_def pairs_def)

lemma snd_pairs_VLambda: "snd ` pairs (VLambda A f) = f ` elts A"
  by (force simp: VLambda_def pairs_def)

lemma VLambda_eq_D1: "VLambda A f = VLambda B g \<Longrightarrow> A = B"
  by (metis ZFC_in_HOL.ext fst_pairs_VLambda)

lemma VLambda_eq_D2: "\<lbrakk>VLambda A f = VLambda A g; x \<in> elts A\<rbrakk> \<Longrightarrow> f x = g x"
  by (metis beta)


subsection\<open>Transitive closure of a set\<close>

definition TC :: "V\<Rightarrow>V"
  where "TC \<equiv> transrec (\<lambda>f x. x \<squnion> \<Squnion> (f ` elts x))"

lemma TC: "TC a = a \<squnion> \<Squnion> (TC ` elts a)"
  by (metis (no_types, lifting) SUP_cong TC_def restrict_apply' transrec)

lemma TC_0 [simp]: "TC 0 = 0"
  by (metis TC ZFC_in_HOL.Sup_empty elts_0 image_is_empty sup_V_0_left)

lemma arg_subset_TC: "a \<le> TC a"
  by (metis (no_types) TC sup_ge1)

lemma Transset_TC: "Transset(TC a)"
proof (induction a rule: eps_induct)
  case (step x)
  have 1: "v \<in> elts (TC x)" if "v \<in> elts u" "u \<in> elts x" for u v
    using that unfolding TC [of x]
    using arg_subset_TC by fastforce
  have 2: "v \<in> elts (TC x)" if "v \<in> elts u" "\<exists>x\<in>elts x. u \<in> elts (TC x)" for u v
    using that step unfolding TC [of x] Transset_def by auto
  show ?case
    unfolding Transset_def
    by (subst TC) (force intro: 1 2)
qed

lemma TC_least: "\<lbrakk>Transset x;  a\<le>x\<rbrakk> \<Longrightarrow> TC a \<le> x"
proof (induction a rule: eps_induct)
  case (step y)
  show ?case
  proof (cases "y=0")
    case True
    then show ?thesis
      by auto
  next
    case False
    have "\<Squnion> (TC ` elts y) \<le> x"
    proof (rule cSup_least)
      show "TC ` elts y \<noteq> {}"
        using False by auto
      show "z \<le> x" if "z \<in> TC ` elts y" for z
        using that by (metis Transset_def image_iff step.IH step.prems vsubsetD)
    qed
    then show ?thesis
      by (simp add: step TC [of y])
  qed
qed

definition less_TC (infix \<open>\<sqsubset>\<close> 50)
  where "x \<sqsubset> y \<equiv> x \<in> elts (TC y)"

definition le_TC (infix \<open>\<sqsubseteq>\<close> 50)
  where "x \<sqsubseteq> y \<equiv> x \<sqsubset> y \<or> x=y"

lemma less_TC_imp_not_le: "x \<sqsubset> a \<Longrightarrow> \<not> a \<le> x"
proof (induction a arbitrary: x rule: eps_induct)
  case (step a)
  then show ?case
    unfolding TC[of a] less_TC_def
    using Transset_TC Transset_def by force
qed

lemma non_TC_less_0 [iff]: "\<not> (x \<sqsubset> 0)"
  using less_TC_imp_not_le by blast

lemma less_TC_iff: "x \<sqsubset> y \<longleftrightarrow> (\<exists>z \<in> elts y. x \<sqsubseteq> z)"
  by (auto simp: less_TC_def le_TC_def TC [of y])

lemma nonzero_less_TC: "x \<noteq> 0 \<Longrightarrow> 0 \<sqsubset> x"
  by (metis eps_induct le_TC_def less_TC_iff trad_foundation)

lemma less_irrefl_TC [simp]: "\<not> x \<sqsubset> x"
  using less_TC_imp_not_le by blast

lemma less_asym_TC: "\<lbrakk>x \<sqsubset> y; y \<sqsubset> x\<rbrakk> \<Longrightarrow> False"
  by (metis TC_least Transset_TC Transset_def antisym_conv less_TC_def less_TC_imp_not_le order_refl)

lemma le_antisym_TC: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
  using le_TC_def less_asym_TC by auto

lemma less_le_TC: "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
  using le_TC_def less_asym_TC by blast

lemma less_imp_le_TC [iff]: "x \<sqsubset> y \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: le_TC_def)

lemma le_TC_refl [iff]: "x \<sqsubseteq> x"
  by (simp add: le_TC_def)

lemma le_TC_trans [trans]: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (smt (verit, best) TC_least Transset_TC Transset_def le_TC_def less_TC_def vsubsetD)

context order
begin

lemma nless_le_TC: "(\<not> a \<sqsubset> b) \<longleftrightarrow> (\<not> a \<sqsubseteq> b) \<or> a = b"
  using le_TC_def less_asym_TC by blast

lemma eq_refl_TC: "x = y \<Longrightarrow> x \<sqsubseteq> y"
  by simp

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=) :: V \<Rightarrow> V \<Rightarrow> bool\<close>}, le = @{term \<open>(\<sqsubseteq>)\<close>}, lt = @{term \<open>(\<sqsubset>)\<close>}},
    thms = {trans = @{thm le_TC_trans}, refl = @{thm le_TC_refl}, eqD1 = @{thm eq_refl_TC},
            eqD2 = @{thm eq_refl_TC[OF sym]}, antisym = @{thm le_antisym_TC}, contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF less_le_TC]},
                 nless_le = @{thm eq_reflection[OF nless_le_TC]}}
  }
\<close>

end


lemma less_TC_trans [trans]: "\<lbrakk>x \<sqsubset> y; y \<sqsubset> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z" 
  and less_le_TC_trans: "\<lbrakk>x \<sqsubset> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z" 
  and le_less_TC_trans [trans]: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubset> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  by simp_all

lemma TC_sup_distrib: "TC (x \<squnion> y) = TC x \<squnion> TC y"
  by (simp add: Sup_Un_distrib TC [of "x \<squnion> y"] TC [of x] TC [of y] image_Un sup.assoc sup_left_commute)

lemma TC_Sup_distrib:
  assumes "small X" shows "TC (\<Squnion>X) = \<Squnion>(TC ` X)"
proof -
  have "\<Squnion>X \<le> \<Squnion> (TC ` X)"
    using arg_subset_TC by fastforce
  moreover have "\<Squnion> (\<Union>x\<in>X. TC ` elts x) \<le> \<Squnion> (TC ` X)"
    using assms 
    by clarsimp (meson TC_least Transset_TC Transset_def arg_subset_TC replacement vsubsetD)
  ultimately
  have "\<Squnion> X \<squnion> \<Squnion> (\<Union>x\<in>X. TC ` elts x) \<le> \<Squnion> (TC ` X)"
    by simp
  moreover have "\<Squnion> (TC ` X) \<le> \<Squnion> X \<squnion> \<Squnion> (\<Union>x\<in>X. TC ` elts x)"
  proof (clarsimp simp add: Sup_le_iff assms)
    show "\<exists>x\<in>X. y \<in> elts x"
      if "x \<in> X" "y \<in> elts (TC x)" "\<forall>x\<in>X. \<forall>u\<in>elts x. y \<notin> elts (TC u)" for x y
      using that by (auto simp: TC [of x])
  qed
  ultimately show ?thesis
    using Sup_Un_distrib TC [of "\<Squnion>X"] image_Union assms
    by (simp add: image_Union inf_sup_aci(5) sup.absorb_iff2)
qed

lemma TC': "TC x = x \<squnion> TC (\<Squnion> (elts x))"
  by (simp add: TC [of x] TC_Sup_distrib)

lemma TC_eq_0_iff [simp]: "TC x = 0 \<longleftrightarrow> x=0"
  using arg_subset_TC by fastforce

text\<open>A distinctive induction principle\<close>
lemma TC_induct_down_lemma:
  assumes ab: "a \<sqsubset> b" and base: "b \<le> d"
      and step: "\<And>y z. \<lbrakk>y \<sqsubset> b; y \<in> elts d; z \<in> elts y\<rbrakk> \<Longrightarrow> z \<in> elts d"
    shows "a \<in> elts d"
proof -
  have "Transset (TC b \<sqinter> d)"
    using Transset_TC
    unfolding Transset_def
    by (metis inf.bounded_iff less_TC_def less_eq_V_def local.step subsetI vsubsetD) 
  moreover have "b \<le> TC b \<sqinter> d"
    by (simp add: arg_subset_TC base)
  ultimately show ?thesis
    using TC_least [THEN vsubsetD] ab unfolding less_TC_def
    by (meson TC_least le_inf_iff vsubsetD)
qed

lemma TC_induct_down [consumes 1, case_names base step small]:
  assumes "a \<sqsubset> b"
    and "\<And>y. y \<in> elts b \<Longrightarrow> P y"
    and "\<And>y z. \<lbrakk>y \<sqsubset> b; P y; z \<in> elts y\<rbrakk> \<Longrightarrow> P z"
    and "small (Collect P)"
  shows "P a"
  using TC_induct_down_lemma [of a b "set (Collect P)"] assms
  by (metis elts_of_set mem_Collect_eq vsubsetI)

subsection\<open>Rank of a set\<close>

definition rank :: "V\<Rightarrow>V"
  where "rank a \<equiv> transrec (\<lambda>f x. set (\<Union>y\<in>elts x. elts (succ(f y)))) a"

lemma rank: "rank a = set(\<Union>y \<in> elts a. elts (succ(rank y)))"
  by (subst rank_def [THEN def_transrec], simp)

lemma rank_Sup: "rank a = \<Squnion>((\<lambda>y. succ(rank y)) ` elts a)"
  by (metis elts_Sup image_image rank replacement set_of_elts small_elts)

lemma Ord_rank [simp]: "Ord(rank a)"
proof (induction a rule: eps_induct)
  case (step x)
  then show ?case
    unfolding rank_Sup [of x]
    by (metis (mono_tags, lifting) Ord_Sup Ord_succ imageE)
qed

lemma rank_of_Ord: "Ord i \<Longrightarrow> rank i = i"
  by (induction rule: Ord_induct) (metis (no_types, lifting) Ord_equality SUP_cong rank_Sup)

lemma Ord_iff_rank: "Ord x \<longleftrightarrow> rank x = x"
  using Ord_rank [of x] rank_of_Ord by fastforce

lemma rank_lt: "a \<in> elts b \<Longrightarrow> rank a < rank b"
  by (metis Ord_linear2 Ord_rank ZFC_in_HOL.SUP_le_iff rank_Sup replacement small_elts succ_le_iff order.irrefl)

lemma rank_0 [simp]: "rank 0 = 0"
  using transrec Ord_0 rank_def rank_of_Ord by presburger

lemma rank_succ [simp]: "rank(succ x) = succ(rank x)"
proof (rule order_antisym)
  show "rank (succ x) \<le> succ (rank x)"
    by (metis (no_types, lifting) Sup_insert elts_of_set elts_succ image_insert rank small_UN small_elts subset_insertI sup.orderE vsubsetI)
  show "succ (rank x) \<le> rank (succ x)"
    by (metis (mono_tags, lifting) ZFC_in_HOL.Sup_upper elts_succ image_insert insertI1 rank_Sup replacement small_elts)
qed

lemma rank_mono: "a \<le> b \<Longrightarrow> rank a \<le> rank b"
  using rank [of a] rank [of b] small_UN by force

lemma VsetI: "rank b \<sqsubset> i \<Longrightarrow> b \<in> elts (Vset i)"
proof (induction i arbitrary: b rule: eps_induct)
  case (step x)
  then consider "rank b \<in> elts x" | "(\<exists>y\<in>elts x. rank b \<in> elts (TC y))"
    using le_TC_def less_TC_def less_TC_iff by fastforce
  then have "\<exists>y\<in>elts x. b \<le> Vset y"
  proof cases
    case 1
    then have "b \<le> Vset (rank b)"
      unfolding less_eq_V_def subset_iff
      by (meson Ord_mem_iff_lt Ord_rank le_TC_refl less_TC_iff rank_lt step.IH)
    then show ?thesis
      using "1" by blast
  next
    case 2
    then show ?thesis
      using step.IH
      unfolding less_eq_V_def subset_iff less_TC_def
      by (meson Ord_mem_iff_lt Ord_rank Transset_TC Transset_def rank_lt vsubsetD)
  qed
  then show ?case
    by (simp add: Vset [of x])
qed

lemma Ord_VsetI: "\<lbrakk>Ord i; rank b < i\<rbrakk> \<Longrightarrow> b \<in> elts (Vset i)"
  by (meson Ord_mem_iff_lt Ord_rank VsetI arg_subset_TC less_TC_def vsubsetD)

lemma arg_le_Vset_rank: "a \<le> Vset(rank a)"
  by (simp add: Ord_VsetI rank_lt vsubsetI)

lemma two_in_Vset:
  obtains \<alpha> where  "x \<in> elts (Vset \<alpha>)" "y \<in> elts (Vset \<alpha>)"
  by (metis Ord_rank Ord_VsetI elts_of_set insert_iff rank_lt small_elts small_insert_iff)

lemma rank_eq_0_iff [simp]: "rank x = 0 \<longleftrightarrow> x=0"
  using arg_le_Vset_rank by fastforce

lemma small_ranks_imp_small:
  assumes "small (rank ` A)" shows "small A"
proof -
  define i where "i \<equiv> set (\<Union>(elts ` (rank ` A)))"
  have "Ord i"
    unfolding i_def using Ord_Union Ord_rank assms imageE by blast
  have *: "Vset (rank x) \<le> (Vset i)" if "x \<in> A" for x
    unfolding i_def by (metis Ord_rank Sup_V_def ZFC_in_HOL.Sup_upper Vfrom_mono assms imageI le_less that)
  have "A \<subseteq> elts (VPow (Vset i))"
    by (meson "*" VPow_iff arg_le_Vset_rank order.trans subsetI)
  then show ?thesis
    using down by blast
qed

lemma rank_Union: "rank(\<Squnion> A) = \<Squnion> (rank ` A)"
proof (rule order_antisym)
  have "elts (\<Squnion>y\<in>elts (\<Squnion> A). succ (rank y)) \<subseteq> elts (\<Squnion> (rank ` A))"
    by clarsimp (meson Ord_mem_iff_lt Ord_rank less_V_def rank_lt vsubsetD)
  then show "rank (\<Squnion> A) \<le> \<Squnion> (rank ` A)"
    by (metis less_eq_V_def rank_Sup)
  show "\<Squnion> (rank ` A) \<le> rank (\<Squnion> A)"
  proof (cases "small A")
    case True
    then show ?thesis
      by (simp add: ZFC_in_HOL.SUP_le_iff ZFC_in_HOL.Sup_upper rank_mono)
  next
    case False
    then have "\<not> small (rank ` A)"
      using small_ranks_imp_small by blast
    then show ?thesis
      by blast
  qed
qed

lemma small_bounded_rank:  "small {x. rank x \<in> elts a}"
proof -
  have "{x. rank x \<in> elts a} \<subseteq> {x. rank x \<sqsubset> a}"
    using less_TC_iff by auto
  also have "\<dots> \<subseteq> elts (Vset a)"
    using VsetI by blast
  finally show ?thesis
    using down by simp
qed

lemma small_bounded_rank_le:  "small {x. rank x \<le> a}"
  using small_bounded_rank [of "VPow a"] VPow_iff [of _ a]  by simp

lemma TC_rank_lt: "a \<sqsubset> b \<Longrightarrow> rank a < rank b"
proof (induction rule: TC_induct_down)
  case (base y)
  then show ?case
    by (simp add: rank_lt)
next
  case (step y z)
  then show ?case
    using less_trans rank_lt by blast
next
  case small
  show ?case
    using smaller_than_small [OF small_bounded_rank_le [of "rank b"]]
    by (simp add: Collect_mono less_V_def)
qed

lemma TC_rank_mem: "x \<sqsubset> y \<Longrightarrow> rank x \<in> elts (rank y)"
  by (simp add: Ord_mem_iff_lt TC_rank_lt)

lemma wf_TC_less: "wf {(x,y). x \<sqsubset> y}"
  proof (rule wf_subset [OF wf_inv_image [OF foundation, of rank]])
    show "{(x, y). x \<sqsubset> y} \<subseteq> inv_image {(x, y). x \<in> elts y} rank"
      by (auto simp: TC_rank_mem inv_image_def)
qed

lemma less_TC_minimal:
  assumes "P a"
  obtains x where "P x" "x \<sqsubseteq> a" "\<And>y. y \<sqsubset> x \<Longrightarrow> \<not> P y"
  using wfE_min' [OF wf_TC_less, of "{x. P x \<and> x \<sqsubseteq> a}"]
  by simp (metis le_TC_def less_le_TC_trans assms)

lemma Vfrom_rank_eq: "Vfrom A (rank(x)) = Vfrom A x"
proof (rule order_antisym)
  show "Vfrom A (rank x) \<le> Vfrom A x"
  proof (induction x rule: eps_induct)
    case (step x)
    have "(\<Squnion>j\<in>elts (rank x). VPow (Vfrom A j)) \<le> (\<Squnion>j\<in>elts x. VPow (Vfrom A j))"
      apply (rule Sup_least)
      apply (clarsimp simp add: rank [of x])
      by (meson Ord_in_Ord Ord_rank OrdmemD Vfrom_mono order.trans less_imp_le order.refl step)
    then show ?case
      by (simp add: Vfrom [of _ x] Vfrom [of _ "rank(x)"] sup.coboundedI2)
qed
  show "Vfrom A x \<le> Vfrom A (rank x)"
  proof (induction x rule: eps_induct)
    case (step x)
    have "(\<Squnion>j\<in>elts x. VPow (Vfrom A j)) \<le> (\<Squnion>j\<in>elts (rank x). VPow (Vfrom A j))"
      using step.IH TC_rank_mem less_TC_iff by force
    then show ?case
      by (simp add: Vfrom [of _ x] Vfrom [of _ "rank(x)"] sup.coboundedI2)
  qed
qed

lemma Vfrom_succ: "Vfrom A (succ(i)) = A \<squnion> VPow(Vfrom A i)"
  by (metis Ord_rank Vfrom_rank_eq Vfrom_succ_Ord rank_succ)

lemma Vset_succ_TC:
  assumes "x \<in> elts (Vset (ZFC_in_HOL.succ k))" "u \<sqsubset> x"
  shows "u \<in> elts (Vset k)"
  using assms
  using TC_least Transset_Vfrom Vfrom_succ less_TC_def by auto

subsection\<open>Cardinal Numbers\<close>

text\<open>We extend the membership relation to a wellordering\<close>
definition VWO :: "(V \<times> V) set"
  where "VWO \<equiv> @r. {(x,y). x \<in> elts y} \<subseteq> r \<and> Well_order r \<and> Field r = UNIV"

lemma VWO: "{(x,y). x \<in> elts y} \<subseteq> VWO \<and> Well_order VWO \<and> Field VWO = UNIV"
  unfolding VWO_def
  by (metis (mono_tags, lifting) VWO_def foundation someI_ex total_well_order_extension)

lemma wf_VWO: "wf(VWO - Id)"
  using VWO well_order_on_def by blast

lemma wf_Ord_less: "wf {(x, y). Ord y \<and> x < y}"
  by (metis (no_types, lifting) Ord_mem_iff_lt eps_induct wfpUNIVI wfp_def)

lemma refl_VWO: "refl VWO"
  using VWO order_on_defs by fastforce

lemma trans_VWO: "trans VWO"
  using VWO by (simp add: VWO wo_rel.TRANS wo_rel_def)

lemma antisym_VWO: "antisym VWO"
  using VWO by (simp add: VWO wo_rel.ANTISYM wo_rel_def)

lemma total_VWO: "total VWO"
    using VWO by (metis wo_rel.TOTAL wo_rel.intro)

lemma total_VWOId: "total (VWO-Id)"
  by (simp add: total_VWO)

lemma Linear_order_VWO: "Linear_order VWO"
  using VWO well_order_on_def by blast

lemma wo_rel_VWO: "wo_rel VWO"
  using VWO wo_rel_def by blast

subsubsection \<open>Transitive Closure and VWO\<close>

lemma mem_imp_VWO: "x \<in> elts y \<Longrightarrow> (x,y) \<in> VWO"
  using VWO by blast

lemma less_TC_imp_VWO: "x \<sqsubset> y \<Longrightarrow> (x,y) \<in> VWO"
  unfolding less_TC_def
proof (induction y arbitrary: x rule: eps_induct)
  case (step y' u)
  then consider "u \<in> elts y'" | v where "v \<in> elts y'" "u \<in> elts (TC v)"
    by (auto simp: TC [of y'])
  then show ?case
  proof cases
    case 2
    then show ?thesis
      by (meson mem_imp_VWO step.IH transD trans_VWO)
  qed (use mem_imp_VWO in blast)
qed

lemma le_TC_imp_VWO: "x \<sqsubseteq> y \<Longrightarrow> (x,y) \<in> VWO"
  by (metis Diff_iff Linear_order_VWO Linear_order_in_diff_Id UNIV_I VWO le_TC_def less_TC_imp_VWO)

lemma le_TC_0_iff [simp]: "x \<sqsubseteq> 0 \<longleftrightarrow> x = 0"
  by (simp add: le_TC_def)

lemma less_TC_succ: " x \<sqsubset> succ \<beta> \<longleftrightarrow> x \<sqsubset> \<beta> \<or> x = \<beta>"
  by (metis elts_succ insert_iff le_TC_def less_TC_iff)

lemma le_TC_succ: "x \<sqsubseteq> succ \<beta> \<longleftrightarrow> x \<sqsubseteq> \<beta> \<or> x = succ \<beta>"
  by (simp add: le_TC_def less_TC_succ)

lemma Transset_TC_eq [simp]: "Transset x \<Longrightarrow> TC x = x"
  by (simp add: TC_least arg_subset_TC eq_iff)

lemma Ord_TC_less_iff: "\<lbrakk>Ord \<alpha>; Ord \<beta>\<rbrakk> \<Longrightarrow> \<beta> \<sqsubset> \<alpha> \<longleftrightarrow> \<beta> < \<alpha>"
  by (metis Ord_def Ord_mem_iff_lt Transset_TC_eq less_TC_def)

lemma Ord_mem_iff_less_TC: "Ord l \<Longrightarrow> k \<in> elts l \<longleftrightarrow> k \<sqsubset> l"
  by (simp add: Ord_def less_TC_def)

lemma le_TC_Ord: "\<lbrakk>\<beta> \<sqsubseteq> \<alpha>; Ord \<alpha>\<rbrakk> \<Longrightarrow> Ord \<beta>"
  by (metis Ord_def Ord_in_Ord Transset_TC_eq le_TC_def less_TC_def)

lemma Ord_less_TC_mem:
  assumes "Ord \<alpha>" "\<beta> \<sqsubset> \<alpha>" shows "\<beta> \<in> elts \<alpha>"
  using Ord_def assms less_TC_def by auto

lemma VWO_TC_le: "\<lbrakk>Ord \<alpha>; Ord \<beta>; (\<beta>, \<alpha>) \<in> VWO\<rbrakk> \<Longrightarrow> \<beta> \<sqsubseteq> \<alpha>"
proof (induct \<alpha> arbitrary: \<beta> rule: Ord_induct)
  case (step \<alpha>)
  then show ?case
    by (metis DiffI IdD Linear_order_VWO Linear_order_in_diff_Id Ord_linear Ord_mem_iff_less_TC VWO iso_tuple_UNIV_I le_TC_def mem_imp_VWO)
qed

lemma VWO_iff_Ord_le [simp]: "\<lbrakk>Ord \<alpha>; Ord \<beta>\<rbrakk> \<Longrightarrow> (\<beta>, \<alpha>) \<in> VWO \<longleftrightarrow> \<beta> \<le> \<alpha>"
  by (metis VWO_TC_le Ord_TC_less_iff le_TC_def le_TC_imp_VWO le_less)

lemma zero_TC_le [iff]: "0 \<sqsubseteq> y"
  using le_TC_def nonzero_less_TC by auto

lemma succ_le_TC_iff: "Ord j \<Longrightarrow> succ i \<sqsubseteq> j \<longleftrightarrow> i \<sqsubset> j"
  by (metis Ord_in_Ord Ord_linear Ord_mem_iff_less_TC Ord_succ le_TC_def less_TC_succ less_asym_TC)

lemma VWO_0_iff [simp]: "(x,0) \<in> VWO \<longleftrightarrow> x=0"
proof
  show "x = 0" if "(x, 0) \<in> VWO"
    using zero_TC_le [of x] le_TC_imp_VWO that
    by (metis DiffI Linear_order_VWO Linear_order_in_diff_Id UNIV_I VWO pair_in_Id_conv)
qed auto

lemma VWO_antisym:
  assumes "(x,y) \<in> VWO" "(y,x) \<in> VWO" shows "x=y"
  by (metis Diff_iff IdD Linear_order_VWO Linear_order_in_diff_Id UNIV_I VWO assms)

subsubsection \<open>Relation VWF\<close>

definition VWF where "VWF \<equiv> VWO - Id"

lemma wf_VWF [iff]: "wf VWF"
  by (simp add: VWF_def wf_VWO)

lemma trans_VWF [iff]: "trans VWF"
  by (simp add: VWF_def antisym_VWO trans_VWO trans_diff_Id)

lemma asym_VWF [iff]: "asym VWF"
  by (metis wf_VWF wf_imp_asym)

lemma total_VWF [iff]: "total VWF"
  using VWF_def total_VWOId by auto

lemma total_on_VWF [iff]: "total_on A VWF"
  by (meson UNIV_I total_VWF total_on_def)

lemma VWF_asym:
  assumes "(x,y) \<in> VWF" "(y,x) \<in> VWF" shows False
  using VWF_def assms wf_VWO wf_not_sym by fastforce

lemma VWF_non_refl [iff]: "(x,x) \<notin> VWF"
  by simp

lemma VWF_iff_Ord_less [simp]: "\<lbrakk>Ord \<alpha>; Ord \<beta>\<rbrakk> \<Longrightarrow> (\<alpha>,\<beta>) \<in> VWF \<longleftrightarrow> \<alpha> < \<beta>"
  by (simp add: VWF_def less_V_def)

lemma mem_imp_VWF: "x \<in> elts y \<Longrightarrow> (x,y) \<in> VWF"
  using VWF_def mem_imp_VWO by fastforce


subsection\<open>Order types\<close>

definition ordermap :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> V"
  where "ordermap A r \<equiv> wfrec r (\<lambda>f x. set (f ` {y \<in> A. (y,x) \<in> r}))"

definition ordertype :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> V"
  where "ordertype A r \<equiv> set (ordermap A r ` A)"

lemma ordermap_type:
    "small A \<Longrightarrow> ordermap A r \<in> A \<rightarrow> elts (ordertype A r)"
  by (simp add: ordertype_def)

lemma ordermap_in_ordertype [intro]: "\<lbrakk>a \<in> A; small A\<rbrakk> \<Longrightarrow> ordermap A r a \<in> elts (ordertype A r)"
  by (simp add: ordertype_def)

lemma ordermap: "wf r \<Longrightarrow> ordermap A r a = set (ordermap A r ` {y \<in> A. (y,a) \<in> r})"
  unfolding ordermap_def
  by (auto simp: wfrec_fixpoint adm_wf_def)

lemma wf_Ord_ordermap [iff]: assumes "wf r" "trans r" shows "Ord (ordermap A r x)"
  using \<open>wf r\<close>
proof (induction x rule: wf_induct_rule)
  case (less u)
  have "Transset (set (ordermap A r ` {y \<in> A. (y, u) \<in> r}))"
  proof (clarsimp simp add: Transset_def)
    show "x \<in> ordermap A r ` {y \<in> A. (y, u) \<in> r}"
      if "small (ordermap A r ` {y \<in> A. (y, u) \<in> r})"
        and x: "x \<in> elts (ordermap A r y)" and "y \<in> A" "(y, u) \<in> r" for x y
    proof -
      have "ordermap A r y = ZFC_in_HOL.set (ordermap A r ` {a \<in> A. (a, y) \<in> r})"
        using ordermap assms(1) by force
      then have "x \<in> ordermap A r ` {z \<in> A. (z, y) \<in> r}"
        by (metis (no_types, lifting) elts_of_set empty_iff x)
      then have "\<exists>v. v \<in> A \<and> (v, u) \<in> r \<and> x = ordermap A r v"
        using that transD [OF \<open>trans r\<close>] by blast
      then show ?thesis
        by blast
    qed
  qed
  moreover have "Ord x"
    if "x \<in> elts (set (ordermap A r ` {y \<in> A. (y, u) \<in> r}))" for x
    using that less by (auto simp: split: if_split_asm)
  ultimately show ?case
    by (metis (full_types) Ord_def ordermap assms(1))
qed

lemma wf_Ord_ordertype: assumes "wf r" "trans r" shows "Ord(ordertype A r)"
proof -
  have "y \<le> set (ordermap A r ` A)"
    if "y = ordermap A r x" "x \<in> A" "small (ordermap A r ` A)" for x y
    using that by (auto simp: less_eq_V_def ordermap [OF \<open>wf r\<close>, of A x])
  moreover have "z \<le> y" if "y \<in> ordermap A r ` A" "z \<in> elts y" for y z
    by (metis wf_Ord_ordermap OrdmemD assms imageE order.strict_implies_order that)
  ultimately show ?thesis
    unfolding ordertype_def Ord_def Transset_def by simp
qed

lemma Ord_ordertype [simp]: "Ord(ordertype A VWF)"
  using wf_Ord_ordertype by blast

lemma Ord_ordermap [simp]: "Ord (ordermap A VWF x)"
  by blast

lemma ordertype_singleton [simp]:
  assumes "wf r" 
  shows "ordertype {x} r = 1"
proof -
  have \<dagger>: "{y. y = x \<and> (y, x) \<in> r} = {}"
    using assms by auto
  show ?thesis
    by (auto simp add: ordertype_def assms \<dagger> ordermap [where a=x])
qed


subsubsection\<open>@{term ordermap} preserves the orderings in both directions\<close>

lemma ordermap_mono:
  assumes wx: "(w, x) \<in> r" and "wf r" "w \<in> A" "small A"
    shows "ordermap A r w \<in> elts (ordermap A r x)"
proof -
  have "small {a \<in> A. (a, x) \<in> r} \<and> w \<in> A \<and> (w, x) \<in> r"
    by (simp add: assms)
  then show ?thesis
    using assms ordermap [of r A]
    by (metis (no_types, lifting) elts_of_set image_eqI mem_Collect_eq replacement)
qed

lemma converse_ordermap_mono:
  assumes "ordermap A r y \<in> elts (ordermap A r x)" "wf r" "total_on A r" "x \<in> A" "y \<in> A" "small A"
  shows "(y, x) \<in> r"
proof (cases "x = y")
  case True
  then show ?thesis
    using assms(1) mem_not_refl by blast
next
  case False
  then consider "(x,y) \<in> r" | "(y,x) \<in> r"
    using \<open>total_on A r\<close> assms by (meson UNIV_I total_on_def)
  then show ?thesis
    by (meson ordermap_mono assms mem_not_sym)
qed

lemma converse_ordermap_mono_iff:
  assumes "wf r" "total_on A r" "x \<in> A" "y \<in> A" "small A"
  shows "ordermap A r y \<in> elts (ordermap A r x) \<longleftrightarrow> (y, x) \<in> r"
  by (metis assms converse_ordermap_mono ordermap_mono)

lemma ordermap_surj: "elts (ordertype A r) \<subseteq> ordermap A r ` A"
  unfolding ordertype_def by simp

lemma ordermap_bij:
  assumes "wf r" "total_on A r" "small A"
  shows "bij_betw (ordermap A r) A (elts (ordertype A r))"
  unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on (ordermap A r) A"
    unfolding inj_on_def by (metis assms mem_not_refl ordermap_mono total_on_def)
  show "ordermap A r ` A = elts (ordertype A r)"
    by (metis ordertype_def \<open>small A\<close> elts_of_set replacement)
qed

lemma ordermap_eq_iff [simp]: 
  "\<lbrakk>x \<in> A; y \<in> A; wf r; total_on A r; small A\<rbrakk> \<Longrightarrow> ordermap A r x = ordermap A r y \<longleftrightarrow> x = y"
  by (metis bij_betw_iff_bijections ordermap_bij)

lemma inv_into_ordermap: "\<alpha> \<in> elts (ordertype A r) \<Longrightarrow> inv_into A (ordermap A r) \<alpha> \<in> A"
  by (meson in_mono inv_into_into ordermap_surj)

lemma ordertype_nat_imp_finite:
  assumes "ordertype A r = ord_of_nat m" "small A" "wf r" "total_on A r"
  shows "finite A"
proof -
  have "A \<approx> elts m"
    using eqpoll_def assms ordermap_bij by fastforce 
  then show ?thesis
    using eqpoll_finite_iff finite_Ord_omega by blast
qed

lemma wf_ordertype_eqpoll:
  assumes "wf r" "total_on A r" "small A"
  shows "elts (ordertype A r) \<approx> A"
  using assms eqpoll_def eqpoll_sym ordermap_bij by blast

lemma ordertype_eqpoll:
  assumes "small A"
  shows "elts (ordertype A VWF) \<approx> A"
  using assms wf_ordertype_eqpoll total_VWF wf_VWF
  by (simp add: wf_ordertype_eqpoll total_on_def)

subsection \<open>More advanced @{term ordertype} and @{term ordermap} results\<close>

lemma ordermap_VWF_0 [simp]: "ordermap A VWF 0 = 0"
  by (simp add: ordermap wf_VWO VWF_def)

lemma ordertype_empty [simp]: "ordertype {} r = 0"
  by (simp add: ordertype_def)

lemma ordertype_eq_0_iff [simp]: "\<lbrakk>small X; wf r\<rbrakk> \<Longrightarrow> ordertype X r = 0 \<longleftrightarrow> X = {}"
  by (metis ordertype_def elts_of_set replacement image_is_empty zero_V_def)

lemma ordermap_mono_less:
  assumes "(w, x) \<in> r"
      and "wf r" "trans r"
      and "w \<in> A" "x \<in> A"
      and "small A"
    shows "ordermap A r w < ordermap A r x"
  by (simp add: OrdmemD assms ordermap_mono)

lemma ordermap_mono_le:
  assumes "(w, x) \<in> r \<or> w=x"
      and "wf r" "trans r"
      and "w \<in> A" "x \<in> A"
      and "small A"
    shows "ordermap A r w \<le> ordermap A r x"
  by (metis assms dual_order.strict_implies_order eq_refl ordermap_mono_less)

lemma converse_ordermap_le_mono:
  assumes "ordermap A r y \<le> ordermap A r x" "wf r" "total r"  "x \<in> A" "small A"
  shows "(y, x) \<in> r \<or> y=x"
  by (meson UNIV_I assms mem_not_refl ordermap_mono total_on_def vsubsetD)

lemma ordertype_mono:
  assumes "X \<subseteq> Y" and r: "wf r" "trans r" and "small Y"
  shows "ordertype X r \<le> ordertype Y r"
proof -
  have "small X"
    using assms smaller_than_small by fastforce 
  have *: "ordermap X r x \<le> ordermap Y r x" for x
    using \<open>wf r\<close>
  proof (induction x rule: wf_induct_rule)
    case (less x)
    have "ordermap X r z < ordermap Y r x" if "z \<in> X" and zx: "(z,x) \<in> r" for z
      using less [OF zx] assms
      by (meson Ord_linear2 OrdmemD wf_Ord_ordermap ordermap_mono in_mono leD that(1) vsubsetD zx)
    then show ?case
      by (auto simp add: ordermap [of _ X x] \<open>small X\<close> Ord_mem_iff_lt set_image_le_iff less_eq_V_def r)
  qed
  show ?thesis
  proof -
    have "ordermap Y r ` Y = elts (ordertype Y r)"
      by (metis ordertype_def \<open>small Y\<close> elts_of_set replacement)
    then have "ordertype Y r \<notin> ordermap X r ` X"
      using "*" \<open>X \<subseteq> Y\<close> by fastforce
    then show ?thesis
      by (metis Ord_linear2 Ord_mem_iff_lt ordertype_def wf_Ord_ordertype \<open>small X\<close> elts_of_set replacement r)
  qed
qed

corollary ordertype_VWF_mono:
  assumes "X \<subseteq> Y" "small Y"
  shows "ordertype X VWF \<le> ordertype Y VWF"
  using assms by (simp add: ordertype_mono)

lemma ordertype_UNION_ge:
  assumes "A \<in> \<A>" "wf r" "trans r" "\<A> \<subseteq> Collect small" "small \<A>"
  shows "ordertype A r \<le> ordertype (\<Union>\<A>) r" 
  by (rule ordertype_mono) (use assms in auto)

lemma inv_ordermap_mono_less:
  assumes "(inv_into M (ordermap M r) \<alpha>, inv_into M (ordermap M r) \<beta>) \<in> r" 
    and "small M" and \<alpha>: "\<alpha> \<in> elts (ordertype M r)" and \<beta>: "\<beta> \<in> elts (ordertype M r)"
    and "wf r" "trans r"
  shows "\<alpha> < \<beta>"
proof -
  have "\<alpha> = ordermap M r (inv_into M (ordermap M r) \<alpha>)"
    by (metis \<alpha> f_inv_into_f ordermap_surj subset_eq)
  also have "\<dots> < ordermap M r (inv_into M (ordermap M r) \<beta>)"
    by (meson \<alpha> \<beta> assms in_mono inv_into_into ordermap_mono_less ordermap_surj)
  also have "\<dots> = \<beta>"
    by (meson \<beta> f_inv_into_f in_mono ordermap_surj)
  finally show ?thesis .
qed

lemma inv_ordermap_mono_eq:
  assumes "inv_into M (ordermap M r) \<alpha> = inv_into M (ordermap M r) \<beta>" 
    and "\<alpha> \<in> elts (ordertype M r)" "\<beta> \<in> elts (ordertype M r)"
  shows "\<alpha> = \<beta>"
  by (metis assms f_inv_into_f ordermap_surj subsetD)

lemma inv_ordermap_VWF_mono_le:
  assumes "inv_into M (ordermap M VWF) \<alpha> \<le> inv_into M (ordermap M VWF) \<beta>" 
    and "M \<subseteq> ON" "small M" and \<alpha>: "\<alpha> \<in> elts (ordertype M VWF)" and \<beta>: "\<beta> \<in> elts (ordertype M VWF)"
  shows "\<alpha> \<le> \<beta>"
proof -
  have "\<alpha> = ordermap M VWF (inv_into M (ordermap M VWF) \<alpha>)"
    by (metis \<alpha> f_inv_into_f ordermap_surj subset_eq)
  also have "\<dots> \<le> ordermap M VWF (inv_into M (ordermap M VWF) \<beta>)"
    by (metis ON_imp_Ord VWF_iff_Ord_less assms dual_order.strict_implies_order elts_of_set eq_refl inv_into_into order.not_eq_order_implies_strict ordermap_mono_less ordertype_def replacement trans_VWF wf_VWF)
  also have "\<dots> = \<beta>"
    by (meson \<beta> f_inv_into_f in_mono ordermap_surj)
  finally show ?thesis .
qed

lemma inv_ordermap_VWF_mono_iff:
  assumes "M \<subseteq> ON" "small M" and "\<alpha> \<in> elts (ordertype M VWF)" and "\<beta> \<in> elts (ordertype M VWF)"
  shows "inv_into M (ordermap M VWF) \<alpha> \<le> inv_into M (ordermap M VWF) \<beta> \<longleftrightarrow> \<alpha> \<le> \<beta>"
  by (metis ON_imp_Ord Ord_linear_le assms dual_order.eq_iff inv_into_ordermap inv_ordermap_VWF_mono_le)

lemma inv_ordermap_VWF_strict_mono_iff:
  assumes "M \<subseteq> ON" "small M" and "\<alpha> \<in> elts (ordertype M VWF)" and "\<beta> \<in> elts (ordertype M VWF)"
  shows "inv_into M (ordermap M VWF) \<alpha> < inv_into M (ordermap M VWF) \<beta> \<longleftrightarrow> \<alpha> < \<beta>"
  by (simp add: assms inv_ordermap_VWF_mono_iff less_le_not_le)

lemma strict_mono_on_ordertype:
  assumes "M \<subseteq> ON" "small M"
  obtains f where "f \<in> elts (ordertype M VWF) \<rightarrow> M" "strict_mono_on (elts (ordertype M VWF)) f"
proof 
  show "inv_into M (ordermap M VWF) \<in> elts (ordertype M VWF) \<rightarrow> M"
    by (meson Pi_I' in_mono inv_into_into ordermap_surj)
  show "strict_mono_on (elts (ordertype M VWF)) (inv_into M (ordermap M VWF))"
  proof (clarsimp simp: strict_mono_on_def)
    fix x y
    assume "x \<in> elts (ordertype M VWF)" "y \<in> elts (ordertype M VWF)" "x < y"
    then show "inv_into M (ordermap M VWF) x < inv_into M (ordermap M VWF) y"
      using assms by (meson ON_imp_Ord Ord_linear2 inv_into_into inv_ordermap_VWF_mono_le leD ordermap_surj subsetD)
  qed
qed

lemma ordermap_inc_eq:
  assumes "x \<in> A" "small A"
    and \<pi>: "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; (x,y) \<in> r\<rbrakk> \<Longrightarrow> (\<pi> x, \<pi> y) \<in> s"
    and r: "wf r" "total_on A r" and "wf s" 
  shows "ordermap (\<pi> ` A) s (\<pi> x) = ordermap A r x"
  using \<open>wf r\<close> \<open>x \<in> A\<close>
proof (induction x rule: wf_induct_rule)
  case (less x)
  then have 1: "{y \<in> A. (y, x) \<in> r} = A \<inter> {y. (y, x) \<in> r}"
    using r by auto
  have 2: "{y \<in> \<pi> ` A. (y, \<pi> x) \<in> s} = \<pi> ` A \<inter> {y. (y, \<pi> x) \<in> s}"
    by auto
  have inv\<pi>: "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; (\<pi> x, \<pi> y) \<in> s\<rbrakk> \<Longrightarrow> (x, y) \<in> r"
    by (metis \<pi> \<open>wf s\<close> \<open>total_on A r\<close> total_on_def wf_not_sym)
  have eq: "f ` (\<pi> ` A \<inter> {y. (y, \<pi> x) \<in> s}) = (f \<circ> \<pi>) ` (A \<inter> {y. (y, x) \<in> r})" for f :: "'b \<Rightarrow> V"
    using less by (auto simp: image_subset_iff inv\<pi> \<pi>)
  show ?case
    using less
    by (simp add: ordermap [OF \<open>wf r\<close>, of _ x] ordermap [OF \<open>wf s\<close>, of _ "\<pi> x"] 1 2 eq)
qed

lemma ordertype_inc_eq:
  assumes "small A"
    and \<pi>: "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; (x,y) \<in> r\<rbrakk> \<Longrightarrow> (\<pi> x, \<pi> y) \<in> s"
    and r: "wf r" "total_on A r" and "wf s" 
  shows "ordertype (\<pi> ` A) s = ordertype A r"
proof -
  have "ordermap (\<pi> ` A) s (\<pi> x) = ordermap A r x" if "x \<in> A" for x
    using assms that by (auto simp: ordermap_inc_eq)
  then show ?thesis
    unfolding ordertype_def
    by (metis (no_types, lifting) image_cong image_image)
qed

lemma ordertype_inc_le:
  assumes "small A" "small B"
    and \<pi>: "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; (x,y) \<in> r\<rbrakk> \<Longrightarrow> (\<pi> x, \<pi> y) \<in> s"
    and r: "wf r" "total_on A r" and "wf s" "trans s"
    and "\<pi> ` A \<subseteq> B"
  shows "ordertype A r \<le> ordertype B s"
  by (metis assms ordertype_inc_eq ordertype_mono)

corollary ordertype_VWF_inc_eq:
  assumes "A \<subseteq> ON" "\<pi> ` A \<subseteq> ON" "small A" and "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; x<y\<rbrakk> \<Longrightarrow> \<pi> x < \<pi> y"
  shows "ordertype (\<pi> ` A) VWF = ordertype A VWF"
proof (rule ordertype_inc_eq)
  show "(\<pi> x, \<pi> y) \<in> VWF"
    if "x \<in> A" "y \<in> A" "(x, y) \<in> VWF" for x y
    using that ON_imp_Ord assms by auto
  show "total_on A VWF"
    by (meson UNIV_I total_VWF total_on_def)
qed (use assms in auto)

lemma ordertype_image_ordermap:
  assumes "small A" "X \<subseteq> A" "wf r" "trans r" "total_on X r"
  shows "ordertype (ordermap A r ` X) VWF = ordertype X r"
proof (rule ordertype_inc_eq)
  show "small X"
    by (meson assms smaller_than_small)
  show "(ordermap A r x, ordermap A r y) \<in> VWF"
    if "x \<in> X" "y \<in> X" "(x, y) \<in> r" for x y
    by (meson that wf_Ord_ordermap VWF_iff_Ord_less assms ordermap_mono_less subsetD)
qed (use assms in auto)
    
lemma ordertype_map_image:
  assumes "B \<subseteq> A" "small A"
  shows "ordertype (ordermap A VWF ` A - ordermap A VWF ` B) VWF = ordertype (A - B) VWF"
proof -
  have "ordermap A VWF ` A - ordermap A VWF ` B = ordermap A VWF ` (A - B)"
    using assms by auto
  then have "ordertype (ordermap A VWF ` A - ordermap A VWF ` B) VWF = ordertype (ordermap A VWF ` (A - B)) VWF"
    by simp
  also have "\<dots> = ordertype (A - B) VWF"
    using \<open>small A\<close> ordertype_image_ordermap by fastforce
  finally show ?thesis .
qed

proposition ordertype_le_ordertype:
  assumes r: "wf r" "total_on A r" and "small A"
  assumes s: "wf s" "total_on B s" "trans s" and "small B"
  shows "ordertype A r \<le> ordertype B s \<longleftrightarrow>
         (\<exists>f \<in> A \<rightarrow> B. inj_on f A \<and> (\<forall>x \<in> A. \<forall>y \<in> A. ((x,y) \<in> r \<longrightarrow> (f x, f y) \<in> s)))"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  define f where "f \<equiv> inv_into B (ordermap B s) \<circ> ordermap A r"
  show ?rhs
  proof (intro bexI conjI ballI impI)
    have AB: "elts (ordertype A r) \<subseteq> ordermap B s ` B"
      by (metis L assms(7) ordertype_def replacement set_of_elts small_elts subset_iff_less_eq_V)
    have bijA: "bij_betw (ordermap A r) A (elts (ordertype A r))"
      using ordermap_bij \<open>small A\<close> r by blast
    have "inv_into B (ordermap B s) (ordermap A r i) \<in> B" if "i \<in> A" for i
      by (meson L \<open>small A\<close> inv_into_into ordermap_in_ordertype ordermap_surj subsetD that vsubsetD)
    then show "f \<in> A \<rightarrow> B"
      by (auto simp: Pi_iff f_def)
    show "inj_on f A"
    proof (clarsimp simp add: f_def inj_on_def)
      fix x y
      assume "x \<in> A" "y \<in> A"
        and "inv_into B (ordermap B s) (ordermap A r x) = inv_into B (ordermap B s) (ordermap A r y)"
      then have "ordermap A r x = ordermap A r y"
        by (meson AB \<open>small A\<close> inv_into_injective ordermap_in_ordertype subsetD)
      then show "x = y"
        by (metis \<open>x \<in> A\<close> \<open>y \<in> A\<close> bijA bij_betw_inv_into_left)
    qed
  next
    fix x y
    assume "x \<in> A" "y \<in> A" and "(x, y) \<in> r"
    have \<ddagger>: "ordermap A r y \<in> ordermap B s ` B"
      by (meson L \<open>y \<in> A\<close> \<open>small A\<close> in_mono ordermap_in_ordertype ordermap_surj vsubsetD)
    moreover have \<dagger>: "\<And>x. inv_into B (ordermap B s) (ordermap A r x) = f x"
      by (simp add: f_def)
    then have *: "ordermap B s (f y) = ordermap A r y"
      using \<ddagger> by (metis f_inv_into_f)
    moreover have "ordermap A r x \<in> ordermap B s ` B"
      by (meson L \<open>x \<in> A\<close> \<open>small A\<close> in_mono ordermap_in_ordertype ordermap_surj vsubsetD)
    moreover have "ordermap A r x < ordermap A r y"
      using * r s by (metis (no_types) wf_Ord_ordermap OrdmemD \<open>(x, y) \<in> r\<close> \<open>x \<in> A\<close> \<open>small A\<close> ordermap_mono)
    ultimately show "(f x, f y) \<in> s"
      using \<dagger> s by (metis assms(7) f_inv_into_f inv_into_into less_asym ordermap_mono_less total_on_def)
  qed
next
  assume R: ?rhs
  then obtain f where f: "f\<in>A \<rightarrow> B" "inj_on f A" "\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> r \<longrightarrow> (f x, f y) \<in> s"
    by blast
  show ?lhs
    by (rule ordertype_inc_le [where \<pi>=f]) (use f assms in auto)
qed

lemma iso_imp_ordertype_eq_ordertype:
  assumes iso: "iso r r' f"
    and "wf r"
    and "Total r"
    and sm: "small (Field r)"
  shows "ordertype (Field r) r = ordertype (Field r') r'"
  by (metis (no_types, lifting) iso_forward iso_wf assms iso_Field ordertype_inc_eq sm)

lemma ordertype_infinite_ge_\<omega>:
  assumes "infinite A" "small A"
  shows "ordertype A VWF \<ge> \<omega>"
proof -
  have "inj_on (ordermap A VWF) A"
    by (meson ordermap_bij \<open>small A\<close> bij_betw_def total_on_VWF wf_VWF)
  then have "infinite (ordermap A VWF ` A)"
    using \<open>infinite A\<close> finite_image_iff by blast
  then show ?thesis
    using Ord_ordertype \<open>small A\<close> infinite_Ord_omega by (auto simp: ordertype_def)
qed

lemma ordertype_eqI:
  assumes "wf r" "total_on A r" "small A" "wf s" 
          "bij_betw f A B" "(\<forall>x \<in> A. \<forall>y \<in> A. (f x, f y) \<in> s \<longleftrightarrow> (x,y) \<in> r)"
  shows "ordertype A r = ordertype B s"
  by (metis assms bij_betw_imp_surj_on ordertype_inc_eq)

lemma ordermap_eq_self:
  assumes "Ord \<alpha>" and x: "x \<in> elts \<alpha>" 
  shows "ordermap (elts \<alpha>) VWF x = x" 
  using Ord_in_Ord [OF assms] x 
proof (induction x rule: Ord_induct)
  case (step x)
  have 1: "{y \<in> elts \<alpha>. (y, x) \<in> VWF} = elts x" (is "?A = _")
  proof
    show "?A \<subseteq> elts x"
      using \<open>Ord \<alpha>\<close> by clarify (meson Ord_in_Ord Ord_mem_iff_lt VWF_iff_Ord_less step.hyps)
    show "elts x \<subseteq> ?A"
      using \<open>Ord \<alpha>\<close> by clarify (meson Ord_in_Ord Ord_trans OrdmemD VWF_iff_Ord_less step.prems)
  qed
  show ?case
    using step
    by (simp add: ordermap [OF wf_VWF, of _ x] 1 Ord_trans [of _ _ \<alpha>] step.prems \<open>Ord \<alpha>\<close> cong: image_cong)
qed

lemma ordertype_eq_Ord [simp]:
  assumes "Ord \<alpha>" 
  shows "ordertype (elts \<alpha>) VWF = \<alpha>"
  using assms ordermap_eq_self [OF assms] by (simp add: ordertype_def)


proposition ordertype_eq_iff:
  assumes \<alpha>: "Ord \<alpha>" and r: "wf r" and "small A" "total_on A r" "trans r"
  shows "ordertype A r = \<alpha> \<longleftrightarrow>
         (\<exists>f. bij_betw f A (elts \<alpha>) \<and> (\<forall>x \<in> A. \<forall>y \<in> A. f x < f y \<longleftrightarrow> (x,y) \<in> r))"
    (is "?lhs = ?rhs")
proof safe
  assume eq: "\<alpha> = ordertype A r"
  show "\<exists>f. bij_betw f A (elts (ordertype A r)) \<and> (\<forall>x\<in>A. \<forall>y\<in>A. f x < f y \<longleftrightarrow> ((x, y) \<in> r))"
  proof (intro exI conjI ballI)
    show "bij_betw (ordermap A r) A (elts (ordertype A r))"
      by (simp add: assms ordermap_bij)
    then show "ordermap A r x < ordermap A r y \<longleftrightarrow> (x, y) \<in> r"
      if "x \<in> A" "y \<in> A" for x y
      using that assms
      by (metis order.asym ordermap_mono_less total_on_def)
  qed
next
  fix f 
  assume f: "bij_betw f A (elts \<alpha>)" "\<forall>x\<in>A. \<forall>y\<in>A. f x < f y \<longleftrightarrow> (x, y) \<in> r"
  have "ordertype A r = ordertype (elts \<alpha>) VWF"
  proof (rule ordertype_eqI)
    show "\<forall>x\<in>A. \<forall>y\<in>A. ((f x, f y) \<in> VWF) = ((x, y) \<in> r)"
      by (meson Ord_in_Ord VWF_iff_Ord_less \<alpha> bij_betwE f)
  qed (use assms f in auto)
  then show ?lhs
    by (simp add: \<alpha>)
qed

corollary ordertype_VWF_eq_iff:
  assumes "Ord \<alpha>" "small A"
  shows "ordertype A VWF = \<alpha> \<longleftrightarrow>
         (\<exists>f. bij_betw f A (elts \<alpha>) \<and> (\<forall>x \<in> A. \<forall>y \<in> A. f x < f y \<longleftrightarrow> (x,y) \<in> VWF))"
  by (metis UNIV_I assms ordertype_eq_iff total_VWF total_on_def trans_VWF wf_VWF)


lemma ordertype_le_Ord:
  assumes "Ord \<alpha>" "X \<subseteq> elts \<alpha>"
  shows "ordertype X VWF \<le> \<alpha>"
  by (metis assms ordertype_VWF_mono ordertype_eq_Ord small_elts)

lemma ordertype_inc_le_Ord:
  assumes "small A" "Ord \<alpha>"
    and \<pi>: "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; (x,y) \<in> r\<rbrakk> \<Longrightarrow> \<pi> x < \<pi> y"
    and "wf r" "total_on A r" 
    and sub: "\<pi> ` A \<subseteq> elts \<alpha>"
  shows "ordertype A r \<le> \<alpha>"
proof -
  have "\<And>x y. \<lbrakk>x\<in>A; y\<in>A; (x,y) \<in> r\<rbrakk> \<Longrightarrow> (\<pi> x, \<pi> y) \<in> VWF"
    by (meson Ord_in_Ord VWF_iff_Ord_less \<pi> \<open>Ord \<alpha>\<close> sub image_subset_iff)
  with assms show ?thesis
    by (metis ordertype_inc_eq ordertype_le_Ord wf_VWF)
qed

lemma le_ordertype_obtains_subset:
  assumes \<alpha>: "\<beta> \<le> \<alpha>" "ordertype H VWF = \<alpha>" and "small H" "Ord \<beta>"
  obtains G where "G \<subseteq> H" "ordertype G VWF = \<beta>" 
proof (intro exI conjI that)
  let ?f = "ordermap H VWF"
  show \<ddagger>: "inv_into H ?f ` elts \<beta> \<subseteq> H"
    unfolding image_subset_iff
    by (metis \<alpha> inv_into_into ordermap_surj subsetD vsubsetD)
  have "\<exists>f. bij_betw f (inv_into H ?f ` elts \<beta>) (elts \<beta>) \<and> (\<forall>x\<in>inv_into H ?f ` elts \<beta>. \<forall>y\<in>inv_into H ?f ` elts \<beta>. (f x < f y) = ((x, y) \<in> VWF))"
  proof (intro exI conjI ballI iffI)
    show "bij_betw ?f (inv_into H ?f ` elts \<beta>) (elts \<beta>)"
      using ordermap_bij [OF wf_VWF total_on_VWF \<open>small H\<close>] \<alpha> 
      by (metis bij_betw_inv_into_RIGHT bij_betw_subset less_eq_V_def \<ddagger>)
  next
    fix x y
    assume x: "x \<in> inv_into H ?f ` elts \<beta>"
        and y: "y \<in> inv_into H ?f ` elts \<beta>"
    show "?f x < ?f y" if "(x,y) \<in> VWF"
      using that \<ddagger> \<open>small H\<close> in_mono ordermap_mono_less x y by fastforce
    show "(x,y) \<in> VWF" if "?f x < ?f y"
      using that \<ddagger> \<open>small H\<close> in_mono ordermap_mono_less [OF _ wf_VWF trans_VWF] x y
      by (metis UNIV_I less_imp_not_less total_VWF total_on_def)
  qed
  then show "ordertype (inv_into H ?f ` elts \<beta>) VWF = \<beta>"
    by (subst ordertype_eq_iff) (use assms in auto)
qed

lemma ordertype_infinite_\<omega>:
  assumes "A \<subseteq> elts \<omega>" "infinite A"
  shows "ordertype A VWF = \<omega>"
proof (rule antisym)
  show "ordertype A VWF \<le> \<omega>"
    by (simp add: assms ordertype_le_Ord)
  show "\<omega> \<le> ordertype A VWF"
    using assms down ordertype_infinite_ge_\<omega> by auto
qed

text \<open>For infinite sets of natural numbers\<close>
lemma ordertype_nat_\<omega>:
  assumes "infinite N" shows "ordertype N less_than = \<omega>"
proof -
  have "small N"
    by (meson inj_on_def ord_of_nat_inject small_def small_iff_range small_image_nat_V)
  have "ordertype (ord_of_nat ` N) VWF = \<omega>"
    by (force simp: assms finite_image_iff inj_on_def intro: ordertype_infinite_\<omega>)
  moreover have "ordertype (ord_of_nat ` N) VWF = ordertype N less_than"
    by (auto intro: ordertype_inc_eq \<open>small N\<close>)
  ultimately show ?thesis
    by simp
qed

proposition ordertype_eq_ordertype:
  assumes r: "wf r" "total_on A r" "trans r" and "small A"
  assumes s: "wf s" "total_on B s" "trans s" and "small B"
  shows "ordertype A r = ordertype B s \<longleftrightarrow>
         (\<exists>f. bij_betw f A B \<and> (\<forall>x \<in> A. \<forall>y \<in> A. (f x, f y) \<in> s \<longleftrightarrow> (x,y) \<in> r))"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  define \<gamma> where "\<gamma> = ordertype A r"
  have A: "bij_betw (ordermap A r) A (ordermap A r ` A)"
    by (meson ordermap_bij assms(4) bij_betw_def r)
  have B: "bij_betw (ordermap B s) B (ordermap B s ` B)"
    by (meson ordermap_bij assms(8) bij_betw_def s)
  define f where "f \<equiv> inv_into B (ordermap B s) \<circ> ordermap A r"
  show ?rhs
  proof (intro exI conjI)
    have bijA: "bij_betw (ordermap A r) A (elts \<gamma>)"
      unfolding \<gamma>_def using ordermap_bij \<open>small A\<close> r by blast
    moreover have bijB: "bij_betw (ordermap B s) B (elts \<gamma>)"
      by (simp add: L \<gamma>_def ordermap_bij \<open>small B\<close> s)
    ultimately show bij: "bij_betw f A B"
      unfolding f_def using bij_betw_comp_iff bij_betw_inv_into by blast
    have invB: "\<And>\<alpha>. \<alpha> \<in> elts \<gamma> \<Longrightarrow> ordermap B s (inv_into B (ordermap B s) \<alpha>) = \<alpha>"
      by (meson bijB bij_betw_inv_into_right)
    have ordermap_A_\<gamma>: "\<And>a. a \<in> A \<Longrightarrow> ordermap A r a \<in> elts \<gamma>"
      using bijA bij_betwE by auto
    have f_in_B: "\<And>a. a \<in> A \<Longrightarrow> f a \<in> B"
      using bij bij_betwE by fastforce
    show "\<forall>x\<in>A. \<forall>y\<in>A. (f x, f y) \<in> s \<longleftrightarrow> (x, y) \<in> r"
    proof (intro iffI ballI)
      fix x y
      assume "x \<in> A" "y \<in> A" and ins: "(f x, f y) \<in> s"
      then have "ordermap A r x < ordermap A r y"
        unfolding o_def 
        by (metis (mono_tags, lifting) f_def \<open>small B\<close> comp_apply f_in_B invB ordermap_A_\<gamma> ordermap_mono_less s(1) s(3))
      then show "(x, y) \<in> r"
        by (metis \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>small A\<close> order.asym ordermap_mono_less r total_on_def)
    next
      fix x y
      assume "x \<in> A" "y \<in> A" and "(x, y) \<in> r"
      then have "ordermap A r x < ordermap A r y"
        by (simp add: \<open>small A\<close> ordermap_mono_less r)
      then have "(f y, f x) \<notin> s"
        by (metis (mono_tags, lifting) \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>small B\<close> comp_apply f_def f_in_B invB order.asym ordermap_A_\<gamma> ordermap_mono_less s(1) s(3))
      moreover have "f y \<noteq> f x"
        by (metis \<open>(x, y) \<in> r\<close> \<open>x \<in> A\<close> \<open>y \<in> A\<close> bij bij_betw_inv_into_left r(1) wf_not_sym)
      ultimately show "(f x, f y) \<in> s"
        by (meson \<open>x \<in> A\<close> \<open>y \<in> A\<close> f_in_B s(2) total_on_def)
    qed
  qed
next
  assume ?rhs
  then show ?lhs
    using assms ordertype_eqI  by blast
qed

corollary ordertype_eq_ordertype_iso:
  assumes r: "wf r" "total_on A r" "trans r" and "small A" and FA: "Field r = A"
  assumes s: "wf s" "total_on B s" "trans s" and "small B" and FB: "Field s = B"
  shows "ordertype A r = ordertype B s \<longleftrightarrow> (\<exists>f. iso r s f)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then obtain f where "bij_betw f A B" "\<forall>x \<in> A. \<forall>y \<in> A. (f x, f y) \<in> s \<longleftrightarrow> (x,y) \<in> r"
    using assms ordertype_eq_ordertype by blast
  then show ?rhs
    using FA FB iso_iff2 by blast
next
  assume ?rhs
  then show ?lhs
    using FA FB \<open>small A\<close> iso_imp_ordertype_eq_ordertype r by blast
qed

lemma Limit_ordertype_imp_Field_Restr:
  assumes Lim: "Limit (ordertype A r)" and r: "wf r" "total_on A r" and "small A"
  shows "Field (Restr r A) = A"
proof -
  have "\<exists>y\<in>A. (x,y) \<in> r" if "x \<in> A" for x
  proof -
    let ?oy = "succ (ordermap A r x)"
    have \<section>: "?oy \<in> elts (ordertype A r)"
      by (simp add: Lim \<open>small A\<close> ordermap_in_ordertype succ_in_Limit_iff that)
    then have A: "inv_into A (ordermap A r) ?oy \<in> A"
      by (simp add: inv_into_ordermap)
    moreover have "(x, inv_into A (ordermap A r) ?oy) \<in> r"
    proof -
      have "ordermap A r x \<in> elts (ordermap A r (inv_into A (ordermap A r) ?oy))"
        by (metis "\<section>" elts_succ f_inv_into_f insert_iff ordermap_surj subsetD)
      then show ?thesis
        by (metis \<open>small A\<close> A converse_ordermap_mono r that)
    qed
    ultimately show ?thesis ..
  qed
  then have "A \<subseteq> Field (Restr r A)"
    by (auto simp: Field_def)
  then show ?thesis
    by (simp add: Field_Restr_subset subset_antisym)
qed

lemma ordertype_Field_Restr:
  assumes "wf r" "total_on A r" "trans r" "small A" "Field (Restr r A) = A"
  shows "ordertype (Field (Restr r A)) (Restr r A) = ordertype A r"
  using assms by (force simp: ordertype_eq_ordertype wf_Int1 total_on_def trans_Restr)

proposition ordertype_eq_ordertype_iso_Restr:
  assumes r: "wf r" "total_on A r" "trans r" and "small A" and FA: "Field (Restr r A) = A"
  assumes s: "wf s" "total_on B s" "trans s" and "small B" and FB: "Field (Restr s B) = B"
  shows "ordertype A r = ordertype B s \<longleftrightarrow> (\<exists>f. iso (Restr r A) (Restr s B) f)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then obtain f where "bij_betw f A B" "\<forall>x \<in> A. \<forall>y \<in> A. (f x, f y) \<in> s \<longleftrightarrow> (x,y) \<in> r"
    using assms ordertype_eq_ordertype by blast
  then show ?rhs
    using FA FB bij_betwE unfolding iso_iff2 by fastforce
next
  assume ?rhs
  moreover
  have "ordertype (Field (Restr r A)) (Restr r A) = ordertype A r"
    using FA \<open>small A\<close> ordertype_Field_Restr r by blast
  moreover
  have "ordertype (Field (Restr s B)) (Restr s B) = ordertype B s"
    using FB \<open>small B\<close> ordertype_Field_Restr s by blast
  ultimately show ?lhs
    using iso_imp_ordertype_eq_ordertype FA FB \<open>small A\<close> r
    by (fastforce intro: total_on_imp_Total_Restr trans_Restr wf_Int1)
qed

lemma ordermap_insert:
  assumes "Ord \<alpha>" and y: "Ord y" "y \<le> \<alpha>" and U: "U \<subseteq> elts \<alpha>"
  shows "ordermap (insert \<alpha> U) VWF y = ordermap U VWF y"
  using y
proof (induction rule: Ord_induct)
  case (step y)
  then have 1: "{u \<in> U. (u, y) \<in> VWF} = elts y \<inter> U"
    apply (simp add: set_eq_iff)
    by (meson Ord_in_Ord Ord_mem_iff_lt VWF_iff_Ord_less assms subsetD)
  have 2: "{u \<in> insert \<alpha> U. (u, y) \<in> VWF} = elts y \<inter> U"
    apply (simp add: set_eq_iff)
    by (meson Ord_in_Ord Ord_mem_iff_lt VWF_iff_Ord_less assms leD step.hyps step.prems subsetD)
  show ?case
    using step
    apply (simp only: ordermap [OF wf_VWF, of _ y] 1 2)
    by (meson Int_lower1 Ord_is_Transset Sup.SUP_cong Transset_def assms(1) in_mono vsubsetD)
qed

lemma ordertype_insert:
  assumes "Ord \<alpha>" and U: "U \<subseteq> elts \<alpha>"
  shows "ordertype (insert \<alpha> U) VWF = succ (ordertype U VWF)"
proof -
  have \<dagger>: "{y \<in> insert \<alpha> U. (y, \<alpha>) \<in> VWF} = U" "{y \<in> U. (y, \<alpha>) \<in> VWF} = U"
    using Ord_in_Ord OrdmemD assms by auto
  have eq: "\<And>x. x \<in> U \<Longrightarrow> ordermap (insert \<alpha> U) VWF x = ordermap U VWF x"
    by (meson Ord_in_Ord Ord_is_Transset Transset_def U assms(1) in_mono ordermap_insert)
  have "ordertype (insert \<alpha> U) VWF =
        ZFC_in_HOL.set (insert (ordermap U VWF \<alpha>) (ordermap U VWF ` U))"
    by (simp add: ordertype_def ordermap_insert assms eq)
  also have "\<dots> = succ (ZFC_in_HOL.set (ordermap U VWF ` U))"
    using "\<dagger>" U by (simp add: ordermap [OF wf_VWF, of _ \<alpha>] down succ_def vinsert_def)
  also have "\<dots> = succ (ordertype U VWF)"
    by (simp add: ordertype_def)
  finally show ?thesis .
qed

lemma finite_ordertype_le_card:
  assumes "finite A" "wf r" "trans r" 
  shows "ordertype A r \<le> ord_of_nat (card A)"
proof -
  have "Ord (ordertype A r)"
    by (simp add: wf_Ord_ordertype assms)
  moreover have "ordermap A r ` A = elts (ordertype A r)"
    by (simp add: ordertype_def finite_imp_small \<open>finite A\<close>)
  moreover have "card (ordermap A r ` A) \<le> card A"
    using \<open>finite A\<close> card_image_le by blast
  ultimately show ?thesis
    by (metis Ord_linear_le Ord_ord_of_nat \<open>finite A\<close> card_ord_of_nat card_seteq finite_imageI less_eq_V_def)
qed

lemma ordertype_VWF_\<omega>:
  assumes "finite A"
  shows "ordertype A VWF \<in> elts \<omega>"
proof -
  have "finite (ordermap A VWF ` A)"
    using assms by blast
  then have "ordertype A VWF < \<omega>"
    by (meson Ord_\<omega> OrdmemD trans_VWF wf_VWF assms finite_ordertype_le_card le_less_trans ord_of_nat_\<omega>)
  then show ?thesis
    by (simp add: Ord_mem_iff_lt)
qed

lemma ordertype_VWF_finite_nat:
  assumes "finite A"
  shows "ordertype A VWF = ord_of_nat (card A)"
  by (metis finite_imp_small ordermap_bij total_on_VWF wf_VWF \<omega>_def assms bij_betw_same_card card_ord_of_nat elts_of_set f_inv_into_f inf ordertype_VWF_\<omega>)

lemma finite_ordertype_eq_card:
  assumes "small A" "wf r" "trans r" "total_on A r"
  shows "ordertype A r = ord_of_nat m \<longleftrightarrow> finite A \<and> card A = m"
  using ordermap_bij [OF \<open>wf r\<close>]
proof -
  have *: "bij_betw (ordermap A r) A (elts (ordertype A r))"
    by (simp add: assms ordermap_bij)
  moreover have "card (ordermap A r ` A) = card A"
    by (meson bij_betw_def * card_image)
  ultimately show ?thesis
    using assms bij_betw_finite bij_betw_imp_surj_on finite_Ord_omega ordertype_VWF_finite_nat wf_Ord_ordertype by fastforce
qed


lemma ex_bij_betw_strict_mono_card:
  assumes "finite M" "M \<subseteq> ON"
  obtains h where "bij_betw h {..<card M} M" and "strict_mono_on {..<card M} h"
proof -
  have bij: "bij_betw (ordermap M VWF) M (elts (card M))"
    using Finite_V \<open>finite M\<close> ordermap_bij ordertype_VWF_finite_nat by fastforce
  let ?h = "(inv_into M (ordermap M VWF)) \<circ> ord_of_nat"
  show thesis
  proof
    show bijh: "bij_betw ?h {..<card M} M"
    proof (rule bij_betw_trans)
      show "bij_betw ord_of_nat {..<card M} (elts (card M))"
        by (simp add: bij_betw_def elts_ord_of_nat inj_on_def)
      show "bij_betw (inv_into M (ordermap M VWF)) (elts (card M)) M"
        using Finite_V assms bij_betw_inv_into ordermap_bij ordertype_VWF_finite_nat by fastforce
    qed
    show "strict_mono_on {..<card M} ?h"
    proof -
      have "?h m < ?h n"
        if "m < n" "n < card M" for m n
      proof (rule ccontr)
        obtain mn: "m \<in> elts (ordertype M VWF)" "n \<in> elts (ordertype M VWF)"
          using \<open>m < n\<close> \<open>n < card M\<close> \<open>finite M\<close> ordertype_VWF_finite_nat by auto
        have ord: "Ord (?h m)" "Ord (?h n)"
          using bijh assms(2) bij_betwE that by fastforce+
        moreover
        assume "\<not> ?h m < ?h n"
        ultimately consider "?h m = ?h n" | "?h m > ?h n"
          using Ord_linear_lt by blast
        then show False
        proof cases
          case 1
          then have "m = n"
            by (metis inv_ordermap_mono_eq mn comp_apply ord_of_nat_inject)
          with \<open>m < n\<close> show False by blast 
        next
          case 2
          then have "ord_of_nat n \<le> ord_of_nat m"
            by (metis Finite_V mn assms comp_def inv_ordermap_VWF_mono_le less_imp_le)
          then show ?thesis
            using leD \<open>m < n\<close> by blast
        qed
      qed
      with assms show ?thesis
        by (auto simp: strict_mono_on_def)
    qed
  qed
qed

lemma ordertype_finite_less_than [simp]: 
  assumes "finite A" shows "ordertype A less_than = card A"
proof -
  let ?M = "ord_of_nat ` A"
  obtain M: "finite ?M" "?M \<subseteq> ON"
    using Ord_ord_of_nat assms by blast
  have "ordertype A less_than = ordertype ?M VWF"
    by (rule ordertype_inc_eq [symmetric]) (use assms finite_imp_small total_on_def in \<open>force+\<close>)
  also have "\<dots> = card A"
  proof (subst ordertype_eq_iff)
    let ?M = "ord_of_nat ` A"
    obtain h where bijh: "bij_betw h {..<card A} ?M" and smh: "strict_mono_on {..<card A} h"
      by (metis M card_image ex_bij_betw_strict_mono_card inj_on_def ord_of_nat_inject)
    define f where "f \<equiv> ord_of_nat \<circ> inv_into {..<card A} h"
    show "\<exists>f. bij_betw f ?M (elts (card A)) \<and> (\<forall>x\<in>?M. \<forall>y\<in>?M. f x < f y \<longleftrightarrow> ((x, y) \<in> VWF))"
    proof (intro exI conjI ballI)
      have "bij_betw (ord_of_nat \<circ> inv_into {..<card A} h) (ord_of_nat ` A) (ord_of_nat ` {..<card A})"
        by (meson UNIV_I bijh bij_betw_def bij_betw_inv_into bij_betw_subset bij_betw_trans inj_ord_of_nat subsetI)
      then show "bij_betw f ?M (elts (card A))"
        by (metis elts_ord_of_nat f_def)
    next
      fix x y
      assume xy: "x \<in> ?M" "y \<in> ?M"
      then obtain m n where "x = ord_of_nat m" "y = ord_of_nat n"
        by auto
      have "(f x < f y) \<longleftrightarrow> ((h \<circ> inv_into {..<card A} h) x < (h \<circ> inv_into {..<card A} h) y)"
        unfolding f_def using smh bij_betw_imp_surj_on [OF bijh] 
        apply simp
        by (metis (mono_tags, lifting) inv_into_into not_less_iff_gr_or_eq order.asym strict_mono_onD xy)
      also have "\<dots> = (x < y)"
        using bijh
        by (simp add: bij_betw_inv_into_right xy)
      also have "\<dots> \<longleftrightarrow> ((x, y) \<in> VWF)"
        using M(2) ON_imp_Ord xy by auto
      finally show "(f x < f y) \<longleftrightarrow> ((x, y) \<in> VWF)" . 
    qed 
  qed auto
  finally show ?thesis .
qed


subsection \<open>Cardinality of an arbitrary HOL set\<close>

definition gcard :: "'a set \<Rightarrow> V" 
  where "gcard X \<equiv> if small X then (LEAST i. Ord i \<and> elts i \<approx> X) else 0"

subsection\<open>Cardinality of a set\<close>

definition vcard :: "V\<Rightarrow>V"
  where "vcard a \<equiv> (LEAST i. Ord i \<and> elts i \<approx> elts a)"

lemma gcard_eq_vcard [simp]: "gcard (elts x) = vcard x"
  by (simp add: vcard_def gcard_def)

definition Card:: "V\<Rightarrow>bool"
  where "Card i \<equiv> i = vcard i"

abbreviation CARD where "CARD \<equiv> Collect Card"

lemma cardinal_cong: "elts x \<approx> elts y \<Longrightarrow> vcard x = vcard y"
  unfolding vcard_def by (meson eqpoll_sym eqpoll_trans)

lemma gcardinal_cong:
  assumes "X \<approx> Y" shows "gcard X = gcard Y"
proof -
  have "(LEAST i. Ord i \<and> elts i \<approx> X) = (LEAST i. Ord i \<and> elts i \<approx> Y)"
    by (meson eqpoll_sym eqpoll_trans assms)
  then show ?thesis
    unfolding gcard_def
    by (meson eqpoll_sym small_eqcong assms)
qed

lemma vcard_set_image: "inj_on f (elts x) \<Longrightarrow> vcard (set (f ` elts x)) = vcard x"
  by (simp add: cardinal_cong)

lemma gcard_image: "inj_on f X \<Longrightarrow> gcard (f ` X) = gcard X"
  by (simp add: gcardinal_cong)

lemma Card_cardinal_eq: "Card \<kappa> \<Longrightarrow> vcard \<kappa> = \<kappa>"
  by (simp add: Card_def)

lemma Card_is_Ord:
  assumes "Card \<kappa>" shows "Ord \<kappa>"
proof -
  obtain \<alpha> where "Ord \<alpha>" "elts \<alpha> \<approx> elts \<kappa>"
    using Ord_ordertype ordertype_eqpoll by blast
  then have "Ord (LEAST i. Ord i \<and> elts i \<approx> elts \<kappa>)"
    by (metis Ord_Least)
  then show ?thesis
    using Card_def vcard_def assms by auto
qed

lemma cardinal_eqpoll: "elts (vcard a) \<approx> elts a"
  unfolding vcard_def
  using ordertype_eqpoll [of "elts a"] Ord_LeastI by (meson Ord_ordertype small_elts)

lemma inj_into_vcard:
  obtains f where "f \<in> elts A \<rightarrow> elts (vcard A)" "inj_on f (elts A)"
  using cardinal_eqpoll [of A] inj_on_the_inv_into the_inv_into_onto
  by (fastforce simp: Pi_iff bij_betw_def eqpoll_def)

lemma cardinal_idem [simp]: "vcard (vcard a) = vcard a"
  using cardinal_cong cardinal_eqpoll by blast

lemma subset_smaller_vcard:
  assumes "\<kappa> \<le> vcard x" "Card \<kappa>"
  obtains y where "y \<le> x" "vcard y = \<kappa>"
proof -
  obtain \<phi> where \<phi>: "bij_betw \<phi> (elts (vcard x)) (elts x)"
    using cardinal_eqpoll eqpoll_def by blast
  show thesis
  proof
    let ?y = "ZFC_in_HOL.set (\<phi> ` elts \<kappa>)"
    show "?y \<le> x"
      by (meson \<phi> assms bij_betwE set_image_le_iff small_elts vsubsetD) 
    show "vcard ?y = \<kappa>"
      by (metis vcard_set_image Card_def assms bij_betw_def bij_betw_subset \<phi> less_eq_V_def)
  qed
qed

text\<open>every natural number is a (finite) cardinal\<close>
lemma nat_into_Card:
  assumes "\<alpha> \<in> elts \<omega>" shows "Card(\<alpha>)"
proof (unfold Card_def vcard_def, rule sym)
  obtain n where n: "\<alpha> = ord_of_nat n"
    by (metis \<omega>_def assms elts_of_set imageE inf)
  have "Ord(\<alpha>)" using assms by auto
  moreover
  { fix \<beta>
    assume "\<beta> < \<alpha>" "Ord \<beta>" "elts \<beta> \<approx> elts \<alpha>"
    with n have "elts \<beta> \<approx> {..<n}"
      by (simp add: ord_of_nat_eq_initial [of n] eqpoll_trans inj_on_def inj_on_image_eqpoll_self)
    hence False using assms n  \<open>Ord \<beta>\<close> \<open>\<beta> < \<alpha>\<close> \<open>Ord(\<alpha>)\<close>
      by (metis \<open>elts \<beta> \<approx> elts \<alpha>\<close> card_seteq eqpoll_finite_iff eqpoll_iff_card finite_lessThan less_eq_V_def less_le_not_le order_refl)
  }
  ultimately
    show "(LEAST i. Ord i \<and> elts i \<approx> elts \<alpha>) = \<alpha>"
      by (metis (no_types, lifting) Least_equality Ord_linear_le eqpoll_refl less_le_not_le)
  qed

lemma Card_ord_of_nat [simp]: "Card (ord_of_nat n)"
  by (simp add: \<omega>_def nat_into_Card)

lemma Card_0 [iff]: "Card 0"
  by (simp add: nat_into_Card)

lemma CardI: "\<lbrakk>Ord i; \<And>j. \<lbrakk>j < i; Ord j\<rbrakk> \<Longrightarrow> \<not> elts j \<approx> elts i\<rbrakk> \<Longrightarrow> Card i"
  unfolding Card_def vcard_def
  by (metis Ord_Least Ord_linear_lt cardinal_eqpoll eqpoll_refl not_less_Ord_Least vcard_def)

lemma vcard_0 [simp]: "vcard 0 = 0"
  using Card_0 Card_def by auto

lemma Ord_cardinal [simp,intro!]: "Ord(vcard a)"
  unfolding vcard_def by (metis Card_def Card_is_Ord cardinal_cong cardinal_eqpoll vcard_def)

lemma gcard_big_0: "\<not> small X \<Longrightarrow> gcard X = 0"
  by (simp add: gcard_def)

lemma gcard_eq_card:
  assumes "finite X" shows "gcard X = ord_of_nat (card X)"
proof -
  have "\<And>y. Ord y \<and> elts y \<approx> X \<Longrightarrow> ord_of_nat (card X) \<le> y"
    by (metis assms eqpoll_finite_iff eqpoll_iff_card order_le_less ordertype_VWF_finite_nat ordertype_eq_Ord)
  then have "(LEAST i. Ord i \<and> elts i \<approx> X) = ord_of_nat (card X)"
    by (simp add: assms eqpoll_iff_card finite_Ord_omega Least_equality)
  with assms show ?thesis
    by (simp add: finite_imp_small gcard_def)
qed

lemma gcard_empty_0 [simp]: "gcard {} = 0"
  by (simp add: gcard_eq_card) 

lemma gcard_single_1 [simp]: "gcard {x} = 1"
  by (simp add: gcard_eq_card one_V_def)

lemma Card_gcard [iff]: "Card (gcard X)"
  by (metis Card_0 Card_def cardinal_idem gcard_big_0 gcardinal_cong small_eqpoll gcard_eq_vcard)

lemma gcard_eqpoll: "small X \<Longrightarrow> elts (gcard X) \<approx> X"
  by (metis cardinal_eqpoll eqpoll_trans gcard_eq_vcard gcardinal_cong small_eqpoll)

lemma lepoll_imp_gcard_le:
  assumes "A \<lesssim> B" "small B"
  shows "gcard A \<le> gcard B"
proof -
  have "elts (gcard A) \<approx> A" "elts (gcard B) \<approx> B"
    by (meson assms gcard_eqpoll lepoll_small)+
  with \<open>A \<lesssim> B\<close> show ?thesis
    by (metis Ord_cardinal Ord_linear2 eqpoll_sym gcard_eq_vcard gcardinal_cong lepoll_antisym
              lepoll_trans2 less_V_def less_eq_V_def subset_imp_lepoll)
qed

lemma gcard_image_le:
  assumes "small A" shows "gcard (f ` A) \<le> gcard A"
  using assms image_lepoll lepoll_imp_gcard_le by blast

lemma subset_imp_gcard_le:
  assumes "A \<subseteq> B" "small B"
  shows "gcard A \<le> gcard B"
  by (simp add: assms lepoll_imp_gcard_le subset_imp_lepoll)

lemma gcard_le_lepoll: "\<lbrakk>gcard A \<le> \<alpha>; small A\<rbrakk> \<Longrightarrow> A \<lesssim> elts \<alpha>"
  by (meson eqpoll_sym gcard_eqpoll lepoll_trans1 less_eq_V_def subset_imp_lepoll)

subsection\<open>Cardinality of a set\<close>

text\<open>The cardinals are the initial ordinals.\<close>
lemma Card_iff_initial: "Card \<kappa> \<longleftrightarrow> Ord \<kappa> \<and> (\<forall>\<alpha>. Ord \<alpha> \<and> \<alpha> < \<kappa> \<longrightarrow> ~ elts \<alpha> \<approx> elts \<kappa>)"
  by (metis CardI Card_def Card_is_Ord not_less_Ord_Least vcard_def)

lemma Card_\<omega> [iff]: "Card \<omega>"
  by (meson CardI Ord_\<omega> eqpoll_finite_iff infinite_Ord_omega infinite_\<omega> leD)

lemma lt_Card_imp_lesspoll: "\<lbrakk>i < a; Card a; Ord i\<rbrakk> \<Longrightarrow> elts i \<prec> elts a"
  by (meson Card_iff_initial less_eq_V_def less_imp_le lesspoll_def subset_imp_lepoll)

lemma lepoll_imp_Card_le:
  assumes "elts a \<lesssim> elts b" shows "vcard a \<le> vcard b"
  using assms lepoll_imp_gcard_le by fastforce

lemma lepoll_cardinal_le: "\<lbrakk>elts A \<lesssim> elts i; Ord i\<rbrakk> \<Longrightarrow> vcard A \<le> i"
  by (metis Ord_Least Ord_linear2 dual_order.trans eqpoll_refl lepoll_imp_Card_le not_less_Ord_Least vcard_def)

lemma cardinal_le_lepoll: "vcard A \<le> \<alpha> \<Longrightarrow> elts A \<lesssim> elts \<alpha>"
  by (meson cardinal_eqpoll eqpoll_sym lepoll_trans1 less_eq_V_def subset_imp_lepoll)

lemma lesspoll_imp_Card_less:
  assumes "elts a \<prec> elts b" shows "vcard a < vcard b"
  by (metis assms cardinal_eqpoll eqpoll_sym eqpoll_trans lepoll_imp_Card_le less_V_def lesspoll_def)


lemma Card_Union [simp,intro]:
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> Card(x)" shows "Card(\<Squnion>A)"
proof (rule CardI)
  show "Ord(\<Squnion>A)" using A
    by (simp add: Card_is_Ord Ord_Sup)
next
  fix j
  assume j: "j < \<Squnion>A" "Ord j"
  hence "\<exists>c\<in>A. j < c \<and> Card(c)" using A
    by (meson Card_is_Ord Ord_linear2 ZFC_in_HOL.Sup_least leD)
  then obtain c where c: "c\<in>A" "j < c" "Card(c)"
    by blast
  hence jls: "elts j \<prec> elts c"
    using j(2) lt_Card_imp_lesspoll by blast
  { assume eqp: "elts j \<approx> elts (\<Squnion>A)"
    have  "elts c \<lesssim> elts (\<Squnion>A)" using c
      by (metis Card_def Sup_V_def ZFC_in_HOL.Sup_upper cardinal_le_lepoll j(1) not_less_0)
    also have "... \<approx> elts j"  by (rule eqpoll_sym [OF eqp])
    also have "... \<prec> elts c"  by (rule jls)
    finally have "elts c \<prec> elts c" .
    hence False
      by auto
  } thus "\<not> elts j \<approx> elts (\<Squnion>A)" by blast
qed

lemma Card_UN: "(\<And>x. x \<in> A \<Longrightarrow> Card(K x)) ==> Card(Sup (K ` A))"
  by blast

subsection\<open>Transfinite recursion for definitions based on the three cases of ordinals\<close>

definition
  transrec3 :: "[V, [V,V]\<Rightarrow>V, [V,V\<Rightarrow>V]\<Rightarrow>V, V] \<Rightarrow> V" where
    "transrec3 a b c \<equiv>
       transrec (\<lambda>r x.
         if x=0 then a
         else if Limit x then c x (\<lambda>y \<in> elts x. r y)
         else b(pred x) (r (pred x)))"

lemma transrec3_0 [simp]: "transrec3 a b c 0 = a"
  by (simp add: transrec transrec3_def)

lemma transrec3_succ [simp]:
     "transrec3 a b c (succ i) = b i (transrec3 a b c i)"
  by (simp add: transrec transrec3_def)

lemma transrec3_Limit [simp]:
     "Limit i \<Longrightarrow>  transrec3 a b c i = c i (\<lambda>j \<in> elts i. transrec3 a b c j)"
  unfolding transrec3_def
  by (subst transrec) auto


subsection \<open>Cardinal Addition\<close>

definition cadd :: "[V,V]\<Rightarrow>V"       (infixl \<open>\<oplus>\<close> 65)
  where "\<kappa> \<oplus> \<mu> \<equiv> vcard (\<kappa> \<Uplus> \<mu>)"

subsubsection\<open>Cardinal addition is commutative\<close>

lemma vsum_commute_eqpoll: "elts (a\<Uplus>b) \<approx> elts (b\<Uplus>a)"
proof -
  have "bij_betw (\<lambda>z \<in> elts (a\<Uplus>b). sum_case Inr Inl z) (elts (a\<Uplus>b)) (elts (b\<Uplus>a))"
    unfolding bij_betw_def
  proof (intro conjI inj_onI)
    show "restrict (sum_case Inr Inl) (elts (a \<Uplus> b)) ` elts (a \<Uplus> b) = elts (b \<Uplus> a)"
     apply auto
     apply (metis (no_types) imageI sum_case_Inr sum_iff)
      by (metis Inl_in_sum_iff imageI sum_case_Inl)
  qed auto
  then show ?thesis
    using eqpoll_def by blast
qed

lemma cadd_commute: "i \<oplus> j = j \<oplus> i"
  by (simp add: cadd_def cardinal_cong vsum_commute_eqpoll)

subsubsection\<open>Cardinal addition is associative\<close>

lemma sum_assoc_bij:
  "bij_betw (\<lambda>z \<in> elts ((a\<Uplus>b)\<Uplus>c). sum_case(sum_case Inl (\<lambda>y. Inr(Inl y))) (\<lambda>y. Inr(Inr y)) z)
      (elts ((a\<Uplus>b)\<Uplus>c)) (elts (a\<Uplus>(b\<Uplus>c)))"
  by (rule_tac f' = "sum_case (\<lambda>x. Inl (Inl x)) (sum_case (\<lambda>x. Inl (Inr x)) Inr)"
      in bij_betw_byWitness) auto

lemma sum_assoc_eqpoll: "elts ((a\<Uplus>b)\<Uplus>c) \<approx> elts (a\<Uplus>(b\<Uplus>c))"
  unfolding eqpoll_def by (metis sum_assoc_bij)

lemma elts_vcard_vsum_eqpoll: "elts (vcard (i \<Uplus> j)) \<approx> Inl ` elts i \<union> Inr ` elts j"
proof -
  have "elts (i \<Uplus> j) \<approx> Inl ` elts i \<union> Inr ` elts j"
    by (simp add: elts_vsum)
  then show ?thesis
    using cardinal_eqpoll eqpoll_trans by blast
qed

lemma cadd_assoc: "(i \<oplus> j) \<oplus> k = i \<oplus> (j \<oplus> k)"
proof (unfold cadd_def, rule cardinal_cong)
  have "elts (vcard(i \<Uplus> j) \<Uplus> k) \<approx> elts ((i \<Uplus> j) \<Uplus> k)"
    by (auto simp: disjnt_def elts_vsum elts_vcard_vsum_eqpoll intro: Un_eqpoll_cong)
  also have "\<dots>  \<approx> elts (i \<Uplus> (j \<Uplus> k))"
    by (rule sum_assoc_eqpoll)
  also have "\<dots>  \<approx> elts (i \<Uplus> vcard(j \<Uplus> k))"
    by (auto simp: disjnt_def elts_vsum elts_vcard_vsum_eqpoll [THEN eqpoll_sym] intro: Un_eqpoll_cong)
  finally show "elts (vcard (i \<Uplus> j) \<Uplus> k) \<approx> elts (i \<Uplus> vcard (j \<Uplus> k))" .
qed

lemma cadd_left_commute: "j \<oplus> (i \<oplus> k) = i \<oplus> (j \<oplus> k)"
  using cadd_assoc cadd_commute by force

lemmas cadd_ac = cadd_assoc cadd_commute cadd_left_commute

text\<open>0 is the identity for addition\<close>
lemma vsum_0_eqpoll: "elts (0\<Uplus>a) \<approx> elts a"
  by (simp add: elts_vsum)

lemma cadd_0 [simp]: "Card \<kappa> \<Longrightarrow> 0 \<oplus> \<kappa> = \<kappa>"
  by (metis Card_def cadd_def cardinal_cong vsum_0_eqpoll)

lemma cadd_0_right [simp]: "Card \<kappa> \<Longrightarrow> \<kappa> \<oplus> 0 = \<kappa>"
  by (simp add: cadd_commute)

lemma vsum_lepoll_self: "elts a \<lesssim> elts (a\<Uplus>b)"
  unfolding elts_vsum  by (meson Inl_iff Un_upper1 inj_onI lepoll_def)

lemma cadd_le_self:
  assumes \<kappa>: "Card \<kappa>" shows "\<kappa> \<le> \<kappa> \<oplus> a"
proof (unfold cadd_def)
  have "\<kappa> \<le> vcard \<kappa>"
    using Card_def \<kappa> by auto
  also have "\<dots> \<le> vcard (\<kappa> \<Uplus> a)"
    by (simp add: lepoll_imp_Card_le vsum_lepoll_self)
  finally show "\<kappa> \<le> vcard (\<kappa> \<Uplus> a)" .
qed

text\<open>Monotonicity of addition\<close>
lemma cadd_le_mono: "\<lbrakk>\<kappa>' \<le> \<kappa>; \<mu>' \<le> \<mu>\<rbrakk> \<Longrightarrow> \<kappa>' \<oplus> \<mu>' \<le> \<kappa> \<oplus> \<mu>"
  unfolding cadd_def
  by (metis (no_types) lepoll_imp_Card_le less_eq_V_def subset_imp_lepoll sum_subset_iff)

subsection\<open>Cardinal multiplication\<close>

definition cmult :: "[V,V]\<Rightarrow>V"       (infixl \<open>\<otimes>\<close> 70)
  where "\<kappa> \<otimes> \<mu> \<equiv> vcard (VSigma \<kappa> (\<lambda>z. \<mu>))"

subsubsection\<open>Cardinal multiplication is commutative\<close>

lemma prod_bij: "\<lbrakk>bij_betw f A C; bij_betw g B D\<rbrakk>
             \<Longrightarrow> bij_betw (\<lambda>(x, y). (f x, g y)) (A \<times> B) (C \<times> D)"
  apply (rule bij_betw_byWitness [where f' = "\<lambda>(x,y). (inv_into A f x, inv_into B g y)"])
     apply (auto simp: bij_betw_inv_into_left bij_betw_inv_into_right bij_betwE)
  using bij_betwE bij_betw_inv_into apply blast+
  done

lemma cmult_commute: "i \<otimes> j = j \<otimes> i"
proof -
  have "(\<lambda>(x, y). \<langle>x, y\<rangle>) ` (elts i \<times> elts j) \<approx> (\<lambda>(x, y). \<langle>x, y\<rangle>) ` (elts j \<times> elts i)"
    by (simp add: times_commute_eqpoll)
  then show ?thesis
    unfolding cmult_def
    using cardinal_cong elts_VSigma by auto
qed

subsubsection\<open>Cardinal multiplication is associative\<close>

lemma elts_vcard_VSigma_eqpoll: "elts (vcard (vtimes i j)) \<approx> elts i \<times> elts j"
proof -
  have "elts (vtimes i j) \<approx> elts i \<times> elts j"
    by (simp add: elts_VSigma)
  then show ?thesis
    using cardinal_eqpoll eqpoll_trans by blast
qed

lemma elts_cmult: "elts (\<kappa>' \<otimes> \<kappa>) \<approx> elts \<kappa>' \<times> elts \<kappa>"
  by (simp add: cmult_def elts_vcard_VSigma_eqpoll)

lemma cmult_assoc: "(i \<otimes> j) \<otimes> k = i \<otimes> (j \<otimes> k)"
  unfolding cmult_def
proof (rule cardinal_cong)
  have "elts (vcard (vtimes i j)) \<times> elts k \<approx> (elts i \<times> elts j) \<times> elts k"
    by (blast intro: times_eqpoll_cong elts_vcard_VSigma_eqpoll cardinal_eqpoll)
  also have "\<dots>  \<approx> elts i \<times> (elts j \<times> elts k)"
    by (rule times_assoc_eqpoll)
  also have "\<dots>  \<approx> elts i \<times> elts (vcard (vtimes j k))"
    by (blast intro: times_eqpoll_cong elts_vcard_VSigma_eqpoll cardinal_eqpoll eqpoll_sym)
  finally show "elts (VSigma (vcard (vtimes i j)) (\<lambda>z. k)) \<approx> elts (VSigma i (\<lambda>z. vcard (vtimes j k)))"
    by (simp add: elts_VSigma)
qed

subsubsection\<open>Cardinal multiplication distributes over addition\<close>

lemma cadd_cmult_distrib: "(i \<oplus> j) \<otimes> k = (i \<otimes> k) \<oplus> (j \<otimes> k)"
  unfolding cadd_def cmult_def
proof (rule cardinal_cong)
have "elts (vtimes (vcard (i \<Uplus> j)) k) \<approx> elts (vcard (vsum i j)) \<times> elts k"
  using cardinal_eqpoll elts_vcard_VSigma_eqpoll eqpoll_sym eqpoll_trans by blast
  also have "\<dots> \<approx> (Inl ` elts i \<union> Inr ` elts j) \<times> elts k"
    using elts_vcard_vsum_eqpoll times_eqpoll_cong by blast
  also have "\<dots> \<approx> (Inl ` elts i) \<times> elts k \<union> (Inr ` elts j) \<times> elts k"
    by (simp add: Sigma_Un_distrib1)
  also have "\<dots>  \<approx> elts (vtimes i k \<Uplus> vtimes j k)"
    unfolding Plus_def
    by (auto simp: elts_vsum elts_VSigma disjnt_iff intro!: Un_eqpoll_cong times_eqpoll_cong)
  also have "\<dots>  \<approx> elts (vcard (vtimes i k \<Uplus> vtimes j k))"
    by (simp add: cardinal_eqpoll eqpoll_sym)
  also have "\<dots>  \<approx> elts (vcard (vtimes i k) \<Uplus> vcard (vtimes j k))"
    by (metis cadd_assoc cadd_def cardinal_cong cardinal_eqpoll vsum_0_eqpoll vsum_commute_eqpoll)
  finally show "elts (VSigma (vcard (i \<Uplus> j)) (\<lambda>z. k))
             \<approx> elts (vcard (vtimes i k) \<Uplus> vcard (vtimes j k))" .
qed

text\<open>Multiplication by 0 yields 0\<close>
lemma cmult_0 [simp]: "0 \<otimes> i = 0"
  using Card_0 Card_def cmult_def by auto

text\<open>1 is the identity for multiplication\<close>
lemma cmult_1 [simp]: assumes "Card \<kappa>" shows "1 \<otimes> \<kappa> = \<kappa>"
proof -
  have "elts (vtimes (set {0}) \<kappa>) \<approx> elts \<kappa>"
    by (auto simp: elts_VSigma intro!: times_singleton_eqpoll)
  then show ?thesis
    by (metis Card_def assms cardinal_cong cmult_def elts_1 set_of_elts)
qed

subsection\<open>Some inequalities for multiplication\<close>

lemma cmult_square_le: assumes "Card \<kappa>" shows "\<kappa> \<le> \<kappa> \<otimes> \<kappa>"
proof -
  have "elts \<kappa> \<lesssim> elts (\<kappa> \<otimes> \<kappa>)"
    using times_square_lepoll [of "elts \<kappa>"] cmult_def elts_vcard_VSigma_eqpoll eqpoll_sym lepoll_trans2
    by fastforce
  then show ?thesis
    using Card_def assms cmult_def lepoll_cardinal_le by fastforce
qed

text\<open>Multiplication by a non-empty set\<close>
lemma cmult_le_self: assumes "Card \<kappa>" "\<alpha> \<noteq> 0" shows "\<kappa> \<le> \<kappa> \<otimes> \<alpha>"
proof -
  have "\<kappa> = vcard \<kappa>"
    using Card_def \<open>Card \<kappa>\<close> by blast
  also have "\<dots> \<le> vcard (vtimes \<kappa> \<alpha>)"
    apply (rule lepoll_imp_Card_le)
    apply (simp add: elts_VSigma)
    by (metis ZFC_in_HOL.ext \<open>\<alpha> \<noteq> 0\<close> elts_0 lepoll_times1)
  also have "\<dots> = \<kappa> \<otimes> \<alpha>"
    by (simp add: cmult_def)
  finally show ?thesis .
qed


text\<open>Monotonicity of multiplication\<close>
lemma cmult_le_mono: "\<lbrakk>\<kappa>' \<le> \<kappa>; \<mu>' \<le> \<mu>\<rbrakk> \<Longrightarrow> \<kappa>' \<otimes> \<mu>' \<le> \<kappa> \<otimes> \<mu>"
  unfolding cmult_def
  by (auto simp: elts_VSigma intro!: lepoll_imp_Card_le times_lepoll_mono subset_imp_lepoll)

lemma vcard_Sup_le_cmult:
  assumes "small U" and \<kappa>: "\<And>x. x \<in> U \<Longrightarrow> vcard x \<le> \<kappa>"
  shows "vcard (\<Squnion>U) \<le> vcard (set U) \<otimes> \<kappa>"
proof -
  have "\<exists>f. f \<in> elts x \<rightarrow> elts \<kappa> \<and> inj_on f (elts x)" if "x \<in> U" for x
    using \<kappa> [OF that] by (metis cardinal_le_lepoll image_subset_iff_funcset lepoll_def)
  then obtain \<phi> where \<phi>: "\<And>x. x \<in> U \<Longrightarrow> (\<phi> x) \<in> elts x \<rightarrow> elts \<kappa> \<and> inj_on (\<phi> x) (elts x)"
    by metis
  define u where "u \<equiv> \<lambda>y. @x. x \<in> U \<and> y \<in> elts x"
  have u: "u y \<in> U \<and> y \<in> elts (u y)" if "y \<in> \<Union>(elts ` U)" for y
    unfolding u_def by (metis (mono_tags, lifting)that someI2_ex UN_iff)  
  define \<psi> where "\<psi> \<equiv> \<lambda>y. (u y, \<phi> (u y) y)"
  have U: "elts (vcard (set U)) \<approx> U"
    by (metis \<open>small U\<close> cardinal_eqpoll elts_of_set)
  have "elts (\<Squnion>U) = \<Union>(elts ` U)"
    using \<open>small U\<close> by blast
  also have "\<dots> \<lesssim> U \<times> elts \<kappa>"
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on \<psi> (\<Union> (elts ` U))"
      using \<phi> u by (smt (verit) \<psi>_def inj_on_def prod.inject)
    show "\<psi> ` \<Union> (elts ` U) \<subseteq> U \<times> elts \<kappa>"
      using \<phi> u by (auto simp: \<psi>_def)
  qed
  also have "\<dots>  \<approx> elts (vcard (set U) \<otimes> \<kappa>)"
    using U elts_cmult eqpoll_sym eqpoll_trans times_eqpoll_cong by blast
  finally have "elts (\<Squnion> U) \<lesssim> elts (vcard (set U) \<otimes> \<kappa>)" .
  then show ?thesis
    by (simp add: cmult_def lepoll_cardinal_le)
qed

subsection\<open>The finite cardinals\<close>

lemma succ_lepoll_succD: "elts (succ(m)) \<lesssim> elts (succ(n)) \<Longrightarrow> elts m \<lesssim> elts n"
  by (simp add: insert_lepoll_insertD)


text\<open>Congruence law for @{text succ} under equipollence\<close>
lemma succ_eqpoll_cong: "elts a \<approx> elts b \<Longrightarrow> elts (succ(a)) \<approx> elts (succ(b))"
  by (simp add: succ_def insert_eqpoll_cong)

lemma sum_succ_eqpoll: "elts (succ a \<Uplus> b) \<approx> elts (succ(a\<Uplus>b))"
  unfolding eqpoll_def
proof (rule exI)
  let ?f = "\<lambda>z. if z=Inl a then a\<Uplus>b else z"
  let ?g = "\<lambda>z. if z=a\<Uplus>b then Inl a else z"
  show "bij_betw ?f (elts (succ a \<Uplus> b)) (elts (succ (a \<Uplus> b)))"
    apply (rule bij_betw_byWitness [where f' = ?g], auto)
     apply (metis Inl_in_sum_iff mem_not_refl)
    by (metis Inr_in_sum_iff mem_not_refl)
qed

lemma cadd_succ: "succ m \<oplus> n = vcard (succ(m \<oplus> n))"
proof (unfold cadd_def)
  have [intro]: "elts (m \<Uplus> n) \<approx> elts (vcard (m \<Uplus> n))"
    using cardinal_eqpoll eqpoll_sym by blast
  have "vcard (succ m \<Uplus> n) = vcard (succ(m \<Uplus> n))"
    by (rule sum_succ_eqpoll [THEN cardinal_cong])
  also have "\<dots> = vcard (succ(vcard (m \<Uplus> n)))"
    by (blast intro: succ_eqpoll_cong cardinal_cong)
  finally show "vcard (succ m \<Uplus> n) = vcard (succ(vcard (m \<Uplus> n)))" .
qed

lemma nat_cadd_eq_add: "ord_of_nat m \<oplus> ord_of_nat n = ord_of_nat (m + n)"
proof (induct m)
  case (Suc m) thus ?case
    by (metis Card_def Card_ord_of_nat add_Suc cadd_succ ord_of_nat.simps(2))
qed auto

lemma vcard_disjoint_sup:
  assumes "x \<sqinter> y = 0" shows "vcard (x \<squnion> y) = vcard x \<oplus> vcard y"
proof -
  have "elts (x \<squnion> y) \<approx> elts (x \<Uplus> y)"
    unfolding eqpoll_def
  proof (rule exI)
    let ?f = "\<lambda>z. if z \<in> elts x then Inl z else Inr z"
    let ?g = "sum_case id id"
    show "bij_betw ?f (elts (x \<squnion> y)) (elts (x \<Uplus> y))"
      by (rule bij_betw_byWitness [where f' = ?g]) (use assms V_disjoint_iff in auto)
  qed
  then show ?thesis
    by (metis cadd_commute cadd_def cardinal_cong cardinal_idem vsum_0_eqpoll cadd_assoc)
qed

lemma vcard_sup: "vcard (x \<squnion> y) \<le> vcard x \<oplus> vcard y"
proof -
  have "elts (x \<squnion> y) \<lesssim> elts (x \<Uplus> y)"
    unfolding lepoll_def
  proof (intro exI conjI)
    let ?f = "\<lambda>z. if z \<in> elts x then Inl z else Inr z"
    show "inj_on ?f (elts (x \<squnion> y))"
      by (simp add: inj_on_def)
    show "?f ` elts (x \<squnion> y) \<subseteq> elts (x \<Uplus> y)"
      by force
  qed
  then show ?thesis
    using cadd_ac
    by (metis cadd_def cardinal_cong cardinal_idem lepoll_imp_Card_le vsum_0_eqpoll)
qed

subsection\<open>Infinite cardinals\<close>

definition InfCard :: "V\<Rightarrow>bool"
  where "InfCard \<kappa> \<equiv> Card \<kappa> \<and> \<omega> \<le> \<kappa>"

lemma InfCard_iff: "InfCard \<kappa> \<longleftrightarrow> Card \<kappa> \<and> infinite (elts \<kappa>)"
proof (cases "\<omega> \<le> \<kappa>")
  case True
  then show ?thesis
    using inj_ord_of_nat lepoll_def less_eq_V_def
    by (auto simp: InfCard_def \<omega>_def infinite_le_lepoll)
next
  case False
  then show ?thesis
    using Card_iff_initial InfCard_def infinite_Ord_omega by blast
qed

lemma InfCard_ge_ord_of_nat:
  assumes "InfCard \<kappa>" shows "ord_of_nat n \<le> \<kappa>"
  using InfCard_def assms ord_of_nat_le_omega by blast

lemma InfCard_not_0[iff]: "\<not> InfCard 0"
  by (simp add: InfCard_iff)

definition csucc :: "V\<Rightarrow>V"
  where "csucc \<kappa> \<equiv> LEAST \<kappa>'. Ord \<kappa>' \<and> (Card \<kappa>' \<and> \<kappa> < \<kappa>')"


lemma less_vcard_VPow: "vcard A < vcard (VPow A)"
proof (rule lesspoll_imp_Card_less)
  show "elts A \<prec> elts (VPow A)"
    by (simp add: elts_VPow down inj_on_def lesspoll_Pow_self)
qed

lemma greater_Card:
  assumes "Card \<kappa>" shows "\<kappa> < vcard (VPow \<kappa>)"
proof -
  have "\<kappa> = vcard \<kappa>"
    using Card_def assms by blast
  also have "\<dots> < vcard (VPow \<kappa>)"
  proof (rule lesspoll_imp_Card_less)
    show "elts \<kappa> \<prec> elts (VPow \<kappa>)"
      by (simp add: elts_VPow down inj_on_def lesspoll_Pow_self)
  qed
  finally show ?thesis .
qed

lemma
  assumes "Card \<kappa>"
  shows Card_csucc [simp]: "Card (csucc \<kappa>)" and less_csucc [simp]: "\<kappa> < csucc \<kappa>"
proof -
  have "Card (csucc \<kappa>) \<and> \<kappa> < csucc \<kappa>"
    unfolding csucc_def
  proof (rule Ord_LeastI2)
    show "Card (vcard (VPow \<kappa>)) \<and> \<kappa> < (vcard (VPow \<kappa>))"
      using Card_def assms greater_Card by auto
  qed auto
  then show "Card (csucc \<kappa>)" "\<kappa> < csucc \<kappa>"
    by auto
qed

lemma le_csucc:
  assumes "Card \<kappa>" shows "\<kappa> \<le> csucc \<kappa>"
  by (simp add: assms less_csucc less_imp_le)


lemma csucc_le: "\<lbrakk>Card \<mu>; \<kappa> \<in> elts \<mu>\<rbrakk> \<Longrightarrow> csucc \<kappa> \<le> \<mu>"
  unfolding csucc_def
  by (simp add: Card_is_Ord Ord_Least_le OrdmemD)

lemma finite_csucc: "a \<in> elts \<omega> \<Longrightarrow> csucc a = succ a"
  unfolding csucc_def
  proof (rule Least_equality)
  show "Ord (ZFC_in_HOL.succ a) \<and> Card (ZFC_in_HOL.succ a) \<and> a < ZFC_in_HOL.succ a"
    if "a \<in> elts \<omega>"
    using that by (auto simp: less_V_def less_eq_V_def nat_into_Card)
  show "ZFC_in_HOL.succ a \<le> y"
    if "a \<in> elts \<omega>"
      and "Ord y \<and> Card y \<and> a < y"
    for y :: V
    using that
    using Ord_mem_iff_lt dual_order.strict_implies_order by fastforce
qed

lemma Finite_imp_cardinal_cons [simp]:
  assumes FA: "finite A" and a: "a \<notin> A"
  shows "vcard (set (insert a A)) = csucc(vcard (set A))"
proof -
  show ?thesis
    unfolding csucc_def
  proof (rule Least_equality [THEN sym])
    have "small A"
      by (simp add: FA Finite_V)
    then have "\<not> elts (set A) \<approx> elts (set (insert a A))"
      using FA a eqpoll_imp_lepoll eqpoll_sym finite_insert_lepoll by fastforce
    then show "Ord (vcard (set (insert a A))) \<and> Card (vcard (set (insert a A))) \<and> vcard (set A) < vcard (set (insert a A))"
      by (simp add: Card_def lesspoll_imp_Card_less lesspoll_def subset_imp_lepoll subset_insertI)
    show "vcard (set (insert a A)) \<le> i"
      if "Ord i \<and> Card i \<and> vcard (set A) < i" for i
    proof -
      have "elts (vcard (set A)) \<approx> A"
        by (metis FA finite_imp_small cardinal_eqpoll elts_of_set)
      then have less: "A \<prec> elts i"
        using eq_lesspoll_trans eqpoll_sym lt_Card_imp_lesspoll that by blast
      show ?thesis
        using that less by (auto simp: less_imp_insert_lepoll lepoll_cardinal_le)
    qed
  qed
qed

lemma vcard_finite_set: "finite A \<Longrightarrow> vcard (set A) = ord_of_nat (card A)"
  by (induction A rule: finite_induct) (auto simp: set_empty \<omega>_def finite_csucc)

lemma lt_csucc_iff:
  assumes "Ord \<alpha>" "Card \<kappa>"
  shows "\<alpha> < csucc \<kappa> \<longleftrightarrow> vcard \<alpha> \<le> \<kappa>"
proof
  show "vcard \<alpha> \<le> \<kappa>" if "\<alpha> < csucc \<kappa>"
  proof -
    have "vcard \<alpha> \<le> csucc \<kappa>"
      by (meson \<open>Ord \<alpha>\<close> dual_order.trans lepoll_cardinal_le lepoll_refl less_le_not_le that)
    then show ?thesis
      by (metis (no_types) Card_def Card_iff_initial Ord_linear2 Ord_mem_iff_lt assms cardinal_eqpoll cardinal_idem csucc_le eq_iff eqpoll_sym that)
  qed
  show "\<alpha> < csucc \<kappa>" if "vcard \<alpha> \<le> \<kappa>"
  proof -
    have "\<not> csucc \<kappa> \<le> \<alpha>"
      using that
      by (metis Card_csucc Card_def assms(2) le_less_trans lepoll_imp_Card_le less_csucc less_eq_V_def less_le_not_le subset_imp_lepoll)
    then show ?thesis
      by (meson Card_csucc Card_is_Ord Ord_linear2 assms)
  qed
qed

lemma Card_lt_csucc_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> (\<kappa>' < csucc \<kappa>) = (\<kappa>' \<le> \<kappa>)"
  by (simp add: lt_csucc_iff Card_cardinal_eq Card_is_Ord)

lemma csucc_lt_csucc_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> (csucc \<kappa>' < csucc \<kappa>) = (\<kappa>' < \<kappa>)"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_less)

lemma csucc_le_csucc_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> (csucc \<kappa>' \<le> csucc \<kappa>) = (\<kappa>' \<le> \<kappa>)"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_less)

lemma csucc_0 [simp]: "csucc 0 = 1"
  by (simp add: finite_csucc one_V_def)

lemma Card_Un [simp,intro]:
  assumes "Card x" "Card y" shows "Card(x \<squnion> y)"
  by (metis Card_is_Ord Ord_linear_le assms sup.absorb2 sup.orderE)

lemma InfCard_csucc: "InfCard \<kappa> \<Longrightarrow> InfCard (csucc \<kappa>)"
  using InfCard_def le_csucc by auto

text\<open>Kunen's Lemma 10.11\<close>
lemma InfCard_is_Limit:
  assumes "InfCard \<kappa>" shows "Limit \<kappa>"
  proof (rule non_succ_LimitI)
  show "\<kappa> \<noteq> 0"
    using InfCard_def assms mem_not_refl by blast
  show "Ord \<kappa>"
    using Card_is_Ord InfCard_def assms by blast
  show "ZFC_in_HOL.succ y \<noteq> \<kappa>" for y
  proof
    assume "succ y = \<kappa>"
    then have "Card (succ y)"
      using InfCard_def assms by auto
    moreover have "\<omega> \<le> y"
      by (metis InfCard_iff Ord_in_Ord \<open>Ord \<kappa>\<close> \<open>ZFC_in_HOL.succ y = \<kappa>\<close> assms elts_succ finite_insert infinite_Ord_omega insertI1)
    moreover have "elts y \<approx> elts (succ y)"
      using InfCard_iff \<open>ZFC_in_HOL.succ y = \<kappa>\<close> assms eqpoll_sym infinite_insert_eqpoll by fastforce
    ultimately show False
      by (metis Card_iff_initial Ord_in_Ord OrdmemD elts_succ insertI1)
  qed
qed


subsection\<open>Toward's Kunen's Corollary 10.13 (1)\<close>

text\<open>Kunen's Theorem 10.12\<close>
lemma InfCard_csquare_eq:
  assumes "InfCard(\<kappa>)" shows "\<kappa> \<otimes> \<kappa> = \<kappa>"
  using infinite_times_eqpoll_self [of "elts \<kappa>"] assms
  unfolding InfCard_iff Card_def
  by (metis cardinal_cong cardinal_eqpoll cmult_def elts_vcard_VSigma_eqpoll eqpoll_trans)

lemma InfCard_le_cmult_eq:
  assumes "InfCard \<kappa>" "\<mu> \<le> \<kappa>" "\<mu> \<noteq> 0"
  shows "\<kappa> \<otimes> \<mu> = \<kappa>"
proof (rule order_antisym)
  have "\<kappa> \<otimes> \<mu> \<le> \<kappa> \<otimes> \<kappa>"
    by (simp add: assms(2) cmult_le_mono)
  also have "\<dots> \<le> \<kappa>"
    by (simp add: InfCard_csquare_eq assms(1))
  finally show "\<kappa> \<otimes> \<mu> \<le> \<kappa>" .
  show "\<kappa> \<le> \<kappa> \<otimes> \<mu>"
    using InfCard_def assms(1) assms(3) cmult_le_self by auto
qed

text\<open>Kunen's Corollary 10.13 (1), for cardinal multiplication\<close>
lemma InfCard_cmult_eq: "\<lbrakk>InfCard \<kappa>; InfCard \<mu>\<rbrakk> \<Longrightarrow> \<kappa> \<otimes> \<mu> = \<kappa> \<squnion> \<mu>"
  by (metis Card_is_Ord InfCard_def InfCard_le_cmult_eq Ord_linear_le cmult_commute inf_sup_aci(5) mem_not_refl sup.orderE sup_V_0_right zero_in_omega)

lemma cmult_succ:
  "succ(m) \<otimes> n = n \<oplus> (m \<otimes> n)"
  unfolding cmult_def cadd_def
proof (rule cardinal_cong)
  have "elts (vtimes (ZFC_in_HOL.succ m) n) \<approx> elts n <+> elts m \<times> elts n"
    by (simp add: elts_VSigma prod_insert_eqpoll)
  also have "\<dots> \<approx> elts (n \<Uplus> vcard (vtimes m n))"
    unfolding elts_VSigma elts_vsum Plus_def
  proof (rule Un_eqpoll_cong)
    show "(Sum_Type.Inr ` (elts m \<times> elts n)::(V + V \<times> V) set) \<approx> Inr ` elts (vcard (vtimes m n))"
      by (simp add: elts_vcard_VSigma_eqpoll eqpoll_sym)
  qed (auto simp: disjnt_def)
  finally show "elts (vtimes (ZFC_in_HOL.succ m) n) \<approx> elts (n \<Uplus> vcard (vtimes m n))" .
qed

lemma cmult_2:
  assumes "Card n" shows "ord_of_nat 2 \<otimes> n = n \<oplus> n"
proof -
  have "ord_of_nat 2 = succ (succ 0)"
    by force
  then show ?thesis
    by (simp add: cmult_succ assms)
qed

lemma InfCard_cdouble_eq:
  assumes "InfCard \<kappa>" shows "\<kappa> \<oplus> \<kappa> = \<kappa>"
proof -
  have "\<kappa> \<oplus> \<kappa> = \<kappa> \<otimes> ord_of_nat 2"
    using InfCard_def assms cmult_2 cmult_commute by auto
  also have "\<dots> = \<kappa>"
    by (simp add: InfCard_le_cmult_eq InfCard_ge_ord_of_nat assms)
  finally show ?thesis .
qed

text\<open>Corollary 10.13 (1), for cardinal addition\<close>
lemma InfCard_le_cadd_eq: "\<lbrakk>InfCard \<kappa>; \<mu> \<le> \<kappa>\<rbrakk> \<Longrightarrow> \<kappa> \<oplus> \<mu> = \<kappa>"
  by (metis InfCard_cdouble_eq InfCard_def antisym cadd_le_mono cadd_le_self)

lemma InfCard_cadd_eq: "\<lbrakk>InfCard \<kappa>; InfCard \<mu>\<rbrakk> \<Longrightarrow> \<kappa> \<oplus> \<mu> = \<kappa> \<squnion> \<mu>"
  by (metis Card_iff_initial InfCard_def InfCard_le_cadd_eq Ord_linear_le cadd_commute sup.absorb2 sup.orderE)

lemma csucc_le_Card_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> csucc \<kappa>' \<le> \<kappa> \<longleftrightarrow> \<kappa>' < \<kappa>"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_le)

lemma cadd_InfCard_le:
  assumes "\<alpha> \<le> \<kappa>" "\<beta> \<le> \<kappa>" "InfCard \<kappa>"
  shows "\<alpha> \<oplus> \<beta> \<le> \<kappa>"
  using assms by (metis InfCard_cdouble_eq cadd_le_mono)

lemma cmult_InfCard_le:
  assumes "\<alpha> \<le> \<kappa>" "\<beta> \<le> \<kappa>" "InfCard \<kappa>"
  shows "\<alpha> \<otimes> \<beta> \<le> \<kappa>"
  using assms
  by (metis InfCard_csquare_eq cmult_le_mono)

subsection \<open>The Aleph-seqence\<close>

text \<open>This is the well-known transfinite enumeration of the cardinal numbers.\<close>

definition Aleph :: "V \<Rightarrow> V"    (\<open>\<aleph>_\<close> [90] 90)
  where "Aleph \<equiv> transrec (\<lambda>f x. \<omega> \<squnion> \<Squnion>((\<lambda>y. csucc(f y)) ` elts x))"

lemma Aleph: "Aleph \<alpha> = \<omega> \<squnion> (\<Squnion>y\<in>elts \<alpha>. csucc (Aleph y))"
  by (simp add: Aleph_def transrec[of _ \<alpha>])

lemma InfCard_Aleph [simp, intro]: "InfCard(Aleph x)"
proof (induction x rule: eps_induct)
  case (step x)
  then show ?case
    by (simp add: Aleph [of x] InfCard_def Card_UN step)
qed

lemma Card_Aleph [simp, intro]: "Card(Aleph x)"
  using InfCard_def by auto

lemma Aleph_0 [simp]: "\<aleph>0 = \<omega>"
  by (simp add: Aleph [of 0])

lemma mem_Aleph_succ: "\<aleph>\<alpha> \<in> elts (Aleph (succ \<alpha>))"
  apply (simp add: Aleph [of "succ \<alpha>"])
  by (meson InfCard_Aleph Card_csucc Card_is_Ord InfCard_def Ord_mem_iff_lt less_csucc)

lemma Aleph_lt_succD [simp]: "\<aleph>\<alpha> < Aleph (succ \<alpha>)"
  by (simp add: InfCard_is_Limit Limit_is_Ord OrdmemD mem_Aleph_succ)

lemma Aleph_succ [simp]: "Aleph (succ x) = csucc (Aleph x)"
proof (rule antisym)
  show "Aleph (ZFC_in_HOL.succ x) \<le> csucc (Aleph x)"
    apply (simp add: Aleph [of "succ x"])
    by (metis Aleph InfCard_Aleph InfCard_def Sup_V_insert le_csucc le_sup_iff order_refl 
         replacement small_elts)
  show "csucc (Aleph x) \<le> Aleph (ZFC_in_HOL.succ x)"
    by (force simp add: Aleph [of "succ x"])
qed

lemma csucc_Aleph_le_Aleph: "\<alpha> \<in> elts \<beta> \<Longrightarrow> csucc (\<aleph>\<alpha>) \<le> \<aleph>\<beta>"
  by (metis Aleph ZFC_in_HOL.SUP_le_iff replacement small_elts sup_ge2)

lemma Aleph_in_Aleph: "\<alpha> \<in> elts \<beta> \<Longrightarrow> \<aleph>\<alpha> \<in> elts (\<aleph>\<beta>)"
  using csucc_Aleph_le_Aleph mem_Aleph_succ by auto

lemma Aleph_Limit:
  assumes "Limit \<gamma>"
  shows "Aleph \<gamma> = \<Squnion> (Aleph ` elts \<gamma>)"
proof -
  have [simp]: "\<gamma> \<noteq> 0"
    using assms by auto 
  show ?thesis
  proof (rule antisym)
    show "Aleph \<gamma> \<le> \<Squnion> (Aleph ` elts \<gamma>)"
      apply (simp add: Aleph [of \<gamma>])
      by (metis (mono_tags, lifting) Aleph_0 Aleph_succ Limit_def ZFC_in_HOL.SUP_le_iff 
           ZFC_in_HOL.Sup_upper assms imageI replacement small_elts)
    show "\<Squnion> (Aleph ` elts \<gamma>) \<le> Aleph \<gamma>"
      apply (simp add: cSup_le_iff)
      by (meson InfCard_Aleph InfCard_def csucc_Aleph_le_Aleph le_csucc order_trans)
  qed
qed

lemma Aleph_increasing:
  assumes ab: "\<alpha> < \<beta>" "Ord \<alpha>" "Ord \<beta>" shows "\<aleph>\<alpha> < \<aleph>\<beta>"
  by (meson Aleph_in_Aleph InfCard_Aleph Card_iff_initial InfCard_def Ord_mem_iff_lt assms)

lemma countable_iff_le_Aleph0: "countable (elts A) \<longleftrightarrow> vcard A \<le> \<aleph>0"
proof
  show "vcard A \<le> \<aleph>0"
    if "countable (elts A)"
  proof (cases "finite (elts A)")
    case True
    then show ?thesis
      using vcard_finite_set by fastforce
  next
    case False
    then have "elts \<omega> \<approx> elts A"
      using countableE_infinite [OF that]     
      by (simp add: eqpoll_def \<omega>_def) 
         (meson bij_betw_def bij_betw_inv bij_betw_trans inj_ord_of_nat)
    then show ?thesis
      using Card_\<omega> Card_def cardinal_cong vcard_def by auto
  qed
  show "countable (elts A)"
    if "vcard A \<le> Aleph 0"
  proof -
    have "elts A \<lesssim> elts \<omega>"
      using cardinal_le_lepoll [OF that] by simp
    then show ?thesis
      by (simp add: countable_iff_lepoll \<omega>_def inj_ord_of_nat)
  qed
qed

lemma Aleph_csquare_eq [simp]: "\<aleph>\<alpha> \<otimes> \<aleph>\<alpha> = \<aleph>\<alpha>"
  using InfCard_csquare_eq by auto

lemma vcard_Aleph [simp]: "vcard (\<aleph>\<alpha>) = \<aleph>\<alpha>"
  using Card_def InfCard_Aleph InfCard_def by auto

lemma omega_le_Aleph [simp]: "\<omega> \<le> \<aleph>\<alpha>"
  using InfCard_def by auto

lemma finite_iff_less_Aleph0: "finite (elts x) \<longleftrightarrow> vcard x < \<omega>"
proof
  show "finite (elts x) \<Longrightarrow> vcard x < \<omega>"
    by (metis Card_\<omega> Card_def finite_lesspoll_infinite infinite_\<omega> lesspoll_imp_Card_less)
  show "vcard x < \<omega> \<Longrightarrow> finite (elts x)"
    by (meson Ord_cardinal cardinal_eqpoll eqpoll_finite_iff infinite_Ord_omega less_le_not_le)
qed

lemma countable_iff_vcard_less1: "countable (elts x) \<longleftrightarrow> vcard x < \<aleph>1"
  by (simp add: countable_iff_le_Aleph0 lt_csucc_iff one_V_def)

lemma countable_infinite_vcard: "countable (elts x) \<and> infinite (elts x) \<longleftrightarrow> vcard x = \<aleph>0"
  by (metis Aleph_0 countable_iff_le_Aleph0 dual_order.refl finite_iff_less_Aleph0 less_V_def)

subsection \<open>The ordinal @{term "\<omega>1"}\<close>

abbreviation "\<omega>1 \<equiv> Aleph 1"

lemma Ord_\<omega>1 [simp]: "Ord \<omega>1"
  by (metis Ord_cardinal vcard_Aleph)

lemma omega_\<omega>1 [iff]: "\<omega> \<in> elts \<omega>1"
  by (metis Aleph_0 mem_Aleph_succ one_V_def)

lemma ord_of_nat_\<omega>1 [iff]: "ord_of_nat n \<in> elts \<omega>1"
  using Ord_\<omega>1 Ord_trans by blast

lemma countable_iff_less_\<omega>1:
  assumes "Ord \<alpha>"
  shows "countable (elts \<alpha>) \<longleftrightarrow> \<alpha> < \<omega>1"
  by (simp add: assms countable_iff_le_Aleph0 lt_csucc_iff one_V_def)

lemma less_\<omega>1_imp_countable:
  assumes "\<alpha> \<in> elts \<omega>1"
  shows "countable (elts \<alpha>)"
  using Ord_\<omega>1 Ord_in_Ord OrdmemD assms countable_iff_less_\<omega>1 by blast

lemma \<omega>1_gt0 [simp]: "\<omega>1 > 0"
  using Ord_\<omega>1 Ord_trans OrdmemD by blast

lemma \<omega>1_gt1 [simp]: "\<omega>1 > 1"
  using Ord_\<omega>1 OrdmemD \<omega>_gt1 less_trans by blast

lemma Limit_\<omega>1 [simp]: "Limit \<omega>1"
  by (simp add: InfCard_def InfCard_is_Limit le_csucc one_V_def)

end
