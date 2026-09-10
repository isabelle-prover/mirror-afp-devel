theory Semantics
  imports Syntax
begin

section \<open>Semantics: applicative structures, Henkin models and standard models\<close>

text \<open>The semantics in BKK's own layered terminology, in their order: @{emph \<open>applicative
  structures\<close>} \<open>(D, @)\<close> (BKK Definition 3.1), \<open>\<Sigma>\<close>-@{emph \<open>evaluations\<close>} \<open>J = (D, @, E)\<close>
  (BKK Definition 3.18) with an @{emph \<open>abstract\<close>} evaluation function subject to BKK's four
  conditions, \<open>\<Sigma>\<close>-@{emph \<open>valuations\<close>} and \<open>\<Sigma>\<close>-@{emph \<open>models\<close>} \<open>M = (D, @, E, \<upsilon>)\<close> (BKK
  Definitions 3.40 and 3.41), and the model class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (BKK Definition 3.49, the
  \<open>\<Sigma>\<close>-Henkin models of Definition 3.50).  The signature \<open>\<Sigma>\<close> is a static parameter of the
  whole development: the logical constants fixed by the term datatype plus the typed
  parameters drawn from \<open>'p\<close>, exactly as BKK fix \<open>\<Sigma>\<close> at the start of their Section 3.

  After the abstract notions, the recursive denotation \<open>\<lparr>t\<rparr>\<^bsub>\<xi>\<^esub>\<close> is introduced as the
  @{emph \<open>canonical construction\<close>} of an evaluation function over frame-like structures
  (BKK's \<open>\<Sigma>\<close>-evaluations over frames); it is the vehicle for building concrete models
  (the standard models here, and the term model of the completeness proof).\<close>

subsection \<open>Assignment update\<close>

text \<open>BKK's assignment update \<open>\<phi>,[a/X]\<close> (BKK Definition 3.17), written in
  function-update style with the variable's type subscripted: \<open>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<close>.\<close>

definition upd :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 'u \<Rightarrow> (nat \<Rightarrow> ty \<Rightarrow> 'u)"
  (\<open>_'(_\<^bsub>_\<^esub> := _')\<close> [1000, 0, 0, 0] 1000) where
  "\<xi>(x\<^bsub>\<sigma>\<^esub> := d) \<equiv> \<lambda>n \<tau>. if n = x \<and> \<tau> = \<sigma> then d else \<xi> n \<tau>"

lemma upd_same [simp]: "\<xi>(x\<^bsub>\<sigma>\<^esub> := d) x \<sigma> = d"  by (simp add: upd_def)
lemma upd_comm: "(x, \<sigma>) \<noteq> (w, \<tau>) \<Longrightarrow> (\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(w\<^bsub>\<tau>\<^esub> := e) = (\<xi>(w\<^bsub>\<tau>\<^esub> := e))(x\<^bsub>\<sigma>\<^esub> := d)"
  by (auto simp: upd_def fun_eq_iff)

subsection \<open>Applicative structures (BKK Definition 3.1)\<close>

text \<open>An applicative structure (BKK Definition 3.1) is a family of non-empty domains
  \<open>D\<^bsub>\<tau>\<^esub>\<close>, one per type, with an application operator.  By BKK's Currying remark
  (Remark 3.3) one binary operator suffices.  The point of the
  notion is its generality: a member of \<open>D\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>\<close> need not be a function, and distinct
  members may behave identically under application.  BKK's term structures
  (Example 3.8), with well-formed formulae as domains and syntactic application, are the
  guiding example --- their \<open>\<beta>\<eta>\<close>-quotient over a signature with a single constant even
  fails functionality (Remark 3.15) --- and the term model of the completeness proof
  below is such a quotient structure.  A @{emph \<open>frame\<close>} (Definition 3.4) is the
  set-theoretic special case in which the function domains consist of actual functions;
  every frame is @{emph \<open>functional\<close>}: members of \<open>D\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>\<close> that agree on all arguments
  are equal (Definition 3.5, Remark 3.6; property f of Definition 3.46).  Functionality
  is the one consequence of being a frame that the proofs use, so the model class below
  is delineated by it, and frames themselves are not needed.\<close>

locale app_struct = fixes Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
  assumes as_nonempty: "\<exists>a. Dm \<alpha> a" and as_appTy: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f \<Longrightarrow> Dm \<alpha> a \<Longrightarrow> Dm \<beta> (Ap f a)"
begin

text \<open>Variable assignments into the structure (BKK Definition 3.17).\<close>

definition asg :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> bool" where "asg \<xi> \<equiv> \<forall>n \<tau>. Dm \<tau> (\<xi> n \<tau>)"

lemma asg_upd: "asg \<xi> \<Longrightarrow> Dm \<sigma> d \<Longrightarrow> asg (\<xi>(x\<^bsub>\<sigma>\<^esub> := d))"
    by (auto simp: asg_def upd_def)

text \<open>Functionality: property f of BKK Definition 3.5.\<close>

definition functional :: bool where
  "functional \<equiv> \<forall>\<alpha> \<beta> f g. Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f \<longrightarrow> Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) g \<longrightarrow>
    (\<forall>a. Dm \<alpha> a  \<longrightarrow> Ap f a = Ap g a) \<longrightarrow> f = g"

end

subsection \<open>\<open>\<Sigma>\<close>-evaluations (BKK Definition 3.18)\<close>

text \<open>An evaluation function \<open>E\<close> maps assignments to typed functions from well-formed
  formulae into the domains, subject to BKK's four conditions: (1) it extends the
  assignment on variables, (2) it is homomorphic for application, (3) it depends only
  on the assignment's values at the free variables (coincidence), and (4) it respects
  \<open>\<beta>\<close>-conversion (BKK state this via \<open>\<beta>\<close>-normal forms; over our typed \<open>\<beta>\<close>-equality
  \<open>\<approx>\<^bsub>\<tau>\<^esub>\<close> of Section 1 the two formulations coincide, cf.\ BKK Remark 3.19).
  In addition \<open>E\<close> is typed: well-formed formulae of type \<open>\<tau>\<close> denote in \<open>D\<^bsub>\<tau>\<^esub>\<close>.\<close>

locale sigma_eval = app_struct Dm Ap for Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u" +
  fixes Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u"
  assumes ev_type: "wff\<^bsub>\<tau>\<^esub>(A) \<Longrightarrow> asg \<xi> \<Longrightarrow> Dm \<tau> (Ee \<xi> A)"
    and ev_var: "asg \<xi> \<Longrightarrow> Ee \<xi> (n\<^sup>f\<^bsub>\<sigma>\<^esub>) = \<xi> n \<sigma>"
    and ev_app: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(F) \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(A) \<Longrightarrow> asg \<xi> \<Longrightarrow> Ee \<xi> (F \<^bold>\<cdot> A) = Ap (Ee \<xi> F) (Ee \<xi> A)"
    and ev_coin: "wff\<^bsub>\<tau>\<^esub>(A) \<Longrightarrow> asg \<xi> \<Longrightarrow> asg \<xi>' \<Longrightarrow> (\<And>n \<sigma>. (n, \<sigma>) \<in> occ A \<Longrightarrow> \<xi> n \<sigma> = \<xi>' n \<sigma>)
                  \<Longrightarrow> Ee \<xi> A = Ee \<xi>' A"
    and ev_beta: "A \<approx>\<^bsub>\<tau>\<^esub> B \<Longrightarrow> asg \<xi> \<Longrightarrow> Ee \<xi> A = Ee \<xi> B"
begin

text \<open>The derived \<open>\<beta>\<close>-application law: the denotation of an abstraction is determined
  applicatively by the openings of its body (from conditions (1), (2), (4) and coincidence;
  the vehicle for all abstraction reasoning below).  In the sharpened form the fresh-name
  condition only concerns the typed occurrence \<open>(x, \<sigma>)\<close>, not the bare name (a name may
  occur at several types).\<close>

lemma ev_abs_app_occ:
  assumes wb: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and xi: "asg \<xi>"
    and x: "(x, \<sigma>) \<notin> occ b" and d: "Dm \<sigma> d"
  shows "Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
proof -
  let ?\<xi>' = "\<xi>(x\<^bsub>\<sigma>\<^esub> := d)"
  have xi': "asg ?\<xi>'" by (rule asg_upd[OF xi d])
  have coin: "Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) = Ee ?\<xi>' (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
    by (rule ev_coin[OF wb xi xi']) (use x in \<open>auto simp: upd_def\<close>)
  have "Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d = Ap (Ee ?\<xi>' (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) (Ee ?\<xi>' (x\<^sup>f\<^bsub>\<sigma>\<^esub>))"
    by (simp add: coin ev_var[OF xi'])
  also have "\<dots> = Ee ?\<xi>' ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> (x\<^sup>f\<^bsub>\<sigma>\<^esub>))"
    by (rule ev_app[OF wb wff_Fre xi', symmetric])
  also have "\<dots> = Ee ?\<xi>' (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    by (rule ev_beta[OF beta[OF wb wff_Fre] xi'])
  finally show ?thesis .
qed

lemma ev_abs_app:
  assumes wb: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and xi: "asg \<xi>" and x: "x \<notin> fvs b" and d: "Dm \<sigma> d"
  shows "Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
  by (metis d ev_abs_app_occ fst_conv fvs_eq_fst_occ image_eqI wb x xi)

end

subsection \<open>\<open>\<Sigma>\<close>-valuations and \<open>\<Sigma>\<close>-models (BKK Definitions 3.40 and 3.41)\<close>

text \<open>A \<open>\<Sigma>\<close>-valuation is a (total) function \<open>\<upsilon> : D\<^bsub>\<o>\<^esub> \<rightarrow> {T, F}\<close> --- rendered as a HOL
  predicate --- satisfying the properties \<open>L\<^sub>\<not>(E(\<not>))\<close>, \<open>L\<^sub>\<or>(E(\<or>))\<close> and \<open>L\<^sup>\<alpha>\<^sub>\<forall>(E(\<Pi>\<^sub>\<alpha>))\<close> of
  BKK's Figure 2.  A \<open>\<Sigma>\<close>-evaluation together with such a valuation is a \<open>\<Sigma>\<close>-model.
  Following BKK Definition 3.41 (and Remark 3.42) we include primitive equality
  \<open>L\<^sup>\<alpha>\<^sub>=(E(=\<^sub>\<alpha>))\<close>, and --- extending BKK Definition 3.41, whose \<open>\<Sigma>\<close>-models have no
  description operator --- a description property for \<open>E(\<iota>\<^sub>\<alpha>)\<close>, matching \<open>NK(\<iota>)\<close>.  Since the logical
  constants are closed, their denotations are assignment-independent (coincidence);
  we fix a canonical assignment to name them.\<close>

locale sigma_model = sigma_eval Dm Ap Ee for
  Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u" and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" +
  fixes vl :: "'u \<Rightarrow> bool" 
  assumes vl_neg: "asg \<xi> \<Longrightarrow> Dm \<o> a \<Longrightarrow> vl (Ap (Ee \<xi> Neg) a) \<longleftrightarrow> \<not> vl a"
      and vl_dis: "asg \<xi> \<Longrightarrow> Dm \<o> a \<Longrightarrow> Dm \<o> b \<Longrightarrow> vl (Ap (Ap (Ee \<xi> Dis) a) b) \<longleftrightarrow> vl a \<or> vl b"
      and vl_pi: "asg \<xi> \<Longrightarrow> Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f \<Longrightarrow>
                  vl (Ap (Ee \<xi> (Pi \<sigma>)) f) \<longleftrightarrow> (\<forall>d. Dm \<sigma> d \<longrightarrow> vl (Ap f d))"
      and vl_eq: "asg \<xi> \<Longrightarrow> Dm \<sigma> a \<Longrightarrow> Dm \<sigma> b \<Longrightarrow> vl (Ap (Ap (Ee \<xi> (Eq \<sigma>)) a) b) \<longleftrightarrow> a = b"
      and vl_iota: "asg \<xi> \<Longrightarrow> Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f \<Longrightarrow> Dm \<sigma> a \<Longrightarrow> (\<And>b. Dm \<sigma> b \<Longrightarrow> vl (Ap f b) \<longleftrightarrow> b = a)
                    \<Longrightarrow>  Ap (Ee \<xi> (Iota \<sigma>)) f = a"
begin

text \<open>Satisfaction and validity (BKK Definition 3.41): \<open>M \<Turnstile>\<^bsub>\<phi>\<^esub> A\<close> iff \<open>\<upsilon>(E\<^bsub>\<phi>\<^esub>(A)) \<equiv> T\<close>.\<close>

definition satisfies :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> bool"  (\<open>\<Turnstile>\<^bsub>_\<^esub> _\<close> [0, 40] 40) where
  "\<Turnstile>\<^bsub>\<xi>\<^esub> A \<equiv> vl (Ee \<xi> A)"
definition valid :: "'p tm \<Rightarrow> bool"  (\<open>\<Turnstile> _\<close> [40] 40) where
  "\<Turnstile> A \<equiv> \<forall>\<xi>. asg \<xi> \<longrightarrow> \<Turnstile>\<^bsub>\<xi>\<^esub> A"

end

subsection \<open>The model class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (BKK Definition 3.49)\<close>

text \<open>BKK's completeness class for \<open>NK\<close> is \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close>: \<open>\<Sigma>\<close>-models satisfying properties
  q, f and b (with primitive equality, property q holds automatically, BKK
  Definition 3.49 --- the q-witness at type \<open>\<alpha>\<close> is the denotation \<open>E(=\<^bsub>\<alpha>\<^esub>)\<close>,
  cf.\ the satisfaction lemma for Leibniz equality; with property b the
  valuation is two-valued on \<open>D\<^bsub>\<o>\<^esub>\<close>).  This class
  coincides with the \<open>\<Sigma>\<close>-Henkin models of BKK Definition 3.50 up to isomorphism
  (BKK Lemma 3.67 and Theorem 3.68).\<close>

locale bkk_model = sigma_model Dm Ap Ee vl
  for Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
  and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" and vl :: "'u \<Rightarrow> bool" +
  assumes prop_f: functional and prop_b: "Dm \<o> a \<Longrightarrow> Dm \<o> b \<Longrightarrow> vl a \<longleftrightarrow> vl b \<Longrightarrow> a = b"

subsection \<open>Truth values in a \<open>\<Sigma>\<close>-model (BKK Lemma 3.43)\<close>

context sigma_model
begin

text \<open>The canonical assignment, from non-emptiness of the domains.\<close>

definition xi0 :: "nat \<Rightarrow> ty \<Rightarrow> 'u" where "xi0 \<equiv> \<lambda>n \<tau>. SOME a. Dm \<tau> a"
lemma asg_xi0: "asg xi0" using as_nonempty by (auto simp: asg_def xi0_def intro: someI_ex)

text \<open>Closed terms evaluate independently of the assignment; the canonical assignment serves as
    the reference.\<close>
lemma Ee_closed: "wff\<^bsub>\<tau>\<^esub>(A) \<Longrightarrow> occ A = {} \<Longrightarrow> asg \<xi> \<Longrightarrow> Ee \<xi> A = Ee xi0 A"
  using ev_coin asg_xi0 by blast

text \<open>Evaluating \<open>\<^bold>\<bottom> = \<^bold>\<Pi>\<^bsub>\<o>\<^esub>(Bnd 0)\<close>: its truth means every boolean object is true.\<close>

lemma vl_FalseB: assumes xi: "asg \<xi>" shows "vl (Ee \<xi> \<^bold>\<bottom>) \<longleftrightarrow> (\<forall>d. Dm \<o> d \<longrightarrow> vl d)"
proof -
  have wI: "wff\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<o>\<^esub> (Bnd 0) :: 'p tm)"
    by (rule wff_AbsI) (simp add: wff_Fre)
  have e: "Ee \<xi> (\<^bold>\<bottom> :: 'p tm) = Ap (Ee \<xi> (Pi \<o>)) (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<o>\<^esub> (Bnd 0)))"
      by (metis FalseB_def Forall_def ev_app wI wff_Pi xi)
  have b: "Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<o>\<^esub> (Bnd 0))) d = d" if d: "Dm \<o> d" for d
      using asg_upd ev_abs_app ev_var that wI xi by auto
  show ?thesis unfolding e using vl_pi xi ev_type wI xi b by auto
qed

text \<open>BKK Lemma 3.43: \<open>\<upsilon>(E(\<^bold>\<top>)) \<equiv> T\<close> and \<open>\<upsilon>(E(\<^bold>\<bottom>)) \<equiv> F\<close>; in particular \<open>D\<^bsub>\<o>\<^esub>\<close> contains a
  true and a false object (BKK Remark 3.44).\<close>

lemma vl_TF: assumes xi: "asg \<xi>" shows "vl (Ee \<xi> \<^bold>\<top>) \<and> \<not> vl (Ee \<xi> \<^bold>\<bottom>)" 
  by (metis (mono_tags, lifting) TrueB_def sigma_eval.ev_app sigma_eval.ev_type
      sigma_eval_axioms vl_FalseB vl_neg wff_FalseB wff_Neg wff_TrueB xi)

end


subsection \<open>Model-relative truth and validity at a carrier\<close>

text \<open>Truth of \<open>A\<close> in a model \<open>\<langle>D,@,E,\<upsilon>\<rangle>\<close> under an assignment, and validity over
  @{emph \<open>all\<close>} models of the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> at a given value carrier \<open>'u\<close> --- the
  carrier appears explicitly in the notation \<open>\<Turnstile>('u) A\<close>.\<close>

definition rel_truth ::
  "((nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u) \<Rightarrow> ('u \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> bool"
  (\<open>\<langle>_,_\<rangle>,_ \<Turnstile> _\<close> [0, 0, 0, 61] 60) where
  "\<langle>Ee,vl\<rangle>,\<xi> \<Turnstile> A \<equiv> vl (Ee \<xi> A)"

definition bkk_valid :: "'u itself \<Rightarrow> 'p tm \<Rightarrow> bool" where
  "bkk_valid u A \<equiv> \<forall>Dm Ap Ee (vl :: 'u \<Rightarrow> bool) \<xi>.
    bkk_model Dm Ap Ee vl \<longrightarrow> app_struct.asg Dm \<xi> \<longrightarrow> \<langle>Ee,vl\<rangle>,\<xi> \<Turnstile> A"

syntax "_bkk_valid" :: "type \<Rightarrow> logic \<Rightarrow> logic"  (\<open>\<Turnstile>'(_') _\<close> [1000, 61] 60)
syntax_consts "_bkk_valid" == bkk_valid
translations "_bkk_valid t A" == "CONST bkk_valid (_TYPE t) A"

definition bkk_consequence :: "'u itself \<Rightarrow> 'p tm set \<Rightarrow> 'p tm \<Rightarrow> bool" where
  "bkk_consequence u \<Gamma> A \<equiv> \<forall>Dm Ap Ee (vl :: 'u \<Rightarrow> bool) \<xi>.
    bkk_model Dm Ap Ee vl \<longrightarrow> app_struct.asg Dm \<xi> \<longrightarrow>
    (\<forall> B \<in> \<Gamma> . wff \<o> B \<and> \<langle>Ee,vl\<rangle>,\<xi> \<Turnstile> B) \<longrightarrow> \<langle>Ee,vl\<rangle>,\<xi> \<Turnstile> A"

syntax "_bkk_consequence" :: "logic \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic"  (\<open>_ \<Turnstile>'(_') _\<close> [61, 1000, 61] 60)
syntax_consts "_bkk_consequence" == bkk_consequence
translations "_bkk_consequence \<Gamma> t A" == "CONST bkk_consequence (_TYPE t) \<Gamma> A"

text \<open>Note the well-formedness conjunct in the antecedent: a context containing an
  ill-formed member entails everything, vacuously.  This is deliberate --- the relation is
  only ever applied to well-formed contexts, and every exported theorem carries explicit
  \<open>wff\<close> hypotheses --- but it is worth stating.

  Consequence is monotone in the hypotheses: enlarging the context only narrows the
  models that must be checked.\<close>

lemma bkk_consequence_mono: "\<Gamma>0 \<Turnstile>('u) A \<Longrightarrow> \<Gamma>0 \<subseteq> \<Gamma> \<Longrightarrow> \<Gamma> \<Turnstile>('u) A"
  unfolding bkk_consequence_def by blast

subsection \<open>\<open>\<Sigma>\<close>-evaluations over frames: the canonical construction\<close>

text \<open>A @{emph \<open>frame signature\<close>} fixes the applicative structure (BKK Definition 3.1) and the
  denotation objects of the logical constants and parameters.  It carries no conditions; the
  denotation and its purely semantic properties (coincidence, BKK Definition 3.18(3)) live here.\<close>

locale frame_sig =
  fixes Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool"   (\<open>\<D>\<^bsub>_\<^esub>\<close>)
    and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"  (infixl \<open>\<^bold>@\<close> 200)
    and Lm :: "ty \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u" and Tv :: 'u  and Fv :: 'u
    and Ngv :: 'u  and Dsv :: 'u and Iv :: "ty \<Rightarrow> 'u"
    and Ev :: "ty \<Rightarrow> 'u" and Piv :: "ty \<Rightarrow> 'u" and Jv :: "'p \<Rightarrow> ty \<Rightarrow> 'u"
begin

text \<open>The denotation \<open>\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>\<close> of a term under an assignment \<open>\<xi>\<close> --- BKK's
  evaluation function (BKK Definition 3.18).\<close>

fun den :: "'p tm \<Rightarrow> (nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'u"  (\<open>\<lparr>_\<rparr>\<^bsub>_\<^esub>\<close> [0,0] 1000) where
    "\<lparr>Bnd i\<rparr>\<^bsub>\<xi>\<^esub> = Tv" \<comment> \<open>junk: no free bound index in a locally closed term\<close>
  | "\<lparr>n\<^sup>f\<^bsub>\<sigma>\<^esub>\<rparr>\<^bsub>\<xi>\<^esub> = \<xi> n \<sigma>"
  | "\<lparr>p\<^sup>p\<^bsub>\<sigma>\<^esub>\<rparr>\<^bsub>\<xi>\<^esub> = Jv p \<sigma>"
  | "\<lparr>Neg\<rparr>\<^bsub>\<xi>\<^esub> = Ngv"
  | "\<lparr>Dis\<rparr>\<^bsub>\<xi>\<^esub> = Dsv"
  | "\<lparr>Pi \<sigma>\<rparr>\<^bsub>\<xi>\<^esub> = Piv \<sigma>"
  | "\<lparr>Iota \<sigma>\<rparr>\<^bsub>\<xi>\<^esub> = Iv \<sigma>"
  | "\<lparr>s \<^bold>\<cdot> t\<rparr>\<^bsub>\<xi>\<^esub> = (\<lparr>s\<rparr>\<^bsub>\<xi>\<^esub>) \<^bold>@ (\<lparr>t\<rparr>\<^bsub>\<xi>\<^esub>)"
  | "\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> = Lm \<sigma> (\<lambda>d. \<lparr>b\<^bold>\<langle>(fresh (fvs b))\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>((fresh (fvs b))\<^bsub>\<sigma>\<^esub> := d)\<^esub>)"
  | "\<lparr>Eq \<sigma>\<rparr>\<^bsub>\<xi>\<^esub> = Ev \<sigma>"

text \<open>The recursive equations must be kept out of the default simpset: the \<open>Abs\<close> equation
  unfolds under a \<open>\<lambda>\<close> and would loop.\<close>

declare den.simps(8,9) [simp del]

text \<open>Coincidence (BKK Definition 3.18(3)): the denotation depends only on the assignment
  at the (typed) free occurrences.\<close>

lemma den_coincidence: "(\<And>n \<tau>. (n, \<tau>) \<in> occ t \<Longrightarrow> \<xi> n \<tau> = \<xi>' n \<tau>) \<Longrightarrow> \<lparr>t\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>t\<rparr>\<^bsub>\<xi>'\<^esub>"
proof (induct t arbitrary: \<xi> \<xi>' rule: size_induct)
  case (App s1 t1)
  hence "\<lparr>s1\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>s1\<rparr>\<^bsub>\<xi>'\<^esub>" using App by fastforce
  moreover have "\<lparr>t1\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>t1\<rparr>\<^bsub>\<xi>'\<^esub>"
    using App by fastforce
  ultimately show ?case
    by (simp add: den.simps(8))
next
  case (Abs \<sigma> b)
  let ?x = "fresh (fvs b)"
  have xnb: "?x \<notin> fvs b" by (rule fresh_notin) simp
  have "\<lparr>b\<^bold>\<langle>?x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(?x\<^bsub>\<sigma>\<^esub> := d)\<^esub> = \<lparr>b\<^bold>\<langle>?x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>'(?x\<^bsub>\<sigma>\<^esub> := d)\<^esub>" for d
    by (auto intro!: Abs)
       (smt (verit, best) Abs.prems Un_iff occ.simps(10,2) occ_opn prod.inject
                          singleton_iff subset_eq upd_def)
  thus ?case by (simp only: Abs den.simps(9))
qed auto

text \<open>\<open>\<alpha>\<close>-invariance: opening with either of two fresh free variables gives the same
  denotation.  This makes the fresh choice built into @{const den} irrelevant, and is the
  key to the substitution-value lemma below.  The abstraction case renames both internal
  fresh choices to a common fresh \<open>w\<close> (inner induction hypothesis), commutes the openings
  (@{thm opn_opn_comm}), then swaps the two names (outer induction hypothesis).\<close>

lemma den_rename: "x \<notin> fvs t \<Longrightarrow> y \<notin> fvs t \<Longrightarrow> \<lparr>opn k (x\<^sup>f\<^bsub>\<sigma>\<^esub>) t\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>
    = \<lparr>opn k (y\<^sup>f\<^bsub>\<sigma>\<^esub>) t\<rparr>\<^bsub>\<xi>(y\<^bsub>\<sigma>\<^esub> := d)\<^esub>"
proof (induction t arbitrary: k \<xi> x y \<sigma> d rule: size_induct)
  case (App s1 t1)
  hence "\<lparr>opn k (x\<^sup>f\<^bsub>\<sigma>\<^esub>) s1\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub> = \<lparr>opn k (y\<^sup>f\<^bsub>\<sigma>\<^esub>) s1\<rparr>\<^bsub>\<xi>(y\<^bsub>\<sigma>\<^esub> := d)\<^esub>" and
        "\<lparr>opn k (x\<^sup>f\<^bsub>\<sigma>\<^esub>) t1\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub> = \<lparr>opn k (y\<^sup>f\<^bsub>\<sigma>\<^esub>) t1\<rparr>\<^bsub>\<xi>(y\<^bsub>\<sigma>\<^esub> := d)\<^esub>"
    by auto
  thus ?case by (simp only: App opn.simps den.simps(8))
next
  case (Abs \<tau> c)
  define w where "w = fresh (fvs c \<union> {x, y})"
  have wc: "w \<notin> fvs c" and wx: "w \<noteq> x" and wy: "w \<noteq> y"
    using fresh_notin[of "fvs c \<union> {x, y}"] unfolding w_def by auto
  have xc: "x \<notin> fvs c" and yc: "y \<notin> fvs c" using Abs by auto
  let ?px = "fresh (fvs (opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>) c))"
  let ?py = "fresh (fvs (opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) c))"
  have pxf: "?px \<notin> fvs (opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>) c)"
    by (rule fresh_notin) simp
  have pyf: "?py \<notin> fvs (opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) c)"
    by (rule fresh_notin) simp
  have wnx: "w \<notin> fvs (opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>) c)"
    using wc wx fvs_opn[of "Suc k" "x\<^sup>f\<^bsub>\<sigma>\<^esub>" c] by auto
  have wny: "w \<notin> fvs (opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) c)"
    using wc wy fvs_opn[of "Suc k" "y\<^sup>f\<^bsub>\<sigma>\<^esub>" c] by auto
  have cw: "(opn (Suc k) (z\<^sup>f\<^bsub>\<sigma>\<^esub>) c)\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle> = opn (Suc k) (z\<^sup>f\<^bsub>\<sigma>\<^esub>) (c\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>)" for z
    by (rule opn_opn_comm) auto
  have "\<lparr>(opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>) c)\<^bold>\<langle>?px\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(?px\<^bsub>\<tau>\<^esub> := e)\<^esub>
        = \<lparr>(opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) c)\<^bold>\<langle>?py\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(y\<^bsub>\<sigma>\<^esub> := d))(?py\<^bsub>\<tau>\<^esub> := e)\<^esub>"
    for e
  proof -
    have "\<lparr>(opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>)
        c)\<^bold>\<langle>?px\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(?px\<^bsub>\<tau>\<^esub> := e)\<^esub>
        = \<lparr>(opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>) c)\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(w\<^bsub>\<tau>\<^esub> := e)\<^esub>"
      using Abs pxf wnx  by (metis nle_le size_opn_Fre)
    also have "\<dots> = \<lparr>opn (Suc k) (x\<^sup>f\<^bsub>\<sigma>\<^esub>) (c\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>)\<rparr>\<^bsub>(\<xi>(w\<^bsub>\<tau>\<^esub> := e))(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>"
      using wx by (simp add: cw upd_comm)
    also have "\<dots> = \<lparr>opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) (c\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>)\<rparr>\<^bsub>(\<xi>(w\<^bsub>\<tau>\<^esub> := e))(y\<^bsub>\<sigma>\<^esub> := d)\<^esub>"
      using Abs xc yc wc wx wy fvs_opn[of 0 "w\<^sup>f\<^bsub>\<tau>\<^esub>" c]
      by (smt (verit, best) Un_insert_right dual_order.refl fvs.simps(2) insertE size_opn_Fre
          subset_eq sup_bot.right_neutral)
    also have "\<dots> = \<lparr>(opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) c)\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(y\<^bsub>\<sigma>\<^esub> := d))(w\<^bsub>\<tau>\<^esub> := e)\<^esub>"
      using wy by (simp add: cw upd_comm)
    also have "\<dots> = \<lparr>(opn (Suc k) (y\<^sup>f\<^bsub>\<sigma>\<^esub>) c)\<^bold>\<langle>?py\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(y\<^bsub>\<sigma>\<^esub> := d))(?py\<^bsub>\<tau>\<^esub> := e)\<^esub>"
      using Abs pyf wny by (metis order_refl size_opn_Fre)
    finally show ?thesis.
  qed
  thus ?case using Abs by (simp add: den.simps(9))
qed(auto simp: upd_def)

text \<open>Any sufficiently fresh variable may be used to compute an abstraction's denotation.\<close>

lemma den_Abs: "x \<notin> fvs b \<Longrightarrow> \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> = Lm \<sigma> (\<lambda>d. \<lparr>b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>)"
  by (metis (no_types, lifting) ext den.simps(9) finite_fvs frame_sig.den_rename fresh_notin)

text \<open>The substitution-value lemma (BKK Lemma 3.20).\<close>

lemma den_fsub: "lc u \<Longrightarrow> \<lparr>fsub x \<sigma> u t\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>t\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>)\<^esub>"
proof (induction t arbitrary: \<xi> rule: size_induct)
  case (Fre n \<rho>) thus ?case by (auto simp: upd_def)
next
  case (App s1 t1)
  have "\<lparr>fsub x \<sigma> u s1\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>s1\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>)\<^esub>" and
       "\<lparr>fsub x \<sigma> u t1\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>t1\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>)\<^esub>"
    using App by auto
  thus ?case by (simp only: App fsub.simps den.simps(8))
next
  case (Abs \<tau> b)
  define w where "w = fresh (fvs b \<union> fvs u \<union> {x})"
  have wb: "w \<notin> fvs b" and wu: "w \<notin> fvs u" and wx: "w \<noteq> x"
      using fresh_notin[of "fvs b \<union> fvs u \<union> {x}"] unfolding w_def by auto
  have wfsb: "w \<notin> fvs (fsub x \<sigma> u b)"
      using wb wu fvs_fsub[of x \<sigma> u b] by auto
  have "\<lparr>fsub x \<sigma> u (\<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> b)\<rparr>\<^bsub>\<xi>\<^esub> = Lm \<tau> (\<lambda>d. \<lparr>(fsub x \<sigma> u
      b)\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(w\<^bsub>\<tau>\<^esub> := d)\<^esub>)"
    by (simp only: fsub.simps den_Abs[OF wfsb])
  also have "\<dots> = Lm \<tau> (\<lambda>d. \<lparr>fsub x \<sigma> u (b\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>)\<rparr>\<^bsub>\<xi>(w\<^bsub>\<tau>\<^esub> := d)\<^esub>)"
      using Abs wx by (simp add: fsub_opn)
  also have "\<dots> = Lm \<tau> (\<lambda>d. \<lparr>b\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(w\<^bsub>\<tau>\<^esub> := d))(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>(w\<^bsub>\<tau>\<^esub> := d)\<^esub>)\<^esub>)"
    using Abs by auto
  also have "\<dots> = Lm \<tau> (\<lambda>d. \<lparr>b\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>))(w\<^bsub>\<tau>\<^esub> := d)\<^esub>)"
  proof (rule arg_cong[where f = "Lm \<tau>"], rule ext)
    fix d
    have "\<lparr>u\<rparr>\<^bsub>\<xi>(w\<^bsub>\<tau>\<^esub> := d)\<^esub> = \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>"
      using den_coincidence wu fvs_eq_fst_occ
      by (smt (verit, ccfv_threshold) fst_conv image_eqI upd_def)
    thus "\<lparr>b\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(w\<^bsub>\<tau>\<^esub> := d))(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>(w\<^bsub>\<tau>\<^esub> := d)\<^esub>)\<^esub>
        = \<lparr>b\<^bold>\<langle>w\<^sup>f\<^bsub>\<tau>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>))(w\<^bsub>\<tau>\<^esub> := d)\<^esub>"
      using wx by (simp add: upd_comm)
  qed
  also have "\<dots> = \<lparr>\<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> b\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>)\<^esub>"
    by (rule den_Abs[OF wb, symmetric])
  finally show ?case unfolding Abs .
qed auto

text \<open>The \<open>\<beta>\<close> form of the substitution-value lemma (BKK Lemma 3.20): opening an
  abstraction body with a (locally closed) argument \<open>u\<close> is computed by evaluating the
  body under the assignment updated with the denotation of \<open>u\<close>.  This is the semantic
  counterpart of \<open>\<beta>\<close>-reduction and the workhorse of soundness.\<close>

lemma den_beta: assumes u: "lc u" and x: "x \<notin> fvs b"
  shows "\<lparr>b\<^bold>\<langle>u\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>u\<rparr>\<^bsub>\<xi>\<^esub>)\<^esub>"
  by (metis den_fsub fsub_intro u x)

end


text \<open>Satisfaction of the connectives (the \<open>\<Sigma>\<close>-valuation conditions of BKK
  Definition 3.41 and Figure 2; for the @{emph \<open>defined\<close>} connectives cf.\ BKK
  Remark 3.47 and Lemma 3.48): model-theoretic facts, stated here so that the
  calculus can use them for soundness.\<close>

context sigma_model
begin

lemma sat_Neg: assumes "wff\<^bsub>\<o>\<^esub>(A)" and "asg \<xi>"
  shows "vl (Ee \<xi> (\<^bold>\<not> A)) \<longleftrightarrow> \<not> vl (Ee \<xi> A)"
  using ev_app wff_Neg assms vl_neg ev_type by metis
lemma sat_Dis: assumes "wff\<^bsub>\<o>\<^esub>(A)" and "wff\<^bsub>\<o>\<^esub>(B)" and "asg \<xi>" 
  shows "vl (Ee \<xi> (A \<^bold>\<or> B)) \<longleftrightarrow> vl (Ee \<xi> A) \<or> vl (Ee \<xi> B)" 
  using ev_app wff_App wff_Dis assms vl_dis ev_type by (smt (verit, ccfv_SIG))
lemma sat_ImpB: assumes "wff\<^bsub>\<o>\<^esub>(A)" and "wff\<^bsub>\<o>\<^esub>(B)" and "asg \<xi>"
  shows "vl (Ee \<xi> (A \<^bold>\<supset> B)) \<longleftrightarrow> (vl (Ee \<xi> A) \<longrightarrow> vl (Ee \<xi> B))"
  unfolding ImpB_def using sat_Dis wff_Not assms sat_Neg by auto
lemma sat_Pi: assumes "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(G)" and "asg \<xi>" 
  shows "vl (Ee \<xi> (Pi \<sigma> \<^bold>\<cdot> G)) \<longleftrightarrow> (\<forall>d. Dm \<sigma> d \<longrightarrow> vl (Ap (Ee \<xi> G) d))"
  using ev_app wff_Pi assms vl_pi ev_type by metis
lemma sat_Forall: assumes wA: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and x: "x \<notin> fvs b" and xi: "asg \<xi>"
  shows "vl (Ee \<xi> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b)) \<longleftrightarrow> (\<forall>d. Dm \<sigma> d \<longrightarrow> vl (Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d))  (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)))"
  unfolding Forall_def using sat_Pi wA xi ev_abs_app x by auto

text \<open>Satisfaction of Leibniz equality (BKK Lemma 4.2): in a \<open>\<Sigma>\<close>-model with primitive
  equality, Leibniz equality holds exactly at identical denotations.\<close>

lemma sat_Leib: assumes wA: "wff\<^bsub>\<alpha>\<^esub>(A)" and wB: "wff\<^bsub>\<alpha>\<^esub>(B)" and xi: "asg \<xi>"
  shows "vl (Ee \<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)) \<longleftrightarrow> Ee \<xi> A = Ee \<xi> B"
proof -
  have lcA: "lc A" and lcB: "lc B" using wA wB by (auto intro: wff_lc)
  define p where "p = fresh (fvs A \<union> fvs B)"
  have p: "p \<notin> fvs A" "p \<notin> fvs B"
    unfolding p_def using fresh_notin[of "fvs A \<union> fvs B"] by auto
  let ?b = "(Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> B)"
  have wI: "wff\<^bsub>(\<alpha>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ?b)"
    by (smt (verit, del_insts) ImpB_def lcA lcB opn.simps(1,4,5,9) opn_lc wA wB
        wff_AbsI wff_App wff_Fre wff_ImpB)
  have pf: "p \<notin> fvs ?b" using p by (auto simp: ImpB_def)
  have unf: "vl (Ee \<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)) \<longleftrightarrow> (\<forall>r. Dm (\<alpha> \<^bold>\<Rightarrow> \<o>) r
      \<longrightarrow> (vl (Ap r (Ee \<xi> A)) \<longrightarrow> vl (Ap r (Ee \<xi> B))))"
  proof -
    have "vl (Ee (\<xi>(p\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> := r)) (?b\<^bold>\<langle>p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>\<^bold>\<rangle>))
        \<longleftrightarrow> (vl (Ap r (Ee \<xi> A)) \<longrightarrow> vl (Ap r (Ee \<xi> B)))"
      if r: "Dm (\<alpha> \<^bold>\<Rightarrow> \<o>) r" for r
    proof -
      let ?\<xi> = "\<xi>(p\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> := r)"
      have ob: "?b\<^bold>\<langle>p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>\<^bold>\<rangle> = (p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> A) \<^bold>\<supset> (p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> B)"
        by (simp add: opn_lc[OF lcA] opn_lc[OF lcB])
      have cA: "Ee ?\<xi> A = Ee \<xi> A"
        using p ev_coin[OF wA asg_upd[OF xi r] xi]
        unfolding upd_def fvs_eq_fst_occ image_iff by force
      have cB: "Ee ?\<xi> B = Ee \<xi> B"
        using p ev_coin[OF wB asg_upd[OF xi r] xi]
        unfolding upd_def fvs_eq_fst_occ image_iff by force
      show ?thesis unfolding ob
        by (smt (verit, del_insts) asg_upd cA cB ev_app ev_var sat_ImpB that upd_same wA wB
            wff_App wff_AppE wff_App_FreFre wff_FreE xi)
    qed
    thus ?thesis
      unfolding ev_beta[OF Leib_beq[OF wA wB] xi] sat_Forall[OF wI pf xi]
      by blast
  qed
  show ?thesis
  proof
    assume L: "vl (Ee \<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B))"
    let ?r = "Ap (Ee \<xi> (Eq \<alpha>)) (Ee \<xi> A)"
    have rA: "vl (Ap ?r (Ee \<xi> A))"
      using vl_eq[OF xi ev_type[OF wA xi] ev_type[OF wA xi]] by simp
    have "vl (Ap ?r (Ee \<xi> B))"
      using unf L as_appTy[OF ev_type[OF wff_Eq xi] ev_type[OF wA xi]] rA by blast
    thus "Ee \<xi> A = Ee \<xi> B"
      using vl_eq[OF xi ev_type[OF wA xi] ev_type[OF wB xi]] by simp
  qed(simp add: unf)
qed

end

subsection \<open>\<open>\<Sigma>\<close>-Henkin models: the general-model locale (BKK Definition 3.50)\<close>

text \<open>BKK's soundness and completeness theorems (BKK Theorem 7.3, Corollary 7.7) cover all
  eight model classes \<open>\<M>\<^sub>*\<close>; we instantiate the most specialised one, the
  class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> of @{emph \<open>\<open>\<Sigma>\<close>-Henkin models\<close>} (BKK Definition 3.50): \<open>\<Sigma>\<close>-models (BKK
  Definition 3.41) satisfying property b, property f (functionality), and property q (BKK
  Definitions 3.46 and 3.49).  Crucially the function domains need not be full (BKK
  Definition 3.5): following Henkin --- in BKK's words, it is sufficient to require that \<open>\<D>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>\<close>
  ``has enough members that any well-formed formula can be evaluated'' (BKK
  Section 2.3.1).  We therefore require the \<open>\<lambda>\<close>-conditions --- \<open>\<lambda>\<close>-comprehension \<open>gm_lamTy\<close> and
  the \<open>\<beta>\<close>-condition \<open>gm_beta\<close> of the \<open>\<Sigma>\<close>-evaluation (BKK Definition 3.18) --- only for the
  functions that are @{emph \<open>denotations of \<open>\<lambda>\<close>-terms\<close>}; equivalently, every wff denotes.
  A term model cannot be full: with property b the domain \<open>\<D>\<^bsub>\<iota>\<^bold>\<Rightarrow>\<o>\<^esub>\<close> of a full frame over
  infinite \<open>\<D>\<^bsub>\<iota>\<^esub>\<close> would be uncountable, whereas the term model over a countable signature
  is countable.
  (BKK avoid Andrews' term @{emph \<open>general models\<close>} for this notion; we keep it in the locale name
  \<open>general_model\<close>, in Andrews' sense.)  Standard models --- the full case, BKK
  Definition 3.51 --- appear at the end of this section as a sublocale.  Beyond BKK, the locale
  carries the description condition \<open>gm_descB\<close> for the typed description operators \<open>Iota \<sigma>\<close>
  (Andrews 1972, BKK's reference [3]), matched by the rule \<open>NK(\<iota>)\<close> of the calculus.

  Note that we render the applicative structure abstractly (an application operation \<open>\<^bold>@\<close> on a
  carrier \<open>'u\<close>) rather than literally over a frame of functions (BKK Definition 3.4); by
  functionality and BKK Theorem 3.68 the two presentations describe the same class of models
  up to isomorphism.\<close>


locale general_model = frame_sig +
  \<comment> \<open>property b (BKK Definition 3.46): \<open>\<D>\<^bsub>\<o>\<^esub> = {Tv, Fv}\<close>\<close>
  assumes gm_TF: "Tv \<noteq> Fv" and gm_boolean: "\<D>\<^bsub>\<o>\<^esub> a \<longleftrightarrow> a = Tv \<or> a = Fv"
    \<comment> \<open>application stays in the codomain, and the constants inhabit their domains\<close>
    and gm_appTy: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> f; \<D>\<^bsub>\<sigma>\<^esub> a\<rbrakk> \<Longrightarrow> \<D>\<^bsub>\<tau>\<^esub> (f \<^bold>@ a)"
    and gm_negTy: "\<D>\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub> Ngv" and gm_disTy: "\<D>\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^bold>\<Rightarrow>\<o>\<^esub> Dsv"
    and gm_piTy: "\<D>\<^bsub>(\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>\<^esub> (Piv \<sigma>)"
    and gm_iotaTy: "\<D>\<^bsub>(\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<sigma>\<^esub> (Iv \<sigma>)" and gm_parTy: "\<D>\<^bsub>\<sigma>\<^esub> (Jv p \<sigma>)"
    \<comment> \<open>\<open>\<Sigma>\<close>-valuation (BKK Figure 2 / Definition 3.41) with \<open>\<upsilon> = (\<lambda>a. a = Tv)\<close>\<close>
    and gm_negB: "\<D>\<^bsub>\<o>\<^esub> a \<Longrightarrow> (Ngv \<^bold>@ a = Tv) = (a \<noteq> Tv)"
    and gm_disB: "\<lbrakk>\<D>\<^bsub>\<o>\<^esub> a; \<D>\<^bsub>\<o>\<^esub> b\<rbrakk> \<Longrightarrow> (Dsv \<^bold>@ a \<^bold>@ b = Tv) = (a = Tv \<or> b = Tv)"
    and gm_piB: "\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub> f \<Longrightarrow> (Piv \<sigma> \<^bold>@ f = Tv) = (\<forall>d. \<D>\<^bsub>\<sigma>\<^esub> d \<longrightarrow> f \<^bold>@ d = Tv)"
\<comment> \<open>property f (functionality, BKK Definition 3.46) and property q (BKK Definitions 3.46 and
      3.49)\<close>
    and gm_funct: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> g; \<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> k; \<And>a. \<D>\<^bsub>\<sigma>\<^esub> a \<Longrightarrow> g \<^bold>@ a = k \<^bold>@ a\<rbrakk> \<Longrightarrow> g = k"
\<comment> \<open>primitive equality (BKK Remark 7.9): \<open>Ev \<sigma>\<close> satisfies \<open>L\<^sup>\<sigma>\<^bsub>=\<^esub>\<close> of BKK Figure 2; property q (BKK
    Definitions 3.46 and 3.49) follows with witness \<open>Ev \<sigma>\<close>\<close>
    and gm_eqTy: "\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub> (Ev \<sigma>)"
    and gm_eqB: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^esub> a; \<D>\<^bsub>\<sigma>\<^esub> b\<rbrakk> \<Longrightarrow> (Ev \<sigma> \<^bold>@ a \<^bold>@ b = Tv) = (a = b)"
\<comment> \<open>the description condition (beyond BKK, cf.\ Andrews 1972): if \<open>f\<close> behaves as the singleton
    \<open>{a}\<close>, description picks out \<open>a\<close>\<close>
    and gm_descB: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub> f; \<D>\<^bsub>\<sigma>\<^esub> a; \<forall>b. \<D>\<^bsub>\<sigma>\<^esub> b \<longrightarrow> (f \<^bold>@ b = Tv) = (b = a)\<rbrakk> \<Longrightarrow> Iv \<sigma> \<^bold>@ f = a"
\<comment> \<open>Henkin \<open>\<lambda>\<close>-conditions: \<open>\<lambda>\<close>-comprehension (the \<open>\<Sigma>\<close>-evaluation is total on wffs, BKK Definition
    3.18) and the \<open>\<beta>\<close>-condition (BKK Definition 3.18(4)), at the @{emph \<open>denotation\<close>} functions
    only\<close>
    and gm_lamTy: "\<lbrakk>wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd); \<forall>n \<rho>. \<D>\<^bsub>\<rho>\<^esub> (\<xi> n \<rho>)\<rbrakk> \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> (\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd\<rparr>\<^bsub>\<xi>\<^esub>)"
    and gm_beta: "\<lbrakk>wff\<^bsub>\<tau>\<^esub>(bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>); x \<notin> fvs bd; \<forall>n \<rho>. \<D>\<^bsub>\<rho>\<^esub> (\<xi> n \<rho>); \<D>\<^bsub>\<sigma>\<^esub> a\<rbrakk>
                   \<Longrightarrow> \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a = \<lparr>bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>"
begin

text \<open>Every domain is inhabited (part of BKK Definition 3.1) --- not an axiom: the parameter
  interpretation \<open>Jv\<close> already inhabits every domain.\<close>

lemma gm_nonempty: "\<exists>d. \<D>\<^bsub>\<sigma>\<^esub> d" using gm_parTy by blast

text \<open>An assignment is @{emph \<open>type-respecting\<close>} (@{term resp}) if it maps every typed variable
  into the matching domain --- BKK's assignment @{emph \<open>into\<close>} the structure.\<close>

definition resp where "resp \<xi> \<equiv> \<forall>n \<tau>. \<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>)"
lemma Tv_dom [simp]: "\<D>\<^bsub>\<o>\<^esub> Tv" and Fv_dom [simp]: "\<D>\<^bsub>\<o>\<^esub> Fv"
  using gm_boolean by auto

text \<open>Every well-formed term denotes in the domain of its type (BKK Definition 3.18): the
  \<open>\<lambda>\<close>-comprehension condition \<open>gm_lamTy\<close> is exactly what makes the abstraction case go through.\<close>

lemma den_dom: "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> resp \<xi> \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^esub> (\<lparr>t\<rparr>\<^bsub>\<xi>\<^esub>)"
proof (induction arbitrary: \<xi> rule: wff.induct)
  case wff_App thus ?case using den.simps(8) gm_appTy by fastforce
next
  case wff_Abs thus ?case using gm_lamTy resp_def wff.wff_Abs by blast
qed(auto simp: resp_def gm_parTy gm_negTy gm_disTy gm_piTy gm_iotaTy gm_eqTy)

text \<open>The semantic \<open>\<beta>\<close> rule at the term level (BKK Remark 3.19): applying an abstraction to a
  well-formed argument evaluates the opened body.\<close>

lemma den_App_Abs:
  assumes wb: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and wa: "wff\<^bsub>\<sigma>\<^esub>(a)" and r: "resp \<xi>"
  shows "\<lparr>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>b\<^bold>\<langle>a\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>\<^esub>" 
proof -
  define x where "x = fresh (fvs b)"
  have xb: "x \<notin> fvs b"
    using fresh_notin unfolding x_def by simp
  have da: "\<D>\<^bsub>\<sigma>\<^esub> (\<lparr>a\<rparr>\<^bsub>\<xi>\<^esub>)" using wa r by (rule den_dom)
  have "\<lparr>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ \<lparr>a\<rparr>\<^bsub>\<xi>\<^esub>" by (simp add: den.simps(8))
  also have "\<dots> = \<lparr>b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := \<lparr>a\<rparr>\<^bsub>\<xi>\<^esub>)\<^esub>"
    using da gm_beta r resp_def wff_Abs_open wb xb by blast
  also have "\<dots> = \<lparr>b\<^bold>\<langle>a\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>\<^esub>" using den_beta wff_lc wa xb by metis
  finally show ?thesis.
qed

text \<open>\<open>\<beta>\<close>-convertible terms denote the same object under any total assignment
  (BKK Remark 3.19); the abstraction-congruence case uses functionality (property f).\<close>

lemma beq_den: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> \<forall>n \<tau>. \<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>) \<Longrightarrow> \<lparr>s\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>t\<rparr>\<^bsub>\<xi>\<^esub>"
proof (induction arbitrary: \<xi> rule: beq.induct)
  case beta thus ?case using den_App_Abs resp_def by blast
next
  case (abs L b \<sigma> \<tau> b')
  define x where "x = fresh (L \<union> fvs b \<union> fvs b')"
  have xL: "x \<notin> L" and xb: "x \<notin> fvs b" and xb': "x \<notin> fvs b'"
    using fresh_notin[of "L \<union> fvs b \<union> fvs b'"] abs unfolding x_def by auto
  have wb: "wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" and wb': "wff\<^bsub>\<tau>\<^esub>(b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    using beq_wffL beq_wffR abs xL by blast+
  {
    fix a
    assume a: "\<D>\<^bsub>\<sigma>\<^esub> a"
    hence tot: "\<forall>n \<gamma>. \<D>\<^bsub>\<gamma>\<^esub> (\<xi>(x\<^bsub>\<sigma>\<^esub> := a) n \<gamma>)"
      using abs.prems by (auto simp: upd_def)
    have "\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a = \<lparr>b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>"
        by (rule gm_beta[OF wb xb abs.prems a])
    also have "\<dots> = \<lparr>b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>"
      using abs.IH[OF xL, of "\<xi>(x\<^bsub>\<sigma>\<^esub> := a)"] tot by blast
    also have "\<dots> = \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b'\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a"
      using gm_beta wb' xb' abs.prems a by simp
    finally have "\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a = \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b'\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a".
  }
  thus ?case
    using gm_funct gm_lamTy wff_Abs_open_rev wb xb abs.prems wb' xb' by blast
qed(auto simp: den.simps(8))

end

text \<open>Every \<open>\<Sigma>\<close>-Henkin general model --- the frame-based canonical construction --- is a
  BKK model: take \<open>E := den\<close> and \<open>\<upsilon> := (\<lambda>a. a = Tv)\<close>.  The four evaluation conditions are
  the denotation lemmas, and the \<open>L\<close>-properties are the \<open>gm\<close>-conditions.\<close>

sublocale general_model \<subseteq> bkkA: app_struct Dm Ap
  by unfold_locales (use gm_nonempty gm_appTy in blast)+

sublocale general_model \<subseteq> bkk: bkk_model Dm Ap "\<lambda>\<xi> A. \<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>" "\<lambda>a. a = Tv"
  by (unfold_locales;
      auto simp: bkkA.functional_def general_model_axioms[unfolded general_model_def]
                 bkkA.asg_def frame_sig.den.simps(8) resp_def
         intro: beq_den den_coincidence den_dom)

text \<open>Reusable satisfaction facts for the defined connectives and the named binders,
  holding in @{emph \<open>any\<close>} \<open>\<Sigma>\<close>-Henkin general model: they peel \<open>\<^bold>\<Pi>x\<^bsub>\<sigma>\<^esub>.\<close>, \<open>\<^bold>\<exists>x\<^bsub>\<sigma>\<^esub>.\<close> and
  the connectives down to the underlying domains, reducing satisfaction of a closed
  formula to a first-order statement about the carrier's domains --- the model-side
  counterparts of the syntactic derived rules in \<open>Calculus\<close>.\<close>

context general_model
begin

lemma sat_NegB:
  assumes "wff\<^bsub>\<o>\<^esub>(A)" and "bkkA.asg \<xi>"
  shows "(\<lparr>\<^bold>\<not> A\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> \<not> (\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub> = Tv)"
  using bkk.sat_Neg[OF assms] by simp

lemma sat_DisB:
  assumes "wff\<^bsub>\<o>\<^esub>(A)" and "wff\<^bsub>\<o>\<^esub>(B)" and "bkkA.asg \<xi>"
  shows "(\<lparr>A \<^bold>\<or> B\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> (\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<or> (\<lparr>B\<rparr>\<^bsub>\<xi>\<^esub> = Tv)"
  using bkk.sat_Dis[OF assms] by simp

lemma sat_ImpBB:
  assumes "wff\<^bsub>\<o>\<^esub>(A)" and "wff\<^bsub>\<o>\<^esub>(B)" and "bkkA.asg \<xi>"
  shows "(\<lparr>A \<^bold>\<supset> B\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> ((\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longrightarrow> (\<lparr>B\<rparr>\<^bsub>\<xi>\<^esub> = Tv))"
  using bkk.sat_ImpB[OF assms] by simp

lemma sat_AndB:
  assumes "wff\<^bsub>\<o>\<^esub>(A)" and "wff\<^bsub>\<o>\<^esub>(B)" and "bkkA.asg \<xi>"
  shows "(\<lparr>A \<^bold>\<and> B\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> (\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<and> (\<lparr>B\<rparr>\<^bsub>\<xi>\<^esub> = Tv)"
  unfolding AndB_def
  using sat_NegB[OF wff_Or[OF wff_Not[OF assms(1)] wff_Not[OF assms(2)]] assms(3)]
        sat_DisB[OF wff_Not[OF assms(1)] wff_Not[OF assms(2)] assms(3)]
        sat_NegB[OF assms(1) assms(3)] sat_NegB[OF assms(2) assms(3)]
  by blast

lemma sat_PEqB:
  assumes wa: "wff\<^bsub>\<sigma>\<^esub>(A)" and wb: "wff\<^bsub>\<sigma>\<^esub>(B)" and xi: "bkkA.asg \<xi>"
  shows "(\<lparr>A \<^bold>=\<^bsub>\<sigma>\<^esub> B\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> (\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>B\<rparr>\<^bsub>\<xi>\<^esub>)"
proof -
  have dA: "\<D>\<^bsub>\<sigma>\<^esub> (\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>)" using bkk.ev_type[OF wa xi] by simp
  have dB: "\<D>\<^bsub>\<sigma>\<^esub> (\<lparr>B\<rparr>\<^bsub>\<xi>\<^esub>)" using bkk.ev_type[OF wb xi] by simp
  have "\<lparr>A \<^bold>=\<^bsub>\<sigma>\<^esub> B\<rparr>\<^bsub>\<xi>\<^esub> = (Ev \<sigma>) \<^bold>@ (\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>) \<^bold>@ (\<lparr>B\<rparr>\<^bsub>\<xi>\<^esub>)"
    by (simp add: den.simps(8))
  thus ?thesis using bkk.vl_eq[OF xi dA dB] by simp
qed

text \<open>Peeling a defined quantifier down to the carrier.\<close>

lemma sat_AllN:
  assumes wb: "wff\<^bsub>\<o>\<^esub>(b)" and xi: "bkkA.asg \<xi>"
  shows "(\<lparr>\<^bold>\<Pi>v\<^bsub>\<sigma>\<^esub>. b\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> (\<forall>d. \<D>\<^bsub>\<sigma>\<^esub> d \<longrightarrow> \<lparr>b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv)"
proof -
  note lcb = wff_lc[OF wb]
  define x where "x = fresh (fvs b)"
  have xnb: "x \<notin> fvs b" unfolding x_def by (rule fresh_notin[OF finite_fvs])
  have wf: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (clos 0 v \<sigma> b))" by (rule wff_LamN_clos[OF wb])
  have xnc: "x \<notin> fvs (clos 0 v \<sigma> b)" using xnb fvs_clos[of 0 v \<sigma> b] by blast
  have sub: "(clos 0 v \<sigma> b)\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> = fsub v \<sigma> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) b"
    by (rule opn_clos_sub[OF opn_lc[OF lcb]])
  have ev: "\<lparr>(clos 0 v \<sigma> b)\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub> = \<lparr>b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub>" for d
  proof -
    have "\<lparr>(clos 0 v \<sigma> b)\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>
          = \<lparr>b\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(v\<^bsub>\<sigma>\<^esub> := \<lparr>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>)\<^esub>"
      by (simp only: sub den_fsub[OF lc_Fre])
    also have "\<dots> = \<lparr>b\<rparr>\<^bsub>(\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(v\<^bsub>\<sigma>\<^esub> := d)\<^esub>" by simp
    also have "\<dots> = \<lparr>b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub>"
    proof (rule den_coincidence)
      fix n \<tau> assume o: "(n, \<tau>) \<in> occ b"
      show "((\<xi>(x\<^bsub>\<sigma>\<^esub> := d))(v\<^bsub>\<sigma>\<^esub> := d)) n \<tau> = (\<xi>(v\<^bsub>\<sigma>\<^esub> := d)) n \<tau>"
      proof (cases "n = x \<and> \<tau> = \<sigma>")
        case True thus ?thesis using o xnb by (auto simp: fvs_eq_fst_occ image_iff)
      next
        case False thus ?thesis by (auto simp: upd_def)
      qed
    qed
    finally show ?thesis .
  qed
  have "(\<lparr>\<^bold>\<Pi>v\<^bsub>\<sigma>\<^esub>. b\<rparr>\<^bsub>\<xi>\<^esub> = Tv)
        = (\<forall>d. \<D>\<^bsub>\<sigma>\<^esub> d \<longrightarrow> \<lparr>(clos 0 v \<sigma> b)\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv)"
    unfolding AllN_def using bkk.sat_Forall[OF wf xnc xi] by simp
  thus ?thesis using ev by simp
qed

lemma sat_ExN:
  assumes wb: "wff\<^bsub>\<o>\<^esub>(b)" and xi: "bkkA.asg \<xi>"
  shows "(\<lparr>\<^bold>\<exists>v\<^bsub>\<sigma>\<^esub>. b\<rparr>\<^bsub>\<xi>\<^esub> = Tv) \<longleftrightarrow> (\<exists>d. \<D>\<^bsub>\<sigma>\<^esub> d \<and> \<lparr>b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv)"
proof -
  have e: "(\<^bold>\<exists>v\<^bsub>\<sigma>\<^esub>. b) = \<^bold>\<not> (\<^bold>\<Pi>v\<^bsub>\<sigma>\<^esub>. (\<^bold>\<not> b))"
    by (simp add: ExN_def AllN_def)
  have wnb: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<not> b)" using wb by (rule wff_Not)
  have wAll: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<Pi>v\<^bsub>\<sigma>\<^esub>. (\<^bold>\<not> b))" by (rule wff_AllN[OF wnb])
  have negd: "(\<lparr>\<^bold>\<not> b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv) = (\<not> (\<lparr>b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv))"
    if "\<D>\<^bsub>\<sigma>\<^esub> d" for d
    using sat_NegB[OF wb bkkA.asg_upd[OF xi that]] .
  have "(\<lparr>\<^bold>\<exists>v\<^bsub>\<sigma>\<^esub>. b\<rparr>\<^bsub>\<xi>\<^esub> = Tv) = (\<not> (\<lparr>\<^bold>\<Pi>v\<^bsub>\<sigma>\<^esub>. (\<^bold>\<not> b)\<rparr>\<^bsub>\<xi>\<^esub> = Tv))"
    unfolding e using sat_NegB[OF wAll xi] by simp
  also have "\<dots> = (\<not> (\<forall>d. \<D>\<^bsub>\<sigma>\<^esub> d \<longrightarrow> \<lparr>\<^bold>\<not> b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv))"
    using sat_AllN[OF wnb xi] by simp
  also have "\<dots> = (\<exists>d. \<D>\<^bsub>\<sigma>\<^esub> d \<and> \<lparr>b\<rparr>\<^bsub>\<xi>(v\<^bsub>\<sigma>\<^esub> := d)\<^esub> = Tv)"
    using negd by blast
  finally show ?thesis .
qed

end

subsection \<open>Substitution-value laws\<close>

text \<open>The substitution-value law for abstract \<open>\<Sigma>\<close>-evaluations (BKK Lemma 3.20 for a
  single free variable): substituting @{emph \<open>any\<close>} well-formed term equals updating
  the assignment with its value.\<close>

context sigma_eval
begin

lemma ev_fsub_one:
  assumes wA: "wff\<^bsub>\<tau>\<^esub>(A)" and wu: "wff\<^bsub>\<sigma>\<^esub>(u)" and xi: "asg \<xi>"
  shows "Ee \<xi> (fsub x \<sigma> u A) = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> u)) A"
proof -
  have opnA: "opn 0 v A = A" for v by (simp add: wff_lc[OF wA])
  let ?B = "clos 0 x \<sigma> A"
  have wAbs: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B)"
    by (rule wff_AbsI) (simp add: opn_clos_sub[OF opnA] wff_fsub[OF wA
        wff_Fre])
  have du: "Dm \<sigma> (Ee \<xi> u)" by (rule ev_type[OF wu xi])
  have "Ee \<xi> (fsub x \<sigma> u A) = Ee \<xi> ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B) \<^bold>\<cdot> u)"
    unfolding opn_clos_sub[OF opnA, symmetric]
    by (rule ev_beta[OF beq.sym[OF beq.beta[OF wAbs wu]] xi])
  also have "\<dots> = Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ?B)) (Ee \<xi> u)"
    by (rule ev_app[OF wAbs wu xi])
  also have "\<dots> = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> u)) (?B\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    by (rule ev_abs_app_occ[OF wAbs xi occ_clos du])
  also have "?B\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> = A"
    by (simp add: opn_clos_sub[OF opnA] fsub_id)
  finally show ?thesis .
qed

text \<open>The @{emph \<open>simultaneous\<close>} substitution-value law (the simultaneous form of BKK
  Lemma 3.20), for replacements that are closed wherever they act: evaluating
  \<open>msub \<rho> A\<close> equals evaluating \<open>A\<close> under the assignment that sends each variable to the
  value of its replacement.\<close>

lemma asg_msub:
  assumes xi: "asg \<xi>" and wr: "\<And>n \<tau>'. wff\<^bsub>\<tau>'\<^esub>(\<rho> n \<tau>')"
  shows "asg (\<lambda>n \<tau>'. Ee \<xi> (\<rho> n \<tau>'))"
  using ev_type[OF wr xi] by (auto simp: asg_def)

lemma ev_msub_aux:
  shows "card {q \<in> occ A. \<rho> (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>} \<le> m \<Longrightarrow>
    wff\<^bsub>\<tau>\<^esub>(A) \<Longrightarrow> asg \<xi> \<Longrightarrow> (\<And>n \<tau>'. wff\<^bsub>\<tau>'\<^esub>(\<rho> n \<tau>')) \<Longrightarrow>
    (\<And>n \<tau>'. \<rho> n \<tau>' \<noteq> n\<^sup>f\<^bsub>\<tau>'\<^esub> \<Longrightarrow> fvs (\<rho> n \<tau>') = {}) \<Longrightarrow>
    Ee \<xi> (msub \<rho> A) = Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho> n \<tau>')) A"
proof (induction m arbitrary: A \<rho>)
  case (0 A \<rho>)
  have fin: "finite {q \<in> occ A. \<rho> (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>}"
    by (rule finite_subset[OF _ finite_occ]) auto
  hence e: "{q \<in> occ A. \<rho> (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>} = {}"
    using 0(1) by simp
  have idA: "msub \<rho> A = A"
    by (subst msub_cong[where \<rho>' = "\<lambda>n \<tau>'. n\<^sup>f\<^bsub>\<tau>'\<^esub>"]) (use e in \<open>auto simp: msub_id\<close>)
  have "Ee \<xi> A = Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho> n \<tau>')) A"
    by (rule ev_coin[OF 0(2) 0(3) asg_msub[OF 0(3) 0(4)]])
       (use e ev_var[OF 0(3)] in fastforce)
  thus ?case by (simp add: idA)
next
  case (Suc m A \<rho>)
  show ?case
  proof (cases "{q \<in> occ A. \<rho> (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>} = {}")
    case True
    have idA: "msub \<rho> A = A"
      by (subst msub_cong[where \<rho>' = "\<lambda>n \<tau>'. n\<^sup>f\<^bsub>\<tau>'\<^esub>"]) (use True in \<open>auto simp: msub_id\<close>)
    have "Ee \<xi> A = Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho> n \<tau>')) A"
      by (rule ev_coin[OF Suc.prems(2) Suc.prems(3) asg_msub[OF Suc.prems(3) Suc.prems(4)]])
         (use True ev_var[OF Suc.prems(3)] in fastforce)
    thus ?thesis by (simp add: idA)
  next
    case False
    then obtain x \<sigma> where xs: "(x, \<sigma>) \<in> occ A" and ne: "\<rho> x \<sigma> \<noteq> x\<^sup>f\<^bsub>\<sigma>\<^esub>" by auto
    have cl: "fvs (\<rho> x \<sigma>) = {}" by (rule Suc.prems(5)[OF ne])
    have occu: "occ (\<rho> x \<sigma>) = {}" using cl by (simp add: fvs_eq_fst_occ)
    define A1 where "A1 = fsub x \<sigma> (\<rho> x \<sigma>) A"
    define \<rho>1 where "\<rho>1 = (\<lambda>n \<tau>'. if n = x \<and> \<tau>' = \<sigma> then n\<^sup>f\<^bsub>\<tau>'\<^esub> else \<rho> n \<tau>')"
    have wA1: "wff\<^bsub>\<tau>\<^esub>(A1)" unfolding A1_def by (rule wff_fsub[OF Suc.prems(2) Suc.prems(4)])
    have wr1: "wff\<^bsub>\<tau>'\<^esub>(\<rho>1 n \<tau>')" for n \<tau>'
      unfolding \<rho>1_def using Suc.prems(4) by (auto intro: wff_Fre)
    have cr1: "\<rho>1 n \<tau>' \<noteq> n\<^sup>f\<^bsub>\<tau>'\<^esub> \<Longrightarrow> fvs (\<rho>1 n \<tau>') = {}" for n \<tau>'
      unfolding \<rho>1_def using Suc.prems(5) by (auto split: if_splits)
    have step: "msub \<rho> A = msub \<rho>1 A1"
      unfolding A1_def \<rho>1_def by (rule msub_step[of \<rho> x \<sigma>]) (rule cl)
    have occA1: "occ A1 = occ A - {(x, \<sigma>)}"
      unfolding A1_def by (rule occ_fsub_closed[OF occu])
    have card1: "card {q \<in> occ A1. \<rho>1 (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>} \<le> m"
    proof -
      let ?S = "{q \<in> occ A. \<rho> (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>}"
      have finS: "finite ?S" by (rule finite_subset[OF _ finite_occ]) auto
      have mem: "(x, \<sigma>) \<in> ?S" using xs ne by simp
      have sub: "{q \<in> occ A1. \<rho>1 (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>} \<subseteq> ?S - {(x, \<sigma>)}"
        unfolding occA1 \<rho>1_def by (auto split: if_splits)
      have "card {q \<in> occ A1. \<rho>1 (fst q) (snd q) \<noteq> (fst q)\<^sup>f\<^bsub>snd q\<^esub>}
          \<le> card (?S - {(x, \<sigma>)})"
        by (rule card_mono[OF finite_Diff[OF finS] sub])
      also have "\<dots> = card ?S - 1" by (rule card_Diff_singleton[OF mem])
      also have "\<dots> \<le> m" using Suc.prems(1) by simp
      finally show ?thesis .
    qed
    have a1: "asg (\<lambda>n \<tau>'. Ee \<xi> (\<rho>1 n \<tau>'))" by (rule asg_msub[OF Suc.prems(3) wr1])
    have "Ee \<xi> (msub \<rho> A) = Ee \<xi> (msub \<rho>1 A1)" by (simp add: step)
    also have "\<dots> = Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho>1 n \<tau>')) A1"
      by (rule Suc.IH[OF card1 wA1 Suc.prems(3) wr1 cr1])
    also have "\<dots> = Ee ((\<lambda>n \<tau>'. Ee \<xi> (\<rho>1 n \<tau>'))(x\<^bsub>\<sigma>\<^esub> := Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho>1 n \<tau>')) (\<rho> x \<sigma>))) A"
      unfolding A1_def by (rule ev_fsub_one[OF Suc.prems(2) Suc.prems(4) a1])
    also have "Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho>1 n \<tau>')) (\<rho> x \<sigma>) = Ee \<xi> (\<rho> x \<sigma>)"
      by (rule ev_coin[OF Suc.prems(4) a1 Suc.prems(3)]) (simp add: occu)
    also have "(\<lambda>n \<tau>'. Ee \<xi> (\<rho>1 n \<tau>'))(x\<^bsub>\<sigma>\<^esub> := Ee \<xi> (\<rho> x \<sigma>))
        = (\<lambda>n \<tau>'. Ee \<xi> (\<rho> n \<tau>'))"
      unfolding \<rho>1_def by (auto simp: upd_def fun_eq_iff)
    finally show ?thesis .
  qed
qed

lemma ev_msub:
  assumes "wff\<^bsub>\<tau>\<^esub>(A)" and "asg \<xi>"
      and "\<And>n \<tau>'. wff\<^bsub>\<tau>'\<^esub>(\<rho> n \<tau>')"
      and "\<And>n \<tau>'. \<rho> n \<tau>' \<noteq> n\<^sup>f\<^bsub>\<tau>'\<^esub> \<Longrightarrow> fvs (\<rho> n \<tau>') = {}"
  shows "Ee \<xi> (msub \<rho> A) = Ee (\<lambda>n \<tau>'. Ee \<xi> (\<rho> n \<tau>')) A"
  by (rule ev_msub_aux[OF order_refl assms])

text \<open>The parameter-valued instance: the simultaneous closure \<open>vpar S \<pi>\<close> evaluates like
  the assignment that reads off the parameter values on \<open>S\<close>.\<close>

lemma ev_vpar:
  assumes wA: "wff\<^bsub>\<tau>\<^esub>(A)" and xi: "asg \<xi>"
  shows "Ee \<xi> (vpar S \<pi> A) = Ee (\<lambda>n \<sigma>. if (n, \<sigma>) \<in> S then Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>) else \<xi> n \<sigma>) A"
proof -
  have "Ee \<xi> (vpar S \<pi> A)
      = Ee (\<lambda>n \<sigma>. Ee \<xi> (if (n, \<sigma>) \<in> S then (\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub> else n\<^sup>f\<^bsub>\<sigma>\<^esub>)) A"
    unfolding vpar_def
    by (rule ev_msub[OF wA xi]) (auto intro: wff_Par wff_Fre split: if_splits)
  also have "(\<lambda>n \<sigma>. Ee \<xi> (if (n, \<sigma>) \<in> S then (\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub> else n\<^sup>f\<^bsub>\<sigma>\<^esub>))
      = (\<lambda>n \<sigma>. if (n, \<sigma>) \<in> S then Ee \<xi> ((\<pi> n \<sigma>)\<^sup>p\<^bsub>\<sigma>\<^esub>) else \<xi> n \<sigma>)"
    by (auto simp: fun_eq_iff ev_var[OF xi])
  finally show ?thesis .
qed

end

subsection \<open>The valuation locale\<close>

text \<open>The \<open>valuation\<close> locale axiomatises what a term model provides: a carrier \<open>'u\<close> with an
  application \<open>\<^bold>@\<close> and an evaluation \<open>\<V>\<close> of closed well-formed terms.  It abstracts the
  @{emph \<open>quotient\<close>} of BKK's term evaluation (BKK Definition 3.35) by Leibniz equality, as
  constructed in the model-existence proof (BKK Theorem 6.33) --- note that the bare term
  evaluation \<open>\<T>\<E>(\<Sigma>)\<^sup>\<beta>\<close> is @{emph \<open>not\<close>} functional (BKK Remark 3.37); functionality only holds
  after the quotient.  The axioms: \<open>v_app\<close>/\<open>v_beta\<close> are the evaluation conditions (BKK
  Definition 3.18(2),(4)); \<open>v_neg\<close>, \<open>v_dis\<close>, \<open>v_pi\<close> are \<open>L\<^bsub>\<not>\<^esub>\<close>, \<open>L\<^bsub>\<or>\<^esub>\<close>, \<open>L\<^sup>\<sigma>\<^bsub>\<forall>\<^esub>\<close> (BKK Figure 2);
  \<open>v_ext\<close> is functionality (property f), \<open>v_eq\<close> is primitive equality \<open>L\<^sup>\<sigma>\<^bsub>=\<^esub>\<close> (whence
  property q), \<open>v_desc\<close> the description condition, \<open>v_type\<close> type-disjointness of the
  domains, and \<open>v_TF\<close>/\<open>v_bool\<close> are property b (BKK Definition 3.46).\<close>

locale valuation =
  fixes Dv :: "ty \<Rightarrow> 'u \<Rightarrow> bool" (\<open>\<D>\<^bsub>_\<^esub>\<close>)
    and Vap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u" (infixl \<open>\<^bold>@\<close> 200)
    and Val :: "'p tm \<Rightarrow> 'u" (\<open>\<V>\<close>)
  assumes v_dom: "\<D>\<^bsub>\<sigma>\<^esub> d \<longleftrightarrow> (\<exists>t. cwff \<sigma> t \<and> d = \<V> t)"
      and v_app: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) s \<Longrightarrow> cwff \<sigma> t \<Longrightarrow> \<V> (s \<^bold>\<cdot> t) = \<V> s \<^bold>@ \<V> t"
      and v_beta: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> cwff \<sigma> a \<Longrightarrow> \<V> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>@ \<V> a = \<V> (b\<^bold>\<langle>a\<^bold>\<rangle>)"
      and v_TF: "\<V> \<^bold>\<top> \<noteq> \<V> \<^bold>\<bottom>"
      and v_bool: "cwff \<o> \<phi> \<Longrightarrow> \<V> \<phi> = \<V> \<^bold>\<top> \<or> \<V> \<phi> = \<V> \<^bold>\<bottom>"
      and v_neg: "cwff \<o> \<phi> \<Longrightarrow> \<V> (\<^bold>\<not> \<phi>) = (if \<V> \<phi> = \<V> \<^bold>\<top> then \<V> \<^bold>\<bottom> else \<V> \<^bold>\<top>)"
      and v_dis: "cwff \<o> \<phi> \<Longrightarrow> cwff \<o> \<psi> \<Longrightarrow>
                  \<V> (\<phi> \<^bold>\<or> \<psi>) = (if \<V> \<phi> = \<V> \<^bold>\<top> \<or> \<V> \<psi> = \<V> \<^bold>\<top> then \<V> \<^bold>\<top> else \<V> \<^bold>\<bottom>)"
      and v_pi: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f \<Longrightarrow> \<V> ((Pi \<sigma>) \<^bold>\<cdot> f) =
                 (if (\<forall>a. cwff \<sigma> a \<longrightarrow> \<V> f \<^bold>@ \<V> a  = \<V> \<^bold>\<top>) then \<V> \<^bold>\<top> else \<V> \<^bold>\<bottom>)"
      and v_ext: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) g \<Longrightarrow> cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) h
                  \<Longrightarrow> (\<And>a. cwff \<sigma> a \<Longrightarrow> \<V> g \<^bold>@ \<V> a = \<V> h \<^bold>@ \<V> a) \<Longrightarrow> \<V> g = \<V> h"
      and v_eq: "cwff \<sigma> a \<Longrightarrow> cwff \<sigma> b \<Longrightarrow> (\<V> (Eq \<sigma>) \<^bold>@ \<V> a \<^bold>@ \<V> b = \<V> \<^bold>\<top>) = (\<V> a = \<V> b)"
      and v_desc: "cwff (\<sigma>\<^bold>\<Rightarrow>\<o>) f \<Longrightarrow> cwff \<sigma> a
                    \<Longrightarrow> (\<forall>b. cwff \<sigma> b \<longrightarrow> (\<V> f \<^bold>@ \<V> b = \<V> \<^bold>\<top>) = (\<V> b = \<V> a))
                    \<Longrightarrow> \<V> ((Iota \<sigma>) \<^bold>\<cdot> f) = \<V> a"
      and v_type: "cwff \<sigma> s \<Longrightarrow> cwff \<tau> t \<Longrightarrow> \<V> s = \<V> t \<Longrightarrow> \<sigma> = \<tau>"
begin

lemma v_domI: "cwff \<sigma> t \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^esub> (\<V> t)" using v_dom by blast

end

subsection \<open>The term evaluation (BKK Section 6)\<close>

text \<open>A valuation extends to an evaluation function by simultaneous substitution of
  representatives: \<open>E\<^bsub>\<xi>\<^esub>(A) := \<V>([\<rho>\<^bsub>\<xi>\<^esub>]A)\<close>, BKK's evaluation for the term structure.
  \<open>\<beta>\<close>-respect is inherited from \<open>v_beta\<close> under closing substitutions, functionality is
  \<open>v_ext\<close>, and the remaining valuation conditions supply the \<open>L\<close>-properties --- so every
  valuation is directly a \<open>\<Sigma>\<close>-model in the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close>, with no detour through the
  recursive denotation.\<close>

context valuation
begin

definition vresp where "vresp \<xi> \<equiv> \<forall>n \<tau>. \<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>)"
definition rep_of where "rep_of \<xi> (n::nat) \<tau> = (SOME t. cwff \<tau> t \<and> \<xi> n \<tau> = \<V> t)"
lemma rep_of_spec:
  assumes "vresp \<xi>" shows "cwff \<tau> (rep_of \<xi> n \<tau>) \<and> \<xi> n \<tau> = \<V> (rep_of \<xi> n \<tau>)"
  by (smt (verit, del_insts) assms rep_of_def someI_ex v_dom valuation.vresp_def
      valuation_axioms)

text \<open>The valuation respects \<open>\<beta>\<close>-conversion under closing substitutions (BKK's quotient
  of the term structure by \<open>\<beta>\<close>, Section 6).\<close>

lemma beq_V: "s \<approx>\<^bsub>\<rho>'\<^esub> t \<Longrightarrow> (\<And>n \<tau>. cwff \<tau> (\<rho> n \<tau>)) \<Longrightarrow> \<V> (msub \<rho> s) = \<V> (msub \<rho> t)"
proof (induction arbitrary: \<rho> rule: beq.induct)
  case (beta \<sigma> \<rho>' b a)
  have lcr: "lc (\<rho> n \<tau>)" for n \<tau>
    using beta.prems by (auto intro: wff_lc cwff_wff)
  have cw1: "cwff (\<sigma>\<^bold>\<Rightarrow>\<rho>') (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b))"
    using cwff_msub[OF beta.hyps(1) beta.prems] by simp
  have "\<V> (msub \<rho> ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a)) = \<V> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b)) \<^bold>@ \<V> (msub \<rho> a)" 
    by (simp add: v_app[OF cw1 cwff_msub[OF beta.hyps(2) beta.prems]])
  also have "\<dots> = \<V> ((msub \<rho> b)\<^bold>\<langle>msub \<rho> a\<^bold>\<rangle>)"
    by (rule v_beta[OF cw1 cwff_msub[OF beta.hyps(2) beta.prems]])
  also have "\<dots> = \<V> (msub \<rho> (b\<^bold>\<langle>a\<^bold>\<rangle>))" by (simp add: msub_opn[OF lcr])
  finally show ?case.
next case (appL s \<sigma> \<rho>' s' t) thus ?case
  by (smt (verit, ccfv_SIG) beq_wff cwff_msub msub.simps(9) valuation.v_app valuation_axioms)
next case (appR t \<sigma> t' \<rho>' s) 
  have wt: "wff\<^bsub>\<sigma>\<^esub>(t)" and wt': "wff\<^bsub>\<sigma>\<^esub>(t')"
    using beq_wff[OF appR.hyps(1)] by auto
  thus ?case using appR cwff_msub by (metis msub.simps(9) v_app)
next case (abs L b \<sigma> \<tau> b')
  obtain x where x: "x \<notin> L \<union> fvs b \<union> fvs b'"
    by (meson abs.hyps(1) ex_new_if_finite finite_UnI finite_fvs infinite_UNIV_nat)
  have wb: "wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" and wb': "wff\<^bsub>\<tau>\<^esub>(b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    using beq_wff[OF abs.hyps(2)[of x]] x by auto
  have wA: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" using wff_Abs_open_rev[OF wb] x by auto
  have wA': "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b')" using wff_Abs_open_rev[OF wb'] x by auto
  have "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b))"
    using cwff_msub[OF wA abs.prems] by simp
  moreover have "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b'))"
    using cwff_msub[OF wA' abs.prems] by simp
  moreover have "\<V> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b)) \<^bold>@ \<V> a = \<V> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b')) \<^bold>@ \<V> a" if a: "cwff \<sigma> a" for a 
  proof -
    let ?\<rho> = "\<rho>(x := (\<rho> x)(\<sigma> := a))"
    have cr: "cwff \<tau>' (?\<rho> n \<tau>')" for n \<tau>' using abs.prems a by auto
    have lcr: "lc (?\<rho> n \<tau>')" for n \<tau>' using cr
      by (meson wff_lc cwff_wff)
    have mb: "msub ?\<rho> b = msub \<rho> b"
      using msub_cong x fvs_eq_fst_occ image_iff
      by (smt (verit, best) UnCI fst_conv fun_upd_other)
    have mb': "msub ?\<rho> b' = msub \<rho> b'"
      using msub_cong fvs_eq_fst_occ image_iff x
      by (smt (verit, ccfv_threshold) Un_iff fst_conv fun_upd_other)
    have e2: "msub ?\<rho> ((x\<^sup>f\<^bsub>\<sigma>\<^esub>) :: 'p tm) = a" by simp
    have ob: "msub ?\<rho> (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = (msub \<rho> b)\<^bold>\<langle>a\<^bold>\<rangle>"
      by (simp only: msub_opn[OF lcr] e2 mb)
    have ob': "msub ?\<rho> (b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = (msub \<rho> b')\<^bold>\<langle>a\<^bold>\<rangle>"
      by (simp only: msub_opn[OF lcr] e2 mb')
    have IH: "\<V> (msub ?\<rho> (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)) = \<V> (msub ?\<rho> (b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>))"
      by (rule abs.IH) (use x cr in auto)
    have "\<V> ((msub \<rho> b)\<^bold>\<langle>a\<^bold>\<rangle>) = \<V> ((msub \<rho> b')\<^bold>\<langle>a\<^bold>\<rangle>)" using IH
      by (simp only: ob ob')
    thus ?thesis using v_beta calculation a by simp
  qed
  ultimately show ?case using v_ext by simp
qed auto

text \<open>BKK's evaluation function for the term model.\<close>

definition Ev :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" where "Ev \<xi> A = \<V> (msub (rep_of \<xi>) A)"

end

text \<open>Every valuation is a \<open>\<Sigma>\<close>-model in the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (the direct construction of
  BKK Section 6).\<close>

sublocale valuation \<subseteq> bkkA: app_struct Dv Vap 
proof (unfold_locales, goal_cases)
  case 1 show ?case using v_domI[OF cwff_Par] by blast
next case 2 thus ?case  using cwff_App v_dom valuation.v_app
    valuation_axioms by fastforce 
qed

sublocale valuation \<subseteq> bkkM: bkk_model Dv Vap Ev "\<lambda>a. a = \<V> \<^bold>\<top>"
proof (unfold_locales, goal_cases)
  case 1 thus ?case
    by (metis Ev_def bkkA.asg_def cwff_msub rep_of_spec v_domI vresp_def)
next case 2 thus ?case
  using Ev_def bkkA.asg_def rep_of_spec vresp_def by (metis msub.simps(2))
next case 3 thus ?case
  by (metis Ev_def bkkA.asg_def cwff_msub msub.simps(9) rep_of_spec v_app vresp_def)
next case (4 \<tau> A \<xi> \<xi>') 
  hence "rep_of \<xi> n \<sigma> = rep_of \<xi>' n \<sigma>" if "(n, \<sigma>) \<in> occ A" for n \<sigma>
    using that by (auto simp: rep_of_def)
  thus ?case unfolding Ev_def by (simp cong: msub_cong)
next case 5 thus ?case using Ev_def beq_V bkkA.asg_def rep_of_spec vresp_def by metis
next case 6 thus ?case by (metis Ev_def cwff_Neg msub.simps(4) v_TF v_app v_dom v_neg)
next case (7 \<xi> a b) 
  then obtain \<phi> \<psi> where ab: "a = \<V> \<phi>" "b = \<V> \<psi>" and c: "cwff \<o> \<phi>" "cwff \<o> \<psi>"
    using v_dom by blast
  have e: "Ev \<xi> Dis = \<V> Dis" by (simp add: Ev_def)
  show ?case unfolding e ab using v_TF
    by (metis c(1,2) cwff_App cwff_Dis v_app v_dis)
next case (8 \<xi> \<sigma> f) 
  then obtain g where fg: "f = \<V> g" and cg: "cwff (\<sigma> \<^bold>\<Rightarrow> \<o>) g"
      using v_dom by blast
  have e: "Ev \<xi> (Pi \<sigma>) = \<V> (Pi \<sigma>)" by (simp add: Ev_def)
  have q: "(\<forall>d. \<D>\<^bsub>\<sigma>\<^esub> d \<longrightarrow> \<V> g \<^bold>@ d = \<V> \<^bold>\<top>) = (\<forall>a. cwff \<sigma> a \<longrightarrow> \<V> g \<^bold>@ \<V> a = \<V> \<^bold>\<top>)"
    using v_dom by metis
  show ?case unfolding e fg using v_TF
      by (auto simp: v_app[OF cwff_Pi cg, symmetric] v_pi[OF cg] q)
next case 9 thus ?case using Ev_def v_dom v_eq by fastforce
next case 10 thus ?case
  by (smt (verit, best) Ev_def cwff_Iota msub.simps(7) v_app v_desc v_dom)
next case 11 thus ?case by (smt (verit, ccfv_threshold) bkkA.functional_def v_dom v_ext)
next case 12 thus ?case by (metis v_bool v_dom)
qed

subsection \<open>Standard models (BKK Definition 3.51)\<close>

text \<open>A @{emph \<open>\<open>\<Sigma>\<close>-standard model\<close>} (BKK Definition 3.51) is a \<open>\<Sigma>\<close>-Henkin model over a
  @{emph \<open>full\<close>} frame (BKK Definition 3.5): every set-function between domains has a
  representative.  We record fullness by the universal abstraction laws \<open>Lm_dom\<close> and
  \<open>beta_Lm\<close>, quantified over @{emph \<open>all\<close>} functions \<open>h :: 'u \<Rightarrow> 'u\<close> --- strictly stronger
  than the Henkin conditions of @{locale general_model}.  On top of the full frame we assume
  the \<open>\<Sigma>\<close>-valuation conditions (BKK Definition 3.41, Figure 2) with property b, property f
  (functionality) and property q (BKK Definition 3.46).\<close>

locale standard_model = frame_sig +
  \<comment> \<open>fullness (BKK Definition 3.5): every function has a representative, \<open>\<^bold>@\<close> computes it\<close>
  assumes beta_Lm: "\<lbrakk>\<And>d. \<D>\<^bsub>\<sigma>\<^esub> d \<Longrightarrow> \<D>\<^bsub>\<tau>\<^esub> (h d); \<D>\<^bsub>\<sigma>\<^esub> a\<rbrakk> \<Longrightarrow> Lm \<sigma> h \<^bold>@ a = h a"
      and Lm_dom: "(\<And>d. \<D>\<^bsub>\<sigma>\<^esub> d \<Longrightarrow> \<D>\<^bsub>\<tau>\<^esub> (h d)) \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> (Lm \<sigma> h)"
      and Ap_dom: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> f; \<D>\<^bsub>\<sigma>\<^esub> a\<rbrakk> \<Longrightarrow> \<D>\<^bsub>\<tau>\<^esub> (f \<^bold>@ a)"
      \<comment> \<open>the logical constants and parameters inhabit their domains\<close>
      and Ngv_dom: "\<D>\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub> Ngv"
      and Dsv_dom: "\<D>\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^bold>\<Rightarrow>\<o>\<^esub> Dsv"
      and Piv_dom: "\<D>\<^bsub>(\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>\<^esub> (Piv \<sigma>)"
      and Iv_dom: "\<D>\<^bsub>(\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<sigma>\<^esub> (Iv \<sigma>)"
      and Ev_dom: "\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub> (Ev \<sigma>)" and Jv_dom: "\<D>\<^bsub>\<sigma>\<^esub> (Jv p \<sigma>)"
      \<comment> \<open>property b (BKK Definition 3.46): \<open>\<D>\<^bsub>\<o>\<^esub> = {Tv, Fv}\<close>\<close>
      and TF: "Tv \<noteq> Fv" and boolean: "\<D>\<^bsub>\<o>\<^esub> a \<longleftrightarrow> a = Tv \<or> a = Fv"
      \<comment> \<open>\<open>\<Sigma>\<close>-valuation (BKK Definition 3.41, Figure 2) with \<open>\<upsilon> = (\<lambda>a. a = Tv)\<close>\<close>
      and Lneg: "\<D>\<^bsub>\<o>\<^esub> a \<Longrightarrow> (Ngv \<^bold>@ a = Tv) = (a \<noteq> Tv)"
      and Ldis: "\<lbrakk>\<D>\<^bsub>\<o>\<^esub> a; \<D>\<^bsub>\<o>\<^esub> b\<rbrakk> \<Longrightarrow> (Dsv \<^bold>@ a \<^bold>@ b = Tv) = (a = Tv \<or> b = Tv)"
      and Lall: "\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub> f \<Longrightarrow> (Piv \<sigma> \<^bold>@ f = Tv) = (\<forall>d. \<D>\<^bsub>\<sigma>\<^esub> d \<longrightarrow> f \<^bold>@ d = Tv)"
      and Leq: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^esub> a; \<D>\<^bsub>\<sigma>\<^esub> b\<rbrakk> \<Longrightarrow> (Ev \<sigma> \<^bold>@ a \<^bold>@ b = Tv) = (a = b)"
      \<comment> \<open>properties f and q (BKK Definition 3.46)\<close>
      and funct: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> g; \<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> k; \<And>a. \<D>\<^bsub>\<sigma>\<^esub> a \<Longrightarrow> g \<^bold>@ a = k \<^bold>@ a\<rbrakk> \<Longrightarrow> g = k"
      \<comment> \<open>the description condition (beyond BKK, cf.\ Andrews 1972)\<close>
      and descB: "\<lbrakk>\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub> f; \<D>\<^bsub>\<sigma>\<^esub> a; \<forall>b. \<D>\<^bsub>\<sigma>\<^esub> b \<longrightarrow> (f \<^bold>@ b = Tv) = (b = a)\<rbrakk>
                  \<Longrightarrow> Iv \<sigma> \<^bold>@ f = a"
begin

text \<open>As in @{locale general_model}, membership of the truth values follows from property b.\<close>

lemma Tv_dom [simp]: "\<D>\<^bsub>\<o>\<^esub> Tv" and Fv_dom [simp]: "\<D>\<^bsub>\<o>\<^esub> Fv"
    by (simp_all add: boolean)

text \<open>In a full frame every domain is inhabited --- the interpretation \<open>Jv\<close> of a parameter
  provides a witness at every type.  BKK build non-emptiness into the applicative structure
  (BKK Definition 3.1).\<close>

lemma dom_nonempty: "\<exists>d. \<D>\<^bsub>\<tau>\<^esub> d" by (metis Jv_dom)

text \<open>In a full frame every well-formed term denotes in the domain of its type (the standard
  homomorphic construction, BKK Section 2.3.1).\<close>

lemma std_den_dom: "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> \<forall>n \<rho>. \<D>\<^bsub>\<rho>\<^esub> (\<xi> n \<rho>) \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^esub> (\<lparr>t\<rparr>\<^bsub>\<xi>\<^esub>)"
proof (induction arbitrary: \<xi> rule: wff.induct)
  case (wff_App \<sigma> \<tau> s t) thus ?case
    by (metis Ap_dom frame_sig.den.simps(8))
next
  case (wff_Abs L \<tau> b \<sigma>)
  define x where "x = fresh (L \<union> fvs b)"
  have xL: "x \<notin> L" and xb: "x \<notin> fvs b"
    using fresh_notin[of "L \<union> fvs b"] wff_Abs unfolding x_def by auto
  have "\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> (Lm \<sigma> (\<lambda>d. \<lparr>b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>))"
    by (simp add: Lm_dom upd_def wff_Abs.IH wff_Abs.prems xL)
  thus ?case by (simp add: den_Abs[OF xb])
qed (simp_all add: Jv_dom Ngv_dom Dsv_dom Piv_dom Iv_dom Ev_dom)

end

text \<open>Every standard model is a \<open>\<Sigma>\<close>-Henkin general model (BKK Definition 3.51 is a special
  case of Definition 3.50): the universal abstraction laws specialise to the denotation
  functions.\<close>

sublocale standard_model \<subseteq> general_model Dm Ap Lm Tv Fv Ngv Dsv Iv Ev Piv Jv
proof
  show "\<D>\<^bsub>\<o>\<^esub> a \<longleftrightarrow> a = Tv \<or> a = Fv" for a using boolean Tv_dom Fv_dom by blast
  show "\<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> g \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> k \<Longrightarrow> (\<And>a. \<D>\<^bsub>\<sigma>\<^esub> a \<Longrightarrow> g \<^bold>@ a = k \<^bold>@ a) \<Longrightarrow> g = k" for \<sigma> \<tau> g k
    by (rule funct)
  show "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd) \<Longrightarrow> \<forall>n \<rho>. \<D>\<^bsub>\<rho>\<^esub> (\<xi> n \<rho>) \<Longrightarrow> \<D>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> (\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd\<rparr>\<^bsub>\<xi>\<^esub>)" for \<sigma> \<tau> bd \<xi>
    using std_den_dom by blast
next
  fix \<tau> x \<sigma> and bd :: \<open>'b tm\<close> and \<xi> :: \<open>nat \<Rightarrow> ty \<Rightarrow> 'a\<close> and a
  assume wb: "wff\<^bsub>\<tau>\<^esub>(bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" and xb: "x \<notin> fvs bd"
      and r: "\<forall>n \<rho>. \<D>\<^bsub>\<rho>\<^esub> (\<xi> n \<rho>)" and da: "\<D>\<^bsub>\<sigma>\<^esub> a"
  have "\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd\<rparr>\<^bsub>\<xi>\<^esub> = Lm \<sigma> (\<lambda>d. \<lparr>bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>)"
      by (rule den_Abs[OF xb])
    moreover have "Lm \<sigma> (\<lambda>d. \<lparr>bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<^esub>) \<^bold>@ a = \<lparr>bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>"
      using r std_den_dom wb by (auto intro!: beta_Lm[where \<tau>=\<tau>, OF _ da] simp: upd_def)
  ultimately show \<open>\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> bd\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a = \<lparr>bd\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>\<close> by simp
qed(safe intro!: Lall Ldis Lneg Leq Jv_dom Ev_dom Iv_dom Piv_dom Dsv_dom Ngv_dom Ap_dom TF
                 descB dom_nonempty)

subsection \<open>Constructing the logical constants over a \<open>\<lambda>\<close>-universe\<close>

text \<open>A \<open>\<Sigma>\<close>-standard model need not be @{emph \<open>given\<close>} its logical constants: over any
  universe with full function spaces (\<open>\<beta>\<close>-abstraction with its typing, extensionality),
  booleans and a domain-respecting parameter interpretation, they can be
  @{emph \<open>constructed\<close>} --- negation, disjunction, quantification and equality by
  \<open>\<lambda>\<close>-abstraction over the domains, description by definite description (\<open>THE\<close>, not
  Hilbert choice).\<close>

locale lambda_universe =
  fixes Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and Lm :: "ty \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u" and Tv Fv :: 'u and Jv :: "'p \<Rightarrow> ty \<Rightarrow> 'u"
  assumes beta: "\<lbrakk>\<And>d. Dm \<sigma> d \<Longrightarrow> Dm \<tau> (h d); Dm \<sigma> a\<rbrakk> \<Longrightarrow> Ap (Lm \<sigma> h) a = h a"
    and Lm_dom: "(\<And>d. Dm \<sigma> d \<Longrightarrow> Dm \<tau> (h d)) \<Longrightarrow> Dm (\<sigma> \<^bold>\<Rightarrow> \<tau>) (Lm \<sigma> h)"
    and Ap_dom: "\<lbrakk>Dm (\<sigma> \<^bold>\<Rightarrow> \<tau>) f; Dm \<sigma> a\<rbrakk> \<Longrightarrow> Dm \<tau> (Ap f a)"
    and funct: "\<lbrakk>Dm (\<sigma> \<^bold>\<Rightarrow> \<tau>) g; Dm (\<sigma> \<^bold>\<Rightarrow> \<tau>) k; \<And>a. Dm \<sigma> a \<Longrightarrow> Ap g a = Ap k a\<rbrakk> \<Longrightarrow> g = k"
    and TF: "Tv \<noteq> Fv"
    and boolean: "Dm \<o> a \<longleftrightarrow> a = Tv \<or> a = Fv"
    and Jv_dom: "Dm \<sigma> (Jv p \<sigma>)"
begin

lemma bTv [simp]: "Dm \<o> Tv" and bFv [simp]: "Dm \<o> Fv" using boolean by auto

definition Ngv :: 'u where "Ngv = Lm \<o> (\<lambda>a. if a = Tv then Fv else Tv)"
definition Dsv :: 'u where
  "Dsv = Lm \<o> (\<lambda>a. Lm \<o> (\<lambda>b. if a = Tv \<or> b = Tv then Tv else Fv))"
definition Piv :: "ty \<Rightarrow> 'u" where
  "Piv \<sigma> = Lm (\<sigma> \<^bold>\<Rightarrow> \<o>) (\<lambda>f. if \<forall>d. Dm \<sigma> d \<longrightarrow> Ap f d = Tv then Tv else Fv)"
definition Ev :: "ty \<Rightarrow> 'u" where
  "Ev \<sigma> = Lm \<sigma> (\<lambda>a. Lm \<sigma> (\<lambda>b. if a = b then Tv else Fv))"
definition Iv :: "ty \<Rightarrow> 'u" where
  "Iv \<sigma> = Lm (\<sigma> \<^bold>\<Rightarrow> \<o>)
     (\<lambda>f. if \<exists>a. Dm \<sigma> a \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a))
          then THE a. Dm \<sigma> a \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a))
          else Jv undefined \<sigma>)"

lemma Ngv_dom: "Dm (\<o> \<^bold>\<Rightarrow> \<o>) Ngv" unfolding Ngv_def by (rule Lm_dom) simp
lemma Dsv_dom: "Dm (\<o> \<^bold>\<Rightarrow> \<o> \<^bold>\<Rightarrow> \<o>) Dsv" unfolding Dsv_def by (intro Lm_dom) simp
lemma Piv_dom: "Dm ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>) (Piv \<sigma>)" unfolding Piv_def by (rule Lm_dom) simp
lemma Ev_dom: "Dm (\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>) (Ev \<sigma>)" unfolding Ev_def by (intro Lm_dom) simp

lemma Ngv_app: "Dm \<o> a \<Longrightarrow> Ap Ngv a = (if a = Tv then Fv else Tv)"
  unfolding Ngv_def by (rule beta[where \<tau> = \<o>]) simp_all
lemma Piv_app: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f \<Longrightarrow> Ap (Piv \<sigma>) f = (if \<forall>d. Dm \<sigma> d \<longrightarrow> Ap f d = Tv then Tv else Fv)"
  unfolding Piv_def by (rule beta[where \<tau> = \<o>]) simp_all
lemma Dsv_app: "\<lbrakk>Dm \<o> a; Dm \<o> b\<rbrakk> \<Longrightarrow> Ap (Ap Dsv a) b = (if a = Tv \<or> b = Tv then Tv else Fv)"
proof -
  assume a: "Dm \<o> a" and b: "Dm \<o> b"
  have "Ap Dsv a = Lm \<o> (\<lambda>b. if a = Tv \<or> b = Tv then Tv else Fv)"
    unfolding Dsv_def by (auto intro!: beta[where \<tau> = "\<o> \<^bold>\<Rightarrow> \<o>", OF _ a] Lm_dom)
  moreover have "Ap (Lm \<o> (\<lambda>b. if a = Tv \<or> b = Tv then Tv else Fv)) b
               = (if a = Tv \<or> b = Tv then Tv else Fv)"
    by (rule beta[where \<tau> = \<o>, OF _ b]) simp
  ultimately show ?thesis by simp
qed
lemma Ev_app: "\<lbrakk>Dm \<sigma> a; Dm \<sigma> b\<rbrakk> \<Longrightarrow> Ap (Ap (Ev \<sigma>) a) b = (if a = b then Tv else Fv)"
proof -
  assume a: "Dm \<sigma> a" and b: "Dm \<sigma> b"
  have "Ap (Ev \<sigma>) a = Lm \<sigma> (\<lambda>b. if a = b then Tv else Fv)"
    unfolding Ev_def by (auto intro!: beta[where \<tau> = "\<sigma> \<^bold>\<Rightarrow> \<o>", OF _ a] Lm_dom)
  moreover have "Ap (Lm \<sigma> (\<lambda>b. if a = b then Tv else Fv)) b = (if a = b then Tv else Fv)"
    by (rule beta[where \<tau> = \<o>, OF _ b]) simp
  ultimately show ?thesis by simp
qed

lemma Iv_body_dom: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f \<Longrightarrow>
    Dm \<sigma> (if \<exists>a. Dm \<sigma> a \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a))
            then THE a. Dm \<sigma> a \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a))
            else Jv undefined \<sigma>)"
  by (smt (verit, ccfv_SIG) Jv_dom Uniq_I the1_equality')

lemma Iv_dom: "Dm ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>) (Iv \<sigma>)"
  unfolding Iv_def by (rule Lm_dom) (rule Iv_body_dom)

lemma Iv_app_desc:
  assumes f: "Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f" and a: "Dm \<sigma> a"
    and s: "\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a)"
  shows "Ap (Iv \<sigma>) f = a"
proof -
  have "(THE a'. Dm \<sigma> a' \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a'))) = a"
    using a s by auto
  moreover have "Ap (Iv \<sigma>) f
      = (if \<exists>a'. Dm \<sigma> a' \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a'))
         then THE a'. Dm \<sigma> a' \<and> (\<forall>b. Dm \<sigma> b \<longrightarrow> (Ap f b = Tv) = (b = a'))
         else Jv undefined \<sigma>)"
    unfolding Iv_def by (rule beta[OF Iv_body_dom f])
  ultimately show ?thesis
    by (metis a s)
qed

theorem is_standard_model: "standard_model Dm Ap Lm Tv Fv Ngv Dsv Iv Ev Piv Jv"
proof unfold_locales
  show "\<And>a. Dm \<o> a \<Longrightarrow> (Ap Ngv a = Tv) = (a \<noteq> Tv)"
    using Ngv_app TF by auto
  show "\<And>a b. Dm \<o> a \<Longrightarrow> Dm \<o> b \<Longrightarrow> (Ap (Ap Dsv a) b = Tv) = (a = Tv \<or> b = Tv)"
    using Dsv_app TF by auto
  show "\<And>\<sigma> f. Dm (\<sigma> \<^bold>\<Rightarrow> \<o>) f \<Longrightarrow> (Ap (Piv \<sigma>) f = Tv) = (\<forall>d. Dm \<sigma> d \<longrightarrow> Ap f d = Tv)"
    using Piv_app TF by auto
  show "\<And>\<sigma> a b. Dm \<sigma> a \<Longrightarrow> Dm \<sigma> b \<Longrightarrow> (Ap (Ap (Ev \<sigma>) a) b = Tv) = (a = b)"
    using Ev_app TF by auto
qed(auto intro: Iv_app_desc funct Jv_dom Ev_dom Iv_dom Piv_dom Lm_dom Ap_dom
                beta Ngv_dom Dsv_dom
         simp: TF boolean)

end

end
