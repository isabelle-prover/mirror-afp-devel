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
  (the standard models here, and the term model of the completeness proof in Section 3).\<close>

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

text \<open>A typed collection of non-empty domains with an application operator.  BKK's
  typing discipline \<open>@ : D\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<times> D\<^bsub>\<alpha>\<^esub> \<rightarrow> D\<^bsub>\<beta>\<^esub>\<close> becomes a closure condition on the
  one abstract operator.  BKK's @{emph \<open>frames\<close>} (Definition 3.4, \<open>D\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<subseteq> F(D\<^bsub>\<alpha>\<^esub>; D\<^bsub>\<beta>\<^esub>)\<close>)
  are a set-theoretic notion with no direct analogue over an abstract carrier; by BKK
  Remark 3.6 every frame is functional, and it is @{emph \<open>functionality\<close>} (BKK
  Definition 3.5; named property f in Definition 3.46) that all mathematical arguments consume, so
      the model class below
  is delineated by functionality.\<close>

locale app_struct = fixes Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
  assumes as_nonempty: "\<exists>a. Dm \<alpha> a" and as_appTy: "Dm (\<alpha> \<^bold>\<Rightarrow> \<beta>) f \<Longrightarrow> Dm \<alpha> a \<Longrightarrow> Dm \<beta> (Ap f a)"
begin

text \<open>Variable assignments into the structure (BKK Definition 3.17); the update \<open>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<close> is
    BKK's \<open>\<phi>,[d/X]\<close>.\<close>

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
    applicatively by the openings of 
  its body (from conditions (1), (2), (4) and coincidence; the vehicle
      for all abstraction reasoning below).\<close>

lemma ev_abs_app:
  assumes wb: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and xi: "asg \<xi>" and x: "x \<notin> fvs b" and d: "Dm \<sigma> d"
  shows "Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d = Ee (\<xi>(x\<^bsub>\<sigma>\<^esub> := d)) (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" 
  by (smt (verit, del_insts) asg_upd beta d fvs.simps(10) fvs_eq_fst_occ image_eqI prod.sel(1)
      sigma_eval.ev_app sigma_eval.ev_beta sigma_eval.ev_coin sigma_eval.ev_var sigma_eval_axioms
      upd_def wb wff_Fre x xi)

end

subsection \<open>\<open>\<Sigma>\<close>-valuations and \<open>\<Sigma>\<close>-models (BKK Definitions 3.40 and 3.41)\<close>

text \<open>A \<open>\<Sigma>\<close>-valuation is a (total) function \<open>\<upsilon> : D\<^bsub>\<o>\<^esub> \<rightarrow> {T, F}\<close> --- rendered as a HOL
  predicate --- satisfying the properties \<open>L\<^sub>\<not>(E(\<not>))\<close>, \<open>L\<^sub>\<or>(E(\<or>))\<close> and \<open>L\<^sup>\<alpha>\<^sub>\<forall>(E(\<Pi>\<^sub>\<alpha>))\<close> of
  BKK's Figure 2.  A \<open>\<Sigma>\<close>-evaluation together with such a valuation is a \<open>\<Sigma>\<close>-model.
  Following BKK Definition 3.41 (and Remark 3.42) we include primitive equality
  \<open>L\<^sup>\<alpha>\<^sub>=(E(=\<^sub>\<alpha>))\<close>, and --- extending BKK Definition 3.41, whose \<open>\<Sigma>\<close>-models have no
  description operator --- a description property for \<open>E(\<iota>\<^sub>\<alpha>)\<close>, matching \<open>NK(\<iota>)\<close>.  Since the logical
      constants are closed, their denotations are assignment-
  independent (coincidence); we fix a canonical assignment to name them.\<close>

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
  by (metis (mono_tags, lifting) TrueB_def sigma_eval.ev_app sigma_eval.ev_type sigma_eval_axioms
      vl_FalseB vl_neg wff_FalseB wff_Neg wff_TrueB xi)

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

text \<open>BKK Lemma 4.2: in a \<open>\<Sigma>\<close>-model with primitive equality (which gives property q with
  witness \<open>E(=\<^bsub>\<alpha>\<^esub>)\<close>), Leibniz equality is satisfied exactly by equal denotations.\<close>

end

subsection \<open>\<open>\<Sigma>\<close>-Henkin models: the general-model locale (BKK Definition 3.50)\<close>

text \<open>BKK's soundness and completeness theorems (BKK Theorem 7.3, Corollary 7.7) cover all
  eight model classes \<open>\<M>\<^sub>*\<close>; this development instantiates the most specialised one, the
  class \<open>\<M>\<^sub>\<beta>\<^sub>f\<^sub>b\<close> of @{emph \<open>\<open>\<Sigma>\<close>-Henkin models\<close>} (BKK Definition 3.50): \<open>\<Sigma>\<close>-models (BKK
  Definition 3.41) satisfying property b, property f (functionality), and property q (BKK
  Definitions 3.46 and 3.49).  Crucially the function domains need not be full (BKK
  Definition 3.5): following Henkin --- in BKK's words, it is sufficient to require that \<open>\<D>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<beta>\<^esub>\<close>
  ``has enough members that any well-formed formula can be evaluated'' (BKK
  Section 2.3.1).  We therefore
  require the \<open>\<lambda>\<close>-conditions --- \<open>\<lambda>\<close>-comprehension \<open>gm_lamTy\<close> and the \<open>\<beta>\<close>-condition \<open>gm_beta\<close>
  of the \<open>\<Sigma>\<close>-evaluation (BKK Definition 3.18) --- only for the functions that are
  @{emph \<open>denotations of \<open>\<lambda>\<close>-terms\<close>}; equivalently, every wff denotes.  A term model cannot be
  full: with property b the domain \<open>\<D>\<^bsub>\<iota>\<^bold>\<Rightarrow>\<o>\<^esub>\<close> of a full frame over infinite \<open>\<D>\<^bsub>\<iota>\<^esub>\<close> would be
  uncountable, whereas the term model is countable.  (BKK avoid Andrews' term
  @{emph \<open>general models\<close>} for this notion; we keep it in the locale name
  \<open>general_model\<close>, in Andrews' sense.)  Standard models --- the full case, BKK
  Definition 3.51 --- appear at the end of this section as a sublocale.  Beyond BKK, the locale
  carries the description condition \<open>gm_descB\<close> for the typed description operators \<open>Iota \<sigma>\<close>
  (Andrews 1972, BKK's reference [3]), matched by the rule \<open>NK(\<iota>)\<close> of the calculus.

  Note that we render the applicative structure abstractly (an application operation \<open>\<^bold>@\<close> on a
  carrier \<open>'u\<close>) rather than literally over a frame of functions (BKK Definition 3.4); by
  functionality and BKK Theorem 3.68 the two presentations describe the same class of models
  up to isomorphism.\<close>


locale general_model = frame_sig +
  \<comment> \<open>every domain is inhabited (part of BKK Definition 3.1, applicative structures)\<close>
  assumes gm_nonempty: "\<exists>d. \<D>\<^bsub>\<sigma>\<^esub> d"
    \<comment> \<open>property b (BKK Definition 3.46): \<open>\<D>\<^bsub>\<o>\<^esub> = {Tv, Fv}\<close>\<close>
    and gm_TF: "Tv \<noteq> Fv" and gm_boolean: "\<D>\<^bsub>\<o>\<^esub> a \<longleftrightarrow> a = Tv \<or> a = Fv"
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

text \<open>An assignment is @{emph \<open>total\<close>} (@{term resp}, respects the domains everywhere) if it
    maps
  every typed variable into the matching domain --- BKK's assignment @{emph \<open>into\<close>} the
      structure.\<close>

definition resp where "resp \<xi> \<longleftrightarrow> (\<forall>(n::nat) \<tau>. \<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>))"
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

end

subsection \<open>Closed well-formed terms and simultaneous substitution\<close>

text \<open>A @{emph \<open>closed\<close>} well-formed term, BKK's \<open>cwff\<^bsub>\<sigma>\<^esub>\<close> (BKK Section 2.2; BKK reserve
  @{emph \<open>sentence\<close>} for closed formulae of type \<open>\<o>\<close> --- parameters are allowed,
  they play the role of BKK's constants).  These are the carriers of the term model.\<close>

definition cwff :: "ty \<Rightarrow> 'p tm \<Rightarrow> bool" where "cwff \<sigma> A \<longleftrightarrow> wff\<^bsub>\<sigma>\<^esub>(A) \<and> fvs A = {}"
lemma cwffI: "wff\<^bsub>\<sigma>\<^esub>(A) \<Longrightarrow> fvs A = {} \<Longrightarrow> cwff \<sigma> A" by (simp add: cwff_def)
lemma cwff_wff: "cwff \<sigma> A \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(A)" by (simp add: cwff_def)
lemma cwff_closed: "cwff \<sigma> A \<Longrightarrow> fvs A = {}" by (simp add: cwff_def)
lemma cwff_lc: "cwff \<sigma> A \<Longrightarrow> lc A" by (metis cwff_def wff_lc)
lemma cwff_Neg: "cwff (\<o>\<^bold>\<Rightarrow>\<o>) Neg"
  and cwff_Dis: "cwff (\<o>\<^bold>\<Rightarrow>\<o>\<^bold>\<Rightarrow>\<o>) Dis"
  and cwff_Pi: "cwff ((\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>) (Pi \<sigma>)" 
  and cwff_Iota: "cwff ((\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<sigma>) (Iota \<sigma>)"
  and cwff_TrueB: "cwff \<o> \<^bold>\<top>"
  and cwff_FalseB: "cwff \<o> \<^bold>\<bottom>" 
  by (auto simp: cwff_def wff_Neg wff_Dis wff_Pi wff_Iota)
lemma cwff_Eq: "cwff (\<sigma>\<^bold>\<Rightarrow>\<sigma>\<^bold>\<Rightarrow>\<o>) (Eq \<sigma>)" by (simp add: cwff_def wff_Eq)
lemma cwff_Par: "cwff \<sigma> (p\<^sup>p\<^bsub>\<sigma>\<^esub>)" by (simp add: cwff_def wff_Par)
lemma cwff_App: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) s \<Longrightarrow> cwff \<sigma> t \<Longrightarrow> cwff \<tau> (s \<^bold>\<cdot> t)"
  by (auto simp: cwff_def intro: wff.wff_App)
lemma cwff_opn: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> cwff \<sigma> a \<Longrightarrow> cwff \<tau> (b\<^bold>\<langle>a\<^bold>\<rangle>)" 
  by (metis (no_types, opaque_lifting) cwff_def fvs.simps(10) fvs_opn
      subset_empty sup.idem wff_opn) 
lemma cwff_unique: "cwff \<sigma> A \<Longrightarrow> cwff \<tau> A \<Longrightarrow> \<sigma> = \<tau>"
  by (auto simp: cwff_def dest: wff_unique)

text \<open>Converse of @{thm wff_Abs_open}: a body that is well-typed when opened with @{emph \<open>one\<close>}
  fresh variable yields a well-typed abstraction (all fresh openings are \<open>\<alpha>\<close>-variants).\<close>

lemma wff_Abs_open_rev: "wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) \<Longrightarrow> x \<notin> fvs b \<Longrightarrow> wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
  by (metis fsub_intro wff_AbsI wff_Fre wff_fsub)

text \<open>Simultaneous substitution of a (closed) term for every free variable --- the analogue of
  the closing substitution \<open>\<sigma>\<close> in BKK's term evaluation (BKK Definition 3.35).  Because the
  replacements are closed, it commutes with opening --- the locally-nameless analogue of BKK's
  parallel substitution, with no binder renaming.\<close>

primrec msub :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm) \<Rightarrow> 'p tm \<Rightarrow> 'p tm" where
    "msub \<rho> (Bnd i) = Bnd i"
  | "msub \<rho> (n\<^sup>f\<^bsub>\<tau>\<^esub>) = \<rho> n \<tau>"
  | "msub \<rho> (p\<^sup>p\<^bsub>\<tau>\<^esub>) = p\<^sup>p\<^bsub>\<tau>\<^esub>"
  | "msub \<rho> Neg = Neg"
  | "msub \<rho> Dis = Dis"
  | "msub \<rho> (Pi \<tau>) = Pi \<tau>"
  | "msub \<rho> (Iota \<tau>) = Iota \<tau>"
  | "msub \<rho> (Eq \<tau>) = Eq \<tau>"
  | "msub \<rho> (s \<^bold>\<cdot> t) = (msub \<rho> s) \<^bold>\<cdot> (msub \<rho> t)"
  | "msub \<rho> (\<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> b) = \<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> (msub \<rho> b)"

text \<open>Parallel-substitution notation: \<open>u\<^bold>\<lbrakk>\<rho>\<^bold>\<rbrakk>\<close> applies the substitution \<open>\<rho>\<close>
  to every free variable of \<open>u\<close>.\<close>

syntax "_msub" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (\<open>_\<^bold>\<lbrakk>_\<^bold>\<rbrakk>\<close> [1000, 0] 1000)
syntax_consts "_msub" == "msub"
translations "u\<^bold>\<lbrakk>\<rho>\<^bold>\<rbrakk>" \<rightleftharpoons> "CONST msub \<rho> u"

lemma msub_opn: "(\<And>n \<tau>. lc (\<rho> n \<tau>)) \<Longrightarrow> msub \<rho> (opn k u t) = opn k (msub \<rho> u) (msub \<rho> t)" 
  by (induction t arbitrary: k) auto
lemma msub_cong: "(\<And>n \<tau>. (n, \<tau>) \<in> occ t \<Longrightarrow> \<rho> n \<tau> = \<rho>' n \<tau>) \<Longrightarrow> msub \<rho> t = msub \<rho>' t" 
  by (induction t) auto
lemma fvs_msub: "(\<And>n \<tau>. fvs (\<rho> n \<tau>) = {}) \<Longrightarrow> fvs (msub \<rho> t) = {}"
  by (induction t) auto
lemma wff_msub:
  "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> (\<And>n \<tau>. wff\<^bsub>\<tau>\<^esub>(\<rho> n \<tau>)) \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(msub \<rho> t)"
proof (induction \<sigma> t arbitrary: \<rho> rule: wff.induct)
  case (wff_Abs L \<tau> b \<sigma>)
  have lcr: "lc (\<rho> n \<tau>')" for n \<tau>' using wff_Abs.prems
    by (rule wff_lc)
  have "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (msub \<rho> b))"
  proof (rule wff.wff_Abs[of "L \<union> fvs b"])
    fix y assume y: "y \<notin> L \<union> fvs b"
    let ?\<rho> = "\<rho>(y := (\<rho> y)(\<sigma> := y\<^sup>f\<^bsub>\<sigma>\<^esub>))"
    have e: "msub ?\<rho> (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = (msub \<rho> b)\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>"
      by (smt (verit, ccfv_SIG) Un_iff fun_upd_other fun_upd_same 
              fvs_eq_fst_occ image_eqI lc_Fre lcr msub.simps(2)
              msub_cong msub_opn prod.sel(1) y)
    have "wff\<^bsub>\<tau>\<^esub>(msub ?\<rho> (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>))"
      using wff_Abs wff.wff_Fre y by (metis Un_iff fun_upd_other fun_upd_same)
    thus "wff\<^bsub>\<tau>\<^esub>((msub \<rho> b)\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" using e by simp
  qed (simp add: wff_Abs)
  thus ?case by simp
qed(auto intro: wff.intros)

text \<open>A well-formed term becomes a @{emph \<open>closed\<close>} well-formed term under a closed simultaneous
  substitution --- the instance used to build the term model.\<close>

lemma cwff_msub: "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> (\<And>n \<tau>. cwff \<tau> (\<rho> n \<tau>)) \<Longrightarrow> cwff \<sigma> (msub \<rho> t)"
  by (metis cwff_def wff_msub fvs_msub)

text \<open>A closed term is untouched by simultaneous substitution.\<close>

lemma msub_closed: "fvs t = {} \<Longrightarrow> msub \<rho> t = t" by (induction t) auto

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

definition vresp where "vresp \<xi> \<longleftrightarrow> (\<forall>(n::nat) \<tau>. \<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>))"
definition rep_of where "rep_of \<xi> (n::nat) \<tau> = (SOME t. cwff \<tau> t \<and> \<xi> n \<tau> = \<V> t)"
lemma rep_of_spec: assumes "vresp \<xi>" shows "cwff \<tau> (rep_of \<xi> n \<tau>) \<and> \<xi> n \<tau> = \<V> (rep_of \<xi> n \<tau>)"
proof -
  have "\<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>)" using assms[unfolded vresp_def] by blast
  hence "\<exists>t. cwff \<tau> t \<and> \<xi> n \<tau> = \<V> t" using v_dom by blast
  thus ?thesis unfolding rep_of_def by (rule someI_ex)
qed

text \<open>The valuation respects \<open>\<beta>\<close>-conversion under closing substitutions (BKK's quotient
  of the term structure by \<open>\<beta>\<close>, Section 6): the abstraction case is pointwise by \<open>v_beta\<close>
      and closed by \<open>v_ext\<close>.\<close>

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
  case (1 \<alpha>) show ?case using v_domI[OF cwff_Par] by blast
next case (2 \<alpha> \<beta> f a) thus ?case  using cwff_App v_dom valuation.v_app
    valuation_axioms by fastforce 
qed

sublocale valuation \<subseteq> bkkM: bkk_model Dv Vap Ev "\<lambda>a. a = \<V> \<^bold>\<top>"
proof (unfold_locales, goal_cases)
  case (1 \<tau> A \<xi>) thus ?case
    by (metis Ev_def bkkA.asg_def cwff_msub rep_of_spec v_domI vresp_def)
next case (2 \<xi> n \<sigma>) thus ?case
  using Ev_def bkkA.asg_def rep_of_spec vresp_def by auto 
next case (3 \<sigma> \<tau> F A \<xi>) thus ?case
  by (metis Ev_def bkkA.asg_def cwff_msub msub.simps(9) rep_of_spec v_app vresp_def)
next case (4 \<tau> A \<xi> \<xi>') 
  hence "rep_of \<xi> n \<sigma> = rep_of \<xi>' n \<sigma>" if "(n, \<sigma>) \<in> occ A" for n \<sigma>
    using that by (auto simp: rep_of_def)
  thus ?case unfolding Ev_def by (simp cong: msub_cong)
next case 5 thus ?case using Ev_def beq_V bkkA.asg_def rep_of_spec vresp_def by auto
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
next case 10 thus ?case by (smt (verit, best) Ev_def cwff_Iota msub.simps(7) v_app v_desc v_dom)
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

text \<open>In a full frame every domain is inhabited (for \<open>\<o>\<close> by \<open>Tv\<close>, for \<open>\<iota>\<close> by applying \<open>Iv\<close>
  to a representable predicate, for function types by a constant function).  BKK build
  non-emptiness into the applicative structure (BKK Definition 3.1).\<close>

lemma dom_nonempty: "\<exists>d. \<D>\<^bsub>\<tau>\<^esub> d" by (metis Jv_dom)

text \<open>In a full frame every well-formed term denotes in the domain of its type (the standard
  homomorphic construction, BKK Section 2.3.1): the abstraction case is immediate from
      fullness.\<close>

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

end
