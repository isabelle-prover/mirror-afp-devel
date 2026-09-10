theory NK_Infinity
  imports Consistency Completeness
begin

section \<open>Consistency of NK (with infinitely many individuals)\<close>

text \<open>The parametric family of finite standard models constructed in \<open>Consistency\<close> provides,
  for every finite size \<open>k > 0\<close>, a standard model with exactly \<open>k\<close> individuals whose
  parameter interpretation can distinguish any prescribed finite family of parameters.  This
  is the model-theoretic input to Andrews' standard method (\<open>\<section>55\<close>) for passing to infinite
  models: consistency of the diagram \<open>Diag = {c\<^sub>i \<noteq> c\<^sub>j | i \<noteq> j}\<close> over countably many fresh
  individual constants \<open>c\<^sub>i\<close>.

  Infinity is formulated as a diagram @{emph \<open>scheme\<close>}, following Andrews.  Compactness ---
  the finite character of derivability, @{thm [source] con_compact} --- lifts the consistency
  of each @{emph \<open>finite\<close>} subdiagram, satisfied in one of the finite models above, to the
  consistency of the whole diagram.  So consistency of \<open>NK\<close> with infinitely many individuals
  is obtained from the finite models alone: no infinite model is constructed, and nothing
  beyond plain HOL is used.  Being a scheme, \<open>Diag\<close> is not to be conflated with a single
  Dedekind-style axiom of infinity.  The relation between scheme and axiom is made precise
  below: the axiom is @{emph \<open>not\<close>} derivable from the scheme, and a general model of the
  whole scheme refutes it.\<close>

subsection \<open>The diagram scheme\<close>

text \<open>An arbitrary injective family \<open>f\<close> of parameter constants (\<open>'p\<close> being infinite) and
  the sentences \<open>f i \<noteq> f j\<close>; the consistency theorem holds for every such family, so no
  canonical choice of constants is needed.\<close>

definition dneq :: "(nat \<Rightarrow> 'p) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'p::infinite tm" where
  "dneq f i j = \<^bold>\<not> ((f i)\<^sup>p\<^bsub>\<iota>\<^esub> \<^bold>=\<^bsub>\<iota>\<^esub> (f j)\<^sup>p\<^bsub>\<iota>\<^esub>)"

lemma wff_dneq: "wff\<^bsub>\<o>\<^esub>(dneq f i j :: 'p::infinite tm)"
  unfolding dneq_def by (simp add: wff_Not wff_PEq wff_Par)

lemma dneq_inj: "inj f \<Longrightarrow> dneq f i j = dneq f i' j' \<Longrightarrow> i = i' \<and> j = j'"
  unfolding dneq_def by (auto dest: injD)

inductive_set Diag :: "(nat \<Rightarrow> 'p) \<Rightarrow> 'p::infinite tm set" for f where
  Diag_I: "i \<noteq> j \<Longrightarrow> dneq f i j \<in> Diag f"

lemma Diag_iff: "B \<in> Diag f \<longleftrightarrow> (\<exists>i j. B = dneq f i j \<and> i \<noteq> j)"
  by (auto simp: Diag.simps)

text \<open>Every finite fragment of the diagram is satisfied by a large-enough finite model,
  hence consistent, and by compactness so is the whole diagram.  The finite model is
  constructed @{emph \<open>once\<close>}, in the separation section below, where the very same model
  also refutes the Dedekind axiom; the consistency theorems \<open>con_finite_sub\<close>, \<open>con_Diag\<close>
  and \<open>con_Diag_fprov\<close> are stated there.\<close>

section \<open>The Dedekind axiom of infinity\<close>

text \<open>A single genuine axiom of infinity in the sense of Dedekind: some self-map \<open>F\<close> of the
  individuals is injective but not surjective,
  \<open>DInf = \<^bold>\<exists>F\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>. (\<^bold>\<Pi>X. \<^bold>\<Pi>Y. F\<cdot>X \<^bold>= F\<cdot>Y \<^bold>\<supset> X \<^bold>= Y) \<^bold>\<and> (\<^bold>\<exists>C. \<^bold>\<Pi>Z. \<^bold>\<not> F\<cdot>Z \<^bold>= C)\<close>.\<close>

subsection \<open>The axiom as an object formula\<close>

definition vF where "vF = (0::nat)"
definition vX where "vX = (1::nat)"
definition vY where "vY = (2::nat)"
definition vC where "vC = (3::nat)"
definition vZ where "vZ = (4::nat)"

lemmas vdefs = vF_def vX_def vY_def vC_def vZ_def

definition EqFXFY :: "'p tm" where
  "EqFXFY = (((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> ((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))"
definition EqXY :: "'p tm" where "EqXY = ((vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>))"
definition ImpBody :: "'p tm" where "ImpBody = EqFXFY \<^bold>\<supset> EqXY"
definition InjBody :: "'p tm" where "InjBody = \<^bold>\<Pi>vX\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>. ImpBody"
definition NsAtom :: "'p tm" where
  "NsAtom = \<^bold>\<not> (((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (vC\<^sup>f\<^bsub>\<iota>\<^esub>))"
definition NsBody :: "'p tm" where "NsBody = \<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. NsAtom"
definition DInf :: "'p tm" where "DInf = \<^bold>\<exists>vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>. (InjBody \<^bold>\<and> NsBody)"

(*<*)
lemma wff_EqFXFY [intro]: "wff\<^bsub>\<o>\<^esub>(EqFXFY :: 'p tm)"
  unfolding EqFXFY_def
  by (rule wff_PEq[OF wff_App[OF wff_Fre wff_Fre] wff_App[OF wff_Fre wff_Fre]])
lemma wff_EqXY [intro]: "wff\<^bsub>\<o>\<^esub>(EqXY :: 'p tm)"
  unfolding EqXY_def by (rule wff_PEq[OF wff_Fre wff_Fre])
lemma wff_ImpBody [intro]: "wff\<^bsub>\<o>\<^esub>(ImpBody :: 'p tm)"
  unfolding ImpBody_def by (rule wff_ImpB[OF wff_EqFXFY wff_EqXY])
lemma wff_InjBody: "wff\<^bsub>\<o>\<^esub>(InjBody :: 'p tm)"
  unfolding InjBody_def by (rule wff_AllN[OF wff_AllN[OF wff_ImpBody]])
lemma wff_NsAtom [intro]: "wff\<^bsub>\<o>\<^esub>(NsAtom :: 'p tm)"
  unfolding NsAtom_def
  by (rule wff_Not[OF wff_PEq[OF wff_App[OF wff_Fre wff_Fre] wff_Fre]])
lemma wff_NsBody: "wff\<^bsub>\<o>\<^esub>(NsBody :: 'p tm)"
  unfolding NsBody_def by (rule wff_ExN[OF wff_AllN[OF wff_NsAtom]])
lemma wff_DInf: "wff\<^bsub>\<o>\<^esub>(DInf :: 'p tm)"
  unfolding DInf_def by (rule wff_ExN[OF wff_AndB[OF wff_InjBody wff_NsBody]])

lemma fvs_DInf: "fvs (DInf :: 'p tm) = {}"
  by (simp add: DInf_def InjBody_def NsBody_def ImpBody_def NsAtom_def EqFXFY_def
      EqXY_def AndB_def ExN_def AllN_def Forall_def ImpB_def vdefs)

lemma cwff_DInf: "cwff \<o> (DInf :: 'p tm)"
  by (rule cwffI[OF wff_DInf fvs_DInf])
(*>*)

text \<open>Assembled, the axiom in full --- first by pure definitional unfolding, then, following
  the presentation of the Cantor sentences in \<open>Cantor\<close>, in its machine-level
  locally-nameless normal form (de Bruijn indices \<open>Bnd 0\<close>, \<open>Bnd (Suc 0)\<close> and so on),
  recovered by computation:\<close>

lemma DInf_unfolded:
  "(DInf :: 'p tm)
   = (\<^bold>\<exists>vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>.
       ((\<^bold>\<Pi>vX\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>.
           ((((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> ((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
            \<^bold>\<supset> ((vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>))))
        \<^bold>\<and> (\<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. \<^bold>\<not> (((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (vC\<^sup>f\<^bsub>\<iota>\<^esub>)))))"
  by (simp only: DInf_def InjBody_def NsBody_def ImpBody_def NsAtom_def EqFXFY_def
      EqXY_def)

lemma DInf_norm:
  "(DInf :: 'p tm)
   = \<^bold>\<exists>\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>
       ((\<^bold>\<Pi>\<^bsub>\<iota>\<^esub> (\<^bold>\<Pi>\<^bsub>\<iota>\<^esub>
           (((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd (Suc 0)) \<^bold>=\<^bsub>\<iota>\<^esub> (Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd 0))
            \<^bold>\<supset> (Bnd (Suc 0) \<^bold>=\<^bsub>\<iota>\<^esub> Bnd 0))))
        \<^bold>\<and> (\<^bold>\<exists>\<^bsub>\<iota>\<^esub> (\<^bold>\<Pi>\<^bsub>\<iota>\<^esub> (\<^bold>\<not> ((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<iota>\<^esub> Bnd (Suc 0))))))"
  by (simp add: DInf_def InjBody_def NsBody_def ImpBody_def NsAtom_def EqFXFY_def
      EqXY_def AndB_def ExN_def AllN_def Forall_def ImpB_def vdefs)

subsection \<open>Injectivity and non-surjectivity in an arbitrary standard model\<close>

text \<open>These facts hold in \<^emph>\<open>any\<close> \<open>\<Sigma>\<close>-standard model: they peel \<open>InjBody\<close> / \<open>NsBody\<close> down
  to injectivity and non-surjectivity of a self-map \<open>d\<close> on the individuals.  Only the
  witness for such a \<open>d\<close> is model-specific, so \<open>DInf_sat\<close> takes that data as hypotheses,
  and every consistency argument about \<open>DInf\<close> --- here and in the companion development ---
  shares this carrier-generic core.\<close>

context standard_model
begin
lemma InjSat:
  assumes xi: "bkkA.asg \<xi>" and d: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d"
  shows "(den InjBody (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := d)) = Tv)
      = (\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b)))"
proof -
    define \<eta> where "\<eta> = \<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := d)"
    have ea: "bkkA.asg \<eta>" unfolding \<eta>_def using xi d by (rule bkkA.asg_upd)
    have inner: "(den ImpBody ((\<eta>(vX\<^bsub>\<iota>\<^esub> := a))(vY\<^bsub>\<iota>\<^esub> := b)) = Tv)
        = (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b)" if a: "Dm \<iota> a" and b: "Dm \<iota> b" for a b
    proof -
      define \<rho> where "\<rho> = (\<eta>(vX\<^bsub>\<iota>\<^esub> := a))(vY\<^bsub>\<iota>\<^esub> := b)"
      have er: "bkkA.asg \<rho>" unfolding \<rho>_def using ea a b by (auto intro: bkkA.asg_upd)
      have fx: "den ((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<rho> = d \<^bold>@ a"
        by (simp add: den.simps(8) \<rho>_def \<eta>_def upd_def vdefs)
      have fy: "den ((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)) \<rho> = d \<^bold>@ b"
        by (simp add: den.simps(8) \<rho>_def \<eta>_def upd_def vdefs)
      have ex: "den (vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<rho> = a" by (simp add: \<rho>_def upd_def vdefs)
      have ey: "den (vY\<^sup>f\<^bsub>\<iota>\<^esub>) \<rho> = b" by (simp add: \<rho>_def upd_def vdefs)
      have peq1: "(den EqFXFY \<rho> = Tv) = (d \<^bold>@ a = d \<^bold>@ b)"
        unfolding EqFXFY_def
        using sat_PEqB[OF wff_App[OF wff_Fre wff_Fre] wff_App[OF wff_Fre wff_Fre] er] fx fy
        by simp
      have peq2: "(den EqXY \<rho> = Tv) = (a = b)"
        unfolding EqXY_def using sat_PEqB[OF wff_Fre wff_Fre er] ex ey by simp
      have "(den ImpBody \<rho> = Tv)
          = ((den EqFXFY \<rho> = Tv) \<longrightarrow> (den EqXY \<rho> = Tv))"
        unfolding ImpBody_def by (rule sat_ImpBB[OF wff_EqFXFY wff_EqXY er])
      also have "\<dots> = (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b)" using peq1 peq2 by simp
      finally show ?thesis by (simp add: \<rho>_def)
    qed
    have step2: "(den (\<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>. ImpBody) (\<eta>(vX\<^bsub>\<iota>\<^esub> := a)) = Tv)
        = (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b))" if a: "Dm \<iota> a" for a
    proof -
      have "(den (\<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>. ImpBody) (\<eta>(vX\<^bsub>\<iota>\<^esub> := a)) = Tv)
          = (\<forall>b. Dm \<iota> b \<longrightarrow> den ImpBody ((\<eta>(vX\<^bsub>\<iota>\<^esub> := a))(vY\<^bsub>\<iota>\<^esub> := b)) = Tv)"
        by (rule sat_AllN[OF wff_ImpBody bkkA.asg_upd[OF ea a]])
      thus ?thesis using inner[OF a] by simp
    qed
    have "(den InjBody \<eta> = Tv)
        = (\<forall>a. Dm \<iota> a \<longrightarrow> den (\<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>. ImpBody) (\<eta>(vX\<^bsub>\<iota>\<^esub> := a)) = Tv)"
      unfolding InjBody_def by (rule sat_AllN[OF wff_AllN[OF wff_ImpBody] ea])
    thus ?thesis using step2 by (simp add: \<eta>_def)
qed

lemma NsSat:
  assumes xi: "bkkA.asg \<xi>" and d: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d"
  shows "(den NsBody (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := d)) = Tv)
      = (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c))"
proof -
    define \<eta> where "\<eta> = \<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := d)"
    have ea: "bkkA.asg \<eta>" unfolding \<eta>_def using xi d by (rule bkkA.asg_upd)
    have inner: "(den NsAtom ((\<eta>(vC\<^bsub>\<iota>\<^esub> := c))(vZ\<^bsub>\<iota>\<^esub> := z)) = Tv)
        = (d \<^bold>@ z \<noteq> c)" if c: "Dm \<iota> c" and z: "Dm \<iota> z" for c z
    proof -
      define \<rho> where "\<rho> = (\<eta>(vC\<^bsub>\<iota>\<^esub> := c))(vZ\<^bsub>\<iota>\<^esub> := z)"
      have er: "bkkA.asg \<rho>" unfolding \<rho>_def using ea c z by (auto intro: bkkA.asg_upd)
      have fz: "den ((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<rho> = d \<^bold>@ z"
        by (simp add: den.simps(8) \<rho>_def \<eta>_def upd_def vdefs)
      have ec: "den (vC\<^sup>f\<^bsub>\<iota>\<^esub>) \<rho> = c" by (simp add: \<rho>_def upd_def vdefs)
      have peq: "(den (((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (vC\<^sup>f\<^bsub>\<iota>\<^esub>)) \<rho> = Tv) = (d \<^bold>@ z = c)"
        using sat_PEqB[OF wff_App[OF wff_Fre wff_Fre] wff_Fre er] fz ec by simp
      have "(den NsAtom \<rho> = Tv)
          = (\<not> (den (((vF\<^sup>f\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (vC\<^sup>f\<^bsub>\<iota>\<^esub>)) \<rho> = Tv))"
        unfolding NsAtom_def
        by (rule sat_NegB[OF wff_PEq[OF wff_App[OF wff_Fre wff_Fre] wff_Fre] er])
      also have "\<dots> = (d \<^bold>@ z \<noteq> c)" using peq by simp
      finally show ?thesis by (simp add: \<rho>_def)
    qed
    have step2: "(den (\<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. NsAtom) (\<eta>(vC\<^bsub>\<iota>\<^esub> := c)) = Tv)
        = (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c)" if c: "Dm \<iota> c" for c
    proof -
      have "(den (\<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. NsAtom) (\<eta>(vC\<^bsub>\<iota>\<^esub> := c)) = Tv)
          = (\<forall>z. Dm \<iota> z \<longrightarrow> den NsAtom ((\<eta>(vC\<^bsub>\<iota>\<^esub> := c))(vZ\<^bsub>\<iota>\<^esub> := z)) = Tv)"
        by (rule sat_AllN[OF wff_NsAtom bkkA.asg_upd[OF ea c]])
      thus ?thesis using inner[OF c] by simp
    qed
    have hall: "(den NsBody \<eta> = Tv)
        = (\<exists>c. Dm \<iota> c \<and> den (\<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. NsAtom) (\<eta>(vC\<^bsub>\<iota>\<^esub> := c)) = Tv)"
      unfolding NsBody_def by (rule sat_ExN[OF wff_AllN[OF wff_NsAtom] ea])
    have "(den NsBody \<eta> = Tv) = (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c))"
      using hall by (simp add: step2 cong: conj_cong)
    thus ?thesis by (simp add: \<eta>_def)
qed

lemma DInf_sat:
  assumes xi: "bkkA.asg \<xi>" and d: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d"
    and inj: "\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b))"
    and ns: "\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c)"
  shows "den DInf \<xi> = Tv"
proof -
  have conj: "den (InjBody \<^bold>\<and> NsBody) (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := d)) = Tv"
    using sat_AndB[OF wff_InjBody wff_NsBody bkkA.asg_upd[OF xi d]]
          InjSat[OF xi d] NsSat[OF xi d] inj ns by simp
  have "(den DInf \<xi> = Tv)
      = (\<exists>e. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) e \<and> den (InjBody \<^bold>\<and> NsBody) (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := e)) = Tv)"
    unfolding DInf_def by (rule sat_ExN[OF wff_AndB[OF wff_InjBody wff_NsBody] xi])
  thus ?thesis using d conj by auto
qed

end

section \<open>Consistency of the scheme, and its separation from the axiom\<close>

text \<open>How do scheme and axiom relate?  The scheme does not yield the
  axiom.  Every @{emph \<open>finite\<close>} standard model refutes \<open>DInf\<close> --- an injective
  self-map of a finite set is surjective --- while a large enough finite model satisfies
  any finite part of the scheme.  Hence the scheme together with \<open>\<^bold>\<not> DInf\<close> is consistent,
  no finite part of \<open>Diag f\<close> derives \<open>DInf\<close> (\<open>\<not> (Diag f \<tturnstile> DInf)\<close>), and a countable
  Henkin model of the whole scheme --- for a family leaving infinitely many parameters in
  reserve --- refutes the axiom, making the separation model-theoretic.  All of this stays
  in plain HOL: the refuting models are the finite ones from \<open>Consistency\<close>, and the Henkin
  model is the term model of \<open>Completeness\<close>.  The converse direction fails as well: \<open>DInf\<close>
  is a pure sentence and does not constrain the parameter interpretation, so it derives no
  inequation of the diagram --- proved via the set-theoretic model in the companion
  development, whose parameters all denote alike.  As sentences, axiom and scheme are
  incomparable.\<close>

context standard_model
begin

lemma DInf_sat_iff:
  assumes xi: "bkkA.asg \<xi>"
  shows "(den DInf \<xi> = Tv)
       = (\<exists>d. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d
              \<and> (\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b)))
              \<and> (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c)))"
proof -
  have unf: "(den DInf \<xi> = Tv)
      = (\<exists>e. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) e
             \<and> den (InjBody \<^bold>\<and> NsBody) (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := e)) = Tv)"
    unfolding DInf_def by (rule sat_ExN[OF wff_AndB[OF wff_InjBody wff_NsBody] xi])
  have cnj: "(den (InjBody \<^bold>\<and> NsBody) (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := e)) = Tv)
      = ((\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (e \<^bold>@ a = e \<^bold>@ b \<longrightarrow> a = b)))
         \<and> (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> e \<^bold>@ z \<noteq> c)))"
    if e: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) e" for e
    using sat_AndB[OF wff_InjBody wff_NsBody bkkA.asg_upd[OF xi e]]
          InjSat[OF xi e] NsSat[OF xi e] by simp
  show ?thesis unfolding unf using cnj by blast
qed

lemma DInf_refuted_finite:
  assumes xi: "bkkA.asg \<xi>" and fin: "finite {x. Dm \<iota> x}"
  shows "den (\<^bold>\<not> DInf) \<xi> = Tv"
proof -
  have "\<not> (den DInf \<xi> = Tv)"
  proof
    assume "den DInf \<xi> = Tv"
    then obtain d where d: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d"
        and dinj: "\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b))"
        and dns: "\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c)"
      using DInf_sat_iff[OF xi] by blast
    have eq: "(\<lambda>a. d \<^bold>@ a) ` {x. Dm \<iota> x} = {x. Dm \<iota> x}"
    proof (rule endo_inj_surj[OF fin])
      show "(\<lambda>a. d \<^bold>@ a) ` {x. Dm \<iota> x} \<subseteq> {x. Dm \<iota> x}"
        using Ap_dom[OF d] by auto
      show "inj_on (\<lambda>a. d \<^bold>@ a) {x. Dm \<iota> x}"
        using dinj by (auto simp: inj_on_def)
    qed
    obtain c where c: "Dm \<iota> c" and nc: "\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c"
      using dns by blast
    have "c \<in> (\<lambda>a. d \<^bold>@ a) ` {x. Dm \<iota> x}" using c eq by auto
    then obtain z where "Dm \<iota> z" and "d \<^bold>@ z = c" by auto
    thus False using nc by blast
  qed
  thus ?thesis using sat_NegB[OF wff_DInf xi] by simp
qed

end

text \<open>The refuting finite models: the size-\<open>k\<close> family of \<open>Consistency\<close>, with the parameter
  interpretation distinguishing the finitely many diagram constants at hand.  The
  construction happens @{emph \<open>once\<close>}: the same model satisfies the fragment and refutes
  the axiom, and the plain consistency of the scheme falls out by monotonicity below.\<close>

lemma con_DInf_neg_finite_sub:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
      and finF: "finite F" and FI: "F \<subseteq> Diag f"
  shows "con (insert (\<^bold>\<not> DInf) F)"
proof -
  have finP: "finite {(i,j). dneq f i j \<in> F}"
  proof -
    have "{(i,j). dneq f i j \<in> F} = (\<lambda>(i,j). dneq f i j) -` F"
      by (auto simp: vimage_def)
    moreover have "inj (\<lambda>(i,j). dneq f i j :: 'p tm)"
      by (auto simp: inj_on_def dneq_inj[OF injf])
    ultimately show ?thesis using finite_vimageI[OF finF] by simp
  qed
  define idxs where "idxs = (\<Union>(i,j)\<in>{(i,j). dneq f i j \<in> F}. {i,j})"
  have finI: "finite idxs" unfolding idxs_def using finP by auto
  define m where "m = Max (insert 0 idxs)"
  define k where "k = Suc m"
  define ix where "ix = (\<lambda>p::'p. min m (inv f p))"
  have kpos: "0 < k" by (simp add: k_def)
  have ix_le: "ix p \<le> m" for p by (simp add: ix_def)
  have ix_bound: "ix p < k" for p using ix_le[of p] by (simp add: k_def)
  have ix_f: "ix (f i) = i" if "i \<le> m" for i
    using that by (simp add: ix_def inv_f_f[OF injf] min.absorb2)
  have idx_le: "i \<le> m" if "dneq f i j \<in> F" for i j
    unfolding m_def
  proof (rule Max_ge)
    show "finite (insert 0 idxs)" using finI by simp
    show "i \<in> insert 0 idxs" using that unfolding idxs_def by auto
  qed
  have jdx_le: "j \<le> m" if "dneq f i j \<in> F" for i j
    unfolding m_def
  proof (rule Max_ge)
    show "finite (insert 0 idxs)" using finI by simp
    show "j \<in> insert 0 idxs" using that unfolding idxs_def by auto
  qed
  interpret U: lambda_universe "cD k" cAp "cLm k" "VB True" "VB False"
    "cJv k ix :: 'p \<Rightarrow> ty \<Rightarrow> ival"
    by (rule concrete_lambda_universe[OF kpos ix_bound])
  interpret standard_model "cD k" cAp "cLm k" "VB True" "VB False"
    U.Ngv U.Dsv U.Iv U.Ev U.Piv "cJv k ix :: 'p \<Rightarrow> ty \<Rightarrow> ival"
    by (rule U.is_standard_model)
  have asgX: "bkkA.asg (cXi k)" by (simp add: bkkA.asg_def cXi_def hd_en_dom[OF kpos])
  have vEq: "cAp (cAp (U.Ev \<iota>) (VI a)) (VI b) = VB (a = b)" if "a < k" "b < k" for a b
    using U.Ev_app[of \<iota> "VI a" "VI b"] that by (simp add: cD_def)
  have vNg: "cAp U.Ngv (VB c) = VB (\<not> c)" for c
    using U.Ngv_app[of "VB c"] by (cases c) (auto simp: cD_def)
  have den_dneq: "den (dneq f i j) (cXi k) = VB (ix (f i) \<noteq> ix (f j))"
    if hi: "ix (f i) < k" and hj: "ix (f j) < k" for i j
  proof -
    have "den (dneq f i j) (cXi k)
        = cAp U.Ngv (cAp (cAp (U.Ev \<iota>) (VI (ix (f i)))) (VI (ix (f j))))"
      unfolding dneq_def by (simp add: den.simps(8) cJv_def)
    also have "\<dots> = cAp U.Ngv (VB (ix (f i) = ix (f j)))"
      using vEq[OF hi hj] by simp
    also have "\<dots> = VB (ix (f i) \<noteq> ix (f j))" using vNg by simp
    finally show ?thesis .
  qed
  have Fsat: "\<forall>B\<in>F. wff\<^bsub>\<o>\<^esub>(B) \<and> den B (cXi k) = VB True"
  proof
    fix B assume "B \<in> F"
    then have "B \<in> Diag f" using FI by blast
    then obtain i j where B: "B = dneq f i j" and ne: "i \<noteq> j"
      by (auto simp: Diag_iff)
    have im: "i \<le> m" and jm: "j \<le> m"
      using \<open>B \<in> F\<close> B by (auto intro: idx_le jdx_le)
    have "den B (cXi k) = VB (ix (f i) \<noteq> ix (f j))"
      unfolding B by (rule den_dneq[OF ix_bound ix_bound])
    also have "\<dots> = VB (i \<noteq> j)" by (simp add: ix_f[OF im] ix_f[OF jm])
    also have "\<dots> = VB True" using ne by simp
    finally show "wff\<^bsub>\<o>\<^esub>(B) \<and> den B (cXi k) = VB True"
      using B by (simp add: wff_dneq)
  qed
  have finD: "finite {x. cD k \<iota> x}" by (simp add: cD_def)
  have nDsat: "den (\<^bold>\<not> DInf :: 'p tm) (cXi k) = VB True"
    by (rule DInf_refuted_finite[OF asgX finD])
  show ?thesis
    by (rule model_con[OF asgX])
       (use Fsat nDsat wff_DInf in \<open>auto intro!: wff_Not\<close>)
qed

text \<open>Discarding the refuted axiom, monotonicity gives the finite consistency of the
  diagram fragments --- Andrews' \<open>\<section>55\<close> route announced above --- and compactness the
  consistency of the whole scheme.\<close>

lemma con_finite_sub:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
      and finF: "finite F" and FI: "F \<subseteq> Diag f"
  shows "con F"
proof -
  have "con (insert (\<^bold>\<not> DInf) F)" by (rule con_DInf_neg_finite_sub[OF assms])
  moreover have "F \<subseteq> insert (\<^bold>\<not> DInf) F" by auto
  moreover have "freep (insert (\<^bold>\<not> DInf) F)"
    by (rule freep_finite) (simp add: finF)
  ultimately show ?thesis by (rule con_mono)
qed

theorem con_Diag:
  assumes "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "con (Diag f)"
  by (rule con_compact) (rule con_finite_sub[OF assms])

text \<open>One caveat: \<open>con\<close> is the @{emph \<open>weak\<close>} reading of consistency for an impure infinite
  context.  \<open>\<turnstile>\<close> derives from the whole context, and \<open>NK(\<Pi>I)\<close> needs an eigen-parameter
  fresh for all of it, so when \<open>usedp (Diag f)\<close> exhausts the alphabet (\<open>'p = \<nat>\<close>, \<open>f\<close>
  surjective), refutations that generalise are blocked by parameter
  @{emph \<open>starvation\<close>} alone.  The robust statement is the one for the hypothesis relation
  \<open>\<tturnstile>\<close>: no finite part of the diagram derives falsity --- which is exactly the finite
  consistency @{thm [source] con_finite_sub} restated through @{thm [source] fprov_con},
  free of any purity of \<open>f\<close>.\<close>

theorem con_Diag_fprov:
  assumes "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "\<not> (Diag f \<tturnstile> (\<^bold>\<bottom> :: 'p tm))"
  unfolding fprov_con by (blast intro: con_finite_sub[OF assms])

text \<open>Thus \<open>NK\<close> is consistent with the requirement of infinitely many individuals, for every
  injective constant family \<open>f\<close>.  The scheme \<open>Diag f\<close> forces \<open>\<D>\<^sub>\<iota>\<close> to be infinite in
  every model of the whole scheme, since it makes the denotations of the constants \<open>f i\<close>
  pairwise distinct.\<close>

theorem con_Diag_not_DInf:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "con (insert (\<^bold>\<not> DInf) (Diag f))"
proof (rule con_compact)
  fix F' :: "'p tm set"
  assume finF': "finite F'" and sub': "F' \<subseteq> insert (\<^bold>\<not> DInf) (Diag f)"
  have "con (insert (\<^bold>\<not> DInf) (F' - {\<^bold>\<not> DInf}))"
    by (rule con_DInf_neg_finite_sub[OF injf]) (use finF' sub' in auto)
  moreover have "F' \<subseteq> insert (\<^bold>\<not> DInf) (F' - {\<^bold>\<not> DInf})" by auto
  moreover have "freep (insert (\<^bold>\<not> DInf) (F' - {\<^bold>\<not> DInf}))"
    by (rule freep_finite) (simp add: finF')
  ultimately show "con F'" by (rule con_mono)
qed

theorem Diag_not_derives_DInf:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "\<not> (Diag f \<tturnstile> (DInf :: 'p tm))"
proof
  assume "Diag f \<tturnstile> (DInf :: 'p tm)"
  then obtain F where finF: "finite F" and FI: "F \<subseteq> Diag f"
      and FD: "F \<turnstile> (DInf :: 'p tm)"
    by (auto simp: fprov_def)
  have D: "insert (\<^bold>\<not> DInf) F \<turnstile> (DInf :: 'p tm)"
    by (rule bprov_weaken[OF FD]) (auto simp: freep_finite finF)
  have N: "insert (\<^bold>\<not> DInf) F \<turnstile> (\<^bold>\<not> DInf :: 'p tm)" by (auto intro: bprov.Hyp)
  have "insert (\<^bold>\<not> DInf) F \<turnstile> (\<^bold>\<bottom> :: 'p tm)"
    by (rule bprov.NegE[OF N D wff_FalseB])
  moreover have "con (insert (\<^bold>\<not> DInf) F)"
    by (rule con_DInf_neg_finite_sub[OF injf finF FI])
  ultimately show False by (simp add: con_def)
qed

text \<open>The Henkin-model face of the separation: a countable general model of the
  @{emph \<open>whole\<close>} scheme in which internal Dedekind infinity fails --- the refuting term
  model of \<open>Completeness\<close>, applied to \<open>Diag f\<close> and \<open>DInf\<close>.\<close>

theorem henkin_scheme_refutes_DInf:
  fixes f :: "nat \<Rightarrow> 'p::{countable,infinite}"
  assumes injf: "inj f" and res: "infinite (- range f)"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
  where "bkk_model Dm Ap Ee vl" "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "\<forall>B\<in>Diag f. vl (Ee \<xi> B)" "\<not> vl (Ee \<xi> (DInf :: 'p tm))"
proof -
  have nd: "\<not> (Diag f \<turnstile> (DInf :: 'p tm))"
    using Diag_not_derives_DInf[OF injf] bprov_fprov by blast
  have "usedp (Diag f) \<subseteq> range f"
    by (auto simp: usedp_def Diag_iff dneq_def)
  hence "- range f \<subseteq> - usedp (Diag f)" by auto
  hence "freep (Diag f)"
    unfolding freep_def by (rule infinite_super[OF _ res])
  hence fp: "richp (Diag f)" by (simp add: richp_iff_freep)
  have sen: "cwff \<o> B" if "B \<in> Diag f" for B :: "'p tm"
  proof -
    have "\<exists>i j. B = dneq f i j \<and> i \<noteq> j" using that by (simp add: Diag_iff)
    then obtain i j where B: "B = dneq f i j" by blast
    show ?thesis unfolding B dneq_def cwff_def
      by (auto intro!: wff_Not wff_PEq wff_Par)
  qed
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
      and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where "bkk_model Dm Ap Ee vl" and "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and "app_struct.asg Dm \<xi>" and "\<forall>B\<in>Diag f. vl (Ee \<xi> B)"
      and "\<not> vl (Ee \<xi> (DInf :: 'p tm))"
    using refuting_term_model_hyps[OF cwff_DInf fp sen nd] .
  thus ?thesis by (rule that)
qed

end
