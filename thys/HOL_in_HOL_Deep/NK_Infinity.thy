theory NK_Infinity
  imports Consistency Completeness
begin

section \<open>The inequation scheme over new constants\<close>

text \<open>The parametric family of finite standard models constructed in \<open>Consistency\<close> provides,
  for every finite size \<open>k > 0\<close>, a standard model with exactly \<open>k\<close> individuals whose
  parameter interpretation can distinguish any prescribed finite family of parameters.  This
  is the model-theoretic input to the classical compactness argument of first-order model
  theory that a theory with arbitrarily large finite models has an infinite model (Skolem
  \<^cite>\<open>Skolem34\<close>, Mal'cev \<^cite>\<open>Malcev36\<close>, Henkin \<^cite>\<open>Henkin49\<close>, Robinson
  \<^cite>\<open>Robinson63\<close>): expand the language by countably many new individual constants
  \<open>c\<^sub>i\<close> and add the inequations \<open>Ineq = {c\<^sub>i \<noteq> c\<^sub>j | i \<noteq> j}\<close>.  In type theory the same
  technique appears in Andrews' \<open>\<section>55\<close> \<^cite>\<open>Andrews02\<close> (Theorem 5506), there in the
  service of nonstandard models.

  Two things should be kept apart.  The standard first-order axiomatisation of ``the domain
  is infinite'' consists of the constant-free sentences ``there are at least \<open>n\<close>
  individuals'', one for each \<open>n\<close> (\<open>ExDistinct n\<close> below).  The inequation scheme over new
  constants is the tool of the compactness argument, not itself an axiomatisation: it
  derives each of those sentences (\<open>Ineq_derives_distinct_n\<close> below); that its
  constant-free consequences are no more than theirs is the translation argument, not
  formalised here.  We keep the short name \<open>Ineq\<close> for the scheme.  Compactness --- the finite character of derivability,
  @{thm [source] con_compact} --- lifts the consistency of each @{emph \<open>finite\<close>} part of
  the scheme, satisfied in one of the finite models above, to the consistency of the whole
  scheme.  So consistency of \<open>NK\<close> with the scheme is obtained from the finite models
  alone: the consistency proof constructs no infinite model, and nothing beyond plain HOL is
  used.  Neither
  the scheme nor the constant-free sentences are to be conflated with a single
  Dedekind-style axiom of infinity.  The relation is made precise below: the axiom derives
  every sentence \<open>ExDistinct n\<close>, but neither the scheme nor those sentences derive the
  axiom, and some general model of the whole scheme refutes it.\<close>

subsection \<open>The scheme as a set of object formulas\<close>

text \<open>An arbitrary injective family \<open>f\<close> of parameter constants (\<open>'p\<close> being infinite) and
  the sentences \<open>f i \<noteq> f j\<close>; the consistency theorem holds for every such family, so no
  canonical choice of constants is needed.\<close>

definition dneq :: "(nat \<Rightarrow> 'p) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'p::infinite tm" where
  "dneq f i j = \<^bold>\<not> ((f i)\<^sup>p\<^bsub>\<iota>\<^esub> \<^bold>=\<^bsub>\<iota>\<^esub> (f j)\<^sup>p\<^bsub>\<iota>\<^esub>)"

lemma wff_dneq: "wff\<^bsub>\<o>\<^esub>(dneq f i j :: 'p::infinite tm)"
  unfolding dneq_def by (simp add: wff_Not wff_PEq wff_Par)

lemma dneq_inj: "inj f \<Longrightarrow> dneq f i j = dneq f i' j' \<Longrightarrow> i = i' \<and> j = j'"
  unfolding dneq_def by (auto dest: injD)

inductive_set Ineq :: "(nat \<Rightarrow> 'p) \<Rightarrow> 'p::infinite tm set" for f where
  Ineq_I: "i \<noteq> j \<Longrightarrow> dneq f i j \<in> Ineq f"

lemma Ineq_iff: "B \<in> Ineq f \<longleftrightarrow> (\<exists>i j. B = dneq f i j \<and> i \<noteq> j)"
  by (auto simp: Ineq.simps)

text \<open>Every finite part of the scheme is satisfied by a large-enough finite model,
  hence consistent, and by compactness so is the whole scheme.  The finite model is
  constructed @{emph \<open>once\<close>}, in the separation section below, where the very same model
  also refutes the Dedekind axiom; the consistency theorems \<open>con_finite_sub\<close>, \<open>con_Ineq\<close>
  and \<open>con_Ineq_fprov\<close> are stated there.\<close>

section \<open>The Dedekind axiom of infinity\<close>

text \<open>A single axiom of infinity in the sense of Dedekind: some self-map \<open>F\<close> of the
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

lemma pars_DInf: "pars (DInf :: 'p tm) = {}"
  by (simp add: DInf_def InjBody_def NsBody_def ImpBody_def NsAtom_def EqFXFY_def
      EqXY_def AndB_def ExN_def AllN_def Forall_def ImpB_def vdefs)
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

subsection \<open>The axiom derives every finite cardinality\<close>

text \<open>The constant-free first-order sentences ``there are at least \<open>n\<close> individuals'',
  \<open>\<^bold>\<exists>x\<^sub>1 \<dots> \<^bold>\<exists>x\<^sub>n. \<And>\<^sub>i\<^sub><\<^sub>j \<^bold>\<not> (x\<^sub>i \<^bold>= x\<^sub>j)\<close>, are derivable from \<open>DInf\<close> inside \<open>NK\<close>: the
  witnesses are \<open>C, F C, F (F C), \<dots>\<close> for the self-map \<open>F\<close> and the point \<open>C\<close> outside its
  range, and their pairwise distinctness follows from injectivity by induction.  The
  derivation is built by meta-level recursion on \<open>n\<close>, one \<open>NK\<close>-derivation for each \<open>n\<close>.
  These sentences are the standard first-order axiomatisation of infinity; the inequation
  scheme derives them too (\<open>Ineq_derives_distinct_n\<close>, below), and so does the axiom.\<close>

text \<open>The sentences.  \<open>AllNeq t ss\<close> says that \<open>t\<close> differs from every member of \<open>ss\<close>,
  \<open>Distinct ts\<close> that the members of \<open>ts\<close> are pairwise distinct, and \<open>ExD ts vs\<close> binds the
  variables \<open>vs\<close> existentially in front of \<open>Distinct (ts @ vs)\<close>.  The variable names
  \<open>vD i\<close> are kept apart from the names \<open>vF, \<dots>, vZ\<close> used in \<open>DInf\<close>.\<close>

primrec AllNeq :: "'p tm \<Rightarrow> 'p tm list \<Rightarrow> 'p tm" where
  "AllNeq t [] = \<^bold>\<top>"
| "AllNeq t (s # ss) = (\<^bold>\<not> (t \<^bold>=\<^bsub>\<iota>\<^esub> s)) \<^bold>\<and> AllNeq t ss"

primrec Distinct :: "'p tm list \<Rightarrow> 'p tm" where
  "Distinct [] = \<^bold>\<top>"
| "Distinct (t # ts) = AllNeq t ts \<^bold>\<and> Distinct ts"

primrec ExD :: "'p tm list \<Rightarrow> nat list \<Rightarrow> 'p tm" where
  "ExD ts [] = Distinct ts"
| "ExD ts (v # vs) = \<^bold>\<exists>v\<^bsub>\<iota>\<^esub>. ExD (ts @ [v\<^sup>f\<^bsub>\<iota>\<^esub>]) vs"

definition vD :: "nat \<Rightarrow> nat" where "vD i = 10 + i"

definition ExDistinct :: "nat \<Rightarrow> 'p tm" where
  "ExDistinct n = ExD [] (map vD [0..<n])"

lemma wff_AllNeq: "wff\<^bsub>\<iota>\<^esub>(t) \<Longrightarrow> \<forall>s \<in> set ss. wff\<^bsub>\<iota>\<^esub>(s) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(AllNeq t ss)"
  by (induction ss) (auto intro: wff_AndB wff_Not wff_PEq)

lemma wff_Distinct: "\<forall>t \<in> set ts. wff\<^bsub>\<iota>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(Distinct ts)"
  by (induction ts) (auto intro: wff_AndB wff_AllNeq)

lemma wff_ExD: "\<forall>t \<in> set ts. wff\<^bsub>\<iota>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(ExD ts vs)"
proof (induction vs arbitrary: ts)
  case Nil thus ?case by (simp add: wff_Distinct)
next
  case (Cons v vs)
  have "wff\<^bsub>\<o>\<^esub>(ExD (ts @ [v\<^sup>f\<^bsub>\<iota>\<^esub>]) vs)"
    by (rule Cons.IH) (use Cons.prems in \<open>auto intro: wff_Fre\<close>)
  thus ?case by (simp add: wff_ExN)
qed

lemma wff_ExDistinct: "wff\<^bsub>\<o>\<^esub>(ExDistinct n)"
  unfolding ExDistinct_def by (rule wff_ExD) simp

lemma fsub_AllNeq: "fsub x \<sigma> u (AllNeq t ss) = AllNeq (fsub x \<sigma> u t) (map (fsub x \<sigma> u) ss)"
  by (induction ss) auto

lemma fsub_Distinct: "fsub x \<sigma> u (Distinct ts) = Distinct (map (fsub x \<sigma> u) ts)"
  by (induction ts) (auto simp: fsub_AllNeq)

lemma fsub_ExD:
  "x \<notin> set vs \<Longrightarrow> fvs u = {} \<Longrightarrow> fsub x \<iota> u (ExD ts vs) = ExD (map (fsub x \<iota> u) ts) vs"
  by (induction vs arbitrary: ts) (auto simp: fsub_Distinct fsub_ExN)

lemma pars_AllNeq: "pars (AllNeq t ss) \<subseteq> pars t \<union> (\<Union>s \<in> set ss. pars s)"
  by (induction ss) (auto simp: AndB_def)

lemma pars_Distinct: "pars (Distinct ts) \<subseteq> (\<Union>t \<in> set ts. pars t)"
  by (induction ts) (auto simp: AndB_def dest: subsetD[OF pars_AllNeq])

lemma pars_ExD: "pars (ExD ts vs) \<subseteq> (\<Union>t \<in> set ts. pars t)"
proof (induction vs arbitrary: ts)
  case Nil thus ?case by (simp add: pars_Distinct)
next
  case (Cons v vs)
  have "pars (ExD ts (v # vs)) = pars (ExD (ts @ [v\<^sup>f\<^bsub>\<iota>\<^esub>]) vs)" by (simp add: ExN_def)
  also have "\<dots> \<subseteq> (\<Union>t \<in> set (ts @ [v\<^sup>f\<^bsub>\<iota>\<^esub>]). pars t)" by (rule Cons.IH)
  also have "\<dots> = (\<Union>t \<in> set ts. pars t)" by simp
  finally show ?case .
qed

lemma pars_ExDistinct: "pars (ExDistinct n) = {}"
  using pars_ExD[of "[]" "map vD [0..<n]"] by (simp add: ExDistinct_def)

text \<open>The witnesses \<open>F\<^sup>k C\<close>, as closed object terms over two parameters.\<close>

primrec itF :: "'p \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'p tm" where
  "itF F C 0 = C\<^sup>p\<^bsub>\<iota>\<^esub>"
| "itF F C (Suc k) = (F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> itF F C k"

lemma wff_itF [simp, intro]: "wff\<^bsub>\<iota>\<^esub>(itF F C k)"
  by (induction k) (auto intro: wff_Par wff_App)
lemma fvs_itF [simp]: "fvs (itF F C k) = {}"
  by (induction k) auto
lemma fsub_itF [simp]: "fsub x \<sigma> u (itF F C k) = itF F C k"
  by (rule fsub_notin) simp

text \<open>Pairwise distinctness assembled into the sentence \<open>Distinct\<close>, for any family of
  closed witnesses whose members below a bound \<open>N\<close> are provably distinct.\<close>

lemma AllNeq_family:
  assumes fp: "freep \<Phi>" and wt: "\<And>k. wff\<^bsub>\<iota>\<^esub>(t k)"
    and neq: "\<And>i j. i < j \<Longrightarrow> j < N \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<not> (t i \<^bold>=\<^bsub>\<iota>\<^esub> t j)"
  shows "\<forall>j \<in> set js. i < j \<and> j < N \<Longrightarrow> \<Phi> \<turnstile> AllNeq (t i) (map t js)"
proof (induction js)
  case Nil show ?case by (simp add: bprov_TrueB)
next
  case (Cons j js)
  have ij: "i < j" "j < N" and rest: "\<forall>j \<in> set js. i < j \<and> j < N" using Cons.prems by auto
  show ?case unfolding list.map AllNeq.simps
    by (rule AndI[OF neq[OF ij] Cons.IH[OF rest] _ _ fp])
       (auto del: wff_Not wff_PEq intro!: wff_AllNeq wff_Not wff_PEq wff_Eq wff_App wff_Par wt)
qed

lemma Distinct_family:
  assumes fp: "freep \<Phi>" and wt: "\<And>k. wff\<^bsub>\<iota>\<^esub>(t k)"
    and neq: "\<And>i j. i < j \<Longrightarrow> j < N \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<not> (t i \<^bold>=\<^bsub>\<iota>\<^esub> t j)"
  shows "i + m \<le> N \<Longrightarrow> \<Phi> \<turnstile> Distinct (map t [i..<i + m])"
proof (induction m arbitrary: i)
  case 0 show ?case by (simp add: bprov_TrueB)
next
  case (Suc m)
  have e: "[i..<i + Suc m] = i # [Suc i..<Suc i + m]"
    using upt_conv_Cons[of i "i + Suc m"] by simp
  show ?case unfolding e list.map Distinct.simps
    by (rule AndI[OF AllNeq_family[OF fp wt neq] Suc.IH _ _ fp])
       (use Suc.prems in \<open>auto intro!: wff_AllNeq wff_Distinct wt\<close>)
qed

text \<open>The derivation, from the two witnessed halves of \<open>DInf\<close>: injectivity of \<open>F\<close> and the
  point \<open>C\<close> outside its range.\<close>

context
  fixes F C :: "'p::infinite" and \<Phi> :: "'p tm set"
  assumes fp: "freep \<Phi>"
    and inj: "\<Phi> \<turnstile> \<^bold>\<Pi>vX\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>.
                 ((((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> ((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
                  \<^bold>\<supset> ((vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))"
    and ns: "\<Phi> \<turnstile> \<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. \<^bold>\<not> (((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (C\<^sup>p\<^bsub>\<iota>\<^esub>))"
begin

lemma inj_inst:
  "\<Phi> \<turnstile> (itF F C (Suc i) \<^bold>=\<^bsub>\<iota>\<^esub> itF F C (Suc j)) \<^bold>\<supset> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> itF F C j)"
proof -
  have 1: "\<Phi> \<turnstile> fsub vX \<iota> (itF F C i) (\<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>.
                 ((((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> ((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
                  \<^bold>\<supset> ((vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>))))"
    by (rule AllN_E[OF inj _ wff_itF])
       (auto del: wff_ImpB wff_PEq
             intro!: wff_AllN wff_ImpB wff_PEq wff_Eq wff_App wff_Par wff_Fre)
  have 2: "\<Phi> \<turnstile> \<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>.
                 ((((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> itF F C i) \<^bold>=\<^bsub>\<iota>\<^esub> ((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
                  \<^bold>\<supset> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))"
    using 1 by (simp add: fsub_AllN vdefs)
  have 3: "\<Phi> \<turnstile> fsub vY \<iota> (itF F C j)
                 ((((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> itF F C i) \<^bold>=\<^bsub>\<iota>\<^esub> ((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
                  \<^bold>\<supset> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))"
    by (rule AllN_E[OF 2 _ wff_itF])
       (auto del: wff_ImpB wff_PEq intro!: wff_ImpB wff_PEq wff_Eq wff_App wff_Par wff_Fre)
  thus ?thesis by (simp add: vdefs)
qed

lemma ns_inst: "\<Phi> \<turnstile> \<^bold>\<not> (itF F C (Suc k) \<^bold>=\<^bsub>\<iota>\<^esub> itF F C 0)"
proof -
  have "\<Phi> \<turnstile> fsub vZ \<iota> (itF F C k) (\<^bold>\<not> (((F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>) \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (C\<^sup>p\<^bsub>\<iota>\<^esub>)))"
    by (rule AllN_E[OF ns _ wff_itF])
       (auto del: wff_Not wff_PEq intro!: wff_Not wff_PEq wff_Eq wff_App wff_Par wff_Fre)
  thus ?thesis by (simp add: vdefs)
qed

lemma neq_itF: "i < j \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<not> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> itF F C j)"
proof (induction i arbitrary: j)
  case 0
  then obtain k where j: "j = Suc k" by (cases j) auto
  show ?case unfolding j by (rule peq_neg_sym[OF ns_inst fp wff_itF wff_itF])
next
  case (Suc i)
  then obtain k where j: "j = Suc k" and ik: "i < k" by (cases j) auto
  let ?E = "itF F C (Suc i) \<^bold>=\<^bsub>\<iota>\<^esub> itF F C (Suc k)"
  have fp': "freep (\<Phi> \<union> {?E})" by (rule freep_un[OF fp])
  have imp: "\<Phi> \<union> {?E} \<turnstile> ?E \<^bold>\<supset> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> itF F C k)"
    by (rule bprov_weaken[OF inj_inst]) (auto simp: freep_add fp)
  have hyp: "\<Phi> \<union> {?E} \<turnstile> ?E" by (auto intro: bprov.Hyp)
  have p: "\<Phi> \<union> {?E} \<turnstile> itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> itF F C k"
    by (rule bprov_ImpE[OF imp hyp fp'])
       (auto del: wff_PEq intro!: wff_PEq wff_Eq wff_App wff_Par)
  have n: "\<Phi> \<union> {?E} \<turnstile> \<^bold>\<not> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> itF F C k)"
    by (rule bprov_weaken[OF Suc.IH[OF ik]]) (auto simp: freep_add fp)
  have "\<Phi> \<union> {?E} \<turnstile> \<^bold>\<bottom>" by (rule bprov.NegE[OF n p wff_FalseB])
  thus ?case unfolding j by (rule bprov.NegI[OF _ wff_PEq[OF wff_itF wff_itF]])
qed

lemma Distinct_itF: "\<Phi> \<turnstile> Distinct (map (itF F C) [0..<n])"
proof -
  have neq: "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<not> (itF F C i \<^bold>=\<^bsub>\<iota>\<^esub> itF F C j)"
    by (rule neq_itF)
  show ?thesis using Distinct_family[OF fp wff_itF neq, where i = 0 and m = n] by simp
qed

end

text \<open>Existential closure: from the distinctness of closed witnesses to the sentence.\<close>

lemma ExD_I:
  assumes d: "\<Phi> \<turnstile> Distinct (ts @ us)" and fp: "freep \<Phi>"
    and cts: "\<forall>t \<in> set ts. wff\<^bsub>\<iota>\<^esub>(t) \<and> fvs t = {}"
    and cus: "\<forall>u \<in> set us. wff\<^bsub>\<iota>\<^esub>(u) \<and> fvs u = {}"
    and len: "length us = length vs" and dv: "distinct vs"
  shows "\<Phi> \<turnstile> ExD ts vs"
  using d cts cus len dv
proof (induction vs arbitrary: ts us)
  case Nil thus ?case by simp
next
  case (Cons v vs)
  obtain u us' where us: "us = u # us'" using Cons.prems(4) by (cases us) auto
  have IH: "\<Phi> \<turnstile> ExD (ts @ [u]) vs"
    by (rule Cons.IH) (use Cons.prems us in auto)
  have wb: "wff\<^bsub>\<o>\<^esub>(ExD (ts @ [v\<^sup>f\<^bsub>\<iota>\<^esub>]) vs)"
    by (rule wff_ExD) (use Cons.prems(2) in \<open>auto intro: wff_Fre\<close>)
  have m: "map (fsub v \<iota> u) ts = ts"
    using Cons.prems(2) by (auto intro!: map_idI simp: fsub_notin)
  have sub: "fsub v \<iota> u (ExD (ts @ [v\<^sup>f\<^bsub>\<iota>\<^esub>]) vs) = ExD (ts @ [u]) vs"
    using Cons.prems(3,5) us by (simp add: fsub_ExD m)
  show ?case unfolding ExD.simps
    by (rule ExN_I[OF IH[folded sub] wb _ fp]) (use Cons.prems(3) us in auto)
qed

theorem DInf_derives_distinct_n: "{DInf :: 'p::infinite tm} \<turnstile> ExDistinct n"
proof -
  obtain F C :: 'p where FC: "F \<noteq> C"
    by (metis (full_types) ex_new_if_finite finite.emptyI
        finite.insertI infinite_UNIV insert_iff)
  note CF = FC[symmetric]
  let ?FP = "F\<^sup>p\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> :: 'p tm" and ?CP = "C\<^sup>p\<^bsub>\<iota>\<^esub> :: 'p tm"
  define InjF :: "'p tm" where
    "InjF = \<^bold>\<Pi>vX\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>. (((?FP \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (?FP \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
                              \<^bold>\<supset> ((vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))"
  define NsB :: "'p tm" where "NsB = \<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. \<^bold>\<not> ((?FP \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (vC\<^sup>f\<^bsub>\<iota>\<^esub>))"
  define NsC :: "'p tm" where "NsC = \<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. \<^bold>\<not> ((?FP \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> ?CP)"
  \<comment> \<open>the two substitution instances\<close>
  have subF: "fsub vF (\<iota> \<^bold>\<Rightarrow> \<iota>) ?FP (InjBody \<^bold>\<and> NsBody) = InjF \<^bold>\<and> (\<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. NsB)"
    by (simp add: InjF_def NsB_def InjBody_def NsBody_def ImpBody_def NsAtom_def
        EqFXFY_def EqXY_def fsub_AllN fsub_ExN vdefs)
  have subC: "fsub vC \<iota> ?CP NsB = NsC"
    by (simp add: NsB_def NsC_def fsub_AllN vdefs)
  \<comment> \<open>well-formedness and parameters\<close>
  have wInjF: "wff\<^bsub>\<o>\<^esub>(InjF)" unfolding InjF_def
    by (auto del: wff_ImpB wff_PEq
             intro!: wff_AllN wff_ImpB wff_PEq wff_Eq wff_App wff_Par wff_Fre)
  have wNsB: "wff\<^bsub>\<o>\<^esub>(NsB)" unfolding NsB_def
    by (auto del: wff_Not wff_PEq
             intro!: wff_AllN wff_Not wff_PEq wff_Eq wff_App wff_Par wff_Fre)
  have wExNsB: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. NsB)" by (rule wff_ExN[OF wNsB])
  have wBody: "wff\<^bsub>\<o>\<^esub>(InjBody \<^bold>\<and> NsBody :: 'p tm)" by (rule wff_AndB[OF wff_InjBody wff_NsBody])
  have pBody: "pars (InjBody \<^bold>\<and> NsBody :: 'p tm) = {}"
    by (simp add: InjBody_def NsBody_def ImpBody_def NsAtom_def EqFXFY_def EqXY_def
        AndB_def ExN_def AllN_def)
  have pInjF: "pars InjF = {F}" by (simp add: InjF_def AllN_def)
  have pNsB: "pars NsB = {F}" by (simp add: NsB_def AllN_def)
  \<comment> \<open>the contexts\<close>
  let ?\<Phi>1 = "{DInf :: 'p tm} \<union> {InjF \<^bold>\<and> (\<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. NsB)}"
  let ?\<Phi>2 = "?\<Phi>1 \<union> {NsC}"
  have fp0: "freep {DInf :: 'p tm}" and fp1: "freep ?\<Phi>1" and fp2: "freep ?\<Phi>2"
    by (intro freep_finite; simp)+
  \<comment> \<open>inside the innermost context: the two halves, and the derivation\<close>
  have and2: "?\<Phi>2 \<turnstile> InjF \<^bold>\<and> (\<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. NsB)" by (auto intro: bprov.Hyp)
  have inj2: "?\<Phi>2 \<turnstile> InjF" by (rule AndE1[OF and2 wInjF wExNsB fp2])
  have ns2: "?\<Phi>2 \<turnstile> NsC" by (auto intro: bprov.Hyp)
  have inj2': "?\<Phi>2 \<turnstile> \<^bold>\<Pi>vX\<^bsub>\<iota>\<^esub>. \<^bold>\<Pi>vY\<^bsub>\<iota>\<^esub>. (((?FP \<^bold>\<cdot> (vX\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> (?FP \<^bold>\<cdot> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))
                              \<^bold>\<supset> ((vX\<^sup>f\<^bsub>\<iota>\<^esub>) \<^bold>=\<^bsub>\<iota>\<^esub> (vY\<^sup>f\<^bsub>\<iota>\<^esub>)))"
    using inj2 by (simp add: InjF_def)
  have ns2': "?\<Phi>2 \<turnstile> \<^bold>\<Pi>vZ\<^bsub>\<iota>\<^esub>. \<^bold>\<not> ((?FP \<^bold>\<cdot> (vZ\<^sup>f\<^bsub>\<iota>\<^esub>)) \<^bold>=\<^bsub>\<iota>\<^esub> ?CP)"
    using ns2 by (simp add: NsC_def)
  have d: "?\<Phi>2 \<turnstile> Distinct (map (itF F C) [0..<n])"
    by (rule Distinct_itF[OF fp2 inj2' ns2'])
  have main: "?\<Phi>2 \<turnstile> ExDistinct n"
    unfolding ExDistinct_def
  proof (rule ExD_I[OF _ fp2])
    show "?\<Phi>2 \<turnstile> Distinct ([] @ map (itF F C) [0..<n])" using d by simp
    show "distinct (map vD [0..<n])" by (simp add: distinct_map inj_on_def vD_def)
  qed simp_all
  \<comment> \<open>discharge the witness \<open>C\<close>\<close>
  have ex1: "?\<Phi>1 \<turnstile> \<^bold>\<exists>vC\<^bsub>\<iota>\<^esub>. NsB"
    by (rule AndE2[OF _ wInjF wExNsB fp1]) (auto intro: bprov.Hyp)
  have h1: "?\<Phi>1 \<turnstile> ExDistinct n"
    by (rule ExN_E[OF ex1 main[folded subC] wNsB wff_ExDistinct _ _ _ fp1])
       (simp_all add: pNsB pInjF pars_DInf pars_ExDistinct AndB_def ExN_def CF)
  \<comment> \<open>discharge the witness \<open>F\<close>\<close>
  have ex0: "{DInf :: 'p tm} \<turnstile> \<^bold>\<exists>vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>. (InjBody \<^bold>\<and> NsBody)"
    using bprov.Hyp[of "DInf :: 'p tm" "{DInf}"] unfolding DInf_def by simp
  show ?thesis
    by (rule ExN_E[OF ex0 h1[folded subF] wBody wff_ExDistinct _ _ _ fp0])
       (simp_all add: pBody pars_DInf pars_ExDistinct)
qed

subsection \<open>Injectivity and non-surjectivity in an arbitrary general model\<close>

text \<open>These facts hold in \<^emph>\<open>any\<close> \<open>\<Sigma>\<close>-Henkin general model --- fullness of the function
  domains is never used: they peel \<open>InjBody\<close> / \<open>NsBody\<close> down
  to injectivity and non-surjectivity of a self-map \<open>d\<close> on the individuals.  Only the
  witness for such a \<open>d\<close> is model-specific, so \<open>DInf_sat\<close> takes that data as hypotheses,
  and the consistency arguments about \<open>DInf\<close>, here and in the companion development,
  share this carrier-generic core.  Conversely, \<open>DInf_sat_Dedekind_infinite\<close> extracts
  from satisfaction of \<open>DInf\<close> an injective, non-surjective self-map of the individual
  domain: even in a Henkin model, the axiom forces Dedekind infinitude of \<open>\<D>\<^bsub>\<iota>\<^esub>\<close>.\<close>

context general_model
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

lemma DInf_sat_Dedekind_infinite:
  assumes xi: "bkkA.asg \<xi>" and sat: "den DInf \<xi> = Tv"
  shows "\<exists>d. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d
           \<and> (\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b)))
           \<and> (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c))"
proof -
  have unf: "(den DInf \<xi> = Tv)
      = (\<exists>e. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) e \<and> den (InjBody \<^bold>\<and> NsBody) (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := e)) = Tv)"
    unfolding DInf_def by (rule sat_ExN[OF wff_AndB[OF wff_InjBody wff_NsBody] xi])
  from sat unf obtain e where e: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) e"
      and cj: "den (InjBody \<^bold>\<and> NsBody) (\<xi>(vF\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub> := e)) = Tv" by auto
  have inj: "\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (e \<^bold>@ a = e \<^bold>@ b \<longrightarrow> a = b))"
    and ns: "\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> e \<^bold>@ z \<noteq> c)"
    using cj sat_AndB[OF wff_InjBody wff_NsBody bkkA.asg_upd[OF xi e]]
          InjSat[OF xi e] NsSat[OF xi e] by simp_all
  show ?thesis using e inj ns by blast
qed

end

section \<open>Consistency of the scheme, and its separation from the axiom\<close>

text \<open>The scheme does not yield the axiom.  Every general model with @{emph \<open>finitely\<close>} many individuals refutes \<open>DInf\<close>
  --- an injective self-map of a finite set is surjective --- while a large enough finite
  standard model satisfies any finite part of the scheme.  Hence the scheme together with \<open>\<^bold>\<not> DInf\<close> is consistent,
  no finite part of \<open>Ineq f\<close> derives \<open>DInf\<close> (\<open>\<not> (Ineq f \<tturnstile> DInf)\<close>), and a Henkin
  model of the whole scheme, countable over a countable signature, refutes the axiom,
  making the separation model-theoretic.  All of this stays
  in plain HOL: the refuting models are the finite ones from \<open>Consistency\<close>, and the Henkin
  model is the term model of \<open>Completeness\<close>.  Conversely, \<open>DInf\<close> mentions no constants, so
  once a model of it exists, one in which all constants coincide refutes every inequation;
  the companion notes this in passing.  This separation rests on the auxiliary constants of the scheme: \<open>DInf\<close> derives,
  for every \<open>n\<close>, the existence of \<open>n\<close> pairwise distinct individuals
  (@{thm [source] DInf_derives_distinct_n}), so every constant-free consequence of a finite
  part of the scheme is a consequence of \<open>DInf\<close> (the remaining step, replacing the
  constants of a derivation by terms, is not formalised here); and
  over standard models the whole scheme entails \<open>DInf\<close>, since an infinite individual domain
  with full function spaces has an injective, non-surjective self-map (not formalised here
  either).  What the scheme cannot supply is that self-map as an element of \<open>\<D>\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>\<close>,
  and that is where its Henkin models refute the axiom.\<close>

context general_model
begin

text \<open>The two directions combined: in any general model, \<open>DInf\<close> holds exactly when the
  function domain \<open>\<D>\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>\<close> contains an injective, non-surjective self-map of the
  individuals.  In a standard model, where that domain is full, this is Dedekind
  infinitude of \<open>\<D>\<^bsub>\<iota>\<^esub>\<close>; in a Henkin model the domain may lack the self-map.\<close>

lemma DInf_sat_iff:
  assumes xi: "bkkA.asg \<xi>"
  shows "(den DInf \<xi> = Tv)
       = (\<exists>d. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d
              \<and> (\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (d \<^bold>@ a = d \<^bold>@ b \<longrightarrow> a = b)))
              \<and> (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> d \<^bold>@ z \<noteq> c)))"
  using DInf_sat[OF xi] DInf_sat_Dedekind_infinite[OF xi] by blast

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
        using gm_appTy[OF d] by auto
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
  interpretation distinguishing the finitely many constants of the scheme at hand.  The
  construction happens @{emph \<open>once\<close>}: the same model satisfies the fragment and refutes
  the axiom, and the plain consistency of the scheme falls out by monotonicity below.\<close>

lemma con_DInf_neg_finite_sub:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
      and finF: "finite F" and FI: "F \<subseteq> Ineq f"
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
    then have "B \<in> Ineq f" using FI by blast
    then obtain i j where B: "B = dneq f i j" and ne: "i \<noteq> j"
      by (auto simp: Ineq_iff)
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
  finite parts of the scheme --- the compactness argument announced above --- and
  compactness the consistency of the whole scheme.\<close>

lemma con_finite_sub:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
      and finF: "finite F" and FI: "F \<subseteq> Ineq f"
  shows "con F"
proof -
  have "con (insert (\<^bold>\<not> DInf) F)" by (rule con_DInf_neg_finite_sub[OF assms])
  moreover have "F \<subseteq> insert (\<^bold>\<not> DInf) F" by auto
  moreover have "freep (insert (\<^bold>\<not> DInf) F)"
    by (rule freep_finite) (simp add: finF)
  ultimately show ?thesis by (rule con_mono)
qed

theorem con_Ineq:
  assumes "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "con (Ineq f)"
  by (rule con_compact) (rule con_finite_sub[OF assms])

text \<open>A caveat on \<open>con\<close> for an impure infinite context.  \<open>\<turnstile>\<close> derives from the whole
  context, and \<open>NK(\<Pi>I)\<close> needs an eigen-parameter that occurs nowhere in it.  If \<open>f\<close> uses
  every parameter (\<open>'p = \<nat>\<close>, \<open>f\<close> surjective), no such parameter exists, and
  \<open>con (Ineq f)\<close> then holds partly because generalisation is blocked.  The proviso that
  infinitely many parameters remain unused is BKK's ``sufficiently \<open>\<Sigma>\<close>-pure'' (BKK
  Definition 6.3).  The statement free of this effect is the one for Andrews' finitary
  consequence \<open>\<tturnstile>\<close>: no finite part of the scheme derives falsity, which is
  @{thm [source] con_finite_sub} restated through @{thm [source] fprov_con}.\<close>

theorem con_Ineq_fprov:
  assumes "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "\<not> (Ineq f \<tturnstile> (\<^bold>\<bottom> :: 'p tm))"
  unfolding fprov_con by (blast intro: con_finite_sub[OF assms])

text \<open>Thus \<open>NK\<close> is consistent with the inequation scheme, for every
  injective constant family \<open>f\<close>.  The scheme \<open>Ineq f\<close> forces \<open>\<D>\<^sub>\<iota>\<close> to be infinite in
  every model of the whole scheme, since it makes the denotations of the constants \<open>f i\<close>
  pairwise distinct (an immediate consequence, not stated as a lemma).\<close>

theorem con_Ineq_not_DInf:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "con (insert (\<^bold>\<not> DInf) (Ineq f))"
proof (rule con_compact)
  fix F' :: "'p tm set"
  assume finF': "finite F'" and sub': "F' \<subseteq> insert (\<^bold>\<not> DInf) (Ineq f)"
  have "con (insert (\<^bold>\<not> DInf) (F' - {\<^bold>\<not> DInf}))"
    by (rule con_DInf_neg_finite_sub[OF injf]) (use finF' sub' in auto)
  moreover have "F' \<subseteq> insert (\<^bold>\<not> DInf) (F' - {\<^bold>\<not> DInf})" by auto
  moreover have "freep (insert (\<^bold>\<not> DInf) (F' - {\<^bold>\<not> DInf}))"
    by (rule freep_finite) (simp add: finF')
  ultimately show "con F'" by (rule con_mono)
qed

theorem Ineq_not_derives_DInf:
  assumes injf: "inj (f :: nat \<Rightarrow> 'p::infinite)"
  shows "\<not> (Ineq f \<tturnstile> (DInf :: 'p tm))"
proof
  assume "Ineq f \<tturnstile> (DInf :: 'p tm)"
  then obtain F where finF: "finite F" and FI: "F \<subseteq> Ineq f"
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

subsection \<open>The constant-free sentences and the scheme\<close>

text \<open>The scheme derives every constant-free sentence \<open>ExDistinct n\<close>: the first \<open>n\<close>
  constants are the witnesses, and their inequations are hypotheses.\<close>

theorem Ineq_derives_distinct_n:
  fixes f :: "nat \<Rightarrow> 'p::infinite"
  shows "Ineq f \<tturnstile> ExDistinct n"
proof -
  let ?c = "\<lambda>i. (f i)\<^sup>p\<^bsub>\<iota>\<^esub> :: 'p tm"
  define F where "F = (\<lambda>(i, j). dneq f i j) ` {(i, j). i < j \<and> j < n}"
  have "{(i, j). i < j \<and> j < n} \<subseteq> {0..<n} \<times> {0..<n}" by auto
  hence finF: "finite F" unfolding F_def by (blast intro: finite_imageI finite_subset)
  have FI: "F \<subseteq> Ineq f" unfolding F_def by (auto intro: Ineq_I)
  have fpF: "freep F" by (rule freep_finite[OF finF])
  have neq: "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> F \<turnstile> \<^bold>\<not> (?c i \<^bold>=\<^bsub>\<iota>\<^esub> ?c j)"
    by (rule bprov.Hyp) (force simp: F_def dneq_def)
  have wc: "\<And>k. wff\<^bsub>\<iota>\<^esub>(?c k)" by (simp add: wff_Par)
  have d: "F \<turnstile> Distinct (map ?c [0..<n])"
    using Distinct_family[OF fpF wc neq, where i = 0 and m = n] by simp
  have "F \<turnstile> ExDistinct n"
    unfolding ExDistinct_def
  proof (rule ExD_I[OF _ fpF])
    show "F \<turnstile> Distinct ([] @ map ?c [0..<n])" using d by simp
    show "distinct (map vD [0..<n])" by (simp add: distinct_map inj_on_def vD_def)
  qed (simp_all add: wff_Par)
  thus ?thesis by (rule fprovI[OF finF FI])
qed

text \<open>Hence the constant-free sentences do not derive the axiom either: a derivation
  from finitely many of them would, by cut, be a derivation from a finite part of the
  scheme.  As a first-order axiomatisation of infinity, \<open>{ExDistinct n | n}\<close> is thus
  strictly weaker than \<open>DInf\<close> in \<open>NK\<close> (the converse derivations are
  @{thm [source] DInf_derives_distinct_n}).  Over standard models the two are
  equivalent, since an infinite individual domain with a full function space has an
  injective, non-surjective self-map; this last step is not formalised.  The Henkin
  countermodel of the next subsection satisfies all \<open>ExDistinct n\<close> and refutes \<open>DInf\<close>.\<close>

lemma distinct_scheme_fprov_Ineq:
  fixes f :: "nat \<Rightarrow> 'p::infinite"
  assumes A: "range ExDistinct \<tturnstile> (A :: 'p tm)" and wA: "wff\<^bsub>\<o>\<^esub>(A)"
  shows "Ineq f \<tturnstile> A"
proof -
  from A obtain \<Lambda> where fin\<Lambda>: "finite \<Lambda>" and \<Lambda>I: "\<Lambda> \<subseteq> range ExDistinct"
      and \<Lambda>A: "\<Lambda> \<turnstile> A"
    by (auto simp: fprov_def)
  have "\<forall>B \<in> \<Lambda>. \<exists>G. finite G \<and> G \<subseteq> Ineq f \<and> G \<turnstile> B"
    using \<Lambda>I Ineq_derives_distinct_n[where f = f] by (auto simp: fprov_def)
  then obtain G where G: "\<And>B. B \<in> \<Lambda> \<Longrightarrow> finite (G B) \<and> G B \<subseteq> Ineq f \<and> G B \<turnstile> B"
    by metis
  define F where "F = (\<Union>B \<in> \<Lambda>. G B)"
  have finF: "finite F" unfolding F_def using fin\<Lambda> G by auto
  have FI: "F \<subseteq> Ineq f" unfolding F_def using G by auto
  have fpF: "freep F" by (rule freep_finite[OF finF])
  have w\<Lambda>: "\<And>B. B \<in> \<Lambda> \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B)" using \<Lambda>I wff_ExDistinct by auto
  have FA: "F \<union> \<Lambda> \<turnstile> A"
    by (rule bprov_weaken[OF \<Lambda>A]) (auto simp: freep_finite finF fin\<Lambda>)
  have FB: "F \<turnstile> B" if B: "B \<in> \<Lambda>" for B
  proof -
    have "G B \<turnstile> B" and "G B \<subseteq> F" using G[OF B] B by (auto simp: F_def)
    thus ?thesis by (rule bprov_weaken[OF _ _ fpF])
  qed
  have "F \<turnstile> A" by (rule bprov_cut_set[OF fin\<Lambda> FA FB w\<Lambda> wA fpF])
  thus ?thesis by (rule fprovI[OF finF FI])
qed

theorem distinct_scheme_not_derives_DInf:
  "\<not> (range (ExDistinct :: nat \<Rightarrow> 'p::infinite tm) \<tturnstile> DInf)"
proof
  assume h: "range (ExDistinct :: nat \<Rightarrow> 'p tm) \<tturnstile> DInf"
  obtain f :: "nat \<Rightarrow> 'p" where injf: "inj f"
    using infinite_UNIV infinite_countable_subset by blast
  have "Ineq f \<tturnstile> (DInf :: 'p tm)"
    by (rule distinct_scheme_fprov_Ineq[OF h wff_DInf])
  thus False using Ineq_not_derives_DInf[OF injf] by simp
qed

text \<open>Consistency of the constant-free sentences themselves, by the same reduction: no finite
  part of \<open>{ExDistinct n | n}\<close> derives falsity.  The finite models of \<open>Consistency\<close> of size
  \<open>k\<close> satisfy \<open>ExDistinct n\<close> for every \<open>n \<le> k\<close>, so the sentences need no auxiliary
  constants at all; the route through the scheme is a convenience of the formalisation.\<close>

theorem con_distinct_scheme:
  "\<not> (range (ExDistinct :: nat \<Rightarrow> 'p::infinite tm) \<tturnstile> \<^bold>\<bottom>)"
proof
  assume h: "range (ExDistinct :: nat \<Rightarrow> 'p tm) \<tturnstile> \<^bold>\<bottom>"
  obtain f :: "nat \<Rightarrow> 'p" where injf: "inj f"
    using infinite_UNIV infinite_countable_subset by blast
  have "Ineq f \<tturnstile> (\<^bold>\<bottom> :: 'p tm)"
    by (rule distinct_scheme_fprov_Ineq[OF h wff_FalseB])
  thus False using con_Ineq_fprov[OF injf] by simp
qed

subsection \<open>The Henkin countermodel\<close>

text \<open>The model-theoretic side of the separation: a general model of the @{emph \<open>whole\<close>}
  scheme in which \<open>DInf\<close> fails --- the refuting term model of \<open>Completeness\<close>, applied to
  \<open>Ineq f\<close> and \<open>DInf\<close>.  The term-model construction needs the context to be parameter-rich
  (\<open>richp\<close>, BKK Definition 6.3 scaled to the size of the signature), which here means that the parameters left unused by the
  family \<open>f\<close> are as numerous as the signature.  This is a condition of the construction only,
  and it is discharged below: any injective family is renamed into one with such a reserve
  (@{thm [source] signature_fold}), and the model obtained there is pulled back along the
  renaming (@{thm [source] bkk_model_reduct}), which fixes the pure sentence \<open>DInf\<close>.\<close>

lemma henkin_scheme_refutes_DInf_reserve:
  fixes f :: "nat \<Rightarrow> 'p::infinite"
  assumes injf: "inj f" and res: "|UNIV :: 'p set| \<le>o |- range f|"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
  where "bkk_model Dm Ap Ee vl" "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "\<forall>B\<in>Ineq f. vl (Ee \<xi> B)" "\<not> vl (Ee \<xi> (DInf :: 'p tm))"
proof -
  have nd: "\<not> (Ineq f \<turnstile> (DInf :: 'p tm))"
    using Ineq_not_derives_DInf[OF injf] bprov_fprov by blast
  have "usedp (Ineq f) \<subseteq> range f"
    by (auto simp: usedp_def Ineq_iff dneq_def)
  hence "- range f \<subseteq> - usedp (Ineq f)" by auto
  hence "|- range f| \<le>o |- usedp (Ineq f)|" by (rule card_of_mono1)
  hence fp: "richp (Ineq f)" unfolding richp_def using res ordLeq_transitive by blast
  have sen: "cwff \<o> B" if "B \<in> Ineq f" for B :: "'p tm"
  proof -
    have "\<exists>i j. B = dneq f i j \<and> i \<noteq> j" using that by (simp add: Ineq_iff)
    then obtain i j where B: "B = dneq f i j" by blast
    show ?thesis unfolding B dneq_def cwff_def
      by (auto intro!: wff_Not wff_PEq wff_Par)
  qed
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
      and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where "bkk_model Dm Ap Ee vl" and "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and "app_struct.asg Dm \<xi>" and "\<forall>B\<in>Ineq f. vl (Ee \<xi> B)"
      and "\<not> vl (Ee \<xi> (DInf :: 'p tm))"
    using refuting_term_model_hyps[OF cwff_DInf fp sen nd] .
  thus ?thesis by (rule that)
qed

text \<open>Renaming commutes with the inequations of the scheme and fixes the pure axiom.\<close>

lemma prn_dneq: "prn h (dneq f i j) = dneq (h \<circ> f) i j"
  by (simp add: dneq_def)

lemma prn_DInf: fixes h :: "'p \<Rightarrow> 'p" shows "prn h (DInf :: 'p tm) = DInf"
  using prn_cong[of "DInf :: 'p tm" h] by (simp add: pars_DInf)

text \<open>The separation theorem, for @{emph \<open>every\<close>} injective family over an infinite signature:
  the signature is folded injectively into one half of itself, the renamed family satisfies
  the reserve condition, and the reduct of its refuting model along the fold is a model of
  the original scheme.  The model satisfies every \<open>ExDistinct n\<close> as well --- its individual
  domain is infinite --- and refutes \<open>DInf\<close>.  Its total domain injects into the term type,
  so over a countable signature it is countable (@{thm [source] countable_of_inj_on_tm}).\<close>

theorem henkin_scheme_refutes_DInf:
  fixes f :: "nat \<Rightarrow> 'p::infinite"
  assumes injf: "inj f"
  obtains Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
    and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
  where "bkk_model Dm Ap Ee vl" "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}" "app_struct.asg Dm \<xi>"
        "\<forall>B\<in>Ineq f. vl (Ee \<xi> B)" "\<forall>n. vl (Ee \<xi> (ExDistinct n :: 'p tm))"
        "\<not> vl (Ee \<xi> (DInf :: 'p tm))"
proof -
  \<comment> \<open>fold the signature; the renamed family has a full-size reserve\<close>
  obtain h :: "'p \<Rightarrow> 'p" where injh: "inj h" and res_h: "|UNIV :: 'p set| \<le>o |- range h|"
    using signature_fold by blast
  define f' where "f' = h \<circ> f"
  have injf': "inj f'" unfolding f'_def using injh injf by (rule inj_compose)
  have res': "|UNIV :: 'p set| \<le>o |- range f'|"
  proof -
    have "- range h \<subseteq> - range f'" by (auto simp: f'_def)
    hence "|- range h| \<le>o |- range f'|" by (rule card_of_mono1)
    thus ?thesis using res_h ordLeq_transitive by blast
  qed
  obtain Dm Ap and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
      and vl \<xi> and rep :: "'p tm set \<Rightarrow> 'p tm"
    where M: "bkk_model Dm Ap Ee vl" and inj: "inj_on rep {x. \<exists>\<tau>. Dm \<tau> x}"
      and xi: "app_struct.asg Dm \<xi>" and sat: "\<forall>B\<in>Ineq f'. vl (Ee \<xi> B)"
      and nD: "\<not> vl (Ee \<xi> (DInf :: 'p tm))"
    using henkin_scheme_refutes_DInf_reserve[OF injf' res'] .
  \<comment> \<open>pull the model back along the fold\<close>
  define Ee' where "Ee' = (\<lambda>\<xi> t. Ee \<xi> (prn h t))"
  have M': "bkk_model Dm Ap Ee' vl" unfolding Ee'_def by (rule bkk_model_reduct[OF M])
  have sat': "\<forall>B\<in>Ineq f. vl (Ee' \<xi> B)"
  proof
    fix B assume "B \<in> Ineq f"
    then obtain i j' where B: "B = dneq f i j'" and ne: "i \<noteq> j'" by (auto simp: Ineq_iff)
    have "dneq f' i j' \<in> Ineq f'" using ne by (rule Ineq_I)
    thus "vl (Ee' \<xi> B)" using sat by (simp add: Ee'_def B prn_dneq f'_def)
  qed
  have nD': "\<not> vl (Ee' \<xi> (DInf :: 'p tm))" using nD by (simp add: Ee'_def prn_DInf)
  \<comment> \<open>the constant-free sentences hold, by soundness from their derivations\<close>
  have satn: "vl (Ee' \<xi> (ExDistinct n :: 'p tm))" for n
  proof -
    obtain G where GI: "G \<subseteq> Ineq f" and GD: "G \<turnstile> (ExDistinct n :: 'p tm)"
      using Ineq_derives_distinct_n[where f = f and n = n] by (auto simp: fprov_def)
    have wG: "\<forall>A\<in>G. wff\<^bsub>\<o>\<^esub>(A)" using GI by (auto simp: Ineq_iff wff_dneq dest!: subsetD)
    have sG: "\<forall>A\<in>G. vl (Ee' \<xi> A)" using GI sat' by blast
    show ?thesis by (rule soundness_bkk[OF GD M' xi wG sG])
  qed
  hence all: "\<forall>n. vl (Ee' \<xi> (ExDistinct n :: 'p tm))" by blast
  show ?thesis by (rule that[OF M' inj xi sat' all nD'])
qed

end
