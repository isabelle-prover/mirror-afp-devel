theory Syntax
  imports Main "HOL-Library.Countable"
begin

section \<open>Syntax: a deep embedding of HOL in HOL\<close>

text \<open>BKK's language of classical higher-order logic --- HOL, by which we mean
  Church's simple theory of types throughout (BKK Sections 2.1--2.2) --- in a @{emph \<open>locally
  nameless\<close>} representation: bound variables are de Bruijn indices, free variables
      and parameters carry their type.  BKK take alphabetic variants to be identical (BKK
  Section 2.1); locally nameless makes that literally true --- \<open>\<alpha>\<close>-equivalent terms are
  @{emph \<open>equal\<close>}, so capture-avoiding substitution and the entire renaming theory disappear.
  As in BKK, non-logical constants are @{emph \<open>parameters\<close>} with names drawn from a type \<open>'p\<close>, and
  we include BKK's optional primitive equality \<open>Eq \<sigma>\<close> (BKK Section 2.1, Remark 7.9),
  alongside the always-expressible defined Leibniz equality (BKK Section 2.2).
  Beyond BKK's signature we deliberately carry a family of description operators \<open>Iota \<sigma>\<close> of
  type \<open>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<close>, one for each type: BKK have no description operator (they decline to
  add one, BKK Section 2.3.1, pointing to Andrews 1972 for the semantic issues); we follow that
  reference instead and equip \<open>Iota \<sigma>\<close> with the description axiom for singletons --- the rule
  \<open>NK(\<iota>)\<close> of the calculus and the corresponding model condition \<open>gm_descB\<close>.  Definitions
      and lemmas below that carry no BKK
  reference are locally-nameless infrastructure (opening, closing, freshness, renaming): they
  have no counterpart in the paper, where identification of alphabetic variants is handled
  informally (BKK Section 2.1).\<close>

subsection \<open>Types and terms\<close>

datatype ty = Ind (\<open>\<iota>\<close>) | Bool (\<open>\<o>\<close>) | Fun ty ty (infixr \<open>\<^bold>\<Rightarrow>\<close> 65)

datatype (pars: 'p) tm =
    Bnd nat  \<comment> \<open>bound variable (de Bruijn index)\<close>
  | Fre nat ty  \<comment> \<open>free variable: a name and its type\<close>
  | Par 'p ty                            \<comment> \<open>parameter (typed constant)\<close>
  | Neg | Dis | Pi ty | Iota ty | Eq ty
      \<comment> \<open>logical constants \<open>\<^bold>\<not>, \<^bold>\<or>, \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub>, \<^bold>\<iota>\<^bsub>\<sigma>\<^esub>, \<^bold>=\<^bsub>\<sigma>\<^esub>\<close>\<close>
  | App "'p tm" "'p tm"  (infixl \<open>\<^bold>\<cdot>\<close> 200)
  | Abs ty "'p tm"    \<comment> \<open>abstraction, domain type annotated (BKK's \<open>\<lambda>X\<^bsub>\<sigma>\<^esub>. A\<close>; nameless, so no binder variable)\<close>
  for map: prn \<comment> \<open>We call the map function for the parameter type @{term prn} for parameter renaming.\<close>

text \<open>BKK write disjunctions in infix and negations in prefix notation (BKK Section 2.2
  declares the convention of writing \<open>((\<or>A)B)\<close> as \<open>A \<or> B\<close>); we mirror this with
  input/output abbreviations for the applied connectives.\<close>

text \<open>Abstraction is written \<open>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<close> for BKK's \<open>\<lambda>X\<^bsub>\<sigma>\<^esub>. A\<close> (bold \<open>\<Lambda>\<close>, since \<open>\<lambda>\<close>
  is reserved); being nameless, it displays the domain type but no binder variable.\<close>

notation Abs (\<open>\<^bold>\<Lambda>\<^bsub>_\<^esub> _\<close> [0, 200] 200)

text \<open>Decorated atoms: a free variable \<open>x\<close> of type \<open>\<sigma>\<close> is written \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> (BKK's
  \<open>X\<^bsub>\<sigma>\<^esub>\<close>), a parameter \<open>w\<close> is written \<open>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<close> (BKK's typed constants).\<close>

notation Fre (\<open>_\<^sup>f\<^bsub>_\<^esub>\<close> [1000, 0] 1000)
notation Par (\<open>_\<^sup>p\<^bsub>_\<^esub>\<close> [1000, 0] 1000)

abbreviation NegA :: "'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<not> _\<close> [66] 66) where
  "\<^bold>\<not> A \<equiv> Neg \<^bold>\<cdot> A"
abbreviation DisA :: "'p tm \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (infixr \<open>\<^bold>\<or>\<close> 61) where
  "A \<^bold>\<or> B \<equiv> (Dis \<^bold>\<cdot> A) \<^bold>\<cdot> B"

text \<open>Summary of the term notation and its BKK Section 2 counterparts: application
  \<open>s \<^bold>\<cdot> t\<close> (BKK juxtaposition), abstraction \<open>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<close>, free variables \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> (BKK's
  \<open>X\<^bsub>\<sigma>\<^esub>\<close>), parameters \<open>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<close> (typed constants), and the applied connectives \<open>\<^bold>\<not> A\<close> and
  \<open>A \<^bold>\<or> B\<close>.  The defined layer adds \<open>A \<^bold>\<supset> B\<close>, \<open>\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b\<close>, Leibniz equality \<open>A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B\<close> and applied
  primitive equality (below); opening is \<open>b\<^bold>\<langle>u\<^bold>\<rangle>\<close> (below); on the semantic side, \<open>\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>\<close> is
  the denotation and \<open>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<close> the assignment update (Section 2).\<close>

text \<open>Types and terms (over a countable parameter type) are countable, so the language of
  sentences can be enumerated --- the basis for our countable rendering of BKK's
  transfinite extension construction (BKK Section 6, Lemma 6.32).\<close>

instance ty :: countable by countable_datatype
instance tm :: (countable) countable by countable_datatype

subsection \<open>Opening and free-variable substitution\<close>

text \<open>\<open>opn\<^bsub>k\<^esub> u t\<close> replaces the bound index \<open>k\<close> in \<open>t\<close> by \<open>u\<close>; \<open>t\<^bold>\<lparr>u\<^bold>\<rparr>\<close> opens the top binder.
  Because bound variables are indices, substituting for a free variable (\<open>fsub\<close>) needs no
  renaming: it passes straight through \<open>Abs\<close>.\<close>

primrec opn :: "nat \<Rightarrow> 'p tm \<Rightarrow> 'p tm \<Rightarrow> 'p tm" where
    "opn k u (Bnd i) = (if i = k then u else Bnd i)"
  | "opn k u (n\<^sup>f\<^bsub>\<sigma>\<^esub>) = n\<^sup>f\<^bsub>\<sigma>\<^esub>"
  | "opn k u (p\<^sup>p\<^bsub>\<sigma>\<^esub>) = p\<^sup>p\<^bsub>\<sigma>\<^esub>"
  | "opn k u Neg = Neg"
  | "opn k u Dis = Dis"
  | "opn k u (Pi \<sigma>) = Pi \<sigma>"
  | "opn k u (Iota \<tau>) = Iota \<tau>"
  | "opn k u (Eq \<tau>) = Eq \<tau>"
  | "opn k u (s \<^bold>\<cdot> t) = (opn k u s) \<^bold>\<cdot> (opn k u t)"
  | "opn k u (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) = \<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (opn (Suc k) u b)"

text \<open>Opening the outermost binder is by far the most frequent operation, so it gets its
  own notation: \<open>b\<^bold>\<langle>u\<^bold>\<rangle>\<close> is \<open>b\<close> with de Bruijn index \<open>0\<close> instantiated to \<open>u\<close> ---
  BKK's \<open>[u/X]B\<close> for the bound variable of the enclosing abstraction or quantifier.\<close>

abbreviation opn0 (\<open>_\<^bold>\<langle>_\<^bold>\<rangle>\<close> [1000, 0] 1000) where "b\<^bold>\<langle>u\<^bold>\<rangle> \<equiv> opn 0 u b"

primrec fsub :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm \<Rightarrow> 'p tm" where
    "fsub x \<sigma> u (Bnd i) = Bnd i"
  | "fsub x \<sigma> u (n\<^sup>f\<^bsub>\<tau>\<^esub>) = (if n = x \<and> \<tau> = \<sigma> then u else n\<^sup>f\<^bsub>\<tau>\<^esub>)"
  | "fsub x \<sigma> u (p\<^sup>p\<^bsub>\<tau>\<^esub>) = p\<^sup>p\<^bsub>\<tau>\<^esub>"
  | "fsub x \<sigma> u Neg = Neg"
  | "fsub x \<sigma> u Dis = Dis"
  | "fsub x \<sigma> u (Pi \<tau>) = Pi \<tau>"
  | "fsub x \<sigma> u (Iota \<tau>) = Iota \<tau>"
  | "fsub x \<sigma> u (Eq \<tau>) = Eq \<tau>"
  | "fsub x \<sigma> u (s \<^bold>\<cdot> t) = (fsub x \<sigma> u s) \<^bold>\<cdot> (fsub x \<sigma> u t)"
  | "fsub x \<sigma> u (\<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> b) = \<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> (fsub x \<sigma> u b)"

text \<open>Substitution notation: \<open>b\<^bold>[u\<^bold>/x\<^bsub>\<sigma>\<^esub>\<^bold>]\<close> substitutes \<open>u\<close> for the free variable \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> in \<open>b\<close>.\<close>

syntax "_fsub" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"  (\<open>_\<^bold>[_\<^bold>'/_\<^bsub>_\<^esub>\<^bold>]\<close> [1000, 0, 0, 0] 1000)
syntax_consts "_fsub" == "fsub"
translations "b\<^bold>[u\<^bold>/x\<^bsub>\<sigma>\<^esub>\<^bold>]" \<rightleftharpoons> "CONST fsub x \<sigma> u b"

subsection \<open>Free variables and parameters\<close>

primrec fvs :: "'p tm \<Rightarrow> nat set" where
    "fvs (Bnd i) = {}"
  | "fvs (n\<^sup>f\<^bsub>\<sigma>\<^esub>) = {n}"
  | "fvs (p\<^sup>p\<^bsub>\<sigma>\<^esub>) = {}"
  | "fvs Neg = {}"  | "fvs Dis = {}"  | "fvs (Pi \<sigma>) = {}"
  | "fvs (Iota \<sigma>) = {}"  | "fvs (Eq \<sigma>) = {}"
  | "fvs (s \<^bold>\<cdot> t) = fvs s \<union> fvs t"
  | "fvs (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) = fvs b"

lemma finite_fvs [simp]: "finite (fvs t)" by (induction t) auto
lemma finite_pars [simp]: "finite (pars t)" by (induction t) auto

text \<open>Renaming parameters.  Eigen-parameters (BKK's \<open>w\<^bsub>\<alpha>\<^esub>\<close>) must be chosen fresh; to weaken the
  context or extend a consistent set we move them out of the way with an injective renaming.\<close>

lemma prn_opn: "prn \<rho> (opn k u t) = opn k (prn \<rho> u) (prn \<rho> t)" by (induction t arbitrary: k) auto
lemma pars_prn: "pars (prn \<rho> t) = \<rho> ` pars t" by (induction t) auto
lemma prn_prn: "prn f (prn g t) = prn (\<lambda>p. f (g p)) t" by (induction t) auto
lemma prn_id [simp]: "prn (\<lambda>p. p) t = t" by (induction t) auto
lemma prn_cong: "(\<And>p. p \<in> pars t \<Longrightarrow> \<rho> p = p) \<Longrightarrow> prn \<rho> t = t" by (induction t) auto

text \<open>The typed free occurrences --- the (name, type) pairs a term reads from an assignment.
  A name can occur at several types, so this is finer than @{const fvs}.\<close>

primrec occ :: "'p tm \<Rightarrow> (nat \<times> ty) set" where
    "occ (Bnd i) = {}"
  | "occ (n\<^sup>f\<^bsub>\<sigma>\<^esub>) = {(n, \<sigma>)}"
  | "occ (p\<^sup>p\<^bsub>\<sigma>\<^esub>) = {}"
  | "occ Neg = {}"  | "occ Dis = {}"  | "occ (Pi \<sigma>) = {}"
  | "occ (Iota \<sigma>) = {}"  | "occ (Eq \<sigma>) = {}"
  | "occ (s \<^bold>\<cdot> t) = occ s \<union> occ t"
  | "occ (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) = occ b"

lemma fvs_eq_fst_occ: "fvs t = fst ` occ t" by (induction t) (auto simp: image_Un)
lemma occ_opn: "occ (opn k u t) \<subseteq> occ t \<union> occ u" by (induction t arbitrary: k) auto

subsection \<open>A fresh free variable exists\<close>

text \<open>A deterministic fresh name for a finite set (used for the abstraction case of the
  denotation).\<close>

definition fresh :: "nat set \<Rightarrow> nat" where "fresh S \<equiv> LEAST n. n \<notin> S"

lemma fresh_notin: "finite S \<Longrightarrow> fresh S \<notin> S"
  by (metis LeastI ex_new_if_finite infinite_UNIV_nat fresh_def)

subsection \<open>Basic laws of opening and substitution\<close>

text \<open>Free variables of a substitution.  (A name may occur at several types, so \<open>x\<close> is only
  removed under the safe over-approximation.)\<close>

lemma fvs_fsub: "fvs (fsub x \<sigma> u t) \<subseteq> fvs t \<union> fvs u" by (induction t) auto
lemma fvs_opn: "fvs (opn k u t) \<subseteq> fvs t \<union> fvs u" by (induction t arbitrary: k) auto

text \<open>Opening with a free variable preserves size --- the measure for the size-recursive
  denotation of an abstraction (its body is opened with a fresh variable of the same size).\<close>

lemma size_opn_Fre [simp]: "size (opn k (x\<^sup>f\<^bsub>\<sigma>\<^esub>) t) = size t" by (induction t arbitrary: k) auto

subsection \<open>Local closure\<close>

text \<open>A term is @{emph \<open>locally closed\<close>} if every bound index is captured by an enclosing
  binder.  As is standard for the locally-nameless representation, the \<open>Abs\<close> rule uses a
  @{emph \<open>cofinite\<close>} quantifier: opening the body with a fresh free variable is locally closed.
  A locally closed term denotes exactly an \<open>\<alpha>\<close>-equivalence class of BKK's named terms
  (BKK Section 2.1).\<close>

inductive lc :: "'p tm \<Rightarrow> bool" where
    lc_Fre [intro]: "lc (n\<^sup>f\<^bsub>\<sigma>\<^esub>)"
  | lc_Par [intro]: "lc (p\<^sup>p\<^bsub>\<sigma>\<^esub>)"
  | lc_Neg [intro]: "lc Neg"
  | lc_Dis [intro]: "lc Dis"
  | lc_Pi  [intro]: "lc (Pi \<sigma>)"
  | lc_Iota [intro]: "lc (Iota \<sigma>)"
  | lc_Eq [intro]: "lc (Eq \<sigma>)"
  | lc_App [intro]: "lc s \<Longrightarrow> lc t \<Longrightarrow> lc (s \<^bold>\<cdot> t)"
  | lc_Abs: "finite L \<Longrightarrow> (\<And>x. x \<notin> L \<Longrightarrow> lc (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)) \<Longrightarrow> lc (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"

text \<open>If opening at \<open>j\<close> is already fixed by a later opening at \<open>i \<noteq> j\<close>, then opening
  at \<open>i\<close> alone was already the identity.\<close>

lemma opn_core: "i \<noteq> j \<Longrightarrow> opn j v t = opn i u (opn j v t) \<Longrightarrow> opn i u t = t"
proof (induction t arbitrary: i j)
  case (Abs \<tau> b)
  have "opn (Suc i) u b = b"
    by (metis Abs.IH opn.simps(10) Abs.prems(1) tm.inject(8) Abs.prems(2) old.nat.inject)
  thus ?case by simp
qed (auto split: if_splits)

text \<open>A locally closed term ignores opening.\<close>

lemma opn_lc [simp]: "lc t \<Longrightarrow> opn k u t = t"
proof (induction arbitrary: k rule: lc.induct)
  case (lc_Abs L b \<sigma>)
  obtain x where x: "x \<notin> L"
    using lc_Abs.hyps(1) by (meson ex_new_if_finite infinite_UNIV_nat)
  have IH: "opn (Suc k) u (b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>" using lc_Abs.IH x by auto
  have "opn (Suc k) u b = b" by (metis opn_core IH nat.simps(3))
  thus ?case by simp
qed simp_all

text \<open>\<open>fsub\<close> commutes with opening when the substituted term is locally closed.\<close>

lemma fsub_opn: "lc u \<Longrightarrow> fsub x \<sigma> u (opn k v t) = opn k (fsub x \<sigma> u v) (fsub x \<sigma> u t)"
  by (induction t arbitrary: k) auto

text \<open>Opening with \<open>u\<close> equals opening with a fresh free variable and then substituting \<open>u\<close> for it.\<close>

lemma fsub_intro: "x \<notin> fvs t \<Longrightarrow> opn k u t = fsub x \<sigma> u (opn k (x\<^sup>f\<^bsub>\<sigma>\<^esub>) t)"
  by (induction t arbitrary: k) auto

text \<open>Openings at distinct indices commute (for locally closed fillers).\<close>

lemma opn_opn_comm: "i \<noteq> j \<Longrightarrow> lc u \<Longrightarrow> lc v \<Longrightarrow> opn i u (opn j v t) = opn j v (opn i u t)"
  by (induction t arbitrary: i j) auto

subsection \<open>Typing: well-formed formulae\<close>

text \<open>\<open>wff\<^bsub>\<sigma>\<^esub>(t)\<close> is BKK's \<open>t \<in> wff\<^bsub>\<sigma>\<^esub>(\<Sigma>)\<close> (BKK Section 2.1): \<open>t\<close> is a well-formed formula of
  type \<open>\<sigma>\<close>.  The \<open>Abs\<close> rule uses the cofinite quantifier, so a well-formed formula is in
  particular locally closed.\<close>

inductive wff :: "ty \<Rightarrow> 'p tm \<Rightarrow> bool"  (\<open>wff\<^bsub>_\<^esub>'(_')\<close> [0,0] 1000) where
    wff_Fre: "wff\<^bsub>\<sigma>\<^esub>(n\<^sup>f\<^bsub>\<sigma>\<^esub>)"
  | wff_Par: "wff\<^bsub>\<sigma>\<^esub>(p\<^sup>p\<^bsub>\<sigma>\<^esub>)"
  | wff_Neg: "wff\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^esub>(Neg)"
  | wff_Dis: "wff\<^bsub>\<o>\<^bold>\<Rightarrow>\<o>\<^bold>\<Rightarrow>\<o>\<^esub>(Dis)"
  | wff_Pi:  "wff\<^bsub>(\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>\<^esub>(Pi \<sigma>)"
  | wff_Iota: "wff\<^bsub>(\<sigma>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<sigma>\<^esub>(Iota \<sigma>)"
  | wff_Eq: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<sigma>\<^bold>\<Rightarrow>\<o>\<^esub>(Eq \<sigma>)"
  | wff_App: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(s) \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(s \<^bold>\<cdot> t)"
  | wff_Abs: "finite L \<Longrightarrow> (\<And>x. x \<notin> L \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)) \<Longrightarrow> wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"

lemma wff_lc: "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> lc t" by (induction rule: wff.induct) (auto intro: lc_Abs)

inductive_cases wff_FreE [elim!]: "wff\<^bsub>\<tau>\<^esub>(n\<^sup>f\<^bsub>\<sigma>\<^esub>)"
inductive_cases wff_ParE [elim!]: "wff\<^bsub>\<tau>\<^esub>(p\<^sup>p\<^bsub>\<sigma>\<^esub>)"
inductive_cases wff_NegE [elim!]: "wff\<^bsub>\<tau>\<^esub>(Neg)"
inductive_cases wff_DisE [elim!]: "wff\<^bsub>\<tau>\<^esub>(Dis)"
inductive_cases wff_PiE  [elim!]: "wff\<^bsub>\<tau>\<^esub>(Pi \<sigma>)"
inductive_cases wff_IotaE [elim!]: "wff\<^bsub>\<tau>\<^esub>(Iota \<sigma>)"
inductive_cases wff_EqE [elim!]: "wff\<^bsub>\<tau>\<^esub>(Eq \<sigma>)"
inductive_cases wff_AppE [elim]: "wff\<^bsub>\<tau>\<^esub>(s \<^bold>\<cdot> t)"
inductive_cases wff_AbsE [elim]: "wff\<^bsub>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"

text \<open>Types are unique.\<close>

lemma wff_unique: "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(t) \<Longrightarrow> \<sigma> = \<tau>"
proof (induction \<sigma> t arbitrary: \<tau> rule: wff.induct)
  case (wff_Abs L \<rho> b \<sigma>)
  from wff_Abs.prems obtain L' \<rho>' where t: "\<tau> = \<sigma> \<^bold>\<Rightarrow> \<rho>'"
      and fL': "finite L'" and hb: "\<And>x. x \<notin> L' \<Longrightarrow> wff\<^bsub>\<rho>'\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" 
    by auto
  obtain x where x: "x \<notin> L \<union> L'" using wff_Abs(1) fL'
    by (meson ex_new_if_finite finite_UnI infinite_UNIV_nat)
  have "\<rho> = \<rho>'" using wff_Abs.IH hb x by auto
  thus ?case using t by simp
qed (fast)+

text \<open>Well-typedness is preserved when a free variable is replaced by a term of the same
  type (BKK Section 2.1: substitution respects the typing; the paper leaves this implicit).\<close>

lemma wff_fsub: "wff\<^bsub>\<tau>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<rho>\<^esub>(u) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(fsub x \<rho> u t)"
proof (induction \<tau> t rule: wff.induct)
  case (wff_Abs L \<tau> b \<sigma>) 
  have lcu: "lc u" using wff_Abs.prems by (rule wff_lc)
  have "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (fsub x \<rho> u b))"
    by (metis finite_insert fsub.simps(2) fsub_opn insert_iff lcu wff.wff_Abs 
              wff_Abs.IH wff_Abs.hyps(1) wff_Abs.prems)
  thus ?case by simp
qed (auto intro: wff.intros simp: wff.wff_Fre)

text \<open>Consequently an abstraction may be opened with @{emph \<open>any\<close>} fresh free variable and
  stays well-typed --- the locally-nameless counterpart of BKK's \<open>\<alpha>\<close>-invariance (BKK Section 2.1).\<close>

lemma wff_Abs_open: assumes w: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" and x: "x \<notin> fvs b"
  shows "wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
proof -
  from w obtain L \<tau>' where L\<tau>': "finite L" "\<tau> = \<tau>'" "\<And>y. y \<notin> L \<Longrightarrow> wff\<^bsub>\<tau>'\<^esub>(b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" by auto
  obtain y where y: "y \<notin> L \<union> fvs b"
    using L\<tau>'(1) by (meson ex_new_if_finite finite_UnI finite_fvs infinite_UNIV_nat)
  have "b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> = fsub y \<sigma> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" using y
    by (intro fsub_intro) auto
  moreover have "wff\<^bsub>\<tau>'\<^esub>(fsub y \<sigma> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>))" using L\<tau>'(3) y wff_Fre
    by (auto intro: wff_fsub)
  ultimately show ?thesis using L\<tau>'(2) by simp
qed

text \<open>Opening a well-typed abstraction with a well-typed argument stays well-typed --- the
  typing counterpart of \<open>\<beta>\<close>-reduction (implicit in BKK Section 2.1; the semantic analogue is BKK
      Lemma 3.20).\<close>

lemma wff_opn: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(a) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>a\<^bold>\<rangle>)" 
  by (metis finite_fvs fresh_notin fsub_intro wff_Abs_open wff_fsub)

text \<open>Parameter renaming leaves the typing unchanged (there is no BKK counterpart: parameter
  renaming is part of the locally-nameless infrastructure).\<close>

lemma wff_prn[intro!]: "wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(prn \<rho> t)"
proof (induction \<sigma> t rule: wff.induct)
  case wff_Abs thus ?case by (metis (mono_tags, lifting) prn_opn tm.simps(120,128) wff.wff_Abs)
qed (auto intro: wff.intros)

subsection \<open>Turning one parameter into a free variable\<close>

text \<open>\<open>pvar w \<sigma> x t\<close> replaces every occurrence of the parameter \<open>w\<close> at type \<open>\<sigma>\<close> by the free
  variable \<open>x\<close>.  This realizes the evaluation variant of BKK's proof of Theorem 7.3 (case
  \<open>NK(\<Pi>I)\<close>): from an evaluation \<open>\<E>\<close> ``one can define another evaluation function \<open>\<E>'\<close> such
  that \<open>\<E>'(w) \<equiv> a\<close> and \<open>\<E>'(A) \<equiv> \<E>(A)\<close> if \<open>w\<close> does not occur in \<open>A\<close>''.\<close>

primrec pvar :: "'p \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> 'p tm \<Rightarrow> 'p tm" where
    "pvar w \<sigma> x (Bnd i) = Bnd i"
  | "pvar w \<sigma> x (n\<^sup>f\<^bsub>\<tau>\<^esub>) = n\<^sup>f\<^bsub>\<tau>\<^esub>"
  | "pvar w \<sigma> x (p\<^sup>p\<^bsub>\<tau>\<^esub>) = (if p = w \<and> \<tau> = \<sigma> then x\<^sup>f\<^bsub>\<sigma>\<^esub> else p\<^sup>p\<^bsub>\<tau>\<^esub>)"
  | "pvar w \<sigma> x Neg = Neg"
  | "pvar w \<sigma> x Dis = Dis"
  | "pvar w \<sigma> x (Pi \<tau>) = Pi \<tau>"
  | "pvar w \<sigma> x (Iota \<tau>) = Iota \<tau>"
  | "pvar w \<sigma> x (Eq \<tau>) = Eq \<tau>"
  | "pvar w \<sigma> x (s \<^bold>\<cdot> t) = (pvar w \<sigma> x s) \<^bold>\<cdot> (pvar w \<sigma> x t)"
  | "pvar w \<sigma> x (\<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> b) = \<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> (pvar w \<sigma> x b)"

lemma pvar_opn: "pvar w \<sigma> x (opn k u t) = opn k (pvar w \<sigma> x u) (pvar w \<sigma> x t)"
  by (induction t arbitrary: k) auto
lemma pvar_id [simp]: "w \<notin> pars t \<Longrightarrow> pvar w \<sigma> x t = t"
  by (induction t) auto
lemma wff_pvar: "wff\<^bsub>\<tau>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(pvar w \<sigma> x t)"
proof (induction \<tau> t rule: wff.induct)
  case wff_Abs thus ?case by (metis pvar.simps(10,2) pvar_opn wff.wff_Abs)
qed (auto intro: wff.intros)

subsection \<open>\<open>\<beta>\<close>-conversion (BKK Section 2)\<close>

text \<open>BKK's \<open>\<beta>\<close>-equality \<open>\<equiv>\<^sub>\<beta>\<close> (BKK Section 2.1): the congruence closure of the \<open>\<beta>\<close>-redex
  \<open>(\<lambda>x. b) a \<rightarrow> b[a/x]\<close>.  In the locally-nameless
  presentation the redex reduces to \<open>b\<^bold>\<langle>a\<^bold>\<rangle>\<close>, and the rule under an abstraction is stated
  cofinitely, as for typing and local closure.\<close>

text \<open>The relation is @{emph \<open>type-indexed\<close>}: \<open>s \<approx>\<^bsub>\<rho>\<^esub> t\<close> holds only for well-formed terms of type
  \<open>\<rho>\<close>.  Carrying the type keeps the symmetric/transitive rules type-preserving (a \<open>\<beta>\<close>-expansion
  does not otherwise determine the argument's type), which is exactly what the soundness proof of
  \<open>NK(\<beta>)\<close> needs.\<close>

inductive beq :: "'p tm \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> bool"  (\<open>_ \<approx>\<^bsub>_\<^esub> _\<close> [51, 0, 51] 50) where
    beta:  "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<rho>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(a) \<Longrightarrow> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a \<approx>\<^bsub>\<rho>\<^esub> b\<^bold>\<langle>a\<^bold>\<rangle>"
  | refl:  "wff\<^bsub>\<rho>\<^esub>(t) \<Longrightarrow> t \<approx>\<^bsub>\<rho>\<^esub> t"
  | sym:   "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> t \<approx>\<^bsub>\<rho>\<^esub> s"
  | trans: "r \<approx>\<^bsub>\<rho>\<^esub> s \<Longrightarrow> s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> r \<approx>\<^bsub>\<rho>\<^esub> t"
  | appL:  "s \<approx>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<rho>\<^esub> s' \<Longrightarrow> wff\<^bsub>\<sigma>\<^esub>(t) \<Longrightarrow> s \<^bold>\<cdot> t \<approx>\<^bsub>\<rho>\<^esub> s' \<^bold>\<cdot> t"
  | appR:  "t \<approx>\<^bsub>\<sigma>\<^esub> t' \<Longrightarrow> wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<rho>\<^esub>(s) \<Longrightarrow> s \<^bold>\<cdot> t \<approx>\<^bsub>\<rho>\<^esub> s \<^bold>\<cdot> t'"
  | abs:   "finite L \<Longrightarrow> (\<And>x. x \<notin> L \<Longrightarrow> b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> \<approx>\<^bsub>\<tau>\<^esub> b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)
              \<Longrightarrow> \<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b \<approx>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> \<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b'"

text \<open>\<open>\<beta>\<close>-conversion relates well-formed terms of the stated type.\<close>

lemma beq_wff: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> wff\<^bsub>\<rho>\<^esub>(s) \<and> wff\<^bsub>\<rho>\<^esub>(t)"
proof (induction rule: beq.induct)
  case beta thus ?case by (auto intro: wff_App wff_opn)
next
  case abs thus ?case by (metis wff_Abs)
qed (auto intro: wff_App)

lemma beq_wffL: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> wff\<^bsub>\<rho>\<^esub>(s)" and beq_wffR: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> wff\<^bsub>\<rho>\<^esub>(t)"
  using beq_wff by blast+

text \<open>\<open>\<beta>\<close>-conversion is stable under parameter renaming.\<close>

lemma beq_rename[intro!]: "s \<approx>\<^bsub>\<tau>\<^esub> t \<Longrightarrow> prn \<pi> s \<approx>\<^bsub>\<tau>\<^esub> prn \<pi> t"
proof (induction rule: beq.induct)
  case beta thus ?case by simp (metis beq.beta prn_opn tm.simps(128) wff_prn)
next case refl thus ?case using beq.refl wff_prn by blast
next case sym thus ?case using beq.sym by blast
next case trans thus ?case using beq.trans by blast
next case appL thus ?case using beq.appL by force
next case appR thus ?case using beq.appR by force
next case abs thus ?case by (metis (mono_tags, lifting) beq.abs prn_opn tm.simps(120,128))
qed


subsection \<open>The defined logical layer (BKK Section 2.2)\<close>

text \<open>Following BKK (BKK Section 2.2), everything beyond the primitive constants of the
  signature --- \<open>\<^bold>\<not>\<close>, \<open>\<^bold>\<or>\<close>, \<open>Pi\<^bsub>\<sigma>\<^esub>\<close>, the primitive equality \<open>Eq \<sigma>\<close> and the description
  operators \<open>Iota \<sigma>\<close> (above) --- is defined.
  The universal quantifier is BKK's shorthand \<open>\<^bold>\<forall>X\<^bsub>\<sigma>\<^esub>. A \<equiv> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub>(\<lambda>X\<^bsub>\<sigma>\<^esub>. A)\<close> and implication
  their \<open>A \<^bold>\<supset> B \<equiv> (\<^bold>\<not>A) \<^bold>\<or> B\<close>.  For falsity we deviate mildly from BKK, who use
  \<open>F\<^bsub>\<o>\<^esub> \<equiv> \<^bold>\<not>\<^bold>\<forall>P\<^bsub>\<o>\<^esub>. P \<^bold>\<or> \<^bold>\<not>P\<close> (BKK Lemma 3.43, footnote 11): our \<open>\<^bold>\<bottom>\<close> is \<open>\<^bold>\<forall>X\<^bsub>\<o>\<^esub>. X\<close> and \<open>\<^bold>\<top> \<equiv> \<^bold>\<not>\<^bold>\<bottom>\<close>.
  The two choices are interderivable in \<open>NK\<^sub>\<beta>\<close> (cf.\ BKK Remark 7.2) and both falsa are
  unsatisfied in every \<open>\<Sigma>\<close>-model, so every use below is invariant under the exchange.
  Leibniz equality --- always expressible, alongside the primitive \<open>Eq \<alpha>\<close> of the signature ---
  is BKK's Leibniz combinator \<open>Q\<^bsub>\<alpha>\<^esub> \<equiv> \<lambda>X\<^bsub>\<alpha>\<^esub> Y\<^bsub>\<alpha>\<^esub>. \<^bold>\<forall>P\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>. P X \<^bold>\<supset> P Y\<close> (BKK Section 2.2,
  the Leibniz formula for equality).  Because bound variables are de Bruijn indices, \<open>Leib \<alpha>\<close> is
  a genuinely @{emph \<open>closed\<close>} term: BKK's reserved bound names \<open>X, Y, P\<close> are simply the indices
  \<open>2, 1, 0\<close>.\<close>


definition Forall :: "ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<Pi>\<^bsub>_\<^esub> _\<close> [0, 200] 200) where 
  "\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b = (Pi \<sigma>) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
definition FalseB :: "'p tm"  (\<open>\<^bold>\<bottom>\<close>) where "\<^bold>\<bottom> = \<^bold>\<Pi>\<^bsub>\<o>\<^esub> (Bnd 0)"
definition TrueB :: "'p tm"  (\<open>\<^bold>\<top>\<close>) where "\<^bold>\<top> = \<^bold>\<not> \<^bold>\<bottom>"
definition ImpB :: "'p tm \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (infixr \<open>\<^bold>\<supset>\<close> 60) where
  "\<phi> \<^bold>\<supset> \<psi> = (\<^bold>\<not> \<phi>) \<^bold>\<or> \<psi>"
definition Leib :: "ty \<Rightarrow> 'p tm" where
  "Leib \<alpha> = \<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (Abs \<alpha> (\<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0) \<^bold>\<cdot> (Bnd 2) \<^bold>\<supset> (Bnd 0) \<^bold>\<cdot> (Bnd 1))))"
abbreviation LeibA :: "'p tm \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>_ \<^bold>\<doteq>\<^bsub>_\<^esub> _\<close> [66,0,66] 65) where
  "A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B \<equiv> ((Leib \<alpha>) \<^bold>\<cdot> A) \<^bold>\<cdot> B"

text \<open>Primitive equality applied (BKK's optional \<open>=\<^sub>\<alpha> \<in> \<Sigma>\<^bsub>\<alpha>\<rightarrow>\<alpha>\<rightarrow>\<o>\<^esub>\<close>, BKK Remark 7.9).\<close>

abbreviation PEqA :: "'p tm \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>_ \<^bold>=\<^bsub>_\<^esub> _\<close> [66,0,66] 65) where
  "A \<^bold>=\<^bsub>\<alpha>\<^esub> B \<equiv> ((Eq \<alpha>) \<^bold>\<cdot> A) \<^bold>\<cdot> B"
lemma wff_PEq [intro]: "wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(B) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A \<^bold>=\<^bsub>\<alpha>\<^esub> B)"
  by (rule wff_App[OF wff_App[OF wff_Eq]])

subsection \<open>Opening distributes over the defined layer\<close>

lemma opn_Forall [simp]: "opn k u (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b) = \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (opn (Suc k) u b)"
  by (simp add: Forall_def)
lemma opn_ImpB [simp]: "opn k u (\<phi> \<^bold>\<supset> \<psi>) = (opn k u \<phi>) \<^bold>\<supset> (opn k u \<psi>)"
  by (simp add: ImpB_def)
lemma opn_FalseB [simp]: "opn k u (\<^bold>\<bottom> :: 'p tm) = \<^bold>\<bottom>"
  by (simp add: FalseB_def)
lemma opn_Leib [simp]: "opn k u (Leib \<alpha> :: 'p tm) = Leib \<alpha>"
  by (simp add: Leib_def)

subsection \<open>A convenient abstraction-typing rule\<close>

text \<open>For the closed defined terms, opening the body with @{emph \<open>any\<close>} free variable is
  well-typed, so the cofinite side-condition collapses to a universal one.\<close>

lemma wff_AbsI: "(\<And>x. wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)) \<Longrightarrow> wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
  by (rule wff_Abs[of "{}"]) auto

subsection \<open>Typing of the defined layer\<close>

lemma wff_Forall [intro]: "(\<And>x. wff\<^bsub>\<o>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b)"
  by (metis Forall_def wff_AbsI wff_App wff_Pi)
lemma wff_Not [intro]: "wff\<^bsub>\<o>\<^esub>(\<phi>) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(\<^bold>\<not> \<phi>)"
  by (rule wff_App[OF wff_Neg])
lemma wff_Or [intro]: "wff\<^bsub>\<o>\<^esub>(\<phi>) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(\<psi>) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(\<phi> \<^bold>\<or> \<psi>)"
  by (rule wff_App[OF wff_App[OF wff_Dis]])
lemma wff_ImpB [intro]: "wff\<^bsub>\<o>\<^esub>(\<phi>) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(\<psi>) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(\<phi> \<^bold>\<supset> \<psi>)"
  by (metis ImpB_def wff_Not wff_Or)
lemma wff_FalseB [intro, simp]: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<bottom>)" unfolding FalseB_def
  by (rule wff_Forall) (simp add: wff_Fre)
lemma wff_TrueB [intro, simp]: "wff\<^bsub>\<o>\<^esub>(\<^bold>\<top>)" unfolding TrueB_def
  by (rule wff_Not[OF wff_FalseB])
lemma wff_App_FreFre [intro]: "wff\<^bsub>\<o>\<^esub>((p\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>\<cdot> (x\<^sup>f\<^bsub>\<sigma>\<^esub>))"
  by (rule wff_App[OF wff_Fre wff_Fre])
lemma wff_Leib [intro, simp]: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(Leib \<alpha>)"
  by (auto simp: Leib_def del: wff_Forall wff_ImpB wff_App_FreFre
           intro!: wff_AbsI wff_Forall wff_ImpB wff_App_FreFre)
lemma wff_LeibE [intro]: "wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(B) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)"
  by (rule wff_App[OF wff_App[OF wff_Leib]])

subsection \<open>Free variables and local closure of the defined layer\<close>

lemma fvs_defs [simp]: "fvs (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b) = fvs b" "fvs (\<^bold>\<bottom> :: 'p tm) = {}" "fvs (\<^bold>\<top> :: 'p tm) = {}"
  "fvs (\<phi> \<^bold>\<supset> \<psi>) = fvs \<phi> \<union> fvs \<psi>" "fvs (Leib \<alpha> :: 'p tm) = {}"
  by (simp_all add: Forall_def FalseB_def TrueB_def ImpB_def Leib_def)

lemma pars_defs [simp]: "pars (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b) = pars b" "pars (\<^bold>\<bottom> :: 'p tm) = {}"
  "pars (\<^bold>\<top> :: 'p tm) = {}" "pars (\<phi> \<^bold>\<supset> \<psi>) = pars \<phi> \<union> pars \<psi>" "pars (Leib \<alpha> :: 'p tm) = {}"
  by (simp_all add: Forall_def FalseB_def TrueB_def ImpB_def Leib_def)

subsection \<open>Parameter renaming distributes over the defined layer\<close>

lemma prn_Forall [simp]: "prn \<rho> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b) = \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (prn \<rho> b)"
  by (simp add: Forall_def)
lemma prn_ImpB [simp]: "prn \<rho> (\<phi> \<^bold>\<supset> \<psi>) = (prn \<rho> \<phi>) \<^bold>\<supset> (prn \<rho> \<psi>)"
  by (simp add: ImpB_def)
lemma prn_FalseB [simp]: "prn \<rho> (\<^bold>\<bottom> :: 'p tm) = \<^bold>\<bottom>"
  by (simp add: FalseB_def)
lemma prn_Leib [simp]: "prn \<rho> (Leib \<alpha> :: 'p tm) = Leib \<alpha>"
  by (simp add: Leib_def)

subsection \<open>The defined existential quantifier\<close>

abbreviation ExistsB :: "ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<exists>\<^bsub>_\<^esub> _\<close> [0, 200] 200) where
  "\<^bold>\<exists>\<^bsub>\<sigma>\<^esub> b \<equiv> \<^bold>\<not> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b))"

subsection \<open>Named binders for the defined quantifiers\<close>

text \<open>Named-binder input syntax for the defined quantifiers: \<open>clos k x \<sigma> t\<close> abstracts the
  free variable \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> to the de Bruijn index \<open>k\<close> (the converse of \<open>opn\<close>), so that
  \<open>\<^bold>\<exists>x\<^bsub>\<sigma>\<^esub>. \<phi>\<close> and \<open>\<^bold>\<Pi>x\<^bsub>\<sigma>\<^esub>. \<phi>\<close> bind an ordinary named variable; the locally-nameless
  representation is recovered by computation (the \<open>_eq\<close> lemmas below).\<close>

primrec clos :: "nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm" where
  "clos k x \<sigma> (Bnd i) = Bnd i"
| "clos k x \<sigma> (n\<^sup>f\<^bsub>\<tau>\<^esub>) = (if n = x \<and> \<tau> = \<sigma> then Bnd k else n\<^sup>f\<^bsub>\<tau>\<^esub>)"
| "clos k x \<sigma> (p\<^sup>p\<^bsub>\<tau>\<^esub>) = p\<^sup>p\<^bsub>\<tau>\<^esub>"
| "clos k x \<sigma> Neg = Neg"
| "clos k x \<sigma> Dis = Dis"
| "clos k x \<sigma> (Pi \<tau>) = Pi \<tau>"
| "clos k x \<sigma> (Iota \<tau>) = Iota \<tau>"
| "clos k x \<sigma> (Eq \<tau>) = Eq \<tau>"
| "clos k x \<sigma> (s \<^bold>\<cdot> t) = (clos k x \<sigma> s) \<^bold>\<cdot> (clos k x \<sigma> t)"
| "clos k x \<sigma> (\<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> b) = \<^bold>\<Lambda>\<^bsub>\<tau>\<^esub> (clos (Suc k) x \<sigma> b)"

lemma clos_Forall [simp]: "clos k x \<sigma> (\<^bold>\<Pi>\<^bsub>\<tau>\<^esub> b) = \<^bold>\<Pi>\<^bsub>\<tau>\<^esub> (clos (Suc k) x \<sigma> b)"
  by (simp add: Forall_def)
lemma clos_ImpB [simp]: "clos k x \<sigma> (\<phi> \<^bold>\<supset> \<psi>) = (clos k x \<sigma> \<phi>) \<^bold>\<supset> (clos k x \<sigma> \<psi>)"
  by (simp add: ImpB_def)
lemma clos_Leib [simp]: "clos k x \<sigma> (Leib \<alpha> :: 'p tm) = Leib \<alpha>"
  by (simp add: Leib_def)
definition ExN :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<exists>_\<^bsub>_\<^esub>. _\<close> [1000, 0, 61] 61) where
  "\<^bold>\<exists>x\<^bsub>\<sigma>\<^esub>. b = \<^bold>\<exists>\<^bsub>\<sigma>\<^esub> (clos 0 x \<sigma> b)"
definition AllN :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<Pi>_\<^bsub>_\<^esub>. _\<close> [1000, 0, 61] 61) where
  "\<^bold>\<Pi>x\<^bsub>\<sigma>\<^esub>. b = \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (clos 0 x \<sigma> b)"
definition LamN :: "nat \<Rightarrow> ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<Lambda>_\<^bsub>_\<^esub>. _\<close> [1000, 0, 61] 61) where
  "\<^bold>\<Lambda>x\<^bsub>\<sigma>\<^esub>. b = \<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (clos 0 x \<sigma> b)"

text \<open>Fixed variable names for readable named-binder statements: the script letters
  \<open>\<G>, \<F>, \<X>, \<I>, \<H>\<close> name the (numeric) free variables \<open>0, \<dots>, 4\<close>.\<close>

definition \<G> :: nat where "\<G> = 0"
definition \<F> :: nat where "\<F> = 1"
definition \<X> :: nat where "\<X> = 2"
definition \<I> :: nat where "\<I> = 3"
definition \<H> :: nat where "\<H> = 4"

text\<open>Stronger size-based induction.\<close>

lemma size_induct[case_names Bnd Fre Par Neg Dis Pi Iota Eq App Abs]:
  assumes \<open>\<And>x. P (Bnd x)\<close>
      and \<open>\<And>x \<alpha>. P x\<^sup>f\<^bsub>\<alpha>\<^esub>\<close>
      and \<open>\<And>x \<alpha>. P x\<^sup>p\<^bsub>\<alpha>\<^esub>\<close>
      and \<open>P Neg\<close>
      and \<open>P Dis\<close>
      and \<open>\<And>\<alpha>. P (Pi \<alpha>)\<close>
      and \<open>\<And>\<alpha>. P (Iota \<alpha>)\<close>
      and \<open>\<And>\<alpha>. P (Eq \<alpha>)\<close>
      and \<open>\<And>A B. (\<And>C. size C \<le> size A \<Longrightarrow> P C) \<Longrightarrow> (\<And>C. size C \<le> size B \<Longrightarrow> P C) \<Longrightarrow> P (A \<^bold>\<cdot> B)\<close>
      and \<open>\<And>\<alpha> A. (\<And>C. size C \<le> size A \<Longrightarrow> P C) \<Longrightarrow> P (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> A)\<close>
    shows \<open>P x\<close>
using assms proof (induct x rule: measure_induct_rule[where f = size])
  case (less x) thus ?case by (induct x; auto)
qed

end
