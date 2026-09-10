theory Syntax
  imports Main "HOL-Library.Countable"
begin

section \<open>Syntax: a deep embedding of HOL in HOL\<close>

text \<open>BKK's language of classical higher-order logic --- HOL, by which we mean
  Church's simple theory of types throughout (BKK Sections 2.1--2.2) --- in a @{emph \<open>locally
  nameless\<close>} representation: bound variables are de Bruijn indices, free variables
  and parameters carry their type.  BKK take alphabetic variants to be identical (BKK
  Section 2.1); locally nameless makes that literally true --- \<open>\<alpha>\<close>-equivalent terms are
  @{emph \<open>equal\<close>}.  Binders bind indices and substitution replaces only free names, so
  capture cannot arise: explicit \<open>\<alpha>\<close>-conversion and bound-variable renaming disappear,
  while substitution itself (opening, \<open>fsub\<close>, \<open>msub\<close>) of course remains.
  As in BKK, non-logical constants are @{emph \<open>parameters\<close>} with names drawn from a type \<open>'p\<close>, and
  we include BKK's optional primitive equality \<open>Eq \<sigma>\<close> (BKK Section 2.1, Remark 7.9),
  alongside the always-expressible defined Leibniz equality (BKK Section 2.2).
  Beyond BKK's signature we also carry a description operator \<open>Iota \<sigma>\<close> of type
  \<open>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<close>, one for each type \<open>\<sigma>\<close>.  BKK themselves have no description operator:
  they decline to add one (BKK Section 2.3.1) and point to Andrews 1972 for the semantic
  issues.  We follow that reference.  \<open>Iota \<sigma>\<close> comes with the description axiom for
  singletons: the rule \<open>NK(\<iota>)\<close> of the calculus and the model condition \<open>gm_descB\<close>, both
  schematic in the type \<open>\<sigma>\<close>.  (The \<open>\<iota>\<close> in the rule's name is Andrews' symbol for
  description, not the type \<open>\<iota>\<close> of individuals.)  Definitions and lemmas below that carry
  no BKK reference are locally-nameless infrastructure: opening, closing, freshness,
  renaming.  They have no counterpart in the paper, where identification of alphabetic
  variants is handled informally (BKK Section 2.1).\<close>

subsection \<open>Types and terms\<close>

datatype ty = Ind (\<open>\<iota>\<close>) | Bool (\<open>\<o>\<close>) | Fun ty ty (infixr \<open>\<^bold>\<Rightarrow>\<close> 65)

datatype (pars: 'p) tm =
    Bnd nat      \<comment> \<open>bound variable (de Bruijn index)\<close>
  | Fre nat ty   \<comment> \<open>free variable: a name and its type\<close>
  | Par 'p ty     \<comment> \<open>parameter (typed constant)\<close>
  | Neg | Dis | Pi ty | Iota ty | Eq ty
      \<comment> \<open>logical constants \<open>\<^bold>\<not>, \<^bold>\<or>, \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub>, \<^bold>\<iota>\<^bsub>\<sigma>\<^esub>, \<^bold>=\<^bsub>\<sigma>\<^esub>\<close>\<close>
  | App "'p tm" "'p tm"  (infixl \<open>\<^bold>\<cdot>\<close> 200)
  | Abs ty "'p tm"    \<comment> \<open>abstraction, domain type annotated (BKK's \<open>\<lambda>X\<^bsub>\<sigma>\<^esub>. A\<close>;
      nameless, so no binder variable)\<close>
  for map: prn \<comment> \<open>We call the map function for the parameter type @{term prn}
      for parameter renaming.\<close>

text \<open>BKK write disjunctions in infix and negations in prefix notation (BKK Section 2.2
  declares the convention of writing \<open>((\<or>A)B)\<close> as \<open>A \<or> B\<close>); we mirror this with
  input/output abbreviations for the applied connectives.\<close>

abbreviation NegA :: "'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<not> _\<close> [66] 66) where
  "\<^bold>\<not> A \<equiv> Neg \<^bold>\<cdot> A"
abbreviation DisA :: "'p tm \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (infixr \<open>\<^bold>\<or>\<close> 61) where
  "A \<^bold>\<or> B \<equiv> (Dis \<^bold>\<cdot> A) \<^bold>\<cdot> B"

text \<open>Abstraction is written \<open>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<close>; it corresponds to BKK's \<open>\<lambda>X\<^bsub>\<sigma>\<^esub>. A\<close>.  The symbol is a
  bold \<open>\<^bold>\<Lambda>\<close> because \<open>\<lambda>\<close> already denotes Isabelle's own abstraction.  The notation is
  nameless: it shows the domain type \<open>\<sigma>\<close> but no binder variable --- the body \<open>b\<close> refers to
  the abstracted position by the de Bruijn index \<open>Bnd 0\<close>.\<close>

notation Abs (\<open>\<^bold>\<Lambda>\<^bsub>_\<^esub> _\<close> [0, 200] 200)

text \<open>Decorated atoms: a free variable \<open>x\<close> of type \<open>\<sigma>\<close> is written \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> (BKK's
  \<open>X\<^bsub>\<sigma>\<^esub>\<close>), a parameter \<open>w\<close> is written \<open>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<close> (BKK's typed constants).\<close>

notation Fre (\<open>_\<^sup>f\<^bsub>_\<^esub>\<close> [1000, 0] 1000)
notation Par (\<open>_\<^sup>p\<^bsub>_\<^esub>\<close> [1000, 0] 1000)

text \<open>The term notation and its BKK Section 2 counterparts: free variables \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> are BKK's
  \<open>X\<^bsub>\<sigma>\<^esub>\<close>, application \<open>s \<^bold>\<cdot> t\<close> is juxtaposition, and parameters \<open>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<close> are typed constants.
  The defined layer below adds \<open>A \<^bold>\<supset> B\<close>, \<open>\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> b\<close>, Leibniz equality \<open>A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B\<close> and applied
  primitive equality; opening is \<open>b\<^bold>\<langle>u\<^bold>\<rangle>\<close>; on the semantic side \<open>\<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>\<close> is the denotation
  and \<open>\<xi>(x\<^bsub>\<sigma>\<^esub> := d)\<close> the assignment update.\<close>

text \<open>Types and terms (over a countable parameter type) are countable.  These instances feed
  the countable-signature corollaries of the completeness development --- countable term-model
  domains, and the collapse of parameter-richness to purity; the extension construction itself
  (BKK Section 6, Lemma 6.32) walks a well-order of the term type and needs no countability.\<close>

instance ty :: countable by countable_datatype
instance tm :: (countable) countable by countable_datatype

subsection \<open>Opening and free-variable substitution\<close>

text \<open>\<open>opn\<^bsub>k\<^esub> u t\<close> replaces the bound index \<open>k\<close> in \<open>t\<close> by \<open>u\<close>.\<close>

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

text \<open>Because bound variables are indices, substituting for a free variable (\<open>fsub\<close>) needs no
  renaming: it passes straight through \<open>Abs\<close>.\<close>

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
  context or extend a consistent set we move them out of the way with an injective renaming. We
  use the map function introduced by the datatype, \<^term>\<open>prn\<close>, for the renaming and prove some
  lemmas about it.\<close>

lemma prn_opn: "prn \<rho> (opn k u t) = opn k (prn \<rho> u) (prn \<rho> t)"
  by (induction t arbitrary: k) auto
text \<open>Statement preserved verbatim from the published version of this entry (compatibility
  export).\<close>

lemma pars_prn: "pars (prn \<rho> t) = \<rho> ` pars t" by (simp add: tm.set_map)
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
lemma prn_occ [simp]: "occ (prn f t) = occ t" by (induction t) auto

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

text \<open>Opening with a free variable preserves \<^term>\<open>size\<close>.\<close>

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
  by (induct t arbitrary: i j; auto split: if_splits) (metis nat.inject)

text \<open>A locally closed term ignores opening.\<close>

lemma opn_lc [simp]: "lc t \<Longrightarrow> opn k u t = t"
  by (induct arbitrary: k rule: lc.induct; simp)
     (metis opn_core fresh_notin nat.distinct(1))

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
  then obtain L' \<rho>' where t: "\<tau> = \<sigma> \<^bold>\<Rightarrow> \<rho>'"
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
  case wff_Abs thus ?case
    by (metis (mono_tags, lifting) prn_opn tm.simps(120,128) wff.wff_Abs)
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
lemma occ_pvar: "occ (pvar w \<sigma>w x t) \<subseteq> occ t \<union> {(x, \<sigma>w)}"
  by (induction t) auto
lemma pars_pvar: "pars (pvar w \<sigma> x t) \<subseteq> pars t"
  by (induction t) auto
lemma pvar_image_id: "\<forall>D \<in> \<Phi>. w \<notin> pars D \<Longrightarrow> pvar w \<sigma> x ` \<Phi> = \<Phi>"
  by (auto simp: image_iff)

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

lemma beq_wff: assumes "s \<approx>\<^bsub>\<rho>\<^esub> t" shows beq_wffL: "wff\<^bsub>\<rho>\<^esub>(s)" and beq_wffR: "wff\<^bsub>\<rho>\<^esub>(t)"
  by (atomize (full))
     (induction rule: beq.induct[OF assms]; auto simp: wff_Abs intro: wff_App wff_opn)

text \<open>\<open>\<beta>\<close>-conversion is stable under parameter renaming.\<close>

lemma beq_rename[intro!]: "s \<approx>\<^bsub>\<tau>\<^esub> t \<Longrightarrow> prn \<pi> s \<approx>\<^bsub>\<tau>\<^esub> prn \<pi> t"
proof (induction rule: beq.induct)
  case beta thus ?case by simp (metis beq.beta prn_opn tm.simps(128) wff_prn)
next
  case abs thus ?case by (metis (mono_tags, lifting) beq.abs prn_opn tm.simps(120,128))
qed(auto intro: beq.intros)

text \<open>And likewise under parameter-to-variable substitution.\<close>

lemma beq_pvar: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> pvar w \<sigma>w x s \<approx>\<^bsub>\<rho>\<^esub> pvar w \<sigma>w x t"
proof (induction rule: beq.induct)
  case beta thus ?case by (smt (verit, best) beq.simps pvar.simps(10,9) pvar_opn wff_pvar)
qed(auto simp: wff_pvar beq.abs pvar_opn intro: beq.intros)


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
definition AndB :: "'p tm \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (infixr \<open>\<^bold>\<and>\<close> 62) where
  "A \<^bold>\<and> B \<equiv> \<^bold>\<not> (\<^bold>\<not> A \<^bold>\<or> \<^bold>\<not> B)"

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
  by (auto intro: wff_Abs)

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
lemma wff_AndB [intro]: "wff\<^bsub>\<o>\<^esub>(A) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(B) \<Longrightarrow> wff\<^bsub>\<o>\<^esub>(A \<^bold>\<and> B)"
  by (auto simp: AndB_def)

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

text \<open>And likewise the parameter-to-variable substitution \<open>pvar\<close>.\<close>

lemma pvar_Forall [simp]: "pvar w \<sigma> x (\<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b) = \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> (pvar w \<sigma> x b)"
  by (simp add: Forall_def)
lemma pvar_Leib [simp]: "pvar w \<sigma> x (Leib \<alpha>) = Leib \<alpha>"
  by (simp add: Leib_def Forall_def ImpB_def)

text \<open>Leibniz equality \<open>\<beta>\<close>-reduces to its \<open>\<forall>\<close>-form.\<close>

lemma Leib_beq: assumes wA: "wff\<^bsub>\<alpha>\<^esub>(A)" and wB: "wff\<^bsub>\<alpha>\<^esub>(B)"
  shows "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B) \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> B))"
proof -
  have lcA: "lc A" and lcB: "lc B" using wA wB by (auto intro: wff_lc)
  let ?inner = "\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (\<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> Bnd 1)))"
  have "(Leib \<alpha> \<^bold>\<cdot> A) \<approx>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ?inner"
    using beq.beta[OF wff_Leib[unfolded Leib_def] wA]
    unfolding Leib_def by (simp add: opn_lc[OF lcA])
  moreover {
    have "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(?inner)" using beq_wffR calculation by blast
    with beq.beta[OF this wB]
    have "(?inner \<^bold>\<cdot> B) \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> B))"
      using opn_lc[OF lcA] opn_lc[OF lcB] by simp
  }
  ultimately show ?thesis using beq.trans beq.appL wB by blast
qed

subsection \<open>The defined existential quantifier\<close>

abbreviation ExistsB :: "ty \<Rightarrow> 'p tm \<Rightarrow> 'p tm"  (\<open>\<^bold>\<exists>\<^bsub>_\<^esub> _\<close> [0, 200] 200) where
  "\<^bold>\<exists>\<^bsub>\<sigma>\<^esub> b \<equiv> \<^bold>\<not> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b))"

subsection \<open>Named binders for the defined quantifiers\<close>

text \<open>Named-binder input syntax for the defined quantifiers: \<open>clos k x \<sigma> t\<close> abstracts the
  free variable \<open>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<close> to the de Bruijn index \<open>k\<close> (the converse of \<open>opn\<close>), so that
  \<open>\<^bold>\<exists>x\<^bsub>\<sigma>\<^esub>. \<phi>\<close> and \<open>\<^bold>\<Pi>x\<^bsub>\<sigma>\<^esub>. \<phi>\<close> bind an ordinary named variable.\<close>

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

text \<open>How closing interacts with opening, substitution and the occurrence sets.\<close>

lemma opn_clos_sub: "opn k v t = t \<Longrightarrow> opn k v (clos k x \<sigma> t) = fsub x \<sigma> v t"
  by (induction t arbitrary: k) auto

lemma fsub_id: "fsub x \<sigma> (x\<^sup>f\<^bsub>\<sigma>\<^esub>) t = t"
  by (induction t) auto

lemma occ_clos: "(x, \<sigma>) \<notin> occ (clos k x \<sigma> t)"
  by (induction t arbitrary: k) auto

lemma pars_clos [simp]: "pars (clos k x \<sigma> t) = pars t"
  by (induction t arbitrary: k) auto

lemma finite_occ: "finite (occ t)"
  by (induction t) auto

lemma occ_fsub_closed: "occ u = {} \<Longrightarrow> occ (fsub x \<sigma> u t) = occ t - {(x, \<sigma>)}"
  by (induction t) auto

lemma wff_LamN_clos:
  assumes "wff\<^bsub>\<o>\<^esub>(b)"
  shows "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (clos 0 v \<sigma> b))"
  by (metis assms opn_clos_sub opn_lc wff_AbsI wff_Fre wff_fsub wff_lc)

lemma wff_AllN: assumes "wff\<^bsub>\<o>\<^esub>(b)" shows "wff\<^bsub>\<o>\<^esub>(\<^bold>\<Pi>v\<^bsub>\<sigma>\<^esub>. b)"
  by (metis AllN_def Forall_def assms wff_App wff_LamN_clos wff_Pi)

lemma wff_ExN: assumes w: "wff\<^bsub>\<o>\<^esub>(b)" shows "wff\<^bsub>\<o>\<^esub>(\<^bold>\<exists>v\<^bsub>\<sigma>\<^esub>. b)"
  by (metis AllN_def ExN_def clos.simps(4,9) w wff_AllN wff_App wff_Neg)

subsection \<open>Closed well-formed terms\<close>

text \<open>A @{emph \<open>closed\<close>} well-formed term, BKK's \<open>cwff\<^bsub>\<sigma>\<^esub>\<close> (BKK Section 2.2; BKK reserve
  @{emph \<open>sentence\<close>} for closed formulae of type \<open>\<o>\<close> --- parameters are allowed,
  they play the role of BKK's constants).  These are the carriers of the term model.\<close>

definition cwff :: "ty \<Rightarrow> 'p tm \<Rightarrow> bool" where "cwff \<sigma> A \<equiv> wff\<^bsub>\<sigma>\<^esub>(A) \<and> fvs A = {}"
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
lemma cwff_Leib: "cwff (\<sigma>\<^bold>\<Rightarrow>\<sigma>\<^bold>\<Rightarrow>\<o>) (Leib \<sigma>)" by (simp add: cwff_def)
lemma cwff_Par: "cwff \<sigma> (p\<^sup>p\<^bsub>\<sigma>\<^esub>)" by (simp add: cwff_def wff_Par)
lemma cwff_App: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) s \<Longrightarrow> cwff \<sigma> t \<Longrightarrow> cwff \<tau> (s \<^bold>\<cdot> t)"
  by (auto simp: cwff_def intro: wff.wff_App)
lemma cwff_LeibE: "cwff \<alpha> A \<Longrightarrow> cwff \<alpha> B \<Longrightarrow> cwff \<o> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)"
  by (meson cwff_App cwff_Leib)
lemma cwff_opn: "cwff (\<sigma>\<^bold>\<Rightarrow>\<tau>) (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<Longrightarrow> cwff \<sigma> a \<Longrightarrow> cwff \<tau> (b\<^bold>\<langle>a\<^bold>\<rangle>)"
  by (metis (no_types, opaque_lifting) cwff_def fvs.simps(10) fvs_opn
      subset_empty sup.idem wff_opn)
lemma cwff_unique: "cwff \<sigma> A \<Longrightarrow> cwff \<tau> A \<Longrightarrow> \<sigma> = \<tau>"
  by (auto simp: cwff_def dest: wff_unique)

text \<open>Converse of @{thm wff_Abs_open}: a body that is well-typed when opened with @{emph \<open>one\<close>}
  fresh variable yields a well-typed abstraction (all fresh openings are \<open>\<alpha>\<close>-variants).\<close>

lemma wff_Abs_open_rev: "wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) \<Longrightarrow> x \<notin> fvs b \<Longrightarrow> wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
  by (metis fsub_intro wff_AbsI wff_Fre wff_fsub)

subsection \<open>Simultaneous substitution\<close>

text \<open>Simultaneous substitution of a term for every free variable --- the general form of
  which \<open>fsub\<close> is the single-variable and \<open>vpar\<close> (below) the variable-to-parameter instance,
  and the analogue of the closing substitution \<open>\<sigma>\<close> in BKK's term evaluation (BKK Definition
  3.35).  For closed replacements it commutes with opening --- the locally-nameless analogue
  of BKK's parallel substitution, with no binder renaming.\<close>

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
lemma msub_id: "msub (\<lambda>n \<tau>. n\<^sup>f\<^bsub>\<tau>\<^esub>) t = t"
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

text \<open>Substituting one closed replacement first: for a variable whose replacement is closed,
  the simultaneous substitution factors through the single substitution \<open>fsub\<close>.\<close>

lemma msub_step:
  assumes cl: "fvs (\<rho> x \<sigma>) = {}"
  shows "msub \<rho> t = msub (\<lambda>n \<tau>. if n = x \<and> \<tau> = \<sigma> then n\<^sup>f\<^bsub>\<tau>\<^esub> else \<rho> n \<tau>) (fsub x \<sigma> (\<rho> x \<sigma>) t)"
  by (induction t) (auto simp: msub_closed[OF cl])

text \<open>\<open>vshift\<close> renames every free variable \<open>n\<close> to \<open>n + 1\<close>, freeing the name \<open>0\<close> at every
  type; \<open>\<beta>\<close>-equality and typing are stable under it.\<close>

definition vshift :: "'p tm \<Rightarrow> 'p tm" where "vshift = msub (\<lambda>n \<tau>. (Suc n)\<^sup>f\<^bsub>\<tau>\<^esub>)"
lemma occ_vshift: "occ (vshift t) = (\<lambda>(n, \<tau>). (Suc n, \<tau>)) ` occ t"
  unfolding vshift_def by (induction t) (auto simp: image_Un)
lemma pars_vshift: "pars (vshift t) = pars t"
  unfolding vshift_def by (induction t) auto
lemma wff_vshift: "wff\<^bsub>\<tau>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(vshift t)"
  by (auto elim: wff_msub intro: wff_Fre simp: vshift_def)
lemma vshift_opn: "vshift (t\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = (vshift t)\<^bold>\<langle>(Suc x)\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>"
  unfolding vshift_def by (subst msub_opn) auto
lemma beq_vshift: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> vshift s \<approx>\<^bsub>\<rho>\<^esub> vshift t"
proof (induction rule: beq.induct)
  case (beta \<sigma> \<rho> b a)
  moreover have "vshift ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a) = (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b)) \<^bold>\<cdot> (vshift a)"
    by (simp add: vshift_def)
  moreover have "vshift (b\<^bold>\<langle>a\<^bold>\<rangle>) = (vshift b)\<^bold>\<langle>vshift a\<^bold>\<rangle>"
    unfolding vshift_def by (subst msub_opn) auto
  moreover have "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<rho>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b))"
    using wff_vshift beta unfolding vshift_def by force
  ultimately show ?case using beq.beta wff_vshift by metis
next case appL thus ?case by (metis beq.appL msub.simps(9) vshift_def wff_vshift)
next case appR thus ?case by (metis beq.appR msub.simps(9) vshift_def wff_vshift)
next case (abs L b \<sigma> \<tau> b')
  have "\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b) \<approx>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> \<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b')"
  proof (rule beq.abs[of "{0} \<union> Suc ` L"])
    show "finite ({0} \<union> Suc ` L)" using abs.hyps(1) by simp
    fix y assume y: "y \<notin> {0} \<union> Suc ` L"
    then obtain x where x: "y = Suc x" "x \<notin> L" by (cases y) auto
    show "(vshift b)\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> \<approx>\<^bsub>\<tau>\<^esub> (vshift b')\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>" using abs.IH[OF x(2)]
      by (simp add: x(1) vshift_opn[symmetric])
  qed
  thus ?case by (simp add: vshift_def)
qed(auto simp: wff_vshift intro: beq.intros)

text \<open>Replacing every free variable of a stock \<open>S\<close> at once by a parameter --- the converse of
  @{const pvar}, as the parameter-valued instance of @{const msub}.\<close>

definition vpar :: "(nat \<times> ty) set \<Rightarrow> (nat \<Rightarrow> ty \<Rightarrow> 'p) \<Rightarrow> 'p tm \<Rightarrow> 'p tm" where
  "vpar S \<pi> \<equiv> msub (\<lambda>n \<tau>. if (n, \<tau>) \<in> S then (\<pi> n \<tau>)\<^sup>p\<^bsub>\<tau>\<^esub> else n\<^sup>f\<^bsub>\<tau>\<^esub>)"

lemma vpar_id: "S \<inter> occ t = {} \<Longrightarrow> vpar S \<pi> t = t"
  unfolding vpar_def by (subst msub_cong[where \<rho>' = "\<lambda>n \<tau>. n\<^sup>f\<^bsub>\<tau>\<^esub>"]) (auto simp: msub_id)

lemma vpar_cong: "occ t \<subseteq> S \<Longrightarrow> vpar S \<pi> t = vpar UNIV \<pi> t"
  unfolding vpar_def by (rule msub_cong) auto

lemma pars_vpar: "q \<in> pars (vpar S \<pi> t) \<Longrightarrow> q \<in> pars t \<or> (\<exists>n \<sigma>. q = \<pi> n \<sigma>)"
  unfolding vpar_def by (induction t) (auto split: if_splits)

lemma cwff_vpar: "wff\<^bsub>\<tau>\<^esub>(t) \<Longrightarrow> cwff \<tau> (vpar UNIV \<pi> t)"
  unfolding vpar_def by (rule cwff_msub) (auto intro: cwffI wff_Par)

text \<open>And @{const pvar} inverts it, one parameter at a time --- injectivity of \<open>\<pi>\<close> protects
  the not-yet-inverted parameters, freshness the original ones.\<close>

lemma pvar_vpar:
  assumes inj: "\<And>n \<tau>. \<pi> n \<tau> = \<pi> x \<sigma> \<Longrightarrow> n = x \<and> \<tau> = \<sigma>"
  shows "\<pi> x \<sigma> \<notin> pars t \<Longrightarrow> pvar (\<pi> x \<sigma>) \<sigma> x (vpar S \<pi> t) = vpar (S - {(x, \<sigma>)}) \<pi> t"
  unfolding vpar_def by (induction t) (auto dest: inj)

text \<open>Fixed variable names for readable named-binder statements: the script letters
  \<open>\<G>, \<F>, \<X>, \<I>, \<H>\<close> name the (numeric) free variables \<open>0, \<dots>, 4\<close>.\<close>

definition \<G> :: nat where "\<G> = 0"
definition \<F> :: nat where "\<F> = 1"
definition \<X> :: nat where "\<X> = 2"
definition \<I> :: nat where "\<I> = 3"
definition \<H> :: nat where "\<H> = 4"

text \<open>Closing shrinks the free variables; the named binders and the defined conjunction
  stay well-typed.\<close>

lemma fvs_clos: "fvs (clos k v \<sigma> b) \<subseteq> fvs b"
  by (induction b arbitrary: k) auto

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
