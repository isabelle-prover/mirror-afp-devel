theory Smolka
  imports Main
begin

section \<open>Human-authored proof formalization\<close>

text \<open>
  Formalization of the correctness proof of the Smolka-Blanchette algorithm
  for minimal type annotation of terms.

  The algorithm takes a Church-typed term and removes type annotations while
  preserving unique type-reconstruction, achieving both completeness (unique
  well-typed completion) and local minimality (removing any further annotation
  breaks uniqueness).
\<close>

subsection \<open>Types\<close>

text \<open>
  Corresponds to Subsection 1.1 of the paper.
  We fix an infinite set of type variables and define types as:
    $\sigma ::= \alpha | \sigma \Rightarrow \tau | (\sigma_1, ..., \sigma_n) \kappa$
  We represent this as a datatype with \<^term>\<open>Arrow\<close> as a distinguished binary constructor
  and \<^term>\<open>TyCon\<close> for n-ary type constructors.
\<close>

datatype ('tv, 'k) ty =
  TyVar 'tv
| Arrow "('tv, 'k) ty" "('tv, 'k) ty"
| TyCon 'k "('tv, 'k) ty list"

text \<open>
  Maybe-types: \<^typ>\<open>('tv, 'k) ty option\<close> where \<^term>\<open>None\<close> represents $\bot$ (no type annotation)
  and \<^term>\<open>Some \<sigma>\<close> represents an actual type.
\<close>

type_synonym ('tv, 'k) mty = "('tv, 'k) ty option"

subsubsection \<open>Type variables of a type\<close>

text \<open>
  \<^term>\<open>tvars_ty\<close>: the set of type variables occurring in a type.
  Extended to maybe-types with \<^term>\<open>tvars_mty None = {}\<close>.
\<close>

fun tvars_ty :: "('tv, 'k) ty \<Rightarrow> 'tv set" where
  "tvars_ty (TyVar a) = {a}"
| "tvars_ty (Arrow \<sigma> \<tau>) = tvars_ty \<sigma> \<union> tvars_ty \<tau>"
| "tvars_ty (TyCon \<kappa> \<sigma>s) = \<Union>(tvars_ty ` set \<sigma>s)"

definition tvars_mty :: "('tv, 'k) mty \<Rightarrow> 'tv set" where
  "tvars_mty \<xi> = (case \<xi> of None \<Rightarrow> {} | Some \<sigma> \<Rightarrow> tvars_ty \<sigma>)"

lemma tvars_mty_None[simp]: "tvars_mty None = {}"
  by (simp add: tvars_mty_def)

lemma tvars_mty_Some[simp]: "tvars_mty (Some \<sigma>) = tvars_ty \<sigma>"
  by (simp add: tvars_mty_def)

lemma tvars_ty_finite[simp, intro]: "finite (tvars_ty \<tau>)"
  by (induction \<tau>) auto

lemma tvars_mty_finite[simp, intro]: "finite (tvars_mty \<xi>)"
  by (cases \<xi>) auto

subsubsection \<open>Type substitution\<close>

text \<open>
  A type substitution is a function from type variables to types.
  \<^term>\<open>subst_ty \<rho> \<sigma>\<close> applies \<^term>\<open>\<rho>\<close> to \<^term>\<open>\<sigma>\<close>.
  Extended to maybe-types with \<^term>\<open>subst_mty \<rho> None = None\<close>.
\<close>

fun subst_ty :: "('tv \<Rightarrow> ('tv, 'k) ty) \<Rightarrow> ('tv, 'k) ty \<Rightarrow> ('tv, 'k) ty" where
  "subst_ty \<rho> (TyVar a) = \<rho> a"
| "subst_ty \<rho> (Arrow \<sigma> \<tau>) = Arrow (subst_ty \<rho> \<sigma>) (subst_ty \<rho> \<tau>)"
| "subst_ty \<rho> (TyCon \<kappa> \<sigma>s) = TyCon \<kappa> (map (subst_ty \<rho>) \<sigma>s)"

definition subst_mty :: "('tv \<Rightarrow> ('tv, 'k) ty) \<Rightarrow> ('tv, 'k) mty \<Rightarrow> ('tv, 'k) mty" where
  "subst_mty \<rho> \<xi> = map_option (subst_ty \<rho>) \<xi>"

lemma subst_mty_None[simp]: "subst_mty \<rho> None = None"
  by (simp add: subst_mty_def)

lemma subst_mty_Some[simp]: "subst_mty \<rho> (Some \<sigma>) = Some (subst_ty \<rho> \<sigma>)"
  by (simp add: subst_mty_def)

subsubsection \<open>Substitution composition and single substitution\<close>

definition comp_subst ::
  "('tv \<Rightarrow> ('tv,'k) ty) \<Rightarrow> ('tv \<Rightarrow> ('tv,'k) ty) \<Rightarrow> ('tv \<Rightarrow> ('tv,'k) ty)" (infixl "\<circ>\<circ>" 55) where
  "(\<rho> \<circ>\<circ> \<rho>') a = subst_ty \<rho> (\<rho>' a)"

text \<open>
  Composition \<^term>\<open>\<rho> \<circ>\<circ> \<rho>'\<close> is defined by \<^term>\<open>(\<rho> \<circ>\<circ> \<rho>') a = subst_ty \<rho> (\<rho>' a)\<close>.
  Single substitution \<^term>\<open>single_subst \<tau> \<alpha>\<close> maps \<^term>\<open>\<alpha>\<close> to \<^term>\<open>\<tau>\<close> and everything else to itself.
\<close>

definition single_subst :: "('tv,'k) ty \<Rightarrow> 'tv \<Rightarrow> ('tv \<Rightarrow> ('tv,'k) ty)" where
  "single_subst \<tau> \<alpha> = (\<lambda>a. if a = \<alpha> then \<tau> else TyVar a)"

lemma single_subst_same[simp]: "single_subst \<tau> \<alpha> \<alpha> = \<tau>"
  by (simp add: single_subst_def)

lemma single_subst_other[simp]: "a \<noteq> \<alpha> \<Longrightarrow> single_subst \<tau> \<alpha> a = TyVar a"
  by (simp add: single_subst_def)

subsubsection \<open>Basic properties of substitution\<close>

lemma subst_ty_comp:
  "subst_ty \<rho> (subst_ty \<rho>' \<tau>) = subst_ty (\<rho> \<circ>\<circ> \<rho>') \<tau>"
  by (induction \<tau>) (auto simp: comp_subst_def)

lemma subst_ty_id[simp]: "subst_ty TyVar \<tau> = \<tau>"
  by (induction \<tau>) (auto simp: map_idI)

lemma subst_mty_id[simp]: "subst_mty TyVar \<xi> = \<xi>"
  by (cases \<xi>) (auto simp: subst_mty_def)

lemma subst_mty_comp: "subst_mty \<rho> (subst_mty \<rho>' \<xi>) = subst_mty (\<rho> \<circ>\<circ> \<rho>') \<xi>"
  by (cases \<xi>) (auto simp: subst_mty_def subst_ty_comp comp_subst_def)

lemma subst_ty_agree:
  "subst_ty \<rho> \<tau> = subst_ty \<rho>' \<tau> \<longleftrightarrow> (\<forall>\<alpha> \<in> tvars_ty \<tau>. \<rho> \<alpha> = \<rho>' \<alpha>)"
  by (induction \<tau>) auto

lemma subst_ty_cong:
  "(\<And>\<alpha>. \<alpha> \<in> tvars_ty \<tau> \<Longrightarrow> \<rho> \<alpha> = \<rho>' \<alpha>) \<Longrightarrow> subst_ty \<rho> \<tau> = subst_ty \<rho>' \<tau>"
  using subst_ty_agree by blast

lemma subst_ty_swap:
  assumes "\<beta> \<notin> tvars_ty \<tau>"
  shows "subst_ty (single_subst (TyVar \<alpha>) \<beta>) (subst_ty (single_subst (TyVar \<beta>) \<alpha>) \<tau>) = \<tau>"
  using assms
  by (induction \<tau>) (auto simp: map_idI single_subst_def)

text \<open>Substitution distributes over \<^const>\<open>tvars_ty\<close>.\<close>
lemma tvars_ty_subst: "tvars_ty (subst_ty \<rho> \<tau>) = \<Union>(tvars_ty ` \<rho> ` tvars_ty \<tau>)"
  by (induction \<tau>) auto

lemma tvars_mty_subst:
  "tvars_mty (subst_mty \<rho> \<xi>) = \<Union>(tvars_ty ` \<rho> ` tvars_mty \<xi>)"
  by (cases \<xi>) (auto simp: tvars_ty_subst)


subsection \<open>Terms\<close>

text \<open>
  Partially-typed terms: $t ::= x_\xi | c_\xi | (t1~t2)_\xi | (\lambda x_\xi. t)_\zeta$
  We do not quotient by alpha-equivalence.
\<close>

datatype ('tv, 'k, 'v, 'c) trm =
  Vr 'v "('tv,'k) mty"
| Ct 'c "('tv,'k) mty"
| App "('tv,'k,'v,'c) trm" "('tv,'k,'v,'c) trm" "('tv,'k) mty"
| Lam 'v "('tv,'k) mty" "('tv,'k,'v,'c) trm" "('tv,'k) mty"

subsubsection \<open>Type variables of a term\<close>

text \<open>\<^term>\<open>tvars_trm\<close>: set of type variables occurring in all annotations of a term.\<close>

fun tvars_trm :: "('tv,'k,'v,'c) trm \<Rightarrow> 'tv set" where
  "tvars_trm (Vr x \<xi>) = tvars_mty \<xi>"
| "tvars_trm (Ct c \<xi>) = tvars_mty \<xi>"
| "tvars_trm (App t1 t2 \<xi>) = tvars_trm t1 \<union> tvars_trm t2 \<union> tvars_mty \<xi>"
| "tvars_trm (Lam x \<xi> t \<zeta>) = tvars_mty \<xi> \<union> tvars_trm t \<union> tvars_mty \<zeta>"

lemma tvars_trm_finite[simp, intro]: "finite (tvars_trm t)"
  by (induction t) auto

subsubsection \<open>Substitution on terms\<close>

text \<open>\<^term>\<open>subst_trm \<rho> t\<close>: apply type substitution \<^term>\<open>\<rho>\<close> to all type annotations in \<^term>\<open>t\<close>.\<close>

fun subst_trm :: "('tv \<Rightarrow> ('tv,'k) ty) \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm" where
  "subst_trm \<rho> (Vr x \<xi>) = Vr x (subst_mty \<rho> \<xi>)"
| "subst_trm \<rho> (Ct c \<xi>) = Ct c (subst_mty \<rho> \<xi>)"
| "subst_trm \<rho> (App t1 t2 \<xi>) = App (subst_trm \<rho> t1) (subst_trm \<rho> t2) (subst_mty \<rho> \<xi>)"
| "subst_trm \<rho> (Lam x \<xi> t \<zeta>) = Lam x (subst_mty \<rho> \<xi>) (subst_trm \<rho> t) (subst_mty \<rho> \<zeta>)"

lemma subst_trm_comp:
  "subst_trm \<rho> (subst_trm \<rho>' t) = subst_trm (\<rho> \<circ>\<circ> \<rho>') t"
  by (induction t) (auto simp: subst_mty_comp)

lemma subst_trm_id[simp]: "subst_trm TyVar t = t"
  by (induction t) auto

lemma subst_trm_cong:
  "(\<And>\<alpha>. \<alpha> \<in> tvars_trm t \<Longrightarrow> \<rho> \<alpha> = \<rho>' \<alpha>) \<Longrightarrow> subst_trm \<rho> t = subst_trm \<rho>' t"
proof (induction t)
  case (Vr x \<xi>)
  then show ?case by (cases \<xi>) (auto intro: subst_ty_cong)
next
  case (Ct c \<xi>)
  then show ?case by (cases \<xi>) (auto intro: subst_ty_cong)
next
  case (App t1 t2 \<xi>)
  then show ?case by (cases \<xi>) (auto cong: subst_ty_cong)
next
  case (Lam x \<xi> t \<zeta>)
  then show ?case by (cases \<xi>; cases \<zeta>) (auto intro: subst_ty_cong)
qed

lemma subst_trm_agree:
  "subst_trm \<rho> t = subst_trm \<rho>' t \<longleftrightarrow> (\<forall>\<alpha> \<in> tvars_trm t. \<rho> \<alpha> = \<rho>' \<alpha>)"
proof (induction t)
  case (Vr x \<xi>)
  then show ?case by (cases \<xi>) (auto simp: subst_ty_agree)
next
  case (Ct c \<xi>)
  then show ?case by (cases \<xi>) (auto simp: subst_ty_agree)
next
  case (App t1 t2 \<xi>)
  then show ?case by (cases \<xi>) (auto simp: subst_ty_agree)
next
  case (Lam x \<xi> t \<zeta>)
  then show ?case by (cases \<xi>; cases \<zeta>) (auto simp: subst_ty_agree)
qed

text \<open>If \<^term>\<open>subst_trm \<rho> v = v\<close>, then \<^term>\<open>\<rho>\<close> acts as identity on \<^term>\<open>tvars_trm v\<close>.\<close>
lemma subst_trm_id_on_tvars:
  assumes "subst_trm \<rho> v = v" "\<alpha> \<in> tvars_trm v"
  shows "\<rho> \<alpha> = TyVar \<alpha>"
proof -
  from assms(1) have "subst_trm \<rho> v = subst_trm TyVar v" by simp
  then have "\<forall>\<alpha> \<in> tvars_trm v. \<rho> \<alpha> = TyVar \<alpha>" by (simp only: subst_trm_agree)
  with assms(2) show ?thesis by blast
qed

lemma subst_trm_swap:
  assumes "\<beta> \<notin> tvars_trm t"
  shows "subst_trm (single_subst (TyVar \<alpha>) \<beta>) (subst_trm (single_subst (TyVar \<beta>) \<alpha>) t) = t"
  using assms
proof (induction t)
  case (Vr x \<xi>)
  then show ?case by (cases \<xi>) (auto simp: subst_ty_swap)
next
  case (Ct c \<xi>)
  then show ?case by (cases \<xi>) (auto simp: subst_ty_swap)
next
  case (App t1 t2 \<xi>)
  then show ?case by (cases \<xi>) (auto simp: subst_ty_swap)
next
  case (Lam x \<xi> t \<zeta>)
  then show ?case by (cases \<xi>; cases \<zeta>) (auto simp: subst_ty_swap)
qed

lemma tvars_trm_subst:
  "tvars_trm (subst_trm \<rho> t) = \<Union>(tvars_ty ` \<rho> ` tvars_trm t)"
  by (induction t) (auto simp: tvars_mty_subst)

subsubsection \<open>Term predicates: F-term, U-term, C-term\<close>

text \<open>
  F-term: all annotations are types \<^term>\<open>None\<close>.
  U-term: all annotations are \<^term>\<open>None\<close>.
  C-term: variable and constant annotations are types, application and abstraction
  outer annotations are \<^term>\<open>None\<close>, and binding variable annotations are types.
\<close>

fun fterm :: "('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "fterm (Vr x \<xi>) \<longleftrightarrow> \<xi> \<noteq> None"
| "fterm (Ct c \<xi>) \<longleftrightarrow> \<xi> \<noteq> None"
| "fterm (App t1 t2 \<xi>) \<longleftrightarrow> fterm t1 \<and> fterm t2 \<and> \<xi> \<noteq> None"
| "fterm (Lam x \<xi> t \<zeta>) \<longleftrightarrow> \<xi> \<noteq> None \<and> fterm t \<and> \<zeta> \<noteq> None"

fun uterm :: "('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "uterm (Vr x \<xi>) \<longleftrightarrow> \<xi> = None"
| "uterm (Ct c \<xi>) \<longleftrightarrow> \<xi> = None"
| "uterm (App t1 t2 \<xi>) \<longleftrightarrow> uterm t1 \<and> uterm t2 \<and> \<xi> = None"
| "uterm (Lam x \<xi> t \<zeta>) \<longleftrightarrow> \<xi> = None \<and> uterm t \<and> \<zeta> = None"

fun cterm :: "('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "cterm (Vr x \<xi>) \<longleftrightarrow> \<xi> \<noteq> None"
| "cterm (Ct c \<xi>) \<longleftrightarrow> \<xi> \<noteq> None"
| "cterm (App t1 t2 \<xi>) \<longleftrightarrow> cterm t1 \<and> cterm t2 \<and> \<xi> = None"
| "cterm (Lam x \<xi> t \<zeta>) \<longleftrightarrow> \<xi> \<noteq> None \<and> cterm t \<and> \<zeta> = None"

lemma fterm_subst[simp]: "fterm v \<Longrightarrow> fterm (subst_trm \<rho> v)"
  by (induction v) auto

subsubsection \<open>Unambiguity\<close>

text \<open>
  A term is unambiguous if no variable appears as a binding variable at two
  different positions. We define the set of binding variables and then unambiguity.
\<close>

fun bvars :: "('tv,'k,'v,'c) trm \<Rightarrow> 'v set" where
  "bvars (Vr x \<xi>) = {}"
| "bvars (Ct c \<xi>) = {}"
| "bvars (App t1 t2 \<xi>) = bvars t1 \<union> bvars t2"
| "bvars (Lam x \<xi> t \<zeta>) = {x} \<union> bvars t"
                                          
lemma subst_trm_bvars[simp]: "bvars (subst_trm \<rho> t) = bvars t"
  by (induction t) auto

fun unambiguous :: "('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "unambiguous (Vr x \<xi>) \<longleftrightarrow> True"
| "unambiguous (Ct c \<xi>) \<longleftrightarrow> True"
| "unambiguous (App t1 t2 \<xi>) \<longleftrightarrow>
    unambiguous t1 \<and> unambiguous t2 \<and> bvars t1 \<inter> bvars t2 = {}"
| "unambiguous (Lam x \<xi> t \<zeta>) \<longleftrightarrow>
    unambiguous t \<and> x \<notin> bvars t"

lemma subst_trm_unambiguous[simp]: "unambiguous (subst_trm \<rho> t) = unambiguous t"
  by (induction t) auto

subsection \<open>Positions\<close>

text \<open>
  Positions are lists of naturals in \<^term>\<open>{1,2}\<close>.
  \<^term>\<open>poss t\<close>: the set of positions of a term.
  \<^term>\<open>mtp_of t p\<close>: the maybe-type at position \<^term>\<open>p\<close> in \<^term>\<open>t\<close>.
\<close>

fun poss :: "('tv,'k,'v,'c) trm \<Rightarrow> nat list set" where
  "poss (Vr x \<xi>) = {[]}"
| "poss (Ct c \<xi>) = {[]}"
| "poss (App t1 t2 \<xi>) = {[]} \<union> ((\<lambda>p. 1 # p) ` poss t1) \<union> ((\<lambda>p. 2 # p) ` poss t2)"
| "poss (Lam x \<xi> t \<zeta>) = {[]} \<union> {[1]} \<union> ((\<lambda>p. 2 # p) ` poss t)"

lemma poss_finite[simp, intro]: "finite (poss t)"
  by (induction t) auto

lemma nil_in_poss[simp]: "[] \<in> poss t"
  by (cases t) auto

lemma subst_trm_poss[simp]: "poss (subst_trm \<rho> t) = poss t"
  by (induction t) auto

fun mtp_of :: "('tv,'k,'v,'c) trm \<Rightarrow> nat list \<Rightarrow> ('tv,'k) mty" where
  "mtp_of (Vr x \<xi>) p = \<xi>"
| "mtp_of (Ct c \<xi>) p = \<xi>"
| "mtp_of (App t1 t2 \<xi>) p = (case p of
    [] \<Rightarrow> \<xi>
  | (Suc 0 # p') \<Rightarrow> mtp_of t1 p'
  | (Suc (Suc 0) # p') \<Rightarrow> mtp_of t2 p'
  | _ \<Rightarrow> None)"
| "mtp_of (Lam x \<xi> t \<zeta>) p = (case p of
    [] \<Rightarrow> \<zeta>
  | [Suc 0] \<Rightarrow> \<xi>
  | (Suc (Suc 0) # p') \<Rightarrow> mtp_of t p'
  | _ \<Rightarrow> None)"

text \<open>
    \<^term>\<open>mtpOf t\<close> is the maybe-type of the root of \<^term>\<open>t\<close>.
\<close>

abbreviation mtp_of_root :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k) mty" where
  "mtp_of_root t \<equiv> mtp_of t []"

lemma mtp_of_subst:
  assumes "p \<in> poss t"
  shows "mtp_of (subst_trm \<rho> t) p = subst_mty \<rho> (mtp_of t p)"
  using assms by (induction t arbitrary: p) (auto split: list.splits nat.splits)

lemma tvars_trm_eq_UN_mtp:
  "tvars_trm t = (\<Union>p \<in> poss t. tvars_mty (mtp_of t p))"
  by (induction t) (auto simp: image_iff)

lemma fterm_mtp_of_Some:
  assumes "fterm v" "p \<in> poss v"
  shows "\<exists>\<sigma>. mtp_of v p = Some \<sigma>"
  using assms by (induction v arbitrary: p) (auto split: list.splits nat.splits)

subsubsection \<open>Removing annotations\<close>

fun remove_annot :: "('tv,'k,'v,'c) trm \<Rightarrow> nat list \<Rightarrow> ('tv,'k,'v,'c) trm" where
  "remove_annot (Vr x \<xi>) p = Vr x None"
| "remove_annot (Ct c \<xi>) p = Ct c None"
| "remove_annot (App t1 t2 \<xi>) p = (case p of
    [] \<Rightarrow> App t1 t2 None
  | Suc 0 # p' \<Rightarrow> App (remove_annot t1 p') t2 \<xi>
  | Suc (Suc 0) # p' \<Rightarrow> App t1 (remove_annot t2 p') \<xi>
  | _ \<Rightarrow> App t1 t2 None)"
| "remove_annot (Lam x \<xi> t \<zeta>) p = (case p of
    [] \<Rightarrow> Lam x \<xi> t None
  | [Suc 0] \<Rightarrow> Lam x None t \<zeta>
  | Suc (Suc 0) # p' \<Rightarrow> Lam x \<xi> (remove_annot t p') \<zeta>
  | _ \<Rightarrow> Lam x \<xi> t None)"

lemma mtp_of_remove_self:
  assumes "p \<in> poss t"
  shows "mtp_of (remove_annot t p) p = None"
  using assms by (induction t arbitrary: p) auto

lemma mtp_of_remove_other:
  assumes "p \<in> poss t" "q \<in> poss t" "q \<noteq> p"
  shows "mtp_of (remove_annot t p) q = mtp_of t q"
  using assms
  by (induction t arbitrary: p q) fastforce+

lemma remove_annot_poss:
  assumes "p \<in> poss t"
  shows "poss (remove_annot t p) = poss t"
  using assms by (induction t arbitrary: p) auto

lemma remove_annot_bvars:
  assumes "p \<in> poss t"
  shows "bvars (remove_annot t p) = bvars t"
  using assms by (induction t arbitrary: p) auto

lemma remove_annot_unambiguous:
  assumes "p \<in> poss t" "unambiguous t"
  shows "unambiguous (remove_annot t p)"
  using assms by (induction t arbitrary: p) (auto simp: remove_annot_bvars)

text \<open>Erase: remove all type annotations.\<close>

fun erase :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm" where
  "erase (Vr x \<xi>) = Vr x None"
| "erase (Ct c \<xi>) = Ct c None"
| "erase (App t1 t2 \<xi>) = App (erase t1) (erase t2) None"
| "erase (Lam x \<xi> t \<zeta>) = Lam x None (erase t) None"

lemma erase_uterm[simp]: "uterm (erase t)"
  by (induction t) auto

lemma erase_poss[simp]: "poss (erase t) = poss t"
  by (induction t) auto

lemma erase_bvars[simp]: "bvars (erase t) = bvars t"
  by (induction t) auto

lemma erase_unambiguous[simp]: "unambiguous (erase t) = unambiguous t"
  by (induction t) auto

subsection \<open>Completion relations for types and terms\<close>

definition mcompl :: "('tv,'k) mty \<Rightarrow> ('tv,'k) mty \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>m" 50) where
  "\<xi> \<sqsubseteq>\<^sub>m \<zeta> \<longleftrightarrow> (\<xi> = None \<or> \<xi> = \<zeta>)"

lemma mcompl_None[simp, intro]: "None \<sqsubseteq>\<^sub>m \<zeta>"
  by (simp add: mcompl_def)

lemma mcompl_refl[simp, intro]: "\<xi> \<sqsubseteq>\<^sub>m \<xi>"
  by (simp add: mcompl_def)

lemma mcompl_Some_iff[simp]: "Some \<sigma> \<sqsubseteq>\<^sub>m \<zeta> \<longleftrightarrow> \<zeta> = Some \<sigma>"
  by (auto simp: mcompl_def)

lemma mcompl_antisym: "\<lbrakk> \<xi> \<sqsubseteq>\<^sub>m \<zeta>; \<zeta> \<sqsubseteq>\<^sub>m \<xi> \<rbrakk> \<Longrightarrow> \<xi> = \<zeta>"
  by (auto simp: mcompl_def)

lemma mcompl_trans: "\<lbrakk> \<xi> \<sqsubseteq>\<^sub>m \<zeta>; \<zeta> \<sqsubseteq>\<^sub>m \<chi> \<rbrakk> \<Longrightarrow> \<xi> \<sqsubseteq>\<^sub>m \<chi>"
  by (auto simp: mcompl_def)

inductive compl :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  compl_Vr: "\<xi> \<sqsubseteq>\<^sub>m \<zeta> \<Longrightarrow> Vr x \<xi> \<sqsubseteq> Vr x \<zeta>"
| compl_Ct: "\<xi> \<sqsubseteq>\<^sub>m \<zeta> \<Longrightarrow> Ct c \<xi> \<sqsubseteq> Ct c \<zeta>"
| compl_App: "\<lbrakk> s1 \<sqsubseteq> s1'; s2 \<sqsubseteq> s2'; \<xi> \<sqsubseteq>\<^sub>m \<xi>' \<rbrakk> \<Longrightarrow> App s1 s2 \<xi> \<sqsubseteq> App s1' s2' \<xi>'"
| compl_Lam: "\<lbrakk> \<zeta> \<sqsubseteq>\<^sub>m \<zeta>'; t \<sqsubseteq> t'; \<xi> \<sqsubseteq>\<^sub>m \<xi>' \<rbrakk> \<Longrightarrow> Lam x \<zeta> t \<xi> \<sqsubseteq> Lam x \<zeta>' t' \<xi>'"

subsubsection \<open>Inversion rules\<close>
text \<open>Inversion rules for \<^term>\<open>compl\<close>. These follow from the cases rule.\<close>

lemma compl_Vr_leftE:
  assumes "Vr x \<xi> \<sqsubseteq> t"
  obtains \<xi>' where "\<xi> \<sqsubseteq>\<^sub>m \<xi>'" "t = Vr x \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_Ct_leftE:
  assumes "Ct c \<xi> \<sqsubseteq> t"
  obtains \<xi>' where "\<xi> \<sqsubseteq>\<^sub>m \<xi>'" "t = Ct c \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_App_leftE:
  assumes "App s1 s2 \<xi> \<sqsubseteq> t"
  obtains s1' s2' \<xi>' where "s1 \<sqsubseteq> s1'" "s2 \<sqsubseteq> s2'" "\<xi> \<sqsubseteq>\<^sub>m \<xi>'" "t = App s1' s2' \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_Lam_leftE:
  assumes "Lam x \<zeta> s \<xi> \<sqsubseteq> t"
  obtains s' \<zeta>' \<xi>' where "s \<sqsubseteq> s'" "\<zeta> \<sqsubseteq>\<^sub>m \<zeta>'" "\<xi> \<sqsubseteq>\<^sub>m \<xi>'" "t = Lam x \<zeta>' s' \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_Vr_rightE:
  assumes "t \<sqsubseteq> Vr x \<xi>"
  obtains \<xi>' where "\<xi>' \<sqsubseteq>\<^sub>m \<xi>" "t = Vr x \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_Ct_rightE:
  assumes "t \<sqsubseteq> Ct c \<xi>"
  obtains \<xi>' where "\<xi>' \<sqsubseteq>\<^sub>m \<xi>" "t = Ct c \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_App_rightE:
  assumes "t \<sqsubseteq> App s1 s2 \<xi>"
  obtains s1' s2' \<xi>' where "s1' \<sqsubseteq> s1" "s2' \<sqsubseteq> s2" "\<xi>' \<sqsubseteq>\<^sub>m \<xi>" "t = App s1' s2' \<xi>'"
  using assms by (cases rule: compl.cases) auto

lemma compl_Lam_rightE:
  assumes "t \<sqsubseteq> Lam x \<zeta> s \<xi>"
  obtains s' \<zeta>' \<xi>' where "s' \<sqsubseteq> s" "\<zeta>' \<sqsubseteq>\<^sub>m \<zeta>" "\<xi>' \<sqsubseteq>\<^sub>m \<xi>" "t = Lam x \<zeta>' s' \<xi>'"
  using assms by (cases rule: compl.cases) auto

subsubsection \<open>Basic properties\<close>
lemma compl_refl[simp, intro]: "t \<sqsubseteq> t"
  by (induction t) (auto intro: compl.intros)

lemma compl_poss_eq: "t \<sqsubseteq> s \<Longrightarrow> poss t = poss s"
  by (induction t s rule: compl.induct) auto

lemma compl_bvars_eq: "t \<sqsubseteq> s \<Longrightarrow> bvars t = bvars s"
  by (induction t s rule: compl.induct) auto

lemma compl_unambiguous: "t \<sqsubseteq> s \<Longrightarrow> unambiguous t = unambiguous s"
  by (induction t s rule: compl.induct) (auto simp: compl_bvars_eq)

lemma erase_compl[simp, intro]: "erase t \<sqsubseteq> t"
  by (induction t) (auto intro: compl.intros)

lemma remove_annot_compl:
  assumes "p \<in> poss t"
  shows "remove_annot t p \<sqsubseteq> t"
  using assms by (induction t arbitrary: p) (auto split: list.splits nat.splits intro: compl.intros)

lemma compl_trans: "\<lbrakk> s \<sqsubseteq> t; t \<sqsubseteq> u \<rbrakk> \<Longrightarrow> s \<sqsubseteq> u"
  by (induction s t arbitrary: u rule: compl.induct)
    (auto elim!: compl_Vr_leftE compl_Ct_leftE compl_App_leftE compl_Lam_leftE 
      intro: compl.intros dest: mcompl_trans)

lemma compl_antisym: "\<lbrakk> s \<sqsubseteq> t; t \<sqsubseteq> s \<rbrakk> \<Longrightarrow> s = t"
  by (induction s t rule: compl.induct) (auto elim!: compl_Vr_rightE compl_Ct_rightE 
      compl_App_rightE compl_Lam_rightE dest: mcompl_antisym)

lemma compl_mtp_of_root: "t \<sqsubseteq> s \<Longrightarrow> mtp_of t [] \<sqsubseteq>\<^sub>m mtp_of s []"
  by (erule compl.cases) auto

subsubsection \<open>Positions and completions\<close>

lemma compl_mtp_of:
  assumes "t \<sqsubseteq> s"
  shows "mtp_of t p \<sqsubseteq>\<^sub>m mtp_of s p"
  using assms
  by (induction t s arbitrary: p rule: compl.induct) (auto split: list.splits nat.splits)

text \<open>\<^term>\<open>erase t \<sqsubseteq> s\<close> is preserved by \<^term>\<open>remove_annot\<close> (erased term has \<^term>\<open>None\<close> everywhere).\<close>
lemma erase_compl_remove_annot:
  assumes "erase t \<sqsubseteq> s"
  shows "erase t \<sqsubseteq> remove_annot s p"
  using assms
proof (induction t arbitrary: s p)
  case (Vr x \<xi>)
  then show ?case by (auto elim!: compl_Vr_leftE intro: compl.intros)
next
  case (Ct c \<xi>)
  then show ?case by (auto elim!: compl_Ct_leftE intro: compl.intros)
next
  case (App t1 t2 \<xi>)
  from App.prems(1) obtain s1 s2 \<xi>s where seq: "s = App s1 s2 \<xi>s"
    "erase t1 \<sqsubseteq> s1" "erase t2 \<sqsubseteq> s2"
    by (auto elim!: compl_App_leftE)
  show ?case using App.prems seq
    by (cases p) (auto split: nat.splits intro: compl.intros App.IH)
next
  case (Lam x \<xi> t \<zeta>)
  from Lam.prems(1) obtain s0 \<zeta>s \<xi>s where seq: "s = Lam x \<zeta>s s0 \<xi>s"
    "erase t \<sqsubseteq> s0"
    by (auto elim!: compl_Lam_leftE)
  show ?case using Lam.prems seq
    by (cases p) (auto split: nat.splits list.splits intro: compl.intros Lam.IH)
qed

text \<open>
  Same shape extensionality: If \<^term>\<open>t \<sqsubseteq> u\<close> and \<^term>\<open>t \<sqsubseteq> u'\<close>, and \<^term>\<open>u\<close>, \<^term>\<open>u'\<close> are F-terms 
  with the same type at every position, then \<^term>\<open>u = u'\<close>.
\<close>

lemma fterm_extensionality:
  assumes "t \<sqsubseteq> u" "t \<sqsubseteq> u'" "fterm u" "fterm u'" "\<And>p. p \<in> poss t \<Longrightarrow> mtp_of u p = mtp_of u' p"
  shows "u = u'"
  using assms
proof (induction t arbitrary: u u')
  case (Vr x \<xi>)
  from Vr.prems(1) obtain \<xi>u where "u = Vr x \<xi>u" by (auto elim!: compl_Vr_leftE)
  moreover from Vr.prems(2) obtain \<xi>u' where "u' = Vr x \<xi>u'" by (auto elim!: compl_Vr_leftE)
  ultimately show "u = u'" using Vr.prems(5)[of "[]"] by auto
next
  case (Ct c \<xi>)
  from Ct.prems(1) obtain \<xi>u where "u = Ct c \<xi>u" by (auto elim!: compl_Ct_leftE)
  moreover from Ct.prems(2) obtain \<xi>u' where "u' = Ct c \<xi>u'" by (auto elim!: compl_Ct_leftE)
  ultimately show "u = u'" using Ct.prems(5)[of "[]"] by auto
next
  case (App t1 t2 \<xi>)
  from App.prems(1) obtain u1 u2 \<xi>u where ueq: "u = App u1 u2 \<xi>u"
    "t1 \<sqsubseteq> u1" "t2 \<sqsubseteq> u2" by (auto elim!: compl_App_leftE)
  from App.prems(2) obtain u1' u2' \<xi>u' where u'eq: "u' = App u1' u2' \<xi>u'"
    "t1 \<sqsubseteq> u1'" "t2 \<sqsubseteq> u2'" by (auto elim!: compl_App_leftE)
  have fu: "fterm u1" "fterm u2" using App.prems(3) ueq(1) by auto
  have fu': "fterm u1'" "fterm u2'" using App.prems(4) u'eq(1) by auto
  have eq1: "\<And>p. p \<in> poss t1 \<Longrightarrow> mtp_of u1 p = mtp_of u1' p"
  proof -
    fix p assume "p \<in> poss t1"
    then have "Suc 0 # p \<in> poss (App t1 t2 \<xi>)" by auto
    from App.prems(5)[OF this] ueq(1) u'eq(1) show "mtp_of u1 p = mtp_of u1' p" by auto
  qed
  have eq2: "\<And>p. p \<in> poss t2 \<Longrightarrow> mtp_of u2 p = mtp_of u2' p"
  proof -
    fix p assume "p \<in> poss t2"
    then have "2 # p \<in> poss (App t1 t2 \<xi>)" by auto
    from App.prems(5)[OF this] ueq(1) u'eq(1) show "mtp_of u2 p = mtp_of u2' p" by auto
  qed
  have "u1 = u1'" using App.IH(1)[OF ueq(2) u'eq(2) fu(1) fu'(1) eq1] .
  moreover have "u2 = u2'" using App.IH(2)[OF ueq(3) u'eq(3) fu(2) fu'(2) eq2] .
  moreover have "\<xi>u = \<xi>u'" using App.prems(5)[of "[]"] ueq(1) u'eq(1) by auto
  ultimately show "u = u'" using ueq(1) u'eq(1) by auto
next
  case (Lam x \<xi> t \<zeta>)
  from Lam.prems(1) obtain u0 \<zeta>u \<xi>u where ueq: "u = Lam x \<zeta>u u0 \<xi>u"
    "t \<sqsubseteq> u0" by (auto elim!: compl_Lam_leftE)
  from Lam.prems(2) obtain u0' \<zeta>u' \<xi>u' where u'eq: "u' = Lam x \<zeta>u' u0' \<xi>u'"
    "t \<sqsubseteq> u0'" by (auto elim!: compl_Lam_leftE)
  have fu: "fterm u0" using Lam.prems(3) ueq(1) by auto
  have fu': "fterm u0'" using Lam.prems(4) u'eq(1) by auto
  have eq0: "\<And>p. p \<in> poss t \<Longrightarrow> mtp_of u0 p = mtp_of u0' p"
  proof -
    fix p assume "p \<in> poss t"
    then have "2 # p \<in> poss (Lam x \<xi> t \<zeta>)" by auto
    from Lam.prems(5)[OF this] ueq(1) u'eq(1) show "mtp_of u0 p = mtp_of u0' p" by auto
  qed
  have "u0 = u0'" using Lam.IH[OF ueq(2) u'eq(2) fu fu' eq0] .
  moreover have "\<zeta>u = \<zeta>u'" using Lam.prems(5)[of "[Suc 0]"] ueq(1) u'eq(1) by auto
  moreover have "\<xi>u = \<xi>u'" using Lam.prems(5)[of "[]"] ueq(1) u'eq(1) by auto
  ultimately show "u = u'" using ueq(1) u'eq(1) by auto
qed

text \<open>
  The crucial fact for completeness:
  If \<^term>\<open>t \<sqsubseteq> u\<close> and \<^term>\<open>u\<close> is an instance of \<^term>\<open>v\<close> (\<^term>\<open>u \<le> v\<close>), 
  and every type variable of \<^term>\<open>v\<close> is "witnessed" at some
  non-bot position of t, then \<^term>\<open>u\<close> is the unique F-term \<^term>\<open>u'\<close> with \<^term>\<open>t \<sqsubseteq> u'\<close> and \<^term>\<open>u' \<le> v\<close>.
\<close>

theorem crucial_uniqueness:
  assumes compl_u: "t \<sqsubseteq> u" and fu: "fterm u"
    and inst_u: "\<exists>\<rho>. u = subst_trm \<rho> v" and fv: "fterm v"
    and cover: "\<forall>\<alpha> \<in> tvars_trm v. \<exists>p \<in> poss v. \<alpha> \<in> tvars_mty (mtp_of v p) \<and> mtp_of t p \<noteq> None"
    and compl_u': "t \<sqsubseteq> u'" and fu': "fterm u'"
    and inst_u': "\<exists>\<rho>'. u' = subst_trm \<rho>' v"
  shows "u = u'"
proof -
  from inst_u obtain \<rho> where u_eq: "u = subst_trm \<rho> v" by auto
  from inst_u' obtain \<rho>' where u'_eq: "u' = subst_trm \<rho>' v" by auto
  text \<open>By @{thm fterm_extensionality}, suffices to show \<^term>\<open>\<forall>p \<in> poss t. mtp_of u p = mtp_of u' p\<close>.\<close>
  have poss_eq: "poss t = poss v"
    using compl_poss_eq[OF compl_u] u_eq by simp
  show "u = u'"
  proof (rule fterm_extensionality[OF compl_u compl_u' fu fu'])
    fix p assume p_in: "p \<in> poss t"
    then have pv: "p \<in> poss v" using poss_eq by auto
    have u_mtp: "mtp_of u p = subst_mty \<rho> (mtp_of v p)"
      using mtp_of_subst[OF pv] u_eq by auto
    have u'_mtp: "mtp_of u' p = subst_mty \<rho>' (mtp_of v p)"
      using mtp_of_subst[OF pv] u'_eq by auto
    text \<open>Since v is an F-term, \<^term>\<open>\<exists>\<sigma>. mtp_of v p = Some \<sigma>\<close>.\<close>
    have "\<exists>\<sigma>. mtp_of v p = Some \<sigma>" using fterm_mtp_of_Some[OF fv pv] .
    then obtain \<sigma> where vsig: "mtp_of v p = Some \<sigma>" by auto
    text \<open>Need to show \<^term>\<open>subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>\<close>.
      By @{thm subst_ty_agree}, suffices to show \<^term>\<open>\<forall>\<alpha> \<in> tvars_ty \<sigma>. \<rho> \<alpha> = \<rho>' \<alpha>\<close>.\<close>
    have "subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>"
    proof (rule subst_ty_cong)
      fix \<alpha> assume alpha_in: "\<alpha> \<in> tvars_ty \<sigma>"
      then have "\<alpha> \<in> tvars_trm v"
        using vsig pv tvars_trm_eq_UN_mtp by fastforce
      from cover[rule_format, OF this]
      obtain q where qv: "q \<in> poss v" and alpha_q: "\<alpha> \<in> tvars_mty (mtp_of v q)"
        and t_q: "mtp_of t q \<noteq> None" by auto
      have qt: "q \<in> poss t" using poss_eq qv by auto
      text \<open>Since \<^term>\<open>mtp_of t q\<close> is not \<^term>\<open>None\<close> and \<^term>\<open>t \<sqsubseteq> u\<close>, \<^term>\<open>u'\<close>, 
        the annotation is preserved.\<close>
      have "mtp_of t q \<sqsubseteq>\<^sub>m mtp_of u q" using compl_mtp_of[OF compl_u] .
      moreover have "mtp_of t q \<sqsubseteq>\<^sub>m mtp_of u' q" using compl_mtp_of[OF compl_u'] .
      ultimately have eq_at_q: "mtp_of u q = mtp_of t q \<and> mtp_of u' q = mtp_of t q"
        using t_q by (auto simp: mcompl_def)
      then have "mtp_of u q = mtp_of u' q" by simp
      text \<open>Now use @{thm mtp_of_subst} to relate to substitutions.\<close>
      have "subst_mty \<rho> (mtp_of v q) = subst_mty \<rho>' (mtp_of v q)"
        using \<open>mtp_of u q = mtp_of u' q\<close> mtp_of_subst[OF qv] u_eq u'_eq by auto
      then show "\<rho> \<alpha> = \<rho>' \<alpha>" using alpha_q
        by (cases "mtp_of v q") (auto simp: subst_ty_agree)
    qed
    then show "mtp_of u p = mtp_of u' p" using u_mtp u'_mtp vsig by simp
  qed
qed

text \<open>Strict \<^term>\<open>(\<sqsubseteq>)\<close> witnesses a position difference.\<close>
lemma compl_strict_witness:
  assumes "s' \<sqsubseteq> s" "s' \<noteq> s"
  shows "\<exists>p \<in> poss s. mtp_of s' p = None \<and> mtp_of s p \<noteq> None"
  using assms
proof (induction s' s rule: compl.induct)
  case (compl_App s1 s1' s2 s2' \<xi> \<xi>')
  show ?case
  proof (cases "s1 = s1'")
    case True
    then show ?thesis
    proof (cases "s2 = s2'")
      case True
      with \<open>s1 = s1'\<close> compl_App.prems compl_App.hyps
      show ?thesis by (auto simp: mcompl_def)
    next
      case False
      with compl_App.IH(2) obtain p where "p \<in> poss s2'" "mtp_of s2 p = None" "mtp_of s2' p \<noteq> None"
        by auto
      then show ?thesis by (intro bexI[of _ "2 # _"]) auto
    qed
  next
    case False
    with compl_App.IH(1) obtain p where "p \<in> poss s1'" "mtp_of s1 p = None" "mtp_of s1' p \<noteq> None"
      by auto
    then show ?thesis by (intro bexI[of _ "Suc 0 # p"]) auto
  qed
next
  case (compl_Lam \<zeta> \<zeta>' t t' \<xi> \<xi>' x)
  show ?case
  proof (cases "t = t'")
    case True
    then show ?thesis
    proof (cases "\<zeta> = \<zeta>'")
      case True
      with \<open>t = t'\<close> compl_Lam.prems compl_Lam.hyps
      show ?thesis by (auto simp: mcompl_def)
    next
      case False
      with compl_Lam.hyps show ?thesis
        by (auto simp: mcompl_def intro!: bexI[of _ "[Suc 0]"])
    qed
  next
    case False
    with compl_Lam.IH obtain p where "p \<in> poss t'" "mtp_of t p = None" "mtp_of t' p \<noteq> None"
      by auto
    then show ?thesis by auto
  qed
qed (auto simp: mcompl_def)

text \<open>Multiple completions from agreeing substitutions.\<close>
lemma multiple_compl:
  assumes "s \<sqsubseteq> subst_trm \<rho> v"
    "\<And>\<alpha> p. \<lbrakk> p \<in> poss v; \<alpha> \<in> tvars_mty (mtp_of v p); mtp_of s p \<noteq> None \<rbrakk> \<Longrightarrow> \<rho> \<alpha> = \<rho>' \<alpha>"
  shows "s \<sqsubseteq> subst_trm \<rho>' v"
  using assms
proof (induction v arbitrary: s)
  case (Vr x \<xi>)
  show ?case
  proof (cases \<xi>)
    case None then show ?thesis using Vr by (auto elim!: compl_Vr_rightE intro: compl.intros)
  next
    case (Some \<sigma>)
    from Vr.prems(1) Some obtain \<xi>s where seq: "s = Vr x \<xi>s" "\<xi>s \<sqsubseteq>\<^sub>m Some (subst_ty \<rho> \<sigma>)"
      by (auto elim!: compl_Vr_rightE)
    show ?thesis
    proof (cases "\<xi>s")
      case None then show ?thesis using seq(1) Some by (auto intro: compl.intros)
    next
      case (Some \<tau>)
      then have "\<tau> = subst_ty \<rho> \<sigma>" using seq(2) by (auto simp: mcompl_def)
      moreover have "\<forall>\<alpha>\<in>tvars_ty \<sigma>. \<rho> \<alpha> = \<rho>' \<alpha>"
        using Vr.prems(2)[of "[]"] seq(1) Some \<open>\<xi> = Some \<sigma>\<close> by auto
      then have "subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>" by (intro subst_ty_cong) auto
      ultimately have "\<tau> = subst_ty \<rho>' \<sigma>" by simp
      then show ?thesis using seq(1) Some \<open>\<xi> = Some \<sigma>\<close> by (auto intro: compl.intros simp: mcompl_def)
    qed
  qed
next
  case (Ct c \<xi>)
  then show ?case
  proof (cases \<xi>)
    case None then show ?thesis using Ct by (auto elim!: compl_Ct_rightE intro: compl.intros)
  next
    case (Some \<sigma>)
    from Ct.prems(1) Some obtain \<xi>s where seq: "s = Ct c \<xi>s" "\<xi>s \<sqsubseteq>\<^sub>m Some (subst_ty \<rho> \<sigma>)"
      by (auto elim!: compl_Ct_rightE)
    show ?thesis
    proof (cases "\<xi>s")
      case None then show ?thesis using seq(1) Some by (auto intro: compl.intros)
    next
      case (Some \<tau>)
      then have "\<tau> = subst_ty \<rho> \<sigma>" using seq(2) by (auto simp: mcompl_def)
      moreover have "\<forall>\<alpha>\<in>tvars_ty \<sigma>. \<rho> \<alpha> = \<rho>' \<alpha>"
        using Ct.prems(2)[of "[]"] seq(1) Some \<open>\<xi> = Some \<sigma>\<close> by auto
      then have "subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>" by (intro subst_ty_cong) auto
      ultimately have "\<tau> = subst_ty \<rho>' \<sigma>" by simp
      then show ?thesis using seq(1) Some \<open>\<xi> = Some \<sigma>\<close> by (auto intro: compl.intros simp: mcompl_def)
    qed
  qed
next
  case (App t1 t2 \<xi>)
  from App.prems(1) obtain s1 s2 \<xi>s where seq: "s = App s1 s2 \<xi>s"
    "s1 \<sqsubseteq> subst_trm \<rho> t1" "s2 \<sqsubseteq> subst_trm \<rho> t2" "\<xi>s \<sqsubseteq>\<^sub>m subst_mty \<rho> \<xi>"
    by (auto elim!: compl_App_rightE)
  have "s1 \<sqsubseteq> subst_trm \<rho>' t1"
  proof (rule App.IH(1)[OF seq(2)])
    fix \<alpha> p assume "p \<in> poss t1" "\<alpha> \<in> tvars_mty (mtp_of t1 p)" "mtp_of s1 p \<noteq> None"
    then show "\<rho> \<alpha> = \<rho>' \<alpha>" using App.prems(2)[of "Suc 0 # p" \<alpha>] seq(1) by auto
  qed
  moreover have "s2 \<sqsubseteq> subst_trm \<rho>' t2"
  proof (rule App.IH(2)[OF seq(3)])
    fix \<alpha> p assume "p \<in> poss t2" "\<alpha> \<in> tvars_mty (mtp_of t2 p)" "mtp_of s2 p \<noteq> None"
    then show "\<rho> \<alpha> = \<rho>' \<alpha>" using App.prems(2)[of "2 # p" \<alpha>] seq(1) by auto
  qed
  moreover have "\<xi>s \<sqsubseteq>\<^sub>m subst_mty \<rho>' \<xi>"
  proof (cases \<xi>)
    case None then show ?thesis using seq(4) by auto
  next
    case (Some \<sigma>)
    show ?thesis
    proof (cases \<xi>s)
      case None then show ?thesis by auto
    next
      case (Some \<tau>)
      then have "\<tau> = subst_ty \<rho> \<sigma>" using seq(4) \<open>\<xi> = Some \<sigma>\<close> by (auto simp: mcompl_def)
      moreover have "\<forall>\<alpha> \<in> tvars_ty \<sigma>. \<rho> \<alpha> = \<rho>' \<alpha>"
        using App.prems(2)[of "[]"] seq(1) Some \<open>\<xi> = Some \<sigma>\<close> by auto
      then have "subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>" by (intro subst_ty_cong) auto
      ultimately show ?thesis using Some \<open>\<xi> = Some \<sigma>\<close> by (auto simp: mcompl_def)
    qed
  qed
  ultimately show ?case using seq(1) by (auto intro: compl.intros)
next
  case (Lam x \<xi> t \<zeta>)
  from Lam.prems(1) obtain s0 \<zeta>s \<xi>s where
    seq: "s = Lam x \<zeta>s s0 \<xi>s"
    "s0 \<sqsubseteq> subst_trm \<rho> t" "\<zeta>s \<sqsubseteq>\<^sub>m subst_mty \<rho> \<xi>" "\<xi>s \<sqsubseteq>\<^sub>m subst_mty \<rho> \<zeta>"
    by (auto elim!: compl_Lam_rightE)
  have "s0 \<sqsubseteq> subst_trm \<rho>' t"
  proof (rule Lam.IH[OF seq(2)])
    fix \<alpha> p assume "p \<in> poss t" "\<alpha> \<in> tvars_mty (mtp_of t p)" "mtp_of s0 p \<noteq> None"
    then show "\<rho> \<alpha> = \<rho>' \<alpha>" using Lam.prems(2)[of "2 # p" \<alpha>] seq(1) by auto
  qed
  moreover have "\<zeta>s \<sqsubseteq>\<^sub>m subst_mty \<rho>' \<xi>"
  proof (cases \<xi>)
    case None then show ?thesis using seq(3) by auto
  next
    case (Some \<sigma>)
    show ?thesis
    proof (cases "\<zeta>s")
      case None then show ?thesis by auto
    next
      case (Some \<tau>)
      then have "\<tau> = subst_ty \<rho> \<sigma>" using seq(3) \<open>\<xi> = Some \<sigma>\<close> by (auto simp: mcompl_def)
    have "\<forall>\<alpha>' \<in> tvars_ty \<sigma>. \<rho> \<alpha>' = \<rho>' \<alpha>'"
    proof (intro ballI)
      fix \<alpha>' assume "\<alpha>' \<in> tvars_ty \<sigma>"
      then show "\<rho> \<alpha>' = \<rho>' \<alpha>'"
        using Lam.prems(2)[of "[Suc 0]" \<alpha>'] \<open>\<xi> = Some \<sigma>\<close> seq(1) Some by auto
    qed
    then have eq: "subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>" by (intro subst_ty_cong) auto
    from \<open>\<tau> = subst_ty \<rho> \<sigma>\<close> eq have "\<tau> = subst_ty \<rho>' \<sigma>" by simp
    then show ?thesis using Some \<open>\<xi> = Some \<sigma>\<close> by (auto simp: mcompl_def)
    qed
  qed
  moreover have "\<xi>s \<sqsubseteq>\<^sub>m subst_mty \<rho>' \<zeta>"
  proof (cases \<zeta>)
    case None then show ?thesis using seq(4) by auto
  next
    case (Some \<sigma>)
    show ?thesis
    proof (cases "\<xi>s")
      case None then show ?thesis by auto
    next
      case (Some \<tau>)
      then have "\<tau> = subst_ty \<rho> \<sigma>" using seq(4) \<open>\<zeta> = Some \<sigma>\<close> by (auto simp: mcompl_def)
      moreover have "\<forall>\<alpha> \<in> tvars_ty \<sigma>. \<rho> \<alpha> = \<rho>' \<alpha>"
        using Lam.prems(2)[of "[]"] seq(1) Some \<open>\<zeta> = Some \<sigma>\<close> by auto
      then have "subst_ty \<rho> \<sigma> = subst_ty \<rho>' \<sigma>" by (intro subst_ty_cong) auto
      ultimately show ?thesis using Some \<open>\<zeta> = Some \<sigma>\<close> by (auto simp: mcompl_def)
    qed
  qed
  ultimately show ?case using seq(1) by (auto intro: compl.intros)
qed

subsubsection \<open>Well-typedness and type inference\<close>

text \<open>
  Well-typedness predicate on F-terms.
  We work in a locale fixing the constant-typing function \<^term>\<open>ctpOf\<close>.
  We also use the abbreviation \<^term>\<open>tpOf\<close> for the type of an F-term.
\<close>

abbreviation tpOf :: "('tv,'k,'v,'c) trm \<Rightarrow> nat list \<Rightarrow> ('tv,'k) ty" where
  "tpOf u p \<equiv> the (mtp_of u p)"

abbreviation tpOfR :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k) ty" where
  "tpOfR u \<equiv> the (mtp_of u [])"

text \<open>Free typed variables of a term: pairs \<^term>\<open>(x, \<sigma>)\<close> where variable \<^term>\<open>x\<close>
  occurs free with type annotation \<^term>\<open>Some \<sigma>\<close>.\<close>

fun fvars :: "('tv,'k,'v,'c) trm \<Rightarrow> ('v \<times> ('tv,'k) ty) set" where
  "fvars (Vr x (Some \<sigma>)) = {(x, \<sigma>)}"
| "fvars (Vr x None) = {}"
| "fvars (Ct c \<xi>) = {}"
| "fvars (App t1 t2 \<xi>) = fvars t1 \<union> fvars t2"
| "fvars (Lam x \<xi> t \<zeta>) = {(y, \<sigma>) \<in> fvars t. y \<noteq> x}"

lemma fvars_subst: "fvars (subst_trm \<rho> t) = (\<lambda>(x, \<sigma>). (x, subst_ty \<rho> \<sigma>)) ` fvars t"
proof (induction t)
  case (Vr x \<xi>) then show ?case by (cases \<xi>) auto
next
  case (Ct c \<xi>) then show ?case by auto
next
  case (App t1 t2 \<xi>) then show ?case by auto
next
  case (Lam x \<xi> t \<zeta>) then show ?case by auto
qed

locale signature =
  fixes ctpOf :: "'c \<Rightarrow> ('tv,'k) ty"
begin

inductive wt :: "('tv,'k,'v,'c) trm \<Rightarrow> bool" ("\<turnstile> _" [50] 50) where
  wt_Vr: "\<turnstile> Vr x (Some \<sigma>)"
| wt_Ct: "\<exists>\<rho>. \<sigma> = subst_ty \<rho> (ctpOf c) \<Longrightarrow> \<turnstile> Ct c (Some \<sigma>)"
| wt_App: "\<lbrakk> \<turnstile> u; \<turnstile> v; tpOfR u = Arrow (tpOfR v) \<sigma> \<rbrakk> \<Longrightarrow> \<turnstile> App u v (Some \<sigma>)"
| wt_Lam: "\<lbrakk> \<turnstile> u; \<forall>\<tau>. (x, \<tau>) \<in> fvars u \<longrightarrow> \<tau> = \<sigma> \<rbrakk> \<Longrightarrow> \<turnstile> Lam x (Some \<sigma>) u (Some (Arrow \<sigma> (tpOfR u)))"

text \<open>Inversion rules for \<^const>\<open>wt\<close>.\<close>

lemma wt_Vr_inv: "\<turnstile> Vr x \<xi> \<Longrightarrow> \<exists>\<sigma>. \<xi> = Some \<sigma>"
  by (erule wt.cases) auto

lemma wt_Ct_inv: "\<turnstile> Ct c (Some \<sigma>) \<Longrightarrow> \<exists>\<rho>. \<sigma> = subst_ty \<rho> (ctpOf c)"
  by (erule wt.cases) auto

lemma wt_App_inv: "\<turnstile> App t1 t2 (Some \<sigma>) \<Longrightarrow> \<turnstile> t1 \<and> \<turnstile> t2 \<and> tpOfR t1 = Arrow (tpOfR t2) \<sigma>"
  by (erule wt.cases) auto

lemma wt_Lam_inv: "\<turnstile> Lam x (Some \<sigma>) t (Some \<tau>) \<Longrightarrow> \<turnstile> t \<and> \<tau> = Arrow \<sigma> (tpOfR t)"
  by (erule wt.cases) auto

lemma wt_App_invE:
  assumes "\<turnstile> App u1 u2 \<xi>"
  obtains \<sigma> where "\<turnstile> u1" "\<turnstile> u2" "\<xi> = Some \<sigma>" "tpOfR u1 = Arrow (tpOfR u2) \<sigma>"
  using assms by (auto elim: wt.cases)

lemma wt_Lam_invE:
  assumes "\<turnstile> Lam x \<xi> u \<zeta>"
  obtains \<sigma> where "\<turnstile> u" "\<xi> = Some \<sigma>" "\<zeta> = Some (Arrow \<sigma> (tpOfR u))"
    "\<forall>\<tau>. (x, \<tau>) \<in> fvars u \<longrightarrow> \<tau> = \<sigma>"
  using assms by (auto elim: wt.cases)

lemma wt_fterm: "\<turnstile> u \<Longrightarrow> fterm u"
  by (induction u rule: wt.induct) auto


text \<open>Substitution lemma for well-typedness.
  Since @{thm wt_Vr} has no conditions, any type substitution preserves \<^term>\<open>wt\<close>.\<close>
lemma subst_wt:
  assumes "\<turnstile> v"
  shows "\<turnstile> subst_trm \<rho> v"
  using assms
proof (induction v rule: wt.induct)
  case (wt_Vr x \<sigma>)
  show ?case by (simp, rule wt.wt_Vr)
next
  case (wt_Ct \<sigma> c)
  then obtain \<rho>0 where "\<sigma> = subst_ty \<rho>0 (ctpOf c)" by auto
  then have "subst_ty \<rho> \<sigma> = subst_ty (\<rho> \<circ>\<circ> \<rho>0) (ctpOf c)"
    by (simp add: subst_ty_comp)
  then show ?case by (simp, intro wt.wt_Ct, auto)
next
  case (wt_App u v \<sigma>)
  from wt_App have fu: "fterm u" "fterm v" by (auto dest: wt_fterm)
  then obtain \<tau>1 \<tau>2 where "mtp_of u [] = Some \<tau>1" "mtp_of v [] = Some \<tau>2"
    using fterm_mtp_of_Some by (metis nil_in_poss)
  with wt_App have tp: "tpOfR (subst_trm \<rho> u) = Arrow (tpOfR (subst_trm \<rho> v)) (subst_ty \<rho> \<sigma>)"
    by (simp add: mtp_of_subst[of "[]" u \<rho>, simplified] mtp_of_subst[of "[]" v \<rho>, simplified])
  from wt_App tp show ?case by (simp, intro wt.wt_App) auto
next
  case (wt_Lam u x \<sigma>)
  from wt_Lam have fu: "fterm u" by (auto dest: wt_fterm)
  then obtain \<tau> where mt: "mtp_of u [] = Some \<tau>"
    using fterm_mtp_of_Some by (metis nil_in_poss)
  from wt_Lam mt show ?case
  proof -
    have eq: "mtp_of (subst_trm \<rho> u) [] = Some (subst_ty \<rho> \<tau>)"
      using mt by (simp add: mtp_of_subst[of "[]" u \<rho>, simplified])
    have tpR: "tpOfR (subst_trm \<rho> u) = subst_ty \<rho> \<tau>" using eq by simp
    have tpU: "tpOfR u = \<tau>" using mt by simp
    have fv_cond: "\<forall>\<tau>'. (x, \<tau>') \<in> fvars (subst_trm \<rho> u) \<longrightarrow> \<tau>' = subst_ty \<rho> \<sigma>"
      using wt_Lam(2) by (auto simp: fvars_subst)
    from wt_Lam have "\<turnstile> Lam x (Some (subst_ty \<rho> \<sigma>)) (subst_trm \<rho> u)
      (Some (Arrow (subst_ty \<rho> \<sigma>) (tpOfR (subst_trm \<rho> u))))"
      by (intro wt.wt_Lam) (use fv_cond in auto)
    then show ?thesis using tpR tpU by simp
  qed
qed

text \<open>
  If \<^term>\<open>t\<close> is a typeable unambiguous C-term, then its well-typed completion
  is unique (there is exactly one F-term \<^term>\<open>u\<close> such that \<^term>\<open>t \<sqsubseteq> u\<close> and \<^term>\<open>wt u\<close>).
\<close>

lemma cterm_unique_completion:
  assumes "cterm t" "unambiguous t"
    "t \<sqsubseteq> u" "\<turnstile> u" "t \<sqsubseteq> v" "\<turnstile> v"
  shows "u = v"
  using assms
proof (induction t arbitrary: u v)
  case (Vr x \<xi>)
  then show ?case by (auto elim!: compl_Vr_leftE simp: mcompl_def)
next
  case (Ct c \<xi>)
  then show ?case by (auto elim!: compl_Ct_leftE simp: mcompl_def)
next
  case (App t1 t2 \<xi>)
  from App.prems have ct1: "cterm t1" "cterm t2" "\<xi> = None" by auto
  from App.prems have ua1: "unambiguous t1" "unambiguous t2" by auto
  from App.prems(3) obtain u1 u2 \<xi>u where ueq: "u = App u1 u2 \<xi>u"
    "t1 \<sqsubseteq> u1" "t2 \<sqsubseteq> u2" "\<xi> \<sqsubseteq>\<^sub>m \<xi>u"
    by (auto elim!: compl_App_leftE)
  from App.prems(5) obtain v1 v2 \<xi>v where veq: "v = App v1 v2 \<xi>v"
    "t1 \<sqsubseteq> v1" "t2 \<sqsubseteq> v2" "\<xi> \<sqsubseteq>\<^sub>m \<xi>v"
    by (auto elim!: compl_App_leftE)
  from App.prems(4) ueq(1) obtain \<sigma>u where
    wtu: "\<turnstile> u1" "\<turnstile> u2" and xiu: "\<xi>u = Some \<sigma>u" and
    tpu: "tpOfR u1 = Arrow (tpOfR u2) \<sigma>u"
    by (auto elim!: wt_App_invE)
  from App.prems(6) veq(1) obtain \<sigma>v where
    wtv: "\<turnstile> v1" "\<turnstile> v2" and xiv: "\<xi>v = Some \<sigma>v" and
    tpv: "tpOfR v1 = Arrow (tpOfR v2) \<sigma>v"
    by (auto elim!: wt_App_invE)
  have "u1 = v1" using App.IH(1)[OF ct1(1) ua1(1) ueq(2) wtu(1) veq(2) wtv(1)] .
  moreover have "u2 = v2" using App.IH(2)[OF ct1(2) ua1(2) ueq(3) wtu(2) veq(3) wtv(2)] .
  ultimately have "\<sigma>u = \<sigma>v" using tpu tpv by simp
  with ueq(1) veq(1) \<open>u1 = v1\<close> \<open>u2 = v2\<close> xiu xiv show "u = v" by simp
next
  case (Lam x \<xi> t \<zeta>)
  from Lam.prems have ct: "cterm t" "\<xi> \<noteq> None" "\<zeta> = None" by auto
  from Lam.prems have ua: "unambiguous t" by auto
  obtain \<sigma> where sig: "\<xi> = Some \<sigma>" using ct(2) by (cases \<xi>) auto
  from Lam.prems(3) sig obtain u' \<xi>u where ueq: "u = Lam x (Some \<sigma>) u' \<xi>u"
    "t \<sqsubseteq> u'"
    by (auto elim!: compl_Lam_leftE simp: mcompl_def)
  from Lam.prems(5) sig obtain v' \<xi>v where veq: "v = Lam x (Some \<sigma>) v' \<xi>v"
    "t \<sqsubseteq> v'"
    by (auto elim!: compl_Lam_leftE simp: mcompl_def)
  from Lam.prems(4) ueq(1) obtain \<tau>u where
    wtu: "\<turnstile> u'" and xiusig: "Some \<sigma> = Some \<sigma>" and xiu: "\<xi>u = Some (Arrow \<sigma> (tpOfR u'))"
    by (auto elim!: wt_Lam_invE)
  from Lam.prems(6) veq(1) obtain \<tau>v where
    wtv: "\<turnstile> v'" and xivsig: "Some \<sigma> = Some \<sigma>" and xiv: "\<xi>v = Some (Arrow \<sigma> (tpOfR v'))"
    by (auto elim!: wt_Lam_invE)
  have "u' = v'" using Lam.IH[OF ct(1) ua ueq(2) wtu veq(2) wtv] .
  with ueq veq xiu xiv show "u = v" by simp
qed

subsubsection \<open>Well-Typed Completions\<close>
definition is_wt_completion :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "is_wt_completion t u \<longleftrightarrow> t \<sqsubseteq> u \<and> fterm u \<and> \<turnstile> u"

definition is_mgen :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "is_mgen t v \<longleftrightarrow> is_wt_completion t v \<and>
    (\<forall>u. is_wt_completion t u \<longrightarrow> (\<exists>\<rho>. u = subst_trm \<rho> v))"

definition typeable :: "('tv,'k,'v,'c) trm \<Rightarrow> bool" where
  "typeable t \<longleftrightarrow> (\<exists>u. is_wt_completion t u)"

end

text \<open>
  We work in an extended locale that assumes the existence of \<^term>\<open>is_mgen\<close>: 
  For any typeable unambiguous term, there exists a most general well-typed completion.
\<close>

locale signature_with_mgen = signature ctpOf
  for ctpOf :: "'c \<Rightarrow> ('tv,'k) ty" +
  assumes mgen_exists:
    "\<lbrakk> typeable (t::('tv,'k,'v,'c) trm); unambiguous t \<rbrakk> \<Longrightarrow> \<exists>v. is_mgen t v" and
    tyvars_inf: "infinite (UNIV :: 'tv set)"
begin

definition mgen :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm" where
  "mgen t = (SOME v. is_mgen t v)"

lemma mgen_is_mgen:
  assumes "typeable t" "unambiguous t"
  shows "is_mgen t (mgen t)"
proof -
  from assms have "\<exists>v. is_mgen t v"
    by (intro mgen_exists)
  then show ?thesis unfolding mgen_def by (rule someI_ex)
qed

lemma mgen_compl:
  assumes "typeable t" "unambiguous t"
  shows "t \<sqsubseteq> mgen t"
  using mgen_is_mgen[OF assms] by (auto simp: is_mgen_def is_wt_completion_def)

lemma mgen_fterm:
  assumes "typeable t" "unambiguous t"
  shows "fterm (mgen t)"
  using mgen_is_mgen[OF assms] by (auto simp: is_mgen_def is_wt_completion_def)

lemma mgen_wt:
  assumes "typeable t" "unambiguous t"
  shows "\<turnstile> mgen t"
  using mgen_is_mgen[OF assms] by (auto simp: is_mgen_def is_wt_completion_def)

lemma mgen_most_general:
  assumes "typeable t" "unambiguous t" "is_wt_completion t u"
  shows "\<exists>\<rho>. u = subst_trm \<rho> (mgen t)"
  using mgen_is_mgen[OF assms(1,2)] assms(3) by (auto simp: is_mgen_def)

subsection \<open>Correct Printings\<close>

text \<open>A correct printing of a typable unambiguous C-term \<^term>\<open>t\<close> is a term \<^term>\<open>s\<close> such that 
  \<^term>\<open>mgen t\<close> is the unique most general well-typed completion of \<^term>\<open>s\<close>:\<close>
definition \<open>correct_printing t s \<longleftrightarrow> (\<forall>t'. is_mgen s t' \<longleftrightarrow> t' = mgen t)\<close>

definition \<open>strong_correct_printing t s \<longleftrightarrow> (\<forall>t'. is_wt_completion s t' \<longleftrightarrow> t' = mgen t)\<close>


text \<open>Extra tyvars yield distinct most general completions.\<close>
lemma two_mgen:
  assumes ua: "unambiguous s" and mg: "is_mgen s v" and extra: "tvars_trm v - tvars_trm s \<noteq> {}"
  shows "\<exists>v'. v' \<noteq> v \<and> is_mgen s v'"
proof -
  from mg have sv: "s \<sqsubseteq> v" and fv: "fterm v" and wtv: "\<turnstile> v"
    and mg_prop: "\<And>u. is_wt_completion s u \<Longrightarrow> \<exists>\<rho>. u = subst_trm \<rho> v"
    by (auto simp: is_mgen_def is_wt_completion_def)
  from extra obtain \<alpha> where alpha_v: "\<alpha> \<in> tvars_trm v" and alpha_ns: "\<alpha> \<notin> tvars_trm s" by auto
  text \<open>Property (a): \<^term>\<open>\<alpha>\<close> only appears at \<^term>\<open>None\<close> positions of \<^term>\<open>s\<close>.\<close>
  have prop_a: "mtp_of s p = None" if "p \<in> poss v" "\<alpha> \<in> tvars_mty (mtp_of v p)" for p
  proof (rule ccontr)
    assume "mtp_of s p \<noteq> None"
    have "p \<in> poss s" using that(1) compl_poss_eq[OF sv] by simp
    have "mtp_of s p \<sqsubseteq>\<^sub>m mtp_of v p" using compl_mtp_of[OF sv] .
    then have "mtp_of s p = mtp_of v p" using \<open>mtp_of s p \<noteq> None\<close> by (auto simp: mcompl_def)
    then have "\<alpha> \<in> tvars_mty (mtp_of s p)" using that(2) by simp
    then have "\<alpha> \<in> tvars_trm s" using tvars_trm_eq_UN_mtp \<open>p \<in> poss s\<close> by fastforce
    with alpha_ns show False by contradiction
  qed
  obtain \<beta> where beta_nv: "\<beta> \<notin> tvars_trm v"
    using ex_new_if_finite[OF tyvars_inf tvars_trm_finite[of v]] by blast
  define v' where "v' = subst_trm (single_subst (TyVar \<beta>) \<alpha>) v"
  text \<open>v != v'.\<close>
  have v_neq: "v \<noteq> v'"
  proof
    assume "v = v'"
    then have "subst_trm (single_subst (TyVar \<beta>) \<alpha>) v = v" by (simp add: v'_def)
    then have "single_subst (TyVar \<beta>) \<alpha> \<alpha> = TyVar \<alpha>"
      using subst_trm_id_on_tvars[of "single_subst (TyVar \<beta>) \<alpha>" v \<alpha>] alpha_v by simp
    then show False using beta_nv alpha_v by simp
  qed
  have wtv': "\<turnstile> v'" unfolding v'_def using subst_wt[OF wtv] .
  have fv': "fterm v'" unfolding v'_def using fv by (induction v) auto
  text \<open>\<^term>\<open>s \<sqsubseteq> v'\<close> using @{thm multiple_compl}.\<close>
  have sv': "s \<sqsubseteq> v'"
  proof -
    have "s \<sqsubseteq> subst_trm TyVar v" using sv by simp
    then show "s \<sqsubseteq> v'" unfolding v'_def
    proof (rule multiple_compl)
      fix \<alpha>' p assume "p \<in> poss v" "\<alpha>' \<in> tvars_mty (mtp_of v p)" "mtp_of s p \<noteq> None"
      then have "\<alpha> \<notin> tvars_mty (mtp_of v p)" using prop_a by auto
      then have "\<alpha>' \<noteq> \<alpha>" using \<open>\<alpha>' \<in> tvars_mty (mtp_of v p)\<close> by auto
      then show "TyVar \<alpha>' = single_subst (TyVar \<beta>) \<alpha> \<alpha>'" by (simp add: single_subst_def)
    qed
  qed
  text \<open>\<^term>\<open>v'\<close> is most general.\<close>
  have "\<And>u. is_wt_completion s u \<Longrightarrow> \<exists>\<rho>. u = subst_trm \<rho> v'"
  proof -
    fix u assume "is_wt_completion s u"
    then obtain \<rho> where "u = subst_trm \<rho> v" using mg_prop by auto
    have "v = subst_trm (single_subst (TyVar \<alpha>) \<beta>) v'"
      unfolding v'_def using subst_trm_swap[OF beta_nv] by simp
    then have "u = subst_trm (\<rho> \<circ>\<circ> single_subst (TyVar \<alpha>) \<beta>) v'"
      using \<open>u = subst_trm \<rho> v\<close> subst_trm_comp by metis
    then show "\<exists>\<rho>. u = subst_trm \<rho> v'" by blast
  qed
  then have "is_mgen s v'"
    using sv' fv' wtv' by (auto simp: is_mgen_def is_wt_completion_def)
  with v_neq show ?thesis by auto
qed

text \<open>Lift distinct completions to distinct most general completions.\<close>
lemma lift_to_most_general:
  fixes s :: \<open>('tv,'k,'v,'c) trm\<close>
  assumes "unambiguous s" "is_wt_completion s u" "is_wt_completion s u'" "u \<noteq> u'"
  obtains v v' where \<open>v \<noteq> v'\<close> \<open>is_mgen s v\<close> \<open>is_mgen s v'\<close>
proof -
  have ty_s: "typeable s" using assms(2) by (auto simp: typeable_def)
  have mg: "is_mgen s (mgen s)" using mgen_is_mgen[OF ty_s assms(1)] .
  obtain \<rho> where u_eq: "u = subst_trm \<rho> (mgen s)"
    using mgen_most_general[OF ty_s assms(1,2)] by auto
  obtain \<rho>' where u'_eq: "u' = subst_trm \<rho>' (mgen s)"
    using mgen_most_general[OF ty_s assms(1,3)] by auto
  from assms(4) u_eq u'_eq have "\<exists>\<alpha> \<in> tvars_trm (mgen s). \<rho> \<alpha> \<noteq> \<rho>' \<alpha>"
    by (auto simp: subst_trm_agree)
  then obtain \<alpha> where alpha_v: "\<alpha> \<in> tvars_trm (mgen s)" and rho_neq: "\<rho> \<alpha> \<noteq> \<rho>' \<alpha>" by auto
  have sv: "s \<sqsubseteq> mgen s" using mgen_compl[OF ty_s assms(1)] .
  have "\<alpha> \<notin> tvars_trm s"
  proof
    assume "\<alpha> \<in> tvars_trm s"
    then obtain p where ps: "p \<in> poss s" and alpha_s: "\<alpha> \<in> tvars_mty (mtp_of s p)"
      using tvars_trm_eq_UN_mtp by fastforce
    then have snone: "mtp_of s p \<noteq> None" by (cases "mtp_of s p") auto
    have pv: "p \<in> poss (mgen s)" using ps compl_poss_eq[OF sv] by simp
    have "mtp_of s p = mtp_of (mgen s) p"
      using compl_mtp_of[OF sv, of p] snone by (auto simp: mcompl_def)
    then have alpha_vp: "\<alpha> \<in> tvars_mty (mtp_of (mgen s) p)" using alpha_s by simp
    have u_at: "mtp_of u p = subst_mty \<rho> (mtp_of (mgen s) p)"
      using mtp_of_subst[OF pv] u_eq by auto
    have u'_at: "mtp_of u' p = subst_mty \<rho>' (mtp_of (mgen s) p)"
      using mtp_of_subst[OF pv] u'_eq by auto
    have "s \<sqsubseteq> u" using assms(2) by (auto simp: is_wt_completion_def)
    then have "mtp_of u p = mtp_of s p"
      using compl_mtp_of[of _ _ p] snone by (fastforce simp: mcompl_def)
    moreover have "s \<sqsubseteq> u'" using assms(3) by (auto simp: is_wt_completion_def)
    then have "mtp_of u' p = mtp_of s p"
      using compl_mtp_of[of _ _ p] snone by (fastforce simp: mcompl_def)
    ultimately have "subst_mty \<rho> (mtp_of (mgen s) p) = subst_mty \<rho>' (mtp_of (mgen s) p)"
      using u_at u'_at by simp
    then have "\<rho> \<alpha> = \<rho>' \<alpha>" using alpha_vp
      by (cases "mtp_of (mgen s) p") (auto simp: subst_ty_agree)
    with rho_neq show False by contradiction
  qed
  with alpha_v have "tvars_trm (mgen s) - tvars_trm s \<noteq> {}" by auto
  from two_mgen[OF assms(1) mg this]
  obtain v' where "v' \<noteq> mgen s" "is_mgen s v'" by auto
  with mg that show ?thesis
    by auto
qed

corollary strong_correct_printing_iff:
  assumes \<open>unambiguous s\<close>
  shows \<open>strong_correct_printing t s \<longleftrightarrow> correct_printing t s\<close>
  using assms
  unfolding strong_correct_printing_def correct_printing_def
  using is_mgen_def typeable_def mgen_is_mgen[of s] lift_to_most_general[of s \<open>mgen t\<close>]
  by metis

subsection \<open>The Algorithm\<close>

text \<open>
  The \<^term>\<open>test\<close> predicate, \<^term>\<open>decrease\<close> function, and the algorithm \<^term>\<open>smobla\<close>.
  We work in a locale that also fixes a position-picking function \<^term>\<open>pickPos\<close>.
\<close>

definition non_bot_poss :: "('tv,'k,'v,'c) trm \<Rightarrow> nat list set" where
  "non_bot_poss s = {p \<in> poss s. mtp_of s p \<noteq> None}"

definition test :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> nat list \<Rightarrow> bool" where
  "test v s p \<longleftrightarrow>
    p \<in> poss s \<inter> poss v \<and> mtp_of s p \<noteq> None \<and>
    (\<forall>\<alpha> \<in> tvars_mty (mtp_of v p).
      \<exists>q \<in> poss s - {p}. \<alpha> \<in> tvars_mty (mtp_of v q) \<and> mtp_of s q \<noteq> None)"

end

locale algorithm = signature_with_mgen ctpOf
  for ctpOf :: "'c \<Rightarrow> ('tv,'k) ty" +
  fixes pickPos :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> nat list"
  assumes compat: "test v s p \<Longrightarrow> test v s (pickPos v s)"
begin

function decrease :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm" where
  "decrease v s = (if \<exists>p. test v s p
    then decrease v (remove_annot s (pickPos v s))
    else s)"
  by auto

termination
proof (relation "measure (\<lambda>(v, s). card (non_bot_poss s))")
  show "wf (measure (\<lambda>(v, s). card (non_bot_poss s)))" by simp
next
  fix v s :: "('tv,'k,'v,'c) trm"
  assume "\<exists>p. test v s p"
  then obtain p0 where t0: "test v s p0" by auto
  then have t: "test v s (pickPos v s)" using compat by auto
  then have pp: "pickPos v s \<in> poss s" and nb: "mtp_of s (pickPos v s) \<noteq> None"
    by (auto simp: test_def)
  have rm: "mtp_of (remove_annot s (pickPos v s)) (pickPos v s) = None"
    using mtp_of_remove_self pp by auto
  have ps: "poss (remove_annot s (pickPos v s)) = poss s"
    using remove_annot_poss pp by auto
  have sub: "non_bot_poss (remove_annot s (pickPos v s)) \<subset> non_bot_poss s"
  proof (intro psubsetI subsetI)
    fix q assume q_in: "q \<in> non_bot_poss (remove_annot s (pickPos v s))"
    then have qp: "q \<in> poss s" and qnb: "mtp_of (remove_annot s (pickPos v s)) q \<noteq> None"
      by (auto simp: non_bot_poss_def ps)
    have "q \<noteq> pickPos v s" using qnb rm by auto
    then have "mtp_of s q \<noteq> None" using mtp_of_remove_other[OF pp _ \<open>q \<noteq> pickPos v s\<close>] qp qnb
      by (auto simp: compl_poss_eq)
    then show "q \<in> non_bot_poss s" using qp by (auto simp: non_bot_poss_def)
  next
    show "non_bot_poss (remove_annot s (pickPos v s)) \<noteq> non_bot_poss s"
    proof
      assume eq: "non_bot_poss (remove_annot s (pickPos v s)) = non_bot_poss s"
      have "pickPos v s \<in> non_bot_poss s" using pp nb by (auto simp: non_bot_poss_def)
      then have "pickPos v s \<in> non_bot_poss (remove_annot s (pickPos v s))" using eq by simp
      then show False using rm by (auto simp: non_bot_poss_def)
    qed
  qed
  then show "((v, remove_annot s (pickPos v s)), v, s)
    \<in> measure (\<lambda>(v, s). card (non_bot_poss s))"
    using psubset_card_mono[OF finite_subset[OF _ poss_finite[of s]]] 
      by (auto simp: non_bot_poss_def)
qed

lemmas decrease.simps[simp del]

definition smobla :: "('tv,'k,'v,'c) trm \<Rightarrow> ('tv,'k,'v,'c) trm" where
  "smobla t = decrease (mgen (erase t)) (mgen t)"

subsection \<open>Completeness\<close>

text \<open>Auxiliary: decrease only removes annotations, so \<^term>\<open>decrease v s \<sqsubseteq> s\<close>.\<close>
lemma decrease_compl:
  "decrease v s \<sqsubseteq> s"
proof (induction v s rule: decrease.induct)
  case (1 v s)
  show ?case
    using compat compl_trans[OF 1 remove_annot_compl]
    by (force simp: test_def decrease.simps[of v s])
qed

text \<open>Auxiliary: \<^term>\<open>erase t \<sqsubseteq> decrease v s\<close> if \<^term>\<open>erase t \<sqsubseteq> s\<close>.\<close>
lemma erase_compl_decrease:
  "erase t \<sqsubseteq> s \<Longrightarrow> erase t \<sqsubseteq> decrease v s"
proof (induction v s rule: decrease.induct)
  case (1 v s)
  show ?case
    using compat erase_compl_remove_annot[OF  1(2)]
    by (auto simp: test_def decrease.simps[of v s] intro: 1)
qed

text \<open>The decrease invariant: coverage is preserved by \<^term>\<open>decrease\<close>.\<close>
lemma decrease_coverage:
  assumes "fterm v" "s \<sqsubseteq> subst_trm \<rho> v"
    "\<forall>\<alpha> \<in> tvars_trm v. \<exists>p \<in> poss v. \<alpha> \<in> tvars_mty (mtp_of v p) \<and> mtp_of s p \<noteq> None"
  shows "\<forall>\<alpha> \<in> tvars_trm v. \<exists>p \<in> poss v. \<alpha> \<in> tvars_mty (mtp_of v p) \<and>
    mtp_of (decrease v s) p \<noteq> None"
  using assms(2,3)
proof (induction v s rule: decrease.induct)
  case (1 v s)
  show ?case
  proof (cases "\<exists>p. test v s p")
    case False
    then have "decrease v s = s" by (metis decrease.simps)
    with 1(3) show ?thesis by simp
  next
    case True
    then have t: "test v s (pickPos v s)" using compat by auto
    then have pp: "pickPos v s \<in> poss v" by (auto simp: test_def)
    have rm_compl: "remove_annot s (pickPos v s) \<sqsubseteq> subst_trm \<rho> v"
      using compl_trans[OF remove_annot_compl 1(2)] t by (auto simp: test_def)
    have rm_cov: "\<forall>\<alpha> \<in> tvars_trm v. \<exists>p \<in> poss v. \<alpha> \<in> tvars_mty (mtp_of v p) \<and>
      mtp_of (remove_annot s (pickPos v s)) p \<noteq> None"
    proof (intro ballI)
      fix \<alpha> assume "\<alpha> \<in> tvars_trm v"
      with 1(3) obtain q where qv: "q \<in> poss v" "\<alpha> \<in> tvars_mty (mtp_of v q)"
        "mtp_of s q \<noteq> None" by auto
      have ps_eq: "poss s = poss v"
        using compl_poss_eq[OF 1(2)] by simp
      show "\<exists>p \<in> poss v. \<alpha> \<in> tvars_mty (mtp_of v p) \<and>
        mtp_of (remove_annot s (pickPos v s)) p \<noteq> None"
      proof (cases "q = pickPos v s")
        case False
        then have "mtp_of (remove_annot s (pickPos v s)) q = mtp_of s q"
          using mtp_of_remove_other t qv(1) ps_eq by (auto simp: test_def)
        with qv show ?thesis by auto
      next
        case True
        text \<open>\<^term>\<open>q = pickPos v s\<close>, so \<^term>\<open>mtp_of s q\<close> is removed. But by the test condition,
          \<^term>\<open>\<alpha>\<close> is covered by some other position.\<close>
        from t True have "\<exists>q' \<in> poss s - {q}. \<alpha> \<in> tvars_mty (mtp_of v q') \<and> mtp_of s q' \<noteq> None"
          using qv(2) by (auto simp: test_def)
        then obtain q' where q'v: "q' \<in> poss v" "q' \<noteq> pickPos v s"
          "\<alpha> \<in> tvars_mty (mtp_of v q')" "mtp_of s q' \<noteq> None"
          using ps_eq True by auto
        have "mtp_of (remove_annot s (pickPos v s)) q' = mtp_of s q'"
          using mtp_of_remove_other t q'v(1,2) ps_eq by (auto simp: test_def)
        with q'v show ?thesis by auto
      qed
    qed
    from 1(1)[OF True rm_compl rm_cov] True
    show ?thesis by (metis decrease.simps)
  qed
qed

theorem completeness:
  assumes ty: "typeable t" and ua: "unambiguous t" and ct: "cterm t"
  shows \<open>correct_printing t (smobla t)\<close>
proof -
  let ?v = "mgen (erase t)"
  let ?s = "smobla t"
  text \<open>Basic setup: \<^term>\<open>erase t\<close> is typeable and unambiguous.\<close>
  have er_ty: "typeable (erase t)"
    using ty by (auto simp: typeable_def is_wt_completion_def
      intro: compl_trans[OF erase_compl])
  have er_ua: "unambiguous (erase t)" using ua by simp
  have t_ty_ua: "typeable t" "unambiguous t" using ty ua by auto
  text \<open>Part 1: \<^term>\<open>erase t \<sqsubseteq> ?s\<close> and \<^term>\<open>?s \<sqsubseteq> mgen t\<close>.\<close>
  have s_def: "?s = decrease ?v (mgen t)" by (simp add: smobla_def)
  have compl1: "erase t \<sqsubseteq> mgen t" using erase_compl mgen_compl[OF ty ua] compl_trans by blast
  have s_compl_mgen: "?s \<sqsubseteq> mgen t" using decrease_compl s_def by simp
  have er_compl_s: "erase t \<sqsubseteq> ?s" using erase_compl_decrease[OF compl1] s_def by simp
  text \<open>\<^term>\<open>mgen t\<close> is a well-typed F-term completion of \<^term>\<open>?s\<close>.\<close>
  have wt_completion: "is_wt_completion ?s (mgen t)"
    unfolding is_wt_completion_def using s_compl_mgen mgen_fterm[OF ty ua] mgen_wt[OF ty ua] by auto
  text \<open>Part 2: uniqueness. Any well-typed completion of \<^term>\<open>?s\<close> must equal \<^term>\<open>mgen t\<close>.\<close>
  have unique: "u = mgen t" if u_wc: \<open>is_wt_completion ?s u\<close> for u
  proof -
    from u_wc have su: "?s \<sqsubseteq> u" and fu: "fterm u" and wtu: "\<turnstile> u"
      by (auto simp: is_wt_completion_def)
    text \<open>\<^term>\<open>u\<close> is a completion of \<^term>\<open>erase t\<close>, hence \<^term>\<open>u\<close> is an instance of \<^term>\<open>?v\<close>.\<close>
    have er_u: "erase t \<sqsubseteq> u" using compl_trans[OF er_compl_s su] .
    have "is_wt_completion (erase t) u"
      unfolding is_wt_completion_def using er_u fu wtu by auto
    then obtain \<rho>' where u_inst: "u = subst_trm \<rho>' ?v"
      using mgen_most_general[OF er_ty er_ua] by auto
    text \<open>Similarly, \<^term>\<open>mgen t\<close> is a completion of \<^term>\<open>erase t\<close>, hence \<^term>\<open>mgen t\<close> is an 
      instance of \<^term>\<open>?v\<close>.\<close>
    have "is_wt_completion (erase t) (mgen t)"
      unfolding is_wt_completion_def using compl1 mgen_fterm[OF ty ua] mgen_wt[OF ty ua] by auto
    then obtain \<rho> where mgen_inst: "mgen t = subst_trm \<rho> ?v"
      using mgen_most_general[OF er_ty er_ua] by auto
    text \<open>The coverage condition: every tyvar of \<^term>\<open>?v\<close> is witnessed 
      at a non-bot position of \<^term>\<open>?s\<close>.\<close>
    have fv: "fterm ?v" using mgen_fterm[OF er_ty er_ua] .
    have cov: "\<forall>\<alpha> \<in> tvars_trm ?v. \<exists>p \<in> poss ?v. \<alpha> \<in> tvars_mty (mtp_of ?v p) \<and>
      mtp_of (mgen t) p \<noteq> None"
    proof (intro ballI)
      fix \<alpha> assume "\<alpha> \<in> tvars_trm ?v"
      then obtain p where "p \<in> poss ?v" "\<alpha> \<in> tvars_mty (mtp_of ?v p)"
      using tvars_trm_eq_UN_mtp by fastforce
      moreover have "mtp_of (mgen t) p \<noteq> None"
      proof -
        have "p \<in> poss (mgen t)" using \<open>p \<in> poss ?v\<close> compl_poss_eq[OF compl1]
          compl_poss_eq[OF mgen_compl[OF er_ty er_ua]] by simp
        then show ?thesis using fterm_mtp_of_Some[OF mgen_fterm[OF ty ua]] by fastforce
      qed
      ultimately show "\<exists>p \<in> poss ?v. \<alpha> \<in> tvars_mty (mtp_of ?v p) \<and> mtp_of (mgen t) p \<noteq> None"
        by auto
    qed
    have s_compl_subst: "?s \<sqsubseteq> subst_trm \<rho> ?v" using s_compl_mgen mgen_inst by simp
    have cov_mgen: "\<forall>\<alpha> \<in> tvars_trm ?v. \<exists>p \<in> poss ?v. \<alpha> \<in> tvars_mty (mtp_of ?v p) \<and>
      mtp_of (mgen t) p \<noteq> None" using cov .
    have cov_s: "\<forall>\<alpha> \<in> tvars_trm ?v. \<exists>p \<in> poss ?v. \<alpha> \<in> tvars_mty (mtp_of ?v p) \<and>
      mtp_of ?s p \<noteq> None"
    proof (intro ballI)
      fix \<alpha> assume "\<alpha> \<in> tvars_trm ?v"
      have dec_cov: "\<forall>\<alpha> \<in> tvars_trm ?v. \<exists>p \<in> poss ?v. \<alpha> \<in> tvars_mty (mtp_of ?v p) \<and>
        mtp_of (decrease ?v (mgen t)) p \<noteq> None"
      proof -
        have "mgen t \<sqsubseteq> subst_trm \<rho> ?v" using mgen_inst by simp
        then show ?thesis using decrease_coverage[OF fv] cov_mgen by blast
      qed
      with \<open>\<alpha> \<in> tvars_trm ?v\<close> obtain p where "p \<in> poss ?v"
        "\<alpha> \<in> tvars_mty (mtp_of ?v p)" "mtp_of (decrease ?v (mgen t)) p \<noteq> None"
        by auto
      then show "\<exists>p \<in> poss ?v. \<alpha> \<in> tvars_mty (mtp_of ?v p) \<and> mtp_of ?s p \<noteq> None"
        unfolding s_def by blast
    qed
    text \<open>Apply @{thm crucial_uniqueness}.\<close>
    have "\<exists>\<rho>. mgen t = subst_trm \<rho> ?v" using mgen_inst by auto
    moreover have "\<exists>\<rho>'. u = subst_trm \<rho>' ?v" using u_inst by auto
    show "u = mgen t"
    proof -
      have "mgen t = u"
        by (rule crucial_uniqueness[OF s_compl_mgen mgen_fterm[OF ty ua]
          \<open>\<exists>\<rho>. mgen t = subst_trm \<rho> ?v\<close> fv cov_s su fu \<open>\<exists>\<rho>'. u = subst_trm \<rho>' ?v\<close>])
      then show ?thesis by simp
    qed
  qed

  show ?thesis
    using assms wt_completion unique mgen_is_mgen
    unfolding correct_printing_def is_mgen_def
    by fastforce+
qed

subsection \<open>Minimality\<close>

text \<open>Supporting lemmas for minimality.\<close>

text \<open>After decrease, no position passes the test.\<close>
lemma decrease_no_test:
  "\<not>test v (decrease v s) p"
proof (induction v s rule: decrease.induct)
  case (1 v s)
  show ?case
  proof (cases "\<exists>p. test v s p")
    case False
    then show ?thesis by (metis decrease.simps)
  next
    case True
    then have "decrease v s = decrease v (remove_annot s (pickPos v s))"
      by (metis decrease.simps)
    with 1 True show ?thesis by simp
  qed
qed

text \<open>Decrease preserves unambiguity.\<close>
lemma decrease_unambiguous:
  "unambiguous s \<Longrightarrow> unambiguous (decrease v s)"
proof (induction v s rule: decrease.induct)
  case (1 v s)
  show ?case
  proof (cases "\<exists>p. test v s p")
    case False
    then show ?thesis using 1(2) by (metis decrease.simps)
  next
    case True
    then have pp: "pickPos v s \<in> poss s" using compat by (auto simp: test_def)
    have "unambiguous (remove_annot s (pickPos v s))"
      using remove_annot_unambiguous[OF pp] 1(2) by auto
    then have "unambiguous (decrease v (remove_annot s (pickPos v s)))"
      using 1(1)[OF True] by auto
    with True show ?thesis by (metis decrease.simps)
  qed
qed

text \<open>Coverage minimality.\<close>
theorem smobla_distinct_completions:
  assumes ty: "typeable t" and ua: "unambiguous t" and ct: "cterm t"
    and ua': "unambiguous s'" and s'_compl: "s' \<sqsubseteq> smobla t" and s'_neq: "s' \<noteq> smobla t"
  obtains v v' where "v \<noteq> v'" "is_mgen s' v" "is_mgen s' v'"
proof -
  let ?s = "smobla t"
  let ?v = "mgen (erase t)"
  have s_ua: "unambiguous ?s"
    using decrease_unambiguous compl_unambiguous[OF mgen_compl[OF ty ua]] ua
    unfolding smobla_def by metis
  text \<open>Get a position where \<^term>\<open>s'\<close> has \<^term>\<open>None\<close> but \<^term>\<open>?s\<close> has non-\<^term>\<open>None\<close>.\<close>
  from compl_strict_witness[OF s'_compl s'_neq]
  obtain p where ps: "p \<in> poss ?s" and s'_none: "mtp_of s' p = None" and s_some: "mtp_of ?s p \<noteq> None"
    by auto
  text \<open>Since not \<^term>\<open>test ?v ?s p\<close>, there exists a tyvar uncovered by \<^term>\<open>?s\<close>.\<close>
  have no_test: "\<not> test ?v ?s p" using decrease_no_test unfolding smobla_def by blast
  text \<open>From completeness, \<^term>\<open>mgen t\<close> is the unique well-typed completion of \<^term>\<open>?s\<close>.
    \<^term>\<open>s' \<sqsubseteq> ?s\<close> and \<^term>\<open>?s \<sqsubseteq> mgen t\<close>, so \<^term>\<open>mgen t\<close> is a completion of \<^term>\<open>s'\<close>.
    Any other completion of \<^term>\<open>s'\<close> gives two distinct completions.\<close>

  have s_compl_mgen: "?s \<sqsubseteq> mgen t"
    using decrease_compl smobla_def by metis
  have s'_compl_mgen: "is_wt_completion s' (mgen t)"
    using compl_trans[OF s'_compl s_compl_mgen] mgen_fterm[OF ty ua] mgen_wt[OF ty ua]
    by (auto simp: is_wt_completion_def)
  text \<open>Construct a second distinct completion using the uncovered tyvar.\<close>
  have er_ty: "typeable (erase t)"
    using ty by (auto simp: typeable_def is_wt_completion_def intro: compl_trans[OF erase_compl])
  have er_ua: "unambiguous (erase t)" using ua by simp
  obtain \<rho> where mgen_inst: "mgen t = subst_trm \<rho> ?v"
    using mgen_most_general[OF er_ty er_ua]
      compl_trans[OF erase_compl mgen_compl[OF ty ua]] mgen_fterm[OF ty ua] mgen_wt[OF ty ua]
    by (auto simp: is_wt_completion_def)
  have fv: "fterm ?v" using mgen_fterm[OF er_ty er_ua] .
  have wtv: "\<turnstile> ?v" using mgen_wt[OF er_ty er_ua] .
  have poss_sv: "poss ?s = poss ?v"
    using compl_poss_eq[OF s_compl_mgen] mgen_inst by simp
  have pv: "p \<in> poss ?v" using ps poss_sv by simp
  text \<open>Extract tyvar from the negated test.\<close>
  from no_test ps pv s_some obtain \<alpha> where alpha_vp: "\<alpha> \<in> tvars_mty (mtp_of ?v p)"
    and uncov: "\<forall>q \<in> poss ?s - {p}. \<alpha> \<in> tvars_mty (mtp_of ?v q) \<longrightarrow> mtp_of ?s q = None"
    unfolding test_def by blast
  text \<open>Property (c): \<^term>\<open>\<alpha>\<close> is uncovered in \<^term>\<open>s'\<close>.\<close>
  have poss_s': "poss s' = poss ?s" using compl_poss_eq[OF s'_compl] .
  have prop_c: \<open>mtp_of s' q = None\<close> if \<open>q \<in> poss s'\<close> and \<open>\<alpha> \<in> tvars_mty (mtp_of ?v q)\<close> for q
    using compl_mtp_of[OF s'_compl, of q] that uncov
    by (auto simp: mcompl_def s'_none poss_s')
  have s'_compl_vrho: "s' \<sqsubseteq> subst_trm \<rho> ?v"
    using compl_trans[OF s'_compl s_compl_mgen] mgen_inst by simp
  text \<open>Construct type differing from \<^term>\<open>\<rho>\<close> at \<^term>\<open>\<alpha>\<close>.
    Simplest: \<^term>\<open>TyVar\<close> with a fresh variable, always well-typed.\<close>
  obtain w :: "('tv,'k) ty" where w_neq: "w \<noteq> \<rho> \<alpha>"
    using ty.distinct(1) by metis
  define \<rho>' where "\<rho>' = (\<lambda>\<beta>. if \<beta> = \<alpha> then w else \<rho> \<beta>)"
  text \<open>(2) \<^term>\<open>\<rho>\<close> and \<^term>\<open>\<rho>'\<close> agree on non-\<^term>\<open>None\<close> positions of \<^term>\<open>s'\<close>.\<close>
  have agree: "\<rho> \<beta> = \<rho>' \<beta>" if "q \<in> poss ?v" "\<beta> \<in> tvars_mty (mtp_of ?v q)" "mtp_of s' q \<noteq> None" 
      for \<beta> q using that \<rho>'_def poss_s' poss_sv prop_c by auto
  have s'_compl_vrho': "s' \<sqsubseteq> subst_trm \<rho>' ?v"
    using multiple_compl[OF s'_compl_vrho agree] .
  have wtvrho': "\<turnstile> subst_trm \<rho>' ?v" using subst_wt[OF wtv] .
  have "\<alpha> \<in> tvars_trm ?v" using alpha_vp tvars_trm_eq_UN_mtp pv by fastforce
  then have vrho_neq: "subst_trm \<rho> ?v \<noteq> subst_trm \<rho>' ?v"
    using w_neq by (auto simp: subst_trm_agree \<rho>'_def)
  text \<open>Two distinct completions of \<^term>\<open>s'\<close>.\<close>
  have wc1: "is_wt_completion s' (subst_trm \<rho> ?v)"
    using s'_compl_vrho fv subst_wt[OF wtv] by (auto simp: is_wt_completion_def)
  have wc2: "is_wt_completion s' (subst_trm \<rho>' ?v)"
    using s'_compl_vrho' fv wtvrho' by (auto simp: is_wt_completion_def)
  from lift_to_most_general[OF ua' wc1 wc2 vrho_neq] show ?thesis using that by metis
qed

corollary minimality:
  assumes "typeable t" "unambiguous t" "cterm t" \<open>s \<sqsubseteq> smobla t\<close> \<open>correct_printing t s\<close>
  shows \<open>s = smobla t\<close>
  using assms smobla_distinct_completions
  unfolding correct_printing_def
  by (metis mgen_compl decrease_unambiguous compl_unambiguous smobla_def)

end

end
