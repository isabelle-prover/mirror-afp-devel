(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Idiomatic terms -- Properties and operations\<close>

theory Idiomatic_Terms
imports Beta_Eta
begin

text \<open>
  This theory proves the correctness of the normalisation algorithm for
  arbitrary applicative functors.
\<close>

subsubsection \<open>Extensions to lambda terms\<close>

abbreviation "\<I> \<equiv> Abs (Var 0)"
abbreviation "\<B> \<equiv> Abs (Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0))))"
abbreviation "\<T> \<equiv> Abs (Abs (Var 0 \<degree> Var 1))" -- \<open>reverse application\<close>

lemma I_eval: "\<I> \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* x"
proof -
  have "\<I> \<degree> x \<rightarrow>\<^sub>\<beta> x" by (metis beta.beta subst_eq)
  thus ?thesis by simp
qed

lemmas I_equiv = I_eval[THEN beta_into_beta_eta, THEN red_into_equiv]

lemma subst_lift2[simp]: "(lift (lift t 0) 0)[x/Suc 0] = lift t 0"
proof -
  have "lift (lift t 0) 0 = lift (lift t 0) (Suc 0)" using lift_lift by simp
  thus ?thesis by simp
qed

lemma B_eval: "\<B> \<degree> g \<degree> f \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* g \<degree> (f \<degree> x)"
proof -
  have "\<B> \<degree> g \<degree> f \<degree> x \<rightarrow>\<^sub>\<beta> Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0)))[g/0] \<degree> f \<degree> x"
    by clarify
  also have "... = Abs (Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0))) \<degree> f \<degree> x"
    by (simp add: numerals)
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0))[f/0] \<degree> x"
    by (rule r_into_rtranclp) clarify
  also have "... = Abs (lift g 0 \<degree> (lift f 0 \<degree> Var 0)) \<degree> x"
    by simp
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* (lift g 0 \<degree> (lift f 0 \<degree> Var 0))[x/0]"
    by (rule r_into_rtranclp) clarify
  also have "... = g \<degree> (f \<degree> x)" by simp
  finally show ?thesis .
qed

lemmas B_equiv = B_eval[THEN beta_into_beta_eta, THEN red_into_equiv]

lemma T_eval: "\<T> \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x"
proof -
  have "\<T> \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta> Abs (Var 0 \<degree> Var 1)[x/0] \<degree> f" by clarify
  also have "... = Abs (Var 0 \<degree> lift x 0) \<degree> f" by simp
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* (Var 0 \<degree> lift x 0)[f/0]" by (rule r_into_rtranclp) clarify
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x" by simp
  finally show ?thesis .
qed

lemmas T_equiv = T_eval[THEN beta_into_beta_eta, THEN red_into_equiv]


lemma subst_liftn:
  "i \<le> n + k \<and> k \<le> i \<Longrightarrow> (liftn (Suc n) s k)[t/i] = liftn n s k"
by (induction s arbitrary: i k t) auto

lemma free_liftn:
  "free (liftn n t k) i = (i < k \<and> free t i \<or> k + n \<le> i \<and> free t (i - n))"
proof (induction t arbitrary: k i)
  case (Var x)
  show ?case by simp arith
next
  case (App s t)
  thus ?case by auto
next
  case (Abs t)
  thus ?case by simp (metis Suc_diff_le add_leD2)
qed


subsubsection \<open>Idiomatic terms\<close>

text \<open>Basic definitions\<close>

datatype itrm =
    Term dB | Pure dB
  | IAp itrm itrm (infixl "\<diamondop>" 150)

inductive itrm_cong :: "(itrm \<Rightarrow> itrm \<Rightarrow> bool) \<Rightarrow> itrm \<Rightarrow> itrm \<Rightarrow> bool"
for p
where
    base_cong: "p x y \<Longrightarrow> itrm_cong p x y"
  | term_subst: "x \<leftrightarrow> y \<Longrightarrow> itrm_cong p (Term x) (Term y)"
  | pure_subst: "x \<leftrightarrow> y \<Longrightarrow> itrm_cong p (Pure x) (Pure y)"
  | ap_congL: "itrm_cong p f f' \<Longrightarrow> itrm_cong p (f \<diamondop> x) (f' \<diamondop> x)"
  | ap_congR: "itrm_cong p x x' \<Longrightarrow> itrm_cong p (f \<diamondop> x) (f \<diamondop> x')"
  | itrm_sym[sym]: "itrm_cong p x y \<Longrightarrow> itrm_cong p y x"
  | itrm_trans[trans]: "itrm_cong p x y \<Longrightarrow> itrm_cong p y z \<Longrightarrow> itrm_cong p x z"

lemma ap_cong: "itrm_cong p f f' \<Longrightarrow> itrm_cong p x x' \<Longrightarrow> itrm_cong p (f \<diamondop> x) (f' \<diamondop> x')"
by (blast intro: itrm_cong.intros)

lemma itrm_refl[simp,intro]: "itrm_cong p x x"
by induction (auto intro: itrm_cong.intros ap_cong)

text \<open>Idiomatic terms are \emph{similar} iff they have the same structure, and all contained
  lambda terms are equivalent.\<close>

abbreviation similar :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" (infixl "\<cong>" 50)
where "x \<cong> y \<equiv> itrm_cong (\<lambda>_ _. False) x y"

lemma pure_similarE:
  assumes "Pure x' \<cong> y"
  obtains y' where "y = Pure y'" and "x' \<leftrightarrow> y'"
proof -
  have "(\<forall>x''. Pure x' = Pure x'' \<longrightarrow> (\<exists>y'. y = Pure y' \<and> x'' \<leftrightarrow> y')) \<and>
    (\<forall>x''. y = Pure x'' \<longrightarrow> (\<exists>y'. Pure x' = Pure y' \<and> x'' \<leftrightarrow> y'))"
  using assms proof (induction)
    case pure_subst thus ?case by (blast intro: term_sym)
  next
    case itrm_trans thus ?case by (fastforce intro: term_trans)
  qed simp_all
  with that show thesis by blast
qed

lemma term_similarE:
  assumes "Term x' \<cong> y"
  obtains y' where "y = Term y'" and "x' \<leftrightarrow> y'"
proof -
  from assms
  have "(\<forall>x''. Term x' = Term x'' \<longrightarrow> (\<exists>y'. y = Term y' \<and> x'' \<leftrightarrow> y')) \<and>
    (\<forall>x''. y = Term x'' \<longrightarrow> (\<exists>y'. Term x' = Term y' \<and> x'' \<leftrightarrow> y'))"
  proof (induction)
    case term_subst thus ?case by (blast intro: term_sym)
  next
    case itrm_trans thus ?case by (fastforce intro: term_trans)
  qed simp_all
  with that show thesis by blast
qed

lemma ap_similarE:
  assumes "x1 \<diamondop> x2 \<cong> y"
  obtains y1 y2 where "y = y1 \<diamondop> y2" and "x1 \<cong> y1" and "x2 \<cong> y2"
proof -
  from assms
  have "(\<forall>x1' x2'. x1 \<diamondop> x2 = x1' \<diamondop> x2' \<longrightarrow> (\<exists>y1 y2. y = y1 \<diamondop> y2 \<and> x1' \<cong> y1 \<and> x2' \<cong> y2)) \<and>
    (\<forall>x1' x2'. y = x1' \<diamondop> x2' \<longrightarrow> (\<exists>y1 y2. x1 \<diamondop> x2 = y1 \<diamondop> y2 \<and> x1' \<cong> y1 \<and> x2' \<cong> y2))"
  proof (induction)
    case ap_congL thus ?case by (blast intro: itrm_sym)
  next
    case ap_congR thus ?case by (blast intro: itrm_sym)
  next
    case itrm_trans thus ?case by (fastforce intro: itrm_cong.itrm_trans)
  qed simp_all
  with that show thesis by blast
qed

text \<open>The following relations define semantic equivalence of idiomatic terms.\<close>

inductive pre_equiv :: "itrm \<Rightarrow> itrm \<Rightarrow> bool"
where
    itrm_id: "pre_equiv x (Pure \<I> \<diamondop> x)"
  | itrm_comp: "pre_equiv (g \<diamondop> (f \<diamondop> x)) (Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x)"
  | itrm_hom: "pre_equiv (Pure f \<diamondop> Pure x) (Pure (f \<degree> x))"
  | itrm_xchng: "pre_equiv (f \<diamondop> Pure x) (Pure (\<T> \<degree> x) \<diamondop> f)"

abbreviation itrm_equiv :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" (infixl "\<simeq>" 50)
where
  "x \<simeq> y \<equiv> itrm_cong pre_equiv x y"

lemma pre_equiv_into_equiv: "pre_equiv x y \<Longrightarrow> x \<simeq> y" ..

lemmas itrm_id' = itrm_id[THEN pre_equiv_into_equiv]
lemmas itrm_comp' = itrm_comp[THEN pre_equiv_into_equiv]
lemmas itrm_hom' = itrm_hom[THEN pre_equiv_into_equiv]
lemmas itrm_xchng' = itrm_xchng[THEN pre_equiv_into_equiv]

lemma similar_equiv: "x \<cong> y \<Longrightarrow> x \<simeq> y"
by (induction pred: itrm_cong) (auto intro: itrm_cong.intros)

text \<open>Structural analysis\<close>

primrec opaque :: "itrm \<Rightarrow> dB list"
where
    "opaque (Term x) = [x]"
  | "opaque (Pure _) = []"
  | "opaque (f \<diamondop> x) = opaque f @ opaque x"

abbreviation "iorder x \<equiv> length (opaque x)"

primrec vary_terms :: "nat \<Rightarrow> itrm \<Rightarrow> nat \<Rightarrow> dB \<times> nat"
where
    "vary_terms n (Term _) i = (Var i, Suc i)"
  | "vary_terms n (Pure x) i = (liftn n x 0, i)"
  | "vary_terms n (f \<diamondop> x)  i = (case vary_terms n x i of (x', i') \<Rightarrow>
        apfst (\<lambda>f. f \<degree> x') (vary_terms n f i'))"

abbreviation "unlift' n x i \<equiv> fst (vary_terms n x i)"

primrec wrap_abs :: "dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "wrap_abs t 0 = t"
  | "wrap_abs t (Suc n) = Abs (wrap_abs t n)"

abbreviation "unlift x \<equiv> wrap_abs (unlift' (iorder x) x 0) (iorder x)"


lemma vary_terms_order: "snd (vary_terms n x i) = i + iorder x"
by (induction arbitrary: i) (auto simp add: case_prod_unfold)

lemma unlift_ap: "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
by (simp add: case_prod_unfold vary_terms_order)

lemma free_unlift: "free (unlift' n x i) j \<Longrightarrow> j \<ge> n \<or> (j \<ge> i \<and> j < i + iorder x)"
proof (induction x arbitrary: i)
  case (Term x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using free_liftn by simp
next
  case (IAp x y)
  thus ?case unfolding unlift_ap by fastforce
qed

lemma unlift_subst: "j \<le> i \<and> j \<le> n \<Longrightarrow> (unlift' (Suc n) t (Suc i))[s/j] = unlift' n t i"
proof (induction t arbitrary: i)
  case (Term x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using subst_liftn by simp
next
  case (IAp x y)
  thus ?case using unlift_ap by simp
qed

lemma wrap_abs_inside: "wrap_abs t (Suc n) = wrap_abs (Abs t) n"
by (induction n) auto

lemma wrap_abs_equiv: "s \<leftrightarrow> t \<Longrightarrow> wrap_abs s n \<leftrightarrow> wrap_abs t n"
by (induction n) auto

lemma list_equiv_refl[simp]: "list_all2 (op \<leftrightarrow>) x x"
by (induction x) (auto)

lemma list_equiv_suffix: "list_all2 (op \<leftrightarrow>) x y \<Longrightarrow> list_all2 (op \<leftrightarrow>) (x @ z) (y @ z)"
by(rule list_all2_appendI) simp_all

lemma list_equiv_prefix: "list_all2 (op \<leftrightarrow>) x y \<Longrightarrow> list_all2 (op \<leftrightarrow>) (z @ x) (z @ y)"
by(rule list_all2_appendI) simp_all

lemma opaque_equiv:
  assumes "x \<simeq> y"
    shows "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)"
using assms proof induction
  case (base_cong x y)
  thus ?case by induction auto
next
  case term_subst
  thus ?case by (auto)
next
  case ap_congL
  thus ?case by (auto intro: list_all2_appendI)
next
  case ap_congR
  thus ?case by (auto intro: list_all2_appendI)
next
  case itrm_sym
  thus ?case using list.rel_conversep[of "op \<leftrightarrow>"] by(simp add: fun_eq_iff)
next
  case itrm_trans
  show ?case by(rule list_all2_trans[OF _ itrm_trans.IH])(rule term_trans)
qed simp_all

lemma iorder_equiv: "x \<simeq> y \<Longrightarrow> iorder x = iorder y"
by(blast dest: opaque_equiv list_all2_lengthD)

lemma unlift'_equiv:
  assumes "x \<simeq> y"
    shows "unlift' n x i \<leftrightarrow> unlift' n y i"
using assms proof (induction arbitrary: n i)
  case (base_cong x y) thus ?case
  proof induction
    case (itrm_id x)
    show ?case
      unfolding unlift_ap using I_equiv[symmetric] by simp
  next
    case (itrm_comp g f x)
    let ?G = "unlift' n g (i + iorder f + iorder x)"
    let ?F = "unlift' n f (i + iorder x)"
    let ?X = "unlift' n x i"
    have "unlift' n (g \<diamondop> (f \<diamondop> x)) i = ?G \<degree> (?F \<degree> ?X)"
      unfolding unlift_ap by (simp add: add.assoc)
    moreover have "unlift' n (Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x) i = \<B> \<degree> ?G \<degree> ?F \<degree> ?X"
      unfolding unlift_ap by (simp add: add.commute add.left_commute)
    moreover have "?G \<degree> (?F \<degree> ?X) \<leftrightarrow> \<B> \<degree> ?G \<degree> ?F \<degree> ?X" using B_equiv[symmetric] .
    ultimately show ?case by simp
  next
    case (itrm_hom f x)
    show ?case by auto
  next
    case (itrm_xchng f x)
    let ?F = "unlift' n f i"
    let ?X = "liftn n x 0"
    have "unlift' n (f \<diamondop> Pure x) i = ?F \<degree> ?X"
      unfolding unlift_ap by simp
    moreover have "unlift' n (Pure (\<T> \<degree> x) \<diamondop> f) i = \<T> \<degree> ?X \<degree> ?F"
      unfolding unlift_ap by simp
    moreover have "?F \<degree> ?X \<leftrightarrow> \<T> \<degree> ?X \<degree> ?F" using T_equiv[symmetric] .
    ultimately show ?case by simp
  qed
next
  case term_subst
  thus ?case by simp
next
  case pure_subst
  thus ?case by (auto intro: equiv_liftn)
next
  case (ap_congL f f' x)
  have "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f' \<diamondop> x) i = unlift' n f' (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  ultimately show ?case using ap_congL.IH equiv_appL by auto
next
  case (ap_congR x x' f)
  from ap_congR.hyps have order_eq: "iorder x = iorder x'"
    using opaque_equiv list_all2_lengthD by blast
  have "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f \<diamondop> x') i = unlift' n f (i + iorder x) \<degree> unlift' n x' i"
    unfolding unlift_ap order_eq by simp
  ultimately show ?case using ap_congR.IH equiv_appR by auto
next
  case itrm_sym
  thus ?case using term_sym by simp
next
  case itrm_trans
  thus ?case using term_trans by blast
qed

lemma unlift_equiv: "x \<simeq> y \<Longrightarrow> unlift x \<leftrightarrow> unlift y"
using assms unlift'_equiv wrap_abs_equiv iorder_equiv by simp


subsubsection \<open>Canonical forms\<close>

inductive_set CF :: "itrm set"
where
    pure_cf[simp,intro]: "Pure x \<in> CF"
  | ap_cf[intro]:   "f \<in> CF \<Longrightarrow> f \<diamondop> Term x \<in> CF"

fun CF_head :: "itrm \<Rightarrow> dB"
where
    "CF_head (Pure x) = x"
  | "CF_head (f \<diamondop> x) = CF_head f"

lemma ap_cfD1[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> f \<in> CF"
by (rule CF.cases) auto

lemma ap_cfD2[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> \<exists>x'. x = Term x'"
by (rule CF.cases) auto

lemma term_not_cf[dest]: "Term x \<in> CF \<Longrightarrow> False"
by (rule CF.cases) auto

lemma cf_similarI:
  assumes "x \<in> CF" "y \<in> CF"
      and "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)"
      and "CF_head x \<leftrightarrow> CF_head y"
    shows "x \<cong> y"
using assms proof (induction arbitrary: y)
  case (pure_cf x)
  hence "opaque y = []" by auto
  with `y \<in> CF` obtain y' where "y = Pure y'" by cases auto
  with pure_cf.prems show ?case by (auto intro: itrm_cong.intros)
next
  case (ap_cf f x)
  from `list_all2 (op \<leftrightarrow>) (opaque (f \<diamondop> Term x)) (opaque y)`
  obtain y1 y2 where "opaque y = y1 @ y2" and "list_all2 (op \<leftrightarrow>) (opaque f) y1" 
    and "list_all2 (op \<leftrightarrow>) [x] y2"  by (auto simp add: list_all2_append1)
  from `list_all2 (op \<leftrightarrow>) [x] y2` obtain y' where "y2 = [y']" and "x \<leftrightarrow> y'"
    by(auto simp add: list_all2_Cons1)
  with `y \<in> CF` and `opaque y = y1 @ y2` obtain g
    where "opaque g = y1" and y_split: "y = g \<diamondop> Term y'" "g \<in> CF" by cases auto
  with ap_cf.prems `list_all2 (op \<leftrightarrow>) (opaque f) y1`
  have "list_all2 (op \<leftrightarrow>) (opaque f) (opaque g)" "CF_head f \<leftrightarrow> CF_head g" by auto
  with ap_cf.IH `g \<in> CF` have "f \<cong> g" by simp
  with ap_cf.prems y_split `x \<leftrightarrow> y'` show ?case by (auto intro: itrm_cong.intros ap_cong)
qed

lemma cf_unlift:
  assumes "x \<in> CF"
    shows "CF_head x \<leftrightarrow> unlift x"
using assms proof (induction set: CF)
  case (pure_cf x)
  show ?case by simp
next
  case (ap_cf f x)
  let ?n = "iorder f + 1"
  have "unlift (f \<diamondop> Term x) = wrap_abs (unlift' ?n f 1 \<degree> Var 0) ?n"
    unfolding unlift_ap by simp
  also have "... = wrap_abs (Abs (unlift' ?n f 1 \<degree> Var 0)) (iorder f)"
    using wrap_abs_inside by simp
  also have "... \<leftrightarrow> unlift f" proof -
    have "\<not> free (unlift' ?n f 1) 0" using free_unlift by fastforce
    hence "Abs (unlift' ?n f 1 \<degree> Var 0) \<rightarrow>\<^sub>\<eta> (unlift' ?n f 1)[Var 0/0]" ..
    also have "... = unlift' (iorder f) f 0"
      using unlift_subst by (metis One_nat_def Suc_eq_plus1 le0)
    finally show ?thesis
      by (simp add: r_into_rtranclp wrap_abs_equiv red_into_equiv)
  qed
  finally show ?case
    using CF_head.simps ap_cf.IH term_sym term_trans by metis
qed

lemma cf_similarD:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and similar: "x \<cong> y"
    shows "CF_head x \<leftrightarrow> CF_head y \<and> list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)"
using assms
by (blast intro!: similar_equiv opaque_equiv cf_unlift unlift_equiv intro: term_trans term_sym)

text \<open>Equivalent idiomatic terms in canonical form are similar. This justifies speaking of a
  normal form.\<close>

lemma cf_unique:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and equiv: "x \<simeq> y"
    shows "x \<cong> y"
using in_cf proof (rule cf_similarI)
  from equiv show "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)" by (rule opaque_equiv)
next
  from equiv have "unlift x \<leftrightarrow> unlift y" by (rule unlift_equiv)
  thus "CF_head x \<leftrightarrow> CF_head y"
    using cf_unlift[OF in_cf(1)] cf_unlift[OF in_cf(2)]
    using term_sym term_trans
    by metis
qed

subsubsection \<open>Normalization of idiomatic terms\<close>

fun rsize :: "itrm \<Rightarrow> nat"
where
    "rsize (x \<diamondop> y) = size y"
  | "rsize _ = 0"

function (sequential) normalize_pure_cf :: "itrm \<Rightarrow> itrm"
where
    "normalize_pure_cf (Pure g \<diamondop> (f \<diamondop> x)) = normalize_pure_cf (Pure (\<B> \<degree> g) \<diamondop> f) \<diamondop> x"
  | "normalize_pure_cf (Pure f \<diamondop> Pure x) = Pure (f \<degree> x)"
  | "normalize_pure_cf x = x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize_cf_pure :: "itrm \<Rightarrow> itrm"
where
    "normalize_cf_pure (f \<diamondop> Pure x) = normalize_pure_cf (Pure (\<T> \<degree> x) \<diamondop> f)"
  | "normalize_cf_pure x = x"

function (sequential) normalize_cf_cf :: "itrm \<Rightarrow> itrm"
where
    "normalize_cf_cf (g \<diamondop> (f \<diamondop> x)) = normalize_cf_cf (normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f) \<diamondop> x"
  | "normalize_cf_cf x = normalize_cf_pure x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize :: "itrm \<Rightarrow> itrm"
where
    "normalize (Pure x) = Pure x"
  | "normalize (Term x) = Pure \<I> \<diamondop> Term x"
  | "normalize (x \<diamondop> y)  = normalize_cf_cf (normalize x \<diamondop> normalize y)"


lemma pure_cf_in_cf:
  assumes "x \<in> CF"
    shows "normalize_pure_cf (Pure f \<diamondop> x) \<in> CF"
using assms
by (induction arbitrary: f rule: CF.induct) auto

lemma pure_cf_equiv: "normalize_pure_cf x \<simeq> x"
proof (induction rule: normalize_pure_cf.induct)
  case (1 g f x)
  have "normalize_pure_cf (Pure g \<diamondop> (f \<diamondop> x)) \<simeq> normalize_pure_cf (Pure (\<B> \<degree> g) \<diamondop> f) \<diamondop> x" by simp
  also from "1.IH" have "... \<simeq> Pure (\<B> \<degree> g) \<diamondop> f \<diamondop> x" by (rule ap_congL)
  also have "... \<simeq> Pure \<B> \<diamondop> Pure g \<diamondop> f \<diamondop> x" by (blast intro: itrm_hom'[symmetric] ap_congL)
  also have "... \<simeq> Pure g \<diamondop> (f \<diamondop> x)" by (rule itrm_comp'[symmetric])
  finally show ?case .
next
  case (2 f x)
  have "normalize_pure_cf (Pure f \<diamondop> Pure x) \<simeq> Pure (f \<degree> x)" by simp
  also have "... \<simeq> Pure f \<diamondop> Pure x" by (rule itrm_hom'[symmetric])
  finally show ?case .
qed auto

lemma cf_pure_in_cf:
  assumes "f \<in> CF"
    shows "normalize_cf_pure (f \<diamondop> Pure x) \<in> CF"
using assms
by (auto intro: pure_cf_in_cf)

lemma cf_pure_equiv: "normalize_cf_pure x \<simeq> x"
proof (induction rule: normalize_cf_pure.induct)
  case (1 f x)
  have "normalize_cf_pure (f \<diamondop> Pure x) \<simeq> normalize_pure_cf (Pure (\<T> \<degree> x) \<diamondop> f)" by simp
  also have "... \<simeq> Pure (\<T> \<degree> x) \<diamondop> f" by (rule pure_cf_equiv)
  also have "... \<simeq> f \<diamondop> Pure x" by (rule itrm_xchng'[symmetric])
  finally show ?case .
qed auto

lemma cf_cf_in_cf:
  assumes "x \<in> CF" and "f \<in> CF"
    shows "normalize_cf_cf (f \<diamondop> x) \<in> CF"
using assms
by (induction arbitrary: f rule: CF.induct) (auto intro: pure_cf_in_cf)

lemma cf_cf_equiv: "normalize_cf_cf x \<simeq> x"
proof (induction rule: normalize_cf_cf.induct)
  case (1 g f x)
  have "normalize_cf_cf (g \<diamondop> (f \<diamondop> x)) \<simeq> normalize_cf_cf (normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f) \<diamondop> x"
    by simp
  also from "1.IH" have "... \<simeq> normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f \<diamondop> x" by (rule ap_congL)
  also have "... \<simeq> Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x" by (blast intro: pure_cf_equiv ap_congL)
  also have "... \<simeq> g \<diamondop> (f \<diamondop> x)" by (rule itrm_comp'[symmetric])
  finally show ?case .
qed (auto simp del: normalize_cf_pure.simps intro: cf_pure_equiv)

lemma normalize_in_cf: "normalize x \<in> CF"
by (induction x rule: normalize.induct) (auto intro: cf_cf_in_cf)

lemma normalize_equiv: "normalize x \<simeq> x"
proof (induction rule: normalize.induct)
  case (2 x)
  have "normalize (Term x) \<simeq> Pure \<I> \<diamondop> Term x" by simp
  also have "... \<simeq> Term x" by (rule itrm_id'[symmetric])
  finally show ?case .
next
  case (3 x y)
  have "normalize (x \<diamondop> y) \<simeq> normalize_cf_cf (normalize x \<diamondop> normalize y)" by simp
  also have "... \<simeq> normalize x \<diamondop> normalize y" by (rule cf_cf_equiv)
  also from "3.IH" have "... \<simeq> x \<diamondop> normalize y" by (blast intro: ap_congL)
  also from "3.IH" have "... \<simeq> x \<diamondop> y" by (blast intro: ap_congR)
  finally show ?case .
qed auto

lemma normal_form: obtains n where "n \<simeq> x" and "n \<in> CF"
using normalize_equiv normalize_in_cf ..


subsubsection \<open>Proving lifted equations\<close>

theorem nf_lifting:
  assumes opaque: "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)"
      and base_eq: "unlift x \<leftrightarrow> unlift y"
    shows "x \<simeq> y"
proof -
  obtain n where "n \<simeq> x" and "n \<in> CF" by (rule normal_form)
  hence n_head: "CF_head n \<leftrightarrow> unlift x"
    using cf_unlift unlift_equiv by (blast intro: term_trans)
  from `n \<simeq> x` have n_opaque: "list_all2 (op \<leftrightarrow>) (opaque n) (opaque x)"
    by (rule opaque_equiv)
  obtain n' where "n' \<simeq> y" and "n' \<in> CF" by (rule normal_form)
  hence n'_head: "CF_head n' \<leftrightarrow> unlift y"
    using cf_unlift unlift_equiv by (blast intro: term_trans)
  from `n' \<simeq> y` have n'_opaque: "list_all2 (op \<leftrightarrow>) (opaque n') (opaque y)"
    by (rule opaque_equiv)
  from n_head n'_head base_eq have "CF_head n \<leftrightarrow> CF_head n'"
    by (blast intro: term_sym term_trans)
  moreover from n_opaque n'_opaque opaque list.rel_conversep[of "op \<leftrightarrow>"]
  have "list_all2 (op \<leftrightarrow>) (opaque n) (opaque n')"
    by(auto simp add: fun_eq_iff elim!: list_all2_trans[where ?P2.0="op \<leftrightarrow>", rotated] intro: term_trans)
  moreover note `n \<in> CF` `n' \<in> CF`
  ultimately have "n \<cong> n'" by (blast intro: cf_similarI)
  hence "n \<simeq> n'" by (rule similar_equiv)
  with `n \<simeq> x` `n' \<simeq> y` show "x \<simeq> y" by (blast intro: itrm_sym itrm_trans)
qed

end
