chapter SeCaV

(*
  Author: Jørgen Villadsen, DTU Compute, 2020
  Contributors: Stefan Berghofer, Asta Halkjær From, Alexander Birch Jensen & Anders Schlichtkrull
*)

section \<open>Sequent Calculus Verifier (SeCaV)\<close>

theory SeCaV imports Main begin

section \<open>Syntax: Terms / Formulas\<close>

datatype tm = Fun nat \<open>tm list\<close> | Var nat

datatype fm = Pre nat \<open>tm list\<close> | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm | Neg fm

section \<open>Semantics: Terms / Formulas\<close>

definition \<open>shift e v x \<equiv> \<lambda>n. if n < v then e n else if n = v then x else e (n - 1)\<close>

primrec semantics_term and semantics_list where
  \<open>semantics_term e f (Var n) = e n\<close> |
  \<open>semantics_term e f (Fun i l) = f i (semantics_list e f l)\<close> |
  \<open>semantics_list e f [] = []\<close> |
  \<open>semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l\<close>

primrec semantics where
  \<open>semantics e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)\<close> |
  \<open>semantics e f g (Dis p q) = (semantics e f g p \<or> semantics e f g q)\<close> |
  \<open>semantics e f g (Con p q) = (semantics e f g p \<and> semantics e f g q)\<close> |
  \<open>semantics e f g (Exi p) = (\<exists>x. semantics (shift e 0 x) f g p)\<close> |
  \<open>semantics e f g (Uni p) = (\<forall>x. semantics (shift e 0 x) f g p)\<close> |
  \<open>semantics e f g (Neg p) = (\<not> semantics e f g p)\<close>

\<comment> \<open>Test\<close>

corollary \<open>semantics e f g (Imp (Pre 0 []) (Pre 0 []))\<close>
  by simp

lemma \<open>\<not> semantics e f g (Neg (Imp (Pre 0 []) (Pre 0 [])))\<close>
  by simp

section \<open>Auxiliary Functions\<close>

primrec new_term and new_list where
  \<open>new_term c (Var n) = True\<close> |
  \<open>new_term c (Fun i l) = (if i = c then False else new_list c l)\<close> |
  \<open>new_list c [] = True\<close> |
  \<open>new_list c (t # l) = (if new_term c t then new_list c l else False)\<close>

primrec new where
  \<open>new c (Pre i l) = new_list c l\<close> |
  \<open>new c (Imp p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Dis p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Con p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Exi p) = new c p\<close> |
  \<open>new c (Uni p) = new c p\<close> |
  \<open>new c (Neg p) = new c p\<close>

primrec news where
  \<open>news c [] = True\<close> |
  \<open>news c (p # z) = (if new c p then news c z else False)\<close>

primrec inc_term and inc_list where
  \<open>inc_term (Var n) = Var (n + 1)\<close> |
  \<open>inc_term (Fun i l) = Fun i (inc_list l)\<close> |
  \<open>inc_list [] = []\<close> |
  \<open>inc_list (t # l) = inc_term t # inc_list l\<close>

primrec sub_term and sub_list where
  \<open>sub_term v s (Var n) = (if n < v then Var n else if n = v then s else Var (n - 1))\<close> |
  \<open>sub_term v s (Fun i l) = Fun i (sub_list v s l)\<close> |
  \<open>sub_list v s [] = []\<close> |
  \<open>sub_list v s (t # l) = sub_term v s t # sub_list v s l\<close>

primrec sub where
  \<open>sub v s (Pre i l) = Pre i (sub_list v s l)\<close> |
  \<open>sub v s (Imp p q) = Imp (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Dis p q) = Dis (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Con p q) = Con (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Exi p) = Exi (sub (v + 1) (inc_term s) p)\<close> |
  \<open>sub v s (Uni p) = Uni (sub (v + 1) (inc_term s) p)\<close> |
  \<open>sub v s (Neg p) = Neg (sub v s p)\<close>

primrec member where
  \<open>member p [] = False\<close> |
  \<open>member p (q # z) = (if p = q then True else member p z)\<close>

primrec ext where
  \<open>ext y [] = True\<close> |
  \<open>ext y (p # z) = (if member p y then ext y z else False)\<close>

\<comment> \<open>Simplifications\<close>

lemma member [iff]: \<open>member p z \<longleftrightarrow> p \<in> set z\<close>
  by (induct z) simp_all

lemma ext [iff]: \<open>ext y z \<longleftrightarrow> set z \<subseteq> set y\<close>
  by (induct z) simp_all

section \<open>Sequent Calculus\<close>

inductive sequent_calculus (\<open>\<tturnstile> _\<close> 0) where
  \<open>\<tturnstile> p # z\<close> if \<open>member (Neg p) z\<close> |
  \<open>\<tturnstile> Dis p q # z\<close> if \<open>\<tturnstile> p # q # z\<close> |
  \<open>\<tturnstile> Imp p q # z\<close> if \<open>\<tturnstile> Neg p # q # z\<close> |
  \<open>\<tturnstile> Neg (Con p q) # z\<close> if \<open>\<tturnstile> Neg p # Neg q # z\<close> |
  \<open>\<tturnstile> Con p q # z\<close> if \<open>\<tturnstile> p # z\<close> and \<open>\<tturnstile> q # z\<close> |
  \<open>\<tturnstile> Neg (Imp p q) # z\<close> if \<open>\<tturnstile> p # z\<close> and \<open>\<tturnstile> Neg q # z\<close> |
  \<open>\<tturnstile> Neg (Dis p q) # z\<close> if \<open>\<tturnstile> Neg p # z\<close> and \<open>\<tturnstile> Neg q # z\<close> |
  \<open>\<tturnstile> Exi p # z\<close> if \<open>\<tturnstile> sub 0 t p # z\<close> |
  \<open>\<tturnstile> Neg (Uni p) # z\<close> if \<open>\<tturnstile> Neg (sub 0 t p) # z\<close> |
  \<open>\<tturnstile> Uni p # z\<close> if \<open>\<tturnstile> sub 0 (Fun i []) p # z\<close> and \<open>news i (p # z)\<close> |
  \<open>\<tturnstile> Neg (Exi p) # z\<close> if \<open>\<tturnstile> Neg (sub 0 (Fun i []) p) # z\<close> and \<open>news i (p # z)\<close> |
  \<open>\<tturnstile> Neg (Neg p) # z\<close> if \<open>\<tturnstile> p # z\<close> |
  \<open>\<tturnstile> y\<close> if \<open>\<tturnstile> z\<close> and \<open>ext y z\<close>

\<comment> \<open>Test\<close>

corollary \<open>\<tturnstile> [Imp (Pre 0 []) (Pre 0 [])]\<close>
  using sequent_calculus.intros(1,3,13) ext.simps member.simps(2) by metis

section \<open>Shorthands\<close>

lemmas Basic = sequent_calculus.intros(1)

lemmas AlphaDis = sequent_calculus.intros(2)
lemmas AlphaImp = sequent_calculus.intros(3)
lemmas AlphaCon = sequent_calculus.intros(4)

lemmas BetaCon = sequent_calculus.intros(5)
lemmas BetaImp = sequent_calculus.intros(6)
lemmas BetaDis = sequent_calculus.intros(7)

lemmas GammaExi = sequent_calculus.intros(8)
lemmas GammaUni = sequent_calculus.intros(9)

lemmas DeltaUni = sequent_calculus.intros(10)
lemmas DeltaExi = sequent_calculus.intros(11)

lemmas Neg = sequent_calculus.intros(12)

lemmas Ext = sequent_calculus.intros(13)

\<comment> \<open>Test\<close>

lemma \<open>\<tturnstile>
  [
    Imp (Pre 0 []) (Pre 0 [])
  ]
  \<close>
proof -
  from AlphaImp have ?thesis if \<open>\<tturnstile>
    [
      Neg (Pre 0 []),
      Pre 0 []
    ]
    \<close>
    using that by simp
  with Ext have ?thesis if \<open>\<tturnstile>
    [
      Pre 0 [],
      Neg (Pre 0 [])
    ]
    \<close>
    using that by simp
  with Basic show ?thesis
    by simp
qed

section \<open>Appendix: Soundness\<close>

subsection \<open>Increment Function\<close>

primrec liftt :: \<open>tm \<Rightarrow> tm\<close> and liftts :: \<open>tm list \<Rightarrow> tm list\<close> where
  \<open>liftt (Var i) = Var (Suc i)\<close> |
  \<open>liftt (Fun a ts) = Fun a (liftts ts)\<close> |
  \<open>liftts [] = []\<close> |
  \<open>liftts (t # ts) = liftt t # liftts ts\<close>

subsection \<open>Parameters: Terms\<close>

primrec paramst :: \<open>tm \<Rightarrow> nat set\<close> and paramsts :: \<open>tm list \<Rightarrow> nat set\<close> where
  \<open>paramst (Var n) = {}\<close> |
  \<open>paramst (Fun a ts) = {a} \<union> paramsts ts\<close> |
  \<open>paramsts [] = {}\<close> |
  \<open>paramsts (t # ts) = (paramst t \<union> paramsts ts)\<close>

lemma p0 [simp]: \<open>paramsts ts = \<Union>(set (map paramst ts))\<close>
  by (induct ts) simp_all

primrec paramst' :: \<open>tm \<Rightarrow> nat set\<close> where
  \<open>paramst' (Var n) = {}\<close> |
  \<open>paramst' (Fun a ts) = {a} \<union> \<Union>(set (map paramst' ts))\<close>

lemma p1 [simp]: \<open>paramst' t = paramst t\<close>
  by (induct t) simp_all

subsection \<open>Parameters: Formulas\<close>

primrec params :: \<open>fm \<Rightarrow> nat set\<close> where
  \<open>params (Pre b ts) = paramsts ts\<close> |
  \<open>params (Imp p q) = params p \<union> params q\<close> |
  \<open>params (Dis p q) = params p \<union> params q\<close> |
  \<open>params (Con p q) = params p \<union> params q\<close> |
  \<open>params (Exi p) = params p\<close> |
  \<open>params (Uni p) = params p\<close> |
  \<open>params (Neg p) = params p\<close>

primrec params' :: \<open>fm \<Rightarrow> nat set\<close> where
  \<open>params' (Pre b ts) = \<Union>(set (map paramst' ts))\<close> |
  \<open>params' (Imp p q) = params' p \<union> params' q\<close> |
  \<open>params' (Dis p q) = params' p \<union> params' q\<close> |
  \<open>params' (Con p q) = params' p \<union> params' q\<close> |
  \<open>params' (Exi p) = params' p\<close> |
  \<open>params' (Uni p) = params' p\<close> |
  \<open>params' (Neg p) = params' p\<close>

lemma p2 [simp]: \<open>params' p = params p\<close>
  by (induct p) simp_all

fun paramst'' :: \<open>tm \<Rightarrow> nat set\<close> where
  \<open>paramst'' (Var n) = {}\<close> |
  \<open>paramst'' (Fun a ts) = {a} \<union> (\<Union>t \<in> set ts. paramst'' t)\<close>

lemma p1' [simp]: \<open>paramst'' t = paramst t\<close>
  by (induct t) simp_all

fun params'' :: \<open>fm \<Rightarrow> nat set\<close> where
  \<open>params'' (Pre b ts) = (\<Union>t \<in> set ts. paramst'' t)\<close> |
  \<open>params'' (Imp p q) = params'' p \<union> params'' q\<close> |
  \<open>params'' (Dis p q) = params'' p \<union> params'' q\<close> |
  \<open>params'' (Con p q) = params'' p \<union> params'' q\<close> |
  \<open>params'' (Exi p) = params'' p\<close> |
  \<open>params'' (Uni p) = params'' p\<close> |
  \<open>params'' (Neg p) = params'' p\<close>

lemma p2' [simp]: \<open>params'' p = params p\<close>
  by (induct p) simp_all

subsection \<open>Update Lemmas\<close>

lemma upd_lemma' [simp]:
  \<open>n \<notin> paramst t \<Longrightarrow> semantics_term e (f(n := z)) t = semantics_term e f t\<close>
  \<open>n \<notin> paramsts ts \<Longrightarrow> semantics_list e (f(n := z)) ts = semantics_list e f ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) auto

lemma upd_lemma [iff]: \<open>n \<notin> params p \<Longrightarrow> semantics e (f(n := z)) g p \<longleftrightarrow> semantics e f g p\<close>
  by (induct p arbitrary: e) simp_all

subsection \<open>Substitution\<close>

primrec substt :: \<open>tm \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm\<close> and substts :: \<open>tm list \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm list\<close> where
  \<open>substt (Var i) s k = (if k < i then Var (i - 1) else if i = k then s else Var i)\<close> |
  \<open>substt (Fun a ts) s k = Fun a (substts ts s k)\<close> |
  \<open>substts [] s k = []\<close> |
  \<open>substts (t # ts) s k = substt t s k # substts ts s k\<close>

primrec subst :: \<open>fm \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> fm\<close> where
  \<open>subst (Pre b ts) s k = Pre b (substts ts s k)\<close> |
  \<open>subst (Imp p q) s k = Imp (subst p s k) (subst q s k)\<close> |
  \<open>subst (Dis p q) s k = Dis (subst p s k) (subst q s k)\<close> |
  \<open>subst (Con p q) s k = Con (subst p s k) (subst q s k)\<close> |
  \<open>subst (Exi p) s k = Exi (subst p (liftt s) (Suc k))\<close> |
  \<open>subst (Uni p) s k = Uni (subst p (liftt s) (Suc k))\<close> |
  \<open>subst (Neg p) s k = Neg (subst p s k)\<close>

lemma shift_eq [simp]: \<open>i = j \<Longrightarrow> (shift e i T) j = T\<close> for i :: nat
  unfolding shift_def by simp

lemma shift_gt [simp]: \<open>j < i \<Longrightarrow> (shift e i T) j = e j\<close> for i :: nat
  unfolding shift_def by simp

lemma shift_lt [simp]: \<open>i < j \<Longrightarrow> (shift e i T) j = e (j - 1)\<close> for i :: nat
  unfolding shift_def by simp

lemma shift_commute [simp]: \<open>shift (shift e i U) 0 T = shift (shift e 0 T) (Suc i) U\<close>
  unfolding shift_def by force

lemma subst_lemma' [simp]:
  \<open>semantics_term e f (substt t u i) = semantics_term (shift e i (semantics_term e f u)) f t\<close>
  \<open>semantics_list e f (substts ts u i) = semantics_list (shift e i (semantics_term e f u)) f ts\<close>
  by (induct t and ts rule: substt.induct substts.induct) simp_all

lemma lift_lemma [simp]:
  \<open>semantics_term (shift e 0 x) f (liftt t) = semantics_term e f t\<close>
  \<open>semantics_list (shift e 0 x) f (liftts ts) = semantics_list e f ts\<close>
  by (induct t and ts rule: liftt.induct liftts.induct) simp_all

lemma subst_lemma [iff]:
  \<open>semantics e f g (subst a t i) \<longleftrightarrow> semantics (shift e i (semantics_term e f t)) f g a\<close>
  by (induct a arbitrary: e i t) simp_all

subsection \<open>Auxiliary Lemmas\<close>

lemma s1 [iff]: \<open>new_term c t \<longleftrightarrow> (c \<notin> paramst t)\<close> \<open>new_list c l \<longleftrightarrow> (c \<notin> paramsts l)\<close>
  by (induct t and l rule: new_term.induct new_list.induct) simp_all

lemma s2 [iff]: \<open>new c p \<longleftrightarrow> (c \<notin> params p)\<close>
  by (induct p) simp_all

lemma s3 [iff]: \<open>news c z \<longleftrightarrow> list_all (\<lambda>p. c \<notin> params p) z\<close>
  by (induct z) simp_all

lemma s4 [simp]: \<open>inc_term t = liftt t\<close> \<open>inc_list l = liftts l\<close>
  by (induct t and l rule: inc_term.induct inc_list.induct) simp_all

lemma s5 [simp]: \<open>sub_term v s t = substt t s v\<close> \<open>sub_list v s l = substts l s v\<close>
  by (induct t and l rule: inc_term.induct inc_list.induct) simp_all

lemma s6 [simp]: \<open>sub v s p = subst p s v\<close>
  by (induct p arbitrary: v s) simp_all

subsection \<open>Soundness\<close>

theorem sound: \<open>\<tturnstile> z \<Longrightarrow> \<exists>p \<in> set z. semantics e f g p\<close>
proof (induct arbitrary: f rule: sequent_calculus.induct)
  case (10 i p z)
  then show ?case
  proof (cases \<open>\<forall>x. semantics e (f(i := \<lambda>_. x)) g (sub 0 (Fun i []) p)\<close>)
    case False
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) z\<close>
      using 10 by simp
    ultimately show ?thesis
      using 10 Ball_set insert_iff list.set(2) upd_lemma by metis
  qed simp
next
  case (11 i p z)
  then show ?case
  proof (cases \<open>\<forall>x. semantics e (f(i := \<lambda>_. x)) g (Neg (sub 0 (Fun i []) p))\<close>)
    case False
    moreover have \<open>list_all (\<lambda>p. i \<notin> params p) z\<close>
      using 11 by simp
    ultimately show ?thesis
      using 11 Ball_set insert_iff list.set(2) upd_lemma by metis
  qed simp
qed force+

corollary \<open>\<tturnstile> z \<Longrightarrow> \<exists>p. member p z \<and> semantics e f g p\<close>
  using sound by force

corollary \<open>\<tturnstile> [p] \<Longrightarrow> semantics e f g p\<close>
  using sound by force

corollary \<open>\<not> (\<tturnstile> [])\<close>
  using sound by force

section \<open>Reference\<close>

text \<open>Mordechai Ben-Ari (Springer 2012): Mathematical Logic for Computer Science (Third Edition)\<close>

end
