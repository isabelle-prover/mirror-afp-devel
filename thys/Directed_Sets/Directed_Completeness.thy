theory Directed_Completeness
  imports 
    Complete_Non_Orders.Continuity 
    Well_Order_Connection
    "HOL-Cardinals.Cardinals" 
    "HOL-Library.FuncSet"
begin

subsection \<open>Missing Lemmas\<close>

no_notation disj  (infixr "|" 30)

lemma Sup_funpow_mono:
  fixes f :: "'a :: complete_lattice \<Rightarrow> 'a"
  assumes mono: "mono f"
  shows "mono (\<Squnion>i. f ^^ i)"
  by (intro monoI, auto intro!: Sup_mono dest: funpow_mono[OF mono])

lemma iso_imp_compat:
  assumes iso: "iso r r' f" shows "compat r r' f"
  by (simp add: compat_def iso iso_forward)

lemma iso_inv_into:
  assumes ISO: "iso r r' f"
  shows "iso r' r (inv_into (Field r) f)"
  using assms unfolding iso_def
  using bij_betw_inv_into inv_into_Field_embed_bij_betw by blast

lemmas iso_imp_compat_inv_into = iso_imp_compat[OF iso_inv_into]

lemma infinite_iff_natLeq: "infinite A \<longleftrightarrow> natLeq \<le>o |A|"
  using infinite_iff_natLeq_ordLeq by blast

text \<open>As we cannot formalize transfinite sequences directly, we take the following approach:
We just use @{term A} as the index set, and instead of the ordering on ordinals,
we take the well-order that is chosen by the cardinality library to denote @{term "|A|"}.\<close>

definition well_order_of ("('(\<preceq>\<^bsub>_\<^esub>'))" [0]1000) where "(\<preceq>\<^bsub>A\<^esub>) x y \<equiv> (x,y) \<in> |A|"

abbreviation well_order_le ("_ \<preceq>\<^bsub>_\<^esub> _" [51,0,51]50) where "x \<preceq>\<^bsub>A\<^esub> y \<equiv> (\<preceq>\<^bsub>A\<^esub>) x y"

abbreviation well_order_less ("_ \<prec>\<^bsub>_\<^esub> _" [51,0,51]50) where "x \<prec>\<^bsub>A\<^esub> y \<equiv> asympartp (\<preceq>\<^bsub>A\<^esub>) x y"

lemmas well_order_ofI = well_order_of_def[unfolded atomize_eq, THEN iffD2]
lemmas well_order_ofD = well_order_of_def[unfolded atomize_eq, THEN iffD1]

lemma carrier: assumes "x \<preceq>\<^bsub>A\<^esub> y" shows "x \<in> A" and "y \<in> A"
  using assms by (auto dest!: well_order_ofD dest: FieldI1 FieldI2)

lemma relation_of[simp]: "relation_of (\<preceq>\<^bsub>A\<^esub>) A = |A|"
  by (auto simp: relation_of_def well_order_of_def dest: FieldI1 FieldI2)

interpretation well_order_of: well_ordered_set A "(\<preceq>\<^bsub>A\<^esub>)"
  apply (fold well_order_on_relation_of)
  by auto

text \<open>Thanks to the well-order theorem,
one can have a sequence $\{A_\alpha\}_{\alpha < |A|}$ of subsets of $A$ that satisfies the 
following three conditions:
\begin{itemize}
\item cardinality: $|A_\alpha| < |A|$ for every $\alpha < |A|$,
\item monotonicity: $A_\alpha \subseteq A_\beta$ whenever $\alpha \le \beta < |A|$, and
\item range: if $A$ is infinite, $A = \bigcup_{\alpha < |A|} A_\alpha$.
\end{itemize}
The following serves the purpose.\<close>

definition Pre ("_\<^sub>\<prec>" [1000]1000) where "A\<^sub>\<prec> a \<equiv> {b \<in> A. b \<prec>\<^bsub>A\<^esub> a}"

lemma Pre_eq_underS: "A\<^sub>\<prec> a = underS |A| a"
  by (auto simp: Pre_def underS_def well_order_ofD carrier well_order_of.antisym dest!: well_order_ofI)

lemma Pre_card: assumes aA: "a \<in> A" shows "|A\<^sub>\<prec> a| <o |A|"
  by (auto simp: Pre_eq_underS aA intro!: card_of_underS[OF card_of_Card_order])

lemma Pre_carrier: "A\<^sub>\<prec> a \<subseteq> A" by (auto simp: Pre_def)

lemma Pre_mono: "monotone_on A (\<preceq>\<^bsub>A\<^esub>) (\<subseteq>) (A\<^sub>\<prec>)"
  by (auto intro!: monotone_onI simp: Pre_def dest: well_order_of.asym_trans well_order_of.asym.irrefl)

lemma extreme_imp_finite:
  assumes e: "extreme A (\<preceq>\<^bsub>A\<^esub>) e" shows "finite A"
proof (rule ccontr)
  assume inf: "infinite A"
  from e have eA: "e \<in> A" by auto
  from e have "A = {a \<in> A. a \<preceq>\<^bsub>A\<^esub> e}" by auto
  also have "\<dots> - {e} = A\<^sub>\<prec> e"
    using eA by (auto simp: Pre_def dest: well_order_of.asympartp_iff_weak_neq)
  finally have AeP: "A - {e} = \<dots>".
  have "infinite (A - {e})" using infinite_remove[OF inf].
  with AeP have infP: "infinite (A\<^sub>\<prec> e)" by simp
  have "A = insert e (A\<^sub>\<prec> e)" using eA by (fold AeP, auto)
  also have "|\<dots>| =o |A\<^sub>\<prec> e|" using infinite_card_of_insert[OF infP].
  finally have "|A\<^sub>\<prec> e| =o |A|" using ordIso_symmetric by auto
  with Pre_card[OF eA] not_ordLess_ordIso
  show False by auto
qed

lemma infinite_imp_ex_Pre:
  assumes inf: "infinite A" and xA: "x \<in> A" shows "\<exists>y \<in> A. x \<in> A\<^sub>\<prec> y"
proof-
  from inf
  have "\<not> extreme A (\<preceq>\<^bsub>A\<^esub>) x" by (auto dest!: extreme_imp_finite)
  with xA obtain y where yA: "y \<in> A" and "\<not> y \<preceq>\<^bsub>A\<^esub> x" by auto
  with xA have "x \<prec>\<^bsub>A\<^esub> y" by (auto simp: well_order_of.not_weak_iff asympartpI)
  with yA show ?thesis by (auto simp: Pre_def xA)
qed

lemma infinite_imp_Un_Pre: assumes inf: "infinite A" shows "\<Union>(A\<^sub>\<prec> ` A) = A"
proof (safe)
  fix x assume xA: "x \<in> A"
  show "y \<in> A\<^sub>\<prec> x \<Longrightarrow> y \<in> A" for y using Pre_carrier[of A x] by auto
  from infinite_imp_ex_Pre[OF inf xA]
  show "x \<in> \<Union> (A\<^sub>\<prec> ` A)" by (auto simp: Pre_def)
qed

section \<open>Iwamura's lemma\<close>

text \<open>As the proof involves a number of (inductive) definitions,
we build a locale for collecting those definitions and lemmas.\<close>

locale Iwamura_proof = related_set +
  assumes dir: "directed_set A (\<sqsubseteq>)"
begin

text \<open>Inside this locale, a related set $(A,\LE)$ is fixed and assumed to be directed.
The proof starts with declaring, using the axiom of choice, a function $f$ that chooses a bound 
$f\ X \in A$ for every finite subset $X \subseteq A$.
This function can be formalized using the SOME construction:\<close>

definition f where "f X \<equiv> SOME z. z \<in> A \<and> bound X (\<sqsubseteq>) z"

lemma assumes XA: "X \<subseteq> A" and Xfin: "finite X"
  shows f_carrier: "f X \<in> A" and f_bound: "bound X (\<sqsubseteq>) (f X)"
  using directed_setD[OF dir XA Xfin, unfolded Bex_def, THEN someI_ex]
  by (auto simp: f_def)

subsection \<open>Uncountable Case\<close>

text \<open>Actually, the main part of the proof of Iwamura's Lemma is about monotonically 
expanding an infinite subset (in particular $A_\alpha$) of @{term A} into a directed one,
without changing the cardinality.
To this end, Iwamura's original proof introduces a function $F\colon\,Pow A \to Pow A$ 
that expands a set with upper bounds of \emph{all finite subsets}.
This approach is different from Markowsky's reproof (based on \cite{Skorniakov64}) 
which uses nested transfinite induction to extend a set one element after another.\<close>

definition F where "F X \<equiv> X \<union> f ` Fpow X"

lemma F_carrier: "X \<subseteq> A \<Longrightarrow> F X \<subseteq> A"
  and F_infl: "X \<subseteq> F X"
  and F_fin: "finite X \<Longrightarrow> finite (F X)"
  by (auto simp: F_def Fpow_def f_carrier)

lemma F_card: assumes inf: "infinite X" shows "|F X| =o |X|"
proof-
  have "|f ` Fpow X| \<le>o |Fpow X|" using card_of_image.
  thm card_of_Fpow_infinite
  also have "|Fpow X| =o |X|" using card_of_Fpow_infinite[OF inf].
  finally have "|f ` Fpow X| \<le>o |X|".
  with inf show ?thesis by (auto simp: F_def)
qed

lemma F_mono: "mono F"
proof(intro monoI)
  show "X \<subseteq> Y \<Longrightarrow> F X \<subseteq> F Y" for X Y
    using Fpow_mono[of X Y] by (auto simp: F_def)
qed

lemma Fn_carrier: "X \<subseteq> A \<Longrightarrow> (F ^^ n) X \<subseteq> A"
  and Fn_infl: "X \<subseteq> (F ^^ n) X"
  and Fn_fin: "finite X \<Longrightarrow> finite ((F ^^ n) X)"
  and Fn_card: "infinite X \<Longrightarrow> |(F ^^ n) X| =o |X|"
proof (atomize(full), induct n)
  case (Suc n)
  define Y where "Y \<equiv> (F^^n) X"
  then have *: "(F ^^ Suc n) X = F Y" by auto
  from Suc[folded Y_def]
  have "infinite X \<Longrightarrow> infinite Y \<and> |Y| =o |X|"
    and "finite X \<Longrightarrow> finite Y"
    and "X \<subseteq> Y"
    and "X \<subseteq> A \<Longrightarrow> Y \<subseteq> A" by (auto simp: Y_def)
  with F_carrier[of "Y"] F_infl[of "Y"] F_card[of "Y"] F_fin[of "Y"]
  show ?case by (unfold *, auto del:subsetI dest:ordIso_transitive)
qed auto

lemma Fn_mono1: "i \<le> j \<Longrightarrow> (F ^^ i) X \<subseteq> (F ^^ j) X" for i j
  using Fn_infl[of "(F^^i) X" "j-i"] funpow_add[of "j-i" i F]
  by auto

text \<open>We take the $\omega$-iteration of the monotone function @{term F}, namely:\<close>

definition Flim ("F\<^sup>\<omega>") where "F\<^sup>\<omega> X \<equiv> \<Union>i. (F ^^ i) X"

lemma Flim_mono: "mono F\<^sup>\<omega>"
proof-
  have "F\<^sup>\<omega> = (\<Squnion> range ((^^) F))" by (auto simp: Flim_def)
  with Sup_funpow_mono[OF F_mono]
  show ?thesis by auto
qed

lemma Flim_infl: "X \<subseteq> F\<^sup>\<omega> X"
  using Fn_infl by (auto simp: Flim_def)

lemma Flim_carrier: assumes "X \<subseteq> A" shows "F\<^sup>\<omega> X \<subseteq> A"
  using Fn_carrier[OF assms] by (auto simp: Flim_def)

lemma Flim_directed: assumes "X \<subseteq> A" shows "directed_set (F\<^sup>\<omega> X) (\<sqsubseteq>)"
proof (safe intro!: directed_setI)
  fix Y assume YC: "Y \<subseteq> F\<^sup>\<omega> X" and finY: "finite Y"
  from finY YC have "\<exists>i. Y \<subseteq> (F ^^ i) X"
  proof (induct)
    case empty
    then show ?case by auto
  next
    case (insert y Y)
    then obtain i j where Yi: "Y \<subseteq> (F ^^ i) X" and "y \<in> (F ^^ j) X" by (auto simp: Flim_def)
    with Fn_mono1[OF max.cobounded1[of i j], of X] Fn_mono1[OF max.cobounded2[of j i], of X]
    show ?case by (auto intro!: exI[of _ "max i j"])
  qed
  then obtain i where Yi: "Y \<subseteq> (F ^^ i) X" by auto
  with Fn_carrier[OF assms] have YA: "Y \<subseteq> A" by auto
  from Yi finY have "f Y \<in> (F ^^ Suc i) X" by (auto simp: F_def Fpow_def)
  then have "f Y \<in> F\<^sup>\<omega> X" by (auto simp: Flim_def simp del: funpow.simps)
  with f_bound[OF YA finY]
  show "\<exists>z\<in>F\<^sup>\<omega> X. bound Y (\<sqsubseteq>) z" by auto
qed

lemma Flim_card: assumes "infinite X" shows "|F\<^sup>\<omega> X| =o |X|"
proof-
  from assms have natX: "|UNIV :: nat set| \<le>o |X|" by (simp add: infinite_iff_card_of_nat)
  have "|F\<^sup>\<omega> X| \<le>o |X|"
    apply (unfold Flim_def, rule card_of_UNION_ordLeq_infinite[OF assms natX])
    using Fn_card[OF assms] ordIso_imp_ordLeq
    by auto
  with Flim_infl show "|F\<^sup>\<omega> X| =o |X|" by (simp add: ordIso_iff_ordLeq)
qed

lemma Flim_fin: assumes "finite X" shows "|F\<^sup>\<omega> X| \<le>o natLeq"
proof-
  have "|F\<^sup>\<omega> X| \<le>o |UNIV :: nat set|"
    apply (unfold Flim_def)
    apply (rule card_of_UNION_ordLeq_infinite)
    by (auto simp: Fn_fin[OF assms] intro!: ordLess_imp_ordLeq)
  then show ?thesis using card_of_nat ordLeq_ordIso_trans by auto
qed

lemma mono_uncountable: "monotone_on A (\<preceq>\<^bsub>A\<^esub>) (\<subseteq>) (F\<^sup>\<omega> \<circ> A\<^sub>\<prec>)"
  using monotone_on_o[OF Flim_mono Pre_mono]
  by (auto simp: o_def)

lemma card_uncountable:
  assumes aA: "a \<in> A" and unc: "natLeq <o |A|"
  shows "|F\<^sup>\<omega> (A\<^sub>\<prec> a)| <o |A|"
proof (cases "finite (A\<^sub>\<prec> a)")
  case True
  note Flim_fin[OF this]
  also note unc
  finally show ?thesis
    using unc not_ordLess_ordIso by auto
next
  case False
  note Flim_card[OF this]
  also note Pre_card[OF aA]
  finally show ?thesis using unc not_ordLess_ordIso by auto
qed

lemma in_I_uncountable: 
  assumes aA: "a \<in> A" and inf: "infinite A"
  shows "\<exists>a' \<in> A. a \<in> F\<^sup>\<omega> (A\<^sub>\<prec> a')"
  using infinite_imp_ex_Pre[OF inf aA] Flim_infl
  by auto

lemma carrier_uncountable:
  shows "F\<^sup>\<omega> (A\<^sub>\<prec> a) \<subseteq> A"
  using Flim_carrier[OF Pre_carrier]
  by auto

lemma range_uncountable: assumes inf: "infinite A" shows "\<Union>((F\<^sup>\<omega> \<circ> A\<^sub>\<prec>) ` A) = A"
proof (safe intro!: subset_antisym)
  fix a assume aA: "a \<in> A"
  from infinite_imp_ex_Pre[OF inf aA] Flim_infl
  show "a \<in> \<Union> ((F\<^sup>\<omega> \<circ> A\<^sub>\<prec>) ` A)" by auto
  show "x \<in> (F\<^sup>\<omega> \<circ> A\<^sub>\<prec>) a \<Longrightarrow> x \<in> A" for x  
    using carrier_uncountable by auto
qed

lemma infl_uncountable:
  assumes aA: "a \<in> A" and bA: "b \<in> A" and ab: "a \<prec>\<^bsub>A\<^esub> b" 
  shows "a \<in> F\<^sup>\<omega> (A\<^sub>\<prec> b)"
  using assms Flim_infl[of "A\<^sub>\<prec> b"] 
  by (auto simp: Pre_def)

subsection \<open>Countable Case\<close>

context
  assumes countable: "|A| =o natLeq"
begin

text \<open>The assumption above means that there exists an order-isomorphism between $(\Nat,\le)$ and 
$(A,\preceq_A)$.\<close>

definition seq :: "nat \<Rightarrow> 'a" where "seq \<equiv> SOME f. iso natLeq |A| f"

lemma seq_iso: "iso natLeq |A| seq"
  apply (unfold seq_def)
  apply (rule someI_ex[of "iso natLeq |A|"])
  using countable[THEN ordIso_symmetric]
  apply (unfold ordIso_def) by auto

lemma seq_bij_betw: "bij_betw seq UNIV A"
  using seq_iso by (auto simp: iso_def Field_natLeq)

text \<open>This means that $A$ has been indexed by $\Nat$.\<close>

lemma range_seq: "range seq = A"
  using seq_bij_betw bij_betw_imp_surj_on by force

lemma seq_mono: "monotone (\<le>) (\<preceq>\<^bsub>A\<^esub>) seq"
  using iso_imp_compat[OF seq_iso]
  by (auto intro!: monotoneI well_order_ofI simp: compat_def natLeq_def)

lemma inv_seq_mono: "monotone_on A (\<preceq>\<^bsub>A\<^esub>) (\<le>) (inv seq)"
  using iso_imp_compat_inv_into[OF seq_iso]
  unfolding Field_natLeq
  by (auto intro!: monotone_onI simp: natLeq_def compat_def well_order_of_def)

text \<open>We turn the sequence into a sequence of directed subsets of @{term A}:\<close>

fun Seq :: "nat \<Rightarrow> 'a set" where
  "Seq 0 = {f {}}"
| "Seq (Suc n) = Seq n \<union> {seq n, f (Seq n \<union> {seq n})}"

lemma seq_n_in_Seq_n: "seq n \<in> Seq (Suc n)" by auto

lemma Seq_finite: "finite (Seq n)" 
  by (induction n) auto

lemma Seq_card: "|Seq n| <o |A|"
  using countable Seq_finite by (simp add: ordIso_natLeq_infinite1)

lemma Seq_carrier: "Seq n \<subseteq> A"
proof(induction n)
  case 0
  show ?case by (auto intro!: f_carrier)
next
  case (Suc n)
  with range_seq have sgA: "Seq n \<union> {seq n} \<subseteq> A" by auto
  from Seq_finite f_carrier[OF sgA]
  have "f (Seq n \<union> {seq n}) \<in> A" by auto
  with sgA show ?case by auto
qed

lemma Seq_range: "\<Union>(range Seq) = A"
proof (intro equalityI)
  from Seq_carrier show "\<Union>(range Seq) \<subseteq> A" by auto
  show "A \<subseteq> \<Union>(range Seq)"
  proof
    fix a assume aA: "a \<in> A"
    with seq_bij_betw obtain n where "a = seq n"
      by (metis bij_betw_inv_into_right)
    with seq_n_in_Seq_n show "a \<in> \<Union>(range Seq)" by (auto intro!: exI[of _ "Suc n"])
  qed
qed

lemma Seq_extremed:
  assumes refl: "reflexive A (\<sqsubseteq>)" shows "extremed (Seq n) (\<sqsubseteq>)"
proof -
  interpret reflexive using refl.
  show ?thesis 
  proof(induction n)
    case 0
    show ?case by (auto intro!: extremedI extremeI f_carrier)
  next
    case (Suc n)
    show ?case
    proof (intro extremedI extremeI)
      show "f (Seq n \<union> {seq n}) \<in> Seq (Suc n)" by auto
      fix x assume xssn: "x \<in> Seq (Suc n)"
      show "x \<sqsubseteq> f (Seq n \<union> {seq n})"
      proof(cases "x \<in> Seq n \<union> {seq n}")
        case True
        with f_bound[of "Seq n \<union> {seq n}"] range_seq Seq_finite[of "n"]
          Seq_carrier[of "n"]
        show ?thesis by (auto simp: bound_def)
      next
        case False
        with xssn have x: "x = f (Seq n \<union> {seq n})" by auto
        from range_seq Seq_finite[of "n"] Seq_carrier[of "n"]
        show ?thesis by (auto simp: x intro!: f_carrier)
      qed
    qed
  qed
qed

lemma Seq_directed: assumes refl: "reflexive A (\<sqsubseteq>)" shows "directed_set (Seq n) (\<sqsubseteq>)"
  using Seq_extremed[OF refl] by (simp add: directed_set_iff_extremed[OF Seq_finite])

lemma range_countable: "\<Union>((Seq \<circ> inv seq) ` A) = A"
  apply (fold image_comp)
  apply (unfold bij_betw_imp_surj_on[OF bij_betw_inv_into[OF seq_bij_betw]])
  using Seq_range.

lemma Seq_mono: "mono Seq"
proof (intro monoI)
  show "n \<le> m \<Longrightarrow> Seq n \<subseteq> Seq m" for n m by (induct rule:inc_induct, auto)
qed

lemma mono_countable: "monotone_on A (\<preceq>\<^bsub>A\<^esub>) (\<subseteq>) (Seq \<circ> inv seq)"
  by (rule monotone_on_o[OF Seq_mono inv_seq_mono]) auto

lemma infl_countable:
  assumes aA: "a \<in> A" and bA: "b \<in> A" and ab: "a \<prec>\<^bsub>A\<^esub> b" 
  shows "a \<in> Seq (inv seq b)"
proof-
  from aA seq_bij_betw seq_n_in_Seq_n
  have a: "a \<in> Seq (Suc (inv seq a))" by (simp add: bij_betw_inv_into_right)
  from ab have "inv seq a < inv seq b"
    by (metis (mono_tags, lifting) aA well_order_of.asympartp_iff_weak_neq bA range_seq inv_seq_mono inv_into_injective not_le_imp_less ord.mono_onD verit_la_disequality)
  then have "Suc (inv seq a) \<le> inv seq b" by auto
  from a monoD[OF Seq_mono this] have "a \<in> Seq (inv seq b)" by auto
  then show ?thesis by auto
qed

end

text \<open>To match the types, we use the inverse @{term "inv seq :: 'a \<Rightarrow> nat"} of the isomorphism 
\@{term seq}.
We define the final $I$ as follows:\<close>

definition I where "I \<equiv> if |A| =o natLeq then Seq \<circ> inv seq else F\<^sup>\<omega> \<circ> A\<^sub>\<prec>"

lemma I_carrier: "I a \<subseteq> A"
  using Seq_carrier carrier_uncountable by (auto simp: I_def)

lemma I_directed: assumes "reflexive A (\<sqsubseteq>)" shows "directed_set (I a) (\<sqsubseteq>)"
  using Seq_directed[OF _ assms] Flim_directed[OF Pre_carrier] 
  by (auto simp: I_def)

lemma I_mono: "monotone_on A (\<preceq>\<^bsub>A\<^esub>) (\<subseteq>) I"
  by (auto simp: mono_uncountable mono_countable I_def)

lemma I_card:
  assumes inf: "infinite A" and aA: "a \<in> A"
  shows "|I a| <o |A|"
proof (cases "|A| =o natLeq")
  case True 
  with Seq_finite[OF this] show ?thesis by (simp add: I_def inf)
next
  case F: False
  with inf have "natLeq <o |A|"
    by (auto simp: infinite_iff_natLeq ordLeq_iff_ordLess_or_ordIso ordIso_symmetric)
  from card_uncountable[OF aA this] show ?thesis by (auto simp: I_def F)
qed

lemma I_range: assumes inf: "infinite A" shows "\<Union>(I`A) = A"
  using range_uncountable[OF inf] range_countable by (auto simp: I_def)

lemma I_infl: assumes "a \<in> A" "b \<in> A" "a \<prec>\<^bsub>A\<^esub> b" shows "a \<in> I b" 
  using infl_countable infl_uncountable assms by (auto simp: I_def)

end

text \<open>Now we close the locale @{locale Iwamura_proof} and state the final result in the global 
scope.\<close>

theorem (in reflexive) Iwamura:
  assumes dir: "directed_set A (\<sqsubseteq>)" and inf: "infinite A"
  shows "\<exists>I. (\<forall>a \<in> A. directed_set (I a) (\<sqsubseteq>) \<and> |I a| <o |A| ) \<and> 
    monotone_on A (\<preceq>\<^bsub>A\<^esub>) (\<subseteq>) I \<and> \<Union>(I`A) = A"
proof-
  interpret Iwamura_proof using dir by unfold_locales
  show ?thesis using I_mono I_card[OF inf] I_directed I_range[OF inf]
    by (auto intro!: exI[of _ I])
qed

section \<open>Directed Completeness and Scott-Continuity\<close>

abbreviation "nonempty A \<equiv> if A = {} then \<bottom> else \<top>"

lemma (in quasi_ordered_set) directed_completeness_lemma:
  fixes leB (infix "\<unlhd>" 50)
  assumes comp: "(nonempty \<sqinter> well_related_set)-complete A (\<sqsubseteq>)" and dir: "directed_set D (\<sqsubseteq>)" and DA: "D \<subseteq> A"
  shows "\<exists>s. extreme_bound A (\<sqsubseteq>) D s"
    and "well_related_set-continuous A (\<sqsubseteq>) B (\<unlhd>) f \<Longrightarrow>
          D \<noteq> {} \<Longrightarrow> extreme_bound A (\<sqsubseteq>) D t \<Longrightarrow> extreme_bound B (\<unlhd>) (f ` D) (f t)"
proof (atomize(full), insert wf_ordLess dir DA, induct "|D|" arbitrary: D t rule: wf_induct_rule)
  interpret less_eq_symmetrize.
  case less
  note this(1)
  note IH = this[THEN conjunct1]
    and IH2 = this[THEN conjunct2, rule_format]
  note DA = \<open>D \<subseteq> A\<close>
  interpret D: quasi_ordered_set D "(\<sqsubseteq>)" using quasi_ordered_subset[OF DA].
  note dir = \<open>directed_set D (\<sqsubseteq>)\<close>
  show ?case
  proof(cases "finite D")
    case True
    from directed_set_iff_extremed[OF True] dir
    obtain d where dD: "d \<in> D" and exd: "extreme D (\<sqsubseteq>) d" by (auto simp: extremed_def)
    then have dd: "d \<sqsubseteq> d" by (auto simp: extreme_def)
    show ?thesis
    proof(intro conjI allI impI exI[of _ d])
      from extreme_imp_extreme_bound[OF exd DA]
      show exbd: "extreme_bound A (\<sqsubseteq>) D d" by auto
      assume f: "well_related_set-continuous A (\<sqsubseteq>) B (\<unlhd>) f"
        and Dt: "extreme_bound A (\<sqsubseteq>) D t" and D0: "D \<noteq> {}"
      from f[THEN continuous_carrierD] have fAB: "f ` A \<subseteq> B" by auto
      from Dt have tA: "t \<in> A" by auto
      show "extreme_bound B (\<unlhd>) (f ` D) (f t)"
      proof (safe intro!: extreme_boundI)
        from fAB tA show "f t \<in> B" by auto
        fix x assume xD: "x \<in> D"
        from xD Dt have xt: "x \<sqsubseteq> t" by auto
        have "monotone_on A (\<sqsubseteq>) (\<unlhd>) f"
          by (auto intro!: continuous_imp_monotone_on[OF f] pair_well_related)
        from monotone_onD[OF this] xD DA tA xt
        show "f x \<unlhd> f t" by (auto simp: bound_empty extreme_def)
      next
        fix b assume "bound (f ` D) (\<unlhd>) b" and bB: "b \<in> B"
        with dD have fdb: "f d \<unlhd> b" by auto
        from Dt exbd have dt: "d \<sim> t" by (auto simp: extreme_bound_iff)
        from dD DA have dA: "d \<in> A" by auto
        with extreme_bound_sym_trans[OF _ extreme_bound_singleton[OF dA] dt tA]
        have "extreme_bound A (\<sqsubseteq>) {d} t" by auto
        from dD DA f[THEN continuousD, OF well_related_singleton_refl _ _ this]
        have exfdt: "extreme_bound B (\<unlhd>) {f d} (f t)" by auto
        from fdb bB exfdt show "f t \<unlhd> b" by auto
      qed
    qed
  next
    case inf: False
    from D.Iwamura[OF dir inf]
    obtain I where Imono: "monotone_on D (\<preceq>\<^bsub>D\<^esub>) (\<subseteq>) I"
      and Icard: "\<forall>a \<in> D. |I a| <o |D|"
      and Idir: "\<forall>a \<in> D. directed_set (I a) (\<sqsubseteq>)"
      and Irange: "\<Union> (I ` D) = D"
      by auto
    have "\<forall>d \<in> D. \<exists>s. extreme_bound A (\<sqsubseteq>) (I d) s"
    proof safe
      fix d assume dD: "d \<in> D"
      with Irange DA have IdA: "I d \<subseteq> A" by auto
      with IH Icard Idir dD range DA
      show "\<exists>s. extreme_bound A (\<sqsubseteq>) (I d) s" by auto
    qed
    from bchoice[OF this]
    obtain s where s: "\<And>d. d \<in> D \<Longrightarrow> extreme_bound A (\<sqsubseteq>) (I d) (s d)" by auto
    then have sDA: "s ` D \<subseteq> A" by auto
    have smono: "monotone_on D (\<preceq>\<^bsub>D\<^esub>) (\<sqsubseteq>) s"
    proof (intro monotone_onI)
      fix x y assume xD: "x \<in> D" and yD: "y \<in> D" and xy: "x \<preceq>\<^bsub>D\<^esub> y"
      show "s x \<sqsubseteq> s y"
        apply (rule extreme_bound_subset[OF monotone_onD[OF Imono xD yD xy], of A])
        using s xD yD by auto
    qed
    from well_order_of.monotone_image_well_related[OF this]
    have wsD: "well_related_set (s ` D) (\<sqsubseteq>)".
    from inf have sD0: "nonempty (s ` D) (\<sqsubseteq>)" by auto
    from completeD[OF comp sDA] wsD sD0
    obtain x where x: "extreme_bound A (\<sqsubseteq>) (s ` D) x" by auto
    show ?thesis
    proof (intro conjI allI impI exI[of _ x])
      show Dx: "extreme_bound A (\<sqsubseteq>) D x"
      proof (intro smono exI[of _ x] extreme_boundI)
        from x show xA: "x \<in> A" by auto
        fix d assume dD: "d \<in> D"
        with Irange obtain d' where d'D: "d' \<in> D" and "d \<in> I d'" by auto
        with s have 1: "d \<sqsubseteq> s d'" by auto
        from x d'D have 2: "\<dots> \<sqsubseteq> x" by auto
        from trans[OF 1 2] show "d \<sqsubseteq> x" using dD sDA d'D DA xA by auto
      next
        fix b assume bA: "b \<in> A" and Db: "bound D (\<sqsubseteq>) b"
        have "bound (s ` D) (\<sqsubseteq>) b"
        proof safe
          fix d assume dD: "d \<in> D"
          from dD Db Irange have "bound (I d) (\<sqsubseteq>) b" by auto
          with s dD bA show "s d \<sqsubseteq> b" by auto
        qed
        with x bA show "x \<sqsubseteq> b" by auto
      qed
      assume f: "well_related_set-continuous A (\<sqsubseteq>) B (\<unlhd>) f"
        and Dt: "extreme_bound A (\<sqsubseteq>) D t" and D0: "D \<noteq> {}"
      from Dt have tA: "t \<in> A" by auto
      have fmono: "monotone_on A (\<sqsubseteq>) (\<unlhd>) f"
        by (auto intro!:continuous_imp_monotone_on[OF f] pair_well_related)
      show "extreme_bound B (\<unlhd>) (f ` D) (f t)"
      proof (safe intro!: extreme_boundI)
        from f tA show "f t \<in> B" by auto
        fix d assume dD: "d \<in> D"
        from dD Dt have dt: "d \<sqsubseteq> t" by auto
        from dD Dt DA show "f d \<unlhd> f t" by (auto intro!: monotone_onD[OF fmono])
      next
        fix b assume fDb: "bound (f ` D) (\<unlhd>) b" and bB: "b \<in> B"
        from Dx Dt have "x \<sim> t" by (auto intro!: sympartpI elim!: extreme_boundE)
        with extreme_bound_sym_trans[OF sDA x this tA]
        have "extreme_bound A (\<sqsubseteq>) (s ` D) t" by auto
        from f[THEN continuousD, OF wsD _ sDA this] D0
        have ft: "extreme_bound B (\<unlhd>) (f ` s ` D) (f t)" by auto
        have "bound (f ` s ` D) (\<unlhd>) b"
        proof (safe)
          fix d assume dD: "d \<in> D"
          from Irange dD have IdD: "I d \<subseteq> D" by auto
          with DA have IdA: "I d \<subseteq> A" by auto
          from directed_setD[OF Idir[rule_format, OF dD], of "{}"]
          have Idne: "I d \<noteq> {}" by auto
          have fsd: "extreme_bound B (\<unlhd>) (f ` I d) (f (s d))"
            apply (rule IH2[OF _ _ IdA f Idne s[OF dD]])
            using Icard Idir dD by auto
          from IdD have "f ` I d \<subseteq> f ` D" by auto
          from bound_subset[OF this fDb] fsd bB
          show "f (s d) \<unlhd> b" by auto
        qed
        with ft bB show "f t \<unlhd> b" by auto
      qed
    qed
  qed
qed

text \<open>The next Theorem corresponds to Proposition 5.9 of \cite{Cohn65}, without antisymmetry 
on $A$.\<close>

theorem (in quasi_ordered_set) well_complete_iff_directed_complete:
  "(nonempty \<sqinter> well_related_set)-complete A (\<sqsubseteq>) \<longleftrightarrow> directed_set-complete A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  show "?l \<Longrightarrow> ?r"
    by (auto intro!: completeI dest!: directed_completeness_lemma(1))
  assume r: ?r
  show ?l
    apply (rule complete_subclass[OF r])
    using well_related_set.directed_set
    by auto
qed

text \<open>The next Theorem corresponds to Corollary 3 of \cite{markowsky76} without any assumptions on the codomain 
$B$ and without antisymmetry on the domain $A$.\<close>

theorem (in quasi_ordered_set)
  fixes leB (infix "\<unlhd>" 50)
  assumes comp: "(nonempty \<sqinter> well_related_set)-complete A (\<sqsubseteq>)"
  shows "well_related_set-continuous A (\<sqsubseteq>) B (\<unlhd>) f \<longleftrightarrow> directed_set-continuous A (\<sqsubseteq>) B (\<unlhd>) f"
    (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  assume l: ?l
  show ?r
    using continuous_carrierD[OF l]
    using directed_completeness_lemma(2)[OF comp _ _ l]
    by (auto intro!: continuousI)
next
  assume r: ?r
  show ?l
    apply (rule continuous_subclass[OF _ r])
    using well_related_set.directed_set by auto
qed

end