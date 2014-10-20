theory Discrete_Time_Markov_Chain
  imports
    Probability
    "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
    "../Coinductive/Coinductive_Nat"
begin

lemma emeasure_measure_pmf_finite:
  "finite S \<Longrightarrow> emeasure (measure_pmf M) S = (\<Sum>s\<in>S. pmf M s)"
  by (subst emeasure_eq_setsum_singleton) (auto simp: emeasure_pmf_single)

lemma mono_les:
  fixes s S N and l1 l2 :: "'a \<Rightarrow> real" and K :: "'a \<Rightarrow> 'a pmf"
  defines "\<Delta> x \<equiv> l2 x - l1 x"
  assumes s: "s \<in> S" and S: "(\<Union>s\<in>S. K s) \<subseteq> S \<union> N"
  assumes int_l1[simp]: "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l1"
  assumes int_l2[simp]: "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l2"
  assumes to_N: "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>N. (s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes l1: "\<And>s. s \<in> S \<Longrightarrow> (\<integral>t. l1 t \<partial>K s) + c s \<le> l1 s"
  assumes l2: "\<And>s. s \<in> S \<Longrightarrow> l2 s \<le> (\<integral>t. l2 t \<partial>K s) + c s"
  assumes eq: "\<And>s. s \<in> N \<Longrightarrow> l2 s \<le> l1 s"
  assumes finitary: "finite (\<Delta> ` (S\<union>N))"
  shows "l2 s \<le> l1 s"
proof -
  def M \<equiv> "{s\<in>S\<union>N. \<forall>t\<in>S\<union>N. \<Delta> t \<le> \<Delta> s}"

  have [simp]: "\<And>s. s\<in>S \<Longrightarrow> integrable (K s) \<Delta>"
    by (simp add: \<Delta>_def[abs_def])

  have M_unqiue: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> M \<Longrightarrow> \<Delta> s = \<Delta> t"
    by (auto intro!: antisym simp: M_def)
  have M1: "\<And>s. s \<in> M \<Longrightarrow> s \<in> S \<union> N"
    by (auto simp: M_def)
  have M2: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> S \<union> N \<Longrightarrow> \<Delta> t \<le> \<Delta> s"
    by (auto simp: M_def)
  have M3: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> S \<union> N \<Longrightarrow> t \<notin> M \<Longrightarrow> \<Delta> t < \<Delta> s"
    by (auto simp: M_def less_le)

  have N: "\<forall>s\<in>N. \<Delta> s \<le> 0"
    using eq by (simp add: \<Delta>_def)

  { fix s assume s: "s \<in> M" "M \<inter> N = {}"
    then have "s \<in> S - N"
      by (auto dest: M1)
    with to_N[of s] obtain t where "(s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*" and "t \<in> N"
      by (auto simp: M_def)
    from this(1) `s \<in> M` have "\<Delta> s \<le> 0"
    proof (induction rule: converse_rtrancl_induct)
      case (step s s')
      then have s: "s \<in> M" "s \<in> S" "s \<notin> N" and s': "s' \<in> S \<union> N" "s' \<in> K s"
        using S `M \<inter> N = {}` by (auto dest: M1)
      have "s' \<in> M"
      proof (rule ccontr)
        assume "s' \<notin> M"
        with `s \<in> S` s' `s \<in> M`
        have "0 < pmf (K s) s'" "\<Delta> s' < \<Delta> s"
          by (auto simp: pmf_nonneg intro: M2 M3 pmf_positive)

        have "\<Delta> s \<le> ((\<integral>t. l2 t \<partial>K s) + c s) - ((\<integral>t. l1 t \<partial>K s) + c s)"
          unfolding \<Delta>_def using `s \<in> S` `s \<notin> N` by (intro diff_mono l1 l2) auto
        then have "\<Delta> s \<le> (\<integral>s'. \<Delta> s' \<partial>K s)"
          using `s \<in> S` by (simp add: \<Delta>_def)
        also have "\<dots> < (\<integral>s'. \<Delta> s \<partial>K s)"
          using `s' \<in> K s` `\<Delta> s' < \<Delta> s` `s\<in>S` S `s\<in>M`
          by (intro measure_pmf.integral_less_AE[where A="{s'}"])
             (auto simp: emeasure_measure_pmf_finite AE_measure_pmf_iff set_pmf_iff[symmetric] intro!: M2)
        finally show False
          using measure_pmf.prob_space[of "K s"] by simp
      qed
      with step.IH `t\<in>N` N have "\<Delta> s' \<le> 0" "s' \<in> M"
        by auto
      with `s\<in>S` show "\<Delta> s \<le> 0"
        by (force simp: M_def)
    qed (insert N `t\<in>N`, auto) }

  show ?thesis
  proof cases
    assume "M \<inter> N = {}"
    have "Max (\<Delta>`(S\<union>N)) \<in> \<Delta>`(S\<union>N)"
      using `s \<in> S` by (intro Max_in finitary) auto
    then obtain t where "t \<in> S \<union> N" "\<Delta> t = Max (\<Delta>`(S\<union>N))"
      unfolding image_iff by metis
    then have "t \<in> M"
      by (auto simp: M_def finitary intro!: Max_ge)
    have "\<Delta> s \<le> \<Delta> t"
      using `t\<in>M` `s\<in>S` by (auto dest: M2)
    also have "\<Delta> t \<le> 0"
      using `t\<in>M` `M \<inter> N = {}` by fact
    finally show ?thesis
      by (simp add: \<Delta>_def)
  next
    assume "M \<inter> N \<noteq> {}"
    then obtain t where "t \<in> M" "t \<in> N" by auto
    with N `s\<in>S` have "\<Delta> s \<le> 0"
      by (intro order_trans[of "\<Delta> s" "\<Delta> t" 0]) (auto simp: M_def)
    then show ?thesis
      by (simp add: \<Delta>_def)
  qed
qed

lemma unique_les:
  fixes s S N and l1 l2 :: "'a \<Rightarrow> real" and K :: "'a \<Rightarrow> 'a pmf"
  defines "\<Delta> x \<equiv> l2 x - l1 x"
  assumes s: "s \<in> S" and S: "(\<Union>s\<in>S. K s) \<subseteq> S \<union> N"
  assumes "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l1"
  assumes "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l2"
  assumes "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>N. (s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes "\<And>s. s \<in> S \<Longrightarrow> l1 s = (\<integral>t. l1 t \<partial>K s) + c s"
  assumes "\<And>s. s \<in> S \<Longrightarrow> l2 s = (\<integral>t. l2 t \<partial>K s) + c s"
  assumes "\<And>s. s \<in> N \<Longrightarrow> l2 s = l1 s"
  assumes 1: "finite (\<Delta> ` (S\<union>N))"
  shows "l2 s = l1 s"
proof -
  have "finite ((\<lambda>x. l2 x - l1 x) ` (S\<union>N))"
    using 1 by (auto simp: \<Delta>_def[abs_def])
  moreover then have "finite (uminus ` (\<lambda>x. l2 x - l1 x) ` (S\<union>N))"
    by auto
  ultimately show ?thesis
    using assms
    by (intro antisym mono_les[of s S K N l2 l1 c] mono_les[of s S K N l1 l2 c])
       (auto simp: image_comp comp_def)
qed

lemma countable_reachable: "countable ((SIGMA s:UNIV. set_pmf (K s))\<^sup>* `` {s})"
  by (auto intro!: countable_rtrancl countable_set_pmf simp: Sigma_Image)

lemma measurable_compose_countable':
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f i x) \<in> measurable M N"
  and g: "g \<in> measurable M (count_space I)" and I: "countable I"
  shows "(\<lambda>x. f (g x) x) \<in> measurable M N"
  unfolding measurable_def
proof safe
  fix x assume "x \<in> space M" then show "f (g x) x \<in> space N"
    using measurable_space[OF f] g[THEN measurable_space] by auto
next
  fix A assume A: "A \<in> sets N"
  have "(\<lambda>x. f (g x) x) -` A \<inter> space M = (\<Union>i\<in>I. (g -` {i} \<inter> space M) \<inter> (f i -` A \<inter> space M))"
    using measurable_space[OF g] by auto
  also have "\<dots> \<in> sets M" using f[THEN measurable_sets, OF _ A] g[THEN measurable_sets]
    by (auto intro!: sets.countable_UN' measurable_sets I)
  finally show "(\<lambda>x. f (g x) x) -` A \<inter> space M \<in> sets M" .
qed

lemma mult_indicator_cong: 
  fixes f g :: "'a \<Rightarrow> ereal"
  shows "(x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> f x * indicator A x = g x * indicator A x"
  by (simp split: split_indicator)

lemma emeasure_Collect_eq_AE:
  "AE x in M. P x \<longleftrightarrow> Q x \<Longrightarrow> Measurable.pred M Q \<Longrightarrow> Measurable.pred M P \<Longrightarrow>
   emeasure M {x\<in>space M. P x} = emeasure M {x\<in>space M. Q x}"
   by (intro emeasure_eq_AE) auto

definition "HLD s = holds (\<lambda>x. x \<in> s)"

abbreviation HLD_nxt (infixr "\<cdot>" 65) where
  "s \<cdot> P \<equiv> HLD s aand nxt P"

lemma HLD_iff: "HLD s \<omega> \<longleftrightarrow> shd \<omega> \<in> s"
  by (simp add: HLD_def)

lemma HLD_Stream[simp]: "HLD X (x ## \<omega>) \<longleftrightarrow> x \<in> X"
  by (simp add: HLD_iff)

lemma measurable_lfp[consumes 1, case_names continuity step]:
  assumes "P M"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "Measurable.pred M (lfp F)"
proof -
  { fix i from `P M` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>x. False) x)"
      by (induct i arbitrary: M) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>x. False) x)"
    by measurable
  also have "(\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>x. False) x) = (SUP i. (F ^^ i) bot)"
    by (auto simp add: bot_fun_def)
  also have "\<dots> = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_gfp[consumes 1, case_names continuity step]:
  assumes "P M"
  assumes "Order_Continuity.down_continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "Measurable.pred M (gfp F)"
proof -
  { fix i from `P M` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>x. True) x)"
      by (induct i arbitrary: M) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>x. True) x)"
    by measurable
  also have "(\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>x. True) x) = (INF i. (F ^^ i) top)"
    by (auto simp add: top_fun_def)
  also have "\<dots> = gfp F"
    by (rule down_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_lfp2[consumes 1, case_names continuity step]:
  assumes "P M s"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>M A s. P M s \<Longrightarrow> (\<And>N t. P N t \<Longrightarrow> Measurable.pred N (A t)) \<Longrightarrow> Measurable.pred M (F A s)"
  shows "Measurable.pred M (lfp F s)"
proof -
  { fix i from `P M s` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>t x. False) s x)"
      by (induct i arbitrary: M s) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>t x. False) s x)"
    by measurable
  also have "(\<lambda>x. \<exists>i. (F ^^ i) (\<lambda>t x. False) s x) = (SUP i. (F ^^ i) bot) s"
    by (auto simp add: bot_fun_def)
  also have "(SUP i. (F ^^ i) bot) = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_gfp2[consumes 1, case_names continuity step]:
  assumes "P M s"
  assumes "Order_Continuity.down_continuous F"
  assumes *: "\<And>M A s. P M s \<Longrightarrow> (\<And>N t. P N t \<Longrightarrow> Measurable.pred N (A t)) \<Longrightarrow> Measurable.pred M (F A s)"
  shows "Measurable.pred M (gfp F s)"
proof -
  { fix i from `P M s` have "Measurable.pred M (\<lambda>x. (F ^^ i) (\<lambda>t x. True) s x)"
      by (induct i arbitrary: M s) (auto intro!: *) }
  then have "Measurable.pred M (\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>t x. True) s x)"
    by measurable
  also have "(\<lambda>x. \<forall>i. (F ^^ i) (\<lambda>t x. True) s x) = (INF i. (F ^^ i) top) s"
    by (auto simp add: top_fun_def)
  also have "(INF i. (F ^^ i) top) = gfp F"
    by (rule down_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

lemma measurable_enat_coinduct:
  fixes f :: "'a \<Rightarrow> enat"
  assumes "R f"
  assumes *: "\<And>f. R f \<Longrightarrow> \<exists>g h i P. R g \<and> f = (\<lambda>x. if P x then h x else eSuc (g (i x))) \<and> 
    Measurable.pred M P \<and>
    i \<in> measurable M M \<and>
    h \<in> measurable M (count_space UNIV)"
  shows "f \<in> measurable M (count_space UNIV)"
proof (simp add: measurable_count_space_eq2_countable, rule )
  fix a :: enat
  have "f -` {a} \<inter> space M = {x\<in>space M. f x = a}"
    by auto
  { fix i :: nat
    from `R f` have "Measurable.pred M (\<lambda>x. f x = enat i)"
    proof (induction i arbitrary: f)
      case 0
      from *[OF this] obtain g h i P
        where f: "f = (\<lambda>x. if P x then h x else eSuc (g (i x)))" and
          [measurable]: "Measurable.pred M P" "i \<in> measurable M M" "h \<in> measurable M (count_space UNIV)"
        by auto
      have "Measurable.pred M (\<lambda>x. P x \<and> h x = 0)"
        by measurable
      also have "(\<lambda>x. P x \<and> h x = 0) = (\<lambda>x. f x = enat 0)"
        by (auto simp: f zero_enat_def[symmetric])
      finally show ?case .
    next
      case (Suc n)
      from *[OF Suc.prems] obtain g h i P
        where f: "f = (\<lambda>x. if P x then h x else eSuc (g (i x)))" and "R g" and
          M[measurable]: "Measurable.pred M P" "i \<in> measurable M M" "h \<in> measurable M (count_space UNIV)"
        by auto
      have "(\<lambda>x. f x = enat (Suc n)) =
        (\<lambda>x. (P x \<longrightarrow> h x = enat (Suc n)) \<and> (\<not> P x \<longrightarrow> g (i x) = enat n))"
        by (auto simp: f zero_enat_def[symmetric] eSuc_enat[symmetric])
      also have "Measurable.pred M \<dots>"
        by (intro pred_intros_logic measurable_compose[OF M(2)] Suc `R g`) measurable
      finally show ?case .
    qed
    then have "f -` {enat i} \<inter> space M \<in> sets M"
      by (simp add: pred_def Int_def conj_commute) }
  note fin = this
  show "f -` {a} \<inter> space M \<in> sets M"
  proof (cases a)
    case infinity
    then have "f -` {a} \<inter> space M = space M - (\<Union>n. f -` {enat n} \<inter> space M)"
      by auto
    also have "\<dots> \<in> sets M"
      by (intro sets.Diff sets.top sets.Un sets.countable_UN) (auto intro!: fin)
    finally show ?thesis .
  qed (simp add: fin)
qed

lemma measurable_alw[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (alw P)"
  unfolding alw_def
  by (coinduction rule: measurable_gfp) (auto simp: Order_Continuity.down_continuous_def)

lemma measurable_ev[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (ev P)"
  unfolding ev_def
  by (coinduction rule: measurable_lfp) (auto simp: Order_Continuity.continuous_def)

lemma measurable_holds [measurable]: "Measurable.pred M P \<Longrightarrow> Measurable.pred (stream_space M) (holds P)"
  unfolding holds.simps[abs_def]
  by (rule measurable_compose[OF measurable_shd]) simp

lemma not_alw_iff: "\<not> (alw P \<omega>) \<longleftrightarrow> ev (not P) \<omega>"
  using not_alw[of P] by (simp add: fun_eq_iff)

lemma not_ev_iff: "\<not> (ev P \<omega>) \<longleftrightarrow> alw (not P) \<omega>"
  using not_alw_iff[of "not P" \<omega>, symmetric]  by simp

lemma streamsE: "s \<in> streams A \<Longrightarrow> (shd s \<in> A \<Longrightarrow> stl s \<in> streams A \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule streams.cases) simp_all

lemma Stream_image: "x ## y \<in> (op ## x') ` Y \<longleftrightarrow> x = x' \<and> y \<in> Y"
  by auto

lemma ev_induct_strong[consumes 1, case_names base step]:
  "ev \<phi> x \<Longrightarrow> (\<And>xs. \<phi> xs \<Longrightarrow> P xs) \<Longrightarrow> (\<And>xs. ev \<phi> (stl xs) \<Longrightarrow> \<not> \<phi> xs \<Longrightarrow> P (stl xs) \<Longrightarrow> P xs) \<Longrightarrow> P x"
  by (induct rule: ev.induct) auto

lemma alw_coinduct[consumes 1, case_names alw stl]:
  "X x \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<phi> x) \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<not> alw \<phi> (stl x) \<Longrightarrow> X (stl x)) \<Longrightarrow> alw \<phi> x"
  using alw.coinduct[of X x \<phi>] by auto

declare alw.cases[elim]
declare ev.intros[intro]

lemma ev_Stream: "ev P (x ## s) \<longleftrightarrow> P (x ## s) \<or> ev P s"
  by (auto elim: ev.cases)

lemma alw_ev_imp_ev_alw:
  assumes "alw (ev P) \<omega>" shows "ev (P aand alw (ev P)) \<omega>"
proof -
  have "ev P \<omega>" using assms by auto
  from this assms show ?thesis
    by induct auto
qed

lemma ev_False: "ev (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
proof
  assume "ev (\<lambda>x. False) \<omega>" then show False
    by induct auto
qed auto

lemma alw_False: "alw (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
  by auto

lemma ev_iff_sdrop: "ev P \<omega> \<longleftrightarrow> (\<exists>m. P (sdrop m \<omega>))"
proof safe
  assume "ev P \<omega>" then show "\<exists>m. P (sdrop m \<omega>)"
    by (induct rule: ev_induct_strong) (auto intro: exI[of _ 0] exI[of _ "Suc n" for n])
next
  fix m assume "P (sdrop m \<omega>)" then show "ev P \<omega>"
    by (induct m arbitrary: \<omega>) auto
qed

lemma alw_iff_sdrop: "alw P \<omega> \<longleftrightarrow> (\<forall>m. P (sdrop m \<omega>))"
proof safe
  fix m assume "alw P \<omega>" then show "P (sdrop m \<omega>)"
    by (induct m arbitrary: \<omega>) auto
next
  assume "\<forall>m. P (sdrop m \<omega>)" then show "alw P \<omega>"
    by (coinduction arbitrary: \<omega>) (auto elim: allE[of _ 0] allE[of _ "Suc n" for n])
qed

lemma infinite_iff_alw_ev: "infinite {m. P (\<omega> !! m)} \<longleftrightarrow> alw (ev (holds P)) \<omega>"
  unfolding infinite_nat_iff_unbounded_le alw_iff_sdrop ev_iff_sdrop
  by simp (metis le_Suc_ex le_add1)

lemma alw_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "alw P (f s) \<longleftrightarrow> alw (\<lambda>x. P (f x)) s"
proof
  assume "alw P (f s)" then show "alw (\<lambda>x. P (f x)) s"
    by (coinduction arbitrary: s rule: alw_coinduct)
       (auto simp: stl)
next
  assume "alw (\<lambda>x. P (f x)) s" then show "alw P (f s)"
    by (coinduction arbitrary: s rule: alw_coinduct) (auto simp: stl[symmetric])
qed

lemma ev_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "ev P (f s) \<longleftrightarrow> ev (\<lambda>x. P (f x)) s"
proof
  assume "ev P (f s)" then show "ev (\<lambda>x. P (f x)) s"
    by (induction "f s" arbitrary: s) (auto simp: stl)
next
  assume "ev (\<lambda>x. P (f x)) s" then show "ev P (f s)"
    by induction (auto simp: stl[symmetric])
qed

lemma alw_smap: "alw P (smap f s) \<longleftrightarrow> alw (\<lambda>x. P (smap f x)) s"
  by (rule alw_inv) simp

lemma ev_smap: "ev P (smap f s) \<longleftrightarrow> ev (\<lambda>x. P (smap f x)) s"
  by (rule ev_inv) simp

lemma alw_cong:
  assumes P: "alw P \<omega>" and eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "alw Q1 \<omega> \<longleftrightarrow> alw Q2 \<omega>"
proof -
  from eq have "(alw P aand Q1) = (alw P aand Q2)" by auto
  then have "alw (alw P aand Q1) \<omega> = alw (alw P aand Q2) \<omega>" by auto
  with P show "alw Q1 \<omega> \<longleftrightarrow> alw Q2 \<omega>"
    by (simp add: alw_aand)
qed

lemma ev_cong:
  assumes P: "alw P \<omega>" and eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "ev Q1 \<omega> \<longleftrightarrow> ev Q2 \<omega>"
proof -
  from P have "alw (\<lambda>xs. Q1 xs \<longrightarrow> Q2 xs) \<omega>" by (rule alw_mono) (simp add: eq)
  moreover from P have "alw (\<lambda>xs. Q2 xs \<longrightarrow> Q1 xs) \<omega>" by (rule alw_mono) (simp add: eq)
  moreover note ev_alw_impl[of Q1 \<omega> Q2] ev_alw_impl[of Q2 \<omega> Q1]
  ultimately show "ev Q1 \<omega> \<longleftrightarrow> ev Q2 \<omega>"
    by auto
qed

lemma smap_ctr: "smap f s = x ## s' \<longleftrightarrow> f (shd s) = x \<and> smap f (stl s) = s'"
  by (cases s) simp

lemma alwD: "alw P x \<Longrightarrow> P x"
  by auto

lemma alw_alwD: "alw P \<omega> \<Longrightarrow> alw (alw P) \<omega>"
  by simp

lemma alw_ev_stl: "alw (ev P) (stl \<omega>) \<longleftrightarrow> alw (ev P) \<omega>"
  by (auto intro: alw.intros)

lemma holds_Stream: "holds P (x ## s) \<longleftrightarrow> P x"
  by simp

lemma holds_eq1[simp]: "holds (op = x) = HLD {x}"
  by rule (auto simp: HLD_iff)

lemma holds_eq2[simp]: "holds (\<lambda>y. y = x) = HLD {x}"
  by rule (auto simp: HLD_iff)

lemma not_holds_eq[simp]: "holds (- op = x) = not (HLD {x})"
  by rule (auto simp: HLD_iff)

lemma measurable_hld[measurable]: assumes [measurable]: "t \<in> sets M" shows "Measurable.pred (stream_space M) (HLD t)"
  unfolding HLD_def by measurable

text {* Strong until *}

inductive suntil (infix "suntil" 60) for \<phi> \<psi> where
  base: "\<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"
| step: "\<phi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) (stl \<omega>) \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"

inductive_simps suntil_Stream: "(\<phi> suntil \<psi>) (x ## s)"

lemma ev_suntil: "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega>"
  by (induct rule: suntil.induct) (auto intro: ev.intros)

lemma suntil_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "(P suntil Q) (f s) \<longleftrightarrow> ((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s"
proof
  assume "(P suntil Q) (f s)" then show "((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s"
    by (induction "f s" arbitrary: s) (auto simp: stl intro: suntil.intros)
next
  assume "((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s" then show "(P suntil Q) (f s)"
    by induction (auto simp: stl[symmetric] intro: suntil.intros)
qed

lemma suntil_smap: "(P suntil Q) (smap f s) \<longleftrightarrow> ((\<lambda>x. P (smap f x)) suntil (\<lambda>x. Q (smap f x))) s"
  by (rule suntil_inv) simp

lemma hld_smap: "HLD x (smap f s) = holds (\<lambda>y. f y \<in> x) s"
  by (simp add: HLD_def)

lemma suntil_mono:
  assumes eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<Longrightarrow> Q2 \<omega>" "\<And>\<omega>. P \<omega> \<Longrightarrow> R1 \<omega> \<Longrightarrow> R2 \<omega>"
  assumes *: "(Q1 suntil R1) \<omega>" "alw P \<omega>" shows "(Q2 suntil R2) \<omega>"
  using * by induct (auto intro: eq suntil.intros)

lemma suntil_cong:
  "alw P \<omega> \<Longrightarrow> (\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>) \<Longrightarrow> (\<And>\<omega>. P \<omega> \<Longrightarrow> R1 \<omega> \<longleftrightarrow> R2 \<omega>) \<Longrightarrow>
    (Q1 suntil R1) \<omega> \<longleftrightarrow> (Q2 suntil R2) \<omega>"
  using suntil_mono[of P Q1 Q2 R1 R2 \<omega>] suntil_mono[of P Q2 Q1 R2 R1 \<omega>] by auto

lemma ev_suntil_iff: "ev (P suntil Q) \<omega> \<longleftrightarrow> ev Q \<omega>"
proof
  assume "ev (P suntil Q) \<omega>" then show "ev Q \<omega>"
   by induct (auto dest: ev_suntil)
next
  assume "ev Q \<omega>" then show "ev (P suntil Q) \<omega>"
    by induct (auto intro: suntil.intros)
qed

lemma true_suntil: "((\<lambda>_. True) suntil P) = ev P"
  by (simp add: suntil_def ev_def)

lemma suntil_lfp: "(\<phi> suntil \<psi>) = lfp (\<lambda>P s. \<psi> s \<or> (\<phi> s \<and> P (stl s)))"
  by (simp add: suntil_def)

lemma sfilter_P[simp]: "P (shd s) \<Longrightarrow> sfilter P s = shd s ## sfilter P (stl s)"
  using sfilter_Stream[of P "shd s" "stl s"] by simp

lemma sfilter_not_P[simp]: "\<not> P (shd s) \<Longrightarrow> sfilter P s = sfilter P (stl s)"
  using sfilter_Stream[of P "shd s" "stl s"] by simp

lemma sfilter_eq: 
  assumes "ev (holds P) s"
  shows "sfilter P s = x ## s' \<longleftrightarrow>
    P x \<and> (not (holds P) suntil (HLD {x} aand nxt (\<lambda>s. sfilter P s = s'))) s"
  using assms
  by (induct rule: ev_induct_strong)
     (auto simp add: HLD_iff intro: suntil.intros elim: suntil.cases)

lemma sfilter_streams:
  "alw (ev (holds P)) \<omega> \<Longrightarrow> \<omega> \<in> streams A \<Longrightarrow> sfilter P \<omega> \<in> streams {x\<in>A. P x}"
proof (coinduction arbitrary: \<omega>)
  case (streams \<omega>)
  then have "ev (holds P) \<omega>" by blast
  from this streams show ?case
    by (induct rule: ev_induct_strong) (auto elim: streamsE)
qed

lemma alw_sfilter:
  assumes *: "alw (ev (holds P)) s"
  shows "alw Q (sfilter P s) \<longleftrightarrow> alw (\<lambda>x. Q (sfilter P x)) s"
proof
  assume "alw Q (sfilter P s)" with * show "alw (\<lambda>x. Q (sfilter P x)) s"
  proof (coinduction arbitrary: s rule: alw_coinduct)
    case (stl s) 
    then have "ev (holds P) s"
      by blast
    from this stl show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
next
  assume "alw (\<lambda>x. Q (sfilter P x)) s" with * show "alw Q (sfilter P s)"
  proof (coinduction arbitrary: s rule: alw_coinduct)
    case (stl s) 
    then have "ev (holds P) s"
      by blast
    from this stl show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
qed

lemma ev_sfilter:
  assumes *: "alw (ev (holds P)) s"
  shows "ev Q (sfilter P s) \<longleftrightarrow> ev (\<lambda>x. Q (sfilter P x)) s"
proof
  assume "ev Q (sfilter P s)" from this * show "ev (\<lambda>x. Q (sfilter P x)) s"
  proof (induction "sfilter P s" arbitrary: s rule: ev_induct_strong)
    case (step s)
    then have "ev (holds P) s"
      by blast
    from this step show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
next
  assume "ev (\<lambda>x. Q (sfilter P x)) s" then show "ev Q (sfilter P s)"
  proof (induction rule: ev_induct_strong)
    case (step s) then show ?case
      by (cases "P (shd s)") auto
  qed auto
qed

lemma holds_sfilter:
  assumes "ev (holds Q) s" shows "holds P (sfilter Q s) \<longleftrightarrow> (not (holds Q) suntil (holds (Q aand P))) s"
proof
  assume "holds P (sfilter Q s)" with assms show "(not (holds Q) suntil (holds (Q aand P))) s"
    by (induct rule: ev_induct_strong) (auto intro: suntil.intros)
next
  assume "(not (holds Q) suntil (holds (Q aand P))) s" then show "holds P (sfilter Q s)"
    by induct auto
qed

lemma funpow_mono:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  shows "mono f \<Longrightarrow> A \<le> B \<Longrightarrow> (f ^^ n) A \<le> (f ^^ n) B"
  by (induct n arbitrary: A B)
     (auto simp del: funpow.simps(2) simp add: funpow_Suc_right mono_def)

lemma funpow_increasing:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  shows "m \<le> n \<Longrightarrow> mono f \<Longrightarrow> (f ^^ n) \<top> \<le> (f ^^ m) \<top>"
  by (induct rule: inc_induct)
     (auto simp del: funpow.simps(2) simp add: funpow_Suc_right
           intro: order_trans[OF _ funpow_mono])

lemma div_eq_zero_iff: fixes a b :: nat shows "a div b = 0 \<longleftrightarrow> a < b \<or> b = 0"
  by (metis Divides.div_less Divides.div_positive div_by_0 gr0I less_numeral_extra(3) not_less)

lemma AE_ball_countable: 
  assumes [intro]: "countable X"
  shows "(AE x in M. \<forall>y\<in>X. P x y) \<longleftrightarrow> (\<forall>y\<in>X. AE x in M. P x y)"
proof
  assume "\<forall>y\<in>X. AE x in M. P x y"
  from this[unfolded eventually_ae_filter Bex_def, THEN bchoice]
  obtain N where N: "\<And>y. y \<in> X \<Longrightarrow> N y \<in> null_sets M" "\<And>y. y \<in> X \<Longrightarrow> {x\<in>space M. \<not> P x y} \<subseteq> N y"
    by auto
  have "{x\<in>space M. \<not> (\<forall>y\<in>X. P x y)} \<subseteq> (\<Union>y\<in>X. {x\<in>space M. \<not> P x y})"
    by auto
  also have "\<dots> \<subseteq> (\<Union>y\<in>X. N y)"
    using N by auto
  finally have "{x\<in>space M. \<not> (\<forall>y\<in>X. P x y)} \<subseteq> (\<Union>y\<in>X. N y)" .
  moreover from N have "(\<Union>y\<in>X. N y) \<in> null_sets M"
    by (intro null_sets_UN') auto
  ultimately show "AE x in M. \<forall>y\<in>X. P x y"
    unfolding eventually_ae_filter by auto
qed auto

lemma (in prob_space) ae_filter_bot: "ae_filter M \<noteq> bot"
  by (simp add: trivial_limit_def)

lemma measurable_nxt[measurable (raw)]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (nxt P)"
  unfolding nxt.simps[abs_def] by simp

lemma emeasure_lfp[consumes 1, case_names cont measurable]:
  assumes "P M"
  assumes cont: "Order_Continuity.continuous F"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "emeasure M {x\<in>space M. lfp F x} = (SUP i. emeasure M {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
proof -
  have "emeasure M {x\<in>space M. lfp F x} = emeasure M (\<Union>i. {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
    using continuous_lfp[OF cont] by (auto simp add: bot_fun_def intro!: arg_cong2[where f=emeasure])
  moreover { fix i from `P M` have "{x\<in>space M. (F ^^ i) (\<lambda>x. False) x} \<in> sets M"
    by (induct i arbitrary: M) (auto simp add: pred_def[symmetric] intro: *) }
  moreover have "incseq (\<lambda>i. {x\<in>space M. (F ^^ i) (\<lambda>x. False) x})"
  proof (rule incseq_SucI)
    fix i
    have "(F ^^ i) (\<lambda>x. False) \<le> (F ^^ (Suc i)) (\<lambda>x. False)"
    proof (induct i)
      case 0 show ?case by (simp add: le_fun_def)
    next
      case Suc thus ?case using monoD[OF continuous_mono[OF cont] Suc] by auto
    qed
    then show "{x \<in> space M. (F ^^ i) (\<lambda>x. False) x} \<subseteq> {x \<in> space M. (F ^^ Suc i) (\<lambda>x. False) x}"
      by auto
  qed
  ultimately show ?thesis
    by (subst SUP_emeasure_incseq) auto
qed

lemma emeasure_Collect_distr:
  assumes X[measurable]: "X \<in> measurable M N" "Measurable.pred N P"
  shows "emeasure (distr M N X) {x\<in>space N. P x} = emeasure M {x\<in>space M. P (X x)}"
  by (subst emeasure_distr)
     (auto intro!: arg_cong2[where f=emeasure] X(1)[THEN measurable_space])

lemma measurable_predpow[measurable]:
  assumes "Measurable.pred M T"
  assumes "\<And>Q. Measurable.pred M Q \<Longrightarrow> Measurable.pred M (R Q)"
  shows "Measurable.pred M ((R ^^ n) T)"
  by (induct n) (auto intro: assms)

lemma emeasure_lfp2[consumes 1, case_names cont f measurable]:
  assumes "P M"
  assumes cont: "Order_Continuity.continuous F"
  assumes f: "\<And>M. P M \<Longrightarrow> f \<in> measurable M' M"
  assumes *: "\<And>M A. P M \<Longrightarrow> (\<And>N. P N \<Longrightarrow> Measurable.pred N A) \<Longrightarrow> Measurable.pred M (F A)"
  shows "emeasure M' {x\<in>space M'. lfp F (f x)} = (SUP i. emeasure M' {x\<in>space M'. (F ^^ i) (\<lambda>x. False) (f x)})"
proof (subst (1 2) emeasure_Collect_distr[symmetric, where X=f])
  show "f \<in> measurable M' M"  "f \<in> measurable M' M"
    using f[OF `P M`] by auto
  { fix i show "Measurable.pred M ((F ^^ i) (\<lambda>x. False))"
    using `P M` by (induction i arbitrary: M) (auto intro!: *) }
  show "Measurable.pred M (lfp F)"
    using `P M` cont * by (rule measurable_lfp[of P])

  have "emeasure (distr M' M f) {x \<in> space (distr M' M f). lfp F x} =
    (\<Squnion>i. emeasure (distr M' M f) {x \<in> space (distr M' M f). (F ^^ i) (\<lambda>x. False) x})"
    using `P M`
  proof (coinduction arbitrary: M rule: emeasure_lfp)
    case (measurable A N) then have "\<And>N. P N \<Longrightarrow> Measurable.pred (distr M' N f) A"
      by metis
    then have "\<And>N. P N \<Longrightarrow> Measurable.pred N A"
      by simp
    with `P N`[THEN *] show ?case
      by auto
  qed fact
  then show "emeasure (distr M' M f) {x \<in> space M. lfp F x} =
    (\<Squnion>i. emeasure (distr M' M f) {x \<in> space M. (F ^^ i) (\<lambda>x. False) x})"
   by simp
qed

lemma (in prob_space) indep_eventsI_indep_vars:
  assumes indep: "indep_vars N X I"
  assumes P: "\<And>i. i \<in> I \<Longrightarrow> {x\<in>space (N i). P i x} \<in> sets (N i)"
  shows "indep_events (\<lambda>i. {x\<in>space M. P i (X i x)}) I"
proof -
  have "indep_sets (\<lambda>i. {X i -` A \<inter> space M |A. A \<in> sets (N i)}) I"
    using indep unfolding indep_vars_def2 by auto
  then show ?thesis
    unfolding indep_events_def_alt
  proof (rule indep_sets_mono_sets)
    fix i assume "i \<in> I"
    then have "{{x \<in> space M. P i (X i x)}} = {X i -` {x\<in>space (N i). P i x} \<inter> space M}"
      using indep by (auto simp: indep_vars_def dest: measurable_space)
    also have "\<dots> \<subseteq> {X i -` A \<inter> space M |A. A \<in> sets (N i)}"
      using P[OF `i \<in> I`] by blast
    finally show "{{x \<in> space M. P i (X i x)}} \<subseteq> {X i -` A \<inter> space M |A. A \<in> sets (N i)}" .
  qed
qed                              

lemma infinite_growing:
  fixes X :: "'a :: linorder set"
  assumes "X \<noteq> {}"
  assumes *: "\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>X. y > x"
  shows "infinite X"
proof
  assume "finite X"
  with `X \<noteq> {}` have "Max X \<in> X" "\<forall>x\<in>X. x \<le> Max X"
    by auto
  with *[of "Max X"] show False
    by auto
qed

lemma emeasure_uniform_measure_1:
  "emeasure M S \<noteq> 0 \<Longrightarrow> emeasure M S \<noteq> \<infinity> \<Longrightarrow> emeasure (uniform_measure M S) S = 1"
  by (subst emeasure_uniform_measure)
     (simp_all add: emeasure_nonneg emeasure_neq_0_sets)

lemma nn_integral_divide:
  "0 < c \<Longrightarrow> f \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+x. f x / c \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M) / c"
  unfolding divide_ereal_def
  apply (rule nn_integral_multc)
  apply assumption
  apply (cases c)
  apply auto
  done

lemma nn_integral_uniform_measure:
  assumes f[measurable]: "f \<in> borel_measurable M" and "\<And>x. 0 \<le> f x" and S[measurable]: "S \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x \<partial>uniform_measure M S) = (\<integral>\<^sup>+x. f x * indicator S x \<partial>M) / emeasure M S"
proof -
  { assume "emeasure M S = \<infinity>"
    then have ?thesis
      by (simp add: uniform_measure_def nn_integral_density f) }
  moreover
  { assume [simp]: "emeasure M S = 0"
    then have ae: "AE x in M. x \<notin> S"
      using sets.sets_into_space[OF S]
      by (subst AE_iff_measurable[OF _ refl]) (simp_all add: subset_eq cong: rev_conj_cong)
    from ae have "(\<integral>\<^sup>+ x. indicator S x * f x / 0 \<partial>M) = 0"
      by (subst nn_integral_0_iff_AE) auto
    moreover from ae have "(\<integral>\<^sup>+ x. f x * indicator S x \<partial>M) = 0"
      by (subst nn_integral_0_iff_AE) auto
    ultimately have ?thesis
      by (simp add: uniform_measure_def nn_integral_density f) }
  moreover
  { assume "emeasure M S \<noteq> 0" "emeasure M S \<noteq> \<infinity>"
    moreover then have "0 < emeasure M S"
      by (simp add: emeasure_nonneg less_le)
    ultimately have ?thesis
      unfolding uniform_measure_def
      apply (subst nn_integral_density)
      apply (auto simp: f nn_integral_divide intro!: zero_le_divide_ereal)
      apply (simp add: mult.commute)
      done }
  ultimately show ?thesis by blast
qed

lemma prob_space_restrict_space:
  "S \<in> sets M \<Longrightarrow> emeasure M S = 1 \<Longrightarrow> prob_space (restrict_space M S)"
  by (intro prob_spaceI)
     (simp add: emeasure_restrict_space space_restrict_space)

lemma sets_Collect_restrict_space_iff: 
  assumes "S \<in> sets M"
  shows "{x\<in>space (restrict_space M S). P x} \<in> sets (restrict_space M S) \<longleftrightarrow> {x\<in>space M. x \<in> S \<and> P x} \<in> sets M"
proof -
  have "{x\<in>S. P x} = {x\<in>space M. x \<in> S \<and> P x}"
    using sets.sets_into_space[OF assms] by auto
  then show ?thesis
    by (subst sets_restrict_space_iff) (auto simp add: space_restrict_space assms)
qed

lemma pred_restrict_space:
  assumes "S \<in> sets M"
  shows "Measurable.pred (restrict_space M S) P \<longleftrightarrow> Measurable.pred M (\<lambda>x. x \<in> S \<and> P x)"
  unfolding pred_def sets_Collect_restrict_space_iff[OF assms] ..

lemma streams_sets:
  assumes X[measurable]: "X \<in> sets M" shows "streams X \<in> sets (stream_space M)"
proof -
  have "streams X = {x\<in>space (stream_space M). x \<in> streams X}"
    using streams_mono[OF _ sets.sets_into_space[OF X]] by (auto simp: space_stream_space)
  also have "\<dots> = {x\<in>space (stream_space M). gfp (\<lambda>p x. shd x \<in> X \<and> p (stl x)) x}"
    apply (simp add: set_eq_iff streams_def streamsp_def)
    apply (intro allI conj_cong refl arg_cong2[where f=gfp] ext)
    apply (case_tac xa)
    apply auto
    done
  also have "\<dots> \<in> sets (stream_space M)"
    apply (intro predE)
    apply (coinduction rule: measurable_gfp)
    apply (auto simp: down_continuous_def)
    done
  finally show ?thesis .
qed

lemma measurable_until:
  assumes [measurable]: "Measurable.pred (stream_space M) \<phi>" "Measurable.pred (stream_space M) \<psi>"
  shows "Measurable.pred (stream_space M) (\<phi> until \<psi>)"
  unfolding UNTIL_def
  by (coinduction rule: measurable_gfp) (simp_all add: down_continuous_def fun_eq_iff)

lemma [measurable (raw)]: "X \<in> sets (count_space UNIV)"
  by auto

lemma finite_nat_iff_bounded_le: "finite P \<longleftrightarrow> (\<exists>m::nat. \<forall>n\<ge>m. n \<notin> P)"
  using infinite_nat_iff_unbounded_le[of P] by auto

lemma (in prob_space) borel_0_1_law_AE:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "indep_events (\<lambda>m. {x\<in>space M. P m x}) UNIV" (is "indep_events ?P _")
  shows "(AE x in M. infinite {m. P m x}) \<or> (AE x in M. finite {m. P m x})"
proof -
  have [measurable]: "\<And>m. {x\<in>space M. P m x} \<in> sets M"
    using assms by (auto simp: indep_events_def)
  have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 0 \<or> prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 1"
    by (rule borel_0_1_law) fact
  also have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 0 \<longleftrightarrow> (AE x in M. finite {m. P m x})"
    by (subst prob_eq_0) (simp_all add: Ball_def finite_nat_iff_bounded_le)
  also have "prob (\<Inter>n. \<Union>m\<in>{n..}. ?P m) = 1 \<longleftrightarrow> (AE x in M. infinite {m. P m x})"
    by (subst prob_eq_1) (simp_all add: Bex_def infinite_nat_iff_unbounded_le)
  finally show ?thesis
    by metis
qed

lemma AE_uniform_measure:
  assumes "emeasure M A \<noteq> 0" "emeasure M A < \<infinity>"
  shows "(AE x in uniform_measure M A. P x) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> P x)"
proof -
  have "A \<in> sets M"
    using `emeasure M A \<noteq> 0` by (metis emeasure_notin_sets)
  moreover have "\<And>x. 0 < indicator A x / emeasure M A \<longleftrightarrow> x \<in> A"
    using emeasure_nonneg[of M A] assms
    by (cases "emeasure M A") (auto split: split_indicator simp: one_ereal_def)
  ultimately show ?thesis
    unfolding uniform_measure_def by (simp add: AE_density)
qed

lemma (in prob_space) indep_eventsI:
  "(\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets M) \<Longrightarrow> (\<And>J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow> prob (\<Inter>i\<in>J. F i) = (\<Prod>i\<in>J. prob (F i))) \<Longrightarrow> indep_events F I"
  by (auto simp: indep_events_def)

lemma case_same: "(case siterate f x of y ## s \<Rightarrow> g y s) = g x (siterate f (f x))"
  by (subst siterate.ctr) simp

lemma (in product_prob_space) AE_component: "i \<in> I \<Longrightarrow> AE x in M i. P x \<Longrightarrow> AE x in PiM I M. P (x i)"
  apply (rule AE_distrD[of "\<lambda>\<omega>. \<omega> i" "PiM I M" "M i" P])
  apply simp
  apply (subst PiM_component)
  apply simp_all
  done

lemma measurable_pred_countable[measurable (raw)]:
  assumes "countable X"
  shows 
    "(\<And>i. i \<in> X \<Longrightarrow> Measurable.pred M (\<lambda>x. P x i)) \<Longrightarrow> Measurable.pred M (\<lambda>x. \<forall>i\<in>X. P x i)"
    "(\<And>i. i \<in> X \<Longrightarrow> Measurable.pred M (\<lambda>x. P x i)) \<Longrightarrow> Measurable.pred M (\<lambda>x. \<exists>i\<in>X. P x i)"
  unfolding pred_def
  by (auto intro!: sets.sets_Collect_countable_All' sets.sets_Collect_countable_Ex' assms)

lemma measurable_THE:
  fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes [measurable]: "\<And>i. Measurable.pred M (P i)"
  assumes I[simp]: "countable I" "\<And>i x. x \<in> space M \<Longrightarrow> P i x \<Longrightarrow> i \<in> I"
  assumes unique: "\<And>x i j. x \<in> space M \<Longrightarrow> P i x \<Longrightarrow> P j x \<Longrightarrow> i = j"
  shows "(\<lambda>x. THE i. P i x) \<in> measurable M (count_space UNIV)"
  unfolding measurable_def
proof safe
  fix X
  def f \<equiv> "\<lambda>x. THE i. P i x" def undef \<equiv> "THE i::'a. False"
  { fix i x assume "x \<in> space M" "P i x" then have "f x = i"
      unfolding f_def using unique by auto }
  note f_eq = this
  { fix x assume "x \<in> space M" "\<forall>i\<in>I. \<not> P i x"
    then have "\<And>i. \<not> P i x"
      using I(2)[of x] by auto
    then have "f x = undef"
      by (auto simp: undef_def f_def) }
  then have "f -` X \<inter> space M = (\<Union>i\<in>I \<inter> X. {x\<in>space M. P i x}) \<union>
     (if undef \<in> X then space M - (\<Union>i\<in>I. {x\<in>space M. P i x}) else {})"
    by (auto dest: f_eq)
  also have "\<dots> \<in> sets M"
    by (auto intro!: sets.Diff sets.countable_UN')
  finally show "f -` X \<inter> space M \<in> sets M" .
qed simp

lemma measurable_bot[measurable]: "Measurable.pred M \<bottom>"
  by (simp add: bot_fun_def)

lemma bex1_def: "(\<exists>!x\<in>X. P x) \<longleftrightarrow> (\<exists>x\<in>X. P x) \<and> (\<forall>x\<in>X. \<forall>y\<in>X. P x \<longrightarrow> P y \<longrightarrow> x = y)"
  by auto

lemma measurable_Ex1[measurable (raw)]:
  assumes [simp]: "countable I" and [measurable]: "\<And>i. i \<in> I \<Longrightarrow> Measurable.pred M (P i)"
  shows "Measurable.pred M (\<lambda>x. \<exists>!i\<in>I. P i x)"
  unfolding bex1_def by measurable

lemma measurable_split_if[measurable (raw)]:
  "(c \<Longrightarrow> Measurable.pred M f) \<Longrightarrow> (\<not> c \<Longrightarrow> Measurable.pred M g) \<Longrightarrow>
   Measurable.pred M (if c then f else g)"
  by simp

lemma ereal_times_divide_eq: "a * (b / c :: ereal) = a * b / c"
  by (cases a b c rule: ereal3_cases)
     (auto simp: field_simps zero_less_mult_iff)

lemma setsum_ereal_left_distrib:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> setsum f A * r = (\<Sum>n\<in>A. f n * r)"
  by (simp add: setsum_ereal_right_distrib mult_ac)

lemma emeasure_eq_0_AE: "AE x in M. \<not> P x \<Longrightarrow> emeasure M {x\<in>space M. P x} = 0"
  using AE_iff_measurable[OF _ refl, of M "\<lambda>x. \<not> P x"]
  by (cases "{x\<in>space M. P x} \<in> sets M") (simp_all add: emeasure_notin_sets)

lemma suntil_induct_strong[consumes 1, case_names base step]:
  "(\<phi> suntil \<psi>) x \<Longrightarrow>
    (\<And>\<omega>. \<psi> \<omega> \<Longrightarrow> P \<omega>) \<Longrightarrow>
    (\<And>\<omega>. \<phi> \<omega> \<Longrightarrow> \<not> \<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) (stl \<omega>) \<Longrightarrow> P (stl \<omega>) \<Longrightarrow> P \<omega>) \<Longrightarrow> P x"
  using suntil.induct[of \<phi> \<psi> x P] by blast

lemma (in prob_space) prob_setsum:
  assumes [simp, intro]: "finite I"
  assumes P: "\<And>n. n \<in> I \<Longrightarrow> {x\<in>space M. P n x} \<in> events"
  assumes Q: "{x\<in>space M. Q x} \<in> events"
  assumes ae: "AE x in M. (\<forall>n\<in>I. P n x \<longrightarrow> Q x) \<and> (Q x \<longrightarrow> (\<exists>!n\<in>I. P n x))"
  shows "\<P>(x in M. Q x) = (\<Sum>n\<in>I. \<P>(x in M. P n x))"
proof -
  from ae[THEN AE_E_prob] guess S . note S = this
  then have disj: "disjoint_family_on (\<lambda>n. {x\<in>space M. P n x} \<inter> S) I"
    by (auto simp: disjoint_family_on_def)
  from S have ae_S:
    "AE x in M. x \<in> {x\<in>space M. Q x} \<longleftrightarrow> x \<in> (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    "\<And>n. n \<in> I \<Longrightarrow> AE x in M. x \<in> {x\<in>space M. P n x} \<longleftrightarrow> x \<in> {x\<in>space M. P n x} \<inter> S"
    using ae by (auto dest!: AE_prob_1)
  from ae_S have *:
    "\<P>(x in M. Q x) = prob (\<Union>n\<in>I. {x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) (auto intro!: sets.Int)
  from ae_S have **:
    "\<And>n. n \<in> I \<Longrightarrow> \<P>(x in M. P n x) = prob ({x\<in>space M. P n x} \<inter> S)"
    using P Q S by (intro finite_measure_eq_AE) auto
  show ?thesis
    using S P disj
    by (auto simp add: * ** simp del: UN_simps intro!: finite_measure_finite_Union)
qed

lemma funpow_decreasing:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  shows "m \<le> n \<Longrightarrow> mono f \<Longrightarrow> (f ^^ m) \<bottom> \<le> (f ^^ n) \<bottom>"
  by (induct rule: dec_induct)
     (auto simp del: funpow.simps(2) simp add: funpow_Suc_right
           intro: order_trans[OF _ funpow_mono])

lemma nn_integral_count_space':
  assumes "finite A" "\<And>x. x \<in> B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = 0" "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" "A \<subseteq> B"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space B) = (\<Sum>x\<in>A. f x)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>count_space B) = (\<Sum>a | a \<in> B \<and> 0 < f a. f a)"
    using assms(2,3)
    by (intro nn_integral_count_space finite_subset[OF _ `finite A`]) (auto simp: less_le)
  also have "\<dots> = (\<Sum>a\<in>A. f a)"
    using assms by (intro setsum.mono_neutral_cong_left) (auto simp: less_le)
  finally show ?thesis .
qed

lemma suntil_aand_nxt:
  "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega> \<longleftrightarrow> (\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
proof
  assume "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega>" then show "(\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
    by induction (auto intro: suntil.intros)
next
  assume "(\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
  then have "(\<phi> suntil \<psi>) (stl \<omega>)" "\<phi> \<omega>"
    by auto
  then show "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega>"
    by (induction "stl \<omega>" arbitrary: \<omega>)
       (auto elim: suntil.cases intro: suntil.intros)
qed

lemma nn_integral_indicator_finite:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite A" and nn: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" and [measurable]: "\<And>a. a \<in> A \<Longrightarrow> {a} \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<Sum>x\<in>A. f x * emeasure M {x})"
proof -
  from f have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>a\<in>A. f a * indicator {a} x) \<partial>M)"
    by (intro nn_integral_cong) (auto simp: indicator_def if_distrib[where f="\<lambda>a. x * a" for x] setsum.If_cases)
  also have "\<dots> = (\<Sum>a\<in>A. f a * emeasure M {a})"
    using nn by (subst nn_integral_setsum) (auto simp: nn_integral_cmult_indicator)
  finally show ?thesis .
qed

lemma nn_integral_measure_pmf_support:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite A" and nn: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x" "\<And>x. x \<in> set_pmf M \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>A. f x * pmf M x)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>M) = (\<integral>\<^sup>+x. f x * indicator A x \<partial>M)"
    using nn by (intro nn_integral_cong_AE) (auto simp: AE_measure_pmf_iff split: split_indicator)
  also have "\<dots> = (\<Sum>x\<in>A. f x * emeasure M {x})"
    using assms by (intro nn_integral_indicator_finite) auto
  finally show ?thesis
    by (simp add: emeasure_measure_pmf_finite)
qed

lemma nn_integral_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes f: "finite (set_pmf M)" and nn: "\<And>x. x \<in> set_pmf M \<Longrightarrow> 0 \<le> f x"
  shows "(\<integral>\<^sup>+x. f x \<partial>measure_pmf M) = (\<Sum>x\<in>set_pmf M. f x * pmf M x)"
  using assms by (intro nn_integral_measure_pmf_support) auto

lemma alw_sconst: "alw P (sconst x) \<longleftrightarrow> P (sconst x)"
proof
  assume "P (sconst x)" then show "alw P (sconst x)"
    by coinduction auto
qed auto

lemma ev_sconst: "ev P (sconst x) \<longleftrightarrow> P (sconst x)"
proof
  assume "ev P (sconst x)" then show "P (sconst x)"
    by (induction "sconst x") auto
qed auto

lemma suntil_sconst: "(\<phi> suntil \<psi>) (sconst x) \<longleftrightarrow> \<psi> (sconst x)"
proof
  assume "(\<phi> suntil \<psi>) (sconst x)" then show "\<psi> (sconst x)"
    by (induction "sconst x") auto
qed (auto intro: suntil.intros)

hide_const cont

lemma mono_funpow:
  fixes Q :: "('i \<Rightarrow> 'a::complete_lattice) \<Rightarrow> ('i \<Rightarrow> 'a::complete_lattice)"
  shows "mono Q \<Longrightarrow> mono (\<lambda>i. (Q ^^ i) \<bottom>)"
  by (auto intro!: funpow_decreasing simp: mono_def)

lemma mono_compose: "mono Q \<Longrightarrow> mono (\<lambda>i x. Q i (f x))"
  unfolding mono_def le_fun_def by auto

lemma SUP_ereal_mult_right:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
    and "0 \<le> c"
  shows "(SUP i:I. c * f i) = c * (SUP i:I. f i)"
proof (rule SUP_eqI)
  fix i assume "i \<in> I"
  then have "f i \<le> SUPREMUM I f"
    by (rule SUP_upper)
  then show "c * f i \<le> c * SUPREMUM I f"
    using `0 \<le> c` by (rule ereal_mult_left_mono)
next
  fix y assume *: "\<And>i. i \<in> I \<Longrightarrow> c * f i \<le> y"
  { assume "c = \<infinity>" have "c * SUPREMUM I f \<le> y"
    proof cases
      assume "\<forall>i\<in>I. f i = 0"
      then show ?thesis
        using * `c = \<infinity>` by (auto simp: SUP_constant bot_ereal_def)
    next
      assume "\<not> (\<forall>i\<in>I. f i = 0)"
      then obtain i where "f i \<noteq> 0" "i \<in> I"
        by auto
      with *[of i] `c = \<infinity>` `i \<in> I \<Longrightarrow> 0 \<le> f i` show ?thesis
        by (auto split: split_if_asm)
    qed }
  moreover
  { assume "c \<noteq> 0" "c \<noteq> \<infinity>"
    moreover with `0 \<le> c` * have "SUPREMUM I f \<le> y / c"
      by (intro SUP_least) (auto simp: ereal_le_divide_pos)
    ultimately have "c * SUPREMUM I f \<le> y"
      using `0 \<le> c` * by (auto simp: ereal_le_divide_pos) }
  moreover { assume "c = 0" with * `I \<noteq> {}` have "c * SUPREMUM I f \<le> y" by auto }
  ultimately show "c * SUPREMUM I f \<le> y"
    by blast
qed

lemma SUP_ereal_add_left:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
    and "0 \<le> c"
  shows "(SUP i:I. f i + c) = SUPREMUM I f + c"
proof (intro SUP_eqI)
  fix B assume *: "\<And>i. i \<in> I \<Longrightarrow> f i + c \<le> B"
  show "SUPREMUM I f + c \<le> B"
  proof cases
    assume "c = \<infinity>" with `I \<noteq> {}` * show ?thesis
      by auto
  next
    assume "c \<noteq> \<infinity>"
    with `0 \<le> c` have [simp]: "\<bar>c\<bar> \<noteq> \<infinity>"
      by simp
    have "SUPREMUM I f \<le> B - c"
      by (simp add: SUP_le_iff ereal_le_minus *)
    then show ?thesis
      by (simp add: ereal_le_minus)
  qed
qed (auto intro: ereal_add_mono SUP_upper)

lemma ereal_mult_divide: fixes a b :: ereal shows "0 < b \<Longrightarrow> b < \<infinity> \<Longrightarrow> b * (a / b) = a"
  by (cases a b rule: ereal2_cases) auto

lemma nn_integral_monotone_convergence_SUP:
  assumes f: "incseq f" and [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
proof -
  have "(\<integral>\<^sup>+ x. max 0 (SUP i. f i x) \<partial>M) = (\<integral>\<^sup>+ x. (SUP i. max 0 (f i x)) \<partial>M)"
    unfolding sup_max[symmetric] Complete_Lattices.SUP_sup_distrib[symmetric] by simp
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. max 0 (f i x) \<partial>M))"
    apply (intro nn_integral_monotone_convergence_SUP)
    apply (auto simp: incseq_def le_fun_def not_le dest!: incseqD[OF f] split: split_max)
    apply (blast intro: order_trans less_imp_le)
    done
  finally show ?thesis
    unfolding nn_integral_max_0 .
qed

lemma some_in_iff: "(SOME x. x \<in> A) \<in> A \<longleftrightarrow> A \<noteq> {}"
  by (metis someI_ex ex_in_conv)

text {*

Markov chain with discrete time steps and discrete state space.

*}

lemma measurable_suntil[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) Q" "Measurable.pred (stream_space M) P"
  shows "Measurable.pred (stream_space M) (Q suntil P)"
  unfolding suntil_def by (coinduction rule: measurable_lfp) (auto simp: Order_Continuity.continuous_def)

locale MC_syntax =
  fixes K :: "'s \<Rightarrow> 's pmf"
begin

coinductive enabled where
  "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> shd \<omega> \<in> K s \<Longrightarrow> enabled s \<omega>"

lemma alw_enabled: "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> alw (\<lambda>\<omega>. enabled (shd \<omega>) (stl \<omega>)) \<omega>"
  by (coinduction arbitrary: \<omega> rule: alw_coinduct) (auto elim: enabled.cases)

abbreviation "S \<equiv> stream_space (count_space UNIV)"

inductive_simps enabled_iff: "enabled s \<omega>"

lemma measurable_enabled[measurable]:
  "Measurable.pred (stream_space (count_space UNIV)) (enabled s)" (is "Measurable.pred ?S _")
  unfolding enabled_def
proof (coinduction arbitrary: s rule: measurable_gfp2)
  case (step A s)
  then have [measurable]: "\<And>t. Measurable.pred ?S (A t)" by auto
  have *: "\<And>x. (\<exists>\<omega> t. s = t \<and> x = \<omega> \<and> A (shd \<omega>) (stl \<omega>) \<and> shd \<omega> \<in> set_pmf (K t)) \<longleftrightarrow>
    (\<exists>t\<in>K s. A t (stl x) \<and> t = shd x)"
    by auto
  note countable_set_pmf[simp]
  show ?case
    unfolding * by measurable
qed (auto simp: down_continuous_def)

lemma enabled_iff_snth: "enabled s \<omega> \<longleftrightarrow> (\<forall>i. \<omega> !! i \<in> K ((s ## \<omega>) !! i))"
proof safe
  fix i assume "enabled s \<omega>" then show "\<omega> !! i \<in> K ((s ## \<omega>) !! i)"
    by (induct i arbitrary: s \<omega>)
       (force elim: enabled.cases)+
next
  assume "\<forall>i. \<omega> !! i \<in> set_pmf (K ((s ## \<omega>) !! i))" then show "enabled s \<omega>"
    by (coinduction arbitrary: s \<omega>)
       (auto elim: allE[of _ "Suc i" for i] allE[of _ 0])
qed

abbreviation "D \<equiv> stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"

lemma sets_D: "sets D = sets (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  by (intro sets_stream_space_cong sets_PiM_cong) simp_all

lemma space_D: "space D = space (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  using sets_eq_imp_space_eq[OF sets_D] .
  
lemma measurable_D_D: "measurable D D = 
    measurable (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV)) (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  by (simp add: measurable_def space_D sets_D)

primcorec walk :: "'s \<Rightarrow> ('s \<Rightarrow> 's) stream \<Rightarrow> 's stream" where
  "shd (walk s \<omega>) = (if shd \<omega> s \<in> K s then shd \<omega> s else (SOME t. t \<in> K s))"
| "stl (walk s \<omega>) = walk (if shd \<omega> s \<in> K s then shd \<omega> s else (SOME t. t \<in> K s)) (stl \<omega>)"

lemma enabled_walk: "enabled s (walk s \<omega>)"
  by (coinduction arbitrary: s \<omega>) (auto simp: some_in_iff set_pmf_not_empty)

lemma measurable_walk[measurable]: "walk s \<in> measurable D S"
proof -
  note measurable_compose[OF measurable_snth, intro!]
  note measurable_compose[OF measurable_component_singleton, intro!]
  note if_cong[cong del]
  note measurable_g = measurable_compose_countable'[OF _ _ countable_reachable]

  def n \<equiv> "0::nat"
  def g \<equiv> "\<lambda>_::('s \<Rightarrow> 's) stream. s"
  then have "g \<in> measurable D (count_space ((SIGMA s:UNIV. K s)\<^sup>* `` {s}))"
    by auto
  then have "(\<lambda>x. walk (g x) (sdrop n x)) \<in> measurable D S"
  proof (coinduction arbitrary: g n rule: measurable_stream_coinduct)
    case (shd f') show ?case
      by (fastforce intro: measurable_g[OF _ shd])
  next
    case (stl f') show ?case
      by (fastforce simp add: sdrop.simps[symmetric] some_in_iff set_pmf_not_empty
                    simp del: sdrop.simps intro: rtrancl_into_rtrancl measurable_g[OF _ stl])
  qed
  then show ?thesis
    by (simp add: g_def n_def)
qed

definition T :: "'s \<Rightarrow> 's stream measure" where
  "T s = distr (stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)) S (walk s)"

lemma space_T[simp]: "space (T s) = space S"
  by (simp add: T_def)

lemma sets_T[simp]: "sets (T s) = sets S"
  by (simp add: T_def)

lemma measurable_T1[simp]: "measurable (T s) M = measurable S M"
  by (intro measurable_cong_sets) simp_all

lemma measurable_T2[simp]: "measurable M (T s) = measurable M S"
  by (intro measurable_cong_sets) simp_all

lemma in_measurable_T1[measurable (raw)]: "f \<in> measurable S M \<Longrightarrow> f \<in> measurable (T s) M"
  by simp

lemma in_measurable_T2[measurable (raw)]: "f \<in> measurable M S \<Longrightarrow> f \<in> measurable M (T s)"
  by simp

lemma AE_T_enabled: "AE \<omega> in T s. enabled s \<omega>"
  unfolding T_def by (simp add: AE_distr_iff enabled_walk)

sublocale T!: prob_space "T s" for s
proof -
  interpret P: product_prob_space K UNIV
    by default
  interpret prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule P.prob_space_stream_space)
  fix s show "prob_space (T s)"
    by (simp add: T_def prob_space_distr)
qed

lemma nn_integral_T:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+t. (\<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t) \<partial>K s)"
proof -
  interpret product_prob_space K UNIV
    by default
  interpret D: prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule prob_space_stream_space)

  have T: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+\<omega>. f (walk s \<omega>) \<partial>D)"
    by (simp add: T_def nn_integral_distr)

  have "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+\<omega>. f (walk s \<omega>) \<partial>D)"
    by (rule T) measurable
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (walk s (d ## \<omega>)) \<partial>D \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (simp add: P.nn_integral_stream_space)
  also have "\<dots> = (\<integral>\<^sup>+d. (\<integral>\<^sup>+\<omega>. f (d s ## walk (d s) \<omega>) * indicator {t. t \<in> K s} (d s) \<partial>D) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    apply (rule nn_integral_cong_AE)
    apply (subst walk.ctr)
    apply (simp cong del: if_cong)
    apply (intro UNIV_I AE_component)
    apply (auto simp: AE_measure_pmf_iff)
    done
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (d s ## \<omega>) * indicator {t. t \<in> K s} (d s) \<partial>T (d s) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (subst T) (simp_all split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) * indicator {t. t \<in> K s} t \<partial>T t \<partial>K s)"
    by (subst (2) PiM_component[symmetric]) (simp_all add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t \<partial>K s)"
    by (rule nn_integral_cong_AE) (simp add: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma emeasure_Collect_T:
  assumes f[measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). P x} = (\<integral>\<^sup>+t. emeasure (T t) {x\<in>space (T t). P (t ## x)} \<partial>K s)"
  apply (subst (1 2) nn_integral_indicator[symmetric])
  apply simp
  apply simp
  apply (subst nn_integral_T)
  apply (auto intro!: nn_integral_cong simp add: space_stream_space indicator_def)
  done

lemma AE_T_iff:
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> (\<forall>y\<in>K x. AE \<omega> in T y. P (y ## \<omega>))"
  by (simp add: AE_iff_nn_integral nn_integral_T[where s=x])
     (auto simp add: nn_integral_0_iff_AE AE_measure_pmf_iff split: split_indicator)

lemma emeasure_suntil:
  assumes [measurable]: "Measurable.pred S P" "Measurable.pred S Q"
  shows "emeasure (T s) {x\<in>space (T s). (P suntil Q) x} =
   (SUP i. emeasure (T s) {x\<in>space (T s). ((\<lambda>R. Q or (P aand nxt R))^^i) (\<lambda>_. False) x})"
proof -
  have suntil_eq: "(P suntil Q) = lfp (\<lambda>R. Q or (P aand nxt R))"
    unfolding suntil_def by (auto intro!: arg_cong[where f=lfp])
  show ?thesis
    unfolding suntil_eq
  proof (coinduction arbitrary: s rule: emeasure_lfp)
    case measurable
    have [measurable]: "Measurable.pred S A"
      using measurable[of "T s"] by auto
    show ?case
      by simp
  qed (auto simp: Order_Continuity.continuous_def)
qed

lemma emeasure_ev:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). ev P x} =
   (SUP i. emeasure (T s) {x\<in>space (T s). ((\<lambda>R. P or nxt R)^^i) (\<lambda>_. False) x})"
proof -
  have ev_eq: "ev P = lfp (\<lambda>R. P or nxt R)"
    unfolding ev_def by (auto intro!: arg_cong[where f=lfp])
  show ?thesis
    unfolding ev_eq
  proof (coinduction arbitrary: s rule: emeasure_lfp)
    case measurable
    have [measurable]: "Measurable.pred S A"
      using measurable[of "T s"] by auto
    show ?case
      by simp
  qed (auto simp: Order_Continuity.continuous_def)
qed

lemma emeasure_suntil_HLD:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). (not (HLD {t}) suntil (HLD {t} aand nxt P)) x} =
   emeasure (T s) {x\<in>space (T s). ev (HLD {t}) x} * emeasure (T t) {x\<in>space (T t). P x}"
proof -
  let ?t = "HLD {t}"
  let ?M = "\<lambda>s P. emeasure (T s) {x\<in>space (T s). P x}"
  let ?F = "\<lambda>i. ((\<lambda>Q. (?t aand nxt P) or (not ?t aand nxt Q))^^i) (\<lambda>_. False)"
  let ?E = "\<lambda>i. ((\<lambda>Q. ?t or nxt Q)^^i) (\<lambda>_. False)"

  have "?M s ((not ?t) suntil (?t aand nxt P)) = (SUP i. ?M s (?F i))"
    by (rule emeasure_suntil) measurable
  also have "\<dots> = (SUP i. ?M s (?E i) * ?M t P)"
  proof (intro SUP_cong refl)
    fix i :: nat show "?M s (?F i) = ?M s (?E i) * ?M t P"
    proof (induct i arbitrary: s)
      case (Suc i)
      have "?M s (?F (Suc i)) = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. ?F (Suc i) (t ## \<omega>)) \<partial>K s)"
        by (intro emeasure_Collect_T measurable_predpow) auto
      also have "\<dots> = (\<integral>\<^sup>+t'. (if t' = t then ?M t P else ?M t' (?F i)) \<partial>K s)"
        by (intro nn_integral_cong) (auto simp: HLD_iff)
      also have "\<dots> = (\<integral>\<^sup>+t'. ?M t' (\<lambda>\<omega>. ?E (Suc i) (t' ## \<omega>)) * ?M t P \<partial>K s)"
        using T.emeasure_space_1 unfolding Suc by (intro nn_integral_cong) (auto simp: HLD_iff)
      also have "\<dots> = (\<integral>\<^sup>+t'. ?M t' (\<lambda>\<omega>. ?E (Suc i) (t' ## \<omega>)) \<partial>K s) * ?M t P"
        by (rule nn_integral_multc) auto
      also have "(\<integral>\<^sup>+t'. ?M t' (\<lambda>\<omega>. ?E (Suc i) (t' ## \<omega>)) \<partial>K s) = ?M s (?E (Suc i))"
        by (intro emeasure_Collect_T[symmetric] measurable_predpow) auto
      finally show ?case .
    qed simp
  qed
  also have "\<dots> = (SUP i. ?M s (?E i)) * ?M t P"
    by (subst (1 2) mult.commute) (auto intro!: SUP_ereal_cmult)
  also have [symmetric]: "?M s (ev ?t) = (SUP i. ?M s (?E i))"
    by (rule emeasure_ev) measurable
  finally show ?thesis .
qed

lemma mult_eq_1:
  fixes a b :: "'a :: {ordered_semiring, comm_monoid_mult}"
  shows "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b = 1 \<longleftrightarrow> (a = 1 \<and> b = 1)"
  by (metis mult.left_neutral eq_iff mult.commute mult_right_mono)

lemma AE_suntil: 
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE x in T s. (not (HLD {t}) suntil (HLD {t} aand nxt P)) x) \<longleftrightarrow>
   (AE x in T s. ev (HLD {t}) x) \<and> (AE x in T t. P x)"
  apply (subst (1 2 3) T.prob_Collect_eq_1[symmetric])
  apply simp
  apply simp
  apply simp
  apply (simp_all add: measure_def emeasure_suntil_HLD del: space_T nxt.simps)
  apply (auto simp: T.emeasure_eq_measure mult_eq_1 measure_nonneg)
  done

definition fair :: "'s \<Rightarrow> 's \<Rightarrow> 's stream \<Rightarrow> bool" where
  "fair s t = alw (ev (HLD {s})) impl alw (ev (HLD {s} aand nxt (HLD {t})))"

lemma AE_T_alw:
  assumes [measurable]: "Measurable.pred S P"
  assumes P: "\<And>x. AE \<omega> in T x. P \<omega>"
  shows "AE \<omega> in T x. alw P \<omega>"
proof -
  { fix i have "almost_everywhere (T x) (((\<lambda>p x. P x \<and> p (stl x)) ^^ i) top)"
      apply (induct i arbitrary: x)
      apply simp
      apply (subst AE_T_iff)
      unfolding top_fun_def
      apply measurable
      apply simp
      apply simp
      apply (subst AE_T_iff[symmetric])
      apply simp
      apply (rule P)
      done }
  then have "almost_everywhere (T x) (gfp (\<lambda>p x. P x \<and> p (stl x)))"
    by (subst down_continuous_gfp) (auto simp: down_continuous_def AE_all_countable)
  then show ?thesis
    by (simp add: alw_def)
qed

lemma AE_T_fair:
  assumes "t' \<in> K t"
  shows "AE \<omega> in T s. fair t t' \<omega>"
proof -
  def never \<equiv> "alw (ev (HLD {t})) aand alw (not (HLD {t} aand nxt (HLD {t'})))"
  have never_stl: "\<And>\<omega>. never \<omega> \<Longrightarrow> never (stl \<omega>)"
    by (auto simp: never_def)
  have [measurable]: "Measurable.pred S never"
    unfolding never_def by measurable

  def c \<equiv> "measure (K t) {t'}"
  have c_le_1[arith]: "c \<le> 1"
    unfolding c_def by (rule measure_pmf.prob_le_1)
  have "0 < c"
    unfolding c_def
    using emeasure_pmf_single_eq_zero_iff[of "K t" t'] `t' \<in> K t`
    by (simp add: measure_pmf.emeasure_eq_measure measure_nonneg less_le)

  let ?M = "\<lambda>s P. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>}"
  { fix x k have "?M x (\<lambda>\<omega>. never \<omega>) \<le> (1 - c)^k"
    proof (induct k arbitrary: x)
      case 0 then show ?case
        by (simp add: T.measure_le_1 one_ereal_def[symmetric])
    next
      case (Suc k)
      let ?C = "ereal ((1 - c)^k)"
      let ?until = "not (HLD {t}) suntil (HLD {t} aand nxt (not (HLD {t'}) aand never))"
      { fix \<omega> assume "never \<omega>"
        then have "ev (HLD {t}) \<omega>" "never \<omega>"
          by (auto simp: never_def)
        then have "?until \<omega>"
        proof (induct rule: ev_induct_strong)
          case (base \<omega>) then show ?case
            by (intro suntil.base) (auto simp: never_def)
        next
          case (step \<omega>) then show ?case
            by (intro suntil.step[of _ \<omega>]) (auto simp: never_stl)
        qed }
      then have "?M x (\<lambda>\<omega>. never \<omega>) \<le> ?M x (\<lambda>\<omega>. ?until \<omega>)"
        apply (intro emeasure_mono_AE)
        defer
        apply measurable []
        apply (rule UNIV_I)
        apply measurable
        done
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * ?M t (\<lambda>\<omega>. (not (HLD {t'}) aand never) \<omega>)"
        by (intro emeasure_suntil_HLD) simp
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. ?M y (\<lambda>\<omega>. y \<noteq> t' \<and> never (y ## \<omega>)) \<partial>K t)"
        by (subst (2) emeasure_Collect_T) (simp_all add: HLD_iff)
      also have "\<dots> \<le> ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. ?M y (\<lambda>\<omega>. y \<noteq> t' \<and> never \<omega>) \<partial>K t)"
        by (intro ereal_mult_left_mono emeasure_nonneg nn_integral_mono emeasure_mono_AE)
           (auto dest: never_stl[of "x ## s" for x s, simplified])
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. indicator (- {t'}) y * ?M y never \<partial>K t)"
        by (subst (2 4) emeasure_Collect_T)
           (auto intro!: ereal_left_mult_cong nn_integral_cong split: split_indicator)
      also have "\<dots> \<le> ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (\<integral>\<^sup>+y. indicator (- {t'}) y * ?C \<partial>K t)"
        by (intro ereal_mult_left_mono emeasure_nonneg nn_integral_mono Suc ereal_indicator_nonneg)
      also have "\<dots> = ?M x (\<lambda>\<omega>. ev (HLD {t}) \<omega>) * (emeasure (K t) (space (K t) - {t'}) * ?C)"
        by (subst nn_integral_multc) (auto intro!: zero_le_power simp: Compl_eq_Diff_UNIV)
      also have "\<dots> \<le> 1 * (emeasure (K t) (space (K t) - {t'}) * ?C)"
        by (intro ereal_mult_right_mono T.measure_le_1) (auto intro!: ereal_0_le_mult)
      also have "emeasure (K t) (space (K t) - {t'}) = 1 - emeasure (K t) {t'}"
        using measure_pmf.emeasure_space_1[of "K t"] by (subst emeasure_compl) auto
      also have "1 * ((1 - emeasure (K t) {t'}) * ?C) \<le> 1 * (ereal (1 - c) * ?C)"
        unfolding c_def
        by (intro ereal_mult_right_mono ereal_mult_left_mono)
           (auto simp: measure_pmf.emeasure_eq_measure one_ereal_def field_simps intro!: zero_le_power)
      finally show ?case
        by simp
    qed }
  then have "\<And>x. emeasure (T x) {\<omega> \<in> space (T x). never \<omega>} \<le> 0"
  proof (intro tendsto_le_const[OF sequentially_bot])
    show "(\<lambda>k. ereal ((1 - c) ^ k)) ----> 0"
      unfolding zero_ereal_def by (auto intro!: LIMSEQ_realpow_zero `0 < c`)
  qed auto
  then have "\<And>x. AE \<omega> in T x. \<not> never \<omega>"
    by (intro AE_I[OF order_refl] antisym emeasure_nonneg) auto
  then have "AE \<omega> in T s. alw (not never) \<omega>"
    by (intro AE_T_alw) auto
  moreover
  { fix \<omega> assume "alw (ev (HLD {t})) \<omega>"
    then have "alw (alw (ev (HLD {t}))) \<omega>"
      unfolding alw_alw .
    moreover assume "alw (not never) \<omega>"
    then have "alw (alw (ev (HLD {t})) impl ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      unfolding never_def not_alw_iff not_ev_iff de_Morgan_disj de_Morgan_conj not_not imp_conv_disj .
    ultimately have "alw (ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      by (rule alw_mp) }
  then have "\<forall>\<omega>. alw (not never) \<omega> \<longrightarrow> fair t t' \<omega>"
    by (auto simp: fair_def)
  ultimately show ?thesis
    by (rule eventually_rev_mono)
qed

lemma enabled_imp_trancl:
  assumes "alw (HLD B) \<omega>" "enabled s \<omega>"
  shows "alw (HLD ((SIGMA s:UNIV. K s \<inter> B)\<^sup>* `` {s})) \<omega>"
proof -
  def t \<equiv> s
  then have "(s, t) \<in> (SIGMA s:UNIV. set_pmf (K s) \<inter> B)\<^sup>*"
    by auto
  moreover note `alw (HLD B) \<omega>`
  moreover note `enabled s \<omega>`[unfolded `t == s`[symmetric]]
  ultimately show ?thesis
  proof (coinduction arbitrary: t \<omega> rule: alw_coinduct)
    case stl from this(1,2,3) show ?case
      by (auto simp: enabled.simps[of _ \<omega>] alw.simps[of _ \<omega>] HLD_iff
                 intro!: exI[of _ "shd \<omega>"] rtrancl_trans[of s t])
  next
    case (alw t \<omega>) then show ?case
     by (auto simp: HLD_iff enabled.simps[of _ \<omega>] alw.simps[of _ \<omega>] intro!: rtrancl_trans[of s t])
  qed
qed
  

lemma AE_T_reachable: "AE \<omega> in T s. alw (HLD ((SIGMA s:UNIV. K s)\<^sup>* `` {s})) \<omega>"
  using AE_T_enabled
proof eventually_elim
  fix \<omega> assume "enabled s \<omega>"
  from enabled_imp_trancl[of UNIV, OF _ this]
  show "alw (HLD ((SIGMA s:UNIV. K s)\<^sup>* `` {s})) \<omega>"
    by (auto simp: HLD_iff[abs_def] all_imp_alw)
qed

lemma AE_T_all_fair: "AE \<omega> in T s. \<forall>(t,t')\<in>SIGMA t:UNIV. K t. fair t t' \<omega>"
proof -
  let ?R = "SIGMA t:UNIV. K t" let ?Rn = "SIGMA s:(?R\<^sup>* `` {s}). K s"
  have "AE \<omega> in T s. \<forall>(t,t')\<in>?Rn. fair t t' \<omega>"
  proof (subst AE_ball_countable)
    show "countable ?Rn"
      by (intro countable_SIGMA countable_rtrancl[OF countable_Image])
         (auto simp: Image_def countable_set_pmf)
  qed (auto intro!: AE_T_fair)
  then show ?thesis
    using AE_T_reachable
  proof (eventually_elim, safe)
    fix \<omega> t t' assume "\<forall>(t,t')\<in>?Rn. fair t t' \<omega>" "t' \<in> K t" and alw: "alw (HLD (?R\<^sup>* `` {s})) \<omega>"
    moreover
    { assume "t \<notin> ?R\<^sup>* `` {s}"
      then have "alw (not (HLD {t})) \<omega>"
        by (intro alw_mono[OF alw]) (auto simp: HLD_iff)
      then have "not (alw (ev (HLD {t}))) \<omega>"
        unfolding not_alw_iff not_ev_iff by auto
      then have "fair t t' \<omega>"
        unfolding fair_def by auto }
    ultimately show "fair t t' \<omega>"
      by auto
  qed
qed

lemma pigeonhole_stream:
  assumes "alw (HLD s) \<omega>"
  assumes "finite s"
  shows "\<exists>x\<in>s. alw (ev (HLD {x})) \<omega>"
proof -
  have "\<forall>i\<in>UNIV. \<exists>x\<in>s. \<omega> !! i = x"
    using `alw (HLD s) \<omega>` by (simp add: alw_iff_sdrop HLD_iff)
  from pigeonhole_infinite_rel[OF infinite_UNIV_nat `finite s` this]
  show ?thesis
    by (simp add: infinite_iff_alw_ev[where P="\<lambda>x. x = b" for b] )
qed

lemma fair_imp: assumes "fair t t' \<omega>" "alw (ev (HLD {t})) \<omega>" shows "alw (ev (HLD {t'})) \<omega>"
proof -
  { fix \<omega> assume "ev (HLD {t} aand nxt (HLD {t'})) \<omega>" then have "ev (HLD {t'}) \<omega>"
      by induction auto }
  with assms show ?thesis
    by (auto simp: fair_def elim!: alw_mp intro: all_imp_alw)
qed

lemma AE_T_ev_HLD:
  assumes exiting: "\<And>t. (s, t) \<in> (SIGMA s:UNIV. set_pmf (K s) - B)\<^sup>* \<Longrightarrow>
    \<exists>t'\<in>B. (t, t') \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes fin: "finite ((SIGMA s:UNIV. set_pmf (K s) - B)\<^sup>* `` {s})"
  shows "AE \<omega> in T s. ev (HLD B) \<omega>"
  using AE_T_all_fair AE_T_enabled
proof eventually_elim
  fix \<omega> assume fair: "\<forall>(t, t')\<in>(SIGMA s:UNIV. K s). fair t t' \<omega>" and "enabled s \<omega>"

  show "ev (HLD B) \<omega>"
  proof (rule ccontr)
    assume "\<not> ev (HLD B) \<omega>"
    then have "alw (HLD (- B)) \<omega>"
      by (simp add: not_ev_iff HLD_iff[abs_def])
    from enabled_imp_trancl[OF this `enabled s \<omega>`]
    have "alw (HLD ((SIGMA x:UNIV. set_pmf (K x) - B)\<^sup>* `` {s})) \<omega>"
      by (simp add: Diff_eq)
    from pigeonhole_stream[OF this fin]
    obtain t where "(s, t) \<in> (SIGMA s:UNIV. set_pmf (K s) - B)\<^sup>*" "alw (ev (HLD {t})) \<omega>"
      by auto
    from exiting[OF this(1)] obtain t' where "(t, t') \<in> (SIGMA x:UNIV. set_pmf (K x))\<^sup>*" "t' \<in> B"
      by auto
    from this(1) have "alw (ev (HLD {t'})) \<omega>"
    proof induction
      case (step u w) then show ?case
        using fair fair_imp[of u w \<omega>] by auto
    qed fact
    { assume "ev (HLD {t'}) \<omega>" then have "ev (HLD B) \<omega>"
      by (rule ev_mono) (auto simp: HLD_iff `t' \<in> B`) }
    then show False
      using `alw (ev (HLD {t'})) \<omega>` `\<not> ev (HLD B) \<omega>` by auto
  qed
qed

lemma nn_integral_enat_function:
  assumes f: "f \<in> measurable M (count_space UNIV)"
  shows "(\<integral>\<^sup>+ x. ereal_of_enat (f x) \<partial>M) = (\<Sum>t. emeasure M {x \<in> space M. t < f x})"
proof -
  def F \<equiv> "\<lambda>i::nat. {x\<in>space M. i < f x}"
  with assms have [measurable]: "\<And>i. F i \<in> sets M"
    by auto

  { fix x assume "x \<in> space M"
    have "(\<lambda>i::nat. if i < f x then 1 else 0) sums ereal_of_enat (f x)"
      using sums_If_finite[of "\<lambda>r. r < f x" "\<lambda>_. 1 :: ereal"]
      apply (cases "f x")
      apply (simp add: one_ereal_def real_of_nat_def[symmetric]) []
      apply (simp add: sums_def tendsto_PInfty_eq_at_top real_of_nat_def[symmetric]
                       filterlim_real_sequentially one_ereal_def)
      done
    also have "(\<lambda>i. (if i < f x then 1 else 0)) = (\<lambda>i. indicator (F i) x)"
      using `x \<in> space M` by (simp add: one_ereal_def F_def fun_eq_iff)
    finally have "ereal_of_enat (f x) = (\<Sum>i. indicator (F i) x)"
      by (simp add: sums_iff) }
  then have "(\<integral>\<^sup>+x. ereal_of_enat (f x) \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>i. indicator (F i) x) \<partial>M)"
    by (simp cong: nn_integral_cong)
  also have "\<dots> = (\<Sum>i. emeasure M (F i))"
    by (simp add: nn_integral_suminf)
  finally show ?thesis
    by (simp add: F_def)
qed

partial_function (gfp) hitting_time :: "'s set \<Rightarrow> 's stream \<Rightarrow> enat" where
  "hitting_time X \<omega> = (if HLD X \<omega> then 0 else eSuc (hitting_time X (stl \<omega>)))"

lemma measurable_hitting_time[measurable]: "hitting_time X \<in> measurable S (count_space UNIV)"
  apply (coinduction rule: measurable_enat_coinduct)
  apply simp
  apply (rule exI[of _ "\<lambda>x. 0"])
  apply (rule exI[of _ stl])
  apply (rule exI[of _ "HLD X"])
  apply (subst hitting_time.simps[abs_def])
  apply simp
  apply measurable
  done

lemma hitting_time_eq_0: "hitting_time X \<omega> = 0 \<longleftrightarrow> HLD X \<omega>"
  by (subst hitting_time.simps) auto

lemma hitting_time_HLD[simp]: "HLD X \<omega> \<Longrightarrow> hitting_time X \<omega> = 0"
  by (subst hitting_time.simps) auto

lemma hitting_time_nHLD[simp]: "\<not> HLD X \<omega> \<Longrightarrow> hitting_time X \<omega> = eSuc (hitting_time X (stl \<omega>))"
  by (subst hitting_time.simps) auto

lemma less_hitting_timeD:
  fixes n :: nat
  assumes "n < hitting_time X \<omega>" shows "\<omega> !! n \<notin> X"
  using assms
proof (induction n arbitrary: \<omega>)
  case (Suc n) then show ?case
    by (auto simp: hitting_time.simps[of _ \<omega>] eSuc_enat[symmetric] split: split_if_asm)
qed (simp add: enat_0 hitting_time_eq_0 HLD_iff)

lemma AE_T_max_hitting_time:
  assumes AE: "AE \<omega> in T c. hitting_time X (c ## \<omega>) < \<infinity>" and "0 < e"
  shows "\<exists>N::nat. \<P>(\<omega> in T c. N < hitting_time X (c ## \<omega>)) < e" (is "\<exists>N. ?P N < e")
proof -
  have "?P ----> measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < hitting_time X (c ## bT)})"
    using dual_order.strict_trans enat_ord_simps(2)
    by (intro T.finite_Lim_measure_decseq) (force simp: decseq_Suc_iff simp del: enat_ord_simps)+
  also have "measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < hitting_time X (c ## bT)}) =
      \<P>(bT in T c. hitting_time X (c ## bT) = \<infinity>)"
    by (auto simp del: not_infinity_eq intro!: arg_cong[where f="measure (T c)"])
       (metis less_irrefl not_infinity_eq)
  also have "\<P>(bT in T c. hitting_time X (c ## bT) = \<infinity>) = 0"
    using AE by (intro T.prob_eq_0_AE) auto
  finally have "\<exists>N. \<forall>n\<ge>N. norm (?P n - 0) < e"
    using `0 < e` by (rule LIMSEQ_D)
  then show ?thesis
    by (auto simp: measure_nonneg)
qed

lemma hitting_time_finite: "hitting_time H \<omega> < \<infinity> \<longleftrightarrow> ev (HLD H) \<omega>"
proof
  assume "hitting_time H \<omega> < \<infinity>"
  then obtain n where "hitting_time H \<omega> = enat n" by auto
  then show "ev (HLD H) \<omega>"
  proof (induction n arbitrary: \<omega>)
    case (Suc n) then show ?case
      by (auto simp add: eSuc_enat[symmetric] hitting_time.simps[of H \<omega>] split: split_if_asm)
  qed (auto simp add: enat_0 hitting_time_eq_0)
next
  assume "ev (HLD H) \<omega>" then show "hitting_time H \<omega> < \<infinity>"
    by (induction rule: ev_induct_strong) (auto simp: eSuc_enat)
qed

lemma hitting_time_Stream: "hitting_time X (s ## x) = (if s \<in> X then 0 else eSuc (hitting_time X x))"
  by (subst hitting_time.simps) (simp add: HLD_iff)

lemma less_hitting_time_iff:
  "(not (HLD X) until (alw (HLD X))) \<omega> \<Longrightarrow> n < hitting_time X \<omega> \<longleftrightarrow> \<omega> !! n \<notin> X"
proof (induction n arbitrary: \<omega>)
  case 0 then show ?case
    by (simp add: enat_0 hitting_time_eq_0 HLD_iff)
next
  case (Suc n)
  from Suc.prems have **: "HLD X \<omega> \<Longrightarrow> HLD X (stl \<omega>)"
    by (auto elim: UNTIL.cases)
  have *: "stl \<omega> !! n \<notin> X \<longleftrightarrow> enat n < hitting_time X (stl \<omega>)"
    using Suc.prems by (intro Suc.IH[symmetric]) (auto intro: UNTIL.intros elim: UNTIL.cases)
  show ?case
    unfolding snth.simps * by (cases "HLD X \<omega>") (simp_all add: ** eSuc_enat[symmetric])
qed

lemma nn_integral_hitting_time_finite:
  assumes [simp]: "finite ((SIGMA x:- H. set_pmf (K x) - H)\<^sup>* `` {s})" (is "finite (?R `` {s})")
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. hitting_time H (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by (simp add: hitting_time.simps)
next
  assume "s \<notin> H"
  then have [simp]: "?R `` {s} \<noteq> {}"
    by auto

  def X \<equiv> "\<lambda>n. ((\<lambda>Q. not (HLD H) aand nxt Q) ^^ n) \<top>"
  then have X_simps: "X 0 = \<top>" "\<And>n. X (Suc n) = not (HLD H) aand nxt (X n)"
    by simp_all

  have [measurable]: "\<And>n. Measurable.pred S (X n)"
    unfolding X_def
  proof (intro measurable_predpow)
    fix n and Q :: "'s stream \<Rightarrow> bool" assume [measurable]: "Measurable.pred S Q"
    show "Measurable.pred S (\<lambda>xs. \<not> HLD H xs \<and> nxt Q xs)"
      by measurable
  qed (simp add: top_fun_def)

  { fix t assume "(s, t) \<in> ?R"
    then have "AE \<omega> in T t. ev (HLD H) (t ## \<omega>)"
    proof induction
      case (step t u) with step.IH show ?case
        by (subst (asm) AE_T_iff)
           (auto simp add: ev_Stream holds_Stream simp del: holds.simps elim!: ballE[of _ _ u])
    qed (simp add: ev_Stream holds_Stream `s \<notin> H` del: holds.simps, fact)
    moreover
    assume "\<forall>n. AE \<omega> in T t. X n (t ## \<omega>)"
    then have "AE \<omega> in T t. alw (not (HLD H)) (t ## \<omega>)"
      unfolding alw_def X_def
      by (subst down_continuous_gfp) (auto simp: down_continuous_def AE_all_countable top_fun_def)
    ultimately have "AE \<omega> in T t. False"
      by eventually_elim (simp add: not_ev_iff[symmetric] del: holds.simps)
    then have False
      by auto }
  then have "\<forall>t\<in>?R `` {s}. \<exists>n. \<not> (AE \<omega> in T t. X n (t ## \<omega>))"
    by blast
  then obtain N where N: "\<And>t. (s, t) \<in> ?R \<Longrightarrow> \<not> (AE \<omega> in T t. X (N t) (t ## \<omega>))"
    unfolding bchoice_iff by auto

  def n \<equiv> "Max (N ` ?R `` {s})"
  { fix t and m :: nat assume t: "(s, t) \<in> ?R"
    then have "N t \<le> n"
      by (simp add: n_def)
    then have "X n \<le> X (N t)"
      unfolding X_def by (intro funpow_increasing) (auto simp: mono_def)
    with N[OF t] have "\<not> (AE \<omega> in T t. X n (t ## \<omega>))"
      by (auto intro: eventually_mono simp add: le_fun_def top_fun_def) }
  note n = this
  have "\<not> N s = 0"
      using N[of s] by (intro notI) (auto simp: X_simps)
  then have "1 \<le> n"
    unfolding n_def by (subst Max_ge_iff) (auto intro!: bexI[of _ s])

  def d \<equiv> "Max ((\<lambda>t. \<P>(\<omega> in T t. X n (t ## \<omega>))) ` ?R `` {s})"
  have d: "\<And>t. t \<in> ?R `` {s} \<Longrightarrow> \<P>(\<omega> in T t. X n (t ## \<omega>)) \<le> d"
    by (simp add: d_def)
  have [arith]: "0 \<le> d"
    using d[of s] by (auto intro: measure_nonneg order_trans)
  have "d < 1"
    unfolding d_def
    apply (subst Max_less_iff)
    apply (auto simp add: less_le dest!: n simp del: space_T)
    apply (subst (asm) T.prob_Collect_eq_1)
    apply simp_all
    done

  let ?M = "\<lambda>s P. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>}"

  have "(\<integral>\<^sup>+ \<omega>. hitting_time H (s ## \<omega>) \<partial>T s) = (\<Sum>i. ?M s (\<lambda>\<omega>. i < hitting_time H (s ## \<omega>)))"
    by (intro nn_integral_enat_function) simp
  also have "\<dots> \<le> (\<Sum>i. ereal (d^(i div n)))"
  proof (intro suminf_le_pos emeasure_nonneg)
    fix N
    def i \<equiv> "N div n"
    def t \<equiv> "s"
    then have "(s, t) \<in> ?R"
      by simp
    have "\<And>\<omega>. enat N < hitting_time H (s ## \<omega>) \<Longrightarrow> enat (i * n) < hitting_time H (s ## \<omega>)"
      by (metis le_add1 mod_div_equality i_def enat_ord_code(1) le_less_trans)
    then have "?M s (\<lambda>\<omega>. enat N < hitting_time H (s ## \<omega>)) \<le> ?M t (\<lambda>\<omega>. enat (i * n) < hitting_time H (t ## \<omega>))"
      unfolding t_def by (intro emeasure_mono Collect_mono) (auto simp: i_def)
    also have "\<dots> \<le> ereal (d ^ i)"
      using `(s, t) \<in> ?R`
    proof (induction i arbitrary: t)
      case 0 then show ?case
        using T.emeasure_space_1
        by (cases "t \<in> H") (simp_all add: hitting_time_Stream zero_enat_def[symmetric])
    next
      case (Suc i)
      def j \<equiv> "i * n"
      have [simp, arith]: "0 \<le> d ^ i"
        by (auto simp add: field_simps intro!: ereal_0_le_mult zero_le_power)
        
      { fix \<omega> have "enat (n + j) < hitting_time H \<omega> \<longleftrightarrow> X n \<omega> \<and> enat j < hitting_time H (sdrop n \<omega>)"
        proof (induct n arbitrary: \<omega>)
          case (Suc n) then show ?case
            by (cases \<omega>) (simp add: hitting_time_Stream eSuc_enat[symmetric] X_simps)
        qed (simp add: X_simps) }
      then have "?M t (\<lambda>\<omega>. enat (Suc i * n) < hitting_time H (t ## \<omega>))
        = ?M t (\<lambda>\<omega>. X n (t ## \<omega>) \<and> enat j < hitting_time H (sdrop n (t ## \<omega>)))"
        by (simp add: j_def)
      also have "\<dots> \<le> ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) * ereal (d ^ i)"
        using Suc.prems
      proof (induction n arbitrary: t)
        case (0 t) then show ?case
          using Suc.IH[of t] T.emeasure_space_1 `d < 1`
          by (auto simp add: X_simps hitting_time_Stream j_def)
      next
        case (Suc n s)
        show ?case
        proof cases
          assume "s \<notin> H"
          then have "?M s (\<lambda>\<omega>. X (Suc n) (s ## \<omega>) \<and> enat j < hitting_time H (sdrop (Suc n) (s ## \<omega>)))
            = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>) \<and> enat j < hitting_time H (sdrop n (t ## \<omega>))) \<partial>K s)"
            by (subst emeasure_Collect_T) (auto simp add: X_simps)
          also have "\<dots> \<le> (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) * ereal (d ^ i) \<partial>K s)"
            using `d < 1` `s \<notin> H`
            apply (intro nn_integral_mono_AE)
            apply (auto simp add: X_simps hitting_time_Stream emeasure_nonneg AE_measure_pmf_iff)
            apply (case_tac "y \<in> H")
            apply (cases n)
            apply (auto simp add: X_simps hitting_time_Stream intro!: ereal_0_le_mult) []
            apply (simp add: X_simps)
            apply (cut_tac t=y in Suc.IH[OF rtrancl_into_rtrancl[OF Suc.prems]])
            apply simp
            apply simp
            done
          also have "\<dots> = (\<integral>\<^sup>+t. ?M t (\<lambda>\<omega>. X n (t ## \<omega>)) \<partial>K s) * d ^ i"
            by (intro nn_integral_multc) auto
          also have "\<dots> = ?M s (\<lambda>\<omega>. X (Suc n) (s ## \<omega>)) * d ^ i"
            using `s \<notin>  H` by (subst (2) emeasure_Collect_T) (simp_all add: X_simps)
          finally show ?case .
        qed (simp add: X_simps)
      qed
      also have "\<dots> \<le> ereal d * d^i"
        using Suc.prems
        by (intro ereal_mult_right_mono)
           (simp_all add: T.emeasure_eq_measure d del: space_T)
      finally show ?case
        by simp
    qed
    finally show "emeasure (T s) {\<omega> \<in> space (T s). enat N < hitting_time H (s ## \<omega>)} \<le> ereal (d ^ i)" .
  qed
  also have "\<dots> < \<infinity>"
  proof cases
    assume "d = 0"
    with `1 \<le> n` have "summable (\<lambda>i. d ^ (i div n))"
      by (auto simp add: power_0_left div_eq_zero_iff)
    then show "(\<Sum>i. ereal (d ^ (i div n))) < \<infinity>"
      by (auto simp: suminf_ereal_finite)
  next
    assume "d \<noteq> 0"
    from `d < 1` `1 \<le> n` have "root n d < 1"
      by (subst real_root_lt_1_iff) simp
    with summable_geometric[of "root n d"] `0 \<le> d`
    have "summable (\<lambda>i. root n d ^ i / d)"
      by (simp add: real_root_ge_zero summable_divide)
    then have "summable (\<lambda>i. d ^ (i div n))"
    proof (rule summable_comparison_test[rotated], intro exI allI impI)
      fix i
      have "i \<le> i div n * n + n"  
        using `1 \<le> n`
        by (subst mod_div_equality[symmetric, of i n]) (intro add_mono, auto)
      then have "(d ^ (i div n) * d) ^ Suc (n - 1) \<le> (root n d ^ n) ^ i"
        using `1 \<le> n` `0 \<le> d` `d < 1` mod_div_equality[of i n]
        by (auto simp add: power_Suc2[symmetric] power_mult[symmetric] simp del: power_Suc
                 intro!: power_decreasing)
      also have "\<dots> = (root n d ^ i) ^ (Suc (n - 1))"
        using `1 \<le> n` unfolding power_mult[symmetric] by (simp add: ac_simps)
      finally have "(d ^ (i div n) * d) \<le> root n d ^ i"
        by (rule power_le_imp_le_base) (insert `0 \<le> d` `1 \<le> n`, simp)
      then show "norm (d ^ (i div n)) \<le> (root n d ^ i / d)"
        using `0 \<le> d` `d \<noteq> 0` by (simp_all add: divide_simps)
    qed
    then show "(\<Sum>i. ereal (d ^ (i div n))) < \<infinity>"
      by (auto simp: suminf_ereal_finite)
  qed
  finally show ?thesis
    by simp
qed

lemma emeasure_HLD_nxt:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (X \<cdot> P) \<omega>} =
    (\<integral>\<^sup>+x. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>} * indicator X x \<partial>K s)"
  by (subst emeasure_Collect_T)
     (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff split: split_indicator)

lemma emeasure_HLD:
  "emeasure (T s) {\<omega>\<in>space (T s). HLD X \<omega>} = emeasure (K s) X"
  using emeasure_HLD_nxt[of "\<lambda>\<omega>. True" s X] T.emeasure_space_1 by simp

lemma (in MC_syntax) emeasure_suntil_sums:
  assumes [measurable]: "Measurable.pred S \<phi>"
  assumes [measurable]: "Measurable.pred S \<psi>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (\<phi> suntil \<psi>) \<omega>} =
    (\<Sum>i. emeasure (T s) {\<omega>\<in>space (T s). ((\<lambda>R. \<phi> aand ((not \<psi>) aand (nxt R))) ^^ i) \<psi> \<omega>})"
proof -
  let ?R = "\<lambda>i \<omega>. ((\<lambda>R. \<psi> or (\<phi> aand (nxt R))) ^^ i) \<bottom> \<omega>"
  let ?L = "\<lambda>j \<omega>. ((\<lambda>R. \<phi> aand ((not \<psi>) aand (nxt R))) ^^ j) \<psi> \<omega>"
  { fix \<omega> i assume "?R i \<omega>" then have "\<exists>j<i. ?L j \<omega>"
    proof (induction i arbitrary: \<omega>)
      case (Suc i) then show ?case
        by (cases "\<not> \<psi> \<omega>") force+
    qed simp }
  moreover
  { fix \<omega> i j assume "?L j \<omega>" then have "?R (Suc j) \<omega>"
      by (induction j arbitrary: \<omega>) auto
    moreover assume "j < i"
    then have "?R (Suc j) \<le> ?R i"
      by (intro funpow_decreasing) (auto simp: mono_def)
    ultimately have "?R i \<omega>"
      by (auto simp: le_fun_def) }
  ultimately have R_eq_L: "\<And>i \<omega>. ?R i \<omega> \<longleftrightarrow> (\<exists>j<i. ?L j \<omega>)"
    by blast

  { fix m n \<omega> assume "?L m \<omega>" "?L n \<omega>"
    then have "m = n"
    proof (induction m arbitrary: \<omega> n)
      case 0 then show ?case
        by (cases n) auto
    next
      case (Suc m) then show ?case
        by (cases n) auto
    qed }
  note inj = this

  have "emeasure (T s) {\<omega>\<in>space (T s). (\<phi> suntil \<psi>) \<omega>} =
    (SUP i. emeasure (T s) {\<omega>\<in>space (T s). ?R i \<omega>})"
    unfolding bot_fun_def bot_bool_def by (intro emeasure_suntil) fact+
  also have "\<dots> = (SUP i. emeasure (T s) (\<Union>j<i. {\<omega>\<in>space (T s). ?L j \<omega>}))"
    unfolding R_eq_L by (auto intro!: SUP_cong arg_cong2[where f=emeasure])
  also have "\<dots> = (SUP i. \<Sum>j<i. emeasure (T s) {\<omega>\<in>space (T s). ?L j \<omega>})"
    apply (intro SUP_cong[OF refl] setsum_emeasure[symmetric] image_subset_iff[THEN iffD2] ballI)
    apply measurable
    apply (auto simp: disjoint_family_on_def inj)
    done
  also have "\<dots> = (\<Sum>i. emeasure (T s) {\<omega>\<in>space (T s). ?L i \<omega>})"
    by (intro suminf_ereal_eq_SUP[symmetric] emeasure_nonneg)
  finally show ?thesis .
qed

lemma emeasure_suntil_geometric:
  assumes [measurable]: "Measurable.pred S \<phi>"
  assumes [measurable]: "Measurable.pred S \<psi>"
  assumes "s \<in> X" and Y: "\<And>s. s \<in> X \<Longrightarrow> Y s \<subseteq> X" and "p < 1"
  assumes \<psi>: "\<And>s. s \<in> X \<Longrightarrow> emeasure (T s) {\<omega>\<in>space (T s). \<psi> \<omega>} = ereal r"
  assumes \<phi>: "\<And>s. s \<in> X \<Longrightarrow> AE \<omega> in T s. (((\<phi> aand not \<psi>) aand nxt \<psi>) \<omega> \<longleftrightarrow> (Y s \<cdot> \<psi>) \<omega>)"
   "\<And>s. s \<in> X \<Longrightarrow> AE \<omega> in T s. (((\<phi> aand not \<psi>) aand nxt (\<phi> aand not \<psi>)) \<omega> \<longleftrightarrow> (Y s \<cdot> (\<phi> aand not \<psi>)) \<omega>)"
  assumes p: "\<And>s. s \<in> X \<Longrightarrow> emeasure (K s) (Y s) = ereal p"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (\<phi> suntil \<psi>) \<omega>} = r / (1 - p)"
proof -
  let ?P = "\<lambda>x P. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>}"
  have nn: "0 \<le> r" "0 \<le> p"
    using p[OF `s \<in> X`, symmetric] \<psi>[OF `s \<in> X`, symmetric]
    by (auto simp: T.emeasure_eq_measure measure_pmf.emeasure_eq_measure measure_nonneg)

  let ?I = "\<lambda>n. ((\<lambda>R. \<phi> aand ((not \<psi>) aand nxt R)) ^^ n) \<psi>"
  { fix n
    from `s \<in> X` have "?P s (?I n) = p^n * r"
    proof (induction n arbitrary: s)
      case (Suc n)
      have "?P s (?I (Suc n)) = ?P s (Y s \<cdot> ?I n)"
      proof (intro emeasure_Collect_eq_AE)
        show "AE \<omega> in T s. ?I (Suc n) \<omega> \<longleftrightarrow> (Y s \<cdot> ?I n) \<omega>"
          using \<phi>[OF `s\<in>X`]
        proof eventually_elim
          fix \<omega> assume "((\<phi> aand not \<psi>) aand nxt \<psi>) \<omega> \<longleftrightarrow> (Y s \<cdot> \<psi>) \<omega>"
            "((\<phi> aand not \<psi>) aand nxt (\<phi> aand not \<psi>)) \<omega> \<longleftrightarrow> (Y s \<cdot> (\<phi> aand not \<psi>)) \<omega>"
          then show "?I (Suc n) \<omega> \<longleftrightarrow> (Y s \<cdot> ?I n) \<omega>"
            by (cases n) auto
        qed
        show "Measurable.pred (T s) (?I (Suc n))"
          by measurable simp
        show "Measurable.pred (T s) (Y s \<cdot> ?I n)"
          unfolding measurable_T1 by measurable
      qed
      also have "\<dots> = (\<integral>\<^sup>+y. ?P y (?I n) * indicator (Y s) y \<partial>K (s))"
        by (intro emeasure_HLD_nxt) measurable
      also have "\<dots> = (\<integral>\<^sup>+y. ereal (p^n * r) * indicator (Y s) y \<partial>K s)"
        using Suc Y by (intro nn_integral_cong mult_indicator_cong) auto
      also have "\<dots> = ereal (p^Suc n * r)"
        using nn Suc by (subst nn_integral_cmult_indicator) (auto simp: p)
      finally show ?case
        by simp
    qed (insert \<psi>, simp) }
  note iter = this

  have "?P s (\<phi> suntil \<psi>) = (\<Sum>n. ?P s (?I n))"
    by (subst emeasure_suntil_sums) measurable
  also have "\<dots> = (\<Sum>n. ereal (p^n * r))"
    by (subst iter) rule
  also have "\<dots> = ereal ((1 / (1 - p)) * r)"
    using `p < 1` nn by (intro sums_suminf_ereal sums_mult2 geometric_sums) auto
  finally show ?thesis
    by simp
qed

lemma emeasure_ev_sums:
  assumes [measurable]: "Measurable.pred S \<phi>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). ev \<phi> \<omega>} =
    (\<Sum>i. emeasure (T s) {\<omega>\<in>space (T s). ((\<lambda>R. (not \<phi>) aand (nxt R)) ^^ i) \<phi> \<omega>})"
  using emeasure_suntil_sums[of "\<lambda>s. True" \<phi> s] by (simp add: true_suntil)

end

lemma integrable_measure_pmf_finite:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "finite (set_pmf M) \<Longrightarrow> integrable M f"
  by (auto intro!: integrableI_bounded simp: nn_integral_measure_pmf_finite)

lemma integral_indicator_finite_real: (*TBD: generalize*)
  fixes f :: "'a \<Rightarrow> real"
  assumes [simp]: "finite A"
  assumes [measurable]: "\<And>a. a \<in> A \<Longrightarrow> {a} \<in> sets M"
  assumes finite: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} < \<infinity>"
  shows "(\<integral>x. f x * indicator A x \<partial>M) = (\<Sum>a\<in>A. f a * measure M {a})"
proof -
  have "(\<integral>x. f x * indicator A x \<partial>M) = (\<integral>x. (\<Sum>a\<in>A. f a * indicator {a} x) \<partial>M)"
  proof (intro integral_cong refl)
    fix x show "f x * indicator A x = (\<Sum>a\<in>A. f a * indicator {a} x)"
      by (auto split: split_indicator simp: eq_commute[of x] cong: conj_cong)
  qed
  also have "\<dots> = (\<Sum>a\<in>A. f a * measure M {a})"
    using finite by (subst integral_setsum) (auto simp add: integrable_mult_left_iff)
  finally show ?thesis .
qed

lemma integral_measure_pmf:
  assumes [simp]: "finite A" and "\<And>a. a \<in> set_pmf M \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> A"
  shows "(\<integral>x. f x \<partial>measure_pmf M) = (\<Sum>a\<in>A. f a * pmf M a)"
proof -
  have "(\<integral>x. f x \<partial>measure_pmf M) = (\<integral>x. f x * indicator A x \<partial>measure_pmf M)"
    using assms(2) by (intro integral_cong_AE) (auto split: split_indicator simp: AE_measure_pmf_iff)
  also have "\<dots> = (\<Sum>a\<in>A. f a * pmf M a)"
    by (subst integral_indicator_finite_real) (auto simp: measure_def emeasure_measure_pmf_finite)
  finally show ?thesis .
qed

lemma (in MC_syntax) prob_T:
  assumes P: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>t. \<P>(\<omega> in T t. P (t ## \<omega>)) \<partial>K s)"
  using emeasure_Collect_T[OF P, of s] unfolding T.emeasure_eq_measure
  by (subst (asm) nn_integral_eq_integral)
     (auto intro!: measure_pmf.integrable_const_bound[where B=1] simp: measure_nonneg)

lemma Sigma_empty_iff: "(SIGMA i:I. X i) = {} \<longleftrightarrow> (\<forall>i\<in>I. X i = {})"
  by auto

lemma borel_measurable_sup[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    (\<lambda>x. sup (f x) (g x)::ereal) \<in> borel_measurable M"
  by simp

lemma borel_measurable_lfp[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> ereal) \<Rightarrow> ('a \<Rightarrow> ereal)"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>f. f \<in> borel_measurable M \<Longrightarrow> F f \<in> borel_measurable M"
  shows "lfp F \<in> borel_measurable M"
proof -
  { fix i have "((F ^^ i) (\<lambda>t. \<bottom>)) \<in> borel_measurable M"
      by (induct i) (auto intro!: * simp: bot_fun_def) }
  then have "(\<lambda>x. SUP i. (F ^^ i) (\<lambda>t. \<bottom>) x) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. SUP i. (F ^^ i) (\<lambda>t. \<bottom>) x) = (SUP i. (F ^^ i) bot)"
    by (auto simp add: bot_fun_def)
  also have "(SUP i. (F ^^ i) bot) = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma lfp_pair:
  "lfp (\<lambda>f (a, b). F (\<lambda>a b. f (a, b)) a b) (a, b) = lfp F a b"
  unfolding lfp_def
  apply simp
  unfolding INF_def
  apply (intro arg_cong[where f=Inf])
  apply (auto simp: le_fun_def image_Collect)
  apply (rule_tac x = "\<lambda>(a, b). u a b" in exI)
  apply auto
  done

lemma SUP_ereal_add_right:
  fixes c :: ereal
  shows "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> 0 \<le> c \<Longrightarrow> (\<Squnion>i\<in>I. c + f i) = c + SUPREMUM I f"
  using SUP_ereal_add_left[of I f c] by (simp add: add_ac)

locale MC_with_rewards = MC_syntax K for K :: "'s \<Rightarrow> 's pmf" +
  fixes \<iota> :: "'s \<Rightarrow> 's \<Rightarrow> ereal" and \<rho> :: "'s \<Rightarrow> ereal"
  assumes \<iota>_nonneg: "\<And>s t. 0 \<le> \<iota> s t" and \<rho>_nonneg: "\<And>s. 0 \<le> \<rho> s"
  assumes measurable_\<iota>[measurable]: "(\<lambda>(a, b). \<iota> a b) \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"
begin

definition reward_until :: "'s set \<Rightarrow> 's \<Rightarrow> 's stream \<Rightarrow> ereal" where
  "reward_until X = lfp (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>))))"

lemma measurable_\<rho>[measurable]: "\<rho> \<in> borel_measurable (count_space UNIV)"
  by simp

lemma measurable_reward_until[measurable (raw)]:
  assumes [measurable]: "f \<in> measurable M (count_space UNIV)"
  assumes [measurable]: "g \<in> measurable M S"
  shows "(\<lambda>x. reward_until X (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>F (s, \<omega>). if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>, stl \<omega>)))"
  { fix s \<omega> 
    have "reward_until X s \<omega> = lfp ?F (s, \<omega>)"
      unfolding reward_until_def lfp_pair[symmetric] .. }
  note * = this

  have [measurable]: "lfp ?F \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
  proof (rule borel_measurable_lfp)
    show "Order_Continuity.continuous ?F"
      using \<iota>_nonneg \<rho>_nonneg
      by (auto simp: Order_Continuity.continuous_def SUP_ereal_add_right SUP_sup_distrib[symmetric]
               simp del: sup_ereal_def)
  next
    fix f :: "('s \<times> 's stream) \<Rightarrow> ereal"
    assume [measurable]: "f \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
    show "?F f \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
      unfolding split_beta'
      apply (intro measurable_If)
      apply measurable []
      apply measurable []
      apply (rule predE)
      apply (rule measurable_compose[OF measurable_fst])
      apply measurable []
      done
  qed
  show ?thesis
    unfolding * by measurable
qed

lemma continuous_reward_until:
  "Order_Continuity.continuous (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>))))"
  unfolding Order_Continuity.continuous_def
  using \<iota>_nonneg \<rho>_nonneg
  by (auto simp: fun_eq_iff SUP_ereal_add_right SUP_sup_distrib[symmetric] simp del: sup_ereal_def)

lemma
  shows reward_until_nonneg: "\<And>s \<omega>. 0 \<le> reward_until X s \<omega>"
    and reward_until_unfold: "reward_until X s \<omega> =
        (if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + reward_until X (shd \<omega>) (stl \<omega>))"
      (is ?unfold)
proof -
  let ?F = "\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (0 \<squnion> (F (shd \<omega>) (stl \<omega>)))"
  { fix s \<omega> have "reward_until X s \<omega> = ?F (reward_until X) s \<omega>"
      unfolding reward_until_def
      apply (subst lfp_unfold)
      apply (rule continuous_reward_until[THEN continuous_mono, of X])
      apply rule
      done }
  note step = this
  show "\<And>s \<omega>. 0 \<le> reward_until X s \<omega>"
    by (subst step) (auto intro!: ereal_add_nonneg_nonneg \<iota>_nonneg \<rho>_nonneg)
  then show ?unfold
    by (subst step) (auto intro!: arg_cong2[where f="op +"] split: split_max)
qed

lemma reward_until_simps[simp]:
  shows "s \<in> X \<Longrightarrow> reward_until X s \<omega> = 0"
    and "s \<notin> X \<Longrightarrow> reward_until X s \<omega> = \<rho> s + \<iota> s (shd \<omega>) + reward_until X (shd \<omega>) (stl \<omega>)"
  unfolding reward_until_unfold[of X s \<omega>] by simp_all

lemma hitting_time_simps[simp]:
  shows "shd \<omega> \<in> H \<Longrightarrow> hitting_time H \<omega> = 0"
    and "shd \<omega> \<notin> H \<Longrightarrow> hitting_time H \<omega> = eSuc (hitting_time H (stl \<omega>))"
  using hitting_time_Stream[of H "shd \<omega>" "stl \<omega>"] by auto

lemma ereal_of_enat_eSuc[simp]: "ereal_of_enat (eSuc x) = 1 + ereal_of_enat x"
  by (cases x) (auto simp: eSuc_enat)

lemma nn_integral_reward_until_finite:
  assumes [simp]: "finite ((SIGMA x:- H. K x)\<^sup>* `` {s})" (is "finite (?R `` {s})")
  assumes \<rho>: "\<And>t. (s, t) \<in> (SIGMA x:- H. set_pmf (K x) - H)\<^sup>* \<Longrightarrow> \<rho> t < \<infinity>"
  assumes \<iota>: "\<And>t t'. (s, t) \<in> (SIGMA x:- H. set_pmf (K x) - H)\<^sup>* \<Longrightarrow> t' \<in> K t \<Longrightarrow> \<iota> t t' < \<infinity>"
  assumes ev: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. reward_until H s \<omega> \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by simp
next
  assume "s \<notin>  H"
  let ?L = "(SIGMA x:- H. set_pmf (K x) - H)\<^sup>*"
  def M \<equiv> "Max ((\<lambda>(s, t). \<rho> s + \<iota> s t) ` (SIGMA t:?L``{s}. K t))"
  have "?L \<subseteq> ?R"
    by (intro rtrancl_mono) auto
  with `s \<notin> H` have subset: "(SIGMA t:?L``{s}. K t) \<subseteq> (?R``{s} \<times> ?R``{s})"
    by (auto intro: rtrancl_into_rtrancl elim: rtrancl.cases)
  then have [simp, intro!]: "finite ((\<lambda>(s, t). \<rho> s + \<iota> s t) ` (SIGMA t:?L``{s}. K t))"
    by (intro finite_imageI) (auto dest: finite_subset)
  { fix t t' assume "(s, t) \<in> ?L" "t \<notin> H" "t' \<in> K t"
    then have "(t, t') \<in> (SIGMA t:?L``{s}. K t)"
      by (auto intro: rtrancl_into_rtrancl)
    then have "\<rho> t + \<iota> t t' \<le> M"
      unfolding M_def by (intro Max_ge) auto }
  note le_M = this

  have fin_L: "finite (?L `` {s})"
    by (intro finite_subset[OF _ assms(1)] Image_mono `?L \<subseteq> ?R` order_refl)

  have "M < \<infinity>"
    unfolding M_def
  proof (subst Max_less_iff, safe)
    show "(SIGMA x:?L `` {s}. set_pmf (K x)) = {} \<Longrightarrow> False"
      using `s \<notin> H` by (auto simp add: Sigma_empty_iff set_pmf_not_empty)
    fix t t' assume "(s, t) \<in> ?L" "t' \<in> K t" then show "\<rho> t + \<iota> t t' < \<infinity>"
      using \<rho>[of t] \<iota>[of t t'] by simp
  qed

  from set_pmf_not_empty[of "K s"] obtain t where "t \<in> K s"
    by auto
  with le_M[of s t] have "0 \<le> M"
    using set_pmf_not_empty[of "K s"] `s \<notin> H` le_M[of s] \<iota>_nonneg[of s] \<rho>_nonneg[of s]
    by (intro order_trans[OF _ le_M]) auto

  have "AE \<omega> in T s. reward_until H s \<omega> \<le> M * hitting_time H (s ## \<omega>)"
    using ev AE_T_enabled
  proof eventually_elim
    fix \<omega> assume "ev (HLD H) \<omega>" "enabled s \<omega>"
    moreover def t\<equiv>"s"
    ultimately have "ev (HLD H) \<omega>" "enabled t \<omega>" "t \<in> ?L``{s}"
      by auto
    then show "reward_until H t \<omega> \<le> M * hitting_time H (t ## \<omega>)"
    proof (induction arbitrary: t rule: ev_induct_strong)
      case (base \<omega> t) then show ?case
        by (auto simp: HLD_iff hitting_time_Stream elim: enabled.cases intro: le_M)
    next
      case (step \<omega> t) from step.IH[of "shd \<omega>"] step.prems step.hyps show ?case
        by (auto simp add: HLD_iff enabled.simps[of t] ereal_right_distrib hitting_time_Stream
                           reward_until_simps[of t]
                 simp del: reward_until_simps hitting_time_simps
                 intro!: ereal_add_mono le_M intro: rtrancl_into_rtrancl)
    qed
  qed
  then have "(\<integral>\<^sup>+\<omega>. reward_until H s \<omega> \<partial>T s) \<le> (\<integral>\<^sup>+\<omega>. M * hitting_time H (s ## \<omega>) \<partial>T s)"
    by (rule nn_integral_mono_AE)
  also have "\<dots> < \<infinity>"
    using `0 \<le> M` `M < \<infinity>` nn_integral_hitting_time_finite[OF fin_L ev]
    by (simp add: nn_integral_cmult not_less nn_integral_nonneg)
  finally show ?thesis
    by simp
qed

end

lemma (in MC_syntax) enabled_imp_alw:
  "(\<Union>s\<in>X. K s) \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> enabled x \<omega> \<Longrightarrow> alw (HLD X) \<omega>"
proof (coinduction arbitrary: \<omega> x)
  case alw then show ?case
    unfolding enabled.simps[of _ \<omega>]
    by (auto simp: HLD_iff)
qed

lemma (in MC_syntax) alw_HLD_iff_sconst:
  "alw (HLD {x}) \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "alw (HLD {x}) \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto simp: HLD_iff)
qed (auto simp: alw_sconst HLD_iff)

lemma (in MC_syntax) enabled_iff_sconst:
  assumes [simp]: "set_pmf (K x) = {x}" shows "enabled x \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "enabled x \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto elim: enabled.cases)
next
  assume "\<omega> = sconst x" then show "enabled x \<omega>"
    by (coinduction arbitrary: \<omega>) auto
qed

lemma (in MC_syntax) AE_sconst:
  assumes [simp]: "set_pmf (K x) = {x}"
  shows "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> P (sconst x)"
proof -
  have "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> (AE \<omega> in T x. P \<omega> \<and> \<omega> = sconst x)"
    using AE_T_enabled[of x] by (simp add: enabled_iff_sconst)
  also have "\<dots> = (AE \<omega> in T x. P (sconst x) \<and> \<omega> = sconst x)"
    by (simp del: AE_conj_iff cong: rev_conj_cong)
  also have "\<dots> = (AE \<omega> in T x. P (sconst x))"
    using AE_T_enabled[of x] by (simp add: enabled_iff_sconst)
  finally show ?thesis
    by simp
qed

end

