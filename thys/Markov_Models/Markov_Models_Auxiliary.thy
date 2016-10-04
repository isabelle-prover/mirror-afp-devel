(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Auxiliary definitions and theorems for Markov models *}

text \<open>Parts of it should be moved to the Isabelle repository\<close>

theory Markov_Models_Auxiliary
imports
  "~~/src/HOL/Probability/Probability"
  "~~/src/HOL/Library/Rewrite"
  "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
  "../Coinductive/Coinductive_Stream"
  "../Coinductive/Coinductive_Nat"
begin

instance nat :: second_countable_topology
proof
  show "\<exists>B::nat set set. countable B \<and> open = generate_topology B"
    by (intro exI[of _ "range lessThan \<union> range greaterThan"]) (auto simp: open_nat_def)
qed

definition "with P f d = (if \<exists>x. P x then f (SOME x. P x) else d)"

lemma withI[case_names default exists]:
  "((\<And>x. \<not> P x) \<Longrightarrow> Q d) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q (f x)) \<Longrightarrow> Q (with P f d)"
  unfolding with_def by (auto intro: someI2)

lemma pigeonhole_stream:
  assumes "alw (HLD s) \<omega>"
  assumes "finite s"
  shows "\<exists>x\<in>s. alw (ev (HLD {x})) \<omega>"
proof -
  have "\<forall>i\<in>UNIV. \<exists>x\<in>s. \<omega> !! i = x"
    using `alw (HLD s) \<omega>` by (simp add: alw_iff_sdrop HLD_iff)
  from pigeonhole_infinite_rel[OF infinite_UNIV_nat `finite s` this]
  show ?thesis
    by (simp add: HLD_iff infinite_iff_alw_ev[symmetric])
qed

lemma inf_continuous_suntil_disj[order_continuous_intros]:
  assumes Q: "inf_continuous Q"
  assumes disj: "\<And>x \<omega>. \<not> (P \<omega> \<and> Q x \<omega>)"
  shows "inf_continuous (\<lambda>x. P suntil Q x)"
  unfolding inf_continuous_def
proof (safe intro!: ext)
  fix M \<omega> i assume "(P suntil Q (\<Sqinter>i. M i)) \<omega>" "decseq M" then show "(P suntil Q (M i)) \<omega>"
    unfolding inf_continuousD[OF Q `decseq M`] by induction (auto intro: suntil.intros)
next
  fix M \<omega> assume *: "(\<Sqinter>i. P suntil Q (M i)) \<omega>" "decseq M"
  then have "(P suntil Q (M 0)) \<omega>"
    by auto
  from this * show "(P suntil Q (\<Sqinter>i. M i)) \<omega>"
    unfolding inf_continuousD[OF Q `decseq M`]
  proof induction
    case (base \<omega>) with disj[of \<omega> "M _"] show ?case by (auto intro: suntil.intros elim: suntil.cases)
  next
    case (step \<omega>) with disj[of \<omega> "M _"] show ?case by (auto intro: suntil.intros elim: suntil.cases)
  qed
qed

lemma inf_continuous_nxt[order_continuous_intros]: "inf_continuous P \<Longrightarrow> inf_continuous (\<lambda>x. nxt (P x) \<omega>)"
  by (auto simp: inf_continuous_def)

lemma sup_continuous_nxt[order_continuous_intros]: "sup_continuous P \<Longrightarrow> sup_continuous (\<lambda>x. nxt (P x) \<omega>)"
  by (auto simp: sup_continuous_def)

lemma ev_eq_suntil: "ev P \<omega> \<longleftrightarrow> (not P suntil P) \<omega>"
proof
  assume "ev P \<omega>" then show "((\<lambda>xs. \<not> P xs) suntil P) \<omega>"
    by (induction rule: ev_induct_strong) (auto intro: suntil.intros)
qed (auto simp: ev_suntil)

lemma mcont_ennreal_of_enat: "mcont Sup (op \<le>) Sup op \<le> ennreal_of_enat"
  by (auto intro!: mcontI monotoneI contI ennreal_of_enat_Sup)

lemma mcont2mcont_ennreal_of_enat[cont_intro]:
  "mcont lub ord Sup op \<le> f \<Longrightarrow> mcont lub ord Sup op \<le> (\<lambda>x. ennreal_of_enat (f x))"
  by (auto intro: ccpo.mcont2mcont[OF complete_lattice_ccpo'] mcont_ennreal_of_enat)

declare stream.exhaust[cases type: stream]

lemma lfp_pair: "lfp (\<lambda>f (a, b). F (\<lambda>a b. f (a, b)) a b) (a, b) = lfp F a b"
  unfolding lfp_def
  by (auto intro!: INF_eq simp: le_fun_def)
     (auto intro!: exI[of _ "\<lambda>(a, b). x a b" for x])

lemma all_Suc_split: "(\<forall>i. P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i. P (Suc i)))"
  using nat_induct by auto

lemma scount_eq_emeasure: "scount P \<omega> = emeasure (count_space UNIV) {i. P (sdrop i \<omega>)}"
proof cases
  assume "alw (ev P) \<omega>"
  moreover then have "infinite {i. P (sdrop i \<omega>)}"
    using infinite_iff_alw_ev[of P \<omega>] by simp
  ultimately show ?thesis
    by (simp add: scount_infinite_iff[symmetric])
next
  assume "\<not> alw (ev P) \<omega>"
  moreover then have "finite {i. P (sdrop i \<omega>)}"
    using infinite_iff_alw_ev[of P \<omega>] by simp
  ultimately show ?thesis
    by (simp add: not_alw_iff not_ev_iff scount_eq_card)
qed

lemma measurable_scount[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "scount P \<in> measurable (stream_space M) (count_space UNIV)"
  unfolding scount_eq[abs_def] by measurable

lemma measurable_sfirst[measurable]:
  assumes "Measurable.pred (stream_space M) P"
  shows "sfirst P \<in> measurable (stream_space M) (count_space UNIV)"
  apply (coinduction rule: measurable_enat_coinduct)
  apply simp
  apply (rule exI[of _ "\<lambda>x. 0"])
  apply (rule exI[of _ stl])
  apply (rule exI[of _ P])
  apply (subst sfirst.simps[abs_def])
  apply simp
  apply fact
  done


context order
begin

definition
  "maximal f S = {x\<in>S. \<forall>y\<in>S. f y \<le> f x}"

lemma maximalI: "x \<in> S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> f y \<le> f x) \<Longrightarrow> x \<in> maximal f S"
  by (simp add: maximal_def)

lemma maximalI_trans: "x \<in> maximal f S \<Longrightarrow> f x \<le> f y \<Longrightarrow> y \<in> S \<Longrightarrow> y \<in> maximal f S"
  unfolding maximal_def by (blast intro: antisym order_trans)

lemma maximalD1: "x \<in> maximal f S \<Longrightarrow> x \<in> S"
  by (simp add: maximal_def)

lemma maximalD2: "x \<in> maximal f S \<Longrightarrow> y \<in> S \<Longrightarrow> f y \<le> f x"
  by (simp add: maximal_def)

lemma maximal_inject: "x \<in> maximal f S \<Longrightarrow> y \<in> maximal f S \<Longrightarrow> f x = f y"
  unfolding maximal_def by (blast intro: antisym)

lemma maximal_empty[simp]: "maximal f {} = {}"
  by (simp add: maximal_def)

lemma maximal_singleton[simp]: "maximal f {x} = {x}"
  by (auto simp add: maximal_def)

lemma maximal_in_S: "maximal f S \<subseteq> S"
  by (auto simp: maximal_def)

end

context linorder
begin

lemma maximal_ne:
  assumes "finite S" "S \<noteq> {}"
  shows "maximal f S \<noteq> {}"
  using assms
proof (induct rule: finite_ne_induct)
  case (insert s S)
  show ?case
  proof cases
    assume "\<forall>x\<in>S. f x \<le> f s"
    with insert have "s \<in> maximal f (insert s S)"
      by (auto intro!: maximalI)
    then show ?thesis
      by auto
  next
    assume "\<not> (\<forall>x\<in>S. f x \<le> f s)"
    then have "maximal f (insert s S) = maximal f S"
      by (auto simp: maximal_def)
    with insert show ?thesis
      by auto
  qed
qed simp

end

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
          by (auto intro: M2 M3 pmf_positive)

        have "\<Delta> s \<le> ((\<integral>t. l2 t \<partial>K s) + c s) - ((\<integral>t. l1 t \<partial>K s) + c s)"
          unfolding \<Delta>_def using `s \<in> S` `s \<notin> N` by (intro diff_mono l1 l2) auto
        then have "\<Delta> s \<le> (\<integral>s'. \<Delta> s' \<partial>K s)"
          using `s \<in> S` by (simp add: \<Delta>_def)
        also have "\<dots> < (\<integral>s'. \<Delta> s \<partial>K s)"
          using `s' \<in> K s` `\<Delta> s' < \<Delta> s` `s\<in>S` S `s\<in>M`
          by (intro measure_pmf.integral_less_AE[where A="{s'}"])
             (auto simp: emeasure_measure_pmf_finite AE_measure_pmf_iff set_pmf_iff[symmetric]
                   intro!: M2)
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

lemma lfp_upperbound: "(\<And>y. x \<le> f y) \<Longrightarrow> x \<le> lfp f"
  unfolding lfp_def by (intro Inf_greatest) (auto intro: order_trans)

lemma enn2real_eq_1_iff[simp]: "enn2real x = 1 \<longleftrightarrow> x = 1"
  by (cases x) auto

lemma sets_sstart[measurable]: "sstart \<Omega> xs \<in> sets (stream_space (count_space UNIV))"
proof (induction xs)
  case (Cons x xs)
  note this[measurable]
  have "sstart \<Omega> (x # xs) = {\<omega>\<in>space (stream_space (count_space UNIV)). \<omega> \<in> sstart \<Omega> (x # xs)}"
    by (auto simp: space_stream_space)
  also have "\<dots> \<in> sets (stream_space (count_space UNIV))"
    unfolding in_sstart by measurable
  finally show ?case .
qed (auto intro!: streams_sets)

lemma measurable_SUP2:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f \<in> measurable N (M i)) \<Longrightarrow>
    (\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> space (M i) = space (M j)) \<Longrightarrow> f \<in> measurable N (SUP i:I. M i)"
  by (auto intro!: measurable_Sup2)

lemma sets_borel_eq_count_space: "sets (borel :: 'a::{countable, t2_space} measure) = count_space UNIV"
proof -
  have "(\<Union>a\<in>A. {a}) \<in> sets borel" for A :: "'a set"
    by (intro sets.countable_UN') auto
  then show ?thesis
    by auto
qed

lemma streams_empty_iff: "streams S = {} \<longleftrightarrow> S = {}"
proof safe
  fix x assume "x \<in> S" "streams S = {}"
  then have "sconst x \<in> streams S"
    by (intro sconst_streams)
  then show "x \<in> {}"
    unfolding \<open>streams S = {}\<close> by simp
qed (auto simp: streams_empty)

lemma measurable_case_enat[measurable (raw)]:
  assumes f: "f \<in> M \<rightarrow>\<^sub>M count_space UNIV" and g: "\<And>i. g i \<in> M \<rightarrow>\<^sub>M N" and h: "h \<in> M \<rightarrow>\<^sub>M N"
  shows "(\<lambda>x. case f x of enat i \<Rightarrow> g i x | \<infinity> \<Rightarrow> h x) \<in> M \<rightarrow>\<^sub>M N"
  apply (rule measurable_compose_countable[OF _ f])
  subgoal for i
    by (cases i) (auto intro: g h)
  done

lemma measurable_epred[measurable]: "epred \<in> count_space UNIV \<rightarrow>\<^sub>M count_space UNIV"
  by (rule measurable_count_space)

lemma distr_id2: "sets M = sets N \<Longrightarrow> distr N M (\<lambda>x. x) = N"
  by (rule measure_eqI) (auto simp: emeasure_distr)

lemma bind_distr_return:
  "f \<in> M \<rightarrow>\<^sub>M N \<Longrightarrow> g \<in> N \<rightarrow>\<^sub>M L \<Longrightarrow> space M \<noteq> {} \<Longrightarrow>
    distr M N f \<bind> (\<lambda>x. return L (g x)) = distr M L (\<lambda>x. g (f x))"
  by (subst bind_distr[OF _ measurable_compose[OF _ return_measurable]])
     (auto intro!: bind_return_distr')

instance enat :: second_countable_topology
proof
  show "\<exists>B::enat set set. countable B \<and> open = generate_topology B"
  proof (intro exI conjI)
    show "countable (range lessThan \<union> range greaterThan::enat set set)"
      by auto
  qed (simp add: open_enat_def)
qed

(* ?? *)
lemma lfp_arg: "(\<lambda>t. lfp (F t)) = lfp (\<lambda>x t. F t (x t))"
  apply (auto simp: lfp_def le_fun_def fun_eq_iff intro!: Inf_eqI Inf_greatest)
  subgoal for x y
    by (rule INF_lower2[of "top(x := y)"]) auto
  done

(* Markov_Models? *)

lemma measurable_sfirst2:
  assumes [measurable]: "Measurable.pred (N \<Otimes>\<^sub>M stream_space M) (\<lambda>(x, \<omega>). P x \<omega>)"
  shows "(\<lambda>(x, \<omega>). sfirst (P x) \<omega>) \<in> measurable (N \<Otimes>\<^sub>M  stream_space M) (count_space UNIV)"
  apply (coinduction rule: measurable_enat_coinduct)
  apply simp
  apply (rule exI[of _ "\<lambda>x. 0"])
  apply (rule exI[of _ "\<lambda>(x, \<omega>). (x, stl \<omega>)"])
  apply (rule exI[of _ "\<lambda>(x, \<omega>). P x \<omega>"])
  apply (subst sfirst.simps[abs_def])
  apply (simp add: fun_eq_iff)
  done

lemma measurable_sfirst2'[measurable (raw)]:
  "f \<in> N \<rightarrow>\<^sub>M stream_space M \<Longrightarrow> Measurable.pred (N \<Otimes>\<^sub>M stream_space M) (\<lambda>x. P (fst x) (snd x)) \<Longrightarrow>
    (\<lambda>x. sfirst (P x) (f x)) \<in> measurable N (count_space UNIV)"
  using measurable_sfirst2[measurable]
  apply measurable
  apply assumption
  apply measurable
  apply assumption
  done

end