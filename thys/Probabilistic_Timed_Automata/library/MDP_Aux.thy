(* Back ported from AFP's development version *)

theory MDP_Aux
  imports "Markov_Models.Markov_Decision_Process"
begin


lemma sstart_eq': "sstart \<Omega> (x # xs) = {\<omega>. shd \<omega> = x \<and> stl \<omega> \<in> sstart \<Omega> xs}"
  by (auto simp: sstart_eq)

lemma measure_eq_stream_space_coinduct[consumes 1, case_names left right cont]:
  assumes "R N M"
  assumes R_1: "\<And>N M. R N M \<Longrightarrow> N \<in> space (prob_algebra (stream_space (count_space UNIV)))"
    and R_2: "\<And>N M. R N M \<Longrightarrow> M \<in> space (prob_algebra (stream_space (count_space UNIV)))"
    and cont: "\<And>N M. R N M \<Longrightarrow> \<exists>N' M' p. (\<forall>y\<in>set_pmf p. R (N' y) (M' y)) \<and>
      (\<forall>x. N' x \<in> space (prob_algebra (stream_space (count_space UNIV)))) \<and> (\<forall>x. M' x \<in> space (prob_algebra (stream_space (count_space UNIV)))) \<and> 
      N = (measure_pmf p \<bind> (\<lambda>y. distr (N' y) (stream_space (count_space UNIV)) ((op ##) y))) \<and>
      M = (measure_pmf p \<bind> (\<lambda>y. distr (M' y) (stream_space (count_space UNIV)) ((op ##) y)))"
  shows "N = M"
proof -
  let ?S = "stream_space (count_space UNIV)"
  have "\<forall>N M. R N M \<longrightarrow> (\<exists>N' M' p. (\<forall>y\<in>set_pmf p. R (N' y) (M' y)) \<and>
      (\<forall>x. N' x \<in> space (prob_algebra ?S)) \<and> (\<forall>x. M' x \<in> space (prob_algebra ?S)) \<and>
      N = (measure_pmf p \<bind> (\<lambda>y. distr (N' y) ?S ((op ##) y))) \<and>
      M = (measure_pmf p \<bind> (\<lambda>y. distr (M' y) ?S ((op ##) y))))"
    using cont by auto
  then obtain n m p where
    p: "\<And>N M y. R N M \<Longrightarrow> y \<in> set_pmf (p N M) \<Longrightarrow> R (n N M y) (m N M y)" and
    n: "\<And>N M x. R N M \<Longrightarrow> n N M x \<in> space (prob_algebra ?S)" and
    n_eq: "\<And>N M y. R N M \<Longrightarrow> N = (measure_pmf (p N M) \<bind> (\<lambda>y. distr (n N M y) ?S ((op ##) y)))" and
    m: "\<And>N M x. R N M \<Longrightarrow> m N M x \<in> space (prob_algebra ?S)" and
    m_eq: "\<And>N M y. R N M \<Longrightarrow> M = (measure_pmf (p N M) \<bind> (\<lambda>y. distr (m N M y) ?S ((op ##) y)))"
    unfolding choice_iff' choice_iff by blast

  define A where "A = (SIGMA nm:UNIV. (\<lambda>x. (n (fst nm) (snd nm) x, m (fst nm) (snd nm) x)) ` p (fst nm) (snd nm))"
  have A_singleton: "A `` {nm} = (\<lambda>x. (n (fst nm) (snd nm) x, m (fst nm) (snd nm) x)) ` p (fst nm) (snd nm)" for nm
    by (auto simp: A_def)

  have sets_n[measurable_cong, simp]: "sets (n N M y) = sets ?S" if "R N M" for N M y
    using n[OF that, of y] by (auto simp: space_prob_algebra)
  have sets_m[measurable_cong, simp]: "sets (m N M y) = sets ?S" if "R N M" for N M y
    using m[OF that, of y] by (auto simp: space_prob_algebra)
  have [simp]: "R N M \<Longrightarrow> prob_space (n N M y)" for N M y
    using n[of N M y] by (auto simp: space_prob_algebra)
  have [simp]: "R N M \<Longrightarrow> prob_space (m N M y)" for N M y
    using m[of N M y] by (auto simp: space_prob_algebra)
  have [measurable]: "R N M \<Longrightarrow> n N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    by (rule measurable_prob_algebraD) (auto intro: n)
  have [measurable]: "R N M \<Longrightarrow> m N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    by (rule measurable_prob_algebraD) (auto intro: m)

  define n' where "n' N M y = distr (n N M y) ?S ((op ##) y)" for N M y
  define m' where "m' N M y = distr (m N M y) ?S ((op ##) y)" for N M y
  have n'_eq: "R N M \<Longrightarrow> N = (measure_pmf (p N M) \<bind> n' N M)" for N M unfolding n'_def by (rule n_eq)
  have m'_eq: "R N M \<Longrightarrow> M = (measure_pmf (p N M) \<bind> m' N M)" for N M unfolding m'_def by (rule m_eq)
  have [measurable]: "R N M \<Longrightarrow> n' N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    unfolding n'_def by (rule measurable_distr2[where M="?S"]) measurable
  have [measurable]: "R N M \<Longrightarrow> m' N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    unfolding m'_def by (rule measurable_distr2[where M="?S"]) measurable

  have n'_shd: "R N M \<Longrightarrow> distr (n' N M y) (count_space UNIV) shd = measure_pmf (return_pmf y)" for N M y
    unfolding n'_def by (subst distr_distr) (auto simp: comp_def prob_space.distr_const return_pmf.rep_eq)
  have m'_shd: "R N M \<Longrightarrow> distr (m' N M y) (count_space UNIV) shd = measure_pmf (return_pmf y)" for N M y
    unfolding m'_def by (subst distr_distr) (auto simp: comp_def prob_space.distr_const return_pmf.rep_eq)
  have n'_stl: "R N M \<Longrightarrow> distr (n' N M y) ?S stl = n N M y" for N M y
    unfolding n'_def by (subst distr_distr) (auto simp: comp_def distr_id2)
  have m'_stl: "R N M \<Longrightarrow> distr (m' N M y) ?S stl = m N M y" for N M y
    unfolding m'_def by (subst distr_distr) (auto simp: comp_def distr_id2)

  define F where "F = (A\<^sup>* `` {(N, M)})"
  have "countable F"
    unfolding F_def
    apply (intro countable_rtrancl countable_insert[of _ "(N, M)"] countable_empty)
    apply (rule countable_Image)
     apply (auto simp: A_singleton)
    done
  have F_NM[simp]: "(N, M) \<in> F" unfolding F_def by auto
  have R_F[simp]: "R N' M'" if "(N', M') \<in> F" for N' M'
  proof -
    have "((N, M), (N', M')) \<in> A\<^sup>*" using that by (auto simp: F_def)
    then show "R N' M'"
      by (induction p=="(N', M')" arbitrary: N' M' rule: rtrancl_induct) (auto simp: \<open>R N M\<close> A_def p)
  qed
  have nm_F: "(n N' M' y, m N' M' y) \<in> F" if "y \<in> p N' M'" "(N', M') \<in> F" for N' M' y
  proof -
    have *: "((N, M), (N', M')) \<in> A\<^sup>*" using that by (auto simp: F_def)
    with that show ?thesis
      apply (simp add: F_def)
      apply (intro rtrancl.rtrancl_into_rtrancl[OF *])
      apply (auto simp: A_def)
      done
  qed

  define \<Omega> where "\<Omega> = (\<Union>(n, m)\<in>F. p n m)"
  have [measurable]: "\<Omega> \<in> sets (count_space UNIV)" by auto
  have in_\<Omega>: "(N, M) \<in> F \<Longrightarrow> y \<in> p N M \<Longrightarrow> y \<in> \<Omega>" for N M y
    by (auto simp: \<Omega>_def Bex_def)

  show ?thesis
  proof (intro stream_space_eq_sstart)
    show "countable \<Omega>"
      unfolding \<Omega>_def by (intro countable_UN countable_set_pmf) fact
    show "prob_space N" "prob_space M" "sets N = sets ?S" "sets M = sets ?S"
      using R_1[OF \<open>R N M\<close>] R_2[OF \<open>R N M\<close>] by (auto simp add: space_prob_algebra)
    have "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in N. x !! i \<in> \<Omega>" for i
    proof (induction i)
      case 0 note NM = 0[THEN R_F, simp] show ?case
        apply (subst n'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=shd and M'="count_space UNIV"]
                    simp: AE_measure_pmf_iff n[OF NM] n'_shd in_\<Omega>[OF 0] cong: AE_cong_strong)
        done
    next
      case (Suc i) note NM = Suc(2)[THEN R_F, simp]
      show ?case
        apply (subst n'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=stl and M'="?S"] Suc(1)[OF nm_F] Suc(2)
          simp: AE_measure_pmf_iff n'_stl cong: AE_cong_strong)
        done
    qed
    then have AE_N: "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in N. x \<in> streams \<Omega>"
      unfolding streams_iff_snth AE_all_countable by auto
    then show "AE x in N. x \<in> streams \<Omega>" by (blast intro: F_NM)

    have "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in M. x !! i \<in> \<Omega>" for i
    proof (induction i arbitrary: N M)
      case 0 note NM = 0[THEN R_F, simp] show ?case
        apply (subst m'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=shd and M'="count_space UNIV"]
                    simp: AE_measure_pmf_iff m[OF NM] m'_shd in_\<Omega>[OF 0] cong: AE_cong_strong)
        done
    next
      case (Suc i) note NM = Suc(2)[THEN R_F, simp]
      show ?case
        apply (subst m'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=stl and M'="?S"] Suc(1)[OF nm_F] Suc(2)
          simp: AE_measure_pmf_iff m'_stl cong: AE_cong_strong)
        done
    qed
    then have AE_M: "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in M. x \<in> streams \<Omega>"
      unfolding streams_iff_snth AE_all_countable by auto
    then show "AE x in M. x \<in> streams \<Omega>" by (blast intro: F_NM)

    fix xs assume "xs \<in> lists \<Omega>"
    with \<open>(N, M) \<in> F\<close> show "emeasure N (sstart \<Omega> xs) = emeasure M (sstart \<Omega> xs)"
    proof (induction xs arbitrary: N M)
      case Nil
      have "prob_space N" "prob_space M" "sets N = sets ?S" "sets M = sets ?S"
        using R_1[OF R_F[OF Nil(1)]] R_2[OF R_F[OF Nil(1)]] by (auto simp add: space_prob_algebra)
      have "emeasure N (streams \<Omega>) = 1"
        by (rule prob_space.emeasure_eq_1_AE[OF \<open>prob_space N\<close> _ AE_N[OF Nil(1)]])
           (auto simp add: \<open>sets N = sets ?S\<close> intro!: streams_sets)
      moreover have "emeasure M (streams \<Omega>) = 1"
        by (rule prob_space.emeasure_eq_1_AE[OF \<open>prob_space M\<close> _ AE_M[OF Nil(1)]])
           (auto simp add: \<open>sets M = sets ?S\<close> intro!: streams_sets)
      ultimately show ?case by simp
    next
      case (Cons x xs)
      note NM = Cons(2)[THEN R_F, simp]
      have *: "(op ##) y -` sstart \<Omega> (x # xs) = (if x = y then sstart \<Omega> xs else {})" for y
        by auto
      show ?case
        apply (subst n'_eq[OF NM])
        apply (subst (3) m'_eq[OF NM])
        apply (subst emeasure_bind[OF _ _ sstart_sets])
          apply simp []
         apply measurable []
        apply (subst emeasure_bind[OF _ _ sstart_sets])
          apply simp []
         apply measurable []
        apply (intro nn_integral_cong_AE AE_pmfI)
        apply (subst n'_def)
        apply (subst m'_def)
        using Cons(3)
        apply (auto intro!: Cons nm_F
          simp add: emeasure_distr sets_eq_imp_space_eq[OF sets_n] sets_eq_imp_space_eq[OF sets_m]
                    space_stream_space *)
        done
    qed
  qed
qed

lemma ev_eq_lfp: "ev P = lfp (\<lambda>F \<omega>. P \<omega> \<or> (\<not> P \<omega> \<and> F (stl \<omega>)))"
  unfolding ev_def by (intro antisym lfp_mono) blast+

lemma INF_eq_zero_iff_ennreal: "((\<Sqinter>i\<in>A. f i) = (0::ennreal)) = (\<forall>x>0. \<exists>i\<in>A. f i < x)"
  using INF_eq_bot_iff[where 'a=ennreal] unfolding bot_ennreal_def zero_ennreal_def by auto

lemma inf_continuous_cmul: 
  fixes c :: ennreal
  assumes f: "inf_continuous f" and c: "c < \<top>" 
  shows "inf_continuous (\<lambda>x. c * f x)"
proof (rule inf_continuous_compose[OF _ f], clarsimp simp add: inf_continuous_def)
  fix M :: "nat \<Rightarrow> ennreal" assume M: "decseq M" 
  show "c * (\<Sqinter>i. M i) = (\<Sqinter>i. c * M i)"
    using M
    by (intro LIMSEQ_unique[OF ennreal_tendsto_cmult[OF c] LIMSEQ_INF] LIMSEQ_INF)
       (auto simp: decseq_def mult_left_mono)
qed

lemma (in MC_syntax) AE_T_ev_HLD_infinite:
  fixes X :: "'s set" and r :: real
  assumes "r < 1"
  assumes r: "\<And>x. x \<in> X \<Longrightarrow> measure (K x) X \<le> r"
  shows "AE \<omega> in T x. ev (HLD (- X)) \<omega>"
proof -
  { fix x assume "x \<in> X"
    have "0 \<le> r" using r[OF \<open>x \<in> X\<close>] measure_nonneg[of "K x" X] by (blast  intro: order.trans)
    define P where "P F x = \<integral>\<^sup>+y. indicator X y * (F y \<sqinter> 1) \<partial>K x" for F x
    have [measurable]: "X \<in> sets (count_space UNIV)" by auto
    have bnd: "(\<integral>\<^sup>+ y. indicator X y * (f y \<sqinter> 1) \<partial>K x) \<le> 1" for x f
      by (intro measure_pmf.nn_integral_le_const AE_pmfI) (auto split: split_indicator)
    have "emeasure (T x) {\<omega>\<in>space (T x). alw (HLD X) \<omega>} =
      emeasure (T x) {\<omega>\<in>space (T x). gfp (\<lambda>F \<omega>. shd \<omega> \<in> X \<and> F (stl \<omega>)) \<omega>}"
      by (simp add: alw_def HLD_def)
    also have "\<dots> = gfp P x"
      apply (rule emeasure_gfp)
      apply (auto intro!: order_continuous_intros inf_continuous_cmul split: split_indicator simp: P_def)
      subgoal for x f using bnd[of x f] by (auto simp: top_unique)
      subgoal for P x
        apply (subst T_eq_bind)
        apply (subst emeasure_bind[where N=S])
        apply simp
        apply (rule measurable_distr2[where M=S])
        apply (auto intro: T_subprob[THEN measurable_space] intro!: nn_integral_cong_AE AE_pmfI
            simp: emeasure_distr split: split_indicator)
        apply (simp_all add: space_stream_space T.emeasure_le_1 inf.absorb1)
        done
      apply (intro le_funI)
      apply (subst nn_integral_indicator[symmetric])
      apply simp
      apply (intro nn_integral_mono)
      apply (auto split: split_indicator)
      done
    also have "\<dots> \<le> (INF n. ennreal r ^ n)"
    proof (intro INF_greatest)
      have mono_P: "mono P"
        by (force simp: le_fun_def mono_def P_def intro!: nn_integral_mono intro: le_infI1 split: split_indicator)
      fix n show "gfp P x \<le> ennreal r ^ n"
        using \<open>x \<in> X\<close>
      proof (induction n arbitrary: x)
        case 0 then show ?case
          by (subst gfp_unfold[OF mono_P]) (auto intro!: measure_pmf.nn_integral_le_const AE_pmfI split: split_indicator simp: P_def)
      next
        case (Suc n x)
        have "gfp P x = P (gfp P) x" by (subst gfp_unfold[OF mono_P]) rule
        also have "\<dots> \<le> P (\<lambda>x. ennreal r ^ n) x"
          unfolding P_def[of _ x] by (auto intro!: nn_integral_mono le_infI1 Suc split: split_indicator)
        also have "\<dots> \<le> ennreal r ^ (Suc n)"
          using Suc by (auto simp: P_def nn_integral_multc measure_pmf.emeasure_eq_measure intro!: mult_mono ennreal_leI r)
        finally show ?case .
      qed
    qed
    also have "\<dots> = 0"
      unfolding ennreal_power[OF \<open>0 \<le> r\<close>]
    proof (intro LIMSEQ_unique[OF LIMSEQ_INF])
      show "decseq (\<lambda>i. ennreal (r ^ i))"
        using \<open>0 \<le> r\<close> \<open>r < 1\<close> by (auto intro!: ennreal_leI power_decreasing simp: decseq_def)
      have "(\<lambda>i. ennreal (r ^ i)) \<longlonglongrightarrow> ennreal 0"
        using \<open>0 \<le> r\<close> \<open>r < 1\<close> by (intro tendsto_ennrealI LIMSEQ_power_zero) auto
      then show "(\<lambda>i. ennreal (r ^ i)) \<longlonglongrightarrow> 0" by simp
    qed
    finally have *: "emeasure (T x) {\<omega>\<in>space (T x). alw (HLD X) \<omega>} = 0" by auto
    have "AE \<omega> in T x. ev (HLD (- X)) \<omega>"
      by (rule AE_I[OF _ *]) (auto simp: not_ev_iff not_HLD[symmetric]) }
  note * = this
  show ?thesis
    apply (clarsimp simp add: AE_T_iff[of _ x])
    subgoal for x'
      by (cases "x' \<in> X") (auto simp add: ev_Stream *)
    done
qed


(* NEW STUFF *)

lemma sets_stream_space_cylinder: 
  "sets (stream_space M) = sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))"
proof (rule antisym)
  have closed[simp]: "scylinder (space M) ` lists (sets M) \<subseteq> Pow (streams (space M))"
    using scylinder_streams[of "space M" _] by auto
  have [simp]: "(\<lambda>s. s !! i) \<in> streams (space M) \<rightarrow> space M" for i
    by (auto simp: snth_in)

  interpret sigma_algebra "streams (space M)" "sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))"
    by (intro sigma_algebra_sigma_sets) fact

  have *: "(\<lambda>s. s !! i) -` A \<inter> streams (space M) = scylinder (space M) (replicate i (space M) @ [A])"
    if "A \<in> sets M" for i A
  proof (induction i)
    case (Suc n) show ?case
      apply (intro set_eqI)
      subgoal for \<omega> by (cases \<omega>) (auto simp: streams_Stream Suc[symmetric])
      done
  qed (auto simp: streams_stl)

  have "sets (stream_space M) \<le> sets (sigma (streams (space M)) (scylinder (space M) ` lists (sets M)))"
    unfolding sets_stream_space_eq
    by (rule sets_Sup_in_sets)
       (auto simp: sets_vimage_algebra2 PiE_UNIV_domain space_PiM * intro!: sigma_sets.Basic imageI)
  also have "\<dots> = sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))"
    by (rule sets_measure_of) fact
  finally show "sets (stream_space M) \<le> sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))" .
next
  show "sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M)) \<subseteq> sets (stream_space M)"
    unfolding space_stream_space[symmetric]
    by (rule sets.sigma_sets_subset) (auto intro!: sets_scylinder)
qed

end
