(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

header {* Trace Space equal to Markov Processes *}

theory Trace_Space_Equals_Markov_Processes
  imports Discrete_Time_Markov_Chain
begin

lemma all_le_Suc_split: "(\<forall>i\<le>Suc n. P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i\<le>n. P (Suc i)))"
  by (metis Suc_le_mono less_eq_nat.simps(1) not0_implies_Suc)

lemma measure_le_0: "measure M X \<le> 0 \<longleftrightarrow> measure M X = 0"
  using measure_nonneg[of M X] by auto

lemma subprob_measurableD:
  assumes N: "N \<in> measurable M (subprob_algebra S)" and x: "x \<in> space M"
  shows "space (N x) = space S"
    and "sets (N x) = sets S"
    and "measurable (N x) K = measurable S K"
    and "measurable K (N x) = measurable K S"
  using measurable_space[OF N x]
  by (auto simp: space_subprob_algebra intro!: measurable_cong_sets dest: sets_eq_imp_space_eq)

lemma ereal_indicator_le_0: "(indicator S x::ereal) \<le> 0 \<longleftrightarrow> x \<notin> S"
  by (auto split: split_indicator simp: one_ereal_def)

lemma nn_integral_bind:
  assumes f: "f \<in> borel_measurable B" "\<And>x. 0 \<le> f x"
  assumes N: "N \<in> measurable M (subprob_algebra B)"
  shows "(\<integral>\<^sup>+x. f x \<partial>(M \<guillemotright>= N)) = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f y \<partial>N x \<partial>M)"
proof cases
  assume M: "space M \<noteq> {}" show ?thesis
    unfolding bind_nonempty''[OF N M] nn_integral_join[OF f sets_distr]
    by (rule nn_integral_distr[OF N nn_integral_measurable_subprob_algebra[OF f]])
qed (simp add: bind_empty space_empty[of M] nn_integral_count_space)

lemma (in prob_space) prob_space_bind: 
  assumes ae: "AE x in M. prob_space (N x)"
    and N[measurable]: "N \<in> measurable M (subprob_algebra S)"
  shows "prob_space (M \<guillemotright>= N)"
proof
  have "emeasure (M \<guillemotright>= N) (space (M \<guillemotright>= N)) = (\<integral>\<^sup>+x. emeasure (N x) (space (N x)) \<partial>M)"
    by (subst emeasure_bind[where N=S])
       (auto simp: not_empty space_bind[OF N] subprob_measurableD[OF N] intro!: nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+x. 1 \<partial>M)"
    using ae by (intro nn_integral_cong_AE, eventually_elim) (rule prob_space.emeasure_space_1)
  finally show "emeasure (M \<guillemotright>= N) (space (M \<guillemotright>= N)) = 1"
    by (simp add: emeasure_space_1)
qed

lemma AE_bind:
  assumes P[measurable]: "Measurable.pred B P"
  assumes N[measurable]: "N \<in> measurable M (subprob_algebra B)"
  shows "(AE x in M \<guillemotright>= N. P x) \<longleftrightarrow> (AE x in M. AE y in N x. P y)"
proof cases
  assume M: "space M = {}" show ?thesis
    unfolding bind_empty[OF M] unfolding space_empty[OF M] by (simp add: AE_count_space)
next
  assume M: "space M \<noteq> {}"
  have *: "(\<integral>\<^sup>+x. indicator {x. \<not> P x} x \<partial>(M \<guillemotright>= N)) = (\<integral>\<^sup>+x. indicator {x\<in>space B. \<not> P x} x \<partial>(M \<guillemotright>= N))"
    by (intro nn_integral_cong) (simp add: space_bind[OF N M] split: split_indicator)

  have "(AE x in M \<guillemotright>= N. P x) \<longleftrightarrow> (\<integral>\<^sup>+ x. integral\<^sup>N (N x) (indicator {x \<in> space B. \<not> P x}) \<partial>M) = 0"
    by (simp add: AE_iff_nn_integral sets_bind[OF N M] space_bind[OF N M] * nn_integral_bind[where B=B]
             del: nn_integral_indicator)
  also have "\<dots> = (AE x in M. AE y in N x. P y)"
    apply (subst nn_integral_0_iff_AE)
    apply (rule measurable_compose[OF N nn_integral_measurable_subprob_algebra])
    apply measurable
    apply (intro eventually_subst AE_I2)
    apply simp
    apply (subst nn_integral_0_iff_AE)
    apply (simp add: subprob_measurableD(3)[OF N])
    apply (auto simp add: ereal_indicator_le_0 subprob_measurableD(1)[OF N] intro!: eventually_subst)
    done
  finally show ?thesis .
qed

lemma measure_eqI_restrict_generator:
  assumes E: "Int_stable E" "E \<subseteq> Pow \<Omega>" "\<And>X. X \<in> E \<Longrightarrow> emeasure M X = emeasure N X"
  assumes sets_eq: "sets M = sets N" and \<Omega>: "\<Omega> \<in> sets M"
  assumes "sets (restrict_space M \<Omega>) = sigma_sets \<Omega> E"
  assumes "sets (restrict_space N \<Omega>) = sigma_sets \<Omega> E" 
  assumes ae: "AE x in M. x \<in> \<Omega>" "AE x in N. x \<in> \<Omega>"
  assumes A: "range A \<subseteq> E" "(\<Union>i::nat. A i) = \<Omega>" "\<And>i. emeasure M (A i) \<noteq> \<infinity>"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets M"
  then have "emeasure M X = emeasure (restrict_space M \<Omega>) (X \<inter> \<Omega>)"
    using ae \<Omega> by (auto simp add: emeasure_restrict_space intro!: emeasure_eq_AE)
  also have "restrict_space M \<Omega> = restrict_space N \<Omega>"
  proof (rule measure_eqI_generator_eq)
    fix X assume "X \<in> E"
    then show "emeasure (restrict_space M \<Omega>) X = emeasure (restrict_space N \<Omega>) X"
      using E \<Omega> by (subst (1 2) emeasure_restrict_space) (auto simp: sets_eq sets_eq[THEN sets_eq_imp_space_eq])
  next
    fix i
    have "emeasure (restrict_space M \<Omega>) (A i) = emeasure M (A i)"
      using A \<Omega> by (subst emeasure_restrict_space) (auto simp: sets_eq sets_eq[THEN sets_eq_imp_space_eq])
    with A show "emeasure (restrict_space M \<Omega>) (A i) \<noteq> \<infinity>"
      by auto
  qed fact+
  also have "emeasure (restrict_space N \<Omega>) (X \<inter> \<Omega>) = emeasure N X"
    using X ae \<Omega> by (auto simp add: emeasure_restrict_space sets_eq intro!: emeasure_eq_AE)
  finally show "emeasure M X = emeasure N X" .
qed fact

lemma (in prob_space) emeasure_eq_1_AE:
  "S \<in> sets M \<Longrightarrow> AE x in M. x \<in> S \<Longrightarrow> emeasure M S = 1"
  by (subst emeasure_eq_AE[where B="space M"]) (auto simp: emeasure_space_1)

lemma streams_mono2: "S \<subseteq> T \<Longrightarrow> streams S \<subseteq> streams T"
  by (auto intro: streams_mono)

lemma emeasure_sigma: "emeasure (sigma \<Omega> A) X = 0"
  unfolding measure_of_def emeasure_def
  by (subst Abs_measure_inverse)
     (auto simp: measure_space_def positive_def countably_additive_def
           intro!: sigma_algebra_sigma_sets sigma_algebra_trivial)

lemma vimage_algebra_vimage_algebra_eq:
  assumes *: "f \<in> X \<rightarrow> Y" "g \<in> Y \<rightarrow> space M"
  shows "vimage_algebra X f (vimage_algebra Y g M) = vimage_algebra X (\<lambda>x. g (f x)) M"
  (is "?VV = ?V")
proof (rule measure_eqI)
  have "(\<lambda>x. g (f x)) \<in> X \<rightarrow> space M" "\<And>A. A \<inter> f -` Y \<inter> X = A \<inter> X"
    using * by auto
  with * show "sets ?VV = sets ?V"
    by (simp add: sets_vimage_algebra2 ex_simps[symmetric] vimage_comp comp_def del: ex_simps)
qed (simp add: vimage_algebra_def emeasure_sigma)

lemma sets_vimage_Sup_eq:
  assumes *: "M \<noteq> {}" "\<And>m. m \<in> M \<Longrightarrow> f \<in> X \<rightarrow> space m"
  shows "sets (vimage_algebra X f (Sup_sigma M)) = sets (\<Squnion>\<^sub>\<sigma> m \<in> M. vimage_algebra X f m)"
  (is "?IS = ?SI")
proof
  show "?IS \<subseteq> ?SI"
    by (intro sets_image_in_sets measurable_Sup_sigma2 measurable_Sup_sigma1)
       (auto simp: space_Sup_sigma measurable_vimage_algebra1 *)
  { fix m assume "m \<in> M"
    moreover then have "f \<in> X \<rightarrow> space (Sup_sigma M)" "f \<in> X \<rightarrow> space m"
      using * by (auto simp: space_Sup_sigma)
    ultimately have "f \<in> measurable (vimage_algebra X f (Sup_sigma M)) m"
      by (auto simp add: measurable_def sets_vimage_algebra2 intro: in_Sup_sigma) }
  then show "?SI \<subseteq> ?IS"
    by (auto intro!: sets_image_in_sets sets_Sup_in_sets del: subsetI simp: *)
qed

lemma restrict_space_eq_vimage_algebra:
  "\<Omega> \<subseteq> space M \<Longrightarrow> sets (restrict_space M \<Omega>) = sets (vimage_algebra \<Omega> (\<lambda>x. x) M)"
  unfolding restrict_space_def
  apply (subst sets_measure_of)
  apply (auto simp add: image_subset_iff dest: sets.sets_into_space) []
  apply (auto simp add: sets_vimage_algebra intro!: arg_cong2[where f=sigma_sets])
  done

lemma vimage_algebra_cong: "sets M = sets N \<Longrightarrow> sets (vimage_algebra X f M) = sets (vimage_algebra X f N)"
  by (simp add: sets_vimage_algebra)

lemma SUP_sigma_cong: 
  assumes *: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sets (N i)" shows "sets (\<Squnion>\<^sub>\<sigma> i\<in>I. M i) = sets (\<Squnion>\<^sub>\<sigma> i\<in>I. N i)"
  using * sets_eq_imp_space_eq[OF *] by (simp add: Sup_sigma_def)

lemma snth_in: "s \<in> streams X \<Longrightarrow> s !! n \<in> X"
  by (force simp: streams_iff_sset sset_range)

lemma streams_iff_snth: "s \<in> streams X \<longleftrightarrow> (\<forall>n. s !! n \<in> X)"
  by (force simp: streams_iff_sset sset_range)

lemma to_stream_in_streams: "to_stream X \<in> streams S \<longleftrightarrow> (\<forall>n. X n \<in> S)"
  by (simp add: to_stream_def streams_iff_snth)


lemma in_streams: "stl s \<in> streams S \<Longrightarrow> shd s \<in> S \<Longrightarrow> s \<in> streams S"
  by (cases s) auto

lemma sets_stream_space_in_sets:
  assumes space: "space N = streams (space M)"
  assumes sets: "\<And>i. (\<lambda>x. x !! i) \<in> measurable N M"
  shows "sets (stream_space M) \<subseteq> sets N"
  unfolding stream_space_def sets_distr
  by (auto intro!: sets_image_in_sets measurable_Sup_sigma2 measurable_vimage_algebra2 del: subsetI equalityI 
           simp add: sets_PiM_eq_proj snth_in space sets cong: measurable_cong_sets)

lemma sets_stream_space_eq: "sets (stream_space M) =
    sets (\<Squnion>\<^sub>\<sigma> i\<in>UNIV. vimage_algebra (streams (space M)) (\<lambda>s. s !! i) M)"
  by (auto intro!: sets_stream_space_in_sets sets_Sup_in_sets sets_image_in_sets
                   measurable_Sup_sigma1  snth_in measurable_vimage_algebra1 del: subsetI
           simp: space_Sup_sigma space_stream_space)

lemma sets_restrict_stream_space:
  assumes S[measurable]: "S \<in> sets M"
  shows "sets (restrict_space (stream_space M) (streams S)) = sets (stream_space (restrict_space M S))"
  using  S[THEN sets.sets_into_space]
  apply (subst restrict_space_eq_vimage_algebra)
  apply (simp add: space_stream_space streams_mono2)
  apply (subst vimage_algebra_cong[OF sets_stream_space_eq])
  apply (subst sets_stream_space_eq)
  apply (subst sets_vimage_Sup_eq)
  apply simp
  apply (auto intro: streams_mono) []
  apply (simp add: image_image space_restrict_space)
  apply (intro SUP_sigma_cong)
  apply (simp add: vimage_algebra_cong[OF restrict_space_eq_vimage_algebra])
  apply (subst (1 2) vimage_algebra_vimage_algebra_eq)
  apply (auto simp: streams_mono snth_in)
  done

primrec sstart :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a stream set" where
  "sstart S [] = streams S"
| [simp del]: "sstart S (x # xs) = op ## x ` sstart S xs"

lemma in_sstart[simp]: "s \<in> sstart S (x # xs) \<longleftrightarrow> shd s = x \<and> stl s \<in> sstart S xs"
  by (cases s) (auto simp: sstart.simps(2))

lemma sstart_in_streams: "xs \<in> lists S \<Longrightarrow> sstart S xs \<subseteq> streams S"
  by (induction xs) (auto simp: sstart.simps(2))

lemma sstart_eq: "x \<in> streams S \<Longrightarrow> x \<in> sstart S xs = (\<forall>i<length xs. x !! i = xs ! i)"
  by (induction xs arbitrary: x) (auto simp: nth_Cons streams_stl split: nat.splits)

lemma sstart_sets: "sstart S xs \<in> sets (stream_space (count_space UNIV))"
proof (induction xs)
  case (Cons x xs)
  note Cons[measurable]
  have "sstart S (x # xs) =
    {s\<in>space (stream_space (count_space UNIV)). shd s = x \<and> stl s \<in> sstart S xs}"
    by (simp add: set_eq_iff space_stream_space)
  also have "\<dots> \<in> sets (stream_space (count_space UNIV))"
    by measurable
  finally show ?case .
qed (simp add: streams_sets)

lemma sets_stream_space_sstart:
  assumes S[simp]: "countable S"
  shows "sets (stream_space (count_space S)) = sets (sigma (streams S) (sstart S`lists S \<union> {{}}))"
proof
  have [simp]: "sstart S ` lists S \<subseteq> Pow (streams S)"
    by (simp add: image_subset_iff sstart_in_streams)

  let ?S = "sigma (streams S) (sstart S ` lists S \<union> {{}})"
  { fix i a assume "a \<in> S"
    { fix x have "(x !! i = a \<and> x \<in> streams S) \<longleftrightarrow> (\<exists>xs\<in>lists S. length xs = i \<and> x \<in> sstart S (xs @ [a]))"
      proof (induction i arbitrary: x)
        case (Suc i) from this[of "stl x"] show ?case
          by (simp add: length_Suc_conv Bex_def ex_simps[symmetric] del: ex_simps)
             (metis stream.collapse streams_Stream)
      qed (insert `a \<in> S`, auto intro: streams_stl in_streams) }
    then have "(\<lambda>x. x !! i) -` {a} \<inter> streams S = (\<Union>xs\<in>{xs\<in>lists S. length xs = i}. sstart S (xs @ [a]))"
      by (auto simp add: set_eq_iff)
    also have "\<dots> \<in> sets ?S"
      using `a\<in>S` by (intro sets.countable_UN') (auto intro!: sigma_sets.Basic image_eqI)
    finally have " (\<lambda>x. x !! i) -` {a} \<inter> streams S \<in> sets ?S" . }
  then show "sets (stream_space (count_space S)) \<subseteq> sets (sigma (streams S) (sstart S`lists S \<union> {{}}))"
    by (intro sets_stream_space_in_sets) (auto simp: measurable_count_space_eq_countable snth_in)

  have "sigma_sets (space (stream_space (count_space S))) (sstart S`lists S \<union> {{}}) \<subseteq> sets (stream_space (count_space S))"
  proof (safe intro!: sets.sigma_sets_subset)
    fix xs assume "\<forall>x\<in>set xs. x \<in> S"
    then have "sstart S xs = {x\<in>space (stream_space (count_space S)). \<forall>i<length xs. x !! i = xs ! i}"
      by (induction xs)
         (auto simp: space_stream_space nth_Cons split: nat.split intro: in_streams streams_stl)
    also have "\<dots> \<in> sets (stream_space (count_space S))"
      by measurable
    finally show "sstart S xs \<in> sets (stream_space (count_space S))" .
  qed
  then show "sets (sigma (streams S) (sstart S`lists S \<union> {{}})) \<subseteq> sets (stream_space (count_space S))"
    by (simp add: space_stream_space)
qed

lemma Int_stable_sstart: "Int_stable (sstart S`lists S \<union> {{}})"
proof -
  { fix xs ys assume "xs \<in> lists S" "ys \<in> lists S"
    then have "sstart S xs \<inter> sstart S ys \<in> sstart S ` lists S \<union> {{}}"
    proof (induction xs ys rule: list_induct2')
      case (4 x xs y ys)
      show ?case
      proof cases
        assume "x = y"
        then have "sstart S (x # xs) \<inter> sstart S (y # ys) = op ## x ` (sstart S xs \<inter> sstart S ys)"
          by (auto simp: image_iff intro!: stream.collapse[symmetric])
        also have "\<dots> \<in> sstart S ` lists S \<union> {{}}"
          using 4 by (auto simp: sstart.simps(2)[symmetric] del: in_listsD)
        finally show ?case .
      qed auto
    qed (simp_all add: sstart_in_streams inf.absorb1 inf.absorb2 image_eqI[where x="[]"]) }
  then show ?thesis
    by (auto simp: Int_stable_def)
qed

lemma stream_space_eq_sstart:
  assumes S[simp]: "countable S"
  assumes P: "prob_space M" "prob_space N"
  assumes ae: "AE x in M. x \<in> streams S" "AE x in N. x \<in> streams S"
  assumes sets_M: "sets M = sets (stream_space (count_space UNIV))"
  assumes sets_N: "sets N = sets (stream_space (count_space UNIV))"
  assumes *: "\<And>xs. xs \<noteq> [] \<Longrightarrow> xs \<in> lists S \<Longrightarrow> emeasure M (sstart S xs) = emeasure N (sstart S xs)"
  shows "M = N"
proof (rule measure_eqI_restrict_generator[OF Int_stable_sstart])
  have [simp]: "sstart S ` lists S \<subseteq> Pow (streams S)"
    by (simp add: image_subset_iff sstart_in_streams)

  interpret M: prob_space M by fact

  show "sstart S ` lists S \<union> {{}} \<subseteq> Pow (streams S)"
    by (auto dest: sstart_in_streams del: in_listsD)

  { fix M :: "'a stream measure" assume M: "sets M = sets (stream_space (count_space UNIV))"
    have "sets (restrict_space M (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
      apply (simp add: sets_eq_imp_space_eq[OF M] space_stream_space restrict_space_eq_vimage_algebra
        vimage_algebra_cong[OF M])
      apply (simp add: sets_eq_imp_space_eq[OF M] space_stream_space restrict_space_eq_vimage_algebra[symmetric])
      apply (simp add: sets_restrict_stream_space restrict_count_space sets_stream_space_sstart)
      done }
  from this[OF sets_M] this[OF sets_N]
  show "sets (restrict_space M (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
       "sets (restrict_space N (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
    by auto
  show "range (\<lambda>i::nat. streams S) \<subseteq> sstart S ` lists S \<union> {{}}"
    "(\<Union>i. streams S) = streams S" "emeasure M (streams S) \<noteq> \<infinity>"
    using M.emeasure_space_1 space_stream_space[of "count_space S"] sets_eq_imp_space_eq[OF sets_M]
    by (auto simp add: image_eqI[where x="[]"])
  show "sets M = sets N"
    by (simp add: sets_M sets_N)
next
  fix X assume "X \<in> sstart S ` lists S \<union> {{}}"
  then obtain xs where "X = {} \<or> (xs \<in> lists S \<and> X = sstart S xs)"
    by auto
  moreover have "emeasure M (streams S) = 1"
    using ae by (intro prob_space.emeasure_eq_1_AE[OF P(1)]) (auto simp: sets_M streams_sets)
  moreover have "emeasure N (streams S) = 1"
    using ae by (intro prob_space.emeasure_eq_1_AE[OF P(2)]) (auto simp: sets_N streams_sets)
  ultimately show "emeasure M X = emeasure N X"
    using P[THEN prob_space.emeasure_space_1]
    by (cases "xs = []") (auto simp: * space_stream_space del: in_listsD)
qed (auto simp: * ae sets_M del: in_listsD intro!: streams_sets)

lemma measure_density_const:
  "A \<in> sets M \<Longrightarrow> 0 \<le> c \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow> measure (density M (\<lambda>_. c)) A = real c * measure M A"
  by (auto simp: emeasure_density_const measure_def)

lemma emeasure_single_in_space: "emeasure M {x} \<noteq> 0 \<Longrightarrow> x \<in> space M"
  using emeasure_notin_sets[of "{x}" M] by (auto dest: sets.sets_into_space)

lemma (in prob_space) AE_support_countable:
  assumes [simp]: "sets M = UNIV"
  shows "(AE x in M. measure M {x} \<noteq> 0) \<longleftrightarrow> (\<exists>S. countable S \<and> (AE x in M. x \<in> S))"
proof
  assume "\<exists>S. countable S \<and> (AE x in M. x \<in> S)"
  then obtain S where S[intro]: "countable S" and ae: "AE x in M. x \<in> S"
    by auto
  then have "emeasure M (\<Union>x\<in>{x\<in>S. emeasure M {x} \<noteq> 0}. {x}) = 
    (\<integral>\<^sup>+ x. emeasure M {x} * indicator {x\<in>S. emeasure M {x} \<noteq> 0} x \<partial>count_space UNIV)"
    by (subst emeasure_UN_countable)
       (auto simp: disjoint_family_on_def nn_integral_restrict_space[symmetric] restrict_count_space)
  also have "\<dots> = (\<integral>\<^sup>+ x. emeasure M {x} * indicator S x \<partial>count_space UNIV)"
    by (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = emeasure M (\<Union>x\<in>S. {x})"
    by (subst emeasure_UN_countable)
       (auto simp: disjoint_family_on_def nn_integral_restrict_space[symmetric] restrict_count_space)
  also have "\<dots> = emeasure M (space M)"
    using ae by (intro emeasure_eq_AE) auto
  finally have "emeasure M {x \<in> space M. x\<in>S \<and> emeasure M {x} \<noteq> 0} = 1"
    by (simp add: emeasure_space_1 emeasure_single_in_space cong: rev_conj_cong)
  then have "AE x in M. x \<in> S \<and> emeasure M {x} \<noteq> 0"
    by (rule AE_I_eq_1) simp
  then show "AE x in M. measure M {x} \<noteq> 0"
    by (auto simp: emeasure_eq_measure)
qed (auto intro!: exI[of _ "{x. measure M {x} \<noteq> 0}"] countable_support)

lemma (in prob_space) measure_uniform_measure_eq_cond_prob:
  assumes [measurable]: "Measurable.pred M P" "Measurable.pred M Q"
  shows "\<P>(x in uniform_measure M {x\<in>space M. Q x}. P x) = \<P>(x in M. P x \<bar> Q x)"
proof cases
  assume Q: "measure M {x\<in>space M. Q x} = 0"
  then have "AE x in M. \<not> Q x"
    by (simp add: prob_eq_0)
  then have "AE x in M. indicator {x\<in>space M. Q x} x / ereal 0 = 0"
    by (auto split: split_indicator)
  from density_cong[OF _ _ this] show ?thesis
    by (simp add: uniform_measure_def emeasure_eq_measure cond_prob_def Q measure_density_const)
qed (auto simp add: emeasure_eq_measure cond_prob_def intro!: arg_cong[where f=prob])

context MC_syntax
begin

text {* Markov chain with initial distribution @{term_type "I::'s pmf"}: *}

definition T' :: "'s pmf \<Rightarrow> 's stream measure" where
  "T' I = bind I (\<lambda>s. distr (T s) S (op ## s))"

lemma T_subprob: "T \<in> measurable (measure_pmf I) (subprob_algebra S)"
  by (auto intro!: space_bind simp: space_subprob_algebra) unfold_locales

lemma distr_Stream_subprob:
  "(\<lambda>s. distr (T s) S (op ## s)) \<in> measurable (measure_pmf I) (subprob_algebra S)"
  apply (intro measurable_distr2[OF _ T_subprob])
  apply (subst measurable_cong_sets[where M'="count_space UNIV \<Otimes>\<^sub>M S" and N'=S])
  apply (rule sets_pair_measure_cong)
  apply auto
  done

lemma sets_T': "sets (T' I) = sets S"
  by (simp add: T'_def sets_bind[OF distr_Stream_subprob])

lemma prob_space_T': "prob_space (T' I)"
  unfolding T'_def
proof (rule measure_pmf.prob_space_bind)
  show "AE s in I. prob_space (distr (T s) S (op ## s))"
    by (intro AE_measure_pmf_iff[THEN iffD2] ballI T.prob_space_distr) simp
qed (rule distr_Stream_subprob)

lemma AE_T':
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE x in T' I. P x) \<longleftrightarrow> (\<forall>s\<in>I. AE x in T s. P (s ## x))"
  unfolding T'_def by (simp add: AE_bind[OF _ distr_Stream_subprob] AE_measure_pmf_iff AE_distr_iff)

lemma emeasure_T':
  assumes [measurable]: "X \<in> sets S"
  shows "emeasure (T' I) X = (\<integral>\<^sup>+s. emeasure (T s) {\<omega>\<in>space S. s ## \<omega> \<in> X} \<partial>I)"
  unfolding T'_def
  by (simp add: emeasure_bind[OF _ distr_Stream_subprob] emeasure_distr vimage_def Int_def conj_ac)

lemma prob_T':
  assumes [measurable]: "Measurable.pred S P"
  shows "\<P>(x in T' I. P x) = (\<integral>s. \<P>(x in T s. P (s ## x)) \<partial>I)"
proof -
  interpret T': prob_space "T' I" by (rule prob_space_T')
  show ?thesis
    using emeasure_T'[of "{x\<in>space (T' I). P x}" I]
    unfolding T'.emeasure_eq_measure T.emeasure_eq_measure sets_eq_imp_space_eq[OF sets_T']
    apply simp
    apply (subst (asm) nn_integral_eq_integral)
    apply (auto intro!: measure_pmf.integrable_const_bound[where B=1] integral_cong arg_cong2[where f=measure]
                simp: AE_measure_pmf measure_nonneg space_stream_space)
    done
qed

lemma T_eq_T': "T s = T' (K s)"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets (T s)"
  then have [measurable]: "X \<in> sets S"
    by simp
  have X_eq: "X = {x\<in>space (T s). x \<in> X}"
    using sets.sets_into_space[OF X] by auto
  show "emeasure (T s) X = emeasure (T' (K s)) X"
    apply (subst X_eq)
    apply (subst emeasure_Collect_T, simp)
    apply (subst emeasure_T', simp)
    apply simp
    done
qed (simp add: sets_T')

end

definition "with P f d = (if \<exists>x. P x then f (SOME x. P x) else d)"

lemma withI[case_names default exists]:
  "((\<And>x. \<not> P x) \<Longrightarrow> Q d) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q (f x)) \<Longrightarrow> Q (with P f d)"
  unfolding with_def by (auto intro: someI2)

text {*
  We can construct for each time-homogeneous discrete-time Markov chain a corresponding
  probability space using @{theory Discrete_Time_Markov_Chain}. The constructed probability space
  has the same probabilities.
*}

locale Time_Homogeneous_Discrete_Markov_Process = M: prob_space +
  fixes S :: "'s set" and X :: "nat \<Rightarrow> 'a \<Rightarrow> 's"
  assumes X [measurable]: "\<And>t. X t \<in> measurable M (count_space UNIV)"
  assumes S: "countable S" "\<And>n. AE x in M. X n x \<in> S"
  assumes MC: "\<And>n s s'.
    \<P>(\<omega> in M. \<forall>t\<le>n. X t \<omega> = s t ) \<noteq> 0 \<Longrightarrow>
    \<P>(\<omega> in M. X (Suc n) \<omega> = s' \<bar> \<forall>t\<le>n. X t \<omega> = s t ) =
    \<P>(\<omega> in M. X (Suc n) \<omega> = s' \<bar> X n \<omega> = s n )"
  assumes TH: "\<And>n m s t.
    \<P>(\<omega> in M. X n \<omega> = t) \<noteq> 0 \<Longrightarrow> \<P>(\<omega> in M. X m \<omega> = t) \<noteq> 0 \<Longrightarrow>
    \<P>(\<omega> in M. X (Suc n) \<omega> = s \<bar> X n \<omega> = t) = \<P>(\<omega> in M. X (Suc m) \<omega> = s \<bar> X m \<omega> = t)"
begin

context
begin

interpretation pmf_as_measure .

lift_definition I :: "'s pmf" is "distr M (count_space UNIV) (X 0)"
proof -
  let ?X = "distr M (count_space UNIV) (X 0)"
  have "AE x in ?X. measure ?X {x} \<noteq> 0"
    using S by (subst prob_space.AE_support_countable) (auto simp: prob_space_distr AE_distr_iff intro!: exI[of _ S])
  then show "prob_space ?X \<and> sets ?X = UNIV \<and> (AE x in ?X. measure ?X {x} \<noteq> 0)"
    by (simp add: prob_space_distr AE_support_countable)
qed

lemma I_in_S:
  assumes "pmf I s \<noteq> 0" shows "s \<in> S"
proof -
  from `pmf I s \<noteq> 0` have "0 \<noteq> \<P>(x in M. X 0 x = s)"
    by transfer (auto simp: measure_distr vimage_def Int_def conj_commute)
  also have "\<P>(x in M. X 0 x = s) = \<P>(x in M. X 0 x = s \<and> s \<in> S)"
    using S(2)[of 0] by (intro M.finite_measure_eq_AE) auto
  finally show ?thesis
    by (cases "s \<in> S") auto
qed

lift_definition K :: "'s \<Rightarrow> 's pmf" is
  "\<lambda>s. with (\<lambda>n. \<P>(\<omega> in M. X n \<omega> = s) \<noteq> 0)
     (\<lambda>n. distr (uniform_measure M {\<omega>\<in>space M. X n \<omega> = s}) (count_space UNIV) (X (Suc n)))
     (uniform_measure (count_space UNIV) {s})"
proof (rule withI)
  fix s n assume *: "\<P>(\<omega> in M. X n \<omega> = s) \<noteq> 0"
  let ?D = "distr (uniform_measure M {\<omega>\<in>space M. X n \<omega> = s}) (count_space UNIV) (X (Suc n))"
  have D: "prob_space ?D"
    by (intro prob_space.prob_space_distr prob_space_uniform_measure)
       (auto simp: M.emeasure_eq_measure *)
  moreover have sets_D: "sets ?D = UNIV"
    by simp
  moreover have "AE x in ?D. measure ?D {x} \<noteq> 0"
    unfolding prob_space.AE_support_countable[OF D sets_D]
  proof (intro exI[of _ S] conjI)
    show "countable S" by (rule S)
    show "AE x in ?D. x \<in> S"
      using * S(2)[of "Suc n"] by (auto simp add: AE_distr_iff AE_uniform_measure M.emeasure_eq_measure)
  qed
  ultimately show "prob_space ?D \<and> sets ?D = UNIV \<and> (AE x in ?D. measure ?D {x} \<noteq> 0)"
    by blast
qed (auto intro!: prob_space_uniform_measure AE_uniform_measureI)

lemma pmf_K:
  assumes n: "0 < \<P>(\<omega> in M. X n \<omega> = s)"
  shows "pmf (K s) t = \<P>(\<omega> in M. X (Suc n) \<omega> = t \<bar> X n \<omega> = s)"
proof (transfer fixing: n s t)
  let ?P = "\<lambda>n. \<P>(\<omega> in M. X n \<omega> = s) \<noteq> 0"
  let ?D = "\<lambda>n. distr (uniform_measure M {\<omega>\<in>space M. X n \<omega> = s}) (count_space UNIV) (X (Suc n))"
  let ?U = "uniform_measure (count_space UNIV) {s}"
  show "measure (with ?P ?D ?U) {t} = \<P>(\<omega> in M. X (Suc n) \<omega> = t \<bar> X n \<omega> = s)"
  proof (rule withI)
    fix n' assume "?P n'"
    moreover have "X (Suc n') -` {t} \<inter> space M = {x\<in>space M. X (Suc n') x = t}"
      by auto
    ultimately show "measure (?D n') {t} = \<P>(\<omega> in M. X (Suc n) \<omega> = t \<bar> X n \<omega> = s)"
      using n M.measure_uniform_measure_eq_cond_prob[of "\<lambda>x. X (Suc n') x = t" "\<lambda>x. X n' x = s"]
      by (auto simp: measure_distr M.emeasure_eq_measure simp del: measure_uniform_measure intro!: TH)
  qed (insert n, simp)
qed

lemma pmf_K2:
  "(\<And>n. \<P>(\<omega> in M. X n \<omega> = s) = 0) \<Longrightarrow> pmf (K s) t = indicator {t} s"
  apply (transfer fixing: s t)
  apply (rule withI)
  apply (auto split: split_indicator)
  done

end

sublocale K!: MC_syntax K .

lemma bind_I_K_eq_M: "K.T' I = distr M K.S (\<lambda>\<omega>. to_stream (\<lambda>n. X n \<omega>))" (is "_ = ?D")
proof (rule stream_space_eq_sstart)
  note streams_sets[measurable]
  note measurable_abs_UNIV[measurable (raw)]
  note sstart_sets[measurable]

  { fix s assume "s \<in> S"
    from K.AE_T_enabled[of s] have "AE \<omega> in K.T s. \<omega> \<in> streams S"
    proof eventually_elim
      fix \<omega> assume "K.enabled s \<omega>" from this `s\<in>S` show "\<omega> \<in> streams S"
      proof (coinduction arbitrary: s \<omega>)
        case streams
        then have 1: "pmf (K s) (shd \<omega>) \<noteq> 0"
          by (simp add: K.enabled.simps[of s] set_pmf_iff)
        have "shd \<omega> \<in> S"
        proof cases
          assume "\<exists>n. 0 < \<P>(\<omega> in M. X n \<omega> = s)"
          then obtain n where "0 < \<P>(\<omega> in M. X n \<omega> = s)" by auto
          with 1 have 2: "\<P>(\<omega>' in M. X (Suc n) \<omega>' = shd \<omega> \<and> X n \<omega>' = s) \<noteq> 0"
            by (simp add: pmf_K cond_prob_def)
          show "shd \<omega> \<in> S"
          proof (rule ccontr)
            assume "shd \<omega> \<notin> S"
            with S(2)[of "Suc n"] have "\<P>(\<omega>' in M. X (Suc n) \<omega>' = shd \<omega> \<and> X n \<omega>' = s) = 0"
              by (intro M.prob_eq_0_AE) auto
            with 2 show False by contradiction
          qed
        next
          assume "\<not> (\<exists>n. 0 < \<P>(\<omega> in M. X n \<omega> = s))"
          then have "pmf (K s) (shd \<omega>) = indicator {shd \<omega>} s"
            by (intro pmf_K2) (auto simp: not_less measure_le_0)
          with 1 `s\<in>S` show ?thesis
            by (auto split: split_indicator_asm)
        qed
        with streams show ?case
          by (cases \<omega>) (auto simp: K.enabled.simps[of s])
      qed
    qed }
  note AE_streams = this

  show "prob_space (K.T' I)"
    by (rule K.prob_space_T')
  show "prob_space ?D"
    by (rule M.prob_space_distr) simp

  show "AE x in K.T' I. x \<in> streams S"
    by (auto simp add: K.AE_T' set_pmf_iff I_in_S AE_distr_iff streams_Stream intro!: AE_streams)
  show "AE x in ?D. x \<in> streams S"
    by (simp add: AE_distr_iff to_stream_in_streams AE_all_countable S)
  show "sets (K.T' I) = sets (stream_space (count_space UNIV))"
    by (simp add: K.sets_T')
  show "sets ?D = sets (stream_space (count_space UNIV))"
    by simp

  fix xs' assume "xs' \<noteq> []" "xs' \<in> lists S"
  then obtain s xs where xs': "xs' = s # xs" and s: "s \<in> S" and xs: "xs \<in> lists S"
    by (auto simp: neq_Nil_conv del: in_listsD)

  have "emeasure (K.T' I) (sstart S xs') = (\<integral>\<^sup>+s. emeasure (K.T s) {\<omega>\<in>space K.S. s ## \<omega> \<in> sstart S xs'} \<partial>I)"
    by (rule K.emeasure_T') measurable
  also have "\<dots> = (\<integral>\<^sup>+s'. emeasure (K.T s) (sstart S xs) * indicator {s} s' \<partial>I)"
    by (auto split: split_indicator simp: emeasure_distr vimage_def space_stream_space neq_Nil_conv xs'
             intro!: arg_cong2[where f=emeasure] nn_integral_cong)
  also have "\<dots> = pmf I s * emeasure (K.T s) (sstart S xs)"
    by (simp add: nn_integral_cmult_indicator emeasure_nonneg emeasure_measure_pmf_finite) (rule mult.commute)
  also have "emeasure (K.T s) (sstart S xs) = ereal (\<Prod>i<length xs. pmf (K ((s#xs)!i)) (xs!i))"
    using xs s
  proof (induction arbitrary: s)
    case Nil then show ?case
      by (simp add: K.T.emeasure_eq_1_AE AE_streams)
  next
    case (Cons t xs)
    have "emeasure (K.T s) (sstart S (t # xs)) = 
      emeasure (K.T s) {x\<in>space (K.T s). shd x = t \<and> stl x \<in> sstart S xs}"
      by (intro arg_cong2[where f=emeasure]) (auto simp: space_stream_space)
    also have "\<dots> = (\<integral>\<^sup>+t'. emeasure (K.T t') {x\<in>space K.S. t' = t \<and> x \<in> sstart S xs} \<partial>K s)"
      by (subst K.emeasure_Collect_T) auto
    also have "\<dots> = (\<integral>\<^sup>+t'. emeasure (K.T t) (sstart S xs) * indicator {t} t' \<partial>K s)"
      by (intro nn_integral_cong) (auto split: split_indicator simp: space_stream_space)
    also have "\<dots> = emeasure (K.T t) (sstart S xs) * pmf (K s) t"
      by (simp add: emeasure_nonneg nn_integral_cmult_indicator emeasure_measure_pmf_finite)
    finally show ?case
      by (simp add: lessThan_Suc_eq_insert_0 Zero_notin_Suc setprod.reindex Cons)
  qed
  also have "pmf I s * ereal (\<Prod>i<length xs. pmf (K ((s#xs)!i)) (xs!i)) = 
    \<P>(x in M. \<forall>i\<le>length xs. X i x = (s # xs) ! i)"
    using xs s
  proof (induction xs rule: rev_induct)
    case Nil
    have "pmf I s = prob {x \<in> space M. X 0 x = s}"
      by transfer (simp add: vimage_def Int_def measure_distr conj_commute)
    then show ?case
      by simp
  next
    case (snoc t xs)
    let ?l = "length xs" and ?lt = "length (xs @ [t])" and ?xs' = "s # xs @ [t]"
    have "ereal (pmf I s) * (\<Prod>i<?lt. pmf (K ((?xs') ! i)) ((xs @ [t]) ! i)) =
      (ereal (pmf I s) * (\<Prod>i<?l. pmf (K ((s # xs) ! i)) (xs ! i))) * pmf (K ((s # xs) ! ?l)) t"
      by (simp add: lessThan_Suc mult_ac nth_append append_Cons[symmetric] del: append_Cons)
    also have "\<dots> = \<P>(x in M. \<forall>i\<le>?l. X i x = (s # xs) ! i) * pmf (K ((s # xs) ! ?l)) t"
      using snoc by simp
    also have "\<dots> = \<P>(x in M. \<forall>i\<le>?lt. X i x = (?xs') ! i)"
    proof cases
      assume "\<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i) = 0"
      moreover have "\<P>(x in M. \<forall>i\<le>?lt. X i x = (?xs') ! i) \<le> \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        by (intro M.finite_measure_mono) (auto simp: nth_append nth_Cons split: nat.split)
      moreover have "\<P>(x in M. \<forall>i\<le>?l. X i x = (s # xs) ! i) \<le> \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        by (intro M.finite_measure_mono) (auto simp: nth_append nth_Cons split: nat.split)
      ultimately show ?thesis 
        by (simp add: measure_le_0)
    next
      assume "\<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i) \<noteq> 0"
      then have *: "0 < \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        unfolding less_le by (simp add: measure_nonneg)
      moreover have "\<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i) \<le> \<P>(\<omega> in M. X ?l \<omega> = (s # xs) ! ?l)"
        by (intro M.finite_measure_mono) (auto simp: nth_append nth_Cons split: nat.split)
      ultimately have "\<P>(\<omega> in M. X ?l \<omega> = (s # xs) ! ?l) \<noteq> 0"
        by auto
      then have "pmf (K ((s # xs) ! ?l)) t = \<P>(\<omega> in M. X ?lt \<omega> = ?xs' ! ?lt \<bar> X ?l \<omega> = (s # xs) ! ?l)"
        by (subst pmf_K) (auto simp: less_le measure_nonneg)
      also have "\<dots> = \<P>(\<omega> in M. X ?lt \<omega> = ?xs' ! ?lt \<bar> \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        using * MC[of ?l "\<lambda>i. (s # xs) ! i" "?xs' ! ?lt"] by simp
      also have "\<dots> = \<P>(\<omega> in M. \<forall>i\<le>?lt. X i \<omega> = ?xs' ! i) / \<P>(\<omega> in M. \<forall>i\<le>?l. X i \<omega> = (s # xs) ! i)"
        unfolding cond_prob_def
        by (intro arg_cong2[where f="op /"] arg_cong2[where f=measure]) (auto simp: nth_Cons nth_append split: nat.splits)
      finally show ?thesis
        using * by simp
    qed
    finally show ?case .
  qed
  also have "\<dots> = emeasure ?D (sstart S xs')"
  proof -
    have "AE x in M. \<forall>i. X i x \<in> S"
      using S(2) by (simp add: AE_all_countable)
    then have "AE x in M. (\<forall>i\<le>length xs. X i x = (s # xs) ! i) = (to_stream (\<lambda>n. X n x) \<in> sstart S xs')"
    proof eventually_elim
      fix x assume "\<forall>i. X i x \<in> S"
      then have "to_stream (\<lambda>n. X n x) \<in> streams S"
        by (auto simp: streams_iff_snth to_stream_def)
      then show "(\<forall>i\<le>length xs. X i x = (s # xs) ! i) = (to_stream (\<lambda>n. X n x) \<in> sstart S xs')"
        by (simp add: sstart_eq xs' to_stream_def less_Suc_eq_le del: sstart.simps(1) in_sstart)
    qed
    then show ?thesis
      by (auto simp: emeasure_distr M.emeasure_eq_measure intro!: M.finite_measure_eq_AE)
  qed
  finally show "emeasure (K.T' I) (sstart S xs') = emeasure ?D (sstart S xs')" .
qed (rule S)

end

lemma (in MC_syntax) is_THDTMC:
  fixes I :: "'s pmf"
  defines "U \<equiv> (SIGMA s:UNIV. K s)\<^sup>* `` I"
  shows "Time_Homogeneous_Discrete_Markov_Process (T' I) U (\<lambda>n \<omega>. \<omega> !! n)"
proof -
  have [measurable]: "U \<in> sets (count_space UNIV)"
    by auto

  interpret prob_space "T' I"
    by (rule prob_space_T')

  { fix s t I
    have "\<And>t s. \<P>(\<omega> in T s. s = t) = indicator {t} s"
      using T.prob_space by (auto split: split_indicator)
    moreover then have "\<And>t t' s. \<P>(\<omega> in T s. shd \<omega> = t' \<and> s = t) = pmf (K t) t' * indicator {t} s"
      by (subst prob_T) (auto split: split_indicator simp: pmf.rep_eq)
    ultimately have "\<P>(\<omega> in T' I. shd (stl \<omega>) = t \<and> shd \<omega> = s) = \<P>(\<omega> in T' I. shd \<omega> = s) * pmf (K s) t"
      by (simp add: prob_T' pmf.rep_eq measure_nonneg) }
  note start_eq = this

  { fix n s t assume "\<P>(\<omega> in T' I. \<omega> !! n = s) \<noteq> 0"
    moreover have "\<P>(\<omega> in T' I. \<omega> !! (Suc n) = t \<and> \<omega> !! n = s) = \<P>(\<omega> in T' I. \<omega> !! n = s) * pmf (K s) t"
    proof (induction n arbitrary: I)
      case (Suc n) then show ?case
        by (subst (1 2) prob_T') (simp_all del: space_T add: T_eq_T')
    qed (simp add: start_eq)
    ultimately have "\<P>(\<omega> in T' I. stl \<omega> !! n = t \<bar> \<omega> !! n = s) = pmf (K s) t" 
      by (simp add: cond_prob_def field_simps) }
  note TH = this

  { fix n \<omega>' t assume "\<P>(\<omega> in T' I. \<forall>i\<le>n. \<omega> !! i = \<omega>' i) \<noteq> 0"
    moreover have "\<P>(\<omega> in T' I. \<omega> !! (Suc n) = t \<and> (\<forall>i\<le>n. \<omega> !! i = \<omega>' i)) =
      \<P>(\<omega> in T' I. \<forall>i\<le>n. \<omega> !! i = \<omega>' i) * pmf (K (\<omega>' n)) t"
    proof (induction n arbitrary: I \<omega>')
      case (Suc n)
      have *[simp]: "\<And>s P. measure (T' (K s)) {x. s = \<omega>' 0 \<and> P x} = 
        measure (T' (K (\<omega>' 0))) {x. P x} * indicator {\<omega>' 0} s"
        by (auto split: split_indicator)
      from Suc[of _ "\<lambda>i. \<omega>' (Suc i)"] show ?case
        by (subst (1 2) prob_T')
           (simp_all add: T_eq_T' all_le_Suc_split conj_commute conj_left_commute sets_eq_imp_space_eq[OF sets_T'])
    qed (simp add: start_eq)
    ultimately have "\<P>(\<omega> in T' I. stl \<omega> !! n = t \<bar> \<forall>i\<le>n. \<omega> !! i = \<omega>' i) = pmf (K (\<omega>' n)) t" 
      by (simp add: cond_prob_def field_simps) }
  note MC = this

  { fix n \<omega>' assume "\<P>(\<omega> in T' I. \<forall>t\<le>n. \<omega> !! t = \<omega>' t) \<noteq> 0"
    moreover have "\<P>(\<omega> in T' I. \<forall>t\<le>n. \<omega> !! t = \<omega>' t) \<le> \<P>(\<omega> in T' I. \<omega> !! n = \<omega>' n)"
      by (auto intro!: finite_measure_mono_AE simp: sets_T' sets_eq_imp_space_eq[OF sets_T'])
    ultimately have "\<P>(\<omega> in T' I. \<omega> !! n = \<omega>' n) \<noteq> 0"
      by (auto simp: neq_iff not_less measure_le_0) }
  note MC' = this

  show ?thesis
  proof
    show "countable U"
      unfolding U_def by (rule countable_reachable countable_Image countable_set_pmf)+
    show "\<And>t. (\<lambda>\<omega>. \<omega> !! t) \<in> measurable (T' I) (count_space UNIV)"
      by (subst measurable_cong_sets[OF sets_T' refl]) simp
  next
    fix n
    have "\<forall>x\<in>I. AE y in T x. (x ## y) !! n \<in> U"
      unfolding U_def
    proof (induction n arbitrary: I)
      case 0 then show ?case
        by auto
    next
      case (Suc n)
      { fix x assume "x \<in> I"
        have "AE y in T x. y !! n \<in> (SIGMA x:UNIV. K x)\<^sup>* `` K x"
          apply (subst AE_T_iff)
          apply (rule measurable_compose[OF measurable_snth], simp)
          apply (rule Suc)
          done
        moreover have "(SIGMA x:UNIV. K x)\<^sup>* `` K x \<subseteq> (SIGMA x:UNIV. K x)\<^sup>* `` I"
          using `x \<in> I` by (auto intro: converse_rtrancl_into_rtrancl)
        ultimately have "AE y in T x. y !! n \<in> (SIGMA x:UNIV. K x)\<^sup>* `` I"
          by (auto simp: subset_eq) }
      then show ?case
        by simp
    qed
    then show "AE x in T' I. x !! n \<in> U"
      by (simp add: AE_T')
  qed (simp_all add: TH MC MC')
qed

end
