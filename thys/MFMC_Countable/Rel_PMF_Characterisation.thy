(* Author: Andreas Lochbihler, ETH Zurich *)

theory Rel_PMF_Characterisation imports
  Max_Flow_Min_Cut_Countable
begin

section \<open>Characterisation of @{const rel_pmf}\<close>

context begin

private datatype ('a, 'b) vertex = Source | Sink | Left 'a | Right 'b

private lemma inj_Left [simp]: "inj_on Left X"
by(simp add: inj_on_def)

private lemma inj_Right [simp]: "inj_on Right X"
by(simp add: inj_on_def)

proposition rel_pmf_measureI:
  fixes p :: "'a pmf" and q :: "'b pmf"
  assumes le: "\<And>A. measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
  shows "rel_pmf R p q"
proof -
  have DomR: "\<exists>y\<in>set_pmf q. R x y" if "x \<in> set_pmf p" for x
  proof(rule ccontr)
    assume *: "\<not> ?thesis"
    from le[of "{x}"] have "pmf p x \<le> measure (measure_pmf q) {y. R x y}"
      by(auto simp add: pmf.rep_eq)
    also have "\<dots> = 0" using * by(auto simp add: measure_pmf_zero_iff)
    finally show False using that by(auto dest: pmf_positive)
  qed
  have RanR: "\<exists>x\<in>set_pmf p. R x y" if "y \<in> set_pmf q" for y
  proof(rule ccontr)
    assume *: "\<not> ?thesis"
    then have "measure (measure_pmf q) {y. \<exists>x\<in>set_pmf p. R x y} + measure (measure_pmf q) {y} = measure (measure_pmf q) ({y. \<exists>x\<in>set_pmf p. R x y} \<union> {y})"
      by(intro measure_pmf.finite_measure_Union[symmetric]) auto
    also have "\<dots> \<le> 1" by simp
    also have "measure (measure_pmf p) (set_pmf p) = 1" by(simp add: measure_pmf.prob_eq_1 AE_measure_pmf)
    then have "1 \<le> measure (measure_pmf q) {y. \<exists>x\<in>set_pmf p. R x y}" using le[of "set_pmf p"] by auto
    ultimately have "measure (measure_pmf q) {y} \<le> 0" by auto
    with that show False by(auto dest: pmf_positive simp add: pmf.rep_eq)
  qed

  def edge' \<equiv> "\<lambda>xv yv. case (xv, yv) of
      (Source, Left x) \<Rightarrow> x \<in> set_pmf p
    | (Left x, Right y) \<Rightarrow> R x y \<and> x \<in> set_pmf p \<and> y \<in> set_pmf q
    | (Right y, Sink) \<Rightarrow> y \<in> set_pmf q
    | _ \<Rightarrow> False"
  have edge'_simps [simp]:
    "edge' xv (Left x) \<longleftrightarrow> xv = Source \<and> x \<in> set_pmf p"
    "edge' (Left x) (Right y) \<longleftrightarrow> R x y \<and> x \<in> set_pmf p \<and> y \<in> set_pmf q"
    "edge' (Right y) yv \<longleftrightarrow> yv = Sink \<and> y \<in> set_pmf q"
    "edge' Source (Right y) \<longleftrightarrow> False"
    "edge' Source Sink \<longleftrightarrow> False"
    "edge' xv Source \<longleftrightarrow> False"
    "edge' Sink yv \<longleftrightarrow> False"
    "edge' (Left x) Sink \<longleftrightarrow> False"
    for xv yv x y by(simp_all add: edge'_def split: vertex.split)
  have edge'_cases[cases pred]: thesis if "edge' xv yv" 
    "\<And>x. \<lbrakk> xv = Source; yv = Left x; x \<in> set_pmf p \<rbrakk> \<Longrightarrow> thesis" 
    "\<And>x y. \<lbrakk> xv = Left x; yv = Right y; R x y; x \<in> set_pmf p; y \<in> set_pmf q \<rbrakk> \<Longrightarrow> thesis"
    "\<And>y. \<lbrakk> xv = Right y; yv = Sink; y \<in> set_pmf q \<rbrakk> \<Longrightarrow> thesis"
    for thesis xv yv using that by(simp add: edge'_def split: prod.split_asm vertex.split_asm)
  have edge'_SourceE [elim!]: thesis if "edge' Source yv" "\<And>x. \<lbrakk> yv = Left x; x \<in> set_pmf p \<rbrakk> \<Longrightarrow> thesis"
    for yv thesis using that by(auto elim: edge'_cases)
  have edge'_LeftE [elim!]: thesis if "edge' (Left x) yv" "\<And>y. \<lbrakk> yv = Right y; R x y; x \<in> set_pmf p; y \<in> set_pmf q \<rbrakk> \<Longrightarrow> thesis"
    for x yv thesis using that by(auto elim: edge'_cases)
  have edge'_RightE [elim!]: thesis if "edge' xv (Right y)" "\<And>x. \<lbrakk> xv = Left x; R x y; x \<in> set_pmf p; y \<in> set_pmf q \<rbrakk> \<Longrightarrow> thesis"
    for xv y thesis using that by(auto elim: edge'_cases)
  have edge'_SinkE [elim!]: thesis if "edge' xv Sink" "\<And>y. \<lbrakk> xv = Right y; y \<in> set_pmf q \<rbrakk> \<Longrightarrow> thesis"
    for xv thesis using that by(auto elim: edge'_cases)
  have edge'1: "x \<in> set_pmf p \<Longrightarrow> edge' Source (Left x)"
    and edge'2: "\<lbrakk> R x y; x \<in> set_pmf p; y \<in> set_pmf q \<rbrakk> \<Longrightarrow> edge' (Left x) (Right y)"
    and edge'3: "y \<in> set_pmf q \<Longrightarrow> edge' (Right y) Sink"
    for x y by simp_all
  note edge'I[intro] = this
  
  def cap \<equiv> "(\<lambda>(xv, yv). case (xv, yv) of
      (Source, Left x) \<Rightarrow> pmf p x
    | (Left x, Right y) \<Rightarrow> if R x y \<and> x \<in> set_pmf p \<and> y \<in> set_pmf q then 2 else 0
    | (Right y, Sink) \<Rightarrow> pmf q y
    | _ \<Rightarrow> 0) :: ('a, 'b) vertex flow"
  have cap_simps [simp]:
    "cap (xv, Left x) = (if xv = Source then ereal (pmf p x) else 0)"
    "cap (Left x, Right y) = (if R x y \<and> x \<in> set_pmf p \<and> y \<in> set_pmf q then 2 else 0)"
    "cap (Right y, yv) = (if yv = Sink then ereal (pmf q y) else 0)"
    "cap (Source, Right y) = 0"
    "cap (Source, Sink) = 0"
    "cap (xv, Source) = 0"
    "cap (Sink, yv) = 0"
    "cap (Left x, Sink) = 0"
    for xv yv x y by(simp_all add: cap_def split: vertex.split)

  def \<Delta> \<equiv> "\<lparr>edge = edge', capacity = cap, source = Source, sink = Sink\<rparr>"
  write \<Delta> (structure)
  have \<Delta>_sel [simp]:
    "edge \<Delta> = edge'"
    "capacity \<Delta> = cap"
    "source \<Delta> = Source"
    "sink \<Delta> = Sink"
    by(simp_all add: \<Delta>_def)

  have IN_Left [simp]: "\<^bold>I\<^bold>N (Left x) = (if x \<in> set_pmf p then {Source} else {})" for x
    by(auto simp add: incoming_def)
  have OUT_Right [simp]: "\<^bold>O\<^bold>U\<^bold>T (Right y) = (if y \<in> set_pmf q then {Sink} else {})" for y
    by(auto simp add: outgoing_def)

  interpret network: countable_network \<Delta>
  proof
    show "source \<Delta> \<noteq> sink \<Delta>" by simp
    show "capacity \<Delta> e = 0" if "e \<notin> \<^bold>E" for e using that
      by(cases e)(auto simp add: edge'_def pmf_eq_0_set_pmf split: vertex.split_asm)
    show "0 \<le> capacity \<Delta> e" for e by(auto simp add: cap_def pmf_nonneg split: prod.split vertex.split)
    show "capacity \<Delta> e \<noteq> \<infinity>" for e by(auto simp add: cap_def split: prod.split vertex.split)
    have "\<^bold>E \<subseteq> ((Pair Source \<circ> Left) ` set_pmf p) \<union> (map_prod Left Right ` (set_pmf p \<times> set_pmf q)) \<union> ((\<lambda>y. (Right y, Sink)) ` set_pmf q)"
      by(auto elim: edge'_cases)
    thus "countable \<^bold>E" by(rule countable_subset) auto
  qed
  from network.max_flow_min_cut obtain f S 
    where f: "flow \<Delta> f" and cut: "cut \<Delta> S" and ortho: "orthogonal \<Delta> f S" by blast
  from cut obtain Source: "Source \<in> S" and Sink: "Sink \<notin> S" by cases simp

  have f_finite [simp]: "f e \<noteq> \<infinity>" "\<bar>f e\<bar> \<noteq> \<infinity>" "f e \<noteq> - \<infinity>" for e
    using network.flowD_finite[OF f, of e] flowD_nonneg[OF f, of e] by simp_all

  have OUT_cap_Source: "d_OUT cap Source = 1"
  proof -
    have "d_OUT cap Source = (\<Sum>\<^sup>+ y\<in>range Left. cap (Source, y))"
      by(auto 4 4 simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.capacity_outside[simplified] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y. pmf p y)" by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = 1" by(simp add: nn_integral_pmf)
    finally show ?thesis .
  qed
  have IN_cap_Left: "d_IN cap (Left x) = pmf p x" for x
    by(subst d_IN_alt_def[of _ \<Delta>])(simp_all add: pmf_eq_0_set_pmf pmf_nonneg nn_integral_count_space_indicator max_def)
  have OUT_cap_Right: "d_OUT cap (Right y) = pmf q y" for y
    by(subst d_OUT_alt_def[of _ \<Delta>])(simp_all add: pmf_eq_0_set_pmf pmf_nonneg nn_integral_count_space_indicator max_def)
  have IN_f_Left: "d_IN f (Left x) = f (Source, Left x)" for x
    by(subst d_IN_alt_def[of _ \<Delta>])(simp_all add: nn_integral_count_space_indicator max_def network.flowD_outside[OF f] flowD_nonneg[OF f])
  have OUT_f_Right: "d_OUT f (Right y) = f (Right y, Sink)" for y
    by(subst d_OUT_alt_def[of _ \<Delta>])(simp_all add: nn_integral_count_space_indicator max_def network.flowD_outside[OF f] flowD_nonneg[OF f])

  have S_LR: "Right y \<in> S" if Left: "Left x \<in> S" and edge: "R x y" "x \<in> set_pmf p" "y \<in> set_pmf q" for x y
  proof(rule ccontr)
    assume Right: "Right y \<notin> S"
    from edge have "edge \<Delta> (Left x) (Right y)" by simp
    from orthogonalD_out[OF ortho this Left Right] edge have "2 = f (Left x, Right y)" by simp
    also have "\<dots> \<le> d_OUT f (Left x)" unfolding d_OUT_def by(rule nn_integral_ge_point) simp
    also have "\<dots> = d_IN f (Left x)" using f by(rule flowD_KIR) simp_all
    also have "\<dots> \<le> d_IN cap (Left x)" using flowD_capacity_IN[OF f, of "Left x"] by simp
    also have "\<dots> = pmf p x" by(rule IN_cap_Left)
    also have "\<dots> \<le> 1" by(simp add: pmf_le_1)
    finally show False by simp
  qed

  have "value_flow \<Delta> f \<le> 1" using flowD_capacity_OUT[OF f, of Source] by(simp add: OUT_cap_Source)
  moreover have "1 \<le> value_flow \<Delta> f"
  proof -
    let ?L = "Left -` S \<inter> set_pmf p"
    let ?R = "{y|y x. x \<in> set_pmf p \<and> Left x \<in> S \<and> R x y \<and> y \<in> set_pmf q}"
    have "value_flow \<Delta> f = (\<Sum>\<^sup>+ x\<in>range Left. f (Source, x))" unfolding d_OUT_def
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x. f (Source, Left x) * indicator ?L x) + (\<Sum>\<^sup>+ x. f (Source, Left x) * indicator (- ?L) x)"
      by(subst nn_integral_add[symmetric])(auto simp add: flowD_nonneg[OF f] nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
    also have "(\<Sum>\<^sup>+ x. f (Source, Left x) * indicator (- ?L) x) = (\<Sum>\<^sup>+ x\<in>- ?L. cap (Source, Left x))"
      using orthogonalD_out[OF ortho _ Source]
      apply(auto simp add: set_pmf_iff network.flowD_outside[OF f] flowD_nonneg[OF f] nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      subgoal for x by(cases "x \<in> set_pmf p")(auto simp add: set_pmf_iff zero_ereal_def[symmetric] network.flowD_outside[OF f])
      done
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>- ?L. pmf p x)" by simp
    also have "\<dots> = emeasure (measure_pmf p) (- ?L)" by(simp add: nn_integral_pmf)
    also have "(\<Sum>\<^sup>+ x. f (Source, Left x) * indicator ?L x) = (\<Sum>\<^sup>+ x\<in>?L. d_IN f (Left x))"
      by(subst d_IN_alt_def[of _ \<Delta>])(auto simp add: network.flowD_outside[OF f] nn_integral_count_space_indicator max_def flowD_nonneg[OF f] intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>?L. d_OUT f (Left x))"
      by(rule nn_integral_cong flowD_KIR[OF f, symmetric])+ simp_all
    also have "\<dots> = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. f (Left x, y) * indicator (range Right) y * indicator ?L x)"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Right. \<Sum>\<^sup>+ x. f (Left x, y) * indicator ?L x)"
      by(subst nn_integral_fst_count_space[where f="case_prod _", simplified])
        (simp add: nn_integral_snd_count_space[where f="case_prod _", simplified] nn_integral_count_space_indicator nn_integral_cmult[symmetric] mult_ac)
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x)"
      by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x * indicator {y|x. Right y \<in> S \<and> x \<in> set_pmf p \<and> Left x \<in> S \<and> R x y \<and> y \<in> set_pmf q} y)"
      apply(rule nn_integral_cong)+
      subgoal for y x
        by(cases "R x y" "y \<in> set_pmf q" rule: bool.exhaust[case_product bool.exhaust])
          (auto split: split_indicator dest: S_LR simp add: network.flowD_outside[OF f])
      done
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?R y)"
      apply(rule nn_integral_cong)+
      subgoal for y x
        by(cases "R x y" "x \<in> set_pmf p" rule: bool.exhaust[case_product bool.exhaust])
          (auto split: split_indicator simp add: orthogonalD_in[OF ortho] network.flowD_outside[OF f] dest: S_LR)
      done
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R. \<Sum>\<^sup>+ x\<in>range Left. f (x, Right y))"
      by(simp add: nn_integral_count_space_reindex)(auto simp add:  nn_integral_count_space_indicator nn_integral_multc intro!: nn_integral_cong arg_cong2[where f="op *"] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R. d_IN f (Right y))"
      by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R. d_OUT f (Right y))" using flowD_KIR[OF f] by simp
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R. d_OUT cap (Right y))"
      by(auto 4 3 intro!: nn_integral_cong simp add: d_OUT_def network.flowD_outside[OF f] Sink dest: S_LR intro: orthogonalD_out[OF ortho, of "Right _" Sink, simplified])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R. pmf q y)" by(simp add: OUT_cap_Right)
    also have "\<dots> = emeasure (measure_pmf q) ?R"  by(simp add: nn_integral_pmf)
    also have "\<dots> \<ge> emeasure (measure_pmf p) ?L" using le[of ?L]
      by(auto elim!: order_trans simp add: measure_pmf.emeasure_eq_measure AE_measure_pmf_iff intro!: measure_pmf.finite_measure_mono_AE)
    ultimately have "value_flow \<Delta> f \<ge> emeasure (measure_pmf p) ?L + emeasure (measure_pmf p) (- ?L)"
      by(simp add: add_right_mono)
    also have "emeasure (measure_pmf p) ?L + emeasure (measure_pmf p) (- ?L) = emeasure (measure_pmf p) (?L \<union> - ?L)"
      by(subst plus_emeasure) auto
    also have "?L \<union> -?L = UNIV" by blast
    finally show ?thesis by simp
  qed
  ultimately have val: "value_flow \<Delta> f = 1" by simp

  have SAT_p: "f (Source, Left x) = pmf p x" for x
  proof(rule antisym)
    show "f (Source, Left x) \<le> pmf p x" using flowD_capacity[OF f, of "(Source, Left x)"] by simp
    show "pmf p x \<le> f (Source, Left x)"
    proof(rule ccontr)
      assume *: "\<not> ?thesis"
      have finite: "(\<Sum>\<^sup>+ y. f (Source, Left y) * indicator (- {x}) y) \<noteq> \<infinity>"
      proof -
        have "(\<Sum>\<^sup>+ y. f (Source, Left y) * indicator (- {x}) y) \<le> (\<Sum>\<^sup>+ y\<in>range Left. f (Source, y))"
          by(auto simp add: nn_integral_count_space_reindex flowD_nonneg[OF f] intro!: nn_integral_mono split: split_indicator)
        also have "\<dots> = value_flow \<Delta> f"
          by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
        finally show ?thesis using val by auto
      qed
      have "value_flow \<Delta> f = (\<Sum>\<^sup>+ y\<in>range Left. f (Source, y))"
        by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y. f (Source, Left y) * indicator (- {x}) y) + (\<Sum>\<^sup>+ y. f (Source, Left y) * indicator {x} y)"
        by(subst nn_integral_add[symmetric])(auto simp add: nn_integral_count_space_reindex flowD_nonneg[OF f] intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> < (\<Sum>\<^sup>+ y. f (Source, Left y) * indicator (- {x}) y) + (\<Sum>\<^sup>+ y. pmf p y * indicator {x} y)" using * finite
        by(auto simp add: max_def pmf_nonneg flowD_nonneg[OF f] not_le intro: ereal_less_add)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ y. pmf p y * indicator (- {x}) y) + (\<Sum>\<^sup>+ y. pmf p y * indicator {x} y)"
        using flowD_capacity[OF f, of "(Source, Left _)"]
        by(auto intro!: ereal_add_mono nn_integral_mono split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y. pmf p y)"
        by(subst nn_integral_add[symmetric])(auto simp add: pmf_nonneg intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = 1" unfolding nn_integral_pmf by simp
      finally show False using val by simp
    qed
  qed

  have IN_Sink: "d_IN f Sink = 1"
  proof -
    have "d_IN f Sink = (\<Sum>\<^sup>+ x\<in>range Right. f (x, Sink))" unfolding d_IN_def
      by(auto intro!: nn_integral_cong network.flowD_outside[OF f] simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y. d_OUT f (Right y))" by(simp add: nn_integral_count_space_reindex OUT_f_Right)
    also have "\<dots> = (\<Sum>\<^sup>+ y. d_IN f (Right y))" by(simp add: flowD_KIR[OF f])
    also have "\<dots> = (\<Sum>\<^sup>+ y. (\<Sum>\<^sup>+ x\<in>range Left. f (x, Right y)))"
      by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y))" by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. f (Left x, Right y))"
      by(subst nn_integral_fst_count_space[where f="case_prod _", simplified])(simp add: nn_integral_snd_count_space[where f="case_prod _", simplified])
    also have "\<dots> = (\<Sum>\<^sup>+ x. (\<Sum>\<^sup>+ y\<in>range Right. f (Left x, y)))"
      by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT f (Left x))" unfolding d_OUT_def
      by(auto intro!: nn_integral_cong network.flowD_outside[OF f] simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x. d_IN f (Left x))" by(simp add: flowD_KIR[OF f])
    also have "\<dots> = (\<Sum>\<^sup>+ x. pmf p x)" by(simp add: IN_f_Left SAT_p)
    also have "\<dots> = 1" unfolding nn_integral_pmf by simp
    finally show ?thesis .
  qed

  have SAT_q: "f (Right y, Sink) = pmf q y" for y
  proof(rule antisym)
    show "f (Right y, Sink) \<le> pmf q y" using flowD_capacity[OF f, of "(Right y, Sink)"] by simp
    show "pmf q y \<le> f (Right y, Sink)"
    proof(rule ccontr)
      assume *: "\<not> ?thesis"
      have finite: "(\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator (- {y}) x) \<noteq> \<infinity>"
      proof -
        have "(\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator (- {y}) x) \<le> (\<Sum>\<^sup>+ x\<in>range Right. f (x, Sink))"
          by(auto simp add: nn_integral_count_space_reindex flowD_nonneg[OF f] intro!: nn_integral_mono split: split_indicator)
        also have "\<dots> = d_IN f Sink"
          by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
        finally show ?thesis using IN_Sink by auto
      qed
      have "d_IN f Sink = (\<Sum>\<^sup>+ x\<in>range Right. f (x, Sink))"
        by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator (- {y}) x) + (\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator {y} x)"
        by(subst nn_integral_add[symmetric])(auto simp add: nn_integral_count_space_reindex flowD_nonneg[OF f] intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> < (\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator (- {y}) x) + (\<Sum>\<^sup>+ x. pmf q x * indicator {y} x)" using * finite
        by(auto simp add: max_def pmf_nonneg flowD_nonneg[OF f] not_le intro: ereal_less_add)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ x. pmf q x * indicator (- {y}) x) + (\<Sum>\<^sup>+ x. pmf q x * indicator {y} x)"
        using flowD_capacity[OF f, of "(Right _, Sink)"]
        by(auto intro!: ereal_add_mono nn_integral_mono split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x. pmf q x)"
        by(subst nn_integral_add[symmetric])(auto simp add: pmf_nonneg intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = 1" unfolding nn_integral_pmf by simp
      finally show False using IN_Sink by simp
    qed
  qed

  let ?z = "\<lambda>(x, y). real_of_ereal (f (Left x, Right y))"
  have nonneg: "\<And>xy. 0 \<le> ?z xy" by(clarsimp simp add: flowD_nonneg[OF f] real_of_ereal_pos)
  have prob: "(\<Sum>\<^sup>+ xy. ?z xy) = 1"
  proof -
    have "(\<Sum>\<^sup>+ xy. ?z xy) = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. (ereal \<circ> ?z) (x, y))"
      unfolding nn_integral_fst_count_space by(simp add: split_def o_def)
    also have "\<dots> = (\<Sum>\<^sup>+ x. (\<Sum>\<^sup>+y\<in>range Right. f (Left x, y)))"
      by(auto simp add: ereal_real flowD_nonneg[OF f] nn_integral_count_space_reindex intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT f (Left x))"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator split: split_indicator intro!: nn_integral_cong network.flowD_outside[OF f])
    also have "\<dots> = (\<Sum>\<^sup>+ x. d_IN f (Left x))" using flowD_KIR[OF f] by simp
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Left. f (Source, x))" by(simp add: nn_integral_count_space_reindex IN_f_Left)
    also have "\<dots> = value_flow \<Delta> f"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    finally show ?thesis using val by(simp)
  qed
  note z = nonneg prob
  def z \<equiv> "embed_pmf ?z"
  have z_sel [simp]: "pmf z (x, y) = real_of_ereal (f (Left x, Right y))" for x y
    by(simp add: z_def pmf_embed_pmf[OF z])

  show ?thesis
  proof
    show "R x y" if "(x, y) \<in> set_pmf z" for x y
      using that network.flowD_outside[OF f, of "(Left x, Right y)"] unfolding set_pmf_iff 
      by(auto simp add: real_of_ereal_eq_0)
    
    show "map_pmf fst z = p"
    proof(rule pmf_eqI)
      fix x
      have "pmf (map_pmf fst z) x = (\<Sum>\<^sup>+ e\<in>range (Pair x). pmf z e)"
        by(auto simp add: ereal_pmf_map nn_integral_measure_pmf nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Right. f (Left x, y))" by(simp add: nn_integral_count_space_reindex ereal_real)
      also have "\<dots> = d_OUT f (Left x)"
        by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = d_IN f (Left x)" by(rule flowD_KIR[OF f]) simp_all
      also have "\<dots> = f (Source, Left x)" by(simp add: IN_f_Left)
      also have "\<dots> = pmf p x" by(simp add: SAT_p)
      finally show "pmf (map_pmf fst z) x = pmf p x" by simp
    qed

    show "map_pmf snd z = q"
    proof(rule pmf_eqI)
      fix y
      have "pmf (map_pmf snd z) y = (\<Sum>\<^sup>+ e\<in>range (\<lambda>x. (x, y)). pmf z e)"
        by(auto simp add: ereal_pmf_map nn_integral_measure_pmf nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Left. f (x, Right y))" by(simp add: nn_integral_count_space_reindex ereal_real)
      also have "\<dots> = d_IN f (Right y)"
        by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = d_OUT f (Right y)" by(simp add: flowD_KIR[OF f])
      also have "\<dots> = f (Right y, Sink)" by(simp add: OUT_f_Right)
      also have "\<dots> = pmf q y" by(simp add: SAT_q)
      finally show "pmf (map_pmf snd z) y = pmf q y" by simp
    qed
  qed
qed

end

corollary rel_pmf_distr_mono: "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
-- \<open>This fact has already been proven for the registration of @{typ "'a pmf"} as a BNF, 
  but this proof is much shorter and more elegant. See @{cite HoelzlLochbihlerTraytel2015ITP} for a
  comparison of formalisations.\<close>
proof(intro le_funI le_boolI rel_pmf_measureI, elim relcomppE)
  fix p q r A
  assume pq: "rel_pmf R p q" and qr: "rel_pmf S q r"
  have "measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
    (is "_ \<le> measure _ ?B") using pq by(rule rel_pmf_measureD)
  also have "\<dots> \<le> measure (measure_pmf r) {z. \<exists>y\<in>?B. S y z}"
    using qr by(rule rel_pmf_measureD)
  also have "{z. \<exists>y\<in>?B. S y z} = {z. \<exists>x\<in>A. (R OO S) x z}" by auto
  finally show "measure (measure_pmf p) A \<le> measure (measure_pmf r) \<dots>" .
qed

end