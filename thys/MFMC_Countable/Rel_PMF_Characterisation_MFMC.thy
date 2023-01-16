(* Author: Andreas Lochbihler, Digital Asset *)

theory Rel_PMF_Characterisation_MFMC
imports 
  MFMC_Bounded 
  MFMC_Unbounded
  "HOL-Library.Simps_Case_Conv"
begin

section \<open>Characterisation of @{const rel_pmf} proved via MFMC\<close>

context begin

private datatype ('a, 'b) vertex = Source | Sink | Left 'a | Right 'b

private lemma inj_Left [simp]: "inj_on Left X"
by(simp add: inj_on_def)

private lemma inj_Right [simp]: "inj_on Right X"
by(simp add: inj_on_def)

context fixes p :: "'a pmf" and q :: "'b pmf" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" begin

private inductive edge' :: "('a, 'b) vertex \<Rightarrow> ('a, 'b) vertex \<Rightarrow> bool" where
  "edge' Source (Left x)" if "x \<in> set_pmf p"
| "edge' (Left x) (Right y)" if "R x y" "x \<in> set_pmf p" "y \<in> set_pmf q"
| "edge' (Right y) Sink" if "y \<in> set_pmf q"

private inductive_simps edge'_simps [simp]:
  "edge' xv (Left x)"
  "edge' (Left x) (Right y)"
  "edge' (Right y) yv"
  "edge' Source (Right y)"
  "edge' Source Sink"
  "edge' xv Source"
  "edge' Sink yv"
  "edge' (Left x) Sink"

private inductive_cases edge'_SourceE [elim!]: "edge' Source yv"
private inductive_cases edge'_LeftE [elim!]: "edge' (Left x) yv"
private inductive_cases edge'_RightE [elim!]: "edge' xv (Right y)"
private inductive_cases edge'_SinkE [elim!]: "edge' xv Sink"

private function cap :: "('a, 'b) vertex flow" where
  "cap (xv, Left x) = (if xv = Source then ennreal (pmf p x) else 0)"
| "cap (Left x, Right y) = 
  (if R x y \<and> x \<in> set_pmf p \<and> y \<in> set_pmf q 
   then pmf q y \<comment> \<open>Return @{term \<open>pmf q y\<close>} so that total weight of @{text \<open>x\<close>}'s neighbours is finite,
                    i.e., the network satisfies @{locale bounded_countable_network}.\<close>
   else 0)"
| "cap (Right y, yv) = (if yv = Sink then ennreal (pmf q y) else 0)"
| "cap (Source, Right y) = 0"
| "cap (Source, Sink) = 0"
| "cap (xv, Source) = 0"
| "cap (Sink, yv) = 0"
| "cap (Left x, Sink) = 0"
  by pat_completeness auto
termination by lexicographic_order

private definition \<Delta> :: "('a, 'b) vertex network"
  where "\<Delta> = \<lparr>edge = edge', capacity = cap, source = Source, sink = Sink\<rparr>"

private lemma \<Delta>_sel [simp]:
  "edge \<Delta> = edge'"
  "capacity \<Delta> = cap"
  "source \<Delta> = Source"
  "sink \<Delta> = Sink"
  by(simp_all add: \<Delta>_def)

private lemma IN_Left [simp]: "\<^bold>I\<^bold>N\<^bsub>\<Delta>\<^esub> (Left x) = (if x \<in> set_pmf p then {Source} else {})"
  by(auto simp add: incoming_def)
private lemma OUT_Right [simp]: "\<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Delta>\<^esub> (Right y) = (if y \<in> set_pmf q then {Sink} else {})"
  by(auto simp add: outgoing_def)

interpretation network: countable_network \<Delta>
proof
  show "source \<Delta> \<noteq> sink \<Delta>" by simp
  show "capacity \<Delta> e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>\<^esub>" for e using that
    by(cases e; cases "fst e"; cases "snd e")(auto simp add: pmf_eq_0_set_pmf)
  show "capacity \<Delta> e \<noteq> top" for e by(cases e rule: cap.cases)(auto)
  have "\<^bold>E\<^bsub>\<Delta>\<^esub> \<subseteq> ((Pair Source \<circ> Left) ` set_pmf p) \<union> (map_prod Left Right ` (set_pmf p \<times> set_pmf q)) \<union> ((\<lambda>y. (Right y, Sink)) ` set_pmf q)"
    by(auto elim: edge'.cases)
  thus "countable \<^bold>E\<^bsub>\<Delta>\<^esub>" by(rule countable_subset) auto
qed

private lemma OUT_cap_Source: "d_OUT cap Source = 1"
proof -
  have "d_OUT cap Source = (\<Sum>\<^sup>+ y\<in>range Left. cap (Source, y))"
    by(auto 4 4 simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.capacity_outside[simplified] split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y. pmf p y)" by(simp add: nn_integral_count_space_reindex)
  also have "\<dots> = 1" by(simp add: nn_integral_pmf)
  finally show ?thesis .
qed
private lemma IN_cap_Left: "d_IN cap (Left x) = pmf p x"
  by(subst d_IN_alt_def[of _ \<Delta>])(simp_all add: pmf_eq_0_set_pmf nn_integral_count_space_indicator max_def)
private lemma OUT_cap_Right: "d_OUT cap (Right y) = pmf q y"
  by(subst d_OUT_alt_def[of _ \<Delta>])(simp_all add: pmf_eq_0_set_pmf nn_integral_count_space_indicator max_def)

private lemma rel_pmf_measureI_aux:
  assumes ex_flow: "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
    and le: "\<And>A. measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
  shows "rel_pmf R p q"
proof -
  from ex_flow obtain f S
    where f: "flow \<Delta> f" and cut: "cut \<Delta> S" and ortho: "orthogonal \<Delta> f S" by blast
  from cut obtain Source: "Source \<in> S" and Sink: "Sink \<notin> S" by cases simp

  have f_finite [simp]: "f e < top" for e
    using network.flowD_finite[OF f, of e] by (simp_all add: less_top)

  have IN_f_Left: "d_IN f (Left x) = f (Source, Left x)" for x
    by(subst d_IN_alt_def[of _ \<Delta>])(simp_all add: nn_integral_count_space_indicator max_def network.flowD_outside[OF f])
  have OUT_f_Right: "d_OUT f (Right y) = f (Right y, Sink)" for y
    by(subst d_OUT_alt_def[of _ \<Delta>])(simp_all add: nn_integral_count_space_indicator max_def network.flowD_outside[OF f])

  have "value_flow \<Delta> f \<le> 1" using flowD_capacity_OUT[OF f, of Source] by(simp add: OUT_cap_Source)
  moreover have "1 \<le> value_flow \<Delta> f"
  proof -
    let ?L = "Left -` S \<inter> set_pmf p"
    let ?R' = "{y|y x. x \<in> set_pmf p \<and> Left x \<in> S \<and> R x y \<and> y \<in> set_pmf q \<and> Right y \<in> S}"
    let ?R'' = "{y|y x. x \<in> set_pmf p \<and> Left x \<in> S \<and> R x y \<and> y \<in> set_pmf q \<and> \<not> Right y \<in> S}"
    have "value_flow \<Delta> f = (\<Sum>\<^sup>+ x\<in>range Left. f (Source, x))" unfolding d_OUT_def
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x. f (Source, Left x) * indicator ?L x) + (\<Sum>\<^sup>+ x. f (Source, Left x) * indicator (- ?L) x)"
      by(subst nn_integral_add[symmetric])(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
    also have "(\<Sum>\<^sup>+ x. f (Source, Left x) * indicator (- ?L) x) = (\<Sum>\<^sup>+ x\<in>- ?L. cap (Source, Left x))"
      using orthogonalD_out[OF ortho _ Source]
      apply(auto simp add: set_pmf_iff network.flowD_outside[OF f] nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      subgoal for x by(cases "x \<in> set_pmf p")(auto simp add: set_pmf_iff network.flowD_outside[OF f])
      done
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>- ?L. pmf p x)" by simp
    also have "\<dots> = emeasure p (- ?L)" by(simp add: nn_integral_pmf)
    also have "(\<Sum>\<^sup>+ x. f (Source, Left x) * indicator ?L x) = (\<Sum>\<^sup>+ x\<in>?L. d_IN f (Left x))"
      by(subst d_IN_alt_def[of _ \<Delta>])(auto simp add: network.flowD_outside[OF f] nn_integral_count_space_indicator intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>?L. d_OUT f (Left x))"
      by(rule nn_integral_cong flowD_KIR[OF f, symmetric])+ simp_all
    also have "\<dots> = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. f (Left x, y) * indicator (range Right) y * indicator ?L x)"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Right. \<Sum>\<^sup>+ x. f (Left x, y) * indicator ?L x)"
      by(subst nn_integral_fst_count_space[where f="case_prod _", simplified])
        (simp add: nn_integral_snd_count_space[where f="case_prod _", simplified] nn_integral_count_space_indicator nn_integral_cmult[symmetric] mult_ac)
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x)"
      by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x * indicator ?R' y) +
      (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x * indicator ?R'' y)"
      by(subst nn_integral_add[symmetric]; simp)
        (subst nn_integral_add[symmetric]; auto intro!: nn_integral_cong split: split_indicator intro!: network.flowD_outside[OF f])
    also have "(\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x * indicator ?R' y) =
       (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?R' y)"
      apply(clarsimp simp add: network.flowD_outside[OF f] intro!: nn_integral_cong split: split_indicator)
      subgoal for y x by(cases "edge \<Delta> (Left x) (Right y)")(auto intro: orthogonalD_in[OF ortho] network.flowD_outside[OF f])
      done
    also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x\<in>range Left. f (x, Right y) * indicator ?R' y)"
      by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R'. d_IN f (Right y))"
      by(subst d_IN_alt_def[of _ \<Delta>])(auto simp add: network.flowD_outside[OF f] nn_integral_count_space_indicator incoming_def intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R'. d_OUT f (Right y))" using flowD_KIR[OF f] by simp
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R'. d_OUT cap (Right y))"
      by(auto 4 3 intro!: nn_integral_cong simp add: d_OUT_def network.flowD_outside[OF f] Sink dest: intro: orthogonalD_out[OF ortho, of "Right _" Sink, simplified])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?R'. pmf q y)" by(simp add: OUT_cap_Right)
    also have "\<dots> = emeasure q ?R'" by(simp add: nn_integral_pmf)
    also have "(\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. f (Left x, Right y) * indicator ?L x * indicator ?R'' y) \<ge> emeasure q ?R''" (is "?lhs \<ge> _")
    proof -
      have "?lhs = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. (if R x y then pmf q y else 0) * indicator ?L x * indicator ?R'' y)"
        by(rule nn_integral_cong)+(auto split: split_indicator simp add: network.flowD_outside[OF f] simp add: orthogonalD_out[OF ortho, of "Left _" "Right _", simplified])
      also have "\<dots> \<ge> (\<Sum>\<^sup>+ y. pmf q y * indicator ?R'' y)"
        by(rule nn_integral_mono)(auto split: split_indicator intro: order_trans[OF _ nn_integral_ge_point])
      also have "(\<Sum>\<^sup>+ y. pmf q y * indicator ?R'' y) = (\<Sum>\<^sup>+ y\<in>?R''. pmf q y)" 
        by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      finally show ?thesis by(simp add: nn_integral_pmf)
    qed
    ultimately have "value_flow \<Delta> f \<ge> emeasure q ?R' + emeasure q ?R'' + emeasure p (- ?L)"
      by(simp add: add_right_mono)
    also have "emeasure q ?R' + emeasure q ?R'' = emeasure q {y|y x. x \<in> set_pmf p \<and> Left x \<in> S \<and> R x y \<and> y \<in> set_pmf q}"
      by(subst plus_emeasure)(auto intro!: arg_cong2[where f=emeasure])
    also have "\<dots> \<ge> emeasure p ?L" using le[of ?L]
      by(auto elim!: order_trans simp add: measure_pmf.emeasure_eq_measure AE_measure_pmf_iff intro!: measure_pmf.finite_measure_mono_AE)
    ultimately have "value_flow \<Delta> f \<ge> emeasure (measure_pmf p) ?L + emeasure (measure_pmf p) (- ?L)"
      by (smt (verit, best) add_right_mono inf.absorb_iff2 le_inf_iff)
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
          by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_mono split: split_indicator)
        also have "\<dots> = value_flow \<Delta> f"
          by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
        finally show ?thesis using val by (auto simp: top_unique)
      qed
      have "value_flow \<Delta> f = (\<Sum>\<^sup>+ y\<in>range Left. f (Source, y))"
        by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y. f (Source, Left y) * indicator (- {x}) y) + (\<Sum>\<^sup>+ y. f (Source, Left y) * indicator {x} y)"
        by(subst nn_integral_add[symmetric])(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> < (\<Sum>\<^sup>+ y. f (Source, Left y) * indicator (- {x}) y) + (\<Sum>\<^sup>+ y. pmf p y * indicator {x} y)" using * finite
        by(auto simp add:)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ y. pmf p y * indicator (- {x}) y) + (\<Sum>\<^sup>+ y. pmf p y * indicator {x} y)"
        using flowD_capacity[OF f, of "(Source, Left _)"]
        by(auto intro!: nn_integral_mono split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y. pmf p y)"
        by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
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
          by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_mono split: split_indicator)
        also have "\<dots> = d_IN f Sink"
          by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
        finally show ?thesis using IN_Sink by (auto simp: top_unique)
      qed
      have "d_IN f Sink = (\<Sum>\<^sup>+ x\<in>range Right. f (x, Sink))"
        by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator (- {y}) x) + (\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator {y} x)"
        by(subst nn_integral_add[symmetric])(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> < (\<Sum>\<^sup>+ x. f (Right x, Sink) * indicator (- {y}) x) + (\<Sum>\<^sup>+ x. pmf q x * indicator {y} x)" using * finite
        by auto
      also have "\<dots> \<le> (\<Sum>\<^sup>+ x. pmf q x * indicator (- {y}) x) + (\<Sum>\<^sup>+ x. pmf q x * indicator {y} x)"
        using flowD_capacity[OF f, of "(Right _, Sink)"]
        by(auto intro!: nn_integral_mono split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x. pmf q x)"
        by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = 1" unfolding nn_integral_pmf by simp
      finally show False using IN_Sink by simp
    qed
  qed

  let ?z = "\<lambda>(x, y). enn2real (f (Left x, Right y))"
  have nonneg: "\<And>xy. 0 \<le> ?z xy" by clarsimp
  have prob: "(\<Sum>\<^sup>+ xy. ?z xy) = 1"
  proof -
    have "(\<Sum>\<^sup>+ xy. ?z xy) = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. (ennreal \<circ> ?z) (x, y))"
      unfolding nn_integral_fst_count_space by(simp add: split_def o_def)
    also have "\<dots> = (\<Sum>\<^sup>+ x. (\<Sum>\<^sup>+y\<in>range Right. f (Left x, y)))"
      by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT f (Left x))"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator split: split_indicator intro!: nn_integral_cong network.flowD_outside[OF f])
    also have "\<dots> = (\<Sum>\<^sup>+ x. d_IN f (Left x))" using flowD_KIR[OF f] by simp
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Left. f (Source, x))" by(simp add: nn_integral_count_space_reindex IN_f_Left)
    also have "\<dots> = value_flow \<Delta> f"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
    finally show ?thesis using val by(simp)
  qed
  note z = nonneg prob
  define z where "z = embed_pmf ?z"
  have z_sel [simp]: "pmf z (x, y) = enn2real (f (Left x, Right y))" for x y
    by(simp add: z_def pmf_embed_pmf[OF z])

  show ?thesis
  proof
    show "R x y" if "(x, y) \<in> set_pmf z" for x y
      using that network.flowD_outside[OF f, of "(Left x, Right y)"] unfolding set_pmf_iff
      by(auto simp add: enn2real_eq_0_iff)

    show "map_pmf fst z = p"
    proof(rule pmf_eqI)
      fix x
      have "pmf (map_pmf fst z) x = (\<Sum>\<^sup>+ e\<in>range (Pair x). pmf z e)"
        by(auto simp add: ennreal_pmf_map nn_integral_measure_pmf nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Right. f (Left x, y))" by(simp add: nn_integral_count_space_reindex)
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
        by(auto simp add: ennreal_pmf_map nn_integral_measure_pmf nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Left. f (x, Right y))" by(simp add: nn_integral_count_space_reindex)
      also have "\<dots> = d_IN f (Right y)"
        by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_cong network.flowD_outside[OF f] split: split_indicator)
      also have "\<dots> = d_OUT f (Right y)" by(simp add: flowD_KIR[OF f])
      also have "\<dots> = f (Right y, Sink)" by(simp add: OUT_f_Right)
      also have "\<dots> = pmf q y" by(simp add: SAT_q)
      finally show "pmf (map_pmf snd z) y = pmf q y" by simp
    qed
  qed
qed

proposition rel_pmf_measureI_unbounded: \<comment> \<open>Proof uses the unbounded max-flow min-cut theorem\<close>
  assumes le: "\<And>A. measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
  shows "rel_pmf R p q"
  using assms by(rule rel_pmf_measureI_aux[OF network.max_flow_min_cut])

interpretation network: bounded_countable_network \<Delta>
proof
  have OUT_Left: "d_OUT cap (Left x) \<le> 1" for x
  proof -
    have "d_OUT cap (Left x) \<le> (\<Sum>\<^sup>+ y\<in>range Right. cap (Left x, y))"
      by(subst d_OUT_alt_def[of _ \<Delta>])(auto intro: network.capacity_outside[simplified] intro!: nn_integral_mono simp add: nn_integral_count_space_indicator outgoing_def split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y. cap (Left x, Right y))" by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> \<le> (\<Sum>\<^sup>+ y. pmf q y)" by(rule nn_integral_mono)(simp)
    also have "\<dots> = 1" by(simp add: nn_integral_pmf)
    finally show ?thesis .
  qed
  show "d_OUT (capacity \<Delta>) x < \<top>" if "x \<in> \<^bold>V\<^bsub>\<Delta>\<^esub>" "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" for x
    using that by(cases x)(auto simp add: OUT_cap_Right intro: le_less_trans[OF OUT_Left])
qed

proposition rel_pmf_measureI_bounded: \<comment> \<open>Proof uses the bounded max-flow min-cut theorem\<close>
  assumes le: "\<And>A. measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
  shows "rel_pmf R p q"
  using assms by(rule rel_pmf_measureI_aux[OF network.max_flow_min_cut_bounded])

end

end

interpretation rel_spmf_characterisation by unfold_locales(rule rel_pmf_measureI_bounded)

corollary rel_pmf_distr_mono: "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
\<comment> \<open>This fact has already been proven for the registration of @{typ "'a pmf"} as a BNF,
  but this proof is much shorter and more elegant. See \<^cite>\<open>HoelzlLochbihlerTraytel2015ITP\<close> for a
  comparison of formalisations.\<close>
proof(intro le_funI le_boolI rel_pmf_measureI_bounded, elim relcomppE)
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
