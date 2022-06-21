theory Metric_Point_Structure
  imports Interval
begin

(* Conversion from the abstract time domain (Definition 4.1) introduced
   in the paper ``Specifying Real-Time Properties with Metric Temporal Logic''
   (Koymans, 1990) to our time-stamps. *)

(* Metric domain. *)

class metric_domain = plus + zero + ord +
  assumes \<Delta>1: "x + x' = x' + x"
    and \<Delta>2: "(x + x') + x'' = x + (x' + x'')"
    and \<Delta>3: "x + 0 = x"
    and \<Delta>3': "x = 0 + x"
    and \<Delta>4: "x + x' = x + x'' \<Longrightarrow> x' = x''"
    and \<Delta>4': "x + x'' = x' + x'' \<Longrightarrow> x = x'"
    and \<Delta>5: "x + x' = 0 \<Longrightarrow> x = 0"
    and \<Delta>5': "x + x' = 0 \<Longrightarrow> x' = 0"
    and \<Delta>6: "\<exists>x''. x = x' + x'' \<or> x' = x + x''"
    and metric_domain_le_def: "x \<le> x' \<longleftrightarrow> (\<exists>x''. x' = x + x'')"
    and metric_domain_lt_def: "x < x' \<longleftrightarrow> (\<exists>x''. x'' \<noteq> 0 \<and> x' = x + x'')"
begin

lemma metric_domain_pos: "x \<ge> 0"
  using \<Delta>3' local.metric_domain_le_def by auto

lemma less_eq_le_neq: "x < x' \<longleftrightarrow> (x \<le> x' \<and> x \<noteq> x')"
  apply (auto simp: metric_domain_le_def metric_domain_lt_def)
   apply (metis \<Delta>3 \<Delta>4)
  apply (metis \<Delta>3)
  done

end

(* Metric domain extended with embedding of natural numbers and syntactically extended with sup, tfin. *)

class metric_domain_timestamp = metric_domain + sup + embed_nat + tfin +
  assumes metric_domain_sup_def: "sup x x' = (if x \<le> x' then x' else x)"
    and metric_domain_\<iota>_mono: "\<And>i j. i \<le> j \<Longrightarrow> \<iota> i \<le> \<iota> j"
    and metric_domain_\<iota>_progressing: "\<exists>j. \<not>\<iota> j \<le> \<iota> i + x"
    and metric_domain_tfin_def: "tfin = UNIV"

subclass (in metric_domain_timestamp) timestamp
  apply unfold_locales
                  apply (auto simp: \<Delta>2)[1]
                 apply (auto simp: \<Delta>1)[1]
                apply (auto simp: \<Delta>3'[symmetric])[1]
  subgoal for x y
    apply (auto simp: metric_domain_le_def metric_domain_lt_def)
     apply (metis \<Delta>2 \<Delta>3 \<Delta>4 \<Delta>5)
    apply (metis \<Delta>2 \<Delta>3)
    done
  using \<Delta>6 apply (auto simp: metric_domain_le_def)[1]
  using \<Delta>2 apply (auto simp: metric_domain_le_def)[1]
  subgoal for x y
    apply (auto simp: metric_domain_le_def metric_domain_lt_def)
    apply (metis \<Delta>2 \<Delta>3 \<Delta>4 \<Delta>5)
    done
  using \<Delta>6 apply (fastforce simp: metric_domain_le_def metric_domain_sup_def)
  using \<Delta>6 apply (fastforce simp: metric_domain_le_def metric_domain_sup_def)
         apply (auto simp: metric_domain_le_def metric_domain_sup_def)[1]
  using metric_domain_\<iota>_mono apply (auto simp: metric_domain_le_def)[1]
       apply (auto simp: metric_domain_tfin_def)[1]
  using metric_domain_\<iota>_progressing apply (auto simp: metric_domain_le_def)[1]
     apply (auto simp: metric_domain_tfin_def)[2]
  using \<Delta>2 apply (auto simp: metric_domain_le_def)[1]
  using \<Delta>1 \<Delta>3 apply (auto simp: metric_domain_lt_def)
  done

(* Metric point structure.
   We map Koymans' time-stamps t in a trace to d t0 t, where t0 is the initial time-stamp of the trace.
   Because Koymans assumes the strict precedence relation on time-stamps to be
   ``transitive, irreflexive and comparable'', the precedence relation is actually a partial order. *)

locale metric_point_structure =
  fixes d :: "'t :: {order} \<Rightarrow> 't \<Rightarrow> 'd :: metric_domain_timestamp"
  assumes d1: "d t t' = 0 \<longleftrightarrow> t = t'"
    and d2: "d t t' = d t' t"
    and d3: "t < t' \<Longrightarrow> t' < t'' \<Longrightarrow> d t t'' = d t t' + d t' t''"
    and d3': "t < t' \<Longrightarrow> t' < t'' \<Longrightarrow> d t'' t = d t'' t' + d t' t"
begin

lemma metric_point_structure_memL_aux: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> x \<le> d t t' \<longleftrightarrow> (d t0 t + x \<le> d t0 t')"
  apply (rule iffI)
   apply (metis \<Delta>1 add_0 add_mono_comm d1 d3 order_le_less)
  apply (cases "t0 < t"; cases "t < t'")
     apply (auto simp: metric_domain_le_def)
     apply (metis \<Delta>4 ab_semigroup_add_class.add_ac(1) d3)
    apply (metis comm_monoid_add_class.add_0 group_cancel.add1 metric_domain_lt_def nless_le)
   apply (metis \<Delta>3' d1)
  apply (metis add_0 d1)
  done

lemma metric_point_structure_memL_strict_aux: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> x < d t t' \<longleftrightarrow> (d t0 t + x < d t0 t')"
  using metric_point_structure_memL_aux[of t0 t t' x]
  apply auto
   apply (metis (no_types, lifting) \<Delta>1 \<Delta>3 \<Delta>4 antisym_conv2 d1 d3)
  apply (metis \<Delta>1 add_0 d1 d3 order.order_iff_strict order_less_irrefl)
  done

lemma metric_point_structure_memR_aux: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> d t t' \<le> x \<longleftrightarrow> (d t0 t' \<le> d t0 t + x)"
  apply auto
   apply (metis \<Delta>1 \<Delta>3 d1 d3 order_le_less add_mono)
  apply (smt (verit, ccfv_threshold) \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4 d1 d3 metric_domain_le_def order_le_less)
  done

lemma metric_point_structure_memR_strict_aux: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> d t t' < x \<longleftrightarrow> (d t0 t' < d t0 t + x)"
  by (auto simp add: metric_point_structure_memL_aux metric_point_structure_memR_aux less_le_not_le)

lemma metric_point_structure_le_mem: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> d t t' \<le> x \<longleftrightarrow> mem (d t0 t) (d t0 t') (interval 0 x True True)"
  unfolding mem_def
  apply (transfer fixing: d)
  using metric_point_structure_memR_aux
  apply (auto simp: metric_domain_le_def metric_domain_tfin_def)
  apply (metis add.right_neutral d3 order.order_iff_strict)
  done

lemma metric_point_structure_lt_mem: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> 0 < x \<Longrightarrow> d t t' < x \<longleftrightarrow> mem (d t0 t) (d t0 t') (interval 0 x True False)"
  unfolding mem_def
  apply (transfer fixing: d)
  using metric_point_structure_memR_strict_aux
  apply (auto simp: metric_domain_tfin_def)
  apply (metis \<Delta>3 metric_domain_pos metric_point_structure_memL_aux)
  done

lemma metric_point_structure_eq_mem: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> d t t' = x \<longleftrightarrow> mem (d t0 t) (d t0 t') (interval x x True True)"
  unfolding mem_def
  apply (transfer fixing: d)
  subgoal for t0 t t' x
    using metric_point_structure_memL_aux[of t0 t t' x] metric_point_structure_memR_aux[of t0 t t' x] metric_domain_pos
    by (auto simp: metric_domain_tfin_def)
  done

lemma metric_point_structure_ge_mem: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> x \<le> d t t' \<longleftrightarrow> mem (Some (d t0 t)) (Some (d t0 t')) (interval (Some x) None True True)"
  unfolding mem_def
  apply (transfer fixing: d)
  using metric_point_structure_memL_aux by (auto simp: tfin_option_def zero_option_def plus_option_def less_eq_option_def metric_domain_le_def metric_domain_tfin_def split: option.splits)

lemma metric_point_structure_gt_mem: "t0 \<le> t \<Longrightarrow> t \<le> t' \<Longrightarrow> x < d t t' \<longleftrightarrow> mem (Some (d t0 t)) (Some (d t0 t')) (interval (Some x) None False True)"
  unfolding mem_def
  apply (transfer fixing: d)
  using metric_point_structure_memL_strict_aux by (auto simp: tfin_option_def zero_option_def plus_option_def less_option_def less_eq_option_def metric_domain_le_def metric_domain_tfin_def split: option.splits)

end

instantiation nat :: metric_domain_timestamp
begin

instance
  apply standard
               apply auto[8]
        apply (meson less_eqE timestamp_total)
  using nat_le_iff_add apply blast
  using less_imp_add_positive apply auto[1]
     apply (auto simp: sup_max)[1]
    apply (auto simp: \<iota>_nat_def)[1]
  subgoal for i x
    apply (auto simp: \<iota>_nat_def)
    using add_le_same_cancel1 by blast
  apply (auto simp: tfin_nat_def)
  done

end

interpretation nat_metric_point_structure: metric_point_structure "\<lambda>t :: nat. \<lambda>t'. if t \<le> t' then t' - t else t - t'"
  by unfold_locales auto

end
