theory Dinitz_Garg_Goemans_Counterexample
  imports Complex_Main
begin

section \<open>Finite path-flow instances\<close>

text \<open>
  We use a path-based formulation of single-source flow.  A route records one
  admissible source-to-terminal path, and @{term pf_uses} is its arc-incidence
  predicate.  The finite carrier types make all loads and costs explicit finite
  sums.
\<close>

record ('commodity, 'route, 'arc) path_flow_instance =
  pf_admissible :: "'commodity \<Rightarrow> 'route \<Rightarrow> bool"
  pf_demand :: "'commodity \<Rightarrow> real"
  pf_capacity :: "'arc \<Rightarrow> real"
  pf_cost :: "'arc \<Rightarrow> real"
  pf_uses :: "'commodity \<Rightarrow> 'route \<Rightarrow> 'arc \<Rightarrow> bool"

definition fractional_load ::
    "('commodity::finite, 'route::finite, 'arc) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow> 'arc \<Rightarrow> real" where
  "fractional_load I f a =
     (\<Sum>k\<in>UNIV. \<Sum>r\<in>UNIV. if pf_uses I k r a then f k r else 0)"

definition fractional_cost ::
    "('commodity::finite, 'route::finite, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow> real" where
  "fractional_cost I f =
     (\<Sum>a\<in>UNIV. pf_cost I a * fractional_load I f a)"

definition maximum_demand ::
    "('commodity::finite, 'route, 'arc) path_flow_instance \<Rightarrow> real" where
  "maximum_demand I = Max (pf_demand I ` (UNIV :: 'commodity set))"

definition well_formed_instance ::
    "('commodity, 'route, 'arc) path_flow_instance \<Rightarrow> bool" where
  "well_formed_instance I \<longleftrightarrow>
     (\<forall>k. 0 < pf_demand I k \<and> (\<exists>r. pf_admissible I k r)) \<and>
     (\<forall>a. 0 \<le> pf_capacity I a \<and> 0 \<le> pf_cost I a)"

definition fractional_feasible ::
    "('commodity::finite, 'route::finite, 'arc) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow> bool" where
  "fractional_feasible I f \<longleftrightarrow>
     well_formed_instance I \<and>
     (\<forall>k r. 0 \<le> f k r) \<and>
     (\<forall>k r. \<not> pf_admissible I k r \<longrightarrow> f k r = 0) \<and>
     (\<forall>k. (\<Sum>r\<in>UNIV. f k r) = pf_demand I k) \<and>
     (\<forall>a. fractional_load I f a \<le> pf_capacity I a)"

definition unsplittable_routing ::
    "('commodity, 'route, 'arc) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route) \<Rightarrow> bool" where
  "unsplittable_routing I q \<longleftrightarrow> (\<forall>k. pf_admissible I k (q k))"

definition unsplittable_load ::
    "('commodity::finite, 'route, 'arc) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route) \<Rightarrow> 'arc \<Rightarrow> real" where
  "unsplittable_load I q a =
     (\<Sum>k\<in>UNIV. if pf_uses I k (q k) a then pf_demand I k else 0)"

definition unsplittable_cost ::
    "('commodity::finite, 'route, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route) \<Rightarrow> real" where
  "unsplittable_cost I q =
     (\<Sum>a\<in>UNIV. pf_cost I a * unsplittable_load I q a)"

definition weak_dgg_rounding ::
    "('commodity::finite, 'route::finite, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow>
     ('commodity \<Rightarrow> 'route) \<Rightarrow> bool" where
  "weak_dgg_rounding I f q \<longleftrightarrow>
     unsplittable_routing I q \<and>
     (\<forall>a. unsplittable_load I q a
        \<le> fractional_load I f a + maximum_demand I) \<and>
     unsplittable_cost I q \<le> fractional_cost I f"

definition strict_dgg_rounding ::
    "('commodity::finite, 'route::finite, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow>
     ('commodity \<Rightarrow> 'route) \<Rightarrow> bool" where
  "strict_dgg_rounding I f q \<longleftrightarrow>
     unsplittable_routing I q \<and>
     (\<forall>a. unsplittable_load I q a
        < fractional_load I f a + maximum_demand I) \<and>
     unsplittable_cost I q \<le> fractional_cost I f"

definition weak_dgg_property ::
    "('commodity::finite, 'route::finite, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow> bool" where
  "weak_dgg_property I f \<longleftrightarrow> (\<exists>q. weak_dgg_rounding I f q)"

definition strict_dgg_property ::
    "('commodity::finite, 'route::finite, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow> bool" where
  "strict_dgg_property I f \<longleftrightarrow> (\<exists>q. strict_dgg_rounding I f q)"

definition dgg_counterexample ::
    "('commodity::finite, 'route::finite, 'arc::finite) path_flow_instance \<Rightarrow>
     ('commodity \<Rightarrow> 'route \<Rightarrow> real) \<Rightarrow> bool" where
  "dgg_counterexample I f \<longleftrightarrow>
     well_formed_instance I \<and> fractional_feasible I f \<and>
     \<not> weak_dgg_property I f"

lemma strict_dgg_rounding_imp_weak:
  "strict_dgg_rounding I f q \<Longrightarrow> weak_dgg_rounding I f q"
  unfolding strict_dgg_rounding_def weak_dgg_rounding_def
  by (blast intro: less_imp_le)

section \<open>The directed graph and all of its terminal paths\<close>

datatype vertex =
    Source
  | Junction_U
  | Junction_V
  | Junction_W
  | Terminal_1
  | Terminal_2
  | Terminal_3

datatype commodity = Commodity_1 | Commodity_2 | Commodity_3

datatype arc =
    S_T1
  | S_T2
  | S_U
  | U_V
  | U_T3
  | V_T1
  | V_W
  | W_T2
  | W_T3

datatype route_choice = Paid | Free

fun arc_tail :: "arc \<Rightarrow> vertex" where
  "arc_tail S_T1 = Source"
| "arc_tail S_T2 = Source"
| "arc_tail S_U = Source"
| "arc_tail U_V = Junction_U"
| "arc_tail U_T3 = Junction_U"
| "arc_tail V_T1 = Junction_V"
| "arc_tail V_W = Junction_V"
| "arc_tail W_T2 = Junction_W"
| "arc_tail W_T3 = Junction_W"

fun arc_head :: "arc \<Rightarrow> vertex" where
  "arc_head S_T1 = Terminal_1"
| "arc_head S_T2 = Terminal_2"
| "arc_head S_U = Junction_U"
| "arc_head U_V = Junction_V"
| "arc_head U_T3 = Terminal_3"
| "arc_head V_T1 = Terminal_1"
| "arc_head V_W = Junction_W"
| "arc_head W_T2 = Terminal_2"
| "arc_head W_T3 = Terminal_3"

fun commodity_terminal :: "commodity \<Rightarrow> vertex" where
  "commodity_terminal Commodity_1 = Terminal_1"
| "commodity_terminal Commodity_2 = Terminal_2"
| "commodity_terminal Commodity_3 = Terminal_3"

fun edge_path :: "vertex \<Rightarrow> arc list \<Rightarrow> vertex \<Rightarrow> bool" where
  "edge_path u [] v = (u = v)"
| "edge_path u (a # as) v =
     (arc_tail a = u \<and> edge_path (arc_head a) as v)"

lemma arc_tail_eq_source [simp]:
  "arc_tail a = Source \<longleftrightarrow> a = S_T1 \<or> a = S_T2 \<or> a = S_U"
  by (cases a) simp_all

lemma arc_tail_eq_junction_u [simp]:
  "arc_tail a = Junction_U \<longleftrightarrow> a = U_V \<or> a = U_T3"
  by (cases a) simp_all

lemma arc_tail_eq_junction_v [simp]:
  "arc_tail a = Junction_V \<longleftrightarrow> a = V_T1 \<or> a = V_W"
  by (cases a) simp_all

lemma arc_tail_eq_junction_w [simp]:
  "arc_tail a = Junction_W \<longleftrightarrow> a = W_T2 \<or> a = W_T3"
  by (cases a) simp_all

lemma arc_tail_eq_terminal_1 [simp]:
  "arc_tail a = Terminal_1 \<longleftrightarrow> False"
  by (cases a) simp_all

lemma arc_tail_eq_terminal_2 [simp]:
  "arc_tail a = Terminal_2 \<longleftrightarrow> False"
  by (cases a) simp_all

lemma arc_tail_eq_terminal_3 [simp]:
  "arc_tail a = Terminal_3 \<longleftrightarrow> False"
  by (cases a) simp_all

lemma edge_path_from_terminal_1 [simp]:
  "edge_path Terminal_1 as v \<longleftrightarrow> as = [] \<and> v = Terminal_1"
  by (cases as) auto

lemma edge_path_from_terminal_2 [simp]:
  "edge_path Terminal_2 as v \<longleftrightarrow> as = [] \<and> v = Terminal_2"
  by (cases as) auto

lemma edge_path_from_terminal_3 [simp]:
  "edge_path Terminal_3 as v \<longleftrightarrow> as = [] \<and> v = Terminal_3"
  by (cases as) auto

lemma edge_path_from_junction_w [simp]:
  "edge_path Junction_W as v \<longleftrightarrow>
     (as = [] \<and> v = Junction_W) \<or>
     (as = [W_T2] \<and> v = Terminal_2) \<or>
     (as = [W_T3] \<and> v = Terminal_3)"
  by (cases as) auto

lemma edge_path_from_junction_v [simp]:
  "edge_path Junction_V as v \<longleftrightarrow>
     (as = [] \<and> v = Junction_V) \<or>
     (as = [V_T1] \<and> v = Terminal_1) \<or>
     (as = [V_W] \<and> v = Junction_W) \<or>
     (as = [V_W, W_T2] \<and> v = Terminal_2) \<or>
     (as = [V_W, W_T3] \<and> v = Terminal_3)"
  by (cases as) auto

lemma edge_path_from_junction_u [simp]:
  "edge_path Junction_U as v \<longleftrightarrow>
     (as = [] \<and> v = Junction_U) \<or>
     (as = [U_V] \<and> v = Junction_V) \<or>
     (as = [U_T3] \<and> v = Terminal_3) \<or>
     (as = [U_V, V_T1] \<and> v = Terminal_1) \<or>
     (as = [U_V, V_W] \<and> v = Junction_W) \<or>
     (as = [U_V, V_W, W_T2] \<and> v = Terminal_2) \<or>
     (as = [U_V, V_W, W_T3] \<and> v = Terminal_3)"
  by (cases as) auto

lemma edge_path_from_source [simp]:
  "edge_path Source as v \<longleftrightarrow>
     (as = [] \<and> v = Source) \<or>
     (as = [S_T1] \<and> v = Terminal_1) \<or>
     (as = [S_T2] \<and> v = Terminal_2) \<or>
     (as = [S_U] \<and> v = Junction_U) \<or>
     (as = [S_U, U_V] \<and> v = Junction_V) \<or>
     (as = [S_U, U_T3] \<and> v = Terminal_3) \<or>
     (as = [S_U, U_V, V_T1] \<and> v = Terminal_1) \<or>
     (as = [S_U, U_V, V_W] \<and> v = Junction_W) \<or>
     (as = [S_U, U_V, V_W, W_T2] \<and> v = Terminal_2) \<or>
     (as = [S_U, U_V, V_W, W_T3] \<and> v = Terminal_3)"
proof (cases as)
  case Nil
  show ?thesis
    using Nil by auto
next
  case (Cons a rest)
  show ?thesis
    using Cons by (cases a) simp_all
qed

fun route_edges :: "commodity \<Rightarrow> route_choice \<Rightarrow> arc list" where
  "route_edges Commodity_1 Paid = [S_T1]"
| "route_edges Commodity_1 Free = [S_U, U_V, V_T1]"
| "route_edges Commodity_2 Paid = [S_T2]"
| "route_edges Commodity_2 Free = [S_U, U_V, V_W, W_T2]"
| "route_edges Commodity_3 Paid = [S_U, U_T3]"
| "route_edges Commodity_3 Free = [S_U, U_V, V_W, W_T3]"

lemma route_edges_valid:
  "edge_path Source (route_edges k r) (commodity_terminal k)"
  by (cases k; cases r) simp_all

theorem all_source_terminal_paths:
  "edge_path Source as (commodity_terminal k) \<longleftrightarrow>
     as = route_edges k Paid \<or> as = route_edges k Free"
  by (cases k) auto

corollary graph_paths_exactly_routes:
  "{as. edge_path Source as (commodity_terminal k)} =
   {route_edges k Paid, route_edges k Free}"
  using all_source_terminal_paths by auto

section \<open>The counterexample instance\<close>

fun demand_amount :: "commodity \<Rightarrow> real" where
  "demand_amount Commodity_1 = 15"
| "demand_amount Commodity_2 = 10"
| "demand_amount Commodity_3 = 15"

fun arc_capacity :: "arc \<Rightarrow> real" where
  "arc_capacity S_T1 = 10"
| "arc_capacity S_T2 = 6"
| "arc_capacity S_U = 24"
| "arc_capacity U_V = 14"
| "arc_capacity U_T3 = 10"
| "arc_capacity V_T1 = 5"
| "arc_capacity V_W = 9"
| "arc_capacity W_T2 = 4"
| "arc_capacity W_T3 = 5"

fun arc_cost :: "arc \<Rightarrow> real" where
  "arc_cost S_T1 = 2"
| "arc_cost S_T2 = 3"
| "arc_cost S_U = 0"
| "arc_cost U_V = 0"
| "arc_cost U_T3 = 2"
| "arc_cost V_T1 = 0"
| "arc_cost V_W = 0"
| "arc_cost W_T2 = 0"
| "arc_cost W_T3 = 0"

definition counterexample_uses ::
    "commodity \<Rightarrow> route_choice \<Rightarrow> arc \<Rightarrow> bool" where
  "counterexample_uses k r a \<longleftrightarrow> a \<in> set (route_edges k r)"

definition counterexample_instance ::
    "(commodity, route_choice, arc) path_flow_instance" where
  "counterexample_instance =
     \<lparr>pf_admissible = (\<lambda>_ _. True),
      pf_demand = demand_amount,
      pf_capacity = arc_capacity,
      pf_cost = arc_cost,
      pf_uses = counterexample_uses\<rparr>"

fun split_flow :: "commodity \<Rightarrow> route_choice \<Rightarrow> real" where
  "split_flow Commodity_1 Paid = 10"
| "split_flow Commodity_1 Free = 5"
| "split_flow Commodity_2 Paid = 6"
| "split_flow Commodity_2 Free = 4"
| "split_flow Commodity_3 Paid = 10"
| "split_flow Commodity_3 Free = 5"

lemma UNIV_commodity [simp]:
  "(UNIV :: commodity set) =
   {Commodity_1, Commodity_2, Commodity_3}"
  by (auto intro: commodity.exhaust)

lemma UNIV_route_choice [simp]:
  "(UNIV :: route_choice set) = {Paid, Free}"
  by (auto intro: route_choice.exhaust)

lemma UNIV_arc [simp]:
  "(UNIV :: arc set) =
   {S_T1, S_T2, S_U, U_V, U_T3, V_T1, V_W, W_T2, W_T3}"
  by (auto intro: arc.exhaust)

instantiation commodity :: finite
begin

instance
proof
  show "finite (UNIV :: commodity set)"
    by (rule finite_subset[of _ "{Commodity_1, Commodity_2, Commodity_3}"])
      (auto intro: commodity.exhaust)
qed

end

instantiation route_choice :: finite
begin

instance
proof
  show "finite (UNIV :: route_choice set)"
    by (rule finite_subset[of _ "{Paid, Free}"])
      (auto intro: route_choice.exhaust)
qed

end

instantiation arc :: finite
begin

instance
proof
  show "finite (UNIV :: arc set)"
    by (rule finite_subset[
          of _ "{S_T1, S_T2, S_U, U_V, U_T3, V_T1, V_W, W_T2, W_T3}"])
      (auto intro: arc.exhaust)
qed

end

lemma counterexample_well_formed:
  "well_formed_instance counterexample_instance"
  unfolding well_formed_instance_def counterexample_instance_def
  apply (intro conjI)
   apply (intro allI)
   apply (case_tac k)
   apply simp_all
  apply (intro allI)
  apply (case_tac a)
  apply simp_all
  done

lemma counterexample_maximum_demand [simp]:
  "maximum_demand counterexample_instance = 15"
  unfolding maximum_demand_def counterexample_instance_def
  by simp

lemma split_flow_meets_demands:
  "(\<Sum>r\<in>UNIV. split_flow k r) = demand_amount k"
  by (cases k) simp_all

lemma split_flow_load [simp]:
  "fractional_load counterexample_instance split_flow a = arc_capacity a"
  by (cases a)
    (simp_all add: fractional_load_def counterexample_instance_def
      counterexample_uses_def)

theorem split_flow_saturates_capacities:
  "\<forall>a. fractional_load counterexample_instance split_flow a =
     pf_capacity counterexample_instance a"
proof
  fix a
  have "fractional_load counterexample_instance split_flow a = arc_capacity a"
    by (rule split_flow_load)
  also have "\<dots> = pf_capacity counterexample_instance a"
    by (simp add: counterexample_instance_def)
  finally show "fractional_load counterexample_instance split_flow a =
      pf_capacity counterexample_instance a" .
qed

lemma split_flow_bound_iff_capacity_bound:
  "(\<forall>a. unsplittable_load counterexample_instance q a
       \<le> fractional_load counterexample_instance split_flow a + 15)
   \<longleftrightarrow>
   (\<forall>a. unsplittable_load counterexample_instance q a
       \<le> pf_capacity counterexample_instance a + 15)"
proof -
  have cap:
    "\<And>a. fractional_load counterexample_instance split_flow a =
      pf_capacity counterexample_instance a"
    using split_flow_saturates_capacities by blast
  show ?thesis
    by (simp only: cap)
qed

theorem split_flow_feasible:
  "fractional_feasible counterexample_instance split_flow"
  unfolding fractional_feasible_def
proof (intro conjI)
  show "well_formed_instance counterexample_instance"
    by (rule counterexample_well_formed)
  show "\<forall>k r. 0 \<le> split_flow k r"
    by (intro allI; case_tac k; case_tac r) simp_all
  show "\<forall>k r.
      \<not> pf_admissible counterexample_instance k r \<longrightarrow>
        split_flow k r = 0"
    by (simp add: counterexample_instance_def)
  show "\<forall>k.
      (\<Sum>r\<in>UNIV. split_flow k r) = pf_demand counterexample_instance k"
    using split_flow_meets_demands
    by (simp add: counterexample_instance_def)
  show "\<forall>a.
      fractional_load counterexample_instance split_flow a
        \<le> pf_capacity counterexample_instance a"
  proof
    fix a
    have "fractional_load counterexample_instance split_flow a = arc_capacity a"
      by (rule split_flow_load)
    also have "\<dots> = pf_capacity counterexample_instance a"
      by (simp add: counterexample_instance_def)
    finally show "fractional_load counterexample_instance split_flow a
        \<le> pf_capacity counterexample_instance a"
      by simp
  qed
qed

theorem split_flow_cost:
  "fractional_cost counterexample_instance split_flow = 58"
  unfolding fractional_cost_def
  apply (simp only: split_flow_load)
  apply (simp add: counterexample_instance_def)
  done

section \<open>Every bounded unsplittable routing costs at least sixty\<close>

text \<open>
  Every paid route costs exactly thirty.  If at most one commodity takes its
  paid route, one of three backbone arcs violates the additive bound: the
  load on @{term S_U} is forty when only commodity three is paid, the load on
  @{term U_V} is thirty when only commodity two is paid, and the load on
  @{term V_W} is twenty-five when only commodity one is paid.  Their respective
  allowed loads are thirty-nine, twenty-nine, and twenty-four.
\<close>

definition paid_count :: "(commodity \<Rightarrow> route_choice) \<Rightarrow> nat" where
  "paid_count q =
     (if q Commodity_1 = Paid then 1 else 0) +
     (if q Commodity_2 = Paid then 1 else 0) +
     (if q Commodity_3 = Paid then 1 else 0)"

lemma unsplittable_load_s_u:
  "unsplittable_load counterexample_instance q S_U =
     (if q Commodity_1 = Free then 15 else 0) +
     (if q Commodity_2 = Free then 10 else 0) + 15"
  by (cases "q Commodity_1"; cases "q Commodity_2"; cases "q Commodity_3")
    (simp_all add: unsplittable_load_def counterexample_instance_def
      counterexample_uses_def)

lemma unsplittable_load_u_v:
  "unsplittable_load counterexample_instance q U_V =
     (if q Commodity_1 = Free then 15 else 0) +
     (if q Commodity_2 = Free then 10 else 0) +
     (if q Commodity_3 = Free then 15 else 0)"
  by (cases "q Commodity_1"; cases "q Commodity_2"; cases "q Commodity_3")
    (simp_all add: unsplittable_load_def counterexample_instance_def
      counterexample_uses_def)

lemma unsplittable_load_v_w:
  "unsplittable_load counterexample_instance q V_W =
     (if q Commodity_2 = Free then 10 else 0) +
     (if q Commodity_3 = Free then 15 else 0)"
  by (cases "q Commodity_1"; cases "q Commodity_2"; cases "q Commodity_3")
    (simp_all add: unsplittable_load_def counterexample_instance_def
      counterexample_uses_def)

lemma bounded_routing_has_two_paid:
  assumes bound:
    "\<forall>a. unsplittable_load counterexample_instance q a
       \<le> fractional_load counterexample_instance split_flow a + 15"
  shows "2 \<le> paid_count q"
proof -
  have su:
    "unsplittable_load counterexample_instance q S_U
       \<le> fractional_load counterexample_instance split_flow S_U + 15"
    using bound by blast
  have uv:
    "unsplittable_load counterexample_instance q U_V
       \<le> fractional_load counterexample_instance split_flow U_V + 15"
    using bound by blast
  have vw:
    "unsplittable_load counterexample_instance q V_W
       \<le> fractional_load counterexample_instance split_flow V_W + 15"
    using bound by blast
  show ?thesis
    using su uv vw
    by (cases "q Commodity_1"; cases "q Commodity_2"; cases "q Commodity_3")
      (simp_all add: unsplittable_load_s_u unsplittable_load_u_v
        unsplittable_load_v_w paid_count_def)
qed

lemma unsplittable_cost_eq_paid_count:
  "unsplittable_cost counterexample_instance q = 30 * real (paid_count q)"
  by (cases "q Commodity_1"; cases "q Commodity_2"; cases "q Commodity_3")
    (simp_all add: unsplittable_cost_def unsplittable_load_def
      counterexample_instance_def counterexample_uses_def paid_count_def)

theorem bounded_unsplittable_cost:
  assumes bound:
    "\<forall>a. unsplittable_load counterexample_instance q a
       \<le> fractional_load counterexample_instance split_flow a + 15"
  shows "60 \<le> unsplittable_cost counterexample_instance q"
proof -
  have count: "2 \<le> paid_count q"
    using bound by (rule bounded_routing_has_two_paid)
  have count_real: "(2 :: real) \<le> real (paid_count q)"
    using count by (simp only: of_nat_le_iff)
  show ?thesis
    unfolding unsplittable_cost_eq_paid_count
    using count_real by linarith
qed

corollary capacity_bounded_unsplittable_cost:
  assumes bound:
    "\<forall>a. unsplittable_load counterexample_instance q a
       \<le> pf_capacity counterexample_instance a + 15"
  shows "60 \<le> unsplittable_cost counterexample_instance q"
  using assms split_flow_bound_iff_capacity_bound bounded_unsplittable_cost
  by blast

theorem no_weak_dgg_rounding:
  "\<not> weak_dgg_property counterexample_instance split_flow"
proof
  assume "weak_dgg_property counterexample_instance split_flow"
  then obtain q where q:
      "weak_dgg_rounding counterexample_instance split_flow q"
    unfolding weak_dgg_property_def by blast
  have bound:
    "\<forall>a. unsplittable_load counterexample_instance q a
       \<le> fractional_load counterexample_instance split_flow a + 15"
    using q unfolding weak_dgg_rounding_def by simp
  have lower: "60 \<le> unsplittable_cost counterexample_instance q"
    using bound by (rule bounded_unsplittable_cost)
  have upper:
    "unsplittable_cost counterexample_instance q
       \<le> fractional_cost counterexample_instance split_flow"
    using q unfolding weak_dgg_rounding_def by blast
  show False
    using lower upper split_flow_cost by linarith
qed

corollary no_strict_dgg_rounding:
  "\<not> strict_dgg_property counterexample_instance split_flow"
  unfolding strict_dgg_property_def
  using no_weak_dgg_rounding strict_dgg_rounding_imp_weak
    weak_dgg_property_def by blast

theorem dinitz_garg_goemans_cost_counterexample:
  "dgg_counterexample counterexample_instance split_flow"
  unfolding dgg_counterexample_def
  using counterexample_well_formed split_flow_feasible no_weak_dgg_rounding
  by blast

corollary weak_dgg_cost_conjecture_false:
  "\<not> (\<forall>(I :: (commodity, route_choice, arc) path_flow_instance) f.
      well_formed_instance I \<and> fractional_feasible I f
        \<longrightarrow> weak_dgg_property I f)"
  using dinitz_garg_goemans_cost_counterexample
  unfolding dgg_counterexample_def by blast

corollary strict_dgg_cost_conjecture_false:
  "\<not> (\<forall>(I :: (commodity, route_choice, arc) path_flow_instance) f.
      well_formed_instance I \<and> fractional_feasible I f
        \<longrightarrow> strict_dgg_property I f)"
  using counterexample_well_formed split_flow_feasible no_strict_dgg_rounding
  by blast

end
