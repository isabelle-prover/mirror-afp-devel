section \<open> ApproxMCCore definitions \<close>

text \<open>
  This section defines the ApproxMCCore locale and various failure events to be used in its probabilistic analysis.
  The definitions closely follow Section 4.2 of Chakraborty et al.~\cite{DBLP:conf/ijcai/ChakrabortyMV16}.
  Some non-probabilistic properties of the events are proved, most notably, the event inclusions of Lemma 3~\cite{DBLP:conf/ijcai/ChakrabortyMV16}.
  Note that ``events'' here refer to subsets of hash functions.
\<close>

theory ApproxMCCore imports
  ApproxMCPreliminaries
begin

(* An 'a assg is a finite map from 'a to bool
  It is useful to think of 'a as the type of (projected) variables *)
type_synonym 'a assg = "'a \<rightharpoonup> bool"

(* Restrict function to a domain (analogous to restrict_map) *)
definition restr :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a assg"
  where "restr S w = (\<lambda>x. if x \<in> S then Some (w x) else None)"

lemma restrict_eq_mono:
  assumes "x \<subseteq> y"
  assumes "f |` y = g |` y"
  shows "f |` x = g |` x"
  using assms
  by (metis Map.restrict_restrict inf.absorb_iff2)

(* Projection of a solution set W onto variables S *)
definition proj :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) set \<Rightarrow> 'a assg set"
  where "proj S W = restr S ` W"

lemma card_proj:
  assumes "finite S"
  shows "finite (proj S W)" "card (proj S W) \<le> 2 ^ card S"
proof -
  have *: "proj S W \<subseteq> {w. dom w = S}"
    unfolding proj_def restr_def
    by (auto split: if_splits)
  also have 1: "{w. dom w = S} = {w. dom w = S \<and> ran w \<subseteq> {True,False}}"
    by auto
  have f: "finite  {w. dom w = S \<and> ran w \<subseteq> {True,False}}"
    by (simp add: assms finite_set_of_finite_maps)
  thus "finite (proj S W)"
    using * 1
    by (metis finite_subset)

  have 2:"card {w. dom w = S \<and> ran w \<subseteq> {True,False}} = (card {True,False}) ^ card S"
    apply (intro card_dom_ran)
    using assms by auto

  show "card (proj S W) \<le> 2 ^ card S"
    using * 1 2
    by (metis (no_types, lifting) f card.empty card_insert_disjoint card_mono finite.emptyI finite.insertI insert_absorb insert_not_empty numeral_2_eq_2 singleton_insert_inj_eq)
qed

lemma proj_mono:
  assumes "x \<subseteq> y"
  shows "proj w x \<subseteq> proj w y"
  unfolding proj_def
  using assms by blast

(* We can view nat assg as bit vectors, and take the i-th prefix slices *)
definition aslice :: "nat \<Rightarrow> nat assg \<Rightarrow> nat assg"
  where "aslice i a = a |` {..<i}"

lemma aslice_eq:
  assumes "i \<ge> n"
  assumes "dom a = {..<n}"
  shows "aslice i a = aslice n a"
  using assms
  unfolding aslice_def restrict_map_def dom_def
  by fastforce

(*  Prefix slice after hashing *)
definition hslice :: "nat \<Rightarrow>
  ('a assg \<Rightarrow> nat assg) \<Rightarrow> ('a assg \<Rightarrow> nat assg)"
  where "hslice i h = aslice i \<circ> h"

(* Convenient grouping of assumptions and parameters *)
locale ApproxMCCore =
  fixes W :: "('a \<Rightarrow> bool) set"
  fixes S :: "'a set"
  fixes \<epsilon> :: "real"
  fixes \<alpha> :: "nat assg"
  fixes thresh :: "nat"
  assumes \<alpha>: "dom \<alpha> = {0..<card S - 1}"
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes thresh:
    "thresh > 4"
    "card (proj S W) \<ge> thresh"
  assumes S: "finite S"
begin

lemma finite_proj_S:
  shows "finite (proj S W)"
  using S by (auto intro!: card_proj)

definition \<mu> :: "nat \<Rightarrow> real"
  where "\<mu> i = card (proj S W) / 2 ^ i"

(* A frequently used expression for the number of projected
   witnesses w whose i-th slices match the target *)
definition card_slice ::"
  ('a assg \<Rightarrow> nat assg) \<Rightarrow>
  nat \<Rightarrow> nat"
  where "card_slice h i =
    card (proj S W \<inter> {w. hslice i h w = aslice i \<alpha>})"

lemma card_slice_anti_mono:
  assumes "i \<le> j"
  shows "card_slice h j \<le> card_slice h i"
proof -
  have *: "{..<i} \<subseteq> {..<j}" using assms by auto
  have "{w. hslice j h w = aslice j \<alpha>}
    \<subseteq> {w. hslice i h w = aslice i \<alpha>}"
    by (auto intro: restrict_eq_mono[OF *] simp add: hslice_def aslice_def)
  thus ?thesis
    unfolding card_slice_def
    apply (intro card_mono)
    subgoal using finite_proj_S by blast
    by (auto intro!: proj_mono)
qed

lemma hslice_eq:
  assumes "n \<le> i"
  assumes "\<And>w. dom (h w) = {..<n}"
  shows "hslice i h = hslice n h"
  using assms aslice_eq
  unfolding hslice_def by auto

lemma card_slice_lim:
  assumes "card S - 1 \<le> i"
  assumes "\<And>w. dom (h w) = {..<(card S - 1)}"
  shows "card_slice h i = card_slice h (card S - 1)"
  unfolding card_slice_def
  apply(subst aslice_eq[OF assms(1)])
  subgoal using \<alpha> by auto
  apply(subst hslice_eq[OF assms(1)])
  using assms by auto

(* Defining the various events with respect to a fixed h *)
definition T :: "nat \<Rightarrow>
  ('a assg \<Rightarrow> nat assg) set"
  where "T i = {h. card_slice h i < thresh}"

lemma T_mono:
  assumes "i \<le> j"
  shows "T i \<subseteq> T j"
  unfolding T_def
  using card_slice_anti_mono[OF assms]
    dual_order.strict_trans2
    of_nat_mono
  by blast

lemma \<mu>_anti_mono:
  assumes "i \<le> j"
  shows "\<mu> i \<ge> \<mu> j"
proof -
  have "2^ i \<le> (2::real) ^ j"
    by (simp add: assms)
  then show ?thesis unfolding \<mu>_def
    by (simp add: frac_le)
qed

lemma card_proj_witnesses:
  "card (proj S W) > 0"
  using thresh by linarith

lemma \<mu>_strict_anti_mono:
  assumes "i < j"
  shows "\<mu> i > \<mu> j"
proof -
  have "2^ i < (2::real) ^ j"
    by (simp add: assms)
  then show ?thesis unfolding \<mu>_def
    using card_proj_witnesses
    by (simp add: frac_less2)
qed

lemma \<mu>_gt_zero:
  shows "\<mu> i > 0"
  unfolding \<mu>_def
  using card_proj_witnesses
  by auto

definition L :: "nat \<Rightarrow>
  ('a assg \<Rightarrow> nat assg) set"
  where "
    L i =
    {h. real (card_slice h i) < \<mu> i / (1 + \<epsilon>)}"

definition U :: "nat \<Rightarrow>
  ('a assg \<Rightarrow> nat assg) set"
  where "
    U i =
    {h. real (card_slice h i) \<ge> \<mu> i * (1 + \<epsilon> / (1 + \<epsilon>))}"

(* Model of ApproxMC core without random choice of h *)
definition approxcore :: "
  ('a assg \<Rightarrow> nat assg) \<Rightarrow>
  nat \<times> nat"
  where "
    approxcore h =
    (case List.find
      (\<lambda>i. h \<in> T i) [1..<card S] of
      None \<Rightarrow> (2 ^ card S, 1)
    | Some m \<Rightarrow>
      (2 ^ m, card_slice h m))"

(* The failure event as a set over hashes *)
definition approxcore_fail :: "
  ('a assg \<Rightarrow> nat assg) set"
  where "approxcore_fail  =
    {h.
      let (cells,sols) = approxcore h in
      cells * sols \<notin>
      { card (proj S W) / (1 + \<epsilon>) ..
        (1 + \<epsilon>::real) * card (proj S W)}
    }"

(* This is a global assumption of the locale *)
lemma T0_empty:
  shows "T 0 = {}"
  unfolding T_def card_slice_def
    hslice_def aslice_def
  using thresh(2) by auto

lemma L0_empty:
  shows "L 0 = {}"
proof -
  have "0 < \<epsilon> \<Longrightarrow>
    real (card (proj S W))
    < real (card (proj S W)) / (1 + \<epsilon>) \<Longrightarrow>
    False"
    by (smt (z3) card_proj_witnesses divide_minus1 frac_less2 nonzero_minus_divide_right of_nat_0_less_iff)
  thus ?thesis
  unfolding L_def card_slice_def
  hslice_def aslice_def \<mu>_def
  using \<epsilon> by clarsimp
qed

lemma U0_empty:
  shows "U 0 = {}"
proof -
  have *: "(1 + \<epsilon> / (1 + \<epsilon>)) > 1"
    using \<epsilon> by auto
  have **: "U 0 = {}"
    unfolding U_def card_slice_def
      hslice_def aslice_def \<mu>_def
    using *
    by (simp add: card_proj_witnesses)
  thus ?thesis using ** by auto
qed

lemma real_divide_pos_left:
  assumes "(0::real) < a"
  assumes "a * b < c"
  shows "b < c / a"
  using assms
  by (simp add: mult.commute mult_imp_less_div_pos)

lemma real_divide_pos_right:
  assumes "a > (0::real)"
  assumes "b < a * c"
  shows "b / a < c"
  using assms
  by (simp add: mult.commute mult_imp_div_pos_less)

(* The first inclusion used in the upper bound of Lemma 3 *)
lemma failure_imp:
  shows "approxcore_fail \<subseteq>
    (\<Union>i\<in>{1..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i)) \<union>
    -T (card S - 1)"
proof standard
  fix h
  assume "h \<in> approxcore_fail"
  then obtain cells sols where
    h: "approxcore h = (cells, sols)"
    "cells * sols \<notin>
      { card (proj S W) / (1 + \<epsilon>) ..
        (1 + \<epsilon>::real) * card (proj S W)}" (is "_ \<notin> {?lower..?upper}")
    unfolding approxcore_fail_def
    by auto

  have "List.find (\<lambda>i. h \<in> T i) [1..<card S] = None \<or>
    List.find (\<lambda>i. h \<in> T i) [1..<card S] \<noteq> None" by auto
  moreover {
    assume "List.find (\<lambda>i. h \<in> T i) [1..<card S] = None"
    then have "h \<notin> T (card S - 1)"
      unfolding find_None_iff
      by (metis T0_empty atLeastLessThan_iff diff_is_0_eq' diff_less empty_iff gr_zeroI leI less_one not_less_zero set_upt)
  }
  moreover {
    assume "List.find (\<lambda>i. h \<in> T i) [1..<card S] \<noteq> None"
    then obtain m where
      findm: "List.find (\<lambda>i. h \<in> T i) [1..<card S] = Some m" by auto
    then have
      m: "1 \<le> m" "m < card S"
      "h \<in> T m"
      "\<forall>i. 1 \<le> i \<and> i < m \<longrightarrow> h \<notin> T i"
      unfolding find_Some_iff
      using less_Suc_eq_0_disj by auto

    then have 1: "h \<notin> T (m - 1)"
      by (metis T0_empty bot_nat_0.not_eq_extremum diff_is_0_eq diff_less empty_iff less_one)

    have "2 ^ m * card_slice h m < ?lower \<or>
       2 ^ m * card_slice h m > ?upper"
      using h unfolding approxcore_def findm by auto
    moreover {
      assume "2 ^ m * card_slice h m < ?lower"
      then have "card_slice h m < ?lower / 2 ^ m"
        using real_divide_pos_left
        by (metis numeral_power_eq_of_nat_cancel_iff of_nat_mult zero_less_numeral zero_less_power)

      then have "h \<in> L m" unfolding L_def
        by (simp add: \<mu>_def mult.commute)
    }
    moreover {
      assume *: "?upper < 2 ^ m * card_slice h m"
      have "1 / (1 + \<epsilon>) <  1"
        using \<epsilon> divide_less_eq_1 by fastforce
      then have "\<epsilon> / (1 + \<epsilon>) <  \<epsilon>"
        using \<epsilon>
        by (metis (no_types, opaque_lifting) add_cancel_left_right div_by_1 divide_divide_eq_left divide_less_eq_1_pos mult.commute nonzero_divide_mult_cancel_left)
      then have "card (proj S W) * (1 + \<epsilon> / (1 + \<epsilon>)) \<le> ?upper"
        using linorder_not_less not_less_iff_gr_or_eq by fastforce
      then have "(card (proj S W) * (1 + \<epsilon> / (1 + \<epsilon>))) / 2 ^ m < card_slice h m"
        apply (intro real_divide_pos_right)
        using * by auto
      then have "h \<in> U m" unfolding U_def
        by (simp add: \<mu>_def)
    }
    ultimately have "h \<in> L m \<or> h \<in> U m" by blast
    then have "\<forall>m\<in>{Suc 0..<card S}.
            h \<in> T m \<longrightarrow>
            h \<in> T (m - Suc 0) \<or>
            h \<notin> L m \<and> h \<notin> U m \<Longrightarrow>
         h \<in> T (card S - Suc 0) \<Longrightarrow> False"
      using m 1 by auto
  }
  ultimately show
      "h \<in> (\<Union>i\<in>{1..<card S}.
                  (T i - T (i - 1)) \<inter> (L i \<union> U i)) \<union>
              - T (card S - 1)"
    by auto
qed

(* technically not smallest, but doesn't matter for our use *)
lemma smallest_nat_exists:
  assumes "P i" "\<not>P (0::nat)"
  obtains m where "m \<le> i" "P m" "\<not>P (m-1)"
  using assms
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  then show ?case
    by (metis diff_Suc_1 le_Suc_eq)
qed

lemma mstar_non_zero:
  shows "\<not> \<mu> 0 * (1 + \<epsilon> / (1 + \<epsilon>)) \<le> thresh"
proof -
  have "\<mu> 0 \<ge> thresh"
    unfolding \<mu>_def
    by (auto simp add: thresh(2))
  thus ?thesis
    by (smt (verit, best) \<epsilon> \<mu>_gt_zero divide_pos_pos mult_le_cancel_left2)
qed

lemma real_div_less:
  assumes "c > 0"
  assumes "a \<le> b * (c::nat)"
  shows "real a / real c \<le> b"
  by (metis assms(1) assms(2) divide_le_eq of_nat_0_less_iff of_nat_mono of_nat_mult)

(* Instead of giving mstar explicitly, we'll select it implicitly by the properties below *)
lemma mstar_exists:
  obtains m where
    "\<mu> (m - 1) * (1 + \<epsilon> / (1 + \<epsilon>)) > thresh"
    "\<mu> m * (1 + \<epsilon> / (1 + \<epsilon>)) \<le> thresh"
    "m \<le> card S - 1"
proof -
  have e1:"1 + \<epsilon> / (1 + \<epsilon>) > 1"
    by (simp add: \<epsilon> add_nonneg_pos)
  have e2:"1 + \<epsilon> / (1 + \<epsilon>) < 2"
    by (simp add: \<epsilon> add_nonneg_pos)
  have "thresh  \<ge> (4::real)"
    using thresh(1) by linarith
  then have up:"thresh / (1 + \<epsilon> / (1 + \<epsilon>)) > 2"
    by (smt (verit) e1 e2 field_sum_of_halves frac_less2)

  have "card (proj S W) \<le> 2 * 2 ^ (card S - Suc 0)"
    by (metis One_nat_def S Suc_diff_Suc card.empty card_gt_0_iff card_proj(2) diff_zero less_one order_less_le_trans plus_1_eq_Suc power_0 power_Suc0_right power_add thresh(1) thresh(2) zero_neq_numeral)

  then have low:"\<mu> (card S - 1) \<le> 2"
    unfolding \<mu>_def
    using real_div_less
    by (smt (verit) Num.of_nat_simps(2) Num.of_nat_simps(4) Suc_1 nat_zero_less_power_iff numeral_nat(7) of_nat_power plus_1_eq_Suc pos2)

  have pi: "\<mu> (card S - 1) * (1 + \<epsilon> / (1 + \<epsilon>)) \<le> thresh"
    using up low
    by (smt (verit, ccfv_SIG) divide_le_eq e1)

  from smallest_nat_exists[OF pi mstar_non_zero]
  show ?thesis
    by (metis linorder_not_less that)
qed

definition mstar :: "nat"
  where "mstar = (@m.
    \<mu> (m - 1) * (1 + \<epsilon> / (1 + \<epsilon>)) > thresh \<and>
    \<mu> m * (1 + \<epsilon> / (1 + \<epsilon>)) \<le> thresh \<and>
    m \<le> card S - 1)"

(* The main inequalities we need from mstar *)
lemma mstar_prop:
  shows
    "\<mu> (mstar - 1) * (1 + \<epsilon> / (1 + \<epsilon>)) > thresh"
    "\<mu> mstar * (1 + \<epsilon> / (1 + \<epsilon>)) \<le> thresh"
    "mstar \<le> card S - 1"
  unfolding mstar_def
  by (smt (verit) some_eq_ex mstar_exists)+

lemma O1_lem:
  assumes "i \<le> m"
  shows "(T i - T (i-1)) \<inter> (L i \<union> U i) \<subseteq> T m"
  using T_mono assms by blast

lemma O1:
  shows "(\<Union>i\<in>{1..mstar-3}.
    (T i - T (i-1)) \<inter> (L i \<union> U i)) \<subseteq> T (mstar-3)"
  using T_mono by force

lemma T_anti_mono_neg:
  assumes "i \<le> j"
  shows "- T j \<subseteq> - T i"
  by (simp add: Diff_mono T_mono assms)

lemma O2_lem:
  assumes "mstar < i"
  shows "(T i - T (i-1)) \<inter> (L i \<union> U i) \<subseteq> -T mstar"
proof -
  have "(T i - T (i-1)) \<inter> (L i \<union> U i) \<subseteq> -T (i-1)"
    by blast
  thus ?thesis
    by (smt (verit) T_mono ApproxMCCore_axioms One_nat_def Suc_diff_Suc Suc_le_eq assms compl_mono diff_is_0_eq' diff_less_mono leI minus_nat.diff_0 subset_trans)
qed

lemma O2:
  shows "(\<Union>i\<in>{mstar..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i)) \<union>
    -T (card S - 1) \<subseteq> L mstar \<union> U mstar"
proof -
  have 0: "(\<Union>i\<in>{mstar..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i)) \<subseteq>
    (T mstar - T (mstar-1)) \<inter> (L mstar \<union> U mstar) \<union>
    (\<Union>i\<in>{mstar+1..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i))"
    apply (intro subsetI)
    apply clarsimp
    by (metis Suc_le_eq atLeastLessThan_iff basic_trans_rules(18))

  have 1: "(\<Union>i\<in>{mstar+1..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i)) \<subseteq> -T mstar"
    apply clarsimp
    by (metis (no_types, lifting) ApproxMCCore.T_mono ApproxMCCore_axioms One_nat_def diff_Suc_1 diff_le_mono subsetD)

  have 2: "-T (card S - 1) \<subseteq> - T mstar"
    using T_anti_mono_neg mstar_prop(3) by presburger

  (* Note that the strict inequality is needed here *)
  have "thresh \<ge> \<mu> mstar * (1 + \<epsilon> / (1 + \<epsilon>))"
    using mstar_prop(2) thresh by linarith

  then have *: "- T mstar \<subseteq> U mstar"
    unfolding T_def U_def
    by auto

  have "(\<Union>i\<in>{mstar..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i)) \<union>
    -T (card S - 1) \<subseteq>
    ((T mstar - T (mstar-1)) \<inter> (L mstar \<union> U mstar)) \<union> -T mstar"
    using 0 1 2 by (smt (z3) Un_iff subset_iff)

  moreover have "... \<subseteq> L mstar \<union> U mstar"
    using *
    by blast
  ultimately show ?thesis by auto
qed

lemma O3:
  assumes "i \<le> mstar - 1"
  shows "(T i - T (i-1)) \<inter> (L i \<union> U i) \<subseteq> L i"
proof -
  have *: "\<mu> i * (1 + \<epsilon> / (1 + \<epsilon>)) > thresh"
    by (smt (verit, ccfv_SIG) \<epsilon> \<mu>_anti_mono assms divide_nonneg_nonneg mstar_prop(1) mult_right_mono)

  have "x \<in> T i \<and> x \<in> U i \<Longrightarrow> False" for x
      unfolding T_def U_def
      using * by auto
  thus ?thesis
    by blast
qed

lemma union_split_lem:
  assumes x: "x \<in> (\<Union>i\<in>{1..<n::nat}. P i)"
  shows "x \<in> (\<Union>i\<in>{1..m-3}. P i) \<union>
    P (m-2) \<union>
    P (m-1) \<union>
    (\<Union>i\<in>{m..<n}. P i)"
proof -
  obtain i where i: "i \<in> {1..<n}"
    "x \<in> P i" using x by auto
  have "i \<in> {1..m-3} \<or> i = m-2 \<or> i = m-1 \<or> i \<in> {m..<n}"
    using i(1)
    by auto
  thus ?thesis using i
    by blast
qed

lemma union_split:
  "(\<Union>i\<in>{1..<n::nat}. P i) \<subseteq>
   (\<Union>i\<in>{1..m-3}. P i) \<union>
    P (m-2) \<union>
    P (m-1) \<union>
    (\<Union>i\<in>{m..<n}. P i)"
  using union_split_lem
  by (metis subsetI)

lemma failure_bound:
  shows "approxcore_fail \<subseteq>
  T (mstar-3) \<union>
  L (mstar-2) \<union>
  L (mstar-1) \<union>
  (L mstar \<union> U mstar)"
proof -

  have *: "approxcore_fail \<subseteq>
    (\<Union>i\<in>{1..<card S}.
      (T i - T (i-1)) \<inter> (L i \<union> U i)) \<union> -T (card S - 1)" (is "_ \<subseteq> (\<Union>i\<in>{1..<card S}. ?P i) \<union> _")
    using failure_imp .

  moreover have "... \<subseteq>
    (\<Union>i\<in>{1..mstar - 3}. ?P i) \<union>
    ?P (mstar - 2) \<union>
    ?P (mstar - 1) \<union>
    ((\<Union>i\<in>{mstar..<card S}. ?P i) \<union> -T (card S - 1))"
    using
    union_split[of "\<lambda>i. ?P i" "card S" "mstar"]
    by blast
  moreover have "... \<subseteq>
    T (mstar - 3) \<union>
    L (mstar - 2) \<union>
    L (mstar - 1) \<union>
    (L mstar \<union> U mstar)
  "
    using O1 O2 O3
    by (metis (no_types, lifting) One_nat_def Un_mono diff_Suc_eq_diff_pred diff_le_self nat_1_add_1 plus_1_eq_Suc)
  ultimately show ?thesis
    by (meson order_trans)
qed

end

end
