section \<open> WEST Proofs \<close>
theory WEST_Proofs

imports WEST_Algorithms

begin

subsection \<open> Useful Definitions \<close>

definition trace_of_vars::"trace \<Rightarrow> nat \<Rightarrow> bool"
  where "trace_of_vars trace num_vars = (
  \<forall>k. (k < (length trace) \<longrightarrow> (\<forall>p\<in>(trace!k). p < num_vars)))"


definition state_regex_of_vars::"state_regex \<Rightarrow> nat \<Rightarrow> bool"
  where "state_regex_of_vars state num_vars = ((length state) = num_vars)"


definition trace_regex_of_vars::"trace_regex \<Rightarrow> nat \<Rightarrow> bool"
  where "trace_regex_of_vars trace num_vars =
   (\<forall> i < (length trace). length (trace!i) = num_vars)"


definition WEST_regex_of_vars::"WEST_regex \<Rightarrow> nat \<Rightarrow> bool"
  where "WEST_regex_of_vars traceList num_vars =
  (\<forall> k<length traceList. trace_regex_of_vars (traceList!k) num_vars)"

subsection \<open> Proofs about Traces Matching Regular Expressions \<close>

value "match_regex [{0::nat}, {0,1}, {}] []"
lemma arbitrary_regtrace_matches_any_trace:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  assumes \<pi>_of_num_vars: "trace_of_vars \<pi> num_vars"
  shows "match_regex \<pi> []"
proof-
  have get_state_empty: "(WEST_get_state [] time num_vars) = (map (\<lambda> k. S) [0 ..< num_vars])" for time
    by auto
  have match_arbitrary_state: "(match_timestep state (map (\<lambda> k. S) [0 ..< num_vars])) = True" if state_of_vars:"(\<forall>p\<in>state. p < num_vars)" for state
    using state_of_vars
    unfolding match_timestep_def
    by simp
  have eliminate_forall: "match_timestep (\<pi> ! time) (WEST_get_state [] time num_vars)" if time_bounded:"time < length \<pi>" for time
    using time_bounded \<pi>_of_num_vars get_state_empty[of time] match_arbitrary_state[of "\<pi> ! time"] unfolding match_regex_def trace_of_vars_def
    by (metis (mono_tags, lifting))
  then show ?thesis
    unfolding match_regex_def trace_of_vars_def
    by auto
qed

lemma WEST_and_state_difflengths_is_none:
  assumes "length s1 \<noteq> length s2"
  shows "WEST_and_state s1 s2 = None"
  using assms
  proof (induction s1 arbitrary: s2)
    case Nil
    then show ?case
      apply (induction s2) by simp_all
  next
    case (Cons a s1)
    then show ?case
    proof (induction s2)
      case Nil
      then show ?case by auto
    next
      case (Cons b s2)
      have "length s1 \<noteq> length s2" using Cons.prems(2)
        by auto
      then have and_s1_s2_none: "WEST_and_state s1 s2 = None" using Cons.prems(1)[of s2]
        by simp
      {assume ab_none: "WEST_and_bitwise a b = None"
        then have ?case
          by simp
      }
      moreover {assume ab_not_none: "WEST_and_bitwise a b \<noteq> None"
        then have ?case using and_s1_s2_none using WEST_and_state.simps(2)[of a s1 b s2]
          by auto
      }
      ultimately show ?case
        by blast
    qed
  qed


subsection \<open> Facts about the WEST and operator \<close>

subsubsection \<open> Commutative \<close>

lemma WEST_and_bitwise_commutative:
  fixes b1 b2::"WEST_bit"
  shows "WEST_and_bitwise b1 b2 = WEST_and_bitwise b2 b1"
  apply (cases b2)
      apply (cases b1) apply simp_all
     apply(cases b1) apply simp_all
  apply (cases b1) by simp_all

fun remove_option_type_bit:: "WEST_bit option \<Rightarrow> WEST_bit"
  where "remove_option_type_bit (Some i) = i"
  | "remove_option_type_bit _ = S"

lemma WEST_and_state_commutative:
  fixes s1 s2::"state_regex"
  assumes same_len: "length s1 = length s2"
  shows "WEST_and_state s1 s2 = WEST_and_state s2 s1"
proof-
  show ?thesis using same_len
  proof (induct "length s1" arbitrary: s1 s2)
    case 0
    then show ?case using WEST_and_state.simps by simp
  next
    case (Suc x)
    obtain h1 T1 where "s1 = h1#T1"
      using Suc.hyps(2)
      by (metis length_Suc_conv)
    obtain h2 T2 where "s2 = h2#T2"
      using Suc.prems(1) Suc.hyps(2)
      by (metis length_Suc_conv)
    then show ?case using WEST_and_bitwise_commutative[of h1 h2] WEST_and_state.simps(2)[of h1 T1 h2 T2]
      WEST_and_state.simps(2)[of h2 T2 h1 T1]
      by (metis (no_types, lifting) Suc.hyps(1) Suc.hyps(2) Suc.prems(1) Suc_length_conv WEST_and_bitwise_commutative \<open>s1 = h1 # T1\<close> list.inject option.simps(4) option.simps(5) remove_option_type_bit.cases)
  qed
qed


lemma WEST_and_trace_commutative:
  fixes num_vars::"nat"
  fixes regtrace1::"trace_regex"
  fixes regtrace2::"trace_regex"
  assumes regtrace1_of_num_vars: "trace_regex_of_vars regtrace1 num_vars"
  assumes regtrace2_of_num_vars: "trace_regex_of_vars regtrace2 num_vars"
  shows "(WEST_and_trace regtrace1 regtrace2) = (WEST_and_trace regtrace2 regtrace1)"
proof-
  have WEST_and_bitwise_commutative: "WEST_and_bitwise b1 b2 = WEST_and_bitwise b2 b1" for b1 b2
    apply (cases b2)
      apply (cases b1) apply simp_all
     apply(cases b1) apply simp_all
    apply (cases b1) by simp_all
  then have WEST_and_state_commutative: "WEST_and_state s1 s2 = WEST_and_state s2 s1" if same_len: "(length s1) = (length s2)" for s1 s2
  using same_len
  proof (induct "length s1" arbitrary: s1 s2)
    case 0
    then show ?case using WEST_and_state.simps by simp
  next
    case (Suc x)
    obtain h1 T1 where "s1 = h1#T1"
      using Suc.hyps(2)
      by (metis length_Suc_conv)
    obtain h2 T2 where "s2 = h2#T2"
      using Suc.prems(2) Suc.hyps(2)
      by (metis length_Suc_conv)
    then show ?case using WEST_and_bitwise_commutative[of h1 h2] WEST_and_state.simps(2)[of h1 T1 h2 T2]
      WEST_and_state.simps(2)[of h2 T2 h1 T1]
      by (metis (no_types, lifting) Suc.hyps(1) Suc.hyps(2) Suc.prems(2) Suc_length_conv WEST_and_bitwise_commutative \<open>s1 = h1 # T1\<close> list.inject option.simps(4) option.simps(5) remove_option_type_bit.cases)
  qed
  show ?thesis using regtrace1_of_num_vars  regtrace2_of_num_vars
  proof (induction regtrace1 arbitrary: regtrace2)
    case Nil
    then show ?case using WEST_and_trace.simps(1-2)
      by (metis neq_Nil_conv)
  next
    case (Cons h1 T1)
    {assume *: "regtrace2 = []"
      then have ?case using WEST_and_trace.simps
        by simp
    } moreover {assume *: "regtrace2 \<noteq> []"
      then obtain h2 T2 where h2T2: "regtrace2 = h2#T2"
        by (meson list.exhaust)
      have comm_1: "WEST_and_trace T1 T2 = WEST_and_trace T2 T1"
        using Cons h2T2
        unfolding trace_regex_of_vars_def
        by (metis Suc_less_eq length_Cons nth_Cons_Suc)
      have comm_2: "WEST_and_state h1 h2 = WEST_and_state h2 h1"
        using WEST_and_state_commutative[of h1 h2] h2T2
        Cons(2-3) unfolding trace_regex_of_vars_def
        by (metis WEST_and_state_difflengths_is_none)
      have ?case using WEST_and_trace.simps(3)[of h1 T1 h2 T2]
        h2T2 WEST_and_trace.simps(3)[of h2 T2 h1 T1] comm_1 comm_2
        by presburger
    }
    ultimately show ?case by blast
  qed
qed

lemma WEST_and_helper_subset:
  shows "set (WEST_and_helper h L) \<subseteq> set (WEST_and_helper h (a # L))"
proof -
  {assume *: "WEST_and_trace h a = None"
    then have "WEST_and_helper h L = WEST_and_helper h (a # L)"
      using WEST_and_helper.simps(2)[of h a L] by auto
    then  have ?thesis by simp
  }
  moreover {assume *: "WEST_and_trace h a \<noteq> None"
    then obtain res where "WEST_and_trace h a = Some res"
      by auto
    then have "WEST_and_helper h (a#L) = res # WEST_and_helper h L"
      using WEST_and_helper.simps(2)[of h a L] by auto
    then have ?thesis  by auto
  }
  ultimately show ?thesis by blast
qed


lemma WEST_and_helper_set_member_converse:
  fixes regtrace h::"trace_regex"
  fixes L::"WEST_regex"
  assumes assumption: "(\<exists> loc. loc < length L \<and> (\<exists>sometrace. WEST_and_trace h (L ! loc) = Some sometrace \<and> regtrace = sometrace))"
  shows "regtrace \<in> set (WEST_and_helper h L)"
proof -
  show ?thesis using assumption
  proof (induct L)
    case Nil
    then show ?case using WEST_and_helper.simps(1)
      by simp
  next
    case (Cons a L)
    then obtain loc sometrace where obt: "loc < length (a#L) \<and> WEST_and_trace h ((a#L) ! loc) = Some sometrace \<and> regtrace = sometrace"
      by blast
    {assume *: "loc = 0"
      then have " WEST_and_trace h a = Some sometrace \<and> regtrace = sometrace"
        using obt
        by simp
      then have ?case using WEST_and_helper.simps(2)[of h a L]
        by auto
    } moreover {assume *: "loc > 0"
      then have loc: "loc-1 < length L \<and>
        WEST_and_trace h (L ! (loc-1)) = Some sometrace \<and> regtrace = sometrace"
        using obt by auto
      have "set (WEST_and_helper h L) \<subseteq> set (WEST_and_helper h (a # L))"
        using WEST_and_helper_subset by blast
      then have ?case using Cons(1) loc by blast
    }
    ultimately show ?case by auto
  qed
qed

lemma WEST_and_helper_set_member_forward:
  fixes regtrace h::"trace_regex"
  fixes L::"WEST_regex"
  assumes "regtrace \<in> set (WEST_and_helper h L)"
  shows "(\<exists> loc. loc < length L \<and>  (\<exists>sometrace. WEST_and_trace h (L ! loc) = Some sometrace \<and> regtrace = sometrace))"
using assms proof (induction L)
  case Nil
  then show ?case by simp
next
  case (Cons a L)
  {assume *: "WEST_and_trace h a = None"
    then have ?case using WEST_and_helper.simps(2)[of h a L] Cons
      by force
  } moreover {assume *: "WEST_and_trace h a \<noteq> None"
    then obtain res where res: "WEST_and_trace h a = Some res"
      by auto
    then have "WEST_and_helper h (a#L) = res # WEST_and_helper h L"
      using WEST_and_helper.simps(2)[of h a L] by auto
    then have eo: "regtrace = res \<or> regtrace \<in> set (WEST_and_helper h L)"
      using Cons(2)
      by auto
    {assume *: "regtrace = res"
      then have ?case using res by auto
    } moreover  {assume *: "regtrace \<in> set (WEST_and_helper h L)"
      then obtain loc where loc_prop: "loc<length L \<and>
       (\<exists>sometrace. WEST_and_trace h (L ! loc) = Some sometrace \<and> regtrace = sometrace)"
        using Cons.IH by blast
      then have "loc+1<length (a#L) \<and>
       (\<exists>sometrace. WEST_and_trace h ((a#L) ! (loc+1)) = Some sometrace \<and> regtrace = sometrace)"
        by auto
      then have ?case by blast
    }
    ultimately have ?case using eo
      by blast
  }
  ultimately show ?case by blast
qed


lemma WEST_and_helper_set_member:
  fixes regtrace h::"trace_regex"
  fixes L::"WEST_regex"
  shows "regtrace \<in> set (WEST_and_helper h L) \<longleftrightarrow>
    (\<exists> loc. loc < length L \<and>  (\<exists>sometrace. WEST_and_trace h (L ! loc) = Some sometrace \<and> regtrace = sometrace))"
  using WEST_and_helper_set_member_forward WEST_and_helper_set_member_converse
  by blast

lemma WEST_and_set_member_dir1:
  fixes num_vars::"nat"
  fixes L1::"WEST_regex"
  fixes L2::"WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 num_vars"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 num_vars"
  assumes "regtrace \<in> set (WEST_and L1 L2)"
  shows "(\<exists> loc1 loc2. loc1 < length L1 \<and> loc2 < length L2 \<and>
    (\<exists>sometrace. WEST_and_trace (L1 ! loc1) (L2 ! loc2) = Some sometrace \<and> regtrace = sometrace))"
  using assms proof (induct L1 arbitrary: L2)
  case Nil
  then show ?case using WEST_and.simps(2) WEST_and.simps(1)
    by (metis list.distinct(1) list.exhaust list.set_cases)
next
  case (Cons head tail)
  {assume L2_empty: "L2 = []"
    then have ?case
      using Cons.prems(3) by auto
  }
  moreover { assume L2_not_empty: "L2 \<noteq> []"
    {assume regtrace_in_head_L2: "regtrace \<in> set (WEST_and_helper head L2)"
      then obtain loc2 where "(loc2<length L2 \<and>
        (\<exists>sometrace. WEST_and_trace head (L2 ! loc2) = Some sometrace \<and> regtrace = sometrace))"
        using WEST_and_helper_set_member[of regtrace head L2]
        by blast
      then have "0 < length (head # tail) \<and>
       loc2 < length L2 \<and>
       (\<exists>sometrace.
           WEST_and_trace ((head # tail) ! 0) (L2 ! loc2) = Some sometrace \<and>
           regtrace = sometrace)"
        using regtrace_in_head_L2
        by simp
      then have ?case
        by blast
    }
    moreover {assume regtrace_notin_head_L2: "regtrace \<notin> set (WEST_and_helper head L2)"
      obtain h2 T2 where h2T2:"L2 = h2#T2" using L2_not_empty
        by (meson list.exhaust)
      {assume *: "WEST_and_helper head (h2 # T2) = []"
        then have "WEST_and (head # tail) L2 = WEST_and tail L2"
          using WEST_and.simps(3)[of head tail h2 T2] h2T2 by simp
      }
      moreover {assume *: "WEST_and_helper head (h2 # T2) \<noteq> []"
        then have "WEST_and (head # tail) L2 = (WEST_and_helper head L2) @ WEST_and tail L2"
          using WEST_and.simps(3)[of head tail h2 T2] h2T2
          by (simp add: list.case_eq_if)
      }
      ultimately have e_o: "WEST_and (head # tail) L2 = WEST_and tail L2 \<or> WEST_and (head # tail) L2 = (WEST_and_helper head L2) @ WEST_and tail L2"
        by blast
      have regtrace_in: "regtrace \<in> set (WEST_and tail L2)" using L2_not_empty regtrace_notin_head_L2 Cons.prems(3) h2T2 e_o
        by fastforce
      have "\<forall>k<length (head # tail). trace_regex_of_vars ((head # tail) ! k) num_vars"
        using Cons.prems(1) unfolding WEST_regex_of_vars_def by argo
      then have regtracelist_tail: "WEST_regex_of_vars tail num_vars"
        unfolding WEST_regex_of_vars_def by auto
      obtain loc1 loc2 where "loc1 < length tail \<and>
       loc2 < length L2 \<and> (\<exists>sometrace. WEST_and_trace (tail ! loc1) (L2 ! loc2) = Some sometrace \<and> regtrace = sometrace)"
        using Cons.hyps[OF regtracelist_tail Cons.prems(2) regtrace_in] by blast
      then have "loc1+1 < length (head # tail) \<and>
       loc2 < length L2 \<and>
       (\<exists>sometrace.
           WEST_and_trace ((head # tail) ! (loc1+1)) (L2 ! loc2) = Some sometrace \<and>
           regtrace = sometrace)"
        by simp
      then have ?case
        by blast
    }
    ultimately have ?case
      by blast
  }
  ultimately show ?case
    by blast
qed

lemma WEST_and_subset:
  shows "set (WEST_and T1 L2) \<subseteq> set (WEST_and (h1#T1) L2)"
proof -
  {assume *: "L2 = []"
    then have ?thesis by auto
  } moreover {assume *: "L2 \<noteq> []"
    then obtain h2 T2 where "L2 = h2#T2"
      using list.exhaust_sel by blast
    then have ?thesis
      using WEST_and.simps(3)[of h1 T1 h2 T2]
      by (simp add: list.case_eq_if)
  }
  ultimately show ?thesis by blast
qed

lemma WEST_and_set_member_dir2:
  fixes num_vars::"nat"
  fixes L1::"WEST_regex"
  fixes L2::"WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 num_vars"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 num_vars"
  assumes exists_locs: "(\<exists> loc1 loc2. loc1 < length L1 \<and> loc2 < length L2 \<and>
    (\<exists>sometrace. WEST_and_trace (L1 ! loc1) (L2 ! loc2) = Some sometrace \<and> regtrace = sometrace))"
  shows "regtrace \<in> set (WEST_and L1 L2)" using assms
proof (induct L1 arbitrary: L2)
  case Nil
  then show ?case by auto
next
  case (Cons h1 T1)
  then obtain loc1 loc2 where loc1loc2: "loc1 < length (h1 # T1) \<and>
       loc2 < length L2 \<and>
       (\<exists>sometrace.
           WEST_and_trace ((h1 # T1) ! loc1) (L2 ! loc2) = Some sometrace \<and>
           regtrace = sometrace)" by blast
  {assume *: "L2 = []"
    then have ?case using Cons by auto
  } moreover {assume *: "L2 \<noteq> []"
    then obtain h2 T2 where h2T2: "L2 = h2#T2"
      using list.exhaust_sel by blast
    have "\<forall>k<length (h1 # T1). trace_regex_of_vars ((h1 # T1) ! k) num_vars"
      using Cons.prems(1) unfolding WEST_regex_of_vars_def by argo
    then have regtraceList_T1: "WEST_regex_of_vars T1 num_vars"
      unfolding WEST_regex_of_vars_def by auto
    {assume **: "WEST_and_helper h1 L2 = []"
      then have "loc1 > 0"
        using loc1loc2
        by (metis WEST_and_helper.simps(1) WEST_and_helper_set_member gr_implies_not_zero list.size(3) not_gr0 nth_Cons_0)
      then have exi: "\<exists>loc1 loc2.
       loc1 < length T1 \<and>
       loc2 < length L2 \<and>
       (\<exists>sometrace.
           WEST_and_trace (T1 ! loc1) (L2 ! loc2) = Some sometrace \<and>
           regtrace = sometrace)"
        using loc1loc2
        by (metis One_nat_def Suc_pred bot_nat_0.not_eq_extremum length_Cons nat_add_left_cancel_less nth_Cons' plus_1_eq_Suc)
      then have ?case
        using Cons.hyps[OF regtraceList_T1 Cons(3) exi] WEST_and_subset
        by auto
    } moreover {assume **: "WEST_and_helper h1 L2 \<noteq> []"
      then have "WEST_and (h1 # T1) (h2 # T2) = WEST_and_helper h1 (h2 # T2)  @ WEST_and T1 (h2 # T2)"
        by (simp add: list.case_eq_if)
      then have ?case
        using Cons.hyps[OF regtraceList_T1 Cons.prems(2)]
        by (metis One_nat_def Suc_pred Un_iff WEST_and_helper_set_member_converse gr_implies_not_zero h2T2 length_Cons linorder_neqE_nat loc1loc2 nat_add_left_cancel_less nth_Cons' plus_1_eq_Suc set_append)
    }
    ultimately have ?case
      by auto
  }
  ultimately show ?case
    by auto
qed

lemma WEST_and_set_member:
  fixes num_vars::"nat"
  fixes L1::"WEST_regex"
  fixes L2::"WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 num_vars"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 num_vars"
  shows "regtrace \<in> set (WEST_and L1 L2) \<longleftrightarrow>
    (\<exists> loc1 loc2. loc1 < length L1 \<and> loc2 < length L2 \<and>
    (\<exists>sometrace. WEST_and_trace (L1 ! loc1) (L2 ! loc2) = Some sometrace \<and> regtrace = sometrace))"
  using WEST_and_set_member_dir1 WEST_and_set_member_dir2 assms by blast

lemma WEST_and_commutative_sets_member:
  fixes num_vars::"nat"
  fixes L1::"WEST_regex"
  fixes L2::"WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 num_vars"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 num_vars"
  assumes regtrace_in: "regtrace \<in> set (WEST_and L1 L2) "
  shows "regtrace \<in> set (WEST_and L2 L1)"
proof -
  obtain loc1 loc2 where loc1loc2: "loc1 < length L1 \<and>
        loc2 < length L2 \<and>
        (\<exists>sometrace.
            WEST_and_trace (L1 ! loc1) (L2 ! loc2) = Some sometrace \<and>
            regtrace = sometrace)"
  using WEST_and_set_member[OF L1_of_num_vars L2_of_num_vars] regtrace_in
  by auto
  have loc1: "trace_regex_of_vars (L1 ! loc1) num_vars"
    using L1_of_num_vars loc1loc2 unfolding WEST_regex_of_vars_def
    by (meson less_imp_le_nat)
  have loc2: "trace_regex_of_vars (L2 ! loc2) num_vars"
    using L2_of_num_vars loc1loc2 unfolding WEST_regex_of_vars_def
    by (meson less_imp_le_nat)
    have "loc1 < length L1 \<and>
        loc2 < length L2 \<and>
        (\<exists>sometrace.
            WEST_and_trace (L2 ! loc2) (L1 ! loc1) = Some sometrace \<and>
            regtrace = sometrace)"
    using loc1loc2 WEST_and_trace_commutative[OF loc1 loc2]
    by simp
  then show ?thesis using loc1loc2
    using WEST_and_set_member[OF L2_of_num_vars L1_of_num_vars]
    by blast
qed

lemma WEST_and_commutative_sets:
  fixes num_vars::"nat"
  fixes L1::"WEST_regex"
  fixes L2::"WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 num_vars"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 num_vars"
  shows "set (WEST_and L1 L2) = set (WEST_and L2 L1)"
  using WEST_and_commutative_sets_member[OF L1_of_num_vars L2_of_num_vars]
    WEST_and_commutative_sets_member[OF L2_of_num_vars L1_of_num_vars]
  by blast

lemma WEST_and_commutative:
  fixes num_vars::"nat"
  fixes L1::"WEST_regex"
  fixes L2::"WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 num_vars"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 num_vars"
  shows "regex_equiv (WEST_and L1 L2) (WEST_and L2 L1)"
proof -
  have "set (WEST_and L1 L2) = set (WEST_and L2 L1)"
    using WEST_and_commutative_sets assms
    by blast
  then have "match \<pi> (WEST_and L1 L2) = match \<pi> (WEST_and L2 L1)" for \<pi>
    using match_def match_regex_def
    by (metis in_set_conv_nth)
  then show ?thesis
    unfolding regex_equiv_def by auto
qed

subsubsection \<open> Identity and Zero \<close>


lemma WEST_and_helper_identity:
  shows "WEST_and_helper [] trace = trace"
proof (induct trace)
  case Nil
  then show ?case by auto
next
  case (Cons h T)
  then show ?case
    using WEST_and_helper.simps(2)[of "[]" h T]
    by (smt (verit) WEST_and_trace.elims list.discI option.simps(5))
qed

lemma WEST_and_identity: "WEST_and [[]] L = L"
proof-
  {assume *: "L = []"
    then have ?thesis
      by auto
  } moreover {assume *: "L \<noteq> []"
    then obtain h T where hT: "L = h#T"
      using list.exhaust by auto
    then have ?thesis using WEST_and.simps(3)[of "[]" "[]" h T]
      using hT
      by (metis (no_types, lifting) WEST_and.simps(2) WEST_and_helper_identity append.right_neutral list.simps(5))
  }
  ultimately show ?thesis by linarith
qed


lemma WEST_and_zero: "WEST_and L [] = []"
  by simp


subsubsection \<open> WEST-and-state \<close>

paragraph \<open> Well Defined \<close>

fun advance_state:: "state \<Rightarrow> state"
  where "advance_state state = {x-1 | x. (x\<in>state \<and> x \<noteq> 0)}"

lemma advance_state_elt_bound:
  fixes state::"state"
  fixes num_vars::"nat"
  assumes "\<forall>x\<in>state. x < num_vars"
  shows "\<forall>x\<in>(advance_state state). x < (num_vars-1)"
  using assms advance_state.simps by auto

lemma advance_state_elt_member:
  fixes state::"state"
  fixes x::"nat"
  assumes "x+1 \<in> state"
  shows "x \<in> advance_state state"
  using assms advance_state.simps by force

lemma advance_state_match_timestep:
  fixes h::"WEST_bit"
  fixes t::"state_regex"
  fixes state::"state"
  assumes "match_timestep state (h#t)"
  shows "match_timestep (advance_state state) t"
proof-
  have "(\<forall>x<length (h # t).
           ((h # t) ! x = One \<longrightarrow> x \<in> state) \<and> ((h # t) ! x = Zero \<longrightarrow> x \<notin> state))" using assms unfolding match_timestep_def by argo
  then have "\<forall>x<length t.
           ((h # t) ! (x+1) = One \<longrightarrow> (x+1) \<in> state) \<and> ((h # t) ! (x+1) = Zero \<longrightarrow> (x+1) \<notin> state)" by auto
  then have "\<forall>x<length t.
           (t ! x = One \<longrightarrow> x \<in> (advance_state state)) \<and> (t ! x = Zero \<longrightarrow> x \<notin> (advance_state state))"
    using advance_state.simps advance_state_elt_member by fastforce
  then show ?thesis using assms unfolding match_timestep_def by metis
qed


lemma WEST_and_state_well_defined:
  fixes num_vars::"nat"
  fixes state::"state"
  fixes s1 s2:: "state_regex"
  assumes s1_of_num_vars: "state_regex_of_vars s1 num_vars"
  assumes s2_of_num_vars: "state_regex_of_vars s2 num_vars"
  assumes \<pi>_match_r1_r2: "match_timestep state s1 \<and> match_timestep state s2"
  shows "WEST_and_state s1 s2 \<noteq> None"
proof-
  have same_length: "length s1 = length s2"
    using assms unfolding state_regex_of_vars_def by simp
  have "(\<forall> x. x < num_vars \<longrightarrow> (((s1 ! x = One) \<longrightarrow> x \<in> state) \<and> ((s1 ! x = Zero) \<longrightarrow> x \<notin> state)))"
    using assms unfolding match_timestep_def state_regex_of_vars_def by metis
  then have match_timestep_s1_unfold: "\<forall>x\<in>state. x < num_vars \<longrightarrow> ((s1 ! x = One) \<or> (s1 ! x = S))"
    using assms by (meson WEST_bit.exhaust)
  then have x_in_state_s1: "\<forall>x. (x < num_vars \<and> x \<in> state) \<longrightarrow> ((s1 ! x = One) \<or> (s1 ! x = S))" by blast
  then have x_notin_state_s1: "\<forall>x. (x < num_vars \<and> x \<notin> state) \<longrightarrow> ((s1 ! x = Zero) \<or> (s1 ! x = S))"
    using match_timestep_s1_unfold
    by (meson WEST_bit.exhaust \<open>\<forall>x<num_vars. (s1 ! x = One \<longrightarrow> x \<in> state) \<and> (s1 ! x = Zero \<longrightarrow> x \<notin> state)\<close>)
  have match_timestep_s2_unfold: "(\<forall> x. x < num_vars \<longrightarrow> (((s2 ! x = One) \<longrightarrow> x \<in> state) \<and> ((s2 ! x = Zero) \<longrightarrow> x \<notin> state)))"
    using assms unfolding match_timestep_def state_regex_of_vars_def by metis
  then have "\<forall>x\<in>state. x < num_vars \<longrightarrow> ((s2 ! x = One) \<or> (s2 ! x = S))"
    using assms by (meson WEST_bit.exhaust)
  then have x_in_state_s2: "\<forall>x. (x < num_vars \<and> x \<in> state) \<longrightarrow> ((s2 ! x = One) \<or> (s2 ! x = S))" by blast
  then have x_notin_state_s2: "\<forall>x. (x < num_vars \<and> x \<notin> state) \<longrightarrow> ((s2 ! x = Zero) \<or> (s2 ! x = S))"
    using match_timestep_s1_unfold
    by (meson WEST_bit.exhaust \<open>\<forall>x<num_vars. (s2 ! x = One \<longrightarrow> x \<in> state) \<and> (s2 ! x = Zero \<longrightarrow> x \<notin> state)\<close>)
  have no_contradictory_bits1: "\<forall>x\<in>state. x < num_vars \<longrightarrow> WEST_and_bitwise (s1 ! x) (s2 ! x) \<noteq> None"
    using x_in_state_s1 x_notin_state_s1 x_in_state_s2 x_notin_state_s2 WEST_and_bitwise.simps
    by (metis match_timestep_s2_unfold not_Some_eq)
  then have no_contradictory_bits2: "\<forall>x. (x \<notin> state \<and> x < num_vars) \<longrightarrow> WEST_and_bitwise (s1 ! x) (s2 ! x) \<noteq> None"
    using x_in_state_s1 x_notin_state_s1 x_in_state_s2 x_notin_state_s2 WEST_and_bitwise.simps
    by fastforce
  have no_contradictory_bits: "\<forall>x. x < num_vars \<longrightarrow> WEST_and_bitwise (s1 ! x) (s2 ! x) \<noteq> None"
    using no_contradictory_bits1 no_contradictory_bits2
    by blast
  show ?thesis using same_length no_contradictory_bits assms
  proof (induct s1 arbitrary: s2 num_vars state)
    case Nil
    then show ?case by auto
  next
    case (Cons a s1)
    then have num_vars_bound: "num_vars = (length s1) + 1"
      unfolding state_regex_of_vars_def by simp
    then have len_s2: "length s2 = num_vars" using Cons by simp
    then have "length s2 \<ge> 1" using num_vars_bound by simp
    then have s2_ht_exists: "\<exists>h t. s2 = h#t"
      by (metis Suc_eq_plus1 Suc_le_length_iff \<open>length s2 = num_vars\<close> not_less_eq_eq num_vars_bound)
    obtain h t where s2_ht: "s2 = h#t" using s2_ht_exists by blast
    {assume *: "WEST_and_bitwise a h = None"
      then have ?case using WEST_and_state.simps(2)
        using Cons.prems(2) \<open>length s2 = num_vars\<close> s2_ht by force
    } moreover {assume **: "WEST_and_bitwise a h \<noteq> None"
      have h1: "length s1 = length t"
        using len_s2 num_vars_bound s2_ht by simp
      obtain num_var_minus1 where nvm1_def: "num_var_minus1 = num_vars - 1" by simp
      then have "\<forall>x<(num_vars-1). WEST_and_bitwise ((a#s1) ! (x+1)) ((h#t) ! (x+1)) \<noteq> None"
        using Cons.prems(2)
        using num_vars_bound s2_ht by auto
      then have h2: "\<forall>x<num_var_minus1. WEST_and_bitwise (s1 ! x) (t ! x) \<noteq> None"
        using nvm1_def by simp
      obtain adv_state where adv_state_def: "adv_state = advance_state state" by simp
      have h4: "state_regex_of_vars s1 num_var_minus1"
        using Cons.prems unfolding state_regex_of_vars_def
        by (simp add: add_implies_diff num_vars_bound nvm1_def)
      have h5: "state_regex_of_vars t num_var_minus1"
        using h4 h1 unfolding state_regex_of_vars_def by simp
      have h6: "match_timestep adv_state s1 \<and> match_timestep adv_state t"
        using Cons.prems(5) s2_ht adv_state_def
        using advance_state_match_timestep by blast
      have ih: "WEST_and_state s1 t \<noteq> None"
        using Cons.hyps[of t num_var_minus1 adv_state] h1 h2 h4 h5 h6 by auto
      have ?case using WEST_and_state.simps(2)[of a s1 h t] ** ih s2_ht by auto
    }
    ultimately show ?case
      by blast
  qed
qed


paragraph \<open> Correct Forward \<close>

lemma WEST_and_state_length:
  fixes s1 s2::"state_regex"
  assumes samelen: "length s1 = length s2"
  assumes r_exists: "(WEST_and_state s1 s2) \<noteq> None"
  shows "\<exists>r. length r = length s1 \<and> WEST_and_state s1 s2 = Some r"
proof-
  have s1s2_exists: "\<exists>r. WEST_and_state s1 s2 = Some r"
    using assms by simp
  then obtain r where s1s2_obt: "WEST_and_state s1 s2 = Some r" by auto
  let ?n = "length s1"
  have s1s2_length_n: "length r = ?n"
    using assms s1s2_obt
  proof (induct ?n arbitrary: s1 s2 r)
    case 0
    then show ?case using WEST_and_state.simps(1) by simp
  next
    case (Suc x)
    have "length s1 \<ge> 1" using Suc.hyps(2) by simp
    then have "\<exists>h1 t1. s1 = h1 # t1" by (simp add: Suc_le_length_iff)
    then obtain h1 t1 where h1t1: "s1 = h1 # t1" by blast
    have "length s2 \<ge> 1" using Suc.hyps(2) Suc.prems(1) by auto
    then have "\<exists>h2 t2. s2 = h2 # t2" by (simp add: Suc_le_length_iff)
    then obtain h2 t2 where h2t2: "s2 = h2 # t2" by blast
    have "WEST_and_bitwise h1 h2 \<noteq> None"
      using Suc.prems h1t1 h2t2 WEST_and_state.simps(2)[of h1 t1 h2 t2]
      by (metis option.simps(4))
    then obtain h1h2 where h1h2_and: "Some h1h2 = WEST_and_bitwise h1 h2" by auto
    have "WEST_and_state t1 t2 \<noteq> None"
      using Suc.prems h1t1 h2t2 WEST_and_state.simps(2)[of h1 t1 h2 t2]
      by (metis (no_types, lifting) not_None_eq option.simps(4) option.simps(5))
    then obtain t1t2 where t1t2_and: "Some t1t2 = WEST_and_state t1 t2" by auto
    have cond1: "x = length t1" using h1t1 Suc.hyps(2) by auto
    have cond2: "length t1 = length t2" using h1t1 h2t2 Suc.prems(1) by auto
    have len_t1t2: "length t1t2 = length t1"
      using Suc.hyps(1)[of t1 t2 t1t2] using cond1 cond2 t1t2_and
      using \<open>WEST_and_state t1 t2 \<noteq> None\<close> by fastforce
    have r_decomp: "r = h1h2 # t1t2"
      using Suc.prems(3) h1h2_and t1t2_and WEST_and_state.simps(2)
      by (metis h1t1 h2t2 option.inject option.simps(5))
    show ?case using r_decomp len_t1t2 h1t1 h2t2 by auto
  qed
  then show ?thesis using assms s1s2_obt s1s2_exists by simp
qed


lemma index_shift:
  fixes "a"::"WEST_bit"
  fixes "t"::"state_regex"
  fixes "state"::"state"
  assumes "(a = One \<longrightarrow> 0 \<in> state) \<and> (a = Zero \<longrightarrow> 0 \<notin> state)"
  assumes "\<forall>x<length t. ((t!x) = One \<longrightarrow> x + 1 \<in> state) \<and> ((t!x) = Zero \<longrightarrow> x + 1 \<notin> state)"
  shows "\<forall>x<length (a#t). ((a#t) ! x = One \<longrightarrow> x \<in> state) \<and> ((a#t) ! x = Zero \<longrightarrow> x \<notin> state)"
proof-
  have "(a = One \<longrightarrow> 0 \<in> state)" using assms by auto
  then have a_one: "(a#t)!0 = One \<longrightarrow> 0 \<in> state" by simp
  have t_one: "\<forall>x<length t. (t!x) = One \<longrightarrow> x + 1 \<in> state" using assms by auto
  have "\<forall>x<(length t)+1. (x \<noteq> 0 \<and> (a#t)!x = One) \<longrightarrow> x \<in> state"
    using t_one assms(2)
    by (metis (no_types, lifting) Suc_diff_1 Suc_less_eq add_Suc_right cancel_comm_monoid_add_class.diff_cancel gr_zeroI less_numeral_extra(1) linordered_semidom_class.add_diff_inverse nth_Cons' verit_comp_simplify1(1))
  then have at_one: "\<forall>x<length (a#t). ((a#t) ! x = One \<longrightarrow> x \<in> state)"
    using a_one t_one by (simp add: nth_Cons')
  have "(a = Zero \<longrightarrow> 0 \<notin> state)" using assms by auto
  then have a_zero: "(a#t)!0 = Zero \<longrightarrow> 0 \<notin> state" by simp
  have t_zero: "\<forall>x<length t. (t!x) = Zero \<longrightarrow> x + 1 \<notin> state" using assms by auto
  have "\<forall>x<(length t)+1. (x \<noteq> 0 \<and> (a#t)!x = Zero) \<longrightarrow> x \<notin> state"
    using t_zero assms(2)
    by (metis Nat.add_0_right Suc_diff_1 Suc_less_eq add_Suc_right cancel_comm_monoid_add_class.diff_cancel less_one not_gr_zero nth_Cons')
  then have at_zero: "\<forall>x<length (a#t). ((a#t) ! x = Zero \<longrightarrow> x \<notin> state)"
    using a_zero t_zero by (simp add: nth_Cons')
  show ?thesis using at_one at_zero by blast
qed


lemma index_shift_reverse:
  fixes "a"::"WEST_bit"
  fixes "t"::"state_regex"
  fixes "state"::"state"
  assumes "\<forall>x<length (a#t). ((a#t) ! x = One \<longrightarrow> x \<in> state) \<and> ((a#t) ! x = Zero \<longrightarrow> x \<notin> state)"
  shows "\<forall>x<length t. ((t!x) = One \<longrightarrow> x + 1 \<in> state) \<and> ((t!x) = Zero \<longrightarrow> x + 1 \<notin> state)"
proof-
  have "length (a#t) = (length t) + 1" by simp
  then have "\<forall>x<(length t)+1. ((a#t) ! x = One \<longrightarrow> x \<in> state) \<and> ((a#t) ! x = Zero \<longrightarrow> x \<notin> state)"
    using assms by metis
  then show ?thesis by simp
qed


lemma WEST_and_state_correct_forward:
  fixes num_vars::"nat"
  fixes state::"state"
  fixes s1 s2:: "state_regex"
  assumes s1_of_num_vars: "state_regex_of_vars s1 num_vars"
  assumes s2_of_num_vars: "state_regex_of_vars s2 num_vars"
  assumes match_both: "match_timestep state s1 \<and> match_timestep state s2"
  shows "\<exists>somestate. (match_timestep state somestate) \<and> (WEST_and_state s1 s2) = Some somestate"
proof-
  have "WEST_and_state s1 s2 \<noteq> None"
    using WEST_and_state_well_defined assms by simp
  then have "\<exists>somestate. WEST_and_state s1 s2 = Some somestate" by auto
  then obtain somestate where somestate_obt: "WEST_and_state s1 s2 = Some somestate" by auto
  have samelength: "length s1 = length s2" using assms(1, 2) unfolding state_regex_of_vars_def by auto
  have len_s1: "length s1 = num_vars" using assms unfolding state_regex_of_vars_def by auto
  have len_s2: "length s2 = num_vars" using samelength len_s1 by auto
  have len_somestate: "length somestate = num_vars"
    using samelength somestate_obt WEST_and_state.simps WEST_and_state_length
    using len_s1 len_s2
    by fastforce
  have s1_bits: "\<forall>x<num_vars. (s1 ! x = One \<longrightarrow> x \<in> state) \<and> (s1 ! x = Zero \<longrightarrow> x \<notin> state)"
    using assms(3) len_s1 unfolding match_timestep_def by metis
  have s2_bits: "\<forall>x<num_vars. (s2 ! x = One \<longrightarrow> x \<in> state) \<and> (s2 ! x = Zero \<longrightarrow> x \<notin> state)"
    using assms(3) len_s2 unfolding match_timestep_def len_s2 by metis
  have somestate_bits: "\<forall>x<num_vars. (somestate ! x = One \<longrightarrow> x \<in> state)
                                     \<and> (somestate ! x = Zero \<longrightarrow> x \<notin> state)"
    using s1_bits s2_bits somestate_obt len_s1 len_s2 len_somestate assms(1)
  proof(induct somestate arbitrary: s1 s2 num_vars state)
    case Nil
    then show ?case
      by (metis less_nat_zero_code list.size(3))
  next
    case (Cons a t)
    have "length s1 \<ge> 1" using Cons.prems(4, 5, 6) by auto
    then have "\<exists>h1 t1. s1 = h1 # t1" by (simp add: Suc_le_length_iff)
    then obtain h1 t1 where h1t1: "s1 = h1 # t1" by auto
    have "length s2 \<ge> 1" using Cons.prems(4, 5, 6) by auto
    then have "\<exists>h2 t2. s2 = h2 # t2" by (simp add: Suc_le_length_iff)
    then obtain h2 t2 where h2t2: "s2 = h2 # t2" by auto
    have h1h2_not_none: "WEST_and_bitwise h1 h2 \<noteq> None"
      using Cons.prems(3) h1t1 h2t2 WEST_and_state.simps(2)[of h1 t1 h2 t2]
      by (metis option.discI option.simps(4))
    then have t1t2_not_none: "WEST_and_state t1 t2 \<noteq> None"
      using Cons.prems(3) h1t1 h2t2 WEST_and_state.simps(2)[of h1 t1 h2 t2]
      by (metis option.case_eq_if option.distinct(1))
    have h1h2_is_a: "WEST_and_bitwise h1 h2 = Some a"
      using Cons.prems(3) h1t1 h2t2 WEST_and_state.simps(2)[of h1 t1 h2 t2]
      using t1t2_not_none h1h2_not_none by auto
    have t1t2_is_t: "WEST_and_state t1 t2 = Some t"
      using Cons.prems(3) h1t1 h2t2 WEST_and_state.simps(2)[of h1 t1 h2 t2]
      using t1t2_not_none h1h2_not_none by auto
    let ?num_vars_m1 = "num_vars - 1"
    have len_t: "Suc (length t) = num_vars"
      using Cons.prems(1-6) by simp
    then have length_t: "length t = ?num_vars_m1" by simp
    then have length_t1: "length t1 = ?num_vars_m1" using Cons.prems(1-6) h1t1 by simp
    then have length_t2: "length t2 = ?num_vars_m1" using Cons.prems(1-6) h2t2 by simp
    have "(a = One \<longrightarrow> 0 \<in> state) \<and> (a = Zero \<longrightarrow> 0 \<notin> state)"
      using h1h2_is_a Cons.prems(1, 2) h1t1 h2t2 WEST_and_bitwise.simps
      by (smt (verit) WEST_and_bitwise.elims len_t nth_Cons_0 option.inject zero_less_Suc)
    then have a_fact: "((a # t) ! 0 = One \<longrightarrow> 0 \<in> state) \<and> ((a # t) ! 0 = Zero \<longrightarrow> 0 \<notin> state)" by auto
    let ?adv_state = "advance_state state"
    have "\<forall>x<num_vars.((h1#t1) ! x = One \<longrightarrow> x \<in> state) \<and> ((h1#t1) ! x = Zero \<longrightarrow> x \<notin> state)"
      using Cons.prems(1) h1t1 advance_state.simps[of state] by blast
    then have cond1: "\<forall>x<num_vars-1.(t1 ! x = One \<longrightarrow> (x+1) \<in> state) \<and> (t1 ! x = Zero \<longrightarrow> (x+1) \<notin> state)"
      using index_shift_reverse[of h1 t1] by simp
    then have cond1: " \<forall>x<num_vars-1.(t1 ! x = One \<longrightarrow> x \<in> ?adv_state) \<and> (t1 ! x = Zero \<longrightarrow> x \<notin> ?adv_state)"
      using advance_state_elt_member by fastforce
    have "\<forall>x<num_vars.((h2#t2) ! x = One \<longrightarrow> x \<in> state) \<and> ((h2#t2) ! x = Zero \<longrightarrow> x \<notin> state)"
      using Cons.prems(2) h2t2 advance_state.simps[of state] by blast
    then have " \<forall>x<num_vars-1.(t2 ! x = One \<longrightarrow> (x+1) \<in> state) \<and> (t2 ! x = Zero \<longrightarrow> (x+1) \<notin> state)"
      using index_shift_reverse[of h2 t2] by simp
    then have cond2: " \<forall>x<num_vars-1.(t2 ! x = One \<longrightarrow> x \<in> ?adv_state) \<and> (t2 ! x = Zero \<longrightarrow> x \<notin> ?adv_state)"
      using advance_state_elt_member by fastforce
    have t_fact: "\<forall>x < length t. (t ! x = One \<longrightarrow> x \<in> ?adv_state) \<and> (t ! x = Zero \<longrightarrow> x \<notin> ?adv_state)"
      using Cons.hyps[of ?num_vars_m1 t1 ?adv_state t2]
      using length_t length_t1 length_t2 t1t2_is_t cond1 cond2
      by (metis (mono_tags, opaque_lifting) state_regex_of_vars_def)
    then have t_fact: "\<forall>x < length t. (t ! x = One \<longrightarrow> (x+1) \<in> state) \<and> (t ! x = Zero \<longrightarrow> (x+1) \<notin> state)"
      using advance_state_elt_member by auto
    have cons_index: "\<forall>x < length (a#t). (t ! x) = (a#t)!(x+1)" by auto
    have somestate_fact: "\<forall>x<length (a#t). ((a # t) ! x = One \<longrightarrow> x \<in> state) \<and> ((a # t) ! x = Zero \<longrightarrow> x \<notin> state)"
      using a_fact t_fact index_shift[of a state] Cons.prems(5,6)
      using \<open>(a = One \<longrightarrow> 0 \<in> state) \<and> (a = Zero \<longrightarrow> 0 \<notin> state)\<close> by blast
    show ?case
      using somestate_fact len_t by auto
  qed
  have match_somestate: "match_timestep state somestate"
    using somestate_obt assms somestate_bits
    using len_s2 len_somestate
    unfolding match_timestep_def
    by metis
  then show ?thesis using somestate_obt by simp
qed


paragraph \<open> Correct Converse \<close>

lemma WEST_and_state_indices:
  fixes s s1 s2::"state_regex"
  assumes "WEST_and_state s1 s2 = Some s"
  assumes "length s1 = length s2"
  assumes "x<length s"
  shows "Some (s!x) = WEST_and_bitwise (s1!x) (s2!x)"
  using assms
proof(induct s arbitrary: s1 s2 x)
  case Nil
  then show ?case by simp
next
  case (Cons h t)
  then obtain h1 t1 where h1t1: "s1 = h1 # t1"
    by (metis WEST_and_state.simps(1) length_greater_0_conv neq_Nil_conv option.inject)
  obtain h2 t2 where h2t2: "s2 = h2 # t2"
    using Cons
    by (metis WEST_and_state.simps(1) length_greater_0_conv neq_Nil_conv option.inject)
  have notnone1: " WEST_and_bitwise h1 h2 \<noteq> None" using h1t1 h2t2 Cons(2) WEST_and_state.simps(2)[of h1 t1 h2 t2]
    by (metis option.distinct(1) option.simps(4))
  have notnone2: " WEST_and_state t1 t2 \<noteq> None" using h1t1 h2t2 Cons(2) WEST_and_state.simps(2)[of h1 t1 h2 t2]
    by (metis option.case_eq_if option.discI)
  have someh: "WEST_and_bitwise h1 h2 = Some h" using h1t1 h2t2 Cons(2) WEST_and_state.simps(2)[of h1 t1 h2 t2]
    notnone1 notnone2 by auto
  have somet: "WEST_and_state t1 t2 = Some t" using h1t1 h2t2 Cons(2) WEST_and_state.simps(2)[of h1 t1 h2 t2]
    notnone1 notnone2 by auto
  then have some_t: "x < length t \<Longrightarrow> Some (t ! x) = WEST_and_bitwise (t1 ! x) (t2 ! x)" for x
    using h1t1 h2t2 Cons(1)[OF somet] Cons(3)
    by simp
  have some_zero: "Some ((h # t) ! 0) = WEST_and_bitwise (s1 ! 0) (s2 ! 0)"
    using someh h1t1 h2t2 by simp
  {assume *: "x = 0"
    then have ?case
      using some_zero by auto
  } moreover {assume *: "x > 0"
    then have xminus_lt: "x-1 < length t"
      using Cons(4) by simp
    have "Some ((h # t) ! x) = Some (t ! (x-1))"
      using *
      by auto
    then have ?case
      using some_t[OF xminus_lt] h1t1 h2t2
      by (simp add: "*")
  }
  ultimately show ?case
    by blast
qed

lemma WEST_and_state_correct_converse_s1:
  fixes num_vars::"nat"
  fixes state::"state"
  fixes s1 s2:: "state_regex"
  assumes s1_of_num_vars: "state_regex_of_vars s1 num_vars"
  assumes s2_of_num_vars: "state_regex_of_vars s2 num_vars"
  assumes match_and: "\<exists>somestate. (match_timestep state somestate) \<and> (WEST_and_state s1 s2) = Some somestate"
  shows "match_timestep state s1"
proof-
  have s1_bits: "(\<forall>x<length s1. (s1 ! x = One \<longrightarrow> x \<in> state) \<and> (s1 ! x = Zero \<longrightarrow> x \<notin> state))"
    using assms
  proof(induct s1 arbitrary: s2 num_vars state)
    case Nil
    then show ?case by auto
  next
    case (Cons h1 t1)
    obtain somestate where
    somestate_obt: "(match_timestep state somestate) \<and> (WEST_and_state (h1#t1) s2) = Some somestate"
      using Cons.prems(3) by auto

    have len_s1: "length (h1#t1) = num_vars" using Cons.prems unfolding state_regex_of_vars_def by simp
    have len_s2: "length s2 = num_vars" using Cons.prems unfolding state_regex_of_vars_def by simp
    then obtain h2 t2 where h2t2: "s2=h2#t2"
      by (metis WEST_and_state.simps(3) neq_Nil_conv not_Some_eq somestate_obt)
    have len_somestate: "length somestate = num_vars"
      using somestate_obt WEST_and_state_length[of _ s2] unfolding state_regex_of_vars_def len_s2
      using len_s1 by fastforce
    then obtain h t where ht: "somestate = h#t" using len_s1
      by (metis Ex_list_of_length Zero_not_Suc length_Cons neq_Nil_conv)

    have somestate_bits: "(\<forall>x<length somestate. (somestate ! x = One \<longrightarrow> x \<in> state) \<and> (somestate ! x = Zero \<longrightarrow> x \<notin> state))"
      using somestate_obt unfolding match_timestep_def by argo
    then have somestate_bits_conv: "(\<forall>x<length somestate. (x \<in> state \<longrightarrow> (somestate ! x = One \<or> somestate ! x = S)) \<and>
                                     (x \<notin> state \<longrightarrow> (somestate ! x = Zero \<or> somestate ! x = S)))"
      by (meson WEST_bit.exhaust)
    have "WEST_and_state (h1#t1) s2 = Some somestate" using somestate_obt by blast
    then have somestate_and: "WEST_and_state (h1#t1) (h2#t2) = Some (h#t)"
      using h2t2 ht by simp

    have "(somestate ! 0 = One \<longrightarrow> 0 \<in> state) \<and> (somestate ! 0 = Zero \<longrightarrow> 0 \<notin> state)"
      using somestate_bits len_somestate len_s1 by simp
    then have somestate_bit0: "(h = One \<longrightarrow> 0 \<in> state) \<and> (h = Zero \<longrightarrow> 0 \<notin> state)"
      using ht by simp
    have h1h2_not_none: "WEST_and_bitwise h1 h2 \<noteq> None"
      using somestate_and WEST_and_state.simps(2)[of h1 t1 h2 t2] h2t2
      using option.simps(4) by fastforce
    have t1t2_not_none: "WEST_and_state t1 t2 \<noteq> None"
      using h1h2_not_none somestate_and WEST_and_state.simps(2)[of h1 t1 h2 t2]
      using option.simps(4) by fastforce
    then have h1h2_is_h: "WEST_and_bitwise h1 h2 = Some h"
      using somestate_and WEST_and_state.simps(2)[of h1 t1 h2 t2] h1h2_not_none by auto
    have h_fact_converse: "(0 \<in> state \<longrightarrow> (h1 = One \<or> h1 = S)) \<and> (0 \<notin> state \<longrightarrow> (h1 = Zero \<or> h1 = S))"
      using somestate_bit0 h1h2_is_h WEST_and_bitwise.simps[of h1] h1h2_not_none
      by (metis (full_types) WEST_and_bitwise.elims option.inject)
    then have h_fact: "(h1 = One \<longrightarrow> 0 \<in> state) \<and> (h1 = Zero \<longrightarrow> 0 \<notin> state)" by auto

    have somestate_bits_t: "\<forall>x<length t. (t!x = One \<longrightarrow> (x+1) \<in> state) \<and> (t!x = Zero \<longrightarrow> (x+1) \<notin> state)"
      using index_shift_reverse[of h t] Cons.prems(1) somestate_bits len_somestate len_s1 ht by blast
    have t1t2_is_t: "WEST_and_state t1 t2 = Some t"
      using somestate_and WEST_and_state.simps(2)[of h1 t1 h2 t2] t1t2_not_none h1h2_not_none by auto
    then have t1t2_is_t_indices: "\<forall>x<length t. Some (t!x) = WEST_and_bitwise (t1!x) (t2!x)"
      using WEST_and_state_indices[of t1 t2 t] len_s1 len_s2 h2t2 by simp
    have t_fact_converse1: "\<And>x. x<length t1 \<Longrightarrow> (((x+1) \<in> state \<longrightarrow> (t1!x = One \<or> t1!x = S)) \<and> ((x+1) \<notin> state \<longrightarrow> (t1!x = Zero \<or> t1!x = S)))"
    proof -
      fix x
      assume x_lt: "x<length t1"
      have *:"(t!x = One \<longrightarrow> (x+1) \<in> state) \<and> (t!x = Zero \<longrightarrow> (x+1) \<notin> state)"
        using x_lt somestate_bits_t len_s1 len_somestate ht by auto
      have **: "Some (t ! x) = WEST_and_bitwise (t1 ! x) (t2 ! x)"
        using x_lt somestate_bits_t len_s1 len_somestate ht t1t2_is_t_indices by auto

      {assume case1: "(x+1) \<in> state"
        then have "t!x = One \<or> t1!x = S"
          using *
          by (smt (verit) "**" WEST_and_bitwise.elims WEST_and_bitwise.simps(2) option.distinct(1) option.inject)
        then have "(t1!x = One \<or> t1!x = S)"
          using x_lt WEST_and_bitwise.simps[of "t1!x"] * **
          by (metis (full_types) WEST_bit.exhaust not_None_eq option.inject)
      } moreover {assume case2: "(x+1) \<notin> state"
          then have "t!x = Zero \<or> t1!x = S"
            using *
            by (smt (verit) "**" WEST_and_bitwise.elims WEST_and_bitwise.simps(2) option.distinct(1) option.inject)
        then have "(t1!x = Zero \<or> t1!x = S)"
          using x_lt WEST_and_bitwise.simps[of "t1!x"] * **
          by (metis (full_types) WEST_bit.exhaust not_None_eq option.inject)
      }
      ultimately show "(((x+1) \<in> state \<longrightarrow> (t1!x = One \<or> t1!x = S)) \<and> ((x+1) \<notin> state \<longrightarrow> (t1!x = Zero \<or> t1!x = S)))"
        by blast
    qed
    then have t_fact: "\<forall>x<length t1. (t1!x = One \<longrightarrow> (x+1)\<in>state) \<and> (t1!x = Zero \<longrightarrow> (x+1)\<notin>state)"
      by force

    show ?case
      using h_fact t_fact Cons.prems len_s2 len_somestate index_shift[of h1 state]
      unfolding state_regex_of_vars_def by blast
  qed

  show ?thesis
    using s1_bits assms(1) unfolding match_timestep_def
    using state_regex_of_vars_def s1_of_num_vars by presburger
qed

lemma WEST_and_state_correct_converse:
  fixes num_vars::"nat"
  fixes state::"state"
  fixes s1 s2:: "state_regex"
  assumes s1_of_num_vars: "state_regex_of_vars s1 num_vars"
  assumes s2_of_num_vars: "state_regex_of_vars s2 num_vars"
  assumes match_and: "\<exists>somestate. (match_timestep state somestate) \<and> (WEST_and_state s1 s2) = Some somestate"
  shows "match_timestep state s1 \<and> match_timestep state s2"
proof-
  have match_s1: "match_timestep state s1" using assms WEST_and_state_correct_converse_s1 by simp
  have match_s2: "match_timestep state s2"
    using assms WEST_and_state_correct_converse_s1 WEST_and_state_commutative
    by (simp add: state_regex_of_vars_def)
  show ?thesis using match_s1 match_s2 by simp
qed


lemma WEST_and_state_correct:
  fixes num_vars::"nat"
  fixes state::"state"
  fixes s1 s2:: "state_regex"
  assumes s1_of_num_vars: "state_regex_of_vars s1 num_vars"
  assumes s2_of_num_vars: "state_regex_of_vars s2 num_vars"
  shows "(match_timestep state s1 \<and> match_timestep state s2) \<longleftrightarrow> (\<exists>somestate. match_timestep state somestate \<and> (WEST_and_state s1 s2) = Some somestate)"
  using assms WEST_and_state_correct_converse
              WEST_and_state_correct_forward by metis


subsubsection \<open> WEST-and-trace \<close>

paragraph \<open> Well Defined \<close>

lemma WEST_and_trace_well_defined:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  assumes \<pi>_match_r1_r2: "match_regex \<pi> r1 \<and> match_regex \<pi> r2"
  shows "WEST_and_trace r1 r2 \<noteq> None"
proof-
  show ?thesis using assms
  proof(induct r1 arbitrary: r2 \<pi> num_vars)
    case Nil
    {assume r2_empty:"r2 = []"
      then have ?case using WEST_and_trace.simps by blast
    } moreover {assume r2_nonempty: "r2\<noteq>[]"
      then obtain h2 t2 where "r2 = h2#t2"
        by (metis trim_reversed_regex.cases)
      then have?case using WEST_and_trace.simps(2)[of h2 t2] by blast
      }
      ultimately show ?case by blast
  next
    case (Cons h1 t1)
    {assume r2_empty:"r2 = []"
      then have ?case using WEST_and_trace.simps by blast
    } moreover {assume r2_nonempty: "r2\<noteq>[]"
      then obtain h2 t2 where h2t2: "r2 = h2#t2"
        by (metis trim_reversed_regex.cases)

      have h1t1_nv: "\<forall>i<length (h1 # t1). length ((h1 # t1) ! i) = num_vars"
        using Cons.prems(1) unfolding trace_regex_of_vars_def by argo
      then have "length ((h1 # t1) ! 0) = num_vars" by blast
      then have h1_nv: "state_regex_of_vars h1 num_vars"
        unfolding state_regex_of_vars_def by simp
      have h2t2_nv: "\<forall>i<length (h2 # t2). length ((h2 # t2) ! i) = num_vars"
        using Cons.prems(2) h2t2 unfolding trace_regex_of_vars_def by metis
      then have "length ((h2 # t2) ! 0) = num_vars" by blast
      then have h2_nv: "state_regex_of_vars h2 num_vars"
        unfolding state_regex_of_vars_def by simp

      have "match_timestep (\<pi> ! 0) h1 \<and> match_timestep (\<pi> ! 0) h2"
        using Cons(4) unfolding match_regex_def
        by (metis h2t2 length_greater_0_conv list.distinct(1) nth_Cons_0)
      then have h1h2_notnone: "WEST_and_state h1 h2 \<noteq> None"
        using WEST_and_state_well_defined[of h1 num_vars h2 "\<pi>!0", OF h1_nv h2_nv] by blast

      have t1_nv: "trace_regex_of_vars t1 num_vars"
        using h1t1_nv unfolding trace_regex_of_vars_def by auto
      have t2_nv: "trace_regex_of_vars t2 num_vars"
        using h2t2_nv unfolding trace_regex_of_vars_def by auto

      have unfold_prem3: "(\<forall>time<length (h1 # t1). match_timestep (\<pi> ! time) ((h1 # t1) ! time)) \<and>
      length (h1 # t1) \<le> length \<pi> \<and> (\<forall>time<length r2. match_timestep (\<pi> ! time) (r2 ! time)) \<and> length r2 \<le> length \<pi>"
        using Cons.prems(3) unfolding match_regex_def by argo

      have unfold_prem3_bounds: "length (h1 # t1) \<le> length \<pi> \<and> length r2 \<le> length \<pi>"
        using unfold_prem3 by blast
      have \<pi>_drop1_len: "length (drop 1 \<pi>) = (length \<pi>)-1" by simp
      have len_t1t2: "length t1 = length (h1#t1)-1 \<and> length t2 = length (h2#t2)-1" by simp
      have bounds: "length t1 \<le> length (drop 1 \<pi>) \<and> length t2 \<le> length (drop 1 \<pi>)"
        using unfold_prem3_bounds h2t2 \<pi>_drop1_len len_t1t2 h2t2
        by (metis diff_le_mono)

      have unfold_prem3_matches: "(\<forall>time<length (h1 # t1). match_timestep (\<pi> ! time) ((h1 # t1) ! time)) \<and>
                                   (\<forall>time<length (h2 # t2). match_timestep (\<pi> ! time) ((h2 # t2) ! time))"
        using unfold_prem3 h2t2 by blast

      have h1t1_match:"(\<forall>time<length (h1 # t1). match_timestep (\<pi> ! time) ((h1 # t1) ! time))"
        using unfold_prem3_matches by blast
      then have "(\<And>time. time<length t1 \<Longrightarrow> match_timestep (drop 1 \<pi> ! time) (t1 ! time))"
      proof-
        fix time
        assume time_bound: "time < length t1"
        have "time+1 < length (h1#t1)" using time_bound by auto
        then have "match_timestep (\<pi> ! (time+1)) ((h1 # t1) ! (time+1))" using h1t1_match by auto
        then show "match_timestep (drop 1 \<pi> ! time) (t1 ! time)"
          using cancel_comm_monoid_add_class.diff_cancel unfold_prem3 by auto
      qed
      then have t1_match: "(\<forall>time<length t1. match_timestep (drop 1 \<pi> ! time) (t1 ! time))"
        by blast

      have h2t2_match: "\<forall>time < length (h2 # t2). match_timestep (\<pi> ! time) ((h2 # t2) ! time)"
        using unfold_prem3_matches by blast
      then have "(\<And>time. time<length t2 \<Longrightarrow> match_timestep (drop 1 \<pi> ! time) (t2 ! time))"
        proof-
        fix time
        assume time_bound: "time < length t2"
        have "time+1 < length (h2#t2)" using time_bound by auto
        then have "match_timestep (\<pi> ! (time+1)) ((h2 # t2) ! (time+1))" using h2t2_match by auto
        then show "match_timestep (drop 1 \<pi> ! time) (t2 ! time)"
          using cancel_comm_monoid_add_class.diff_cancel unfold_prem3 by auto
      qed
      then have t2_match: "(\<forall>time<length t2. match_timestep (drop 1 \<pi> ! time) (t2 ! time))"
        by blast

      then have matches: "(\<forall>time<length t1. match_timestep (drop 1 \<pi> ! time) (t1 ! time)) \<and>
                     (\<forall>time<length t2. match_timestep (drop 1 \<pi> ! time) (t2 ! time))"
        using t1_match t2_match by blast
      have "match_regex (drop 1 \<pi>) t1 \<and> match_regex (drop 1 \<pi>) t2"
        using bounds matches unfolding match_regex_def h2t2 by auto
      then have t1t2_notnone: "WEST_and_trace t1 t2 \<noteq> None"
        using Cons.hyps[of num_vars t2 "drop 1 \<pi>", OF t1_nv t2_nv] by simp

      have "WEST_and_trace (h1 # t1) (h2 # t2) \<noteq> None"
        using h1h2_notnone t1t2_notnone WEST_and_trace.simps(3) by auto
      then have ?case using h2t2 by auto
    }
    ultimately show ?case by blast
  qed
qed

paragraph "Correct Forward"

lemma WEST_and_trace_correct_forward_aux:
  assumes "match_regex \<pi> (h#t)"
  shows "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
proof -
  have ind_h: "(\<forall>time<length (h#t). match_timestep (\<pi> ! time) ((h#t) ! time)) \<and> length (h#t) \<le> length \<pi>"
    using assms unfolding match_regex_def by metis
  then have part1: "match_timestep (\<pi> ! 0) h"
   by auto
  have part2: "match_timestep (drop 1 \<pi> ! time) (t ! time)" if time_lt: "time<length t" for time
  proof -
    have match: "match_timestep (\<pi> ! (time+1)) ((h # t) ! (time+1))"
      using ind_h time_lt by auto
    have "(\<pi> ! (time + 1)) = (drop 1 \<pi> ! time)"
      using add.commute add_gr_0 impossible_Cons ind_h less_add_same_cancel2 less_eq_iff_succ_less by auto
    then show ?thesis using match by auto
  qed
  have part3: "length t \<le> length (drop 1 \<pi>)"
    using ind_h by auto
  show ?thesis using part1 part2 part3 unfolding match_regex_def by simp
qed

lemma WEST_and_trace_correct_forward_aux_converse:
  assumes "\<pi> = hxi#txi"
  assumes "match_timestep (hxi) h"
  assumes "match_regex txi t"
  shows "match_regex \<pi> (h#t)"
proof-
  have all_time_t: "\<forall>time<length t. match_timestep (txi ! time) (t ! time)"
     using assms(3) unfolding match_regex_def  by argo
  have len_t_leq: "length t \<le> length txi"
    using assms(3) unfolding match_regex_def  by argo
  have match_ht: "match_timestep (\<pi> ! time) ((h # t) ! time)" if time_ht: "time<length (h # t)"
    for time
  proof -
    {assume *: "time = 0"
      then have ?thesis
        using assms(2) assms(1)
        by auto
    } moreover {assume *: "time > 0"
        then have ?thesis
        using time_ht all_time_t assms(1)
        by auto
    }
    ultimately show ?thesis
      by blast
  qed
  have len_condition: "length (h # t) \<le> length \<pi>"
    using assms(1) len_t_leq by auto
  then show ?thesis
    using match_ht len_condition unfolding match_regex_def by simp
qed


lemma WEST_and_trace_correct_forward_empty_trace:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  assumes match1: "match_regex [] r1"
  assumes match2: "match_regex [] r2"
  shows "\<exists>sometrace. match_regex [] sometrace \<and> (WEST_and_trace r1 r2) = Some sometrace"
proof -
  have r1_empty: "length r1 \<le> length []"
    using match1 unfolding match_regex_def
    by (metis list.size(3))
  have r2_empty: "length r2 \<le> length []"
    using match2 unfolding match_regex_def
  by (metis list.size(3))
  have r1r2: "r1 = [] \<and> r2 = []"
    using r1_empty r2_empty by simp
  have "match_regex [] [] \<and> (WEST_and_trace [] []) = Some []"
    unfolding WEST_and_trace.simps match_regex_def by simp
  then show ?thesis using r1r2
    by blast
qed

lemma WEST_and_trace_correct_forward_nonempty_trace:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  assumes "match_regex \<pi> r1 \<and> match_regex \<pi> r2"
  assumes "length \<pi> > 0"
  shows "\<exists>sometrace. match_regex \<pi> sometrace \<and> (WEST_and_trace r1 r2) = Some sometrace"
proof-
  have "WEST_and_trace r1 r2 \<noteq> None"
    using WEST_and_trace_well_defined[of r1 num_vars r2 \<pi>] assms by blast
  then obtain sometrace where sometrace_obt: "WEST_and_trace r1 r2 = Some sometrace" by blast

  have "match_regex \<pi> sometrace"
    using assms sometrace_obt
  proof(induct sometrace arbitrary: r1 r2 \<pi>)
    case Nil
    then show ?case unfolding match_regex_def by auto
  next
    case (Cons h t)

    have match_r1: "(\<forall>time<length r1. match_timestep (\<pi> ! time) (r1 ! time))"
      using Cons.prems(3) unfolding match_regex_def by argo

    have match_r2: "(\<forall>time<length r2. match_timestep (\<pi> ! time) (r2 ! time))"
      using Cons.prems(3) unfolding match_regex_def by argo

    have match_h_match_t: "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
    proof-
      {assume r1r2_empty: "r1 = [] \<and> r2 = []"
        have "WEST_and_trace r1 r2 = Some []"
          using WEST_and_trace.simps r1r2_empty by blast
        then have ht_empty: "h = [] \<and> t = []"
          using Cons.prems by simp
        have "match_timestep (\<pi>!0) [] \<and> match_regex (drop 1 \<pi>) []"
          unfolding match_regex_def match_timestep_def by simp
        then have "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
          using ht_empty by simp
      } moreover {
        assume r1_empty: "r1 = [] \<and> r2 \<noteq> []"
        obtain h2 t2 where h2t2: "r2 = h2#t2"
          by (meson neq_Nil_conv r1_empty)
        have "WEST_and_trace r1 r2 = Some (h2#t2)"
          using r1_empty WEST_and_trace.simps(2)[of h2 t2] h2t2 by blast
        then have hh2_tt2: "h=h2 \<and> t=t2"
          using Cons.prems by simp
        have "match_timestep (\<pi>!0) h2 \<and> match_regex (drop 1 \<pi>) t2"
          using WEST_and_trace_correct_forward_aux[of \<pi> h2 t2] Cons(4) h2t2 by auto
        then have "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
          using hh2_tt2 by simp
      } moreover {
        assume r2_empty: "r2 = [] \<and> r1 \<noteq> []"
        obtain h1 t1 where h1t1: "r1 = h1#t1"
          by (meson neq_Nil_conv r2_empty)
        have "WEST_and_trace r1 r2 = Some (h1#t1)"
          using r2_empty WEST_and_trace.simps(1)[of r1] h1t1
          by blast
        then have hh1_tt1: "h=h1 \<and> t=t1"
          using Cons.prems by simp
        have "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
          using WEST_and_trace_correct_forward_aux[of \<pi> h1 t1] Cons(4) h1t1 hh1_tt1
          by blast
      } moreover {
        assume r1r2_nonempty: "r1 \<noteq> [] \<and> r2 \<noteq> []"
        obtain h1 t1 where h1t1: "r1 = h1#t1"
          by (meson neq_Nil_conv r1r2_nonempty)
        obtain h2 t2 where h2t2: "r2 = h2#t2"
          by (meson neq_Nil_conv r1r2_nonempty)

        have ht: "WEST_and_trace (h1#t1) (h2#t2) = Some (h # t)"
          using Cons(6) h1t1 h2t2 by blast
        then have h1h2_notnone: "WEST_and_state h1 h2 \<noteq> None"
          using WEST_and_trace.simps(3)[of h1 t1 h2 t2]
          using not_None_eq by fastforce
        then have t1t2_notnone: "WEST_and_trace t1 t2 \<noteq> None"
          using WEST_and_trace.simps(3)[of h1 t1 h2 t2]
          using not_None_eq
          using \<open>WEST_and_trace (h1 # t1) (h2 # t2) = Some (h # t)\<close> by fastforce
        have h_is: "(WEST_and_state h1 h2) = Some h"
          using WEST_and_trace.simps(3)[of h1 t1 h2 t2] h1h2_notnone t1t2_notnone ht
          by auto
        have t_is: "(WEST_and_trace t1 t2) = Some t"
          using WEST_and_trace.simps(3)[of h1 t1 h2 t2] h1h2_notnone t1t2_notnone ht
          by auto

        have h1t1_nv: "\<forall>i<length (h1#t1). length ((h1#t1) ! i) = num_vars"
          using Cons.prems(1) h1t1 unfolding trace_regex_of_vars_def by meson
        then have hyp1: "trace_regex_of_vars t1 num_vars"
          unfolding trace_regex_of_vars_def by auto
        have h2t2_nv: "\<forall>i<length (h2#t2). length ((h2#t2) ! i) = num_vars"
          using Cons.prems(2) h2t2 unfolding trace_regex_of_vars_def by meson
        then have hyp2: "trace_regex_of_vars t2 num_vars"
          unfolding trace_regex_of_vars_def by auto

        have hyp3a: "match_regex (drop 1 \<pi>) t1"
          using WEST_and_trace_correct_forward_aux[of \<pi> h1 t1] h1t1 Cons.prems(3) by blast
        have hyp3b: "match_regex (drop 1 \<pi>) t2"
          using WEST_and_trace_correct_forward_aux[of \<pi> h2 t2] h2t2 Cons.prems(3) by blast
        have hyp3: "match_regex (drop 1 \<pi>) t1 \<and> match_regex (drop 1 \<pi>) t2"
          using hyp3a hyp3b by auto

        have "match_regex (drop 1 \<pi>) t" if "[] = (drop 1 \<pi>)"
          using WEST_and_trace_correct_forward_empty_trace[of t1 num_vars t2]
          using hyp3a hyp3b hyp1 hyp2
          using t_is that by auto

        then have match_t: "match_regex (drop 1 \<pi>) t"
          using Cons.hyps[of t1 t2 "(drop 1 \<pi>)", OF hyp1 hyp2 hyp3] t_is
          by fastforce

        have h1_nv: "state_regex_of_vars h1 num_vars"
          using h1t1_nv unfolding state_regex_of_vars_def by auto
        have h2_nv: "state_regex_of_vars h2 num_vars"
          using h2t2_nv unfolding state_regex_of_vars_def by auto
        have match_h1: "match_timestep (\<pi> ! 0) h1"
          using Cons.prems(3) h1t1 unfolding match_regex_def
          using Cons.prems(3) WEST_and_trace_correct_forward_aux by blast
        have match_h2: "match_timestep (\<pi> ! 0) h2"
          using Cons.prems(3) h2t2 unfolding match_regex_def
          using Cons.prems(3) WEST_and_trace_correct_forward_aux by blast
        have match_h: "match_timestep (\<pi>!0) h"
          using WEST_and_state_correct_forward[of h1 num_vars h2 "\<pi>!0", OF h1_nv h2_nv] h_is
          using match_h1 match_h2 by simp

        have "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
          using match_h match_t by blast
      }
      ultimately show "match_timestep (\<pi>!0) h \<and> match_regex (drop 1 \<pi>) t"
        by blast
    qed

    have match_h: "match_timestep (\<pi>!0) h"
      using match_h_match_t by auto
    have match_t: "match_regex (drop 1 \<pi>) t"
      using match_h_match_t by auto

    have len_\<pi>: "length (drop 1 \<pi>) = (length \<pi>)-1" by auto
    have len_ht: "length t = length (h#t)-1" by auto
    have "length t \<le> length (drop 1 \<pi>)" using match_t unfolding match_regex_def by argo
    then have "(length (h#t))-1 \<le> (length \<pi>)-1" using len_\<pi> len_ht by argo
    then have ht_less_\<pi>: "length (h#t) \<le> length \<pi>"
      using Cons.prems(4)
      by linarith

    have "(\<And>time. time<length (h # t) \<Longrightarrow> (match_timestep (\<pi> ! time) ((h # t) ! time)) \<and>
       length (h # t) \<le> length \<pi>)"
    proof-
      fix time
      assume time_bound: "time<length (h # t)"
      {assume *:"time=0"
        have "(match_timestep (\<pi> ! 0) h) \<and> length (h # t) \<le> length \<pi>"
          using match_h ht_less_\<pi> by simp
        then have "(match_timestep (\<pi> ! time) ((h # t) ! time)) \<and> length (h # t) \<le> length \<pi>"
          using * by simp
      } moreover {
        assume **: "time > 0"
        have time_m1: "time-1 < length t"
          using time_bound
          using "**" len_ht by linarith
        have "(\<forall>time<length t. match_timestep (drop 1 \<pi> ! time) (t ! time))"
          using match_t unfolding match_regex_def by argo
        then have fact0: "match_timestep (drop 1 \<pi> ! (time-1)) (t ! (time-1))"
          using time_m1 by blast
        have fact1: "(t ! (time-1)) = ((h # t) ! time)"
          by (simp add: "**")
        have fact2: "(drop 1 \<pi> ! (time-1)) = (\<pi> ! time)"
          using ** time_m1 ht_less_\<pi> by force

        then have "(match_timestep (\<pi> ! time) ((h # t) ! time))"
          using fact1 fact2 fact0 by simp
        then have "(match_timestep (\<pi> ! time) ((h # t) ! time)) \<and> length (h # t) \<le> length \<pi>"
          using ht_less_\<pi> by simp
      }
      ultimately show "(match_timestep (\<pi> ! time) ((h # t) ! time)) \<and> length (h # t) \<le> length \<pi>"
        by (metis bot_nat_0.not_eq_extremum)
    qed
    then show ?case unfolding match_regex_def by auto
  qed
  then show ?thesis using sometrace_obt by blast
qed

lemma WEST_and_trace_correct_forward:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  assumes "match_regex \<pi> r1 \<and> match_regex \<pi> r2"
  shows "\<exists>sometrace. match_regex \<pi> sometrace \<and> (WEST_and_trace r1 r2) = Some sometrace"
  using WEST_and_trace_correct_forward_empty_trace WEST_and_trace_correct_forward_nonempty_trace
  assms by fast

paragraph \<open> Correct Converse \<close>

lemma WEST_and_trace_nonempty_args:
  fixes h1 h2::"state_regex"
  fixes t t1 t2::"trace_regex"
  assumes "WEST_and_trace (h1 # t1) (h2 # t2) = Some (h # t)"
  shows "WEST_and_state h1 h2 = Some h \<and> WEST_and_trace t1 t2 = Some t"
proof-
  have h1h2_nn: "(WEST_and_state h1 h2) \<noteq> None"
    using WEST_and_trace.simps(3)[of h1 t1 h2 t2] assms
    using option.simps(4) by fastforce
  then have t1t2_nn: "WEST_and_trace t1 t2 \<noteq> None"
    using assms WEST_and_trace.simps(3)[of h1 t1 h2 t2]
    by (metis (no_types, lifting) WEST_and_state_difflengths_is_none WEST_and_state_length option.distinct(1) option.simps(4) option.simps(5))

  have nn: "WEST_and_trace (h1 # t1) (h2 # t2) \<noteq> None" using assms by blast
  then have h_fact: "WEST_and_state h1 h2 = Some h"
    using h1h2_nn t1t2_nn assms WEST_and_trace.simps(3)[of h1 t1 h2 t2] by auto
  then have t_fact: "WEST_and_trace t1 t2 = Some t"
    using t1t2_nn h1h2_nn assms WEST_and_trace.simps(3)[of h1 t1 h2 t2] nn by auto
  show ?thesis using h_fact t_fact by blast
qed

lemma WEST_and_trace_lengths_r1:
  assumes "trace_regex_of_vars r1 n"
  assumes "trace_regex_of_vars r2 n"
  assumes "(WEST_and_trace r1 r2) = Some sometrace"
  shows "length sometrace \<ge> length r1"
  using assms
proof(induction r1 arbitrary:r2 sometrace)
  case Nil
  then show ?case by simp
next
  case (Cons h1 t1)
  {assume r2_empty: "r2 = []"
    have "WEST_and_trace (h1 # t1) r2 = Some (h1 # t1)"
      using Cons WEST_and_trace.simps(1) r2_empty by blast
    then have ?case using Cons by simp
  } moreover {
    assume r2_nonempty: "r2 \<noteq> []"
    obtain h2 t2 where h2t2: "r2 = h2#t2"
      by (meson neq_Nil_conv r2_nonempty)
    have h1t1_and_h2t2: "WEST_and_trace (h1 # t1) (h2 # t2) = Some sometrace"
      using Cons WEST_and_trace.simps(3) h2t2 by blast
    then have h1h2_nn: "(WEST_and_state h1 h2) \<noteq> None"
      using WEST_and_trace.simps(3)[of h1 t1 h2 t2]
      using option.simps(4) by fastforce
    then have t1t2_nn: "WEST_and_trace t1 t2 \<noteq> None"
      using h1t1_and_h2t2 WEST_and_trace.simps(3)[of h1 t1 h2 t2]
      by (metis (no_types, lifting) WEST_and_state_difflengths_is_none WEST_and_state_length option.distinct(1) option.simps(4) option.simps(5))
    obtain h where h_obt: "WEST_and_state h1 h2 = Some h" using h1h2_nn by blast
    obtain t where t_obt: "WEST_and_trace t1 t2 = Some t" using t1t2_nn by blast
    then have *: "sometrace = h # t"
      using h_obt t_obt h1t1_and_h2t2 by auto
    then have sometrace_ht: "WEST_and_trace (h1 # t1) (h2 # t2) = Some (h # t)"
      using h2t2 h1t1_and_h2t2 by blast

    have "\<forall>i<length (h1 # t1). length ((h1 # t1) ! i) = n"
      using Cons.prems unfolding trace_regex_of_vars_def by argo
    then have hyp1: "trace_regex_of_vars t1 n"
      unfolding trace_regex_of_vars_def by auto
    have "\<forall>i<length (h2 # t2). length ((h2 # t2) ! i) = n"
      using Cons.prems h2t2 unfolding trace_regex_of_vars_def by meson
    then have hyp2: "trace_regex_of_vars t2 n"
      unfolding trace_regex_of_vars_def by auto

    have "length t \<ge> length t1"
      using Cons(1)[of "t2" t, OF hyp1 hyp2 t_obt] by simp
    then have ?case using * by simp
  }
  ultimately show ?case by blast
qed

lemma WEST_and_trace_lengths:
  assumes "trace_regex_of_vars r1 n"
  assumes "trace_regex_of_vars r2 n"
  assumes "(WEST_and_trace r1 r2) = Some sometrace"
  shows "length sometrace \<ge> length r1 \<and> length sometrace \<ge> length r2"
  using assms WEST_and_trace_lengths_r1 WEST_and_trace_commutative
proof-
  have lenr1: "length r1 \<le> length sometrace"
    using assms WEST_and_trace_lengths_r1[of r1 n r2 sometrace] by blast
  have "WEST_and_trace r1 r2 = WEST_and_trace r2 r1"
    using WEST_and_trace_commutative assms by blast
  then have lenr2: "length r2 \<le> length sometrace"
    using WEST_and_trace_lengths_r1[of r2 n r1 sometrace] assms by auto
  show ?thesis using lenr1 lenr2 by auto
qed

lemma WEST_and_trace_correct_converse_r1:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  assumes "(\<exists>sometrace. match_regex \<pi> sometrace \<and> (WEST_and_trace r1 r2) = Some sometrace)"
  shows "match_regex \<pi> r1"
  using assms
proof(induct r1 arbitrary: r2 \<pi>)
    case Nil
  then show ?case
    unfolding match_regex_def by auto
  next
    case (Cons h1 t1)
    obtain sometrace where sometrace_obt: "match_regex \<pi> sometrace \<and> (WEST_and_trace (h1#t1) r2) = Some sometrace"
      using Cons.prems by blast
    have match_sometrace_pre: "match_regex \<pi> sometrace" using sometrace_obt by simp
    have r1r2_is_sometrace: "(WEST_and_trace (h1#t1) r2) = Some sometrace" using sometrace_obt by simp
    have match_sometrace: "\<forall>time<length sometrace. match_timestep (\<pi> ! time) (sometrace ! time)"
      using match_sometrace_pre unfolding match_regex_def by argo
    have len_r1: "length (h1#t1) \<le> length \<pi>"
      using Cons.prems sometrace_obt WEST_and_trace_lengths
      by (meson le_trans match_regex_def)

    {assume empty_trace: "\<pi> = []"
      then have ?case using len_r1 by simp
    } moreover {
      assume nonempty_trace: "\<pi> \<noteq> []"
      {assume r2_empty: "r2 = []"
        have "WEST_and_trace (h1#t1) r2 = Some (h1#t1)"
          using sometrace_obt WEST_and_trace.simps r2_empty by simp
        then have ?case using sometrace_obt
          unfolding match_regex_def by force
      } moreover {
        assume r2_nonempty: "r2 \<noteq> []"

        obtain hxi txi where hxitxi: "\<pi> = hxi#txi" using nonempty_trace by (meson list.exhaust)
        obtain h2 t2 where h2t2: "r2 = h2#t2" using r2_nonempty by (meson list.exhaust)
        have not_none: "WEST_and_trace (h1#t1) (h2#t2) = Some sometrace"
          using sometrace_obt h2t2 by blast
        have h1h2_nn: "WEST_and_state h1 h2 \<noteq> None"
          using not_none WEST_and_trace.simps(3)[of h1 t1 h2 t2] not_none
          using option.simps(4) by fastforce
        then have t1t2_nn: "WEST_and_trace t1 t2 \<noteq> None"
          using not_none WEST_and_trace.simps(3)[of h1 t1 h2 t2] not_none
          using option.simps(4) by fastforce
        obtain h t where sometrace_ht: "sometrace = h#t"
          using not_none h1h2_nn t1t2_nn by auto

        have h1h2_h: "WEST_and_state h1 h2 = Some h"
          using WEST_and_trace_nonempty_args[of h1 t1 h2 t2 h t] not_none sometrace_ht
          by blast
        have t1t2_t: "WEST_and_trace t1 t2 = Some t"
          using WEST_and_trace_nonempty_args[of h1 t1 h2 t2 h t] not_none sometrace_ht
          by blast

        have match_ht: "\<forall>time<length (h#t). match_timestep ((hxi # txi) ! time) (((h#t)) ! time)"
          using sometrace_ht sometrace_obt hxitxi unfolding match_regex_def
          by meson
        have h1_nv: "state_regex_of_vars h1 num_vars"
          using Cons.prems unfolding trace_regex_of_vars_def state_regex_of_vars_def
          by (metis Ex_list_of_length append_self_conv2 arbitrary_regtrace_matches_any_trace bot_nat_0.not_eq_extremum le_0_eq less_nat_zero_code list.pred_inject(2) list_all_length list_ex_length list_ex_simps(1) match_regex_def nth_append_length trace_of_vars_def)
        have h2_nv: "state_regex_of_vars h2 num_vars"
          using Cons.prems unfolding trace_regex_of_vars_def h2t2 state_regex_of_vars_def
          by (metis Ex_list_of_length append_self_conv2 arbitrary_regtrace_matches_any_trace bot_nat_0.not_eq_extremum le_0_eq less_nat_zero_code list.pred_inject(2) list_all_length list_ex_length list_ex_simps(1) match_regex_def nth_append_length trace_of_vars_def)
        have match_h: "match_timestep hxi h"
          using match_ht unfolding match_regex_def by auto
        have match_h1: "match_timestep hxi h1"
          using WEST_and_state_correct_converse_s1[of h1 num_vars h2 hxi, OF h1_nv h2_nv]
          using sometrace_ht h1h2_h match_h by blast

        have "\<forall>i<length (h1 # t1). length ((h1 # t1) ! i) = num_vars"
          using Cons.prems unfolding trace_regex_of_vars_def by argo
        then have t1_nv: "trace_regex_of_vars t1 num_vars"
          unfolding trace_regex_of_vars_def by auto
        have "\<forall>i<length (h2 # t2). length ((h2 # t2) ! i) = num_vars"
          using Cons.prems h2t2 unfolding trace_regex_of_vars_def by metis
        then have t2_nv: "trace_regex_of_vars t2 num_vars"
          unfolding trace_regex_of_vars_def h2t2 by auto
        have "match_regex \<pi> (h # t)"
          using sometrace_ht sometrace_obt hxitxi unfolding match_regex_def
          by blast
        then have "match_regex txi t"
          using hxitxi WEST_and_trace_correct_forward_aux[of \<pi> h t]
          unfolding match_regex_def by fastforce
        then have match_t1: "match_regex txi t1"
          using Cons.hyps[of t2 txi, OF t1_nv t2_nv] t1t2_t by blast

        have ?case
          using match_h1 match_t1 len_r1
          using WEST_and_trace_correct_forward_aux_converse[OF _ match_h1 match_t1, of \<pi>] hxitxi
          by blast
      }
      ultimately have ?case by blast
    }
    ultimately show ?case by blast
  qed


lemma WEST_and_trace_correct_converse:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  assumes "(\<exists>sometrace. match_regex \<pi> sometrace \<and> (WEST_and_trace r1 r2) = Some sometrace)"
  shows "match_regex \<pi> r1 \<and> match_regex \<pi> r2"
proof-
  show ?thesis using WEST_and_trace_correct_converse_r1 WEST_and_trace_commutative
    using assms(3) r1_of_num_vars r2_of_num_vars by presburger
qed

lemma WEST_and_trace_correct:
  fixes num_vars::"nat"
  fixes \<pi>::"trace"
  fixes r1 r2:: "trace_regex"
  assumes r1_of_num_vars: "trace_regex_of_vars r1 num_vars"
  assumes r2_of_num_vars: "trace_regex_of_vars r2 num_vars"
  shows "match_regex \<pi> r1 \<and> match_regex \<pi> r2 \<longleftrightarrow> (\<exists>sometrace. match_regex \<pi> sometrace \<and> (WEST_and_trace r1 r2) = Some sometrace)"
  using WEST_and_trace_correct_forward WEST_and_trace_correct_converse assms by blast


subsubsection \<open> WEST-and correct \<close>

paragraph \<open> Correct Forward \<close>

lemma WEST_and_helper_subset_of_WEST_and:
  assumes "List.member L1 elem"
  shows "set (WEST_and_helper elem (h2#T2)) \<subseteq> set (WEST_and L1 (h2#T2))"
  using assms
proof (induct L1)
  case Nil
  then show ?case
    by (simp add: member_rec(2))
next
  case (Cons h1 T1)
  {assume *: "h1 = elem"
    then have ?case using WEST_and.simps(3)[of h1 T1 h2 T2]
      by (simp add: list.case_eq_if)
  } moreover {assume *: "h1 \<noteq> elem"
    then have "List.member T1 elem"
      using Cons
      by (simp add: member_rec(1))
    then have ?case using Cons WEST_and_subset by blast
  }
  ultimately show ?case by blast
qed

lemma WEST_and_trace_element_of_WEST_and_helper:
  assumes "List.member L2 elem2"
  assumes "(WEST_and_trace elem1 elem2) = Some sometrace"
  shows "sometrace \<in> set (WEST_and_helper elem1 L2)"
  using assms
proof (induct L2)
  case Nil
  then show ?case
    by (simp add: member_rec(2))
next
  case (Cons h2 T2)
  {assume *: "elem2 = h2"
    then have ?case
      using WEST_and_helper.simps(2)[of elem1 h2 t2]
      using assms(2) by fastforce
  } moreover  {assume *: "elem2 \<noteq> h2"
    then have "List.member T2 elem2" using Cons(2)
      by (simp add: member_rec(1))
    then have ?case using Cons(1, 3) WEST_and_helper_subset
      by blast
}
  ultimately show ?case by blast
qed

lemma index_of_L_in_L:
  assumes "i < length L"
  shows "List.member L (L ! i)"
  using assms in_set_member by force

lemma WEST_and_indices:
  fixes L1 L2::"WEST_regex"
  fixes sometrace::"trace_regex"
  assumes "\<exists>i1 i2. i1 < length L1 \<and> i2 < length L2 \<and> WEST_and_trace (L1 ! i1) (L2 ! i2) = Some sometrace"
  shows "\<exists>i<length (WEST_and L1 L2). WEST_and L1 L2 ! i = sometrace"
proof-
  obtain i1 i2 where i1_e2_prop: "i1 < length L1 \<and> i2 < length L2 \<and> WEST_and_trace (L1 ! i1) (L2 ! i2) = Some sometrace"
    using assms by blast

  then have elem: "List.member L1 (L1 ! i1)"
    using index_of_L_in_L i1_e2_prop by blast
  have elem2: "List.member L2 (L2 ! i2)"
    using index_of_L_in_L i1_e2_prop by blast

  let ?L = "WEST_and L1 L2"
  have L1_nonempty: "L1 \<noteq> []"
    using i1_e2_prop by fastforce
  have L2_nonempty: "L2 \<noteq> []"
    using i1_e2_prop by fastforce

  obtain h1 t1 where h1t1: "L1 = h1#t1" using L1_nonempty using list.exhaust by blast
  obtain h2 t2 where h2t2: "L2 = h2#t2" using L2_nonempty using list.exhaust by blast

  then have set_subset: "set (WEST_and_helper (L1 ! i1) L2) \<subseteq> set (WEST_and L1 L2)"
    using h2t2 WEST_and_helper_subset_of_WEST_and[of L1 "(L1 ! i1)" h2 t2] elem
    by blast

  have sometrace_in: "sometrace \<in> set (WEST_and_helper (L1 ! i1) L2)"
    using WEST_and_trace_element_of_WEST_and_helper[OF elem2, of "(L1 ! i1)" sometrace]
     i1_e2_prop by blast

  show ?thesis using set_subset sometrace_in
    by (simp add: in_set_conv_nth subset_code(1))
qed

lemma WEST_and_correct_forward:
  fixes n::"nat"
  fixes \<pi>::"trace"
  fixes L1 L2:: "WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 n"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 n"
  assumes "match \<pi> L1 \<and> match \<pi> L2"
  shows "match \<pi> (WEST_and L1 L2)"
proof-
  have L1_nonempty: "L1 \<noteq> []"
    using assms(3) unfolding match_def by auto
  have L2_nonempty: "L2 \<noteq> []"
    using assms(3) unfolding match_def by auto

  obtain i1 i2 where *:"i1 < length L1 \<and> i2 < length L2 \<and> match_regex \<pi> (L1!i1) \<and> match_regex \<pi> (L2!i2)"
    using assms(3) unfolding match_def by metis

  let ?r1 = "L1!i1"
  let ?r2 = "L2!i2"
  have bounds: "i1 < length L1 \<and> i2 < length L2" using * by auto
  have match_r1r2: "match_regex \<pi> ?r1 \<and> match_regex \<pi> ?r2" using * by simp

  have r1_nv: "trace_regex_of_vars (L1 ! i1) n"
    using bounds assms(1) unfolding WEST_regex_of_vars_def by metis
  have r2_nv: "trace_regex_of_vars (L2 ! i2) n"
    using bounds assms(2) unfolding WEST_regex_of_vars_def by metis

  have "\<exists>sometrace. match_regex \<pi> sometrace \<and> (WEST_and_trace ?r1 ?r2) = Some sometrace"
    using WEST_and_trace_correct_forward[of ?r1 n ?r2 \<pi>, OF r1_nv r2_nv match_r1r2] by blast
  then obtain sometrace where sometrace_obt: "match_regex \<pi> sometrace \<and> (WEST_and_trace ?r1 ?r2) = Some sometrace"
    by auto

  have "\<exists>i1 i2.
     i1 < length L1 \<and>
     i2 < length L2 \<and> WEST_and_trace (L1 ! i1) (L2 ! i2) = Some sometrace"
    using bounds sometrace_obt by blast
  then have "\<exists>i < length (WEST_and L1 L2). (WEST_and L1 L2)!i = sometrace"
    using WEST_and_indices[of L1 L2 sometrace]
    using sometrace_obt by force

  then obtain i where sometrace_index: "i < length (WEST_and L1 L2) \<and> (WEST_and L1 L2)!i = sometrace"
    by blast
  have sometrace_match: "match_regex \<pi> sometrace" using sometrace_obt by auto
  have "\<exists>i<length (WEST_and L1 L2). match_regex \<pi> (WEST_and L1 L2 ! i)"
    using sometrace_index sometrace_match by blast
  then show?thesis
    unfolding match_def by simp
qed


paragraph \<open> Correct Converse \<close>

lemma WEST_and_correct_converse_L1:
  fixes n::"nat"
  fixes \<pi>::"trace"
  fixes L1 L2:: "WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 n"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 n"
  assumes "match \<pi> (WEST_and L1 L2)"
  shows "match \<pi> L1"
proof-
  have "\<exists>i<length (WEST_and L1 L2). match_regex \<pi> ((WEST_and L1 L2) ! i)"
    using assms unfolding match_def by argo
  then obtain i where i_obt: "i<length (WEST_and L1 L2) \<and>
                       match_regex \<pi> ((WEST_and L1 L2) ! i)" by auto
  then obtain i1 i2 where i1i2: "i1 < length L1 \<and> i2 < length L2 \<and> Some ((WEST_and L1 L2)!i) = WEST_and_trace (L1!i1) (L2!i2)"
    using WEST_and.simps WEST_and_helper.simps
    by (metis L1_of_num_vars L2_of_num_vars WEST_and_set_member nth_mem)

  have i1_L1: "i1 < length L1" using i1i2 by auto
  have i2_L2: "i2 < length L2" using i1i2 by auto

  let ?r1 = "L1!i1"
  let ?r2 = "L2!i2"
  let ?r = "WEST_and L1 L2 ! i"

  have r1_of_nv: "trace_regex_of_vars (L1 ! i1) n" using assms(1) i1_L1
    unfolding WEST_regex_of_vars_def by metis
  have r2_of_nv: "trace_regex_of_vars (L2 ! i2) n" using assms(2) i2_L2
    unfolding WEST_regex_of_vars_def by metis

  have "match_regex \<pi> ?r"
    using WEST_and_trace_correct_converse[of ?r1 n ?r2 \<pi>, OF r1_of_nv r2_of_nv]
    using i_obt i1i2 by auto
  then have "match_regex \<pi> (WEST_and L1 L2 ! i)" unfolding match_def by simp
  then have match_r1r2: "(match_regex \<pi> (L1 ! i1) \<and> match_regex \<pi> (L2 ! i2))"
    using WEST_and_trace_correct_converse[of ?r1 n ?r2 \<pi>, OF r1_of_nv r2_of_nv]
    using i1i2 i_obt by force
  then have "\<exists>i<length [L1 ! i1]. match_regex \<pi> ([L1 ! i1] ! i)" unfolding match_def by auto
  then have "\<exists>i<1. match_regex \<pi> ([L1 ! i1] ! i)" unfolding match_def by auto
  then have "match_regex \<pi> (L1 ! i1)" by simp
  then show?thesis using i1_L1
    unfolding match_def by auto
qed


lemma WEST_and_correct_converse:
  fixes n::"nat"
  fixes \<pi>::"trace"
  fixes L1 L2:: "WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 n"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 n"
  assumes "match \<pi> (WEST_and L1 L2)"
  shows "match \<pi> L1 \<and> match \<pi> L2"
proof-
  show?thesis using WEST_and_correct_converse_L1 WEST_and_commutative assms
    by (meson regex_equiv_def)
qed


lemma WEST_and_correct:
  fixes \<pi>::"trace"
  fixes L1 L2:: "WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 n"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 n"
  shows "match \<pi> L1 \<and> match \<pi> L2 \<longleftrightarrow> match \<pi> (WEST_and L1 L2)"
proof-
  show?thesis using WEST_and_correct_forward WEST_and_correct_converse assms
    by blast
qed


subsection \<open> Facts about the WEST or operator \<close>

lemma WEST_or_correct:
  fixes \<pi>::"trace"
  fixes L1 L2::"WEST_regex"
  shows "match \<pi> (L1@L2) \<longleftrightarrow> (match \<pi> L1) \<or> (match \<pi> L2)"
proof-
  have forward: "match \<pi> (L1@L2) \<longrightarrow> (match \<pi> L1) \<or> (match \<pi> L2)"
    unfolding match_def
    by (metis add_diff_inverse_nat length_append nat_add_left_cancel_less nth_append)

  have converse: "(match \<pi> L1) \<or> (match \<pi> L2) \<longrightarrow> match \<pi> (L1@L2)"
    unfolding match_def by (metis list_ex_append list_ex_length)
  show ?thesis
    using forward converse by blast
qed


subsection \<open> Pad and Match Facts \<close>

lemma shift_match_regex:
  assumes "length \<pi> \<ge> a"
  assumes "match_regex \<pi> ((arbitrary_trace num_vars a)@L)"
  shows "match_regex (drop a \<pi>) (drop a ((arbitrary_trace num_vars a)@L))"
proof-
  have drop_a: "(drop a ((arbitrary_trace num_vars a)@L)) = L"
    using arbitrary_trace.simps[of num_vars a] by simp
  let ?padL = "(arbitrary_trace num_vars a)@L"
  have "length (arbitrary_trace num_vars a @ L) = a + (length L)"
    by auto
  then have match_all: "\<forall>time<a+(length L). match_timestep (\<pi> ! time) (?padL ! time)"
    using assms(2) arbitrary_trace.simps[of num_vars a]
    unfolding match_regex_def by metis

  have len_xi: "length \<pi> \<ge> a + (length L)"
    using assms(2) arbitrary_trace.simps[of num_vars a]
    unfolding match_regex_def
    using \<open>length (arbitrary_trace num_vars a @ L) = a + length L\<close> by argo

  then have match_drop_a: "match_timestep (drop a \<pi> ! time) (L ! time)"
    if time_le: "time < length L" for time
  proof-
    have "time + a < a + (length L)" using time_le by simp
    then have fact1: "match_timestep (\<pi> ! (time + a)) (?padL ! (time + a))"
      using match_all by blast
    have fact2: "(\<pi> ! (time + a)) = (drop a \<pi> ! time)"
      using time_le len_xi
      by (simp add: add.commute)
    have fact3: "(?padL ! (time + a)) = (L ! time)"
      using time_le len_xi
      by (metis \<open>length (arbitrary_trace num_vars a @ L) = a + length L\<close> add.commute drop_a le_add1 nth_drop)
    show ?thesis
      using fact1 fact2 fact3 by argo
  qed

  have len_L_drop_a: "length L \<le> length (drop a \<pi>)"
    using assms(2) unfolding match_regex_def
    by (metis assms(1) diff_add drop_a drop_drop drop_eq_Nil length_drop)
  then have "match_regex (drop a \<pi>) L" unfolding match_regex_def
    using match_drop_a by metis
  then show ?thesis using drop_a assms by argo
qed

lemma match_regex:
  assumes "length \<pi> \<ge> a"
  assumes "length L1 = a"
  assumes "match_regex \<pi> (L1@L2)"
  shows "match_regex (drop a \<pi>) (drop a (L1@L2))"
proof -
  have time_h: "\<forall>time<length (L1 @ L2). match_timestep (\<pi> ! time) ((L1 @ L2) ! time)"
    using assms unfolding match_regex_def by argo
  then have time: "match_timestep (drop a \<pi> ! time) ((drop a (L1 @ L2)) ! time)" if time_lt: "time<length (drop a (L1 @ L2))" for time
  proof -
    have "time + a < length (L1@L2)"
      using time_lt assms(2) by auto
    then have h0: "match_timestep (\<pi> ! (time + a)) ((L1 @ L2) ! (time + a))"
      using time_h by blast
    have h1: "\<pi> ! (time + a) = (drop a \<pi>) ! time"
      using assms(1)
      by (simp add: add.commute)
    have h2: "((L1 @ L2) ! (time + a)) = (drop a (L1 @ L2)) ! time"
      using assms(2)
      by (metis add.commute append_eq_conv_conj nth_append_length_plus)
    then show ?thesis using assms h0 h1 h2 by simp
  qed
  have len_h: "length (L1 @ L2) \<le> length \<pi>"
    using assms unfolding match_regex_def by argo
  then have len: "length (drop a (L1 @ L2)) \<le> length (drop a \<pi>)"
    using assms(1-2) by auto
  show ?thesis
    using len time unfolding match_regex_def
    by argo
qed


lemma match_regex_converse:
  assumes "length \<pi> \<ge> a"
  assumes "L1 = (arbitrary_trace num_vars a)"
  assumes "match_regex (drop a \<pi>) (drop a (L1@L2))"
  shows "match_regex \<pi> (L1@L2)"
proof-
  have "length (drop a (L1 @ L2)) = length L2"
    using arbitrary_trace.simps[of num_vars a] assms by simp
  then have match_L2: "\<And>time. time<length L2 \<Longrightarrow> match_timestep ((drop a \<pi>) ! time) (L2 ! time)"
  proof-
    fix time
    assume time_lt: "time<length L2"
    then have time_lt_dropa_L1L2: "time < length (drop a (L1 @ L2))"
      using assms(2) arbitrary_trace.simps[of num_vars a] by auto
    have "\<forall>time<length (drop a (L1 @ L2)). match_timestep (drop a \<pi> ! time) (drop a (L1 @ L2) ! time)"
      using assms unfolding match_regex_def by metis
    then have "match_timestep (drop a \<pi> ! time) (drop a (L1 @ L2) ! time)"
      using time_lt_dropa_L1L2 by blast
    then show "match_timestep (drop a \<pi> ! time) (L2 ! time)"
      using assms(2) arbitrary_trace.simps[of num_vars a] by simp
  qed
  have match_L1L2: "match_timestep (\<pi> ! time) ((L1 @ L2) ! time)" if time_le_L1L2: "time<length (L1 @ L2)" for time
  proof-
    {assume time_le_L1: "time < length L1"
      {assume L1_empty: "L1 = []"
        have "match_timestep (\<pi> ! time) (L2 ! time)"
          using assms unfolding match_regex_def arbitrary_trace.simps
          using L1_empty time_le_L1 by auto
        then have ?thesis using L1_empty by simp
      } moreover {
        assume L1_nonempty: "L1 \<noteq> []"
        have L1_arb: "(L1!time) = arbitrary_state num_vars"
          using assms unfolding arbitrary_trace.simps time_le_L1
          using time_le_L1 by auto

        have "match_timestep (\<pi> ! time) (arbitrary_state num_vars)"
          unfolding arbitrary_state.simps match_timestep_def by auto
        then have match_L1: "match_timestep (\<pi> ! time) (L1!time)"
          using L1_arb by auto

        have "(L1 @ L2) ! time = L1!time"
          using time_le_L1L2 time_le_L1 L1_nonempty by (meson nth_append)
        then have ?thesis using match_L1 by auto
      }
      ultimately have ?thesis by blast
    } moreover {
      assume time_geq_L1: "time \<ge> length L1"
      then have time_minus_a_le_L2: "time - a < length L2"
        using assms(2) time_le_L1L2 unfolding arbitrary_trace.simps by simp
      then have match_time_minus_a: "match_timestep ((drop a \<pi>) ! (time - a)) (L2 ! (time - a))"
        using match_L2 by blast

      have "length (drop a (L1 @ L2)) \<le> length (drop a \<pi>)"
        using assms unfolding match_regex_def by metis
      then have L2_le_dropa_xi: "length L2 \<le> length (drop a \<pi>)"
        using assms unfolding arbitrary_trace.simps by simp
      then have fact1_h1: "length L2 \<le> length \<pi> - a" by auto
      have fact1_h2: "length L1 \<le> time" using time_geq_L1 by blast
      have fact1_h3: "time - a < length L2" using time_minus_a_le_L2 by auto
      have fact1_h4: "time < length L1 + length L2" using time_le_L1L2 by simp
      have "length L2 \<le> length \<pi> - a \<Longrightarrow>
            length L1 \<le> time \<Longrightarrow>
            time - a < length L2 \<Longrightarrow>
            time < length L1 + length L2 \<Longrightarrow> \<pi> ! (a + (time - a)) = \<pi> ! time"
        using fact1_h1 fact1_h2 fact1_h3 fact1_h4 time_geq_L1 assms
        unfolding arbitrary_trace.simps by simp
      then have fact1: "drop a \<pi> ! (time - a) = \<pi> ! time"
        using time_geq_L1 time_minus_a_le_L2 time_le_L1L2 L2_le_dropa_xi by simp

      have L1_a: "length L1 = a" using assms unfolding arbitrary_trace.simps by auto
      then have fact2: "L2 ! (time - a) = (L1 @ L2) ! time"
        using fact1_h2 fact1_h3 fact1_h4 time_geq_L1
        by (metis le_add_diff_inverse nth_append_length_plus)

      have ?thesis using fact1 fact2 match_time_minus_a by auto
    }
    ultimately show ?thesis by force
  qed
  have "length (drop a (L1 @ L2)) \<le> length (drop a \<pi>)"
    using assms(2) arbitrary_trace.simps[of num_vars num_pad]
    by (metis assms(3) match_regex_def)
  then have "length (L1 @ L2) \<le> length \<pi>"
    using assms unfolding match_regex_def by simp
  then show ?thesis using match_L1L2 unfolding match_regex_def by simp
qed


lemma shift_match:
  assumes "length \<pi> \<ge> a"
  assumes "match \<pi> (shift L num_vars a)"
  shows "match (drop a \<pi>) L"
proof-
  obtain i where i_obt: "i<length (shift L num_vars a) \<and> match_regex \<pi> (shift L num_vars a ! i)"
    using assms unfolding match_def by force
  have "(shift L num_vars a ! i) = (arbitrary_trace num_vars a)@(L!i)"
    using shift.simps
    using \<open>i < length (shift L num_vars a) \<and> match_regex \<pi> (shift L num_vars a ! i)\<close> by auto

  then have match: "match_regex \<pi> ((arbitrary_trace num_vars a)@(L!i))"
    using i_obt by argo

  have len_at: "length (arbitrary_trace num_vars a) = a"
    unfolding arbitrary_trace.simps by simp

  have drop_a: "(drop a (arbitrary_trace num_vars a)@(L!i)) = L!i"
    using arbitrary_trace.simps[of num_vars a] by simp

  then have "match_regex (drop a \<pi>) (drop a (arbitrary_trace num_vars a)@(L!i))"
    using match using match_regex[OF assms(1) len_at] by simp
  then have "match_regex (drop a \<pi>) (L ! i)"
    using drop_a by argo
  then show ?thesis using assms i_obt unfolding match_def by auto
qed


lemma shift_match_converse:
  assumes "length \<pi> \<ge> a"
  assumes "match (drop a \<pi>) L"
  shows "match \<pi> (shift L num_vars a)"
proof-
  obtain i where i_obt: "match_regex (drop a \<pi>) (L!i) \<and> i < length L"
    using assms unfolding match_def by metis
  then have match_padLi: "match_regex \<pi> ((arbitrary_trace num_vars a)@(L!i))"
    using match_regex_converse assms by auto
  have i_bound: "i<length (shift L num_vars a)"
    using shift.simps i_obt by auto
  have "(shift L num_vars a ! i) = (arbitrary_trace num_vars a)@(L!i)"
    unfolding shift.simps
    by (simp add: i_obt)
  then have "\<exists>i<length (shift L num_vars a). match_regex \<pi> (shift L num_vars a ! i)"
    using assms match_padLi i_bound by metis
  then show ?thesis unfolding match_def by argo
qed

lemma pad_zero:
  shows "shift L2 num_vars 0 = L2"
  unfolding shift.simps arbitrary_trace.simps
proof -
  have "\<exists>wsss. L2 = wsss \<and> (@) ([]::trace_regex) = (\<lambda>wss. wss) \<and> L2 = wsss"
    by blast
  then show "map ((@) (map (\<lambda>n. arbitrary_state num_vars) [0..<0])) L2 = L2"
    by simp
qed

subsection \<open> Facts about WEST num vars \<close>

lemma regtrace_append:
  assumes "trace_regex_of_vars L1 k"
  assumes "trace_regex_of_vars L2 k"
  shows "trace_regex_of_vars (L1@L2) k"
  using assms unfolding trace_regex_of_vars_def
  by (simp add: nth_append)

lemma WEST_num_vars_subformulas:
  assumes "G \<in> subformulas F"
  shows "(WEST_num_vars F) \<ge> WEST_num_vars G"
  using assms
proof (induct F)
  case True_mltl
  then show ?case unfolding subformulas.simps by auto
next
  case False_mltl
  then show ?case unfolding subformulas.simps by auto
next
  case (Prop_mltl x)
  then show ?case unfolding subformulas.simps by auto
next
  case (Not_mltl F)
  then show ?case unfolding subformulas.simps by auto
next
  case (And_mltl F1 F2)
  then show ?case unfolding subformulas.simps by auto
next
  case (Or_mltl F1 F2)
  then show ?case unfolding subformulas.simps by auto
next
  case (Future_mltl F x2 x3a)
  then show ?case unfolding subformulas.simps by auto
next
  case (Global_mltl F x2 x3a)
  then show ?case unfolding subformulas.simps by auto
next
  case (Until_mltl F1 F2 x3a x4a)
  then show ?case unfolding subformulas.simps by auto
next
  case (Release_mltl F1 F2 x3a x4a)
  then show ?case unfolding subformulas.simps by auto
qed

lemma WEST_num_vars_nnf:
  shows "(WEST_num_vars \<phi>) = WEST_num_vars (convert_nnf \<phi>)"
proof (induction "depth_mltl \<phi>" arbitrary: \<phi> rule: less_induct)
  case less
  then show ?case proof (cases \<phi>)
    case True_mltl
    then show ?thesis by auto
  next
    case False_mltl
    then show ?thesis by auto
  next
    case (Prop_mltl x3)
    then show ?thesis by auto
  next
    case (Not_mltl p)
    then show ?thesis proof (induct p)
      case True_mltl
      then show ?case using Not_mltl less by auto
    next
      case False_mltl
      then show ?case using Not_mltl less by auto
    next
      case (Prop_mltl x)
      then show ?case using Not_mltl less by auto
    next
      case (Not_mltl p)
      then show ?case using Not_mltl less by auto
    next
      case (And_mltl \<phi>1 \<phi>2)
      then have phi_is: "\<phi> = Not_mltl (And_mltl \<phi>1 \<phi>2)"
        using Not_mltl by auto
      have ind1: "WEST_num_vars \<phi>1 = WEST_num_vars (convert_nnf (Not_mltl \<phi>1))"
        using less[of "Not_mltl \<phi>1"] phi_is by auto
      have ind2: "WEST_num_vars \<phi>2 = WEST_num_vars (convert_nnf (Not_mltl \<phi>2))"
        using less[of "Not_mltl \<phi>2"] phi_is by auto
      then show ?case using ind1 ind2 phi_is
        by auto
    next
      case (Or_mltl \<phi>1 \<phi>2)
      then have phi_is: "\<phi> = Not_mltl (Or_mltl \<phi>1 \<phi>2)"
        using Not_mltl by auto
      have ind1: "WEST_num_vars \<phi>1 = WEST_num_vars (convert_nnf (Not_mltl \<phi>1))"
        using less[of "Not_mltl \<phi>1"] phi_is by auto
      have ind2: "WEST_num_vars \<phi>2 = WEST_num_vars (convert_nnf (Not_mltl \<phi>2))"
        using less[of "Not_mltl \<phi>2"] phi_is by auto
      then show ?case using ind1 ind2 phi_is
        by auto
    next
      case (Future_mltl a b \<phi>1)
      then have phi_is: "\<phi> = Not_mltl (Future_mltl a b \<phi>1)"
        using Not_mltl
        by auto
      have ind1: "WEST_num_vars \<phi> = WEST_num_vars (convert_nnf (Not_mltl \<phi>1))"
        using less[of "Not_mltl \<phi>1"] phi_is by auto
      then show ?case using ind1  phi_is
        by auto
    next
      case (Global_mltl a b \<phi>1)
      then have phi_is: "\<phi> = Not_mltl (Global_mltl a b \<phi>1)"
        using Not_mltl
        by auto
      have ind1: "WEST_num_vars \<phi> = WEST_num_vars (convert_nnf (Not_mltl \<phi>1))"
        using less[of "Not_mltl \<phi>1"] phi_is by auto
      then show ?case using ind1  phi_is
        by auto
    next
      case (Until_mltl \<phi>1 a b \<phi>2)
      then have phi_is: "\<phi> = Not_mltl (Until_mltl \<phi>1 a b \<phi>2)"
        using Not_mltl by auto
      have ind1: "WEST_num_vars \<phi>1 = WEST_num_vars (convert_nnf (Not_mltl \<phi>1))"
        using less[of "Not_mltl \<phi>1"] phi_is by auto
      have ind2: "WEST_num_vars \<phi>2 = WEST_num_vars (convert_nnf (Not_mltl \<phi>2))"
        using less[of "Not_mltl \<phi>2"] phi_is by auto
      then show ?case using ind1 ind2 phi_is
        by auto
    next
      case (Release_mltl \<phi>1 a b \<phi>2)
      then have phi_is: "\<phi> = Not_mltl (Release_mltl \<phi>1 a b \<phi>2)"
        using Not_mltl by auto
      have ind1: "WEST_num_vars \<phi>1 = WEST_num_vars (convert_nnf (Not_mltl \<phi>1))"
        using less[of "Not_mltl \<phi>1"] phi_is by auto
      have ind2: "WEST_num_vars \<phi>2 = WEST_num_vars (convert_nnf (Not_mltl \<phi>2))"
        using less[of "Not_mltl \<phi>2"] phi_is by auto
      then show ?case using ind1 ind2 phi_is
        by auto
    qed
  next
    case (And_mltl \<phi>1 \<phi>2)
    then show ?thesis using less by auto
  next
    case (Or_mltl \<phi>1 \<phi>2)
    then show ?thesis using less by auto
  next
    case (Future_mltl a b \<phi>)
    then show ?thesis using less by auto
  next
    case (Global_mltl a b \<phi>)
    then show ?thesis using less by auto
  next
    case (Until_mltl \<phi>1 a b \<phi>2)
    then show ?thesis using less by auto
  next
    case (Release_mltl \<phi>1 a b \<phi>2)
    then show ?thesis using less by auto
  qed
qed

subsubsection \<open> Facts about num vars for different WEST operators \<close>

lemma length_WEST_and:
  assumes "length state1 = k"
  assumes "length state2 = k"
  assumes "WEST_and_state state1 state2 = Some state"
  shows "length state = k"
  using assms
proof (induct "length state1" arbitrary: state1 state2 k state rule: less_induct)
  case less
  {assume *: "k = 0"
    then have ?case using less(2-3) less(4) WEST_and_state.simps(1)
      by auto
  } moreover {assume *: "k > 0"
    obtain h1 t1 where h1t1: "state1 = h1#t1"
      using * less(2)
      using list.exhaust by auto
    obtain h2 t2 where h2t2: "state2 = h2#t2"
      using * less(3)
      using list.exhaust by auto
    have "WEST_and_bitwise h1 h2 \<noteq> None"
      by (metis WEST_and_state.simps(2) h1t1 h2t2 less.prems(3) option.discI option.simps(4))
    then obtain h where someh: "WEST_and_bitwise h1 h2 = Some h"
      by blast
    have "WEST_and_state t1 t2 \<noteq> None"
      by (metis (no_types, lifting) WEST_and_state.simps(2) h1t1 h2t2 less.prems(3) option.case_eq_if option.discI)
    then obtain t where somet: "WEST_and_state t1 t2 = Some t"
      by blast
    then have "length t = k-1"
      using less(1)[of t1 "k-1" t2] h1t1 h2t2
      by (metis WEST_and_state_difflengths_is_none diff_Suc_1 length_Cons less.prems(1) lessI option.distinct(1))
    then have ?case using less WEST_and_state.simps(2)[of h1 t1 h2 t2]
      using someh somet
      by (metis WEST_and_state_length option.discI option.inject)
  }
  ultimately show ?case
    by auto
qed

lemma WEST_and_trace_num_vars:
  assumes "trace_regex_of_vars r1 k"
  assumes "trace_regex_of_vars r2 k"
  assumes "(WEST_and_trace r1 r2) = Some sometrace"
  shows "trace_regex_of_vars sometrace k"
  using assms
proof(induct r1 arbitrary: r2 sometrace)
  case Nil
  then have "sometrace = r2"
    using WEST_and_trace.simps(2)
    by (metis WEST_and_trace.simps(1) WEST_and_trace_commutative option.inject)
  then show ?case using Nil unfolding trace_regex_of_vars_def by blast
next
  case (Cons h1 t1)
  {assume r2_empty: "r2 = []"
    then have "sometrace = (h1#t1)"
      using WEST_and_trace.simps WEST_and_trace_commutative(1) Cons.prems by auto
    then have ?case using Cons
      unfolding trace_regex_of_vars_def by blast
  } moreover {
    assume r2_nonempty: "r2 \<noteq> []"
    then obtain h2 t2 where h2t2: "r2 = h2#t2"
      by (meson trim_reversed_regex.cases)
    {assume sometrace_empty: "sometrace = []"
      then have ?case unfolding trace_regex_of_vars_def by simp
    } moreover {
      assume sometrace_nonempty: "sometrace \<noteq> []"
      then obtain h t where ht_obt: "WEST_and_state h1 h2 = Some h \<and> WEST_and_trace t1 t2 = Some t"
        using WEST_and_trace_nonempty_args[of h1 t1 h2 t2] Cons.prems(3)
        by (metis \<open>r2 = h2 # t2\<close> trim_reversed_regex.cases)
      then have sometrace_ht: "sometrace = h#t"
        using Cons.prems(3) unfolding h2t2 by auto

      have h1t1_nv: "\<forall>i<length (h1 # t1). length ((h1 # t1) ! i) = k"
        using Cons.prems unfolding trace_regex_of_vars_def by argo
      have h1_nv: "length h1 = k"
        using h1t1_nv by auto
      have t1_nv: "trace_regex_of_vars t1 k"
        using h1t1_nv unfolding trace_regex_of_vars_def by auto
      have h2t2_nv: "\<forall>i<length (h2 # t2). length ((h2 # t2) ! i) = k"
        using Cons.prems h2t2 unfolding trace_regex_of_vars_def by metis
      have h2_nv: "length h2 = k"
        using h2t2_nv by auto
      have t2_nv: "trace_regex_of_vars t2 k"
        using h2t2_nv unfolding trace_regex_of_vars_def by auto

      have h1h2_h: "WEST_and_state h1 h2 = Some h"
        using ht_obt by simp
      then have h_nv: "length h = k" using h1_nv h2_nv
        using length_WEST_and by blast

      have t1t2_t: "WEST_and_trace t1 t2 = Some t"
        using ht_obt by simp
      then have t_nv: "trace_regex_of_vars t k"
        using Cons.hyps[of t2 t, OF t1_nv t2_nv] by blast

      have t_nv_unfold: "\<forall>i<length t. length (t ! i) = k"
        using h_nv t_nv sometrace_ht unfolding trace_regex_of_vars_def by presburger

      then have "length (sometrace ! i) = k" if i_lt: "i<length sometrace" for i
        using i_lt sometrace_ht h_nv
      proof-
        {assume *: "i = 0"
          then have ?thesis
            using sometrace_ht h_nv by auto
        } moreover {assume *: "i > 0"
          then have "sometrace ! i = t ! (i-1)"
            using i_lt sometrace_ht by simp

          then have ?thesis
            using t_nv_unfold i_lt sometrace_ht
            by (metis "*" One_nat_def Suc_less_eq Suc_pred length_Cons)
        }
        ultimately show ?thesis by auto
      qed
      then have ?case unfolding trace_regex_of_vars_def by auto
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by blast
qed


lemma WEST_and_num_vars:
  assumes "WEST_regex_of_vars L1 k"
  assumes "WEST_regex_of_vars L2 k"
  shows "WEST_regex_of_vars (WEST_and L1 L2) k"
proof-
  {assume L1L2_empty: "(WEST_and L1 L2) = []"
    then have ?thesis unfolding WEST_regex_of_vars_def by simp
  } moreover {
    assume L1L2_nonempty: "WEST_and L1 L2 \<noteq> []"

    have "trace_regex_of_vars (WEST_and L1 L2 ! i) k" if i_index: "i < length (WEST_and L1 L2)" for i
    proof-
      obtain sometrace where sometrace_obt: "(WEST_and L1 L2)!i = sometrace"
        using L1L2_nonempty by simp
      then obtain i1 i2 where i1i2_obt: "i1 < length L1 \<and> i2 < length L2 \<and> Some sometrace = WEST_and_trace (L1!i1) (L2!i2)"
        using WEST_and.simps WEST_and_helper.simps
        by (metis WEST_and_set_member_dir1 assms(1) assms(2) i_index nth_mem)

      let ?r1 = "L1!i1"
      let ?r2 = "L2!i2"
      have r1r2_sometrace: "Some sometrace = WEST_and_trace (L1!i1) (L2!i2)"
        using i1i2_obt by blast
      have r1_nv: "trace_regex_of_vars ?r1 k"
        using assms i1i2_obt unfolding WEST_regex_of_vars_def by metis
      have r2_nv: "trace_regex_of_vars ?r2 k"
        using assms i1i2_obt unfolding WEST_regex_of_vars_def by metis
      have "trace_regex_of_vars sometrace k"
        using r1_nv r2_nv r1r2_sometrace WEST_and_trace_num_vars[of ?r1 k ?r2] by metis
      then show ?thesis
        using sometrace_obt by blast
    qed
    then have ?thesis unfolding WEST_regex_of_vars_def by simp
  }
  ultimately show ?thesis by blast
qed


lemma WEST_or_num_vars:
  assumes L1_nv: "WEST_regex_of_vars L1 k"
  assumes L2_nv: "WEST_regex_of_vars L2 k"
  shows "WEST_regex_of_vars (L1@L2) k"
proof-
  let ?L = "L1@L2"
  have "trace_regex_of_vars (?L!i) k" if i_lt: "i < length ?L" for i
  proof-
    {assume in_L1: "i < length L1"
      then have L1_i_nv: "trace_regex_of_vars (L1!i) k"
        using L1_nv unfolding WEST_regex_of_vars_def by metis
      have "?L!i = L1!i"
        using in_L1
        by (simp add: nth_append)
      then have ?thesis using L1_i_nv by simp
    } moreover {
      assume in_L2: "i \<ge> length L1"
      then have "i - length L1 < length L2"
        using i_lt by auto
      then have L2_i_nv: "trace_regex_of_vars (L2!(i - length L1)) k"
        using L2_nv unfolding WEST_regex_of_vars_def by metis
      have "(?L ! i) = L2!(i - length L1)"
        using in_L2
        by (simp add: nth_append)
      then have ?thesis using L2_i_nv by simp
    }
    ultimately show ?thesis by fastforce
  qed

  then show ?thesis unfolding WEST_regex_of_vars_def by simp
qed


lemma regtraceList_cons_num_vars:
  assumes "trace_regex_of_vars h num_vars"
  assumes "WEST_regex_of_vars T num_vars"
  shows "WEST_regex_of_vars (h#T) num_vars"
proof-
  let ?H = "[h]"
  have "WEST_regex_of_vars ?H num_vars"
    using assms unfolding WEST_regex_of_vars_def by auto
  then have "WEST_regex_of_vars (?H@T) num_vars"
    using WEST_or_num_vars[of ?H num_vars T] assms by simp
  then show ?thesis by simp
qed

lemma WEST_simp_state_num_vars:
  assumes "length s1 = num_vars"
  assumes "length s2 = num_vars"
  shows "length (WEST_simp_state s1 s2) = num_vars"
  using assms WEST_simp_state.simps by auto


lemma WEST_get_state_length:
  assumes "trace_regex_of_vars r num_vars"
  shows "length (WEST_get_state r k num_vars) = num_vars"
  using assms unfolding trace_regex_of_vars_def
  using WEST_get_state.simps[of r k num_vars]
  by (metis leI length_map length_upt minus_nat.diff_0)


lemma WEST_simp_trace_num_vars:
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  shows "trace_regex_of_vars (WEST_simp_trace r1 r2 num_vars) num_vars"
  using WEST_simp_state_num_vars assms
  unfolding WEST_simp_trace.simps trace_regex_of_vars_def
  using WEST_get_state_length assms(1) by auto

lemma remove_element_at_index_preserves_nv:
  assumes "i < length L"
  assumes "WEST_regex_of_vars L num_vars"
  shows "WEST_regex_of_vars (remove_element_at_index i L) num_vars"
proof-
  have "length (take i L @ drop (i + 1) L) = length L-1"
    using assms by simp
  have take_nv: "WEST_regex_of_vars (take i L) num_vars"
    using assms unfolding WEST_regex_of_vars_def
    by (metis in_set_conv_nth in_set_takeD)
  have drop_nv: "WEST_regex_of_vars (drop (i + 1) L) num_vars"
    using assms unfolding WEST_regex_of_vars_def
    by (metis add.commute length_drop less_diff_conv less_iff_succ_less_eq nth_drop)
  then show ?thesis
    using take_nv drop_nv WEST_or_num_vars by simp
qed


lemma update_L_length:
  assumes "h \<in> set (enum_pairs L)"
  shows "length (update_L L h num_var) = length L - 1"
proof-
  have "length L \<le> 1 \<longrightarrow> enum_pairs L = []"
    unfolding enum_pairs.simps using enumerate_pairs.simps
    by (simp add: upt_rec)
  then have len_L: "length L \<ge> 2"
    using assms by auto
  let ?i = "fst h"
  let ?j = "snd h"
  have i_le_j: "?i < ?j" using enum_pairs_fact assms(1)
    by metis
  have j_bound: "?j < length L"
    using assms(1) enum_pairs_bound[of L]
    by metis
  then have i_bound: "?i < (length L)-1"
    using i_le_j by auto

  have len_orsimp: "length [WEST_simp_trace (L ! fst h) (L ! snd h) num_var] = 1"
    by simp
  have "length (remove_element_at_index (snd h) L) = length L - 1"
    using assms j_bound by auto
  then have "length (remove_element_at_index (fst h) (remove_element_at_index (snd h) L)) = length L - 2"
    using assms i_bound j_bound   by simp
  then show ?thesis
    using len_orsimp len_L
    using length_append[of "(remove_element_at_index (fst h) (remove_element_at_index (snd h) L))" "[WEST_simp_trace (L ! fst h) (L ! snd h) num_var]"]
    unfolding update_L.simps by linarith
qed

lemma update_L_preserves_num_vars:
  assumes "WEST_regex_of_vars L num_var"
  assumes "h \<in> set (enum_pairs L)"
  assumes "K = update_L L h num_var"
  shows "WEST_regex_of_vars K num_var"
proof-
  have simp_nv: "trace_regex_of_vars (WEST_simp_trace (L ! fst h) (L ! snd h) num_var) num_var"
    using WEST_simp_trace_num_vars assms unfolding WEST_regex_of_vars_def
    by (metis enum_pairs_bound enum_pairs_fact order.strict_trans)
  then have simp_nv: "WEST_regex_of_vars [WEST_simp_trace (L ! fst h) (L ! snd h) num_var] num_var"
    unfolding WEST_regex_of_vars_def by auto
  have *:"WEST_regex_of_vars (remove_element_at_index (snd h) L) num_var"
    using assms remove_element_at_index_preserves_nv
    using enum_pairs_fact[of L] enum_pairs_bound[of L]
    using remove_element_at_index_preserves_nv by blast
  let ?La = "(remove_element_at_index (snd h) L)"
  have "fst h < length (remove_element_at_index (snd h) L)"
    using enum_pairs_fact[of L] enum_pairs_bound[of L] assms(2)
    by auto
  then have "WEST_regex_of_vars (remove_element_at_index (fst h) (remove_element_at_index (snd h) L)) num_var"
    using remove_element_at_index_preserves_nv[of "fst h" ?La num_var] *
    by blast
  then show ?thesis
    using simp_nv assms(3) unfolding update_L.simps using WEST_or_num_vars
    using WEST_regex_of_vars_def by blast
qed

lemma WEST_simp_helper_can_simp:
  assumes "simp_L = WEST_simp_helper L (enum_pairs L) i num_vars"
  assumes "\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))"
  assumes "min_j = Min {j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))}"
  assumes "newL = update_L L (enum_pairs L ! min_j) num_vars"
  assumes "i < length (enum_pairs L)"
  shows "simp_L = WEST_simp_helper newL (enum_pairs newL) 0 num_vars"
proof-
  let ?j_set = "{j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                check_simp (L ! fst (enum_pairs L ! j))
                           (L ! snd (enum_pairs L ! j))}"
  have cond1: "finite ?j_set"
    by fast
  have cond2: "?j_set \<noteq> {}"
    using assms(2) by blast
  have "min_j \<in> ?j_set"
    using Min_in[OF cond1 cond2] assms(3) by blast
  then have min_j_props: "min_j < length (enum_pairs L) \<and> min_j \<ge> i
                        \<and> check_simp (L ! fst (enum_pairs L ! min_j))
                                     (L ! snd (enum_pairs L ! min_j))"
    by blast
  have minimality: "\<not> (check_simp (L ! fst (enum_pairs L ! k))
                                  (L ! snd (enum_pairs L ! k)))"
    if k_prop: "(k < min_j \<and> k < length (enum_pairs L) \<and> k \<ge> i)"
    for k
  proof-
    have "k \<notin> ?j_set"
      using assms(3) Min_gr_iff[of ?j_set k] k_prop
      by (metis (no_types, lifting) empty_iff finite_nat_set_iff_bounded mem_Collect_eq order_less_imp_not_eq2)
    then show ?thesis using k_prop by blast
  qed
  then have minimality: "\<forall>k. (k < min_j \<and> k < length (enum_pairs L) \<and> k \<ge> i) \<longrightarrow>
                       \<not> (check_simp (L ! fst (enum_pairs L ! k))
                                     (L ! snd (enum_pairs L ! k)))"
    by blast
  show ?thesis
    using assms(1, 4, 5) minimality min_j_props
  proof(induction "min_j - i" arbitrary: min_j i L simp_L newL)
    case 0
    then have "check_simp (L ! fst (enum_pairs L ! i))
     (L ! snd (enum_pairs L ! i))"
      by force
    then show ?case
      using 0 WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
      by (metis diff_diff_cancel diff_zero linorder_not_less)
  next
    case (Suc x)
    have min_j_eq: "min_j - i = x+1"
      using Suc.hyps(2) by auto
    then have "min_j > i"
      by auto
    then have cant_match_i: "\<not> (check_simp (L ! fst (enum_pairs L ! i))
                                     (L ! snd (enum_pairs L ! i)))"
      using Suc by fast
    let ?simp_L = "WEST_simp_helper L (enum_pairs L) i num_vars"
    let ?simp_Lnext = "WEST_simp_helper L (enum_pairs L) (i+1) num_vars"
    let ?newL = "update_L L (enum_pairs L ! min_j) num_vars"
    have simp_L_eq: "?simp_L = ?simp_Lnext"
      using cant_match_i WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars] Suc.prems(3)
      by auto
    have cond1: "x = min_j - (i+1)"
      using min_j_eq by auto
    have cond2: "?simp_Lnext = WEST_simp_helper L (enum_pairs L) (i+1) num_vars"
      by simp
    have cond3: "?newL = update_L L (enum_pairs L ! min_j) num_vars"
      by simp
    have cond4: "i + 1 < length (enum_pairs L)"
      using Suc by linarith
    have cond5: "\<forall>k. k < min_j \<and> k < length (enum_pairs L) \<and> i + 1 \<le> k \<longrightarrow>
      \<not> check_simp (L ! fst (enum_pairs L ! k))
          (L ! snd (enum_pairs L ! k))"
      using Suc
      using add_leD1 by blast
    have cond6: "min_j < length (enum_pairs L) \<and> i + 1 \<le> min_j \<and>
                 check_simp (L ! fst (enum_pairs L ! min_j))
                            (L ! snd (enum_pairs L ! min_j))"
      using Suc by linarith

    have "?simp_Lnext = WEST_simp_helper newL (enum_pairs newL) 0 num_vars"
      using Suc.hyps(1)[OF cond1 cond2 cond3 cond4 cond5 cond6]
      using Suc.prems by blast
    then show ?case
      using simp_L_eq Suc.prems(1) by argo
  qed
qed

lemma WEST_simp_helper_cant_simp:
  assumes "simp_L = WEST_simp_helper L (enum_pairs L) i num_vars"
  assumes "\<not>(\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j)))"
  shows "simp_L = L"
  using assms
proof(induct "length (enum_pairs L) - i" arbitrary: simp_L L i )
  case 0
  then have "i \<ge> length (enum_pairs L)"
    by simp
  then show ?case
    using 0(2) WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
    by auto
next
  case (Suc x)
  then have i_eq: "i = length (enum_pairs L) - (x+1)"
    by simp
  let ?simp_L = "WEST_simp_helper L (enum_pairs L) i num_vars"
  let ?simp_nextL = "WEST_simp_helper L (enum_pairs L) (i+1) num_vars"
  have simp_L_eq: "?simp_L = ?simp_nextL"
    using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
    using i_eq Suc
    by (metis diff_is_0_eq le_refl nat.distinct(1) zero_less_Suc zero_less_diff)
  have cond1: "x = length (enum_pairs L) - (i+1)"
    using Suc.hyps(2) by auto
  have cond2: "?simp_nextL = WEST_simp_helper L (enum_pairs L) (i + 1) num_vars"
    by blast
  have cond3: "\<not> (\<exists>j<length (enum_pairs L).
         i + 1 \<le> j \<and>
         check_simp (L ! fst (enum_pairs L ! j))
          (L ! snd (enum_pairs L ! j)))"
    using Suc by auto
  have "?simp_nextL = L"
    using Suc.hyps(1)[OF cond1 cond2 cond3] by auto
  then show ?case
    using Suc.prems(1) simp_L_eq by argo
qed

lemma WEST_simp_helper_length:
  shows "length (WEST_simp_helper L (enum_pairs L) i num_vars) \<le> length L"
proof(induct "length L" arbitrary: L i rule: less_induct)
case less
  {assume i_geq: "length (enum_pairs L) \<le> i"
    then have "WEST_simp_helper L (enum_pairs L) i num_vars = L"
      using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
      by simp
    then have ?case
      by auto
  } moreover {
    assume i_le: "length (enum_pairs L) > i"
    then have WEST_simp_helper_eq: "WEST_simp_helper L (enum_pairs L) i num_vars =
          (if check_simp (L ! fst (enum_pairs L ! i))
              (L ! snd (enum_pairs L ! i))
          then let newL = update_L L (enum_pairs L ! i) num_vars
               in WEST_simp_helper newL (enum_pairs newL) 0 num_vars
          else WEST_simp_helper L (enum_pairs L) (i + 1) num_vars)"
      using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
      by simp
    let ?simp_L = "WEST_simp_helper L (enum_pairs L) i num_vars"
    {assume can_simp: "\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))"
      then obtain min_j where obt_min_j: "min_j = Min {j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))}"
        by blast
      let ?newL = "update_L L (enum_pairs L ! min_j) num_vars"
      have "?simp_L = WEST_simp_helper ?newL (enum_pairs ?newL) 0 num_vars"
        using WEST_simp_helper_can_simp[of ?simp_L L i num_vars min_j ?newL]
        using obt_min_j can_simp i_le by blast
      have min_j_bounds: "min_j < length (enum_pairs L) \<and> min_j \<ge> i"
        using can_simp obt_min_j Min_in[of "{j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))}"]
        by fastforce
      have "length ?newL < length L"
        using update_L_length[of "enum_pairs L ! min_j" L num_vars]
        using min_j_bounds
        by (metis diff_less enum_pairs_bound less_nat_zero_code not_gr_zero nth_mem zero_less_one)
      then have ?case
        using less(1)[of ?newL] less.prems min_j_bounds update_L_preserves_num_vars
        by (metis (no_types, lifting) \<open>WEST_simp_helper L (enum_pairs L) i num_vars = WEST_simp_helper (update_L L (enum_pairs L ! min_j) num_vars) (enum_pairs (update_L L (enum_pairs L ! min_j) num_vars)) 0 num_vars\<close> leD le_trans nat_le_linear)
    } moreover {
      assume cant_simp: "\<not>(\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j)))"
      then have "?simp_L = L"
        using WEST_simp_helper_cant_simp i_le by blast
      then have ?case by simp
    }
    ultimately have ?case using WEST_simp_helper_eq by blast
  }
  ultimately show ?case
    using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
    by fastforce
qed

lemma WEST_simp_helper_num_vars:
  assumes "WEST_regex_of_vars L num_vars"
  shows "WEST_regex_of_vars (WEST_simp_helper L (enum_pairs L) i num_vars) num_vars"
  using assms
proof(induct "length L" arbitrary: L i rule: less_induct)
  case less
  {assume i_geq: "length (enum_pairs L) \<le> i"
    then have "WEST_simp_helper L (enum_pairs L) i num_vars = L"
      using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
      by simp
    then have ?case
      using less by argo
  } moreover {
    assume i_le: "length (enum_pairs L) > i"
    then have WEST_simp_helper_eq: "WEST_simp_helper L (enum_pairs L) i num_vars =
          (if check_simp (L ! fst (enum_pairs L ! i))
              (L ! snd (enum_pairs L ! i))
          then let newL = update_L L (enum_pairs L ! i) num_vars
               in WEST_simp_helper newL (enum_pairs newL) 0 num_vars
          else WEST_simp_helper L (enum_pairs L) (i + 1) num_vars)"
      using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
      by simp
    let ?simp_L = "WEST_simp_helper L (enum_pairs L) i num_vars"
    {assume can_simp: "\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))"
      then obtain min_j where obt_min_j: "min_j = Min {j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))}"
        by blast
      let ?newL = "update_L L (enum_pairs L ! min_j) num_vars"
      have "?simp_L = WEST_simp_helper ?newL (enum_pairs ?newL) 0 num_vars"
        using WEST_simp_helper_can_simp[of ?simp_L L i num_vars min_j ?newL]
        using obt_min_j can_simp i_le by blast
      have min_j_bounds: "min_j < length (enum_pairs L) \<and> min_j \<ge> i"
        using can_simp obt_min_j Min_in[of "{j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))}"]
        by fastforce
      have "length ?newL < length L"
        using update_L_length[of "enum_pairs L ! min_j" L num_vars]
        using min_j_bounds
        by (metis diff_less enum_pairs_bound less_nat_zero_code not_gr_zero nth_mem zero_less_one)
      then have ?case
        using less(1)[of ?newL] less.prems min_j_bounds update_L_preserves_num_vars
        by (metis \<open>WEST_simp_helper L (enum_pairs L) i num_vars = WEST_simp_helper (update_L L (enum_pairs L ! min_j) num_vars) (enum_pairs (update_L L (enum_pairs L ! min_j) num_vars)) 0 num_vars\<close> nth_mem)
    } moreover {
      assume cant_simp: "\<not>(\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j)))"
      then have "?simp_L = L"
        using WEST_simp_helper_cant_simp i_le by blast
      then have ?case using less by simp
    }
    ultimately have ?case using WEST_simp_helper_eq by blast
  }
  ultimately show ?case
    using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
    by fastforce
qed

lemma WEST_simp_num_vars:
  assumes "WEST_regex_of_vars L num_vars"
  shows "WEST_regex_of_vars (WEST_simp L num_vars) num_vars"
  unfolding WEST_simp.simps
  using WEST_simp_helper_num_vars assms by blast

lemma WEST_and_simp_num_vars:
  assumes "WEST_regex_of_vars L1 k"
  assumes "WEST_regex_of_vars L2 k"
  shows "WEST_regex_of_vars (WEST_and_simp L1 L2 k) k"
  unfolding WEST_and_simp.simps
  using WEST_simp_num_vars WEST_and_num_vars assms by blast


lemma WEST_or_simp_num_vars:
  assumes "WEST_regex_of_vars L1 k"
  assumes "WEST_regex_of_vars L2 k"
  shows "WEST_regex_of_vars (WEST_or_simp L1 L2 k) k"
  unfolding WEST_or_simp.simps
  using WEST_simp_num_vars WEST_or_num_vars assms by blast


lemma shift_num_vars:
  fixes L::"WEST_regex"
  fixes a k::"nat"
  assumes "WEST_regex_of_vars L k"
  shows "WEST_regex_of_vars (shift L k a) k"
  using assms
proof(induct L)
  case Nil
  then show ?case
    unfolding WEST_regex_of_vars_def by auto
next
  case (Cons h t)
  let ?padding = "arbitrary_trace k a"
  let ?padh = "?padding @ h"
  let ?padt = "shift t k a"
  have padding_nv: "\<forall>i<length (arbitrary_trace k a). length (arbitrary_trace k a ! i) = k"
    unfolding trace_regex_of_vars_def by auto
  have h_nv: "trace_regex_of_vars h k"
    using Cons.prems unfolding WEST_regex_of_vars_def
    by (metis length_greater_0_conv list.distinct(1) nth_Cons_0)
  then have h_nv: "\<forall>i<length h. length (h ! i) = k"
    unfolding trace_regex_of_vars_def by metis
  have "length ((?padding @ h) ! i) = k" if i_lt: "i < length (?padding @ h)" for i
  proof-
    {assume in_padding: "i < length ?padding"
      then have ?thesis
        using padding_nv
        by (metis nth_append)
    } moreover {
      assume in_h: "i \<ge> length ?padding"
      let ?index = "i - (length ?padding)"
      have "i - (length ?padding) < length h"
        using i_lt in_h by auto
      then have "h!?index = (?padding@h)!i"
        using i_lt in_h by (simp add: nth_append)
      then have ?thesis using h_nv
        by (metis \<open>i - length (arbitrary_trace k a) < length h\<close>)
    }
    ultimately show ?thesis by fastforce
  qed
  then have padh_nv: "trace_regex_of_vars ?padh k"
    unfolding trace_regex_of_vars_def by simp
  have "\<forall>ka<length (h # t). trace_regex_of_vars ((h # t) ! ka) k"
    using Cons.prems unfolding WEST_regex_of_vars_def by metis
  then have "WEST_regex_of_vars t k"
    unfolding WEST_regex_of_vars_def by auto
  then have padt_nv: "WEST_regex_of_vars ?padt k"
    using Cons.hyps by simp
  then show ?case using padh_nv padt_nv
    using regtraceList_cons_num_vars[of ?padh k ?padt] by simp
qed


lemma WEST_future_num_vars:
  assumes "WEST_regex_of_vars L k"
  assumes "a \<le> b"
  shows "WEST_regex_of_vars (WEST_future L a b k) k"
  using assms
proof(induct "b-a" arbitrary: L a b)
  case 0
  then have "a = b" by simp
  then have WEST_future_base: "(WEST_future L a b k) = shift L k a"
    using WEST_future.simps[of L a b k] by auto
  have "WEST_regex_of_vars (shift L k a) k"
    using shift_num_vars 0 by blast
  then show ?case using WEST_future_base by simp
next
  case (Suc x)
  then have "b = a + (Suc x)" by auto
  then have west_future: "WEST_future L a b k = WEST_or_simp (shift L k b) (WEST_future L a (b - 1) k) k"
    using WEST_future.simps[of L a b k]
    by (metis Suc.hyps(2) Zero_not_Suc cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' linorder_le_less_linear)
  have fact: "WEST_regex_of_vars (shift L k b) k"
    using shift_num_vars Suc by blast
  have indh: "WEST_regex_of_vars (WEST_future L a (b - 1) k) k"
    using Suc.hyps Suc.prems by simp
  show ?case
    using west_future WEST_or_simp_num_vars fact indh by metis
qed


lemma WEST_global_num_vars:
  assumes "WEST_regex_of_vars L k"
  assumes "a \<le> b"
  shows "WEST_regex_of_vars (WEST_global L a b k) k"
  using assms
proof(induct "b-a" arbitrary: L a b)
  case 0
  then have "a = b" by simp
  then have WEST_global_base: "(WEST_global L a b k) = shift L k a"
    using WEST_global.simps[of L a b k] by auto
  have "WEST_regex_of_vars (shift L k a) k"
    using shift_num_vars 0 by blast
  then show ?case using WEST_global_base by simp
next
  case (Suc x)
  then have "b = a + (Suc x)" by auto
  then have west_global: "WEST_global L a b k = WEST_and_simp (shift L k b) (WEST_global L a (b - 1) k) k"
    using WEST_global.simps[of L a b k]
    by (metis Suc.hyps(2) Suc.prems(2) add_leE cancel_comm_monoid_add_class.diff_cancel le_numeral_extra(3) nat_less_le not_one_le_zero plus_1_eq_Suc)
  have fact: "WEST_regex_of_vars (shift L k b) k"
    using shift_num_vars Suc by blast
  have indh: "WEST_regex_of_vars (WEST_global L a (b - 1) k) k"
    using Suc.hyps Suc.prems by simp
  show ?case
    using west_global WEST_and_simp_num_vars fact indh
    by metis
qed


lemma WEST_until_num_vars:
  assumes "WEST_regex_of_vars L1 k"
  assumes "WEST_regex_of_vars L2 k"
  assumes "a \<le> b"
  shows "WEST_regex_of_vars (WEST_until L1 L2 a b k) k"
  using assms
proof(induct "b-a" arbitrary: L1 L2 a b)
  case 0
  then have "a = b" by auto
  have "WEST_until L1 L2 a b k = WEST_global L2 a a k"
    using WEST_until.simps[of L1 L2 a b k] 0 by auto
  then show ?case using 0 WEST_global_num_vars[of L2 k a b] by simp
next
  case (Suc x)
  then have "b = a + (Suc x)" by auto
  then have west_until: "WEST_until L1 L2 a b k = WEST_or_simp (WEST_until L1 L2 a (b - 1) k)
                                                   (WEST_and_simp (WEST_global L1 a (b - 1) k) (WEST_global L2 b b k) k) k"
    using WEST_until.simps[of L1 L2 a b k]
    by (metis Suc.prems(3) Zero_neq_Suc add_eq_self_zero order_neq_le_trans)

  have fact1: "WEST_regex_of_vars (WEST_global L1 a (b - 1) k) k"
    using WEST_global_num_vars Suc by auto
  have fact2: "WEST_regex_of_vars (WEST_global L2 b b k) k"
    using WEST_global_num_vars Suc by blast
  have indh: "WEST_regex_of_vars (WEST_until L1 L2 a (b - 1) k) k"
    using Suc.hyps Suc.prems by simp
  show ?case
    using west_until WEST_and_num_vars fact1 fact2 indh
    using WEST_and_simp_num_vars WEST_or_simp_num_vars by metis
qed


lemma WEST_release_helper_num_vars:
  assumes "WEST_regex_of_vars L1 k"
  assumes "WEST_regex_of_vars L2 k"
  assumes "a \<le> b"
  shows "WEST_regex_of_vars (WEST_release_helper L1 L2 a b k) k"
  using assms
proof(induct "b-a" arbitrary: L1 L2 a b)
  case 0
  then have "a = b" by auto
  then have "WEST_release_helper L1 L2 a b k = WEST_and_simp (WEST_global L1 a a k) (WEST_global L2 a a k) k"
    using WEST_release_helper.simps[of L1 L2 a b k] by argo
  have fact1: "WEST_regex_of_vars (WEST_global L1 a a k) k"
    using WEST_global_num_vars[of L1 k a a] 0 by blast
  have fact2: "WEST_regex_of_vars (WEST_global L2 a a k) k"
    using WEST_global_num_vars[of L2 k a a] 0 by blast
  then show ?case using WEST_release_helper.simps[of L1 L2 a b k] 0
    using fact1 fact2 WEST_and_simp_num_vars by auto
next
  case (Suc x)
  then have "b = a + (Suc x)" by auto
  then have west_release_helper: "WEST_release_helper L1 L2 a b k = WEST_or_simp (WEST_release_helper L1 L2 a (b - 1) k)
               (WEST_and_simp (WEST_global L2 a b k) (WEST_global L1 b b k) k) k"
    using WEST_release_helper.simps[of L1 L2 a b k]
    by (metis Suc.hyps(2) Suc.prems(3) add_eq_0_iff_both_eq_0 cancel_comm_monoid_add_class.diff_cancel le_neq_implies_less plus_1_eq_Suc zero_neq_one)

  have fact1: "WEST_regex_of_vars ((WEST_global L2 a b k)) k"
    using WEST_global_num_vars Suc by auto
  have fact2: "WEST_regex_of_vars (WEST_global L1 b b k) k"
    using WEST_global_num_vars Suc by blast
  have indh: "WEST_regex_of_vars (WEST_release_helper L1 L2 a (b - 1) k) k"
    using Suc.hyps Suc.prems by simp
  show ?case using WEST_release_helper.simps[of L1 L2 a b k]
    using fact1 fact2 indh WEST_and_simp_num_vars WEST_or_simp_num_vars Suc
    by presburger
qed


lemma WEST_release_num_vars:
  assumes "WEST_regex_of_vars L1 k"
  assumes "WEST_regex_of_vars L2 k"
  assumes "a \<le> b"
  shows "WEST_regex_of_vars (WEST_release L1 L2 a b k) k"
  using assms
proof-
  {assume a_eq_b: "a = b"
    then have "WEST_release L1 L2 a b k = WEST_global L2 a b k"
      using WEST_release.simps[of L1 L2 a b k] by auto
    then have ?thesis using WEST_global_num_vars assms by auto
  } moreover {
    assume a_neq_b: "a \<noteq> b"
    then have b_pos: "b > 0" using assms by simp
    have a_leq_bm1: "a \<le> b-1" using a_neq_b assms by auto
    then have a_le_b: "a < b" using b_pos by auto
    have "WEST_release L1 L2 a b k = WEST_or_simp (WEST_global L2 a b k) (WEST_release_helper L1 L2 a (b - 1) k) k"
      using WEST_release.simps[of L1 L2 a b k] a_le_b by argo
    then have ?thesis
      using WEST_global_num_vars[of L2 a b k]
      using WEST_release_helper_num_vars[of L1 k L2 a b]
      using WEST_or_simp_num_vars[of "WEST_global L2 a b k" k "WEST_release_helper L1 L2 a (b - 1) k"]
      using WEST_global_num_vars WEST_release_helper_num_vars a_leq_bm1 assms(1) assms(2) assms(3) by presburger
  }
  ultimately show ?thesis by blast
qed


lemma WEST_reg_aux_num_vars:
  assumes is_nnf: "\<exists> \<psi>. F1 = (convert_nnf \<psi>)"
  assumes "k \<ge> WEST_num_vars F1"
  assumes "intervals_welldef F1"
  shows "WEST_regex_of_vars (WEST_reg_aux F1 k) k"
  using assms
proof (induct F1 rule: nnf_induct)
  case nnf
  then show ?case using is_nnf by simp
next
  case True
  then show ?case using WEST_reg_aux.simps(1)[of k]
    unfolding WEST_regex_of_vars_def trace_regex_of_vars_def by auto
next
  case False
  show ?case using WEST_reg_aux.simps(2)
    unfolding WEST_regex_of_vars_def trace_regex_of_vars_def by auto
next
  case (Prop p)
  then show ?case using WEST_reg_aux.simps(3)[of p k]
    unfolding WEST_regex_of_vars_def trace_regex_of_vars_def by auto
next
  case (NotProp F p)
  then show ?case using WEST_reg_aux.simps(3)[of p k]
    unfolding WEST_regex_of_vars_def trace_regex_of_vars_def by auto
next
  case (And F F1 F2)
  have nnf_F1: "\<exists>\<psi>. F1 = convert_nnf \<psi>" using And(1, 4)
    by (metis convert_nnf.simps(4) convert_nnf_convert_nnf mltl.inject(3))
  then have F1_k: "WEST_regex_of_vars (WEST_reg_aux F1 k) k"
    using And by auto
  have nnf_F2: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
    by (metis And.hyps(1) And.prems(1) convert_nnf.simps(4) convert_nnf_convert_nnf mltl.inject(3))
  then have F2_k: "WEST_regex_of_vars (WEST_reg_aux F2 k) k"
    using And by auto
  have nv_F1: "WEST_num_vars F1 \<le> k"
    using  WEST_num_vars_subformulas[of F1 "And_mltl F1 F2"] And(1,5) unfolding subformulas.simps
    by simp
  have nv_F2: "WEST_num_vars F2 \<le> k"
    using  WEST_num_vars_subformulas[of F2 "And_mltl F1 F2"] And(1,5) unfolding subformulas.simps
    by simp
  show ?case
    using WEST_reg_aux.simps(6)[of F1 F2 k] And And(2)[OF nnf_F1 nv_F1] And(3)[OF nnf_F2 nv_F2]
    using WEST_and_simp_num_vars[of "(WEST_reg_aux F1 k)" k "(WEST_reg_aux F2 k)"]
    by auto
next
  case (Or F F1 F2)
  have nnf_F1: "\<exists>\<psi>. F1 = convert_nnf \<psi>" using Or
    by (metis convert_nnf.simps(5) convert_nnf_convert_nnf mltl.inject(4))
  then have F1_k: "WEST_regex_of_vars (WEST_reg_aux F1 k) k"
    using Or by auto
  have nnf_F2: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
    by (metis Or.hyps(1) Or.prems(1) convert_nnf.simps(5) convert_nnf_convert_nnf mltl.inject(4))
  then have F2_k: "WEST_regex_of_vars (WEST_reg_aux F2 k) k"
    using Or by auto
  let ?L1 = "(WEST_reg_aux F1 k)"
  let ?L2 = "(WEST_reg_aux F2 k)"
  have "WEST_regex_of_vars ?L1 k"
    using Or nnf_F1 by simp
  then have L1_nv: "\<forall>i<length (WEST_reg_aux F1 k). trace_regex_of_vars (WEST_reg_aux F1 k ! i) k"
    unfolding WEST_regex_of_vars_def by metis
  have "WEST_regex_of_vars ?L2 k"
    using Or nnf_F2 by simp
  then have L2_nv: "\<forall>j<length (WEST_reg_aux F2 k). trace_regex_of_vars (WEST_reg_aux F2 k ! j) k"
    unfolding WEST_regex_of_vars_def by metis

  have L1L2_L: "WEST_reg_aux F k = WEST_or_simp ?L1 ?L2 k"
    using WEST_reg_aux.simps(5)[of F1 F2 k] Or by blast
  let ?L = "?L1@?L2"
  show ?case
    using WEST_or_simp_num_vars[of ?L1 k ?L2, OF] L1_nv L2_nv L1L2_L
    unfolding WEST_regex_of_vars_def by auto
next
  case (Final F F1 a b)
  let ?L1 = "WEST_reg_aux F1 k"
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>" using Final
    by (metis convert_nnf.simps(6) convert_nnf_convert_nnf mltl.inject(5))
  then have L1_nv: "WEST_regex_of_vars ?L1 k"
    using Final by simp
  have WEST_reg_future: "WEST_reg_aux (Future_mltl a b F1) k = WEST_future ?L1 a b k"
    using WEST_reg_aux.simps(7)[of a b F1 k] by blast
  let ?L = "WEST_future ?L1 a b k"
  have "WEST_regex_of_vars ?L k"
    using L1_nv WEST_future_num_vars[of ?L1 k a b] Final by auto
  then show ?case using WEST_reg_future Final by simp
next
  case (Global F F1 a b)
  let ?L1 = "WEST_reg_aux F1 k"
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>" using Global
    by (metis convert_nnf.simps(7) convert_nnf_convert_nnf mltl.inject(6))
  then have L1_nv: "WEST_regex_of_vars ?L1 k"
    using Global by simp
  have "WEST_regex_of_vars (WEST_global ?L1 a b k) k"
    using L1_nv WEST_global_num_vars[of ?L1 k a b] Global by simp
  then show ?case using WEST_reg_aux.simps(8)[of a b F1 k] Global(1) by simp
next
  case (Until F F1 F2 a b)
  have nnf_F1: "\<exists>\<psi>. F1 = convert_nnf \<psi>" using Until
    by (metis convert_nnf.simps(8) convert_nnf_convert_nnf mltl.inject(7))
  then have F1_k: "WEST_regex_of_vars (WEST_reg_aux F1 k) k"
    using Until by auto
  have nnf_F2: "\<exists>\<psi>. F2 = convert_nnf \<psi>" using Until
    by (metis convert_nnf.simps(8) convert_nnf_convert_nnf mltl.inject(7))
  then have F2_k: "WEST_regex_of_vars (WEST_reg_aux F2 k) k"
    using Until by auto
  let ?L1 = "(WEST_reg_aux F1 k)"
  let ?L2 = "(WEST_reg_aux F2 k)"
  have L1_nv:"WEST_regex_of_vars ?L1 k"
    using Until nnf_F1 by simp
  have L2_nv:"WEST_regex_of_vars ?L2 k"
    using Until nnf_F2 by simp

  have "WEST_regex_of_vars (WEST_until (WEST_reg_aux F1 k) (WEST_reg_aux F2 k) a b k) k"
    using WEST_until_num_vars[of ?L1 k ?L2 a b, OF L1_nv L2_nv] Until by auto
  then show ?case using Until(1) WEST_reg_aux.simps(9)[of F1 a b F2 k] by auto
next
  case (Release F F1 F2 a b)
  have nnf_F1: "\<exists>\<psi>. F1 = convert_nnf \<psi>" using Release
    by (metis convert_nnf.simps(9) convert_nnf_convert_nnf mltl.inject(8))

  then have F1_k: "WEST_regex_of_vars (WEST_reg_aux F1 k) k"
    using Release by auto
  have nnf_F2: "\<exists>\<psi>. F2 = convert_nnf \<psi>" using Release
    by (metis convert_nnf.simps(9) convert_nnf_convert_nnf mltl.inject(8))
  then have F2_k: "WEST_regex_of_vars (WEST_reg_aux F2 k) k"
    using Release by auto
  let ?L1 = "(WEST_reg_aux F1 k)"
  let ?L2 = "(WEST_reg_aux F2 k)"
  have L1_nv:"WEST_regex_of_vars ?L1 k"
    using Release nnf_F1 by simp
  have L2_nv:"WEST_regex_of_vars ?L2 k"
    using Release nnf_F2 by simp

  have "WEST_regex_of_vars (WEST_release (WEST_reg_aux F1 k) (WEST_reg_aux F2 k) a b k) k"
    using WEST_release_num_vars[of ?L1 k ?L2 a b, OF L1_nv L2_nv] Release by auto
  then show ?case using WEST_reg_aux.simps(10)[of F1 a b F2 k] Release by argo
qed

lemma nnf_intervals_welldef:
  assumes "intervals_welldef F1"
  shows "intervals_welldef (convert_nnf F1)"
  using assms
proof (induct "depth_mltl F1" arbitrary: F1 rule: less_induct)
  case less
  have iwd: "intervals_welldef F2 \<Longrightarrow>
          F1 = Not_mltl F2 \<Longrightarrow>
          intervals_welldef (convert_nnf (Not_mltl F2))"
    for F2 apply (cases F2) using less by simp_all
  then show ?case using less
    apply (cases F1) by simp_all
qed

lemma WEST_reg_num_vars:
  assumes "intervals_welldef F1"
  shows "WEST_regex_of_vars (WEST_reg F1) (WEST_num_vars F1)"
proof -
  have " WEST_num_vars (convert_nnf F1) = WEST_num_vars F1"
    using WEST_num_vars_nnf by presburger
  then have wnv: "WEST_num_vars (convert_nnf F1) \<le> (WEST_num_vars F1)"
     by simp
  have iwd: " intervals_welldef (convert_nnf F1)"
    using assms nnf_intervals_welldef
    by auto
  show ?thesis
    using assms WEST_reg_aux_num_vars[OF _ wnv iwd]
    unfolding WEST_reg.simps
    by auto
qed

subsection \<open>Correctness of WEST-simp\<close>

subsubsection "WEST-count-diff facts"

lemma count_diff_property_aux:
  assumes "k < length r1 \<and> k < length r2"
  shows "count_diff r1 r2 \<ge> count_diff_state (r1 ! k) (r2 ! k)"
  using assms
proof (induct "length r1" arbitrary: r1 r2 k)
  case 0
  then show ?case by simp
next
  case (Suc x)
  obtain h1 t1 h2 t2 where r1r2: "r1 = h1#t1" "r2 = h2#t2"
    using Suc
    by (metis length_0_conv not_less_zero trim_reversed_regex.cases)
  have cd: "count_diff r1 r2 = count_diff_state h1 h2 + count_diff t1 t2"
      using r1r2 count_diff.simps(4)[of h1 t1 h2 t2] by simp
  {assume *: "k = 0"
    have "count_diff r1 r2 \<ge> count_diff_state h1 h2"
      using cd
      by auto
    then have ?case using * r1r2
      by auto
  } moreover {assume *: "k > 0"
    have t1t2: "t1 ! (k-1) = r1 ! k \<and> t2 ! (k-1) = r2 ! k"
      using Suc(3) * r1r2
      by simp
     have "count_diff_state (t1 ! (k - 1)) (t2 ! (k - 1))
    \<le> count_diff t1 t2"
      using * Suc(1)[of t1 "k-1" t2]
      Suc(2-3) r1r2
      by (metis One_nat_def Suc_less_eq Suc_pred diff_Suc_1' length_Cons)
    then have ?case using cd t1t2
      by auto
  }
  ultimately show ?case by blast
qed

lemma count_diff_state_property:
   assumes "count_diff_state t1 t2 = 0"
   assumes "ka < length t1 \<and> ka < length t2"
   shows "t1 ! ka = t2 ! ka"
  using assms
  proof (induct "length t1" arbitrary: t1 t2 ka)
    case 0
    then show ?case by simp
  next
    case (Suc x)
    obtain h1 T1 h2 T2 where t1t2: "t1 = h1#T1" "t2 = h2#T2"
    using Suc
    by (metis count_nonS_trace.cases length_0_conv less_nat_zero_code)
  have cd: "h1 = h2 \<and> count_diff_state t1 t2 = count_diff_state T1 T2"
    using t1t2 count_diff_state.simps(4)[of h1 T1 h2 T2]
    Suc(3) by presburger
  then have ind0: "count_diff_state T1 T2 = 0"
    using Suc(3) by auto
  {assume *: "ka = 0"
    then have ?case using cd t1t2
      by auto
  } moreover {assume *: "ka > 0"
    have T1T2: "T1 ! (ka-1) = t1 ! ka \<and> T2 ! (ka-1) = t2 ! ka"
      using Suc(3) * t1t2
      by simp
     have "T1 ! (ka-1) = T2 ! (ka-1)"
      using * Suc(1)[OF _ ind0, of ka]
      Suc(2-3) t1t2
      by (metis Suc.hyps(1) Suc.prems(2) Suc_less_eq Suc_pred diff_Suc_1 ind0 length_Cons)
    then have ?case using T1T2
      by auto
  }
  ultimately show ?case by blast
qed

lemma count_diff_property:
  assumes "count_diff r1 r2 = 0"
  assumes "k < length r1 \<and> k < length r2"
  assumes "ka < length (r1 ! k) \<and> ka < length (r2 ! k)"
  shows "r2 ! k ! ka = r1 ! k ! ka"
proof -
  have "count_diff r1 r2 \<ge> count_diff_state (r1 ! k) (r2 ! k)"
    using count_diff_property_aux[OF assms(2)]
    by auto
  then have cdt: "count_diff_state (r1 ! k) (r2 ! k) = 0"
    using assms by auto
  show ?thesis
    using count_diff_state_property[OF cdt assms(3)]
    by auto
qed

lemma count_nonS_trace_0_allS:
  assumes "length h = num_vars"
  assumes "count_nonS_trace h = 0"
  shows "h = map (\<lambda>t. S) [0..<num_vars]"
  using assms
proof(induct num_vars arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc num_vars)
  then obtain head tail where head_tail: "h = head#tail"
      by (meson length_Suc_conv)
    have "tail = map (\<lambda>t. S) [0..<num_vars]"
      using Suc(1)[of tail] head_tail Suc.prems
      by (metis Zero_not_Suc count_nonS_trace.simps(2) length_Cons nat.inject plus_1_eq_Suc)
    then have "count_nonS_trace tail = 0"
      using count_nonS_trace.simps Suc.prems(2)
      by (metis Suc.prems(2) add_is_0 head_tail)
    then show ?case
      using count_nonS_trace.simps(2)[of head tail] head_tail
    proof -
      have f1: "0 = Suc 0 + 0 \<or> head = S"
        using One_nat_def Suc.prems(2) \<open>count_nonS_trace (head # tail) = (if head \<noteq> S then 1 + count_nonS_trace tail else count_nonS_trace tail)\<close> \<open>count_nonS_trace tail = 0\<close> head_tail by argo
      have "map (\<lambda>n. S) [0..<Suc num_vars] = S # map (\<lambda>n. S) [0..<num_vars]"
        using map_upt_Suc by blast
      then show ?thesis
        using f1 \<open>tail = map (\<lambda>t. S) [0..<num_vars]\<close> head_tail by presburger
    qed
qed

lemma trace_tail_num_vars:
  assumes "trace_regex_of_vars (h # trace) num_vars"
  shows "trace_regex_of_vars trace num_vars"
proof-
  have "\<And>i. i<length trace \<Longrightarrow> length (trace ! i) = num_vars"
  proof-
    fix i
    assume i_le: "i<length trace"
    have "i+1 < length (h#trace)"
      using Cons
      by (meson i_le impossible_Cons leI le_trans less_iff_succ_less_eq)
    then have "length ((h # trace) ! (i+1)) = num_vars"
      using assms unfolding trace_regex_of_vars_def by meson
    then show "length (trace ! i) = num_vars"
      by auto
  qed
  then show ?thesis
    unfolding trace_regex_of_vars_def by auto
qed

lemma count_diff_property_S_aux:
  assumes "count_diff trace [] = 0"
  assumes "k < length trace"
  assumes "trace_regex_of_vars trace num_vars"
  assumes "1 \<le> num_vars"
  shows "trace ! k = map (\<lambda>t. S) [0 ..< num_vars]"
  using assms
proof(induct trace arbitrary: k num_vars)
  case Nil
  then show ?case by simp
next
  case (Cons h trace)
  {assume k_zero: "k = 0"
    have cond1: "length h = num_vars"
      using Cons.prems(3) unfolding trace_regex_of_vars_def
      by (metis Cons.prems(2) k_zero nth_Cons_0)
    have cond2: "count_nonS_trace h = 0"
      using Cons.prems(1) count_diff.simps
      by (metis add_is_0 count_diff_state.simps(3) count_nonS_trace.elims)
    have "h = map (\<lambda>t. S) [0..<num_vars]"
      using count_nonS_trace_0_allS[OF cond1 cond2] by simp
    then have ?case
      by (simp add: k_zero)
  } moreover {
    assume k_ge_zero: "k > 0"
    have cond1: "count_diff trace [] = 0"
      by (metis Cons.prems(1) count_diff.simps(2) count_diff.simps(3) neq_Nil_conv zero_eq_add_iff_both_eq_0)
    have cond2: "k-1 < length trace"
      using k_ge_zero Cons.prems(2) by auto
    have cond3: "trace_regex_of_vars trace num_vars"
      using trace_tail_num_vars Cons(4)
      unfolding trace_regex_of_vars_def
      by blast
    have "trace ! (k-1) = map (\<lambda>t. S) [0 ..< num_vars]"
      using Cons.hyps[OF cond1 cond2 cond3] Cons.prems by blast
    then have ?case
      using k_ge_zero by simp
  }
  ultimately show ?case by blast
qed

lemma count_diff_property_S:
  assumes "count_diff r1 r2 = 0"
  assumes "k < length r1 \<and> length r2 \<le> k"
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "num_vars \<ge> 1"
  assumes "ka < num_vars"
  shows "r1 ! k = map (\<lambda>t. S) [0..<num_vars]"
proof-
  have "length r1 > length r2"
    using assms by simp
  let ?tail = "drop (length r2) r1"
  have cond1: "count_diff ?tail [] = 0"
    using assms(1, 2)
  proof(induct r2 arbitrary: r1 k)
    case Nil
    then show ?case by simp
  next
    case (Cons a r2)
    then obtain h T where obt_hT: "r1 = h#T"
      by (metis length_0_conv less_nat_zero_code trim_reversed_regex.cases)
    have "count_diff_state h a = 0"
      using count_diff.simps(4)[of h T a r2] Cons.prems obt_hT by simp
    then have cond1: "count_diff T r2 = 0"
      using count_diff.simps(4)[of h T a r2] Cons.prems obt_hT by simp
    have "count_diff (drop (length r2) T) [] = 0"
      using Cons.hyps[OF cond1] Cons.prems obt_hT
      by (metis count_diff.simps(1) drop_all linorder_le_less_linear order_refl)
    then show ?case
      using obt_hT by simp
  qed
  have cond2: "(k - length r2) < length (drop (length r2) r1)"
    using assms by auto
  have cond3: "trace_regex_of_vars (drop (length r2) r1) num_vars"
    using assms(3, 2) unfolding trace_regex_of_vars_def
    by (metis \<open>length r2 < length r1\<close> add.commute leI length_drop less_diff_conv nth_drop order.asym)
  have "?tail ! (k - length r2) = map (\<lambda>t. S) [0 ..< num_vars]"
    using count_diff_property_S_aux[OF cond1 cond2 cond3] assms by blast
  then show ?thesis
    using assms by auto
qed


lemma count_diff_state_commutative:
  shows "count_diff_state e1 e2 = count_diff_state e2 e1"
  proof (induct e1 arbitrary: e2)
    case Nil
    then show ?case using count_diff_state.simps
      by (metis count_nonS_trace.cases)
  next
    case (Cons h1 t1)
    then show ?case
      by (smt (verit) count_diff_state.elims list.inject null_rec(1) null_rec(2))
  qed

lemma count_diff_commutative:
  shows "count_diff r1 r2 = count_diff r2 r1"
proof (induct r1 arbitrary: r2)
  case Nil
  then show ?case using count_diff.simps
    by (metis trim_reversed_regex.cases)
next
  case (Cons h1 t1)
  {assume *: "r2 = []"
    then have ?case
      using count_diff.simps by auto
  } moreover {
    assume *: "r2 \<noteq> [] "
    then obtain h2 t2 where "r2 = h2#t2"
      by (meson neq_Nil_conv)
    then have ?case using count_diff.simps(4)[of h1 t1 h2 t2]
      Cons[of t2] * count_diff_state_commutative
      by auto
  }
  ultimately show ?case by blast
qed


lemma count_diff_same_trace:
  shows "count_diff trace trace = 0"
proof(induct trace)
  case Nil
  then show ?case by simp
next
  case (Cons a trace)
  have "count_diff_state a a = 0"
  proof(induct a)
    case Nil
    then show ?case by simp
  next
    case (Cons a1 a2)
    then show ?case by simp
  qed
  then show ?case
    using Cons count_diff.simps(4)[of a trace a trace] by auto
qed

lemma count_diff_state_0:
  assumes "count_diff_state h1 h2 = 0"
  assumes "length h1 = length h2"
  shows "h1 = h2"
  using assms
proof(induct h1 arbitrary: h2)
  case Nil
  then show ?case by simp
next
  case (Cons a h1)
  then show ?case
    by (metis count_diff_state_property nth_equalityI)
qed


lemma count_diff_state_1:
  assumes "length h1 = length h2"
  assumes "count_diff_state h1 h2 = 1"
  shows "\<exists>ka<length h1. h1!ka \<noteq> h2!ka"
  using assms
proof(induct h1 arbitrary: h2)
  case Nil
  then show ?case by simp
next
  case (Cons a h1)
  then obtain head tail where obt_headtail: "h2 = head#tail"
    by (metis length_0_conv neq_Nil_conv)
  {assume head_equal: "a = head"
    then have "count_diff_state h1 tail = 1"
      using count_diff_state.simps(4)[of a h1 head tail]
      using Cons.prems(2) obt_headtail by auto
    then have "\<exists>ka<length h1. h1 ! ka \<noteq> tail ! ka"
      using Cons.hyps[of tail] Cons.prems
      by (simp add: obt_headtail)
    then have ?case using obt_headtail by auto
  } moreover {
    assume head_notequal: "a \<noteq> head"
    then have ?case using obt_headtail by auto
  }
  ultimately show ?case by blast
qed

lemma count_diff_state_other_states:
  assumes "count_diff_state h1 h2 = 1"
  assumes "length h1 = length h2"
  assumes "h1!k \<noteq> h2!k"
  assumes "k < length h1"
  shows "\<forall>i<length h1. k\<noteq>i \<longrightarrow> h1!i = h2!i"
  using assms
proof(induct h1 arbitrary: h2 k)
  case Nil
  then show ?case by simp
next
  case (Cons a h1)
  then obtain head tail where headtail: "h2 = head#tail"
    by (metis Suc_length_conv)
  {assume k0: "k = 0"
    then have "count_diff_state h1 tail = 0"
      using Cons.prems headtail count_diff_state.simps(4)[of a h1 head tail] by auto
    then have "h1 = tail"
      using count_diff_state_0 Cons.prems headtail by simp
    then have ?case using k0 headtail by simp
  } moreover {
    assume k_not0: "k \<noteq> 0"
    then have head_eq: "a = head"
      using Cons headtail count_diff_state.simps(4)[of a h1 head tail]
      by (metis One_nat_def Suc_inject count_diff_state_0 length_Cons nth_Cons' plus_1_eq_Suc)
    then have "count_diff_state h1 tail = 1"
      using Cons headtail count_diff_state.simps(4)[of a h1 head tail] by argo
    then have induction: "\<forall>i<length h1. k-1 \<noteq> i \<longrightarrow> h1 ! i = tail ! i"
      using Cons.hyps[of h2 "k-1"] Cons.prems headtail
      by (smt (verit) Cons.hyps Suc_less_eq add_diff_inverse_nat k_not0 length_Cons less_one nth_Cons' old.nat.inject plus_1_eq_Suc)
    have "\<And>i. (i<length (a # h1) \<and> k \<noteq> i) \<Longrightarrow> (a # h1) ! i = h2 ! i"
    proof-
      fix i
      assume i_facts: "(i<length (a # h1) \<and> k \<noteq> i)"
      {assume i0: "i = 0"
        then have "(a # h1) ! i = h2 ! i"
          using headtail head_eq by simp
      } moreover {
        assume i_not0: "i \<noteq> 0"
        then have "(a # h1) ! i = h2 ! i"
          using induction k_not0 i_facts
          using headtail length_Cons nth_Cons' zero_less_diff by auto
      }
      ultimately show "(a # h1) ! i = h2 ! i" by blast
    qed
    then have ?case by blast
  }
  ultimately show ?case by blast
qed

lemma count_diff_same_len:
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  assumes "count_diff r1 r2 = 0"
  assumes "length r1 = length r2"
  shows "r1 = r2"
  using assms
proof(induct r1 arbitrary: r2)
  case Nil
  then show ?case by simp
next
  case (Cons h1 r1)
  then obtain h T where obt_hT: "r2 = h#T"
    by (metis length_0_conv list.exhaust)
  have cond1: "trace_regex_of_vars r1 num_vars"
    using trace_tail_num_vars Cons.prems by blast
  have cond2: "trace_regex_of_vars T num_vars"
    using trace_tail_num_vars Cons.prems obt_hT by blast
  have h1_h_samelen: "length h1 = length h"
    using Cons.prems obt_hT unfolding trace_regex_of_vars_def
    by (metis length_greater_0_conv nth_Cons_0)
  have r1_eq_T: "r1 = T"
    using Cons.hyps[OF cond1 cond2] Cons.prems
    by (simp add: obt_hT)
  then have "count_diff r1 T = 0"
    using count_diff_same_trace by auto
  then have "count_diff_state h1 h = 0"
    using Cons.prems(3) obt_hT count_diff.simps(4)[of h1 r1 h T] by simp
  then have "h = h1" using h1_h_samelen
  proof(induct h arbitrary: h1)
    case Nil
    then show ?case by simp
  next
    case (Cons a h)
    then show ?case using count_diff_state.simps
       Suc_inject count_diff_state.elims  length_Cons less_iff_Suc_add not_less_eq
      by (metis (no_types, opaque_lifting) count_diff_state_0)
    qed
  then show ?case
    using r1_eq_T obt_hT by blast
qed

lemma count_diff_1:
  assumes "count_diff r1 r2 = 1"
  assumes "length r1 = length r2"
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  shows "\<exists>k<length r1. count_diff_state (r1!k) (r2!k) = 1"
  using assms
proof(induct "length r1" arbitrary: r1 r2)
  case 0
  then show ?case by auto
next
  case (Suc x)
  obtain h1 T1 where obt_h1T1: "r1 = h1#T1" using Suc
    by (metis length_Suc_conv)
  obtain h2 T2 where obt_h2T2: "r2 = h2#T2" using Suc
    by (metis length_Suc_conv)
  {assume h1h2_same: "h1 = h2"
    have "count_diff_state h1 h2 = 0"
      using h1h2_same count_diff_state_0
      by (metis Nat.add_0_right count_diff.simps(4) count_diff_same_trace)
    then have cond2: "count_diff T1 T2 = 1"
      using h1h2_same Suc.prems(1) obt_h1T1 obt_h2T2
      using count_diff.simps(4)[of h1 T1 h2 T2] by simp
    have "\<exists>k<length T1. count_diff_state (T1 ! k) (T2 ! k) = 1"
      using Suc obt_h1T1 obt_h2T2 h1h2_same
      by (metis cond2 length_Cons nat.inject trace_tail_num_vars)
    then have ?case using obt_h1T1 obt_h2T2
      by fastforce
  } moreover {
    assume h1h2_notsame: "h1 \<noteq> h2"
    have h1h2_nv: "length h1 = length h2"
      using Suc.prems(3, 4) unfolding trace_regex_of_vars_def
      by (metis Suc.hyps(2) Suc.prems(2) nth_Cons_0 obt_h1T1 obt_h2T2 zero_less_Suc)
    then have "count_diff_state h1 h2 > 0"
      using count_diff_state_0 h1h2_notsame by auto
    then have "count_diff_state h1 h2 = 1"
      using count_diff.simps(4)[of h1 T1 h2 T2] Suc obt_h1T1 obt_h2T2 by auto
    then have ?case using obt_h1T1 obt_h2T2 by auto
  }
  ultimately show ?case by blast
qed


lemma count_diff_1_other_states:
  assumes "count_diff r1 r2 = 1"
  assumes "length r1 = length r2"
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  assumes "count_diff_state (r1!k) (r2!k) = 1"
  shows "\<forall>i<length r1. k\<noteq>i \<longrightarrow> r1!i = r2!i"
  using assms
proof(induct "length r1" arbitrary: r1 r2 k)
  case 0
  then show ?case by auto
next
  case (Suc x)
  obtain h1 T1 where obt_h1T1: "r1 = h1#T1" using Suc
    by (metis length_Suc_conv)
  obtain h2 T2 where obt_h2T2: "r2 = h2#T2" using Suc
    by (metis length_Suc_conv)
  {assume k0: "k = 0"
    have "count_diff T1 T2 = 0"
      using Suc count_diff.simps(4)[of h1 T1 h2 T2] obt_h1T1 obt_h2T2 k0
      by auto
    then have "\<forall>i<length T1. T1 ! i = T2 ! i"
      using Suc.prems count_diff_same_len trace_tail_num_vars
      by (metis Suc_inject length_Cons obt_h1T1 obt_h2T2)
    then have ?case using obt_h1T1 obt_h2T2 k0
      using length_Cons by auto
  } moreover {
    assume k_not0: "k \<noteq> 0"
    then have T1T2_diffby1: "count_diff T1 T2 = 1"
      using Suc.prems obt_h1T1 obt_h2T2 count_diff.simps(4)[of h1 T1 h2 T2]
      by (metis One_nat_def add_right_imp_eq count_diff_same_len count_diff_state_1 list.size(4) not_gr_zero nth_Cons_pos one_is_add trace_tail_num_vars)
    then have h1h2_same: "h1 = h2"
      using k_not0 count_diff.simps(4)[of h1 T1 h2 T2] Suc.prems obt_h1T1 obt_h2T2
      unfolding trace_regex_of_vars_def
      by (metis Suc.hyps(2) add_cancel_right_left count_diff_state_0 nth_Cons_0 zero_less_Suc)
    have induction: "\<forall>i<length T1. (k-1) \<noteq> i \<longrightarrow> T1 ! i = T2 ! i"
      using Suc.hyps(1)[of T1 T2 "k-1"] Suc.hyps(2) Suc.prems T1T2_diffby1
      by (metis (mono_tags, lifting) k_not0 length_Cons nth_Cons' obt_h1T1 obt_h2T2 old.nat.inject trace_tail_num_vars)
    then have ?case using obt_h1T1 obt_h2T2 k_not0 h1h2_same
      by (simp add: nth_Cons')
  }
  ultimately show ?case by blast
qed

subsubsection "Orsimp-trace Facts"

lemma WEST_simp_bitwise_identity:
  assumes "b1 = b2"
  shows "WEST_simp_bitwise b1 b2 = b1"
  using assms WEST_simp_bitwise.simps
  by (metis WEST_bit.exhaust)

lemma WEST_simp_bitwise_commutative:
  shows "WEST_simp_bitwise b1 b2 = WEST_simp_bitwise b2 b1"
  using WEST_simp_bitwise.simps
  by (metis (full_types) WEST_simp_bitwise.elims)


lemma WEST_simp_state_commutative:
  assumes "length s1 = num_vars"
  assumes "length s2 = num_vars"
  shows "WEST_simp_state s1 s2 = WEST_simp_state s2 s1"
  using WEST_simp_state.simps[of s1 s2]
  using WEST_simp_bitwise_commutative assms by simp

lemma WEST_simp_trace_commutative:
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  shows "WEST_simp_trace r1 r2 num_vars = WEST_simp_trace r2 r1 num_vars"
proof-
  have r1_vars: "\<forall>k. length (WEST_get_state r1 k num_vars) = num_vars"
    using assms WEST_get_state_length by blast
  have r2_vars: "\<forall>k. length (WEST_get_state r2 k num_vars) = num_vars"
    using assms WEST_get_state_length by blast
  have "(\<lambda>k. WEST_simp_state (WEST_get_state r1 k num_vars)
               (WEST_get_state r2 k num_vars)) = (\<lambda>k. WEST_simp_state (WEST_get_state r2 k num_vars)
               (WEST_get_state r1 k num_vars))"
    using WEST_simp_state_commutative r1_vars r2_vars by fast
  then show ?thesis
    unfolding WEST_simp_trace.simps[of r1 r2 num_vars]
    unfolding WEST_simp_trace.simps[of r2 r1 num_vars]
    by (simp add: insert_commute)
qed


lemma WEST_simp_trace_identity:
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  assumes "count_diff r1 r2 = 0"
  assumes "length r1 \<ge> length r2"
  shows "WEST_simp_trace r1 r2 num_vars = r1"
proof-
  have of_vars: "\<forall>i<length r1. length (r1 ! i) = num_vars"
    using assms unfolding trace_regex_of_vars_def by argo
  have mapmap: "map (\<lambda>k. map (\<lambda>ka. (r1!k)!ka)
               [0..< num_vars]) [0..<length r1]  = r1"
    using assms(1) unfolding trace_regex_of_vars_def[of r1 num_vars]
    by (smt (verit) length_map list_eq_iff_nth_eq map_nth nth_map)

  have r1_k_ka: "\<And>ka. ka < num_vars \<Longrightarrow>
        WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                            (WEST_get_state r2 k num_vars ! ka) = r1!k!ka"
    if k_lt: "k<length r1" for k
  proof -
    fix ka
    assume ka_lt: "ka < num_vars"
    {assume *: "k < length r2"
      have "length (r1 ! k) = num_vars \<and> length (r2 ! k) = num_vars"
        using assms unfolding trace_regex_of_vars_def * ka_lt
        using "*" that by presburger
      then have "(r2 ! k) ! ka = (r1 ! k) ! ka"
        using * ka_lt using assms(3)
        using count_diff_property_aux
        using count_diff_property that by presburger
      then have "WEST_get_state r2 k num_vars ! ka = WEST_get_state r1 k num_vars ! ka"
        unfolding WEST_get_state.simps using * ka_lt
        using leD that by auto
      then have "WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                            (WEST_get_state r2 k num_vars ! ka) = r1!k!ka"
        using WEST_simp_bitwise_identity that by force
    } moreover {assume *: "k \<ge> length r2"
      then have "WEST_get_state r2 k num_vars = (map (\<lambda> k. S) [0 ..< num_vars])"
        by simp
      then have r2_k_ka_S: "(WEST_get_state r2 k num_vars ! ka) = S"
        using ka_lt by simp

      have r1_k_ka: "(WEST_get_state r1 k num_vars ! ka) = r1!k!ka"
        using k_lt by simp
      have "(r1!k!ka) = S"
        using count_diff_property_S
        using * ka_lt assms(1, 3, 4)
        using that
        by simp
      then have "WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                            S = r1!k!ka"
        using r1_k_ka by simp
      then have "WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                            (WEST_get_state r2 k num_vars ! ka) = r1!k!ka"
        using r2_k_ka_S by simp
    }
    ultimately show "WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                            (WEST_get_state r2 k num_vars ! ka) = r1!k!ka" by auto
  qed
  have len_lhs: "length (map (\<lambda>k. (f k)
               [0..< num_vars])
     [0..<length r1]) = length r1" for f :: "nat \<Rightarrow> nat list \<Rightarrow> WEST_bit list"
    by auto
 have aux_helper: "\<And>i. i < length r1 \<Longrightarrow> (map (\<lambda>k. (f k)
               [0..< num_vars])
     [0..<length r1])! i= r1 ! i"  if f_prop: "\<forall>k<length r1. (f k)
               [0..< num_vars] = r1!k" for f
   proof -
     fix i
     assume " i < length r1"
     show "map (\<lambda>k. f k [0..<num_vars]) [0..<length r1] ! i = r1 ! i"
      using f_prop
      by (simp add: \<open>i < length r1\<close>)
  qed
  have map_prop: "map (\<lambda>k. (f k)
                 [0..< num_vars])
       [0..<length r1] = r1"  if f_prop: "\<forall>k<length r1. (f k)
                 [0..< num_vars] = r1!k" for f
      using len_lhs[of f] aux_helper[of f] f_prop
      by (metis nth_equalityI)

  let ?f = "\<lambda>i. map (\<lambda>ka. WEST_simp_bitwise (WEST_get_state r1 i num_vars ! ka)
                         (WEST_get_state r2 i num_vars ! ka))"

  have "\<forall>k<length r1. map (\<lambda>ka. WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                         (WEST_get_state r2 k num_vars ! ka))
               [0..< num_vars] = r1!k"
    using r1_k_ka
    by (smt (z3) length_map length_upt minus_nat.diff_0 nth_equalityI nth_map_upt of_vars plus_nat.add_0)

  then have "\<forall>k<length r1. (?f k)
               [0..< num_vars] = r1!k"
    by blast
  then have "map (\<lambda>k. (?f k)
               [0..< num_vars])
     [0..<length r1] = r1"
    using map_prop[of ?f]
    by blast
  then have "map (\<lambda>k. map (\<lambda>ka. WEST_simp_bitwise (WEST_get_state r1 k num_vars ! ka)
                         (WEST_get_state r2 k num_vars ! ka))
               [0..< num_vars])
     [0..<length r1] = r1"
    using of_vars
    by blast
  then show ?thesis
    unfolding WEST_simp_trace.simps WEST_simp_state.simps
    using WEST_simp_bitwise_identity assms WEST_get_state_length
    by simp
qed

lemma WEST_simp_trace_length:
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  assumes "length r1 = length r2"
  shows "length (WEST_simp_trace r1 r2 num_vars) = length r1"
  using assms by simp


subsubsection \<open> WEST-orsimp-trace-correct \<close>

lemma WEST_simp_trace_correct_forward:
  assumes "check_simp r1 r2"
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  assumes "match_regex \<pi> (WEST_simp_trace r1 r2 num_vars)"
  shows "match_regex \<pi> r1 \<or> match_regex \<pi> r2"
proof-
  {assume diff0: "count_diff r1 r2 = 0"
    then have *: "(WEST_simp_trace r1 r2 num_vars) = r1"
      using WEST_simp_trace_identity assms diff0 by fastforce
    have "r1 = r2"
      using count_diff_same_len assms diff0 by force
    then have ?thesis using assms * by simp
  } moreover {
    assume diff1: "count_diff r1 r2 = 1"
    then obtain k where obt_k: "k < length r1 \<and> count_diff_state (r1!k) (r2!k) = 1"
      using count_diff_1[of r1 r2 num_vars] assms by fastforce
    then have "length (r1 ! k) = length (r2 ! k)"
      using assms unfolding trace_regex_of_vars_def
      by (metis check_simp.simps)
    then obtain ka where obt_ka: "ka < length (r1!k) \<and> (r1!k!ka) \<noteq> (r2!k!ka)"
      using count_diff_state_1[of "r1!k" "r2!k"] obt_k assms by blast

    let ?r1r2 = "(WEST_simp_trace r1 r2 num_vars)"
    have rest_of_states: "\<forall>i<length r1. i\<noteq>k \<longrightarrow> r1!i = r2!i"
      using count_diff_1_other_states assms obt_k
      by (metis (no_types, opaque_lifting) check_simp.elims(2) diff1)
    have fact1: "\<And>i. (i<length r1 \<and> i\<noteq>k) \<Longrightarrow>
                 ((match_timestep (\<pi>!i) (r1!i)) \<or> (match_timestep (\<pi>!i) (r2!i)))"
    proof-
      fix i
      assume i_assms: "i<length r1 \<and> i\<noteq>k"
      then have states_eq: "r1!i = r2!i" using rest_of_states by blast
      have "?r1r2 = map (\<lambda>k. WEST_simp_state (WEST_get_state r1 k num_vars)
               (WEST_get_state r2 k num_vars)) [0..<length r1]"
        using assms(1) unfolding check_simp.simps WEST_simp_trace.simps
        by (metis (mono_tags, lifting) Max_singleton insert_absorb2)
      then have "?r1r2!i = WEST_simp_state (WEST_get_state r1 i num_vars)
               (WEST_get_state r2 i num_vars)"
        using i_assms by simp
      then have "?r1r2!i = WEST_simp_state (r1!i) (r2!i)"
        using WEST_get_state.simps i_assms
        by (metis assms(1) check_simp.elims(2) leD)
      then have "?r1r2!i = r1!i"
        using WEST_simp_state.simps states_eq
        using WEST_simp_bitwise.simps
        using WEST_simp_bitwise_identity map_nth by fastforce
      then show "((match_timestep (\<pi>!i) (r1!i)) \<or> (match_timestep (\<pi>!i) (r2!i)))"
        using assms states_eq unfolding match_regex_def
        by (metis WEST_simp_trace_length check_simp.elims(2) i_assms)
    qed
    have "?r1r2!k = WEST_simp_state (WEST_get_state r1 k num_vars)
             (WEST_get_state r2 k num_vars)"
        using WEST_simp_trace.simps[of r1 r2 num_vars] obt_k by force
    then have r1r2_k: "?r1r2!k = WEST_simp_state (r1!k) (r2!k)"
      using obt_k assms by auto
    then have other_states: "\<forall>i<length (r1!k). i\<noteq>ka \<longrightarrow> (r1!k!i) = (r2!k!i)"
      using count_diff_state_other_states[of "r1!k" "r2!k" ka]
      using obt_ka obt_k assms fact1
      using \<open>length (r1 ! k) = length (r2 ! k)\<close> by blast
    have "?r1r2!k = WEST_simp_state (WEST_get_state r1 k num_vars)
             (WEST_get_state r2 k num_vars)"
        using WEST_simp_trace.simps[of r1 r2 num_vars] obt_k by force
    then have r1r2_k: "?r1r2!k = WEST_simp_state (r1!k) (r2!k)"
      using obt_k assms by auto
    then have other_states: "\<forall>i<length (r1!k). i\<noteq>ka \<longrightarrow> (r1!k!i) = (r2!k!i)"
      using count_diff_state_other_states[of "r1!k" "r2!k" ka]
      using obt_ka obt_k assms fact1
      using \<open>length (r1 ! k) = length (r2 ! k)\<close> by blast
    have state_fact1: "\<And>i. (i<length (r1!k) \<and> i\<noteq>ka) \<Longrightarrow> (?r1r2!k!i) = (r1!k!i)"
    proof-
      fix i
      assume i_fact: "i<length (r1!k) \<and> i\<noteq>ka"
      have "length (r1 ! k) = length (r2 ! k)"
        using assms obt_k unfolding trace_regex_of_vars_def
        by (simp add: \<open>length (r1 ! k) = length (r2 ! k)\<close>)
      then show "(?r1r2!k!i) = (r1!k!i)"
        using WEST_simp_state.simps[of "r1!k" "r2!k"] i_fact r1r2_k
        by (simp add: WEST_simp_bitwise_identity \<open>length (r1 ! k) = length (r2 ! k)\<close> map_nth other_states)
    qed
    have r1r2_k_ka: "?r1r2!k!ka = WEST_simp_bitwise (r1 ! k ! ka) (r2 ! k ! ka)"
      using WEST_simp_state.simps[of "r1!k" "r2!k"] r1r2_k obt_ka by simp
    then have state_fact2: "?r1r2!k!ka = S"
      using obt_ka WEST_simp_bitwise.elims
      by (metis (full_types))
    then have cases: "(r1!k!ka = S) \<or> (r2!k!ka = S)
              \<or>(r1!k!ka = One \<and> r2!k!ka = Zero)
              \<or>(r1!k!ka = Zero \<and> r2!k!ka = One)"
      using r1r2_k_ka
      by (metis (full_types) WEST_bit.exhaust obt_ka)
    have "\<And>x. x<length (?r1r2 ! k) \<Longrightarrow>
          (((r1 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (r1 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))
         \<or>((r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k)))"
      using state_fact1 state_fact2
    proof-
      fix x
      assume x_fact: "x < length (?r1r2!k)"
      {assume x_is_ka: "x = ka"
        then have "((?r1r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (?r1r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))"
          using state_fact2 by simp
      } moreover {
        assume x_not_ka: "x \<noteq> ka"
        then have "?r1r2!k!x = r1!k!x"
          using state_fact1[of x] x_fact x_not_ka
          using assms(3) check_simp.simps obt_k trace_regex_of_vars_def by fastforce
        then have "(((r1 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (r1 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))
         \<or>((r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k)))"
          using cases assms WEST_simp_trace_length check_simp.elims obt_k x_fact
          unfolding match_timestep_def
          by (metis (mono_tags, lifting) match_regex_def match_timestep_def)
      }
      ultimately show "(((r1 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (r1 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))
         \<or>((r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k)))"
        by (metis obt_ka)
    qed
    then have fact2: "((match_timestep (\<pi>!k) (r1!k)) \<or> (match_timestep (\<pi>!k) (r2!k)))"
      unfolding match_timestep_def
      by (metis WEST_simp_state_num_vars \<open>length (r1 ! k) = length (r2 ! k)\<close> other_states r1r2_k)

    have "\<forall>time<length ?r1r2. ((match_timestep (\<pi>!time) (r1!time)) \<or> (match_timestep (\<pi>!time) (r2!time)))"
      using fact1 fact2 assms
      by (metis WEST_simp_trace_length check_simp.elims(2))
    then have ?thesis
      using assms WEST_simp_trace_length unfolding match_regex_def
      by (smt (verit) check_simp.elims(2) rest_of_states)
  }
  ultimately show ?thesis
    using check_simp.simps[of r1 r2] assms(1) by force
qed


lemma WEST_simp_trace_correct_converse:
  assumes "check_simp r1 r2"
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  assumes "match_regex \<pi> r1 \<or> match_regex \<pi> r2"
  shows "match_regex \<pi> (WEST_simp_trace r1 r2 num_vars)"
proof-
  {assume diff0: "count_diff r1 r2 = 0"
    then have *: "(WEST_simp_trace r1 r2 num_vars) = r1"
      using WEST_simp_trace_identity assms diff0 by fastforce
    have "r1 = r2"
      using count_diff_same_len assms diff0 by force
    then have ?thesis using assms * by simp
  } moreover {
    assume diff1: "count_diff r1 r2 = 1"
    then obtain k where obt_k: "k < length r1 \<and> count_diff_state (r1!k) (r2!k) = 1"
      using count_diff_1[of r1 r2 num_vars] assms by fastforce
    then have "length (r1 ! k) = length (r2 ! k)"
      using assms unfolding trace_regex_of_vars_def
      by (metis check_simp.simps)
    then obtain ka where obt_ka: "ka < length (r1!k) \<and> (r1!k!ka) \<noteq> (r2!k!ka)"
      using count_diff_state_1[of "r1!k" "r2!k"] obt_k assms by blast
    let ?r1r2 = "(WEST_simp_trace r1 r2 num_vars)"
    have rest_of_states: "\<forall>i<length r1. i\<noteq>k \<longrightarrow> r1!i = r2!i"
      using count_diff_1_other_states assms obt_k
      by (metis (no_types, opaque_lifting) check_simp.elims(2) diff1)
    have fact1: "\<And>i. (i<length r1 \<and> i\<noteq>k) \<Longrightarrow> match_timestep (\<pi>!i) (?r1r2!i)"
    proof-
      fix i
      assume i_assms: "i<length r1 \<and> i\<noteq>k"
      then have states_eq: "r1!i = r2!i" using rest_of_states by blast
      have "?r1r2 = map (\<lambda>k. WEST_simp_state (WEST_get_state r1 k num_vars)
               (WEST_get_state r2 k num_vars)) [0..<length r1]"
        using assms(1) unfolding check_simp.simps WEST_simp_trace.simps
        by (metis (mono_tags, lifting) Max_singleton insert_absorb2)
      then have "?r1r2!i = WEST_simp_state (WEST_get_state r1 i num_vars)
               (WEST_get_state r2 i num_vars)"
        using i_assms by simp
      then have "?r1r2!i = WEST_simp_state (r1!i) (r2!i)"
        using WEST_get_state.simps i_assms
        by (metis assms(1) check_simp.elims(2) leD)
      then have "?r1r2!i = r1!i"
        using WEST_simp_state.simps states_eq
        using WEST_simp_bitwise.simps
        using WEST_simp_bitwise_identity map_nth by fastforce
      then show "match_timestep (\<pi>!i) (?r1r2!i)"
        using assms(4) states_eq unfolding match_regex_def
        by (metis assms(1) check_simp.elims(2) i_assms)
    qed
    have "?r1r2!k = WEST_simp_state (WEST_get_state r1 k num_vars)
             (WEST_get_state r2 k num_vars)"
        using WEST_simp_trace.simps[of r1 r2 num_vars] obt_k by force
    then have r1r2_k: "?r1r2!k = WEST_simp_state (r1!k) (r2!k)"
      using obt_k assms by auto
    then have other_states: "\<forall>i<length (r1!k). i\<noteq>ka \<longrightarrow> (r1!k!i) = (r2!k!i)"
      using count_diff_state_other_states[of "r1!k" "r2!k" ka]
      using obt_ka obt_k assms fact1
      using \<open>length (r1 ! k) = length (r2 ! k)\<close> by blast
    have state_fact1: "\<And>i. (i<length (r1!k) \<and> i\<noteq>ka) \<Longrightarrow> (?r1r2!k!i) = (r1!k!i)"
    proof-
      fix i
      assume i_fact: "i<length (r1!k) \<and> i\<noteq>ka"
      have "length (r1 ! k) = length (r2 ! k)"
        using assms obt_k unfolding trace_regex_of_vars_def
        by (simp add: \<open>length (r1 ! k) = length (r2 ! k)\<close>)
      then show "(?r1r2!k!i) = (r1!k!i)"
        using WEST_simp_state.simps[of "r1!k" "r2!k"] i_fact r1r2_k
        by (simp add: WEST_simp_bitwise_identity \<open>length (r1 ! k) = length (r2 ! k)\<close> map_nth other_states)
    qed
    have "?r1r2!k!ka = WEST_simp_bitwise (r1 ! k ! ka) (r2 ! k ! ka)"
      using WEST_simp_state.simps[of "r1!k" "r2!k"] r1r2_k obt_ka by simp
    then have state_fact2: "?r1r2!k!ka = S"
      using obt_ka WEST_simp_bitwise.elims
      by (metis (full_types))
    have match_state: "match_timestep (\<pi>!k) (r1!k) \<or> match_timestep (\<pi>!k) (r2!k)"
      using assms(4) obt_k unfolding match_regex_def
      by (metis assms(1) check_simp.elims(2))
    have "\<And>x. x<length (?r1r2 ! k) \<Longrightarrow>
          ((?r1r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (?r1r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))"
      using state_fact1 state_fact2 match_state
    proof-
      fix x
      assume x_fact: "x < length (?r1r2!k)"
      {assume x_is_ka: "x = ka"
        then have "((?r1r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (?r1r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))"
          using state_fact2 by simp
      } moreover {
        assume x_not_ka: "x \<noteq> ka"
        then have "?r1r2!k!x = r1!k!x"
          using state_fact1[of x] x_fact x_not_ka
          using assms(3) check_simp.simps obt_k trace_regex_of_vars_def by fastforce
        then have "((?r1r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (?r1r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))"
          using match_state unfolding match_timestep_def
          by (smt (verit, best) WEST_simp_trace_length WEST_simp_trace_num_vars \<open>\<forall>i<length (r1 ! k). i \<noteq> ka \<longrightarrow> r1 ! k ! i = r2 ! k ! i\<close> assms(1) assms(2) assms(3) check_simp.simps obt_k trace_regex_of_vars_def x_fact x_not_ka)
      }
      ultimately show "((?r1r2 ! k ! x = One \<longrightarrow> x \<in> \<pi> ! k) \<and> (?r1r2 ! k ! x = Zero \<longrightarrow> x \<notin> \<pi> ! k))"
        by blast
    qed
    then have fact2: "match_timestep (\<pi> ! k) (?r1r2 ! k)"
      unfolding match_timestep_def by argo
    have "\<forall>time<length ?r1r2. match_timestep (\<pi> ! time) (?r1r2 ! time)"
      using fact1 fact2 assms
      by (metis WEST_simp_trace_length check_simp.elims(2))
    then have ?thesis
      using assms WEST_simp_trace_length unfolding match_regex_def
      by (metis (no_types, lifting) check_simp.simps)
  }
  ultimately show ?thesis using check_simp.simps[of r1 r2] assms(1) by force
qed


lemma WEST_simp_trace_correct:
  assumes "check_simp r1 r2"
  assumes "trace_regex_of_vars r1 num_vars"
  assumes "trace_regex_of_vars r2 num_vars"
  shows "match_regex \<pi> (WEST_simp_trace r1 r2 num_vars) \<longleftrightarrow> match_regex \<pi> r1 \<or> match_regex \<pi> r2"
  using assms WEST_simp_trace_correct_forward WEST_simp_trace_correct_converse by metis



subsubsection \<open> Simp-helper Correct \<close>

lemma WEST_simp_helper_can_simp_bound:
  assumes "simp_L = WEST_simp_helper L (enum_pairs L) i num_vars"
  assumes "\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))"
  assumes "i < length (enum_pairs L)"
  shows "length simp_L < length L"
proof-
  obtain min_j where obt_min_j: "min_j = Min {j. j < length (enum_pairs L) \<and> j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! j))
                                  (L ! snd (enum_pairs L ! j))}"
    by blast
  then have min_j_props: "min_j < length (enum_pairs L) \<and> min_j \<ge> i \<and>
                       check_simp (L ! fst (enum_pairs L ! min_j))
                                  (L ! snd (enum_pairs L ! min_j))"
    using Min_in[of "{j. j < length (enum_pairs L) \<and>
            i \<le> j \<and>
            check_simp (L ! fst (enum_pairs L ! j))
             (L ! snd (enum_pairs L ! j))}"]
    by (smt (verit, ccfv_threshold) assms(2) empty_Collect_eq finite_nat_set_iff_bounded mem_Collect_eq)
  let ?newL = "update_L L (enum_pairs L ! min_j) num_vars"
  have length_newL: "length ?newL = length L - 1"
    using update_L_length assms min_j_props by auto
  have "simp_L = WEST_simp_helper ?newL (enum_pairs ?newL) 0 num_vars"
    using WEST_simp_helper_can_simp[OF assms(1) assms(2) obt_min_j, of ?newL] assms
    by blast
  then show ?thesis
    using assms WEST_simp_helper_length length_newL
    by (metis add_le_cancel_right enum_pairs_bound gen_length_def le_neq_implies_less length_code less_nat_zero_code less_one linordered_semidom_class.add_diff_inverse nth_mem)
qed

lemma WEST_simp_helper_same_length:
  assumes "WEST_regex_of_vars L num_vars"
  assumes "K = WEST_simp_helper L (enum_pairs L) 0 num_vars"
  assumes "length K = length L"
  shows "L = K"
  using WEST_simp_helper_can_simp[of K L 0 num_vars] assms WEST_simp_helper_cant_simp
  by (metis (no_types, lifting) WEST_simp_helper_can_simp_bound gr_zeroI less_irrefl_nat less_nat_zero_code)


lemma WEST_simp_helper_less_length:
  assumes "WEST_regex_of_vars L num_vars"
  assumes "length K < length L"
  assumes "K = WEST_simp_helper L (enum_pairs L) 0 num_vars"
  shows "\<exists>min_j.
        (min_j < length (enum_pairs L) \<and>
        K =
        WEST_simp_helper (update_L L (enum_pairs L ! min_j) num_vars)
         (enum_pairs
           (update_L L (enum_pairs L ! min_j) num_vars))
         0 num_vars
        \<and> check_simp (L ! fst (enum_pairs L ! min_j)) (L ! snd (enum_pairs L ! min_j)))"
  using assms
proof-
  have "\<exists>j<length (enum_pairs L).
       0 \<le> j \<and>
       check_simp (L ! fst (enum_pairs L ! j))
        (L ! snd (enum_pairs L ! j))"
    using assms WEST_simp_helper_can_simp[of K L 0 num_vars]
    by (metis (no_types, lifting) WEST_simp_helper_cant_simp less_irrefl_nat)
  then obtain min_j where obt_min_j: "min_j = Min{j. j<length (enum_pairs L) \<and>
       0 \<le> j \<and> check_simp (L ! fst (enum_pairs L ! j))
                          (L ! snd (enum_pairs L ! j))}"
    by blast
  then have min_j_props: "min_j<length (enum_pairs L) \<and>
       0 \<le> min_j \<and> check_simp (L ! fst (enum_pairs L ! min_j))
                          (L ! snd (enum_pairs L ! min_j))"
    using Min_in
    by (smt (verit) \<open>\<exists>j<length (enum_pairs L). 0 \<le> j \<and> check_simp (L ! fst (enum_pairs L ! j)) (L ! snd (enum_pairs L ! j))\<close> empty_def finite_nat_set_iff_bounded mem_Collect_eq)
  let ?newL = "update_L L (enum_pairs L ! min_j) num_vars"
  have "K = WEST_simp_helper ?newL (enum_pairs ?newL) 0 num_vars"
    using obt_min_j assms
    using WEST_simp_helper_can_simp \<open>\<exists>j<length (enum_pairs L). 0 \<le> j \<and> check_simp (L ! fst (enum_pairs L ! j)) (L ! snd (enum_pairs L ! j))\<close> dual_order.strict_trans2 by blast
  then show ?thesis
    using assms min_j_props by blast
qed

lemma remove_element_at_index_subset:
  fixes i::"nat"
  assumes "i < length L"
  shows "set (remove_element_at_index i L) \<subseteq> set L"
proof-
  have fact1: "set (take i L) \<subseteq> set L"
    using assms unfolding remove_element_at_index.simps
    by (meson set_take_subset)
  have fact2: "set (drop (i + 1) L) \<subseteq> set L"
    using assms unfolding remove_element_at_index.simps
    by (simp add: set_drop_subset)
  have "set (take i L @ drop (i + 1) L) = set (take i L) \<union> set (drop (i + 1) L)"
    by simp
  then show ?thesis
    using fact1 fact2 unfolding remove_element_at_index.simps
    by blast
qed

lemma WEST_simp_helper_correct_forward:
  assumes "WEST_regex_of_vars L num_vars"
  assumes "match \<pi> K"
  assumes "K = WEST_simp_helper L (enum_pairs L) 0 num_vars"
  shows "match \<pi> L"
  using assms
proof (induct "length L - length K" arbitrary: K L num_vars rule: less_induct)
  case less
  {assume same_len: "length K = length L"
    then have "K = L"
      using WEST_simp_helper_same_length[OF less.prems(1) less.prems(3)] by blast
    then have ?case using less by blast
  } moreover {
    assume diff_len: "length K \<noteq> length L"
    then have K_le_L: "length L > length K"
      using less(4) WEST_simp_helper_length[of L 0 num_vars] by simp

    then obtain min_j where obt_min_j: "min_j < length (enum_pairs L) \<and>
     K = WEST_simp_helper
     (update_L L ((enum_pairs L)!min_j) num_vars)
     (enum_pairs (update_L L ((enum_pairs L)!min_j) num_vars))
     0 num_vars
     \<and> check_simp (L ! fst (enum_pairs L ! min_j)) (L ! snd (enum_pairs L ! min_j))"
      using WEST_simp_helper_less_length less.prems by blast
    let ?nextL = "(update_L L ((enum_pairs L)!min_j) num_vars)"
    let ?simp_nextL = "WEST_simp_helper ?nextL (enum_pairs ?nextL) 0 num_vars"
    have "length ?nextL = length L - 1"
      using update_L_length obt_min_j by force
    then have cond1: "length ?nextL - length K < length L - length K"
      using obt_min_j
      by (metis K_le_L Suc_diff_Suc diff_Suc_eq_diff_pred lessI)
    have cond2: "WEST_regex_of_vars (update_L L (enum_pairs L ! min_j) num_vars) num_vars"
      using update_L_preserves_num_vars[of L num_vars  "(enum_pairs L)!min_j" ?nextL]
      using less
      using nth_mem obt_min_j by blast
    let ?h = "(enum_pairs L ! min_j)"
    let ?updateL = "(update_L L ?h num_vars)"
    have "match \<pi> ?updateL"
      using less.hyps[OF cond1 cond2 less.prems(2)] obt_min_j by blast
    have updateL_eq: "?updateL = remove_element_at_index (fst ?h)
                    (remove_element_at_index (snd ?h) L) @
                    [WEST_simp_trace (L ! fst ?h) (L ! snd ?h) num_vars]"
      using update_L.simps[of L ?h num_vars] by blast
    have fst_le_snd: "fst ?h < snd ?h"
        using enum_pairs_fact nth_mem obt_min_j by blast
    have h_bound: "snd ?h < length L"
      using enum_pairs_bound[of L] obt_min_j
      using nth_mem by blast
    {assume match_simped_part: "match \<pi> [WEST_simp_trace (L ! fst ?h) (L ! snd ?h) num_vars]"
      have cond1: "check_simp (L ! fst (enum_pairs L ! min_j))
     (L ! snd (enum_pairs L ! min_j))"
        using obt_min_j by blast
      have cond2: "trace_regex_of_vars (L ! fst (enum_pairs L ! min_j)) num_vars"
        using less.prems(1) fst_le_snd h_bound unfolding WEST_regex_of_vars_def
        by (meson order_less_trans)
      have cond3: "trace_regex_of_vars (L ! snd (enum_pairs L ! min_j)) num_vars"
        using less.prems(1) fst_le_snd h_bound unfolding WEST_regex_of_vars_def
        by (meson order_less_trans)
      have match_either: "match_regex \<pi> (L ! fst ?h) \<or> match_regex \<pi> (L ! snd ?h)"
        using WEST_simp_trace_correct_forward[OF cond1 cond2 cond3]
        using match_simped_part unfolding match_def by force
      then have ?case unfolding match_def
        using fst_le_snd h_bound
        by (meson Suc_lessD less_trans_Suc)
    } moreover {
      let ?other_part = "(remove_element_at_index (fst ?h)
                    (remove_element_at_index (snd ?h) L))"
      assume match_other_part: "match \<pi> ?other_part"
      have "set (remove_element_at_index (fst (enum_pairs L ! min_j))
          (remove_element_at_index (snd (enum_pairs L ! min_j)) L))
          \<subseteq> set (remove_element_at_index (snd (enum_pairs L ! min_j)) L)"
        using fst_le_snd h_bound remove_element_at_index_subset
              [of "fst (enum_pairs L ! min_j)" "(remove_element_at_index (snd (enum_pairs L ! min_j)) L)"]
        by simp
      then have other_part_subset: "set ?other_part \<subseteq> set L"
        using fst_le_snd h_bound remove_element_at_index_subset
              [of "snd (enum_pairs L ! min_j)" L] by blast
      then obtain idx where obt_idx: "match_regex \<pi> (?other_part!idx) \<and> idx < length ?other_part"
        using match_other_part unfolding match_def by metis
      then have "(?other_part!idx) \<in> set L"
        using updateL_eq fst_le_snd h_bound other_part_subset
        by (meson in_mono nth_mem)
      then have ?case
        using obt_idx unfolding match_def
        by (metis in_set_conv_nth)
    }
    ultimately have ?case using updateL_eq WEST_or_correct
      by (metis \<open>match \<pi> (update_L L (enum_pairs L ! min_j) num_vars)\<close>)
  }
  ultimately show ?case by blast
qed


lemma remove_element_at_index_fact:
  assumes "j1 < j2"
  assumes "j2 < length L"
  assumes "i < length L"
  assumes "i \<noteq> j1"
  assumes "i \<noteq> j2"
  shows "L ! i
    \<in> set (remove_element_at_index j1 (remove_element_at_index j2 L))"
proof-
  {assume L_small: "length L \<le> 2"
    then have "(remove_element_at_index j1 (remove_element_at_index j2 L)) = []"
      unfolding remove_element_at_index.simps using assms by simp
    then have ?thesis using assms by auto
  } moreover {
    assume L_big: "length L \<ge> 3"
    then have "length (remove_element_at_index j1 (remove_element_at_index j2 L)) \<ge> 1"
      unfolding remove_element_at_index.simps using assms by auto
    {assume in_front: "i < j1"
      then have i_bound: "i < length (take j2 L)"
        using assms by simp
      have "L!i = (take j1 L)!i"
        using in_front assms by auto
      then have "L!i \<in> set (take j1 L)"
        using in_front assms
        by (metis length_take min_less_iff_conj nth_mem)
      then have Li_in: "L!i \<in> set (take j1 (take j2 L))"
        using assms by auto
      have "set (take j1 (take j2 L @ drop (j2 + 1) L)) = set (take j1 (take j2 L))"
        using assms(1) assms(2) by simp
      then have "L!i \<in> set (take j1 (take j2 L @ drop (j2 + 1) L))"
        using Li_in by blast
      then have ?thesis unfolding remove_element_at_index.simps
        by auto
    } moreover {
      assume in_middle: "j1 < i \<and> i < j2"
      then have i_len: "i < length (take j2 L)"
        using assms by auto
      then have Li_eq: "L!i = (take j2 L)!i"
        by simp
      then have "L!i \<in> set (take j2  L)"
        by (metis \<open>i < length (take j2 L)\<close> in_set_member index_of_L_in_L)
      have "i-(j1+1) < length (drop (j1 + 1) (take j2 L @ drop (j2 + 1) L))"
        using assms i_len in_middle by auto
      then have "L!i = (drop (j1 + 1) (take j2 L)) ! (i-(j1+1))"
        using assms i_len in_middle Li_eq by auto
      then have "L!i \<in> set (drop (j1 + 1) (take j2 L))"
        by (metis diff_less_mono i_len in_middle length_drop less_iff_succ_less_eq nth_mem)
      then have ?thesis
        unfolding remove_element_at_index.simps by auto
    } moreover {
      assume in_back: "j2 < i"
      then have "i-(j2+1) < length (drop (j2 + 1) L)"
        using assms by auto
      then have Li_eq: "L!i = (drop (j2 + 1) L)!(i-(j2+1))"
        using assms in_back by auto
      then have "L!i \<in> set (drop (j2 + 1) L)"
        by (metis \<open>i - (j2 + 1) < length (drop (j2 + 1) L)\<close> nth_mem)
      then have "L!i \<in> set(drop (j1 + 1) (take j2 L @ drop (j2 + 1) L))"
        using assms by auto
      then have ?thesis unfolding remove_element_at_index.simps
        by auto
    }
    ultimately have ?thesis unfolding remove_element_at_index.simps
      using assms L_big by linarith
  }
  ultimately show ?thesis by linarith
qed

lemma update_L_match:
  assumes "WEST_regex_of_vars L num_var"
  assumes "match \<pi> L"
  assumes "h \<in> set (enum_pairs L)"
  assumes "check_simp (L!(fst h)) (L!(snd h))"
  shows "match \<pi> (update_L L h num_var)"
proof-
  obtain i where i_obt: "i < length L \<and> match_regex \<pi> (L!i)"
    using assms(2) unfolding match_def by metis
  have fst_le_snd: "fst h < snd h"
    using assms enum_pairs_fact by auto
  have h_bound: "snd h < length L"
    using assms enum_pairs_bound
    by blast
  {assume in_simped: "i = fst h \<or> i = snd h"
    let ?r1 = "(L!(fst h))"
    let ?r2 = "(L!(snd h))"
    have "match_regex \<pi> (WEST_simp_trace (L ! fst h) (L ! snd h) num_var)"
      using WEST_simp_trace_correct_converse[of ?r1 ?r2 num_var]
      using assms unfolding WEST_regex_of_vars_def
      by (metis (mono_tags, lifting) WEST_simp_trace_correct_converse i_obt enum_pairs_bound enum_pairs_fact in_simped order.strict_trans)
    then have ?thesis
      unfolding update_L.simps match_regex_def
      by (metis (no_types, lifting) WEST_or_correct \<open>match_regex \<pi> (WEST_simp_trace (L ! fst h) (L ! snd h) num_var)\<close> append.right_neutral append_eq_append_conv2 impossible_Cons le_eq_less_or_eq match_def nat_le_linear nth_append_length same_append_eq)
  } moreover {
    assume in_rest: "i \<noteq> fst h \<and> i \<noteq> snd h"
    have "L!i \<in> set L"
      using i_obt by simp
    have "L!i \<in> set (remove_element_at_index (fst h) (remove_element_at_index (snd h) L))"
      using fst_le_snd h_bound i_obt in_rest
      using remove_element_at_index_fact by blast
    then have "match \<pi>
     (remove_element_at_index (fst h) (remove_element_at_index (snd h) L))"
      unfolding match_def using i_obt
      by (metis in_set_conv_nth)
    then have ?thesis unfolding update_L.simps match_def
      using WEST_or_correct match_def by blast
  }
  ultimately show ?thesis by blast
qed


lemma WEST_simp_helper_correct_converse:
  assumes "WEST_regex_of_vars L num_vars"
  assumes "match \<pi> L"
  assumes "K = WEST_simp_helper L (enum_pairs L) i num_vars"
  shows "match \<pi> K"
  using assms
  proof (induct "length L" arbitrary: K L i num_vars rule: less_induct)
    case less
    {assume *: "length (enum_pairs L) \<le> i"
      then have "K = L"
        using less(4)
        using WEST_simp_helper.simps[of L "(enum_pairs L)" i num_vars]
        by argo
      then have ?case
        using less(3)
        by blast
    } moreover {assume *: "length (enum_pairs L) > i"
      {assume **: "\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and> check_simp (L ! fst (enum_pairs L ! j))
              (L ! snd (enum_pairs L ! j))"
        then obtain j_min where j_min_obt: "j_min = Min {j. j < length (enum_pairs L) \<and> j \<ge> i \<and> check_simp (L ! fst (enum_pairs L ! j))
              (L ! snd (enum_pairs L ! j))}"
          by blast
        have j_min_props: "j_min < length (enum_pairs L) \<and> j_min \<ge> i \<and> check_simp (L ! fst (enum_pairs L ! j_min))
              (L ! snd (enum_pairs L ! j_min))"
          using j_min_obt Min_in
          by (metis (mono_tags, lifting) "**" Collect_empty_eq finite_nat_set_iff_bounded mem_Collect_eq)
        have K_eq: "K = (let newL =
                       update_L L (enum_pairs L ! j_min)
                        num_vars
                 in WEST_simp_helper newL
                     (enum_pairs newL) 0 num_vars)"
          using less(4) * ** WEST_simp_helper.simps[of L "(enum_pairs L)" j_min num_vars]
          using WEST_simp_helper_can_simp
          by (metis (no_types, lifting) j_min_obt)
        let ?h = "(enum_pairs L ! j_min)"
        have cond1: "length (update_L L (enum_pairs L ! j_min) num_vars) < length L"
          using update_L_length[of ?h L num_vars] j_min_props
          by (metis diff_less enum_pairs_bound less_nat_zero_code less_one not_gr_zero nth_mem)
        have cond2: "WEST_regex_of_vars (update_L L (enum_pairs L ! j_min) num_vars) num_vars"
          using update_L_preserves_num_vars[of L num_vars ?h K] less
          using j_min_props nth_mem update_L_preserves_num_vars by blast
        have cond3: "match \<pi> (update_L L (enum_pairs L ! j_min) num_vars)"
          using update_L_match[OF less(2) less(3), of ?h] j_min_props
          by fastforce
        have ?case
          using less(1)[OF cond1 cond2, of K]
          using K_eq
          by (metis cond3)
      }
      moreover {assume **: "\<not>(\<exists>j. j < length (enum_pairs L) \<and> j \<ge> i \<and> check_simp (L ! fst (enum_pairs L ! j))
              (L ! snd (enum_pairs L ! j)))"
        then have K_eq: "K = L"
          using WEST_simp_helper_cant_simp less.prems(3)
          by presburger
        then have ?case
          using less(3)
        by blast
      }
      ultimately have ?case
        by blast
    }
    ultimately show ?case
      by linarith
  qed

subsubsection "WEST-simp Correct"

lemma simp_correct_forward:
  assumes "WEST_regex_of_vars L num_vars"
  assumes "match \<pi> (WEST_simp L num_vars)"
  shows "match \<pi> L"
  unfolding WEST_simp.simps using WEST_simp_helper_correct_forward assms
  by (metis WEST_simp.elims)


lemma simp_correct_converse:
  assumes "WEST_regex_of_vars L num_vars"
  assumes "match \<pi> L"
  shows "match \<pi> (WEST_simp L num_vars)"
  unfolding WEST_simp.simps using WEST_simp_helper_correct_converse assms
  by blast


lemma simp_correct:
  assumes "WEST_regex_of_vars L num_vars"
  shows "match \<pi> (WEST_simp L num_vars) \<longleftrightarrow> match \<pi> L"
  using simp_correct_forward simp_correct_converse assms
  by blast


subsection \<open> Correctness of WEST-and-simp/WEST-or-simp \<close>

lemma WEST_and_simp_correct:
  fixes \<pi>::"trace"
  fixes L1 L2:: "WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 n"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 n"
  shows "match \<pi> L1 \<and> match \<pi> L2 \<longleftrightarrow> match \<pi> (WEST_and_simp L1 L2 n)"
proof-
  show ?thesis
    using simp_correct[of "WEST_and L1 L2" n \<pi>] assms WEST_and_correct[of L1 n L2 \<pi>]
    unfolding WEST_and_simp.simps
    using WEST_and_num_vars by blast
qed


lemma WEST_or_simp_correct:
  fixes \<pi>::"trace"
  fixes L1 L2:: "WEST_regex"
  assumes L1_of_num_vars: "WEST_regex_of_vars L1 n"
  assumes L2_of_num_vars: "WEST_regex_of_vars L2 n"
  shows "match \<pi> L1 \<or> match \<pi> L2 \<longleftrightarrow> match \<pi> (WEST_or_simp L1 L2 n)"
proof-
  show ?thesis
    using simp_correct[of "L1@L2" n \<pi>]
    using assms WEST_or_correct[of \<pi> L1 L2]
    unfolding WEST_or_simp.simps
    using WEST_or_num_vars by blast
qed


subsection \<open> Facts about the WEST future operator \<close>

lemma WEST_future_correct_forward:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F \<longrightarrow> (match \<pi> L \<longleftrightarrow> semantics_mltl \<pi> F))"
  assumes "WEST_regex_of_vars L num_vars"
  assumes "WEST_num_vars F \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl F) + b"
  assumes "match \<pi> (WEST_future L a b num_vars)"
  shows "\<pi> \<Turnstile>\<^sub>m (F\<^sub>m [a,b] F)"
  using assms
proof(induct "b-a" arbitrary: \<pi> L F a b)
  case 0
  then have a_eq_b: "a = b" by simp
  then have "WEST_future L a b num_vars =  shift L num_vars a"
    using WEST_future.simps[of L a b num_vars] by simp
  then have "match \<pi> (shift L num_vars a)"
    using 0 by simp
  then have match_dropa_L: "match (drop a \<pi>) L"
    using shift_match[of a \<pi> L num_vars] 0 a_eq_b by auto

  have "complen_mltl F \<le> length (drop a \<pi>)"
    using 0(2)[of "(drop a \<pi>)"] 0(6) a_eq_b complen_geq_one[of F] by simp
  then have "semantics_mltl (drop a \<pi>) F"
    using 0(2)[of "(drop a \<pi>)"] match_dropa_L by blast
  then have "\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F"
    using a_eq_b by blast
  then show ?case unfolding semantics_mltl.simps
    using 0(1, 6) a_eq_b complen_geq_one[of F] by simp
next
  case (Suc x)
  then have b_asucx: "b = a + (Suc x)" by simp
  then have "(WEST_future L a b num_vars) = WEST_or_simp (shift L num_vars b) (WEST_future L a (b - 1) num_vars) num_vars"
    using WEST_future.simps[of L a b num_vars]
    by (metis Suc.hyps(2) Suc.prems(4) add_eq_0_iff_both_eq_0 cancel_comm_monoid_add_class.diff_cancel nat_less_le plus_1_eq_Suc zero_neq_one)
  then have "(WEST_future L a b num_vars) = WEST_or_simp (shift L num_vars b) (WEST_future L a (a + x) num_vars) num_vars"
    using b_asucx
    by (metis add_diff_cancel_left' le_add1 ordered_cancel_comm_monoid_diff_class.diff_add_assoc plus_1_eq_Suc)
  {assume match_head: "match \<pi> (shift L num_vars b)"
    then obtain i where "match_regex \<pi> (shift L num_vars b ! i)"
      unfolding match_def by metis
    have "match (drop b \<pi>) L"
      using shift_match[of b \<pi> L num_vars] Suc(7)  match_head by auto
    then have "semantics_mltl (drop b \<pi>) F"
      using Suc by simp
    then have "\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F"
      using Suc.prems(4) by auto
  } moreover {
    assume match_tail: "match \<pi> (WEST_future L a (a + x) num_vars)"
    have hyp1: "x = b - 1 - a" using Suc by simp
    have hyp2: "(\<And>\<pi>. complen_mltl F \<le> length \<pi> \<longrightarrow> match \<pi> L = semantics_mltl \<pi> F)"
      using Suc.prems by blast
    have hyp3: "WEST_regex_of_vars L num_vars" using Suc.prems by simp
    have hyp4: "WEST_num_vars F \<le> num_vars" using Suc.prems by blast
    have hyp5: "a \<le> b - 1" using Suc.prems Suc.hyps by auto
    have hyp6: "complen_mltl F + (b - 1) \<le> length \<pi>" using Suc.prems by simp
    have hyp7: "match \<pi> (WEST_future L a (b - 1) num_vars)"
      using match_tail Suc.hyps(2)
      using b_asucx by fastforce
    have "semantics_mltl \<pi> (Future_mltl a (a+x) F)"
      using Suc.hyps(1)[of "b-1" a F L \<pi>, OF hyp1 hyp2 hyp3 hyp4 hyp5 hyp6 hyp7]
      using b_asucx by simp
    then have "\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F"
      unfolding semantics_mltl.simps b_asucx by auto
  }
  ultimately have "\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F"
    unfolding match_def
    by (metis Nat.add_diff_assoc Suc.prems(2) Suc.prems(6) WEST_future_num_vars WEST_or_simp_correct shift_num_vars \<open>WEST_future L a b num_vars = WEST_or_simp (shift L num_vars b) (WEST_future L a (b - 1) num_vars) num_vars\<close> \<open>match \<pi> (WEST_future L a (a + x) num_vars) \<Longrightarrow> \<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F\<close> \<open>match \<pi> (shift L num_vars b) \<Longrightarrow> \<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F\<close> b_asucx diff_add_inverse le_add1 plus_1_eq_Suc)
  then show ?case
    using Suc unfolding semantics_mltl.simps by auto
qed



lemma WEST_future_correct_converse:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F \<longrightarrow> (match \<pi> L \<longleftrightarrow> semantics_mltl \<pi> F))"
  assumes "WEST_regex_of_vars L num_vars"
  assumes "WEST_num_vars F \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl F) + b"
  assumes "\<pi> \<Turnstile>\<^sub>m (Future_mltl a b F)"
  shows "match \<pi> (WEST_future L a b num_vars)"
  using assms
proof(induct "b-a" arbitrary: \<pi> L F a b)
  case 0
  then have a_eq_b: "a = b" by simp
  then have west_future_aa: "WEST_future L a b num_vars =  shift L num_vars a"
    using WEST_future.simps[of L a b num_vars] by simp
  have "match (drop a \<pi>) L"
    using assms(1)[of "drop a \<pi>"] assms complen_geq_one
    using "0.prems"(1) "0.prems"(5) "0.prems"(6) a_eq_b le_antisym length_drop semantics_mltl.simps(7) by auto
  then have "match \<pi> (shift L num_vars a)"
    using shift_match_converse 0 by auto
  then show ?case using west_future_aa by simp
next
  case (Suc x)
  then have b_asucx: "b = a + (Suc x)" by simp
  then have "(WEST_future L a b num_vars) = WEST_or_simp (shift L num_vars b) (WEST_future L a (b - 1) num_vars) num_vars"
    using WEST_future.simps[of L a b num_vars]
    by (metis Suc.hyps(2) Zero_not_Suc cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' linorder_le_less_linear)
  then have "(WEST_future L a b num_vars) = WEST_or_simp (shift L num_vars b) (WEST_future L a (a + x) num_vars) num_vars"
    using b_asucx
    by (metis add_Suc_right diff_Suc_1)
  {assume sat_b: "semantics_mltl (drop b \<pi>) F"
    then have "match (drop b \<pi>) L" using Suc by simp
    then have "match \<pi> (shift L num_vars b)"
      using shift_match Suc
      by (metis add.commute add_leD1 shift_match_converse)
    then have ?case using WEST_future.simps[of L a b num_vars] Suc
      by (metis Nat.add_diff_assoc WEST_future_num_vars WEST_or_simp_correct shift_num_vars \<open>WEST_future L a b num_vars = WEST_or_simp (shift L num_vars b) (WEST_future L a (b - 1) num_vars) num_vars\<close> b_asucx le_add1 plus_1_eq_Suc)
  } moreover {
    assume sat_before_b: "semantics_mltl \<pi> (Future_mltl a (a+x) F)"
    have "match \<pi> (WEST_future L a (a + x) num_vars)"
      using Suc.hyps(1)[of "a+x" a F L \<pi>] Suc sat_before_b by simp
    have ?case
      using WEST_future.simps[of L a b num_vars] Suc
      by (metis Nat.add_diff_assoc WEST_future_num_vars WEST_or_simp_correct shift_num_vars \<open>WEST_future L a b num_vars = WEST_or_simp (shift L num_vars b) (WEST_future L a (b - 1) num_vars) num_vars\<close> \<open>match \<pi> (WEST_future L a (a + x) num_vars)\<close> diff_add_inverse le_add1 plus_1_eq_Suc)
  }
  ultimately show ?case using b_asucx
    by (metis (no_types, lifting) Suc.prems(6) add_Suc_right le_SucE le_antisym semantics_mltl.simps(7))
qed


lemma WEST_future_correct:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F \<longrightarrow> (match \<pi> L \<longleftrightarrow> semantics_mltl \<pi> F))"
  assumes "WEST_regex_of_vars L num_vars"
  assumes "WEST_num_vars F \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl F) + b"
  shows "match \<pi> (WEST_future L a b num_vars) \<longleftrightarrow>
                  semantics_mltl \<pi> (Future_mltl a b F)"
  using assms WEST_future_correct_forward WEST_future_correct_converse by blast


subsection \<open> Facts about the WEST global operator \<close>

lemma WEST_global_correct_forward:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F \<longrightarrow> (match \<pi> L \<longleftrightarrow> semantics_mltl \<pi> F))"
  assumes "WEST_regex_of_vars L num_vars"
  assumes "WEST_num_vars F \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl F) + b"
  assumes "match \<pi> (WEST_global L a b num_vars)"
  shows "semantics_mltl \<pi> (Global_mltl a b F)"
  using assms
proof(induct "b-a" arbitrary: \<pi> L F a b)
  case 0
  then have a_eq_b: "a = b" by simp
  then have "WEST_global L a b num_vars = shift L num_vars a"
    using assms WEST_global.simps[of L a b num_vars] by auto
  then have "match \<pi> (shift L num_vars a)" using 0 by simp
  then have "match (drop a \<pi>) L"
    using shift_match[of a \<pi> L num_vars] 0 by auto
  then have "semantics_mltl (drop a \<pi>) F"
    using 0(2)[of "(drop a \<pi>)"] complen_geq_one[of F] 0 a_eq_b by auto
  then show ?case using 0
    unfolding semantics_mltl.simps by auto
next
  case (Suc x)
  then have b_asucx: "b = a + (Suc x)" by simp
  then have "(WEST_global L a b num_vars) = WEST_and_simp (shift L num_vars b) (WEST_global L a (a + x) num_vars) num_vars"
    using WEST_global.simps[of L a b num_vars]
    by (metis add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq less_eq_Suc_le not_less_eq_eq ordered_cancel_comm_monoid_diff_class.diff_add_assoc plus_1_eq_Suc zero_eq_add_iff_both_eq_0)

  have nv1: "WEST_regex_of_vars (shift L num_vars b) num_vars"
    using shift_num_vars Suc by blast
  have nv2: "WEST_regex_of_vars (WEST_global L a (a + x) num_vars) num_vars"
    using WEST_global_num_vars Suc b_asucx
    by (metis le_iff_add)
  have match_h: "match \<pi> (shift L num_vars b)"
    using WEST_and_correct_converse nv1 nv2 Suc
    by (metis WEST_and_simp_correct \<open>WEST_global L a b num_vars = WEST_and_simp (shift L num_vars b) (WEST_global L a (a + x) num_vars) num_vars\<close>)
  then have "match (drop b \<pi>) L"
    using shift_match Suc
    using add_leD2 by blast
  then have sat_b: "semantics_mltl (drop b \<pi>) F" using Suc by auto

  have match_t: "match \<pi> (WEST_global L a (a + x) num_vars)"
    using Suc.hyps(1)[of "a+x" a F L \<pi>] Suc b_asucx
    by (metis WEST_and_simp_correct \<open>WEST_global L a b num_vars = WEST_and_simp (shift L num_vars b) (WEST_global L a (a + x) num_vars) num_vars\<close> nv1 nv2)
  then have "semantics_mltl \<pi> (Global_mltl a (a+x) F)"
    using Suc by fastforce
  then have sat_before_b: "\<forall>i. a \<le> i \<and> i \<le> a + x \<longrightarrow> semantics_mltl (drop i \<pi>) F"
    using Suc unfolding semantics_mltl.simps by auto
  have "\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F"
    using sat_b sat_before_b unfolding semantics_mltl.simps
    by (metis add_Suc_right b_asucx le_antisym not_less_eq_eq)
  then show ?case using Suc
    unfolding semantics_mltl.simps by blast
qed


lemma WEST_global_correct_converse:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F \<longrightarrow> (match \<pi> L \<longleftrightarrow> semantics_mltl \<pi> F))"
  assumes "WEST_regex_of_vars L num_vars"
  assumes "WEST_num_vars F \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl F) + b"
  assumes "semantics_mltl \<pi> (Global_mltl a b F)"
  shows "match \<pi> (WEST_global L a b num_vars)"
  using assms
using assms
proof(induct "b-a" arbitrary: \<pi> L F a b)
  case 0
  then have a_eq_b: "a = b" by simp
  then have west_global_aa: "WEST_global L a b num_vars =  shift L num_vars a"
    using WEST_global.simps[of L a b num_vars] by simp
  have "match (drop a \<pi>) L"
    using assms(1)[of "drop a \<pi>"] assms complen_geq_one
    by (metis (mono_tags, lifting) "0.prems"(1) "0.prems"(5) "0.prems"(6) a_eq_b add_le_imp_le_diff drop_all le_trans length_0_conv length_drop not_one_le_zero semantics_mltl.simps(8))
  then have "match \<pi> (shift L num_vars a)"
    using shift_match_converse 0 by auto
  then show ?case using west_global_aa by simp
next
  case (Suc x)
  then have b_asucx: "b = a + (Suc x)" by simp
  then have west_global: "(WEST_global L a b num_vars) = WEST_and_simp (shift L num_vars b) (WEST_global L a (a + x) num_vars) num_vars"
    using WEST_global.simps[of L a b num_vars]
    by (metis add_diff_cancel_left' add_eq_0_iff_both_eq_0 cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq less_eq_Suc_le not_less_eq_eq ordered_cancel_comm_monoid_diff_class.diff_add_assoc plus_1_eq_Suc)

  have sat_b: "semantics_mltl (drop b \<pi>) F"
    using Suc unfolding semantics_mltl.simps by auto
  then have "match (drop b \<pi>) L" using Suc by simp
  then have match_head: "match \<pi> (shift L num_vars b)"
    using shift_match Suc
    by (metis add.commute add_leD1 shift_match_converse)

  have sat_before_b: "semantics_mltl \<pi> (Future_mltl a (a+x) F)"
    using Suc unfolding semantics_mltl.simps by auto
  have match_tail: "match \<pi> (WEST_global L a (a + x) num_vars)"
    using Suc.hyps(1)[of "a+x" a F L \<pi>] Suc sat_before_b
    by (simp add: b_asucx nle_le not_less_eq_eq)

  have nv1: "WEST_regex_of_vars (shift L num_vars b) num_vars"
    using shift_num_vars Suc by blast
  have nv2: "WEST_regex_of_vars (WEST_global L a (a + x) num_vars) num_vars"
    using WEST_global_num_vars Suc b_asucx
    by (metis le_iff_add)
  show ?case using b_asucx match_head match_tail
    using west_global WEST_and_simp_correct nv1 nv2 by metis
qed



lemma WEST_global_correct:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F \<longrightarrow> (match \<pi> L \<longleftrightarrow> semantics_mltl \<pi> F))"
  assumes "WEST_regex_of_vars L num_vars"
  assumes "WEST_num_vars F \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl F) + b"
  shows "match \<pi> (WEST_global L a b num_vars) \<longleftrightarrow>
                  semantics_mltl \<pi> (Global_mltl a b F)"
  using assms WEST_global_correct_forward WEST_global_correct_converse by blast


subsection \<open>Facts about the WEST until operator \<close>

lemma WEST_until_correct_forward:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F1 \<longrightarrow> (match \<pi> L1 \<longleftrightarrow> semantics_mltl \<pi> F1))"
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F2 \<longrightarrow> (match \<pi> L2 \<longleftrightarrow> semantics_mltl \<pi> F2))"
  assumes "WEST_regex_of_vars L1 num_vars"
  assumes "WEST_regex_of_vars L2 num_vars"
  assumes "WEST_num_vars F1 \<le> num_vars"
  assumes "WEST_num_vars F2 \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> complen_mltl (Until_mltl F1 a b F2)"
  assumes "match \<pi> (WEST_until L1 L2 a b num_vars)"
  shows "semantics_mltl \<pi> (Until_mltl F1 a b F2)"
  using assms
proof(induct "b-a" arbitrary: \<pi> L1 L2 F1 F2 a b)
  case 0
  then have a_eq_b: "b = a" by simp
  have len_xi: "complen_mltl F2 + a \<le> length \<pi>"
    using 0 complen_geq_one by auto
  have until_aa: "WEST_until L1 L2 a b num_vars = WEST_global L2 a a num_vars"
    using WEST_until.simps[of L1 L2 a b num_vars] a_eq_b by auto
  then have "WEST_global L2 a a num_vars = shift L2 num_vars a" by auto
  then have "match \<pi> (shift L2 num_vars a)"
    using until_aa 0 by argo
  then have "match (drop a \<pi>) L2"
    using shift_match[of a \<pi> L2 num_vars] 0 by simp
  then have "semantics_mltl (drop a \<pi>) F2" using 0 by auto
  then have sem_until: "(\<exists>i. (a \<le> i \<and> i \<le> a) \<and>
         semantics_mltl (drop i \<pi>) F2 \<and>
         (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
    by auto
  have "max (complen_mltl F1 - 1) (complen_mltl F2) \<ge> 1"
    using complen_geq_one[of F2] by auto
  then have "a < length \<pi>"
    using 0(9) using a_eq_b
    unfolding complen_mltl.simps
    by linarith
  then show ?case using sem_until
    unfolding a_eq_b semantics_mltl.simps
    by blast
next
  case (Suc x)
  then have b_asucx: "b = a + (Suc x)" by simp
  have "WEST_until L1 L2 a b num_vars = WEST_or_simp (WEST_until L1 L2 a (a + x) num_vars)
             (WEST_and_simp (WEST_global L1 a (a + x) num_vars) (WEST_global L2 b b num_vars) num_vars) num_vars"
    using WEST_until.simps[of L1 L2 a b num_vars] Suc b_asucx
    by (metis add_Suc_right cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 less_add_Suc1 n_not_Suc_n zero_diff)

  let ?rec = "WEST_until L1 L2 a (a + x) num_vars"
  let ?base = "WEST_and_simp (WEST_global L1 a (a + x) num_vars) (WEST_global L2 b b num_vars) num_vars"
  have sem_until: "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
         semantics_mltl (drop i \<pi>) F2 \<and>
         (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
  proof-
    {assume match_base: "match \<pi> ?base"
      have nv1: "WEST_regex_of_vars (WEST_global L2 b b num_vars) num_vars"
        using WEST_global_num_vars[of L2 num_vars b b] Suc by simp
      have nv2: "WEST_regex_of_vars (WEST_global L1 a (a + x) num_vars) num_vars"
        using WEST_global_num_vars[of L1 num_vars a "a+x"] Suc by auto
      have "match \<pi> (WEST_global L2 b b num_vars)"
        using match_base WEST_and_simp_correct Suc nv1 nv2 by blast
      then have "match \<pi> (shift L2 num_vars b)"
        using WEST_global.simps[of L2 b b num_vars] by simp
      then have cond1: "semantics_mltl (drop b \<pi>) F2"
        using shift_match[of b \<pi> L2 num_vars] Suc by simp

      have "match \<pi> (WEST_global L1 a (a + x) num_vars)"
        using match_base WEST_and_simp_correct Suc nv1 nv2 by blast
      then have "semantics_mltl \<pi> (Global_mltl a (a+x) F1)"
        using WEST_global_correct[of F1 L1 num_vars a "a+x" \<pi>] Suc by auto
      then have "\<forall>i. a \<le> i \<and> i \<le> a + x \<longrightarrow> semantics_mltl (drop i \<pi>) F1"
        using Suc by auto
      then have cond2: "\<forall>j. a \<le> j \<and> j < b \<longrightarrow> semantics_mltl (drop j \<pi>) F1"
        using b_asucx by auto

      have "semantics_mltl (drop b \<pi>) F2 \<and>
         (\<forall>j. a \<le> j \<and> j < b \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"
        using cond1 cond2 by auto
      then have ?thesis using Suc by blast
    } moreover {
      assume match_rec: "match \<pi> ?rec"
      then have "semantics_mltl \<pi> (Until_mltl F1 a (a+x) F2)"
        using Suc.hyps(1)[of "a+x" a F1 L1 F2 L2 \<pi>] Suc by auto
      then obtain i where i_obt: "(a \<le> i \<and> i \<le> (a+x)) \<and>
        semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"
        by auto
      have ?thesis using i_obt b_asucx by auto
    }
    ultimately show ?thesis using WEST_until.simps[of L1 L2 a b num_vars] Suc
      using WEST_or_simp_correct
      using \<open>WEST_until L1 L2 a b num_vars =  WEST_or_simp (WEST_until L1 L2 a (a + x) num_vars) (WEST_and_simp (WEST_global L1 a (a + x) num_vars) (WEST_global L2 b b num_vars) num_vars) num_vars\<close>
      by (metis (no_types, lifting) WEST_and_simp_num_vars WEST_global_num_vars WEST_until_num_vars le_add1 order_refl)
  qed
  have "a < length \<pi>"
    using Suc(10) using b_asucx complen_geq_one by auto
  then show ?case using sem_until
    unfolding semantics_mltl.simps by auto
qed


lemma WEST_until_correct_converse:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F1 \<longrightarrow> (match \<pi> L1 \<longleftrightarrow> semantics_mltl \<pi> F1))"
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F2 \<longrightarrow> (match \<pi> L2 \<longleftrightarrow> semantics_mltl \<pi> F2))"
  assumes "WEST_regex_of_vars L1 num_vars"
  assumes "WEST_regex_of_vars L2 num_vars"
  assumes "WEST_num_vars F1 \<le> num_vars"
  assumes "WEST_num_vars F2 \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> (complen_mltl (Until_mltl F1 a b F2))"
  assumes "semantics_mltl \<pi> (Until_mltl F1 a b F2)"
  shows "match \<pi> (WEST_until L1 L2 a b num_vars)"
  using assms
proof(induct "b-a" arbitrary: \<pi> L1 L2 F1 F2 a b)
  case 0
  then have a_eq_b: "b = a" using 0 by simp
  then have "semantics_mltl (drop a \<pi>) F2"
    using assms unfolding semantics_mltl.simps
    by (metis "0.prems"(9) le_antisym semantics_mltl.simps(9))
  then have "match (drop a \<pi>) L2"
    using 0 by simp
  then have "match \<pi> (WEST_global L2 a a num_vars)"
    using shift_match_converse[of a \<pi> L2 num_vars] 0 by auto
  then show ?case using WEST_until.simps[of L1 L2 a a num_vars] a_eq_b by simp
next
  case (Suc x)
  have "max (complen_mltl F1 - 1) (complen_mltl F2) \<ge> 1"
    using complen_geq_one[of F2] by auto
  then have b_lt: "b \<le> length \<pi>" using Suc.prems(8) unfolding complen_mltl.simps
    by linarith
  have b_asucx: "b = a + (Suc x)" using Suc by simp
  {assume sat_b: "semantics_mltl (drop b \<pi>) F2 \<and>
           (\<forall>j. a \<le> j \<and> j < b \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"

    have "match (drop b \<pi>) L2"
      using sat_b Suc by auto
    then have "match \<pi> (shift L2 num_vars b)"
      using shift_match[of b \<pi> L2] shift_match_converse[OF b_lt] by auto
    then have match_L2: "match \<pi> (WEST_global L2 b b num_vars)"
      using WEST_global.simps[of L2 b b num_vars] by simp

    have "semantics_mltl \<pi> (Global_mltl a (b-1) F1)"
      using sat_b Suc unfolding semantics_mltl.simps by auto
    then have match_L1: "match \<pi> (WEST_global L1 a (b-1) num_vars)"
      using WEST_global_correct[of F1 L1 num_vars a "b-1" \<pi>] Suc by auto

    have nv1: "WEST_regex_of_vars (WEST_global L1 a (b - 1) num_vars) num_vars"
      using WEST_global_num_vars[of L1 num_vars a "b-1"] Suc by auto
    have nv2: "WEST_regex_of_vars ((WEST_global L2 b b num_vars)) num_vars"
      using WEST_global_num_vars[of L2 num_vars b b] Suc by auto
    have "match \<pi> (WEST_and_simp (WEST_global L1 a (b - 1) num_vars) (WEST_global L2 b b num_vars) num_vars)"
      using match_L2 match_L1 nv1 nv2 WEST_and_simp_correct by blast
    then have ?case
      using WEST_until.simps[of L1 L2 a b num_vars]
      by (metis Suc.prems(3) Suc.prems(4) Suc.prems(7) WEST_and_simp_num_vars WEST_or_simp_correct WEST_until_num_vars \<open>semantics_mltl \<pi> (Global_mltl a (b - 1) F1)\<close> le_antisym linorder_not_less match_L2 nv1 nv2 semantics_mltl.simps(8))
  } moreover {
    assume "\<not>(semantics_mltl (drop b \<pi>) F2 \<and>
           (\<forall>j. a \<le> j \<and> j < b \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
    then have sab_before_b: "(\<exists>i. (a \<le> i \<and> i \<le> (a+x)) \<and>
         semantics_mltl (drop i \<pi>) F2 \<and>
         (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
      using Suc(11) b_asucx unfolding semantics_mltl.simps
      by (metis add_Suc_right le_antisym not_less_eq_eq)
    then have "semantics_mltl \<pi> (Until_mltl F1 a (b - 1) F2)"
      using Suc b_asucx
      unfolding semantics_mltl.simps by auto
    then have match_rec: "match \<pi> (WEST_until L1 L2 a (b - 1) num_vars)"
      using Suc.hyps(1)[of "b-1" a F1 L1 F2 L2 \<pi>] Suc by auto
    have "WEST_until L1 L2 a b num_vars = WEST_or_simp (WEST_until L1 L2 a (b - 1) num_vars)
                (WEST_and_simp (WEST_global L1 a (b - 1) num_vars)
                  (WEST_global L2 b b num_vars) num_vars)
                num_vars"
      using WEST_until.simps[of L1 L2 a b num_vars] Suc
      by (metis add_eq_self_zero b_asucx nat.discI nless_le)
    then have ?case
      using match_rec Suc WEST_or_simp_correct
      by (metis WEST_and_simp_num_vars WEST_global_num_vars WEST_until_num_vars \<open>semantics_mltl \<pi> (Until_mltl F1 a (b - 1) F2)\<close> eq_imp_le semantics_mltl.simps(9))
  }
  ultimately show ?case by blast
qed


lemma WEST_until_correct:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F1 \<longrightarrow> (match \<pi> L1 \<longleftrightarrow> semantics_mltl \<pi> F1))"
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F2 \<longrightarrow> (match \<pi> L2 \<longleftrightarrow> semantics_mltl \<pi> F2))"
  assumes "WEST_regex_of_vars L1 num_vars"
  assumes "WEST_regex_of_vars L2 num_vars"
  assumes "WEST_num_vars F1 \<le> num_vars"
  assumes "WEST_num_vars F2 \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> complen_mltl (Until_mltl F1 a b F2)"
  shows "match \<pi> (WEST_until L1 L2 a b num_vars) \<longleftrightarrow>
                  semantics_mltl \<pi> (Until_mltl F1 a b F2)"
  using WEST_until_correct_forward[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8)]
    WEST_until_correct_converse[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8)]
  by blast

subsection \<open> Facts about the WEST release Operator \<close>

lemma WEST_release_correct_forward:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F1 \<longrightarrow> (match \<pi> L1 \<longleftrightarrow> semantics_mltl \<pi> F1))"
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F2 \<longrightarrow> (match \<pi> L2 \<longleftrightarrow> semantics_mltl \<pi> F2))"
  assumes "WEST_regex_of_vars L1 num_vars"
  assumes "WEST_regex_of_vars L2 num_vars"
  assumes "WEST_num_vars F1 \<le> num_vars"
  assumes "WEST_num_vars F2 \<le> num_vars"
  assumes a_leq_b: "a \<le> b"
  assumes len: "length \<pi> \<ge> complen_mltl (Release_mltl F1 a b F2)"
  assumes "match \<pi> (WEST_release L1 L2 a b num_vars)"
  shows "semantics_mltl \<pi> (Release_mltl F1 a b F2)"
proof-
  {assume match_base: "match \<pi> (WEST_global L2 a b num_vars)"
    {assume * : "a = 0 \<and> b = 0"
      then have "WEST_global L2 a b num_vars = L2"
        using WEST_global.simps pad_zero by simp
      then have matchL2: "match \<pi> L2"
        using match_base by auto
      have "complen_mltl F2 \<le> length \<pi>"
        using assms(8) by auto
      then have "(semantics_mltl \<pi> F2)"
        using matchL2 assms(2)[of \<pi>] *
        by blast
      then have ?thesis using * by simp
    } moreover {assume * : "b > 0"
    then have "semantics_mltl \<pi> (Global_mltl a b F2)"
      using match_base WEST_global_correct[of F2 L2 num_vars a b \<pi>] assms by auto
    then have "\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2"
      unfolding semantics_mltl.simps using assms * add_cancel_right_left complen_geq_one le_add2 le_trans max_nat.neutr_eq_iff nle_le not_one_le_zero
      by (smt (verit, best) add_diff_cancel_left' complen_mltl.simps(9) diff_is_0_eq')
    then have ?thesis unfolding semantics_mltl.simps using assms by blast
  } ultimately have ?thesis using a_leq_b by blast
} moreover {
    assume no_match_base: "match \<pi> (WEST_release_helper L1 L2 a (b-1) num_vars) \<and> a < b"
    have a_le_b: "a < b" using no_match_base by simp
    have no_match: "match \<pi> (WEST_release_helper L1 L2 a (b-1) num_vars)" using no_match_base by blast
    have "(\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2))"
      using assms a_le_b no_match
    proof(induct "b-a-1" arbitrary: \<pi> L1 L2 F1 F2 a b)
      case 0
      have "max (complen_mltl F1 - 1) (complen_mltl F2) \<ge> 0"
        by force
      then have a_leq: "a \<le> length \<pi>"
        using 0(8-9) unfolding complen_mltl.simps
        by auto
      have b_aplus1: "b = a+1" using 0 by presburger
      then have match_rec: "match \<pi> (WEST_release_helper L1 L2 a a num_vars)"
        using 0(10) using WEST_release.simps[of L1 L2 a b num_vars] WEST_or_correct 0
        by (metis diff_add_inverse2)
      then have "match \<pi> (WEST_and_simp (WEST_global L1 a a num_vars) (WEST_global L2 a a num_vars) num_vars)"
        using 0 WEST_release_helper.simps by metis
      then have "match \<pi> (WEST_global L1 a a num_vars) \<and> match \<pi> (WEST_global L2 a a num_vars)"
        using WEST_and_simp_correct 0
        using WEST_global_num_vars[of L1 num_vars a a] WEST_global_num_vars[of L2 num_vars a a]
        by blast
      then have "match \<pi> (shift L1 num_vars a) \<and> match \<pi> (shift L1 num_vars a)"
        by auto
      then have match_L1L2: "match (drop a \<pi>) L1 \<and> match (drop a \<pi>) L2"
        using shift_match 0 a_leq
        by (metis WEST_global.simps \<open>match \<pi> (WEST_global L1 a a num_vars) \<and> match \<pi> (WEST_global L2 a a num_vars)\<close>)
      have "b - a + max (complen_mltl F1 - 1) (complen_mltl F2) \<le> length (drop a \<pi>)"
        using 0(9) unfolding complen_mltl.simps using 0(1, 8) by auto
      then have "b - a + complen_mltl F1 - 1 \<le> length (drop a \<pi>)"
        unfolding complen_mltl.simps using 0(1) by auto
      then have "complen_mltl F1 \<le> length (drop a \<pi>)"
        using 0(1) complen_geq_one[of F1]
        by (simp add: b_aplus1)
      then have F1_equiv: "semantics_mltl (drop a \<pi>) F1 = match \<pi> (shift L1 num_vars a)"
        using 0
        using \<open>match \<pi> (shift L1 num_vars a) \<and> match \<pi> (shift L1 num_vars a)\<close> match_L1L2 by blast
      have "b - a + max (complen_mltl F2 - 1) (complen_mltl F2) \<le> length (drop a \<pi>)"
        using 0(9) unfolding complen_mltl.simps using 0(1, 8) by auto
      then have "b - a + complen_mltl F2 \<le> length (drop a \<pi>)"
        unfolding complen_mltl.simps using 0(1) by auto
      then have "complen_mltl F2 \<le> length (drop a \<pi>)"
        using 0(1) complen_geq_one[of F1]
        by (simp add: b_aplus1)
      then have F2_equiv: "semantics_mltl (drop a \<pi>) F2 = match \<pi> (shift L2 num_vars a)"
        using 0 a_leq match_L1L2 shift_match_converse by blast
      have "semantics_mltl (drop a \<pi>) F1 \<and> semantics_mltl (drop a \<pi>) F2"
        using F1_equiv F2_equiv match_L1L2
        using a_leq shift_match_converse by blast
      then show ?case using b_aplus1 by auto
    next
      case (Suc x)
      then have b_aplus2: "b = a+x+2" by linarith
      then have match_rec: "match \<pi> (WEST_release_helper L1 L2 a (a+x+1) num_vars)"
        using WEST_release.simps[of L1 L2 a "a+x+2" num_vars] WEST_or_correct Suc
        by (metis Suc_1 Suc_eq_plus1 add_Suc_shift add_diff_cancel_right')
      have west_release_helper: "WEST_release_helper L1 L2 a (a+x+1) num_vars = WEST_or_simp (WEST_release_helper L1 L2 a (a + x) num_vars)
             (WEST_and_simp (WEST_global L2 a (a + x + 1) num_vars) (WEST_global L1 (a + x + 1) (a + x + 1) num_vars) num_vars) num_vars"
        using WEST_release_helper.simps[of L1 L2 a "a+x+1" num_vars]
        by (metis add.commute add_diff_cancel_right' less_add_Suc1 less_add_one not_add_less1 plus_1_eq_Suc)
      let ?rec = "WEST_release_helper L1 L2 a (a + x) num_vars"
      let ?base = "WEST_and_simp (WEST_global L2 a (a + x + 1) num_vars) (WEST_global L1 (a + x + 1) (a + x + 1) num_vars) num_vars"
      have match_rec_or_base: "match \<pi> ?rec \<or> match \<pi> ?base"
        using WEST_or_simp_correct WEST_release_helper_num_vars WEST_and_simp_num_vars WEST_global_num_vars
        by (metis (mono_tags, lifting) Suc.prems(3) Suc.prems(4) ab_semigroup_add_class.add_ac(1) eq_imp_le le_add1 match_rec west_release_helper)
      have "\<exists>j\<ge>a. j \<le> a+x+1 \<and>
           semantics_mltl (drop j \<pi>) F1 \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
      proof-
        {assume match_rec: "match \<pi> (WEST_release_helper L1 L2 a (a + x) num_vars)"
          have x_is: "x = a + x + 1 - a - 1"
            by auto
          have a_leq: "a \<le> a + x + 1"
            by simp
          have a_lt: " a < a + x + 1"
            by auto
          have complen: "complen_mltl (Release_mltl F1 a (a + x + 1) F2) \<le> length \<pi>"
            using Suc(10) Suc(2) by simp
          have sum: "a + x + 1 = b - 1"
            using Suc(2) by auto
          have important_match: "match \<pi> (WEST_release_helper L1 L2 a (b-2) num_vars)"
            using match_rec sum b_aplus2 by simp
          have "match \<pi> (WEST_or_simp (WEST_global L2 a (b - 1) num_vars) (WEST_release_helper L1 L2 a (b - 2) num_vars) num_vars)"
            using important_match b_aplus2
            using WEST_or_simp_correct[of "WEST_global L2 a (b - 1) num_vars" num_vars " WEST_release_helper L1 L2 a (b - 2) num_vars" \<pi>]
            by (metis Suc.prems(3) Suc.prems(4) WEST_global_num_vars WEST_release_helper_num_vars a_leq diff_add_inverse2 le_add1 sum)
          then have match1: "match \<pi> (WEST_release L1 L2 a (a + x + 1) num_vars)"
            unfolding WEST_release.simps
            using b_aplus2 sum
            by (metis (full_types) Suc_1 a_lt diff_diff_left plus_1_eq_Suc)
          have match2: "match \<pi> (WEST_release_helper L1 L2 a (a + x + 1 - 1) num_vars)"
            using important_match b_aplus2 by auto
          have "\<exists>j\<ge>a. j \<le> a + x \<and>
           semantics_mltl (drop j \<pi>) F1 \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
            using Suc.hyps(1)[OF x_is Suc(3) Suc(4) Suc(5) Suc(6) Suc(7) Suc(8) a_leq complen _ a_lt ]
            match1 match2
            by (metis add_diff_cancel_right')
          then have ?case using b_aplus2 by auto
        } moreover {
          assume match_base: "match \<pi> (WEST_and_simp (WEST_global L2 a (a + x + 1) num_vars)
                                      (WEST_global L1 (a + x + 1) (a + x + 1) num_vars) num_vars)"
          have "match \<pi> (WEST_global L2 a (a + x + 1) num_vars)"
            using match_base WEST_and_simp_correct WEST_global_num_vars
            by (metis Suc.prems(3) Suc.prems(4) add.commute eq_imp_le less_add_Suc1 order_less_le plus_1_eq_Suc)
          then have "semantics_mltl \<pi> (Global_mltl a (a + x + 1) F2)"
            using WEST_global_correct[of F2 L2 num_vars a "a + x + 1" \<pi>]
            using Suc.prems(2, 4, 6, 8) Suc.hyps(2) by simp
          then have fact2: "(\<forall>k. a \<le> k \<and> k \<le> (a + x + 1) \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
            unfolding semantics_mltl.simps using Suc.prems(8, 10)
            unfolding complen_mltl.simps by simp
          have "match \<pi> (WEST_global L1 (a + x + 1) (a + x + 1) num_vars)"
            using match_base WEST_and_simp_correct WEST_global_num_vars
            by (metis Suc.prems(3) Suc.prems(4) add.commute eq_imp_le less_add_Suc1 order_less_le plus_1_eq_Suc)
          then have "match \<pi> (shift L1 num_vars (a + x + 1))"
            using WEST_global.simps[of L1 "a + x + 1" "a + x + 1" num_vars] by metis
          then have "match (drop (a + x + 1) \<pi>) L1"
            using shift_match[of "a + x + 1" \<pi> L1 num_vars]
            using Suc.prems(8) unfolding complen_mltl.simps using b_aplus2 by simp
          then have fact1: "semantics_mltl (drop (a + x + 1) \<pi>) F1"
            using Suc.prems(1)[of "drop (a + x + 1) \<pi>"]
            using Suc.prems(8) unfolding complen_mltl.simps using b_aplus2 by auto
          have ?case using b_aplus2 fact1 fact2
            by (smt (verit) Suc.hyps(2) Suc.prems(10) Suc_diff_Suc ab_semigroup_add_class.add_ac(1) add.commute add_diff_cancel_left' antisym_conv1 le_iff_add order_less_imp_le plus_1_eq_Suc)
        }
        ultimately show ?thesis using match_rec_or_base
          by (smt (verit, best) Suc.hyps(2) Suc_eq_plus1 add.assoc diff_right_commute le_trans ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
      qed
      then show ?case using b_aplus2 by simp
    qed

    then have ?thesis unfolding semantics_mltl.simps by auto
  }
  ultimately show ?thesis using WEST_release.simps assms(9)
    by (smt (verit, ccfv_SIG) WEST_global_num_vars WEST_or_simp_correct WEST_release_helper_num_vars a_leq_b add_leD2 add_le_cancel_right assms(3) assms(4) diff_add less_iff_succ_less_eq)
qed


lemma WEST_release_correct_converse:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F1 \<longrightarrow> (match \<pi> L1 \<longleftrightarrow> semantics_mltl \<pi> F1))"
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F2 \<longrightarrow> (match \<pi> L2 \<longleftrightarrow> semantics_mltl \<pi> F2))"
  assumes "WEST_regex_of_vars L1 num_vars"
  assumes "WEST_regex_of_vars L2 num_vars"
  assumes "WEST_num_vars F1 \<le> num_vars"
  assumes "WEST_num_vars F2 \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> complen_mltl (Release_mltl F1 a b F2)"
  assumes "semantics_mltl \<pi> (Release_mltl F1 a b F2)"
  shows "match \<pi> (WEST_release L1 L2 a b num_vars)"
proof-
  have len_xi: "a < length \<pi>"
    using assms(7, 8) unfolding complen_mltl.simps
    by (metis (no_types, lifting) add_leD1 complen_geq_one diff_add_inverse diff_is_0_eq' le_add_diff_inverse le_neq_implies_less le_zero_eq less_numeral_extra(4) less_one max_nat.eq_neutr_iff)

  {assume case1: "\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2"
    then have "match \<pi> (WEST_global L2 a b num_vars)"
      using WEST_global_correct_converse assms by fastforce
    then have ?thesis unfolding WEST_release.simps
      using WEST_or_simp_correct
      by (smt (verit) WEST_global_num_vars WEST_release_helper_num_vars add_leE add_le_cancel_right assms(3) assms(4) diff_add less_iff_succ_less_eq)
  } moreover {
    assume case2: "\<exists>j\<ge>a. j \<le> b - 1 \<and>
           semantics_mltl (drop j \<pi>) F1 \<and>
           (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
    then obtain j where obtain_j: "a \<le> j \<and> j \<le> b - 1 \<and>
           semantics_mltl (drop j \<pi>) F1 \<and>
           (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
      by blast
    {
      assume a_eq_b: "a = b"
      then have ?thesis using case2
        using calculation le_antisym by blast
    } moreover {
      assume a_le_b: "a < b"

      have "semantics_mltl \<pi> (Global_mltl j j F1)" using obtain_j
        by auto
      have "(complen_mltl F1 - 1) + b \<le> length \<pi>"
        using assms(8) obtain_j unfolding complen_mltl.simps by auto
      then have "complen_mltl F1 + j \<le> length \<pi>"
        using obtain_j a_le_b by auto
      then have match_global1: "match \<pi> (WEST_global L1 j j num_vars)"
        using WEST_global_correct_converse[of F1 L1 num_vars j j \<pi>] assms
        using \<open>semantics_mltl \<pi> (Global_mltl j j F1)\<close> by blast

      have len_xi_f2j: "complen_mltl F2 + j \<le> length \<pi>"
        using assms(8) obtain_j by auto
      have "a \<le> j"
        using a_le_b obtain_j by blast
      then have "semantics_mltl \<pi> (Global_mltl a j F2)"
        using obtain_j a_le_b
        unfolding semantics_mltl.simps by blast
      then have match_global2: "match \<pi> (WEST_global L2 a j num_vars)"
        using WEST_global_correct_converse[of F2 L2 num_vars a j \<pi>] len_xi_f2j assms
        by simp
      have j_bounds: "a \<le> j \<and> j \<le> b - 1" using obtain_j by blast
      have "match \<pi> (WEST_release_helper L1 L2 a (b - 1) num_vars)"
        using match_global1 match_global2 a_le_b j_bounds assms(1-6)
      proof(induct "b-1-a" arbitrary: a b L1 L2 F1 F2)
        case 0
        then have "match \<pi> (WEST_and_simp (WEST_global L1 a a num_vars) (WEST_global L2 a a num_vars) num_vars)"
          using WEST_and_simp_correct
          by (metis WEST_global_num_vars diff_is_0_eq' diffs0_imp_equal le_trans)
        then show ?case
          using WEST_release_helper.simps[of L1 L2 a "b-1" num_vars] 0
          by (metis diff_diff_cancel diff_zero le_trans)
      next
        case (Suc x)
        have match_helper: "match \<pi> (WEST_or_simp (WEST_release_helper L1 L2 a (b - 1 - 1) num_vars)
             (WEST_and_simp (WEST_global L2 a (b - 1) num_vars)
              (WEST_global L1 (b - 1) (b - 1) num_vars) num_vars) num_vars)"
          using Suc
        proof-
          {assume j_eq_bm1: "j = b-1"
            then have "match \<pi> (WEST_and_simp (WEST_global L2 a (b - 1) num_vars)
              (WEST_global L1 (b - 1) (b - 1) num_vars) num_vars)"
              using Suc WEST_and_simp_correct
              by (meson WEST_global_num_vars)
            then have ?thesis using WEST_or_simp_correct
              by (metis Suc.hyps(2) Suc.prems(4) Suc.prems(7) Suc.prems(8) WEST_and_simp_num_vars WEST_global_num_vars WEST_release_helper_num_vars cancel_comm_monoid_add_class.diff_cancel diff_less_Suc j_eq_bm1 le_SucE le_add1 not_add_less1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
          } moreover {
            assume j_le_bm1: "j < b-1"
            have "match \<pi> (WEST_release_helper L1 L2 a (b - 1 - 1) num_vars)"
              using Suc.hyps(1)[of "b-1" a L1 L2 F1 F2] Suc
              by (smt (verit) Suc_leI diff_Suc_1 diff_le_mono diff_right_commute j_le_bm1 le_eq_less_or_eq not_less_eq_eq)
            then have ?thesis using WEST_or_simp_correct
              using Suc.hyps(2) Suc.prems(4) Suc.prems(7) Suc.prems(8) WEST_and_simp_num_vars WEST_global_num_vars WEST_release_helper_num_vars
              by (smt (verit, del_insts) Nat.lessE Suc_leI diff_Suc_1 j_le_bm1 le_Suc_eq le_trans)
          }
          ultimately show ?thesis using Suc(6)
            by (meson le_neq_implies_less)
        qed

        have "a < b-1" using Suc(2) by simp
        then show ?case
          using WEST_release_helper.simps[of L1 L2 a "b-1" num_vars] match_helper
          by presburger
      qed

      then have "match \<pi> (WEST_or_simp (WEST_global L2 a b num_vars) (WEST_release_helper L1 L2 a (b - 1) num_vars) num_vars)"
        using WEST_or_simp_correct assms
        by (meson WEST_global_num_vars WEST_release_helper_num_vars j_bounds le_trans)
      then have ?thesis using a_le_b unfolding WEST_release.simps
        by presburger
    }
    ultimately have ?thesis using assms(7) by fastforce
  }
  ultimately show ?thesis unfolding semantics_mltl.simps using len_xi assms(9)
    by fastforce
qed


lemma WEST_release_correct:
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F1 \<longrightarrow> (match \<pi> L1 \<longleftrightarrow> semantics_mltl \<pi> F1))"
  assumes "\<And>\<pi>. (length \<pi> \<ge> complen_mltl F2 \<longrightarrow> (match \<pi> L2 \<longleftrightarrow> semantics_mltl \<pi> F2))"
  assumes "WEST_regex_of_vars L1 num_vars"
  assumes "WEST_regex_of_vars L2 num_vars"
  assumes "WEST_num_vars F1 \<le> num_vars"
  assumes "WEST_num_vars F2 \<le> num_vars"
  assumes "a \<le> b"
  assumes "length \<pi> \<ge> complen_mltl (Release_mltl F1 a b F2)"
  shows "semantics_mltl \<pi> (Release_mltl F1 a b F2) \<longleftrightarrow> match \<pi> (WEST_release L1 L2 a b num_vars)"
  using WEST_release_correct_converse[OF assms(1-8)] WEST_release_correct_forward[OF assms(1-8)]
  by blast

subsection \<open> Top level result: Shows that WEST reg is correct \<close>

lemma WEST_reg_aux_correct:
  assumes \<pi>_long_enough: "length \<pi> \<ge> complen_mltl F"
  assumes is_nnf: "\<exists> \<psi>. F = (convert_nnf \<psi>)"
  assumes \<phi>_nv: "WEST_num_vars F \<le> num_vars"
  assumes "intervals_welldef F"
  shows "match \<pi> (WEST_reg_aux F num_vars) \<longleftrightarrow> semantics_mltl \<pi> F"
  using assms
  proof (induction F arbitrary: \<pi> rule: nnf_induct)
  case nnf
  then show ?case using is_nnf by auto
next
  case True
  have semantics_true: "semantics_mltl \<pi> True_mltl = True" by simp
  have "WEST_reg_aux True_mltl num_vars = [[map (\<lambda>j. S) [0..<num_vars]]]"
    using WEST_reg_aux.simps(1) by blast
  have match_state: "match_timestep (\<pi> ! 0) (map (\<lambda>j. S) [0..<num_vars])"
    unfolding match_timestep_def by auto
  have "length \<pi> \<ge> 1" using True by auto
  then have "match_regex \<pi> [(map (\<lambda>j. S) [0..<num_vars])] = True"
    using True match_state unfolding match_regex_def by simp
  then have "match \<pi> (WEST_reg_aux True_mltl num_vars) = True"
    using WEST_reg_aux.simps(1)[of num_vars] unfolding match_def by simp
  then show ?case
    using semantics_true by auto
next
  case False
  have semantics_false: "semantics_mltl \<pi> False_mltl = False" by simp
  have "match \<pi> [] = False"
    unfolding match_def by simp
  then show ?case
    using semantics_false by simp
next
  case (Prop p)
  have trace_nonempty: "length \<pi> \<ge> 1" using Prop by simp
  let ?state = "\<pi>!0"
  {assume p_in: "p \<in> ?state"
    then have semantics_prop_true: "semantics_mltl \<pi> (Prop_mltl p) = True"
      using semantics_mltl.simps(3)[of \<pi>] trace_nonempty by auto
    have WEST_prop: "(WEST_reg_aux (Prop_mltl p) num_vars) = [[map (\<lambda>j. if p = j then One else S) [0..<num_vars]]]"
      using WEST_reg_aux.simps(3) by blast
    have "p < num_vars \<Longrightarrow> p \<in> \<pi> ! 0"
      using p_in Prop by blast
    then have "match_timestep ?state (map (\<lambda>j. if p = j then One else S) [0..<num_vars]) = True"
      unfolding match_timestep_def p_in by auto
    then have "match_regex \<pi> (WEST_reg_aux (Prop_mltl p) num_vars ! 0) = True"
      using trace_nonempty WEST_prop unfolding match_regex_def by auto
    then have "match \<pi> (WEST_reg_aux (Prop_mltl p) num_vars) = True"
      unfolding match_def by auto
    then have ?case using semantics_prop_true by blast
  } moreover {
    assume p_notin: "p \<notin> ?state"
    then have semantics_prop_false: "semantics_mltl \<pi> (Prop_mltl p) = False"
      using semantics_mltl.simps(3)[of \<pi>] trace_nonempty by auto
    have WEST_prop: "(WEST_reg_aux (Prop_mltl p) num_vars) = [[map (\<lambda>j. if p = j then One else S) [0..<num_vars]]]"
      using WEST_reg_aux.simps(3) by blast
    have "p < num_vars \<and> p \<notin> \<pi> ! 0"
      using p_notin Prop by auto
    then have "match_timestep ?state (map (\<lambda>j. if p = j then One else S) [0..<num_vars]) = False"
      unfolding match_timestep_def p_notin by auto
    then have "match_regex \<pi> (WEST_reg_aux (Prop_mltl p) num_vars ! 0) = False"
      using trace_nonempty WEST_prop unfolding match_regex_def by auto
    then have "match \<pi> (WEST_reg_aux (Prop_mltl p) num_vars) = False"
      unfolding match_def by auto
    then have ?case using semantics_prop_false by blast
  }
  ultimately show ?case by blast
next
  case (NotProp F p)
  have trace_nonempty: "length \<pi> \<ge> 1" using NotProp by simp
  let ?state = "\<pi>!0"
  {assume p_in: "p \<in> ?state"
    then have semantics_prop_true: "semantics_mltl \<pi> (Not_mltl (Prop_mltl p)) = False"
      using semantics_mltl.simps trace_nonempty by auto
    have WEST_prop: "(WEST_reg_aux (Not_mltl (Prop_mltl p)) num_vars) = [[map (\<lambda>j. if p = j then Zero else S) [0..<num_vars]]]"
      using WEST_reg_aux.simps by blast
    have "p < num_vars \<and> p \<in> \<pi> ! 0"
      using p_in NotProp by simp
    then have "match_timestep ?state (map (\<lambda>j. if p = j then Zero else S) [0..<num_vars]) = False"
      unfolding match_timestep_def p_in by auto
    then have "match_regex \<pi> (WEST_reg_aux (Not_mltl (Prop_mltl p)) num_vars ! 0) = False"
      using trace_nonempty WEST_prop unfolding match_regex_def by auto
    then have "match \<pi> (WEST_reg_aux (Not_mltl (Prop_mltl p)) num_vars) = False"
      unfolding match_def by auto
    then have ?case using semantics_prop_true NotProp by blast
  } moreover {
    assume p_notin: "p \<notin> ?state"
    then have semantics_prop_false: "semantics_mltl \<pi> (Not_mltl (Prop_mltl p)) = True"
      using semantics_mltl.simps(3)[of \<pi>] trace_nonempty by auto
    have WEST_prop: "(WEST_reg_aux (Not_mltl (Prop_mltl p)) num_vars) = [[map (\<lambda>j. if p = j then Zero else S) [0..<num_vars]]]"
      using WEST_reg_aux.simps by blast
    have "p < num_vars \<and> p \<notin> \<pi> ! 0"
      using p_notin NotProp by auto
    then have "match_timestep ?state (map (\<lambda>j. if p = j then Zero else S) [0..<num_vars]) = True"
      unfolding match_timestep_def p_notin by auto
    then have "match_regex \<pi> (WEST_reg_aux (Not_mltl (Prop_mltl p)) num_vars ! 0) = True"
      using trace_nonempty WEST_prop unfolding match_regex_def by auto
    then have "match \<pi> (WEST_reg_aux (Not_mltl (Prop_mltl p)) num_vars) = True"
      unfolding match_def by simp
    then have ?case using semantics_prop_false NotProp by blast
  }
  ultimately show ?case by blast
next
  case (And F F1 F2)
  have subformula1: "WEST_num_vars F1 \<le> num_vars"
    using WEST_num_vars_subformulas[of F1 F] And(1,6) by simp
  have subformula2: "WEST_num_vars F2 \<le> num_vars"
    using WEST_num_vars_subformulas[of F2 F] And(1,6) by simp
  have "complen_mltl F1 \<le> complen_mltl F"
    using And(1) complen_mltl.simps(5)[of F1 F2] by auto
  then have cp_F1: "complen_mltl F1 \<le> length \<pi>"
    using And.prems by auto
  have h2: "match \<pi> (WEST_reg_aux F1 num_vars) = semantics_mltl \<pi> F1"
    using And(2)[OF cp_F1] subformula1
    by (metis And.hyps And.prems(2) And.prems(4) convert_nnf.simps(4) convert_nnf_convert_nnf intervals_welldef.simps(5) mltl.inject(3))
  have "complen_mltl F2 \<le> complen_mltl F"
    using And(1) complen_mltl.simps(5)[of F2 F2] by simp
  then have cp_F2: "complen_mltl F2 \<le> length \<pi>"
    using And.prems by auto
  have h1: "match \<pi> (WEST_reg_aux F2 num_vars) = semantics_mltl \<pi> F2"
    using And.prems(2) And(1) And(3)[OF cp_F2] subformula2
    by (metis And.prems(4) convert_nnf.simps(4) convert_nnf_convert_nnf intervals_welldef.simps(5) mltl.inject(3))
  let ?n = "num_vars"
  have F1_nv: "WEST_regex_of_vars (WEST_reg_aux F1 num_vars) num_vars"
    using WEST_reg_aux_num_vars[of F1 num_vars] subformula1 And(1) And.prems(2)
    using WEST_num_vars_subformulas
    by (metis And.prems(4) convert_nnf.simps(4) convert_nnf_convert_nnf intervals_welldef.simps(5) mltl.inject(3))
  have F2_nv: "WEST_regex_of_vars (WEST_reg_aux F2 num_vars) num_vars"
    using WEST_reg_aux_num_vars[of F2 num_vars] subformula1 And(1) And.prems(2)
    using WEST_num_vars_subformulas
    by (metis And.prems(4) convert_nnf.simps(4) convert_nnf_convert_nnf intervals_welldef.simps(5) mltl.inject(3) subformula2)
  have match: "match \<pi> (WEST_and (WEST_reg_aux F1 ?n) (WEST_reg_aux F2 ?n)) = (match \<pi> (WEST_reg_aux F1 ?n) \<and> match \<pi> (WEST_reg_aux F2 ?n))"
    using WEST_and_correct[of "WEST_reg_aux F1 ?n" ?n "WEST_reg_aux F2 ?n" \<pi>, OF F1_nv F2_nv]
    by blast
  have WEST_reg_F: "WEST_reg_aux F num_vars = WEST_and_simp (WEST_reg_aux F1 num_vars) (WEST_reg_aux F2 num_vars) num_vars"
    using  And(1) WEST_reg_aux.simps(6)[of F1 F2 num_vars] by argo
  have semantics_F: "semantics_mltl \<pi> (And_mltl F1 F2) = (semantics_mltl \<pi> F1 \<and> semantics_mltl \<pi> F2)"
    using semantics_mltl.simps(5)[of \<pi> F1 F2] by blast
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>"
    using And(1) And(5) nnf_subformulas[of F _ F1]
    by (metis convert_nnf.simps(4) convert_nnf_convert_nnf mltl.inject(3))
  have F1_correct: "match \<pi> (WEST_reg_aux F1 num_vars) = semantics_mltl \<pi> F1"
    using And(2)[OF cp_F1 F1_nnf] WEST_num_vars_subformulas And by auto
  have F2_nnf: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
    using And(1) And(5) nnf_subformulas[of F _ F2]
    by (metis convert_nnf.simps(4) convert_nnf_convert_nnf mltl.inject(3))
  have F2_correct: " match \<pi> (WEST_reg_aux F2 num_vars) = semantics_mltl \<pi> F2"
    using And(3)[OF cp_F2 F2_nnf] WEST_num_vars_subformulas And by auto
  show ?case
    using WEST_reg_F F1_correct F2_correct
    using semantics_mltl.simps(5)[of \<pi> F1 F2] And(1) match
    by (metis F1_nv F2_nv WEST_and_simp_correct)
next
  case (Or F F1 F2)
  have cp_F1: "complen_mltl F1 \<le> length \<pi>"
    using Or complen_mltl.simps(6)[of F1 F2] by simp
  have cp_F2: "complen_mltl F2 \<le> length \<pi>"
    using Or complen_mltl.simps(6)[of F1 F2] by simp
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>"
    using Or(1) nnf_subformulas[of F _ F1]
    by (metis Or.prems(2) convert_nnf.simps(5) convert_nnf_convert_nnf mltl.inject(4))
  have F1_correct: "match \<pi> (WEST_reg_aux F1 num_vars) = semantics_mltl \<pi> F1"
    using Or(2)[OF cp_F1 F1_nnf] WEST_num_vars_subformulas Or by simp
  have F2_nnf: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
    using Or nnf_subformulas[of F _ F2]
    by (metis convert_nnf.simps(5) convert_nnf_convert_nnf mltl.inject(4))
  have F2_correct: "match \<pi> (WEST_reg_aux F2 num_vars) = semantics_mltl \<pi> F2"
    using Or(3)[OF cp_F2 F2_nnf] WEST_num_vars_subformulas Or by simp
  let ?L1 = "(WEST_reg_aux F1 num_vars)"
  let ?L2 = "(WEST_reg_aux F2 num_vars)"
  have L1_nv: "WEST_regex_of_vars ?L1 num_vars"
    using WEST_reg_aux_num_vars[of F1 num_vars, OF F1_nnf]
    using Or(1, 6, 7) by auto
  have L2_nv: "WEST_regex_of_vars ?L2 num_vars"
    using WEST_reg_aux_num_vars[of F2 num_vars, OF F2_nnf]
    using Or(1, 6, 7) by auto
  have "(match \<pi> ?L1 \<or> match \<pi> ?L2) = match \<pi> (WEST_or_simp ?L1 ?L2 num_vars)"
    using WEST_or_simp_correct[of ?L1 num_vars ?L2 \<pi>, OF L1_nv L2_nv] by blast
  then show ?case
    using F1_correct F2_correct
    using semantics_mltl.simps(6)[of \<pi> F1 F2]
    unfolding Or(1) unfolding WEST_reg_aux.simps by blast
next
  case (Final F F1 a b)
  have F1_nv: "WEST_num_vars F1 \<le> num_vars"
    using Final by auto
  have cp_F1: "complen_mltl F1 \<le> length \<pi>"
    using Final by simp
  then have len_xi: "length \<pi> \<ge> (complen_mltl F1) + b" using Final by auto
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>"
    using Final
    by (metis convert_nnf.simps(6) convert_nnf_convert_nnf mltl.inject(5))
  let ?L1 = "(WEST_reg_aux F1 num_vars)"
  have match_F1: "match \<pi> ?L1 = semantics_mltl \<pi> F1"
    using Final(2)[OF cp_F1 F1_nnf F1_nv] Final by auto
  have intervals_welldef_F1: "intervals_welldef F1"
    using Final by auto
  have a_le_b: "a \<le> b"
    using Final by simp
  show ?case using WEST_reg_aux.simps(7)[of a b F1 num_vars] Final
    using match_F1 WEST_future_correct F1_nv len_xi
    using a_le_b intervals_welldef_F1
    by (metis F1_nnf WEST_reg_aux_num_vars)
next
  case (Global F F1 a b)
  have F1_nv: "WEST_num_vars F1 \<le> num_vars"
    using Global by auto
  have cp_F1: "complen_mltl F1 \<le> length \<pi>"
    using Global by simp
  then have len_xi: "length \<pi> \<ge> (complen_mltl F1) + b" using Global by auto
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>"
    using Global
    by (metis convert_nnf.simps(7) convert_nnf_convert_nnf mltl.inject(6))
  let ?L1 = "(WEST_reg_aux F1 num_vars)"
  have match_F1: "match \<pi> ?L1 = semantics_mltl \<pi> F1"
    using Global(2)[OF cp_F1 F1_nnf F1_nv] Global by auto
  then show ?case using WEST_reg_aux.simps(8)[of a b F1 num_vars] Global
    using match_F1 WEST_global_correct F1_nv
    by (metis F1_nnf WEST_reg_aux_num_vars intervals_welldef.simps(8) len_xi)
next
  case (Until F F1 F2 a b)
  have F1_nv: "WEST_num_vars F1 \<le> num_vars"
    using Until by auto
  {assume *: "a = 0 \<and> b = 0"
    have complen_leq: "complen_mltl F2 \<le> length \<pi>"
      using Until(1) Until.prems(1) by simp
    have some_nnf: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
      using Until(1) Until.prems(2)
      by (metis convert_nnf.simps(8) convert_nnf_convert_nnf mltl.inject(7))
    have " F2 \<in> subformulas (Until_mltl F1 a b F2)"
      unfolding subformulas.simps by blast
    then have num_vars: "WEST_num_vars F2 \<le> num_vars"
      using Until(1) Until.prems(3) WEST_num_vars_subformulas[of F2 F]
      by auto
    have match_F2: "match \<pi> (WEST_reg_aux F2 num_vars) = semantics_mltl \<pi> F2"
      using Until(1) Until(3)[OF complen_leq some_nnf num_vars] Until.prems
      by simp
    have "max (complen_mltl F1 - 1) (complen_mltl F2) >= 1"
      using complen_geq_one[of F2] by auto
    then have len_gt: "length \<pi> > 0"
      using Until.prems(1) Until(1)  by auto
    have global: "WEST_global (WEST_reg_aux F2 num_vars) 0 0 num_vars = shift (WEST_reg_aux F2 num_vars) num_vars 0"
      using WEST_global.simps[of _ 0 0 ] by auto
    have "map (\<lambda>k. arbitrary_state num_vars) [0..<0] = []"
      by simp
    then have padis: "shift (WEST_reg_aux F2 num_vars) num_vars 0 = WEST_reg_aux F2 num_vars"
      unfolding shift.simps arbitrary_trace.simps using append.left_neutral list.simps(8) map_ident upt_0
    proof -
      have "(@) (map (\<lambda>n. arbitrary_state num_vars) ([]::nat list)) = (\<lambda>wss. wss)"
        by blast
      then show "map ((@) (map (\<lambda>n. arbitrary_state num_vars) [0..<0])) (WEST_reg_aux F2 num_vars) = WEST_reg_aux F2 num_vars"
        by simp
    qed
    then have "match \<pi> (WEST_global (WEST_reg_aux F2 num_vars) 0 0 num_vars)  =
    (semantics_mltl \<pi> F2)"
      using match_F2 global padis by simp
    then have "match \<pi> (WEST_until (WEST_reg_aux F1 num_vars) (WEST_reg_aux F2 num_vars) 0 0 num_vars) =
    (semantics_mltl \<pi> F2)"
      using WEST_until.simps[of _ _ 0 0 num_vars] by auto
    then have "match \<pi> (WEST_until (WEST_reg_aux F1 num_vars) (WEST_reg_aux F2 num_vars) 0 0 num_vars) =
    (semantics_mltl (drop 0 \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < 0 \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
      by auto
    then have " match \<pi> (WEST_reg_aux (Until_mltl F1 0 0 F2) num_vars) = semantics_mltl \<pi> (Until_mltl F1 0 0 F2)"
      using len_gt *
      unfolding semantics_mltl.simps WEST_reg_aux.simps by auto
    then have ?case using Until(1) * by auto
  } moreover {assume *: "b > 0"
  then have cp_F1: "complen_mltl F1 \<le> length \<pi>"
    using complen_mltl.simps(10)[of F1 a b F2] Until by simp
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>"
    using Until
    by (metis convert_nnf.simps(8) convert_nnf_convert_nnf mltl.inject(7))
  let ?L1 = "(WEST_reg_aux F1 num_vars)"
  have match_F1: "match \<pi> ?L1 = semantics_mltl \<pi> F1"
    using Until(2)[OF cp_F1 F1_nnf F1_nv] Until by auto
  have F2_nv: "WEST_num_vars F2 \<le> num_vars"
    using Until by auto
  have cp_F2: "complen_mltl F2 \<le> length \<pi>"
    using complen_mltl.simps(10)[of F1 a b F2] Until by simp
  have F2_nnf: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
    using Until
    by (metis convert_nnf.simps(8) convert_nnf_convert_nnf mltl.inject(7))
  let ?L2 = "(WEST_reg_aux F2 num_vars)"
  have match_F2: "match \<pi> ?L2 = semantics_mltl \<pi> F2"
    using Until(3)[OF cp_F2 F2_nnf F2_nv] Until by simp
  have len_xi: "length \<pi> \<ge> complen_mltl (Until_mltl F1 a b F2)" using Until by auto
  then have ?case using WEST_until_correct[of F1 ?L1 F2 ?L2 num_vars a b \<pi>]
    using Until F1_nv F2_nv cp_F1 cp_F2 F1_nnf F2_nnf match_F1 match_F2
    using WEST_reg_aux.simps(9)[of F1 a b F2 num_vars] WEST_reg_aux_num_vars
    by (metis (no_types, lifting) intervals_welldef.simps(9))
  }
  ultimately show ?case using Until.prems(4) Until(1)
    by fastforce
next
  case (Release F F1 F2 a b)
  have F1_nv: "WEST_num_vars F1 \<le> num_vars"
    using Release by auto
  {assume *: "a = 0 \<and> b = 0"
    have complen_leq: "complen_mltl F2 \<le> length \<pi>"
      using Release(1) Release.prems(1) by simp
    have some_nnf: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
      using Release(1) Release.prems(2)
      by (metis convert_nnf.simps(9) convert_nnf_convert_nnf mltl.inject(8))
    have " F2 \<in> subformulas (Until_mltl F1 a b F2)"
      unfolding subformulas.simps by blast
    then have num_vars: "WEST_num_vars F2 \<le> num_vars"
      using Release(1) Release.prems(3) WEST_num_vars_subformulas[of F2 F]
      by auto
    have match_F2: "match \<pi> (WEST_reg_aux F2 num_vars) = semantics_mltl \<pi> F2"
      using Release(1) Release(3)[OF complen_leq some_nnf num_vars] Release.prems
      by simp
    have "max (complen_mltl F1 - 1) (complen_mltl F2) >= 1"
      using complen_geq_one[of F2] by auto
    then have len_gt: "length \<pi> > 0"
      using Release.prems(1) Release(1) by auto
    have global: "WEST_global (WEST_reg_aux F2 num_vars) 0 0 num_vars = shift (WEST_reg_aux F2 num_vars) num_vars 0"
      using WEST_global.simps[of _ 0 0 ] by auto
    have "map (\<lambda>k. arbitrary_state num_vars) [0..<0] = []"
      by simp
    then have padis: "shift (WEST_reg_aux F2 num_vars) num_vars 0 = WEST_reg_aux F2 num_vars"
      unfolding shift.simps arbitrary_trace.simps using append.left_neutral list.simps(8) map_ident upt_0
    proof -
      have "(@) (map (\<lambda>n. arbitrary_state num_vars) ([]::nat list)) = (\<lambda>wss. wss)"
        by blast
      then show "map ((@) (map (\<lambda>n. arbitrary_state num_vars) [0..<0])) (WEST_reg_aux F2 num_vars) = WEST_reg_aux F2 num_vars"
        by simp
    qed
    then have "match \<pi> (WEST_global (WEST_reg_aux F2 num_vars) 0 0 num_vars)  =
    (semantics_mltl \<pi> F2)"
      using match_F2 global padis by simp
    then have "match \<pi> (WEST_until (WEST_reg_aux F1 num_vars) (WEST_reg_aux F2 num_vars) 0 0 num_vars) =
    (semantics_mltl \<pi> F2)"
      using WEST_until.simps[of _ _ 0 0 num_vars] by auto
    then have "match \<pi> (WEST_until (WEST_reg_aux F1 num_vars) (WEST_reg_aux F2 num_vars) 0 0 num_vars) =
    (semantics_mltl (drop 0 \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < 0 \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
      by auto
    then have "match \<pi> (WEST_reg_aux (Release_mltl F1 0 0 F2) num_vars) = semantics_mltl \<pi> (Release_mltl F1 0 0 F2)"
      using len_gt *
      unfolding semantics_mltl.simps WEST_reg_aux.simps by auto
    then have ?case using Release(1) *
      by auto
  } moreover {assume *: "b > 0"
  then have cp_F1: "complen_mltl F1 \<le> length \<pi>"
    using complen_mltl.simps(10)[of F1 a b F2] Release by simp
  have F1_nnf: "\<exists>\<psi>. F1 = convert_nnf \<psi>"
    using Release
    by (metis convert_nnf.simps(9) convert_nnf_convert_nnf mltl.inject(8))
  let ?L1 = "(WEST_reg_aux F1 num_vars)"
  have match_F1: "match \<pi> ?L1 = semantics_mltl \<pi> F1"
    using Release(2)[OF cp_F1 F1_nnf F1_nv] Release by auto
  have F2_nv: "WEST_num_vars F2 \<le> num_vars"
    using Release by auto
  have cp_F2: "complen_mltl F2 \<le> length \<pi>"
    using complen_mltl.simps(10)[of F1 a b F2] Release by simp
  have F2_nnf: "\<exists>\<psi>. F2 = convert_nnf \<psi>"
    using Release
    by (metis convert_nnf.simps(9) convert_nnf_convert_nnf mltl.inject(8))
  let ?L2 = "(WEST_reg_aux F2 num_vars)"
  have match_F2: "match \<pi> ?L2 = semantics_mltl \<pi> F2"
    using Release(3)[OF cp_F2 F2_nnf F2_nv] Release by simp
  have len_xi: "length \<pi> \<ge> (max ((complen_mltl F1)-1) (complen_mltl F2)) + b" using * Release
    by auto
  have ?case using WEST_release_correct[of F1 ?L1 F2 ?L2 num_vars a b \<pi>]
    using Release F1_nv F2_nv cp_F1 cp_F2 F1_nnf F2_nnf match_F1 match_F2
    using WEST_reg_aux.simps(10)[of F1 a b F2 num_vars] WEST_reg_aux_num_vars
    by (metis (full_types) intervals_welldef.simps(10))
  }
  ultimately show ?case using Release(7) Release(1) by fastforce
qed

lemma complen_convert_nnf:
  shows "complen_mltl (convert_nnf \<phi>) = complen_mltl \<phi>"
proof(induction "depth_mltl \<phi>" arbitrary: \<phi> rule: less_induct)
  case less
  then show ?case proof (cases \<phi>)
    case True_mltl
    then show ?thesis by simp
  next
    case False_mltl
    then show ?thesis by simp
  next
    case (Prop_mltl p)
    then show ?thesis by simp
  next
    case (Not_mltl p)
    then show ?thesis proof (induct p)
      case True_mltl
      then show ?case using Not_mltl less by auto
    next
      case False_mltl
      then show ?case using Not_mltl less by auto
    next
      case (Prop_mltl x)
      then show ?case using Not_mltl less by auto
    next
      case (Not_mltl p)
      then show ?case using Not_mltl less by auto
    next
      case (And_mltl p1 p2)
      then show ?case using Not_mltl less by auto
    next
      case (Or_mltl p1 p2)
      then show ?case using Not_mltl less by auto
    next
      case (Future_mltl a b x)
      then show ?case using Not_mltl less by auto
    next
      case (Global_mltl a b x)
      then show ?case using Not_mltl less by auto
    next
      case (Until_mltl x a b y)
      then show ?case using Not_mltl less by auto
    next
      case (Release_mltl x a b y)
      then show ?case using Not_mltl less by auto
    qed
  next
    case (And_mltl x y)
    then show ?thesis using less by auto
  next
    case (Or_mltl x y)
    then show ?thesis using less by auto
  next
    case (Future_mltl a b x)
    then show ?thesis using less by auto
  next
    case (Global_mltl a b x)
    then show ?thesis using less by auto
  next
    case (Until_mltl x a b y)
    then show ?thesis using less by auto
  next
    case (Release_mltl x a b y)
    then show ?thesis using less by auto
  qed
qed


lemma nnf_int_welldef:
  assumes "intervals_welldef \<phi>"
  shows "intervals_welldef (convert_nnf \<phi>)"
  using assms
proof (induct "depth_mltl \<phi>" arbitrary: \<phi> rule: less_induct)
  case less
  then show ?case proof (cases \<phi>)
    case True_mltl
    then show ?thesis by simp
  next
    case False_mltl
    then show ?thesis by simp
  next
    case (Prop_mltl p)
    then show ?thesis by simp
  next
    case (Not_mltl \<psi>)
    then have phi_is: "\<phi> = Not_mltl \<psi>"
      by auto
    show ?thesis proof (cases \<psi>)
      case True_mltl
      then show ?thesis using Not_mltl by simp
    next
      case False_mltl
      then show ?thesis using Not_mltl by simp
    next
      case (Prop_mltl p)
      then show ?thesis using Not_mltl by simp
    next
      case (Not_mltl F)
      then have iwd: "intervals_welldef (convert_nnf F)"
        using phi_is less by simp
      have "\<phi> = Not_mltl (Not_mltl F)"
        using phi_is Not_mltl by auto
      then show ?thesis using iwd
        convert_nnf.simps(13)[of F] by simp
    next
      case (And_mltl x y)
      then show ?thesis using Not_mltl less by simp
    next
      case (Or_mltl x y)
      then show ?thesis using Not_mltl less by simp
    next
      case (Future_mltl a b x)
      then show ?thesis using Not_mltl less by simp
    next
      case (Global_mltl a b x)
      then show ?thesis using Not_mltl less by simp
    next
      case (Until_mltl x a b y)
      then show ?thesis using Not_mltl less by simp
    next
      case (Release_mltl x a b y)
      then show ?thesis using Not_mltl less by simp
    qed
  next
    case (And_mltl x y)
    then show ?thesis using less by simp
  next
    case (Or_mltl x y)
    then show ?thesis using less by simp
  next
    case (Future_mltl a b x)
    then show ?thesis using less by simp
  next
    case (Global_mltl a b x)
    then show ?thesis using less by simp
  next
    case (Until_mltl x a b y)
    then show ?thesis using less by simp
  next
    case (Release_mltl x a b y)
    then show ?thesis using less by simp
  qed
qed


lemma WEST_correct:
  fixes \<phi>::"(nat) mltl"
  fixes \<pi>::"trace"
  assumes int_welldef: "intervals_welldef \<phi>"
  assumes \<pi>_long_enough: "length \<pi> \<ge> complen_mltl (convert_nnf \<phi>)"
  shows  "match \<pi> (WEST_reg \<phi>) \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
proof-
 let ?n = "WEST_num_vars \<phi>"
  have "match \<pi> (WEST_reg_aux (convert_nnf \<phi>) (WEST_num_vars \<phi>)) = semantics_mltl \<pi> (convert_nnf \<phi>)"
    using WEST_reg_aux_correct[OF assms(2) _ _ nnf_int_welldef, of "WEST_num_vars \<phi>"] WEST_num_vars_nnf[of \<phi>]
    using int_welldef by auto
  then show ?thesis
    unfolding WEST_reg.simps
    using WEST_num_vars_nnf[of \<phi>] convert_nnf_preserves_semantics[OF assms(1)]
    by simp
qed



lemma WEST_correct_v2:
  fixes \<phi>::"(nat) mltl"
  fixes \<pi>::"trace"
  assumes "intervals_welldef \<phi>"
  assumes \<pi>_long_enough: "length \<pi> \<ge> complen_mltl \<phi>"
  shows  "match \<pi> (WEST_reg \<phi>) \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
proof-
  show ?thesis
    using WEST_correct complen_convert_nnf
    by (metis \<pi>_long_enough assms(1))
qed

subsection \<open> Top level result for padded version \<close>

lemma WEST_correct_pad_aux:
  fixes \<phi>::"(nat) mltl"
  fixes \<pi>::"trace"
  assumes "intervals_welldef \<phi>"
  assumes \<pi>_long_enough: "length \<pi> \<ge> complen_mltl \<phi>"
  shows  "match \<pi> (pad_WEST_reg \<phi>) \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
proof -
  let ?unpadded = "WEST_reg \<phi>"
  let ?complen = "complen_mltl \<phi>"
  let ?num_vars = "WEST_num_vars \<phi>"
  let ?len = "length (WEST_reg \<phi>)"
  have pwr_is: "pad_WEST_reg \<phi> = (map (\<lambda>L. if length L < ?complen
                    then L @ arbitrary_trace ?num_vars (?complen - length L)
                    else L) ?unpadded)"
    unfolding pad_WEST_reg.simps
    by (metis (no_types, lifting) map_equality_iff pad.elims)
  then have "length ?unpadded = length (pad_WEST_reg \<phi>)"
    by auto
  then have pwr_k_is: "(pad_WEST_reg \<phi> ! k) = (if length (?unpadded!k) < ?complen
                    then (?unpadded!k) @ arbitrary_trace ?num_vars (?complen - length (?unpadded!k))
                    else (?unpadded!k))" if k_lt: "k<length (pad_WEST_reg \<phi>)" for k
    using k_lt pwr_is
    by fastforce
  have same_len: "length (pad_WEST_reg \<phi>) = length (WEST_reg \<phi>)"
    unfolding pad_WEST_reg.simps
    by (meson length_map)
 have "match_regex \<pi> (if length (WEST_reg \<phi> ! k) < complen_mltl \<phi>
   then WEST_reg \<phi> ! k @
        arbitrary_trace (WEST_num_vars \<phi>)
         (complen_mltl \<phi> - length (WEST_reg \<phi> ! k))
   else WEST_reg \<phi> ! k) =
    match_regex \<pi> (WEST_reg \<phi> ! k)" if k_lt: "k < ?len" for k
 proof -
   {assume *: "length (WEST_reg \<phi> ! k) < complen_mltl \<phi>"
     then have len_is: "length (WEST_reg \<phi> ! k @
      arbitrary_trace (WEST_num_vars \<phi>)
       (complen_mltl \<phi> - length (WEST_reg \<phi> ! k))) =
      complen_mltl \<phi>"
       by auto
     have univ_prop: "\<And>A B::'a list. (\<forall>time<length
                (A @ B). (time \<ge> length A \<longrightarrow>
            P time)) \<Longrightarrow> ((\<forall>time<length
                (A @ B).  P time) = (\<forall>time<length
                A . P time))" for P::"nat \<Rightarrow> bool"
       by auto
     have "match_timestep (\<pi> ! time)
             ((WEST_reg \<phi> ! k @
               arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) ! time)"
            if time_prop: "time < length (WEST_reg \<phi> ! k @
                 arbitrary_trace (WEST_num_vars \<phi>)
                  (complen_mltl \<phi> - length (WEST_reg \<phi> ! k))) \<and> time \<ge> length (WEST_reg \<phi> ! k)"
       for time
     proof -
       have access: "((WEST_reg \<phi> ! k @
               arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) ! time)
         = (arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) ! (time - (length (WEST_reg \<phi> ! k)))"
         using time_prop
         by (meson leD nth_append)
       have "(arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) ! (time - (length (WEST_reg \<phi> ! k)))
        = arbitrary_state (WEST_num_vars \<phi>)"
         unfolding arbitrary_trace.simps using * time_prop
         by (metis diff_less_mono diff_zero len_is nth_map_upt)
       then have access2: "((WEST_reg \<phi> ! k @
               arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) ! time)
          = arbitrary_state (WEST_num_vars \<phi>) "
         using access
         by auto
       have "match_timestep (\<pi> ! time) (arbitrary_state (WEST_num_vars \<phi>))"
         unfolding arbitrary_state.simps
         match_timestep_def by simp
       then show ?thesis using access2 by auto
     qed
  then have "(\<forall>time<length
                (WEST_reg \<phi> ! k @
                 arbitrary_trace (WEST_num_vars \<phi>)
                  (complen_mltl \<phi> -
                   length (WEST_reg \<phi> ! k))).
            match_timestep (\<pi> ! time)
             ((WEST_reg \<phi> ! k @
               arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) !
              time)) =
      (\<forall>time<length
                (WEST_reg \<phi> ! k).
            match_timestep (\<pi> ! time)
             ((WEST_reg \<phi> ! k @
               arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) !
              time))"
    using univ_prop[of "WEST_reg \<phi> ! k" "arbitrary_trace (WEST_num_vars \<phi>)
                  (complen_mltl \<phi> -
                   length (WEST_reg \<phi> ! k))"]
      by auto
    then have "(\<forall>time<length
                (WEST_reg \<phi> ! k @
                 arbitrary_trace (WEST_num_vars \<phi>)
                  (complen_mltl \<phi> -
                   length (WEST_reg \<phi> ! k))).
            match_timestep (\<pi> ! time)
             ((WEST_reg \<phi> ! k @
               arbitrary_trace (WEST_num_vars \<phi>)
                (complen_mltl \<phi> -
                 length (WEST_reg \<phi> ! k))) !
              time)) =
    (\<forall>time<length (WEST_reg \<phi> ! k).
            match_timestep (\<pi> ! time)
             (WEST_reg \<phi> ! k ! time))"
       by (simp add: nth_append)
     then have "match_regex \<pi> (WEST_reg \<phi> ! k @
        arbitrary_trace (WEST_num_vars \<phi>)
         (complen_mltl \<phi> - length (WEST_reg \<phi> ! k))) =
    match_regex \<pi> (WEST_reg \<phi> ! k)"
       using len_is \<pi>_long_enough *
       unfolding match_regex_def
       by auto
     then have ?thesis
       using * by auto
   }
   moreover {assume *: "length (WEST_reg \<phi> ! k) \<ge> complen_mltl \<phi>"
     then have ?thesis by simp
   }
   ultimately show ?thesis
     by argo
 qed
  then have "match_regex \<pi> (pad_WEST_reg \<phi> ! k) =
    match_regex \<pi> (WEST_reg \<phi> ! k)" if k_lt: "k < ?len" for k
    using pwr_k_is k_lt same_len by presburger
  then have "match \<pi> (pad_WEST_reg \<phi>) \<longleftrightarrow> match \<pi> (WEST_reg \<phi>)"
    using \<pi>_long_enough same_len
    unfolding match_def
    by auto
  then show ?thesis
    using assms WEST_correct_v2
    by blast
qed


lemma WEST_correct_pad:
  fixes \<phi>::"(nat) mltl"
  fixes \<pi>::"trace"
  assumes "intervals_welldef \<phi>"
  assumes \<pi>_long_enough: "length \<pi> \<ge> complen_mltl \<phi>"
  shows  "match \<pi> (simp_pad_WEST_reg \<phi>) \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
proof -
  let ?unpadded = "WEST_reg \<phi>"
  let ?complen = "complen_mltl \<phi>"
  let ?num_vars = "WEST_num_vars \<phi>"
  have pwr_is: "pad_WEST_reg \<phi> = (map (\<lambda>L. if length L < ?complen
                    then L @ arbitrary_trace ?num_vars (?complen - length L)
                    else L) ?unpadded)"
    unfolding pad_WEST_reg.simps
    by (metis (no_types, lifting) map_equality_iff pad.elims)
  then have "length ?unpadded = length (pad_WEST_reg \<phi>)"
    by auto
  then have pwr_k_is: "(pad_WEST_reg \<phi> ! k) = (if length (?unpadded!k) < ?complen
                    then (?unpadded!k) @ arbitrary_trace ?num_vars (?complen - length (?unpadded!k))
                    else (?unpadded!k))" if k_lt: "k<length (pad_WEST_reg \<phi>)" for k
    using k_lt pwr_is
    by fastforce
  have "length (pad_WEST_reg \<phi> ! k ! i) =
       WEST_num_vars \<phi>" if i_is: "i<length (pad_WEST_reg \<phi> ! k) \<and>k<length (pad_WEST_reg \<phi>)"
    for i k
  proof -
    {assume *: "length (?unpadded!k) < ?complen"
      then have pad_is: "(pad_WEST_reg \<phi> ! k) = (?unpadded!k) @ arbitrary_trace ?num_vars (?complen - length (?unpadded!k))"
        using pwr_k_is that by presburger
      have regtrace1: "trace_regex_of_vars (arbitrary_trace (WEST_num_vars \<phi>)
     (complen_mltl \<phi> - length (WEST_reg \<phi> ! k))) (WEST_num_vars \<phi>)"
        unfolding arbitrary_trace.simps
        trace_regex_of_vars_def
        by auto
      have regtrace2: "trace_regex_of_vars (WEST_reg \<phi> ! k)  (WEST_num_vars \<phi>)"
        using WEST_reg_num_vars[OF assms(1)]
        by (metis \<open>length (WEST_reg \<phi>) = length (pad_WEST_reg \<phi>)\<close> WEST_regex_of_vars_def that)
      have ?thesis
        using pad_is
        using regtrace_append[OF regtrace1 regtrace2]
        by (metis regtrace1 regtrace2 regtrace_append trace_regex_of_vars_def that)
    } moreover {assume *: "length (?unpadded!k) \<ge> ?complen"
      then have "(pad_WEST_reg \<phi> ! k) = (?unpadded!k)"
        using pwr_k_is that by presburger
      then have ?thesis
        using WEST_reg_num_vars[OF assms(1)]
        by (metis \<open>length (WEST_reg \<phi>) = length (pad_WEST_reg \<phi>)\<close> WEST_regex_of_vars_def trace_regex_of_vars_def that)
    }
    ultimately show ?thesis by linarith
  qed
  then have "trace_regex_of_vars (pad_WEST_reg \<phi> ! k)
        (WEST_num_vars \<phi>)" if k_lt: "k<length (pad_WEST_reg \<phi>)" for k
    unfolding trace_regex_of_vars_def
    using k_lt by auto
  then have "WEST_regex_of_vars (pad_WEST_reg \<phi>)
     (WEST_num_vars \<phi>)"
    unfolding WEST_regex_of_vars_def
    by blast
  then show ?thesis
    using WEST_correct_pad_aux[OF assms]
    unfolding simp_pad_WEST_reg.simps
    using simp_correct[of "(pad_WEST_reg \<phi>)" "(WEST_num_vars \<phi>)" \<pi>]
    by blast
qed


end