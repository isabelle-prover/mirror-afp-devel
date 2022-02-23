theory Temporal
  imports MDL NFA Window
begin

fun state_cnt :: "('a, 'b :: timestamp) regex \<Rightarrow> nat" where
  "state_cnt (Lookahead phi) = 1"
| "state_cnt (Symbol phi) = 2"
| "state_cnt (Plus r s) = 1 + state_cnt r + state_cnt s"
| "state_cnt (Times r s) = state_cnt r + state_cnt s"
| "state_cnt (Star r) = 1 + state_cnt r"

lemma state_cnt_pos: "state_cnt r > 0"
  by (induction r rule: state_cnt.induct) auto

fun collect_subfmlas :: "('a, 'b :: timestamp) regex \<Rightarrow> ('a, 'b) formula list \<Rightarrow>
  ('a, 'b) formula list" where
  "collect_subfmlas (Lookahead \<phi>) phis = (if \<phi> \<in> set phis then phis else phis @ [\<phi>])"
| "collect_subfmlas (Symbol \<phi>) phis = (if \<phi> \<in> set phis then phis else phis @ [\<phi>])"
| "collect_subfmlas (Plus r s) phis = collect_subfmlas s (collect_subfmlas r phis)"
| "collect_subfmlas (Times r s) phis = collect_subfmlas s (collect_subfmlas r phis)"
| "collect_subfmlas (Star r) phis = collect_subfmlas r phis"

lemma bf_collect_subfmlas: "bounded_future_regex r \<Longrightarrow> phi \<in> set (collect_subfmlas r phis) \<Longrightarrow>
  phi \<in> set phis \<or> bounded_future_fmla phi"
  by (induction r phis rule: collect_subfmlas.induct) (auto split: if_splits)

lemma collect_subfmlas_atms: "set (collect_subfmlas r phis) = set phis \<union> atms r"
  by (induction r phis rule: collect_subfmlas.induct) (auto split: if_splits)

lemma collect_subfmlas_set: "set (collect_subfmlas r phis) = set (collect_subfmlas r []) \<union> set phis"
proof (induction r arbitrary: phis)
  case (Plus r1 r2)
  show ?case
    using Plus(1)[of phis] Plus(2)[of "collect_subfmlas r1 phis"]
      Plus(2)[of "collect_subfmlas r1 []"]
    by auto
next
  case (Times r1 r2)
  show ?case
    using Times(1)[of phis] Times(2)[of "collect_subfmlas r1 phis"]
      Times(2)[of "collect_subfmlas r1 []"]
    by auto
next
  case (Star r)
  show ?case
    using Star[of phis]
    by auto
qed auto

lemma collect_subfmlas_size: "x \<in> set (collect_subfmlas r []) \<Longrightarrow> size x < size r"
proof (induction r)
  case (Plus r1 r2)
  then show ?case
    by (auto simp: collect_subfmlas_set[of r2 "collect_subfmlas r1 []"])
next
  case (Times r1 r2)
  then show ?case
    by (auto simp: collect_subfmlas_set[of r2 "collect_subfmlas r1 []"])
next
  case (Star r)
  then show ?case
    by fastforce
qed (auto split: if_splits)

lemma collect_subfmlas_app: "\<exists>phis'. collect_subfmlas r phis = phis @ phis'"
  by (induction r phis rule: collect_subfmlas.induct) auto

lemma length_collect_subfmlas: "length (collect_subfmlas r phis) \<ge> length phis"
  by (induction r phis rule: collect_subfmlas.induct) auto

fun pos :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "pos a [] = None"
| "pos a (x # xs) =
    (if a = x then Some 0 else (case pos a xs of Some n \<Rightarrow> Some (Suc n) | _ \<Rightarrow> None))"

lemma pos_sound: "pos a xs = Some i \<Longrightarrow> i < length xs \<and> xs ! i = a"
  by (induction a xs arbitrary: i rule: pos.induct) (auto split: if_splits option.splits)

lemma pos_complete: "pos a xs = None \<Longrightarrow> a \<notin> set xs"
  by (induction a xs rule: pos.induct) (auto split: if_splits option.splits)

fun build_nfa_impl :: "('a, 'b :: timestamp) regex \<Rightarrow> (state \<times> state \<times> ('a, 'b) formula list) \<Rightarrow>
  transition list" where
  "build_nfa_impl (Lookahead \<phi>) (q0, qf, phis) = (case pos \<phi> phis of
    Some n \<Rightarrow> [eps_trans qf n]
  | None \<Rightarrow> [eps_trans qf (length phis)])"
| "build_nfa_impl (Symbol \<phi>) (q0, qf, phis) = (case pos \<phi> phis of
    Some n \<Rightarrow> [eps_trans (Suc q0) n, symb_trans qf]
  | None \<Rightarrow> [eps_trans (Suc q0) (length phis), symb_trans qf])"
| "build_nfa_impl (Plus r s) (q0, qf, phis) = (
    let ts_r = build_nfa_impl r (q0 + 1, qf, phis);
        ts_s = build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis) in
    split_trans (q0 + 1) (q0 + 1 + state_cnt r) # ts_r @ ts_s)"
| "build_nfa_impl (Times r s) (q0, qf, phis) = (
    let ts_r = build_nfa_impl r (q0, q0 + state_cnt r, phis);
        ts_s = build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis) in
    ts_r @ ts_s)"
| "build_nfa_impl (Star r) (q0, qf, phis) = (
    let ts_r = build_nfa_impl r (q0 + 1, q0, phis) in
    split_trans (q0 + 1) qf # ts_r)"

lemma build_nfa_impl_state_cnt: "length (build_nfa_impl r (q0, qf, phis)) = state_cnt r"
  by (induction r "(q0, qf, phis)" arbitrary: q0 qf phis rule: build_nfa_impl.induct)
     (auto split: option.splits)

lemma build_nfa_impl_not_Nil: "build_nfa_impl r (q0, qf, phis) \<noteq> []"
  by (induction r "(q0, qf, phis)" arbitrary: q0 qf phis rule: build_nfa_impl.induct)
     (auto split: option.splits)

lemma build_nfa_impl_state_set: "t \<in> set (build_nfa_impl r (q0, qf, phis)) \<Longrightarrow>
  state_set t \<subseteq> {q0..<q0 + length (build_nfa_impl r (q0, qf, phis))} \<union> {qf}"
  by (induction r "(q0, qf, phis)" arbitrary: q0 qf phis t rule: build_nfa_impl.induct)
     (fastforce simp add: build_nfa_impl_state_cnt state_cnt_pos build_nfa_impl_not_Nil
      split: option.splits)+

lemma build_nfa_impl_fmla_set: "t \<in> set (build_nfa_impl r (q0, qf, phis)) \<Longrightarrow>
  n \<in> fmla_set t \<Longrightarrow> n < length (collect_subfmlas r phis)"
proof (induction r "(q0, qf, phis)" arbitrary: q0 qf phis t rule: build_nfa_impl.induct)
  case (1 \<phi> q0 qf phis)
  then show ?case
    using pos_sound pos_complete by (force split: option.splits)
next
  case (2 \<phi> q0 qf phis)
  then show ?case
    using pos_sound pos_complete by (force split: option.splits)
next
  case (3 r s q0 qf phis)
  then show ?case
    using length_collect_subfmlas dual_order.strict_trans1 by fastforce
next
  case (4 r s q0 qf phis)
  then show ?case
    using length_collect_subfmlas dual_order.strict_trans1 by fastforce
next
  case (5 r q0 qf phis)
  then show ?case
    using length_collect_subfmlas dual_order.strict_trans1 by fastforce
qed

context MDL
begin

definition "IH r q0 qf phis transs bss bs i \<equiv>
  let n = length (collect_subfmlas r phis) in
  transs = build_nfa_impl r (q0, qf, phis) \<and> (\<forall>cs \<in> set bss. length cs \<ge> n) \<and> length bs \<ge> n \<and>
  qf \<notin> NFA.SQ q0 (build_nfa_impl r (q0, qf, phis)) \<and>
  (\<forall>k < n. (bs ! k \<longleftrightarrow> sat (collect_subfmlas r phis ! k) (i + length bss))) \<and>
  (\<forall>j < length bss. \<forall>k < n. ((bss ! j) ! k \<longleftrightarrow> sat (collect_subfmlas r phis ! k) (i + j)))"

lemma nfa_correct: "IH r q0 qf phis transs bss bs i \<Longrightarrow>
  NFA.run_accept_eps q0 qf transs {q0} bss bs \<longleftrightarrow> (i, i + length bss) \<in> match r"
proof (induct r arbitrary: q0 qf phis transs bss bs i rule: regex_induct)
case (Lookahead \<phi>)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 transs"
    using Lookahead unfolding IH_def by (auto simp: Let_def)
  have qf_not_q0_Suc_q0: "qf \<notin> {q0}"
    using Lookahead unfolding IH_def
    by (auto simp: NFA.SQ_def split: option.splits)
  have transs_def: "transs = build_nfa_impl (Lookahead \<phi>) (q0, qf, phis)"
    using Lookahead(1)
    by (auto simp: Let_def IH_def)
  interpret base: nfa q0 qf transs
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding IH_def NFA.Q_def NFA.SQ_def transs_def
    by (auto split: option.splits)
  define n where "n \<equiv> case pos \<phi> phis of Some n \<Rightarrow> n | _ \<Rightarrow> length phis"
  then have collect: "n < length (collect_subfmlas (Lookahead \<phi>) phis)"
    "(collect_subfmlas (Lookahead \<phi>) phis) ! n = \<phi>"
    using pos_sound pos_complete by (force split: option.splits)+
  have "\<And>cs q. base.step_eps cs q0 q \<longleftrightarrow> n < length cs \<and> cs ! n \<and> q = qf" "\<And>cs q. \<not>base.step_eps cs qf q"
    using base.q0_sub_SQ qf_not_in_SQ
    by (auto simp: NFA.step_eps_def transs_def n_def split: option.splits)
  then have base_eps: "base.step_eps_closure_set {q0} cs = (if n < length cs \<and> cs ! n then {q0, qf} else {q0})" for cs
    using NFA.step_eps_closure_set_unfold[where ?X="{qf}"]
    using NFA.step_eps_closure_set_step_id[where ?R="{q0}"]
    using NFA.step_eps_closure_set_step_id[where ?R="{qf}"]
    by auto
  have base_delta: "base.delta {q0} cs = {}" for cs
    unfolding NFA.delta_def NFA.step_symb_set_def base_eps
    by (auto simp: NFA.step_symb_def NFA.SQ_def transs_def split: option.splits)
  show ?case
  proof (cases bss)
    case Nil
    have sat: "n < length bs \<and> bs ! n \<longleftrightarrow> sat \<phi> i"
      using Lookahead(1) collect
      by (auto simp: Let_def IH_def Nil)
    show ?thesis
      using qf_not_q0_Suc_q0
      unfolding NFA.run_accept_eps_def NFA.run_def NFA.accept_eps_def Nil
      by (auto simp: base_eps sat)
  next
    case bss_def: (Cons cs css)
    show ?thesis
      using NFA.run_accept_eps_empty
      unfolding NFA.run_accept_eps_def NFA.run_def NFA.accept_eps_def bss_def
      by (auto simp: bss_def base_delta)
  qed
next
  case (Symbol \<phi>)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 transs"
    using Symbol unfolding IH_def by (auto simp: Let_def)
  have qf_not_q0_Suc_q0: "qf \<notin> {q0, Suc q0}"
    using Symbol unfolding IH_def
    by (auto simp: NFA.SQ_def split: option.splits)
  have transs_def: "transs = build_nfa_impl (Symbol \<phi>) (q0, qf, phis)"
    using Symbol(1)
    by (auto simp: Let_def IH_def)
  interpret base: nfa q0 qf transs
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding IH_def NFA.Q_def NFA.SQ_def transs_def
    by (auto split: option.splits)
  define n where "n \<equiv> case pos \<phi> phis of Some n \<Rightarrow> n | _ \<Rightarrow> length phis"
  then have collect: "n < length (collect_subfmlas (Symbol \<phi>) phis)"
    "(collect_subfmlas (Symbol \<phi>) phis) ! n = \<phi>"
    using pos_sound pos_complete by (force split: option.splits)+
  have "\<And>cs q. base.step_eps cs q0 q \<longleftrightarrow> n < length cs \<and> cs ! n \<and> q = Suc q0" "\<And>cs q. \<not>base.step_eps cs (Suc q0) q"
    using base.q0_sub_SQ
    by (auto simp: NFA.step_eps_def transs_def n_def split: option.splits)
  then have base_eps: "base.step_eps_closure_set {q0} cs = (if n < length cs \<and> cs ! n then {q0, Suc q0} else {q0})" for cs
    using NFA.step_eps_closure_set_unfold[where ?X="{Suc q0}"]
    using NFA.step_eps_closure_set_step_id[where ?R="{q0}"]
    using NFA.step_eps_closure_set_step_id[where ?R="{Suc q0}"]
    by auto
  have base_delta: "base.delta {q0} cs = (if n < length cs \<and> cs ! n then {qf} else {})" for cs
    unfolding NFA.delta_def NFA.step_symb_set_def base_eps
    by (auto simp: NFA.step_symb_def NFA.SQ_def transs_def split: option.splits)
  show ?case
  proof (cases bss)
    case Nil
    show ?thesis
      using qf_not_q0_Suc_q0
      unfolding NFA.run_accept_eps_def NFA.run_def NFA.accept_eps_def Nil
      by (auto simp: base_eps)
  next
    case bss_def: (Cons cs css)
    have sat: "n < length cs \<and> cs ! n \<longleftrightarrow> sat \<phi> i"
      using Symbol(1) collect
      by (auto simp: Let_def IH_def bss_def)
    show ?thesis
    proof (cases css)
      case Nil
      show ?thesis
        unfolding NFA.run_accept_eps_def NFA.run_def NFA.accept_eps_def bss_def Nil
        by (auto simp: base_delta sat NFA.step_eps_closure_set_def NFA.step_eps_closure_def)
    next
      case css_def: (Cons ds dss)
      have "base.delta {} ds = {}" "base.delta {qf} ds = {}"
        using base.step_eps_closure_qf qf_not_in_SQ step_symb_dest
         by (fastforce simp: NFA.delta_def NFA.step_eps_closure_set_def NFA.step_symb_set_def)+
      then show ?thesis
        using NFA.run_accept_eps_empty
        unfolding NFA.run_accept_eps_def NFA.run_def NFA.accept_eps_def bss_def css_def
        by (auto simp: base_delta)
    qed
  qed
next
  case (Plus r s)
  obtain phis' where collect: "collect_subfmlas (Plus r s) phis =
    collect_subfmlas r phis @ phis'"
    using collect_subfmlas_app by auto
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Plus r s) (q0, qf, phis))"
    using Plus unfolding IH_def by auto
  interpret base: nfa q0 qf "build_nfa_impl (Plus r s) (q0, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt by fast+
  interpret left: nfa "q0 + 1" qf "build_nfa_impl r (q0 + 1, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  interpret right: nfa "q0 + 1 + state_cnt r" qf
    "build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  from Plus(3) have "IH r (q0 + 1) qf phis (build_nfa_impl r (q0 + 1, qf, phis)) bss bs i"
    unfolding Let_def IH_def collect
    using left.qf_not_in_SQ
    by (auto simp: nth_append)
  then have left_IH: "left.run_accept_eps {q0 + 1} bss bs \<longleftrightarrow>
    (i, i + length bss) \<in> match r"
    using Plus(1) build_nfa_impl_state_cnt
    by auto
  have "IH s (q0 + 1 + state_cnt r) qf (collect_subfmlas r phis)
    (build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)) bss bs i"
    using right.qf_not_in_SQ IH_def Plus
    by (auto simp: Let_def)
  then have right_IH: "right.run_accept_eps {q0 + 1 + state_cnt r} bss bs \<longleftrightarrow>
    (i, i + length bss) \<in> match s"
    using Plus(2) build_nfa_impl_state_cnt
    by auto
  interpret cong: nfa_cong_Plus q0 "q0 + 1" "q0 + 1 + state_cnt r" qf qf qf
    "build_nfa_impl (Plus r s) (q0, qf, phis)" "build_nfa_impl r (q0 + 1, qf, phis)"
    "build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    unfolding NFA.SQ_def build_nfa_impl_state_cnt
      NFA.step_eps_def NFA.step_symb_def
    by (auto simp add: nth_append build_nfa_impl_state_cnt)
  show ?case
    using cong.run_accept_eps_cong left_IH right_IH Plus
    by (auto simp: Let_def IH_def)
next
  case (Times r s)
  obtain phis' where collect: "collect_subfmlas (Times r s) phis =
    collect_subfmlas r phis @ phis'"
    using collect_subfmlas_app by auto
  have transs_def: "transs = build_nfa_impl (Times r s) (q0, qf, phis)"
    using Times unfolding IH_def by (auto simp: Let_def)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Times r s) (q0, qf, phis))"
    using Times unfolding IH_def by auto
  interpret base: nfa q0 qf "build_nfa_impl (Times r s) (q0, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt by fast+
  interpret left: nfa "q0" "q0 + state_cnt r" "build_nfa_impl r (q0, q0 + state_cnt r, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  interpret right: nfa "q0 + state_cnt r" qf
    "build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  from Times(3) have left_IH: "IH r q0 (q0 + state_cnt r) phis
    (build_nfa_impl r (q0 , q0 + state_cnt r, phis)) bss bs i"
    unfolding Let_def IH_def collect
    using left.qf_not_in_SQ
    by (auto simp: nth_append)
  from Times(3) have left_IH_take: "\<And>n. n < length bss \<Longrightarrow>
    IH r q0 (q0 + state_cnt r) phis
    (build_nfa_impl r (q0, q0 + state_cnt r, phis)) (take n bss) (hd (drop n bss)) i"
    unfolding Let_def IH_def collect
    using left.qf_not_in_SQ
    apply (auto simp: nth_append min_absorb2 hd_drop_conv_nth)
     apply (meson in_set_takeD le_add1 le_trans)
    by (meson le_add1 le_trans nth_mem)
  have left_IH_match: "left.run_accept_eps {q0} bss bs \<longleftrightarrow>
    (i, i + length bss) \<in> match r"
    using Times(1) build_nfa_impl_state_cnt left_IH
    by auto
  have left_IH_match_take: "\<And>n. n < length bss \<Longrightarrow>
    left.run_accept_eps {q0} (take n bss) (hd (drop n bss)) \<longleftrightarrow> (i, i + n) \<in> match r"
    using Times(1) build_nfa_impl_state_cnt left_IH_take
    by (fastforce simp add: nth_append min_absorb2)
  have "IH s (q0 + state_cnt r) qf (collect_subfmlas r phis)
    (build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)) bss bs i"
    using right.qf_not_in_SQ IH_def Times
    by (auto simp: Let_def)
  then have right_IH: "\<And>n. n \<le> length bss \<Longrightarrow> IH s (q0 + state_cnt r) qf (collect_subfmlas r phis)
    (build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)) (drop n bss) bs (i + n)"
    unfolding Let_def IH_def
    by (auto simp: nth_append add.assoc) (meson in_set_dropD)
  have right_IH_match: "\<And>n. n \<le> length bss \<Longrightarrow>
    right.run_accept_eps {q0 + state_cnt r} (drop n bss) bs \<longleftrightarrow> (i + n, i + length bss) \<in> match s"
    using Times(2)[OF right_IH] build_nfa_impl_state_cnt
    by (auto simp: IH_def)
  interpret cong: nfa_cong_Times q0 "q0 + state_cnt r" qf
    "build_nfa_impl (Times r s) (q0, qf, phis)"
    "build_nfa_impl r (q0, q0 + state_cnt r, phis)"
    "build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    using NFA.Q_def NFA.SQ_def NFA.step_eps_def NFA.step_symb_def build_nfa_impl_state_set
    by (fastforce simp add: nth_append build_nfa_impl_state_cnt build_nfa_impl_not_Nil
        state_cnt_pos)+
  have right_IH_Nil: "right.run_accept_eps {q0 + state_cnt r} [] bs \<longleftrightarrow>
    (i + length bss, i + length bss) \<in> match s"
    using right_IH_match
    by fastforce
  show ?case
    unfolding match_Times transs_def cong.run_accept_eps_cong left_IH_match right_IH_Nil
    using left_IH_match_take right_IH_match less_imp_le_nat le_eq_less_or_eq
    by auto
next
  case (Star r)
  then show ?case
  proof (induction "length bss" arbitrary: bss bs i rule: nat_less_induct)
    case 1
    have transs_def: "transs = build_nfa_impl (Star r) (q0, qf, phis)"
      using 1 unfolding IH_def by (auto simp: Let_def)
    have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Star r) (q0, qf, phis))"
      using 1 unfolding IH_def by auto
    interpret base: nfa q0 qf "build_nfa_impl (Star r) (q0, qf, phis)"
      apply unfold_locales
      using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
      unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
      by fast+
    interpret left: nfa "q0 + 1" q0 "build_nfa_impl r (q0 + 1, q0, phis)"
      apply unfold_locales
      using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
      unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
      by fastforce+
    from 1(3) have left_IH: "IH r (q0 + 1) q0 phis (build_nfa_impl r (q0 + 1, q0, phis)) bss bs i"
      using left.qf_not_in_SQ
      unfolding Let_def IH_def
      by (auto simp add: nth_append)
    from 1(3) have left_IH_take: "\<And>n. n < length bss \<Longrightarrow>
      IH r (q0 + 1) q0 phis (build_nfa_impl r (q0 + 1, q0, phis)) (take n bss) (hd (drop n bss)) i"
      using left.qf_not_in_SQ
      unfolding Let_def IH_def
      by (auto simp add: nth_append min_absorb2 hd_drop_conv_nth) (meson in_set_takeD)
    have left_IH_match: "left.run_accept_eps {q0 + 1} bss bs \<longleftrightarrow>
      (i, i + length bss) \<in> match r"
      using 1(2) left_IH
      unfolding build_nfa_impl_state_cnt NFA.SQ_def
      by auto
    have left_IH_match_take: "\<And>n. n < length bss \<Longrightarrow>
      left.run_accept_eps {q0 + 1} (take n bss) (hd (drop n bss)) \<longleftrightarrow>
      (i, i + n) \<in> match r"
      using 1(2) left_IH_take
      unfolding build_nfa_impl_state_cnt NFA.SQ_def
      by (fastforce simp add: nth_append min_absorb2)
    interpret cong: nfa_cong_Star q0 "q0 + 1" qf
      "build_nfa_impl (Star r) (q0, qf, phis)"
      "build_nfa_impl r (q0 + 1, q0, phis)"
      apply unfold_locales
      unfolding NFA.SQ_def build_nfa_impl_state_cnt NFA.step_eps_def NFA.step_symb_def
      by (auto simp add: nth_append build_nfa_impl_state_cnt)
    show ?case
      using cong.run_accept_eps_Nil
    proof (cases bss)
      case Nil
      show ?thesis
        unfolding transs_def Nil
        using cong.run_accept_eps_Nil run_Nil run_accept_eps_Nil
        by auto
    next
      case (Cons cs css)
      have aux: "\<And>n j x P. n < x \<Longrightarrow> j < x - n \<Longrightarrow> (\<forall>j < Suc x. P j) \<Longrightarrow> P (Suc (n + j))"
        by auto
      from 1(3) have star_IH: "\<And>n. n < length css \<Longrightarrow>
        IH (Star r) q0 qf phis transs (drop n css) bs (i + n + 1)"
        unfolding Cons Let_def IH_def
        using aux[of _ _ _ "\<lambda>j. \<forall>k<length (collect_subfmlas r phis).
          (cs # css) ! j ! k = sat (collect_subfmlas r phis ! k) (i + j)"]
        by (auto simp add: nth_append add.assoc dest: in_set_dropD)
      have IH_inst: "\<And>xs i. length xs \<le> length css \<Longrightarrow> IH (Star r) q0 qf phis transs xs bs i \<longrightarrow>
        (base.run_accept_eps {q0} xs bs \<longleftrightarrow> (i, i + length xs) \<in> match (Star r))"
        using 1
        unfolding Cons
        by (auto simp add: nth_append less_Suc_eq_le transs_def)
      have "\<And>n. n < length css \<Longrightarrow> base.run_accept_eps {q0} (drop n css) bs \<longleftrightarrow>
        (i + n + 1, i + length (cs # css)) \<in> match (Star r)"
      proof -
        fix n
        assume assm: "n < length css"
        then show "base.run_accept_eps {q0} (drop n css) bs \<longleftrightarrow>
          (i + n + 1, i + length (cs # css)) \<in> match (Star r)"
          using IH_inst[of "drop n css" "i + n + 1"] star_IH
          by (auto simp add: nth_append)
      qed
      then show ?thesis
        using match_Star length_Cons Cons cong.run_accept_eps_cong_Cons
        using cong.run_accept_eps_Nil left_IH_match left_IH_match_take
        apply (auto simp add: Cons transs_def)
         apply (metis Suc_less_eq add_Suc_right drop_Suc_Cons less_imp_le_nat take_Suc_Cons)
        apply (metis Suc_less_eq add_Suc_right drop_Suc_Cons le_eq_less_or_eq lessThan_iff
            take_Suc_Cons)
        done
    qed
  qed
qed

lemma step_eps_closure_set_empty_list:
  assumes "wf_regex r" "IH r q0 qf phis transs bss bs i" "NFA.step_eps_closure q0 transs bs q qf"
  shows "NFA.step_eps_closure q0 transs [] q qf"
  using assms
proof (induction r arbitrary: q0 qf phis transs q)
  case (Symbol \<phi>)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 transs"
    using Symbol unfolding IH_def by (auto simp: Let_def)
  have qf_not_q0_Suc_q0: "qf \<notin> {q0, Suc q0}"
    using Symbol unfolding IH_def
    by (auto simp: NFA.SQ_def split: option.splits)
  have transs_def: "transs = build_nfa_impl (Symbol \<phi>) (q0, qf, phis)"
    using Symbol(2)
    by (auto simp: Let_def IH_def)
  interpret base: nfa q0 qf transs
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding IH_def NFA.Q_def NFA.SQ_def transs_def
    by (auto split: option.splits)
  define n where "n \<equiv> case pos \<phi> phis of Some n \<Rightarrow> n | _ \<Rightarrow> length phis"
  then have collect: "n < length (collect_subfmlas (Symbol \<phi>) phis)"
    "(collect_subfmlas (Symbol \<phi>) phis) ! n = \<phi>"
    using pos_sound pos_complete by (force split: option.splits)+
  have SQD: "q \<in> NFA.SQ q0 transs \<Longrightarrow> q = q0 \<or> q = Suc q0" for q
    by (auto simp: NFA.SQ_def transs_def split: option.splits)
  have "\<not>base.step_eps cs q qf" if "q \<in> NFA.SQ q0 transs" for cs q
    using SQD[OF that] qf_not_q0_Suc_q0
    by (auto simp: NFA.step_eps_def transs_def split: option.splits transition.splits)
  then show ?case
    using Symbol(3)
    by (auto simp: NFA.step_eps_closure_def) (metis rtranclp.simps step_eps_dest)
next
  case (Plus r s)
  have transs_def: "transs = build_nfa_impl (Plus r s) (q0, qf, phis)"
    using Plus(4)
    by (auto simp: IH_def Let_def)
  define ts_l where "ts_l = build_nfa_impl r (q0 + 1, qf, phis)"
  define ts_r where "ts_r = build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)"
  have len_ts: "length ts_l = state_cnt r" "length ts_r = state_cnt s" "length transs = Suc (state_cnt r + state_cnt s)"
    by (auto simp: ts_l_def ts_r_def transs_def build_nfa_impl_state_cnt)
  have transs_eq: "transs = split_trans (q0 + 1) (q0 + 1 + state_cnt r) # ts_l @ ts_r"
    by (auto simp: transs_def ts_l_def ts_r_def)
  have ts_nonempty: "ts_l = [] \<Longrightarrow> False" "ts_r = [] \<Longrightarrow> False"
    by (auto simp: ts_l_def ts_r_def build_nfa_impl_not_Nil)
  obtain phis' where collect: "collect_subfmlas (Plus r s) phis = collect_subfmlas r phis @ phis'"
    using collect_subfmlas_app by auto
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Plus r s) (q0, qf, phis))"
    using Plus unfolding IH_def by auto
  interpret base: nfa q0 qf transs
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt transs_def by fast+
  interpret left: nfa "Suc q0" qf ts_l
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt ts_l_def
    by fastforce+
  interpret right: nfa "Suc (q0 + state_cnt r)" qf ts_r
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt ts_r_def
    by fastforce+
  interpret cong: nfa_cong_Plus q0 "Suc q0" "Suc (q0 + state_cnt r)" qf qf qf transs ts_l ts_r
    apply unfold_locales
    unfolding NFA.SQ_def build_nfa_impl_state_cnt
      NFA.step_eps_def NFA.step_symb_def transs_def ts_l_def ts_r_def
    by (auto simp add: nth_append build_nfa_impl_state_cnt)
  have "IH s (Suc (q0 + state_cnt r)) qf (collect_subfmlas r phis) ts_r bss bs i"
    using right.qf_not_in_SQ IH_def Plus
    by (auto simp: Let_def ts_r_def)
  then have case_right: "base.step_eps_closure [] q qf" if "base.step_eps_closure bs q qf" "q \<in> right.Q" for q
    using cong.right.eps_nfa'_step_eps_closure[OF that] Plus(2,3) cong.right.nfa'_eps_step_eps_closure[OF _ that(2)]
    by auto
  from Plus(4) have "IH r (Suc q0) qf phis ts_l bss bs i"
    using left.qf_not_in_SQ
    unfolding Let_def IH_def collect ts_l_def
    by (auto simp: nth_append)
  then have case_left: "base.step_eps_closure [] q qf" if "base.step_eps_closure bs q qf" "q \<in> left.Q" for q
    using cong.eps_nfa'_step_eps_closure[OF that] Plus(1,3) cong.nfa'_eps_step_eps_closure[OF _ that(2)]
    by auto
  have "q = q0 \<or> q \<in> left.Q \<or> q \<in> right.Q"
    using Plus(5)
    by (auto simp: NFA.Q_def NFA.SQ_def len_ts dest!: NFA.step_eps_closure_dest)
  moreover have ?case if q_q0: "q = q0"
  proof -
    have "q0 \<noteq> qf"
      using qf_not_in_SQ
      by (auto simp: NFA.SQ_def)
    then obtain q' where q'_def: "base.step_eps bs q q'" "base.step_eps_closure bs q' qf"
      using Plus(5)
      by (auto simp: q_q0 NFA.step_eps_closure_def elim: converse_rtranclpE)
    have fst_step_eps: "base.step_eps [] q q'"
      using q'_def(1)
      by (auto simp: q_q0 NFA.step_eps_def transs_eq)
    have "q' \<in> left.Q \<or> q' \<in> right.Q"
      using q'_def(1)
      by (auto simp: NFA.step_eps_def NFA.Q_def NFA.SQ_def q_q0 transs_eq dest: ts_nonempty split: transition.splits)
    then show ?case
      using fst_step_eps case_left[OF q'_def(2)] case_right[OF q'_def(2)]
      by (auto simp: NFA.step_eps_closure_def)
  qed
  ultimately show ?case
    using Plus(5) case_left case_right
    by auto
next
  case (Times r s)
  obtain phis' where collect: "collect_subfmlas (Times r s) phis =
    collect_subfmlas r phis @ phis'"
    using collect_subfmlas_app by auto
  have transs_def: "transs = build_nfa_impl (Times r s) (q0, qf, phis)"
    using Times unfolding IH_def by (auto simp: Let_def)
  define ts_l where "ts_l = build_nfa_impl r (q0, q0 + state_cnt r, phis)"
  define ts_r where "ts_r = build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)"
  have len_ts: "length ts_l = state_cnt r" "length ts_r = state_cnt s" "length transs = state_cnt r + state_cnt s"
    by (auto simp: ts_l_def ts_r_def transs_def build_nfa_impl_state_cnt)
  have transs_eq: "transs = ts_l @ ts_r"
    by (auto simp: transs_def ts_l_def ts_r_def)
  have ts_nonempty: "ts_l = [] \<Longrightarrow> False" "ts_r = [] \<Longrightarrow> False"
    by (auto simp: ts_l_def ts_r_def build_nfa_impl_not_Nil)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Times r s) (q0, qf, phis))"
    using Times unfolding IH_def by auto
  interpret base: nfa q0 qf transs
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt transs_def by fast+
  interpret left: nfa "q0" "q0 + state_cnt r" ts_l
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt ts_l_def
    by fastforce+
  interpret right: nfa "q0 + state_cnt r" qf ts_r
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt ts_r_def
    by fastforce+
  interpret cong: nfa_cong_Times q0 "q0 + state_cnt r" qf transs ts_l ts_r
    apply unfold_locales
    using NFA.Q_def NFA.SQ_def NFA.step_eps_def NFA.step_symb_def build_nfa_impl_state_set
    by (auto simp add: nth_append build_nfa_impl_state_cnt build_nfa_impl_not_Nil
        state_cnt_pos len_ts transs_eq)
  have "qf \<notin> base.SQ"
    using Times(4)
    by (auto simp: IH_def Let_def)
  then have qf_left_Q: "qf \<in> left.Q \<Longrightarrow> False"
    by (auto simp: NFA.Q_def NFA.SQ_def len_ts state_cnt_pos)
  have left_IH: "IH r q0 (q0 + state_cnt r) phis ts_l bss bs i"
    using left.qf_not_in_SQ Times
    unfolding Let_def IH_def collect
    by (auto simp: nth_append ts_l_def)
  have case_left: "base.step_eps_closure [] q (q0 + state_cnt r)" if "left.step_eps_closure bs q (q0 + state_cnt r)" "q \<in> left.Q" and wf: "wf_regex r" for q
    using that(1) Times(1)[OF wf left_IH] cong.nfa'_step_eps_closure_cong[OF _ that(2)]
    by auto
  have left_IH: "IH s (q0 + state_cnt r) qf (collect_subfmlas r phis) ts_r bss bs i"
    using right.qf_not_in_SQ IH_def Times
    by (auto simp: Let_def ts_r_def)
  then have case_right: "base.step_eps_closure [] q qf" if "base.step_eps_closure bs q qf" "q \<in> right.Q" for q
    using cong.right.eps_nfa'_step_eps_closure[OF that] Times(2,3) cong.right.nfa'_eps_step_eps_closure[OF _ that(2)]
    by auto
  have init_right: "q0 + state_cnt r \<in> right.Q"
    by (auto simp: NFA.Q_def NFA.SQ_def dest: ts_nonempty)
  {
    assume q_left_Q: "q \<in> left.Q"
    then have split: "left.step_eps_closure bs q (q0 + state_cnt r)" "base.step_eps_closure bs (q0 + state_cnt r) qf"
      using cong.eps_nfa'_step_eps_closure_cong[OF Times(5)]
      by (auto dest: qf_left_Q)
    have empty_IH: "IH s (q0 + state_cnt r) qf (collect_subfmlas r phis) ts_r [] bs (i + length bss)"
      using left_IH
      by (auto simp: IH_def Let_def ts_r_def)
    have "right.step_eps_closure bs (q0 + state_cnt r) qf"
      using cong.right.eps_nfa'_step_eps_closure[OF split(2) init_right]
      by auto
    then have "right.run_accept_eps {q0 + state_cnt r} [] bs"
      by (auto simp: NFA.run_accept_eps_def NFA.accept_eps_def NFA.step_eps_closure_set_def NFA.run_def)
    then have wf: "wf_regex r"
      using nfa_correct[OF empty_IH] Times(3) match_refl_eps
      by auto
    have ?case
      using case_left[OF split(1) q_left_Q wf] case_right[OF split(2) init_right]
      by (auto simp: NFA.step_eps_closure_def)
  }
  moreover have "q \<in> left.Q \<or> q \<in> right.Q"
    using Times(5)
    by (auto simp: NFA.Q_def NFA.SQ_def transs_eq len_ts dest!: NFA.step_eps_closure_dest)
  ultimately show ?case
    using case_right[OF Times(5)]
    by auto
next
  case (Star r)
  have transs_def: "transs = build_nfa_impl (Star r) (q0, qf, phis)"
    using Star unfolding IH_def by (auto simp: Let_def)
  obtain ts_r where ts_r: "transs = split_trans (q0 + 1) qf # ts_r" "ts_r = build_nfa_impl r (Suc q0, q0, phis)"
    using Star(3)
    by (auto simp: Let_def IH_def)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 transs"
    using Star unfolding IH_def transs_def by auto
  interpret base: nfa q0 qf transs
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt transs_def
    by fast+
  interpret left: nfa "Suc q0" q0 ts_r
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt ts_r(2)
    by fastforce+
  interpret cong: nfa_cong_Star q0 "Suc q0" qf transs ts_r
    apply unfold_locales
    unfolding NFA.SQ_def build_nfa_impl_state_cnt NFA.step_eps_def NFA.step_symb_def
    by (auto simp add: nth_append build_nfa_impl_state_cnt ts_r(1))
  have IH: "wf_regex r" "IH r (Suc q0) q0 phis ts_r bss bs i"
    using Star(2,3)
    by (auto simp: Let_def IH_def NFA.SQ_def ts_r(2))
  have step_eps_q'_qf: "q' = q0" if "base.step_eps bs q' qf" for q'
  proof (rule ccontr)
    assume "q' \<noteq> q0"
    then have "q' \<in> left.SQ"
      using that
      by (auto simp: NFA.step_eps_def NFA.SQ_def ts_r(1))
    then have "left.step_eps bs q' qf"
      using cong.step_eps_cong_SQ that
      by simp
    then show "False"
      using qf_not_in_SQ
      by (metis NFA.Q_def UnE base.q0_sub_SQ cong.SQ_sub left.step_eps_closed subset_eq)
  qed
  show ?case
  proof (cases "q = qf")
    case False
    then have base_q_q0: "base.step_eps_closure bs q q0" "base.step_eps bs q0 qf"
      using Star(4) step_eps_q'_qf
      by (auto simp: NFA.step_eps_closure_def) (metis rtranclp.cases)+
    have base_Nil_q0_qf: "base.step_eps [] q0 qf"
      by (auto simp: NFA.step_eps_def NFA.SQ_def ts_r(1))
    have q_left_Q: "q \<in> left.Q"
      using base_q_q0
      by (auto simp: NFA.Q_def NFA.SQ_def ts_r(1) dest: step_eps_closure_dest)
    have "left.step_eps_closure [] q q0"
      using cong.eps_nfa'_step_eps_closure_cong[OF base_q_q0(1) q_left_Q] Star(1)[OF IH]
      by auto
    then show ?thesis
      using cong.nfa'_step_eps_closure_cong[OF _ q_left_Q] base_Nil_q0_qf
      by (auto simp: NFA.step_eps_closure_def) (meson rtranclp.rtrancl_into_rtrancl)
  qed (auto simp: NFA.step_eps_closure_def)
qed auto

lemma accept_eps_iff_accept:
  assumes "wf_regex r" "IH r q0 qf phis transs bss bs i"
  shows "NFA.accept_eps q0 qf transs R bs = NFA.accept q0 qf transs R"
  using step_eps_closure_set_empty_list[OF assms] step_eps_closure_set_mono'
  unfolding NFA.accept_eps_def NFA.accept_def
  by (fastforce simp: NFA.accept_eps_def NFA.accept_def NFA.step_eps_closure_set_def)

lemma run_accept_eps_iff_run_accept:
  assumes "wf_regex r" "IH r q0 qf phis transs bss bs i"
  shows "NFA.run_accept_eps q0 qf transs {q0} bss bs \<longleftrightarrow> NFA.run_accept q0 qf transs {q0} bss"
  unfolding NFA.run_accept_eps_def NFA.run_accept_def accept_eps_iff_accept[OF assms] ..

end

definition pred_option' :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "pred_option' P z = (case z of Some z' \<Rightarrow> P z' | None \<Rightarrow> False)"

definition map_option' :: "('b \<Rightarrow> 'c option) \<Rightarrow> 'b option \<Rightarrow> 'c option" where
  "map_option' f z = (case z of Some z' \<Rightarrow> f z' | None \<Rightarrow> None)"

definition while_break :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "while_break P f x = while (pred_option' P) (map_option' f) (Some x)"

lemma wf_while_break:
  assumes "wf {(t, s). P s \<and> b s \<and> Some t = c s}"
  shows "wf {(t, s). pred_option P s \<and> pred_option' b s \<and> t = map_option' c s}"
proof -
  have sub: "{(t, s). pred_option P s \<and> pred_option' b s \<and> t = map_option' c s} \<subseteq>
    map_prod Some Some ` {(t, s). P s \<and> b s \<and> Some t = c s} \<union> ({None} \<times> (Some ` UNIV))"
    by (auto simp: pred_option'_def map_option'_def split: option.splits)
       (smt (z3) case_prodI map_prod_imageI mem_Collect_eq not_Some_eq)
  show ?thesis
    apply (rule wf_subset[OF _ sub])
    apply (rule wf_union_compatible)
      apply (rule wf_map_prod_image)
       apply (fastforce simp: wf_def intro: assms)+
    done
qed

lemma wf_while_break':
  assumes "wf {(t, s). P s \<and> b s \<and> Some t = c s}"
  shows "wf {(t, s). pred_option' P s \<and> pred_option' b s \<and> t = map_option' c s}"
  by (rule wf_subset[OF wf_while_break[OF assms]]) (auto simp: pred_option'_def split: option.splits)

lemma while_break_sound:
  assumes "\<And>s s'. P s \<Longrightarrow> b s \<Longrightarrow> c s = Some s' \<Longrightarrow> P s'" "\<And>s. P s \<Longrightarrow> \<not> b s \<Longrightarrow> Q s" "wf {(t, s). P s \<and> b s \<and> Some t = c s}" "P s"
  shows "pred_option Q (while_break b c s)"
proof -
  have aux: "P t \<Longrightarrow> b t \<Longrightarrow> pred_option P (c t)" for t
    using assms(1)
    by (cases "c t") auto
  show ?thesis
    using assms aux
    by (auto simp: while_break_def pred_option'_def map_option'_def split: option.splits
        intro!: while_rule_lemma[where ?P="pred_option P" and ?Q="pred_option Q" and ?b="pred_option' b" and ?c="map_option' c", OF _ _ wf_while_break])
qed

lemma while_break_complete: "(\<And>s. P s \<Longrightarrow> b s \<Longrightarrow> pred_option' P (c s)) \<Longrightarrow> (\<And>s. P s \<Longrightarrow> \<not> b s \<Longrightarrow> Q s) \<Longrightarrow> wf {(t, s). P s \<and> b s \<and> Some t = c s} \<Longrightarrow> P s \<Longrightarrow>
  pred_option' Q (while_break b c s)"
  unfolding while_break_def
  by (rule while_rule_lemma[where ?P="pred_option' P" and ?Q="pred_option' Q" and ?b="pred_option' b" and ?c="map_option' c", OF _ _ wf_while_break'])
     (force simp: pred_option'_def map_option'_def split: option.splits elim!: case_optionE)+

context
  fixes args :: "(bool iarray, nat set, 'd :: timestamp, 't, 'e) args"
begin

abbreviation "reach_w \<equiv> reach_window args"

qualified definition "in_win = init_window args"

definition valid_window_matchP :: "'d \<I> \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow>
  ('d \<times> bool iarray) list \<Rightarrow> nat \<Rightarrow> (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow> bool" where
  "valid_window_matchP I t0 sub rho j w \<longleftrightarrow> j = w_j w \<and>
    valid_window args t0 sub rho w \<and>
    reach_w t0 sub rho (w_i w, w_ti w, w_si w, w_j w, w_tj w, w_sj w) \<and>
    (case w_read_t args (w_tj w) of None \<Rightarrow> True
    | Some t \<Rightarrow> (\<forall>l < w_i w. memL (ts_at rho l) t I))"

lemma valid_window_matchP_reach_tj: "valid_window_matchP I t0 sub rho i w \<Longrightarrow>
  reaches_on (w_run_t args) t0 (map fst rho) (w_tj w)"
  using reach_window_run_tj
  by (fastforce simp: valid_window_matchP_def simp del: reach_window.simps)

lemma valid_window_matchP_reach_sj: "valid_window_matchP I t0 sub rho i w \<Longrightarrow>
  reaches_on (w_run_sub args) sub (map snd rho) (w_sj w)"
  using reach_window_run_sj
  by (fastforce simp: valid_window_matchP_def simp del: reach_window.simps)

lemma valid_window_matchP_len_rho: "valid_window_matchP I t0 sub rho i w \<Longrightarrow> length rho = i"
  by (auto simp: valid_window_matchP_def)

definition "matchP_loop_cond I t = (\<lambda>w. w_i w < w_j w \<and> memL (the (w_read_t args (w_ti w))) t I)"

definition "matchP_loop_inv I t0 sub rho j0 tj0 sj0 t =
  (\<lambda>w. valid_window args t0 sub rho w \<and>
    w_j w = j0 \<and> w_tj w = tj0 \<and> w_sj w = sj0 \<and> (\<forall>l < w_i w. memL (ts_at rho l) t I))"

fun ex_key :: "('c, 'd) mmap \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow>
  ('c \<Rightarrow> bool) \<Rightarrow> ('c, bool) mapping \<Rightarrow> (bool \<times> ('c, bool) mapping)" where
  "ex_key [] time accept ac = (False, ac)"
| "ex_key ((q, t) # qts) time accept ac = (if time t then
    (case cac accept ac q of (\<beta>, ac') \<Rightarrow>
    if \<beta> then (True, ac') else ex_key qts time accept ac')
  else ex_key qts time accept ac)"

lemma ex_key_sound:
  assumes inv: "\<And>q. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v"
  and distinct: "distinct (map fst qts)"
  and eval: "ex_key qts time accept ac = (b, ac')"
  shows "b = (\<exists>q \<in> mmap_keys qts. time (the (mmap_lookup qts q)) \<and> accept q) \<and>
    (\<forall>q. case Mapping.lookup ac' q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v)"
  using assms
proof (induction qts arbitrary: ac)
  case (Cons a qts)
  obtain q t where qt_def: "a = (q, t)"
    by fastforce
  show ?case
  proof (cases "time t")
    case True
    note time_t = True
    obtain \<beta> ac'' where ac''_def: "cac accept ac q = (\<beta>, ac'')"
      by fastforce
    have accept: "\<beta> = accept q" "\<And>q. case Mapping.lookup ac'' q of None \<Rightarrow> True
      | Some v \<Rightarrow> accept q = v"
      using ac''_def Cons(2)
      by (fastforce simp: cac_def Let_def Mapping.lookup_update' split: option.splits if_splits)+
    show ?thesis
    proof (cases \<beta>)
      case True
      then show ?thesis
        using accept(2) time_t Cons(4)
        by (auto simp: qt_def mmap_keys_def accept(1) mmap_lookup_def ac''_def)
    next
      case False
      have ex_key: "ex_key qts time accept ac'' = (b, ac')"
        using Cons(4) time_t False
        by (auto simp: qt_def ac''_def)
      show ?thesis
        using Cons(1)[OF accept(2) _ ex_key] False[unfolded accept(1)] Cons(3)
        by (auto simp: mmap_keys_def mmap_lookup_def qt_def)
    qed
  next
    case False
    have ex_key: "ex_key qts time accept ac = (b, ac')"
      using Cons(4) False
      by (auto simp: qt_def)
    show ?thesis
      using Cons(1)[OF Cons(2) _ ex_key] False Cons(3)
      by (auto simp: mmap_keys_def mmap_lookup_def qt_def)
  qed
qed (auto simp: mmap_keys_def)

fun eval_matchP :: "'d \<I> \<Rightarrow> (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow>
  (('d \<times> bool) \<times> (bool iarray, nat set, 'd, 't, 'e) window) option" where
  "eval_matchP I w =
    (case w_read_t args (w_tj w) of None \<Rightarrow> None | Some t \<Rightarrow>
      (case adv_end args w of None \<Rightarrow> None | Some w' \<Rightarrow>
        let w'' = while (matchP_loop_cond I t) (adv_start args) w';
        (\<beta>, ac') = ex_key (w_e w'') (\<lambda>t'. memR t' t I) (w_accept args) (w_ac w'') in
        Some ((t, \<beta>), w''\<lparr>w_ac := ac'\<rparr>)))"

definition valid_window_matchF :: "'d \<I> \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> ('d \<times> bool iarray) list \<Rightarrow> nat \<Rightarrow>
  (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow> bool" where
  "valid_window_matchF I t0 sub rho i w \<longleftrightarrow> i = w_i w \<and>
    valid_window args t0 sub rho w \<and>
    reach_w t0 sub rho (w_i w, w_ti w, w_si w, w_j w, w_tj w, w_sj w) \<and>
    (\<forall>l \<in> {w_i w..<w_j w}. memR (ts_at rho i) (ts_at rho l) I)"

lemma valid_window_matchF_reach_tj: "valid_window_matchF I t0 sub rho i w \<Longrightarrow>
  reaches_on (w_run_t args) t0 (map fst rho) (w_tj w)"
  using reach_window_run_tj
  by (fastforce simp: valid_window_matchF_def simp del: reach_window.simps)

lemma valid_window_matchF_reach_sj: "valid_window_matchF I t0 sub rho i w \<Longrightarrow>
  reaches_on (w_run_sub args) sub (map snd rho) (w_sj w)"
  using reach_window_run_sj
  by (fastforce simp: valid_window_matchF_def simp del: reach_window.simps)

definition "matchF_loop_cond I t =
  (\<lambda>w. case w_read_t args (w_tj w) of None \<Rightarrow> False | Some t' \<Rightarrow> memR t t' I)"

definition "matchF_loop_inv I t0 sub rho i ti si tjm sjm =
  (\<lambda>w. valid_window args t0 sub (take (w_j w) rho) w \<and>
  w_i w = i \<and> w_ti w = ti \<and> w_si w = si \<and>
  reach_window args t0 sub rho (w_j w, w_tj w, w_sj w, length rho, tjm, sjm) \<and>
  (\<forall>l \<in> {w_i w..<w_j w}. memR (ts_at rho i) (ts_at rho l) I))"

definition "matchF_loop_inv' t0 sub rho i ti si j tj sj =
  (\<lambda>w. w_i w = i \<and> w_ti w = ti \<and> w_si w = si \<and>
    (\<exists>rho'. valid_window args t0 sub (rho @ rho') w \<and>
    reach_window args t0 sub (rho @ rho') (j, tj, sj, w_j w, w_tj w, w_sj w)))"

fun eval_matchF :: "'d \<I> \<Rightarrow> (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow>
  (('d \<times> bool) \<times> (bool iarray, nat set, 'd, 't, 'e) window) option" where
  "eval_matchF I w =
    (case w_read_t args (w_ti w) of None \<Rightarrow> None | Some t \<Rightarrow>
      (case while_break (matchF_loop_cond I t) (adv_end args) w of None \<Rightarrow> None | Some w' \<Rightarrow>
        (case w_read_t args (w_tj w') of None \<Rightarrow> None | Some t' \<Rightarrow>
          let \<beta> = (case snd (the (mmap_lookup (w_s w') {0})) of None \<Rightarrow> False
            | Some tstp \<Rightarrow> memL t (fst tstp) I) in
          Some ((t, \<beta>), adv_start args w'))))"

end

locale MDL_window = MDL \<sigma>
  for \<sigma> :: "('a, 'd :: timestamp) trace" +
  fixes r :: "('a, 'd :: timestamp) regex"
    and t0 :: 't
    and sub :: 'e
    and args :: "(bool iarray, nat set, 'd, 't, 'e) args"
  assumes init_def: "w_init args = {0 :: nat}"
    and step_def: "w_step args =
      NFA.delta' (IArray (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r)"
    and accept_def: "w_accept args = NFA.accept' (IArray (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r)"
    and run_t_sound: "reaches_on (w_run_t args) t0 ts t \<Longrightarrow>
      w_run_t args t = Some (t', x) \<Longrightarrow> x = \<tau> \<sigma> (length ts)"
    and run_sub_sound: "reaches_on (w_run_sub args) sub bs s \<Longrightarrow>
      w_run_sub args s = Some (s', b) \<Longrightarrow>
      b = IArray (map (\<lambda>phi. sat phi (length bs)) (collect_subfmlas r []))"
    and run_t_read: "w_run_t args t = Some (t', x) \<Longrightarrow> w_read_t args t = Some x"
    and read_t_run: "w_read_t args t = Some x \<Longrightarrow> \<exists>t'. w_run_t args t = Some (t', x)"
begin

definition "qf = state_cnt r"
definition "transs = build_nfa_impl r (0, qf, [])"

abbreviation "init \<equiv> w_init args"
abbreviation "step \<equiv> w_step args"
abbreviation "accept \<equiv> w_accept args"
abbreviation "run \<equiv> NFA.run' (IArray transs) qf"
abbreviation "wacc \<equiv> Window.acc (w_step args) (w_accept args)"
abbreviation "rw \<equiv> reach_window args"

abbreviation "valid_matchP \<equiv> valid_window_matchP args"
abbreviation "eval_mP \<equiv> eval_matchP args"
abbreviation "matchP_inv \<equiv> matchP_loop_inv args"
abbreviation "matchP_cond \<equiv> matchP_loop_cond args"

abbreviation "valid_matchF \<equiv> valid_window_matchF args"
abbreviation "eval_mF \<equiv> eval_matchF args"
abbreviation "matchF_inv \<equiv> matchF_loop_inv args"
abbreviation "matchF_inv' \<equiv> matchF_loop_inv' args"
abbreviation "matchF_cond \<equiv> matchF_loop_cond args"

lemma run_t_sound':
  assumes "reaches_on (w_run_t args) t0 ts t" "i < length ts"
  shows "ts ! i = \<tau> \<sigma> i"
proof -
  obtain t' t'' where t'_def: "reaches_on (w_run_t args) t0 (take i ts) t'"
    "w_run_t args t' = Some (t'', ts ! i)"
    using reaches_on_split[OF assms]
    by auto
  show ?thesis
    using run_t_sound[OF t'_def] assms(2)
    by simp
qed

lemma run_sub_sound':
  assumes "reaches_on (w_run_sub args) sub bs s" "i < length bs"
  shows "bs ! i = IArray (map (\<lambda>phi. sat phi i) (collect_subfmlas r []))"
proof -
  obtain s' s'' where s'_def: "reaches_on (w_run_sub args) sub (take i bs) s'"
    "w_run_sub args s' = Some (s'', bs ! i)"
    using reaches_on_split[OF assms]
    by auto
  show ?thesis
    using run_sub_sound[OF s'_def] assms(2)
    by simp
qed

lemma run_ts: "reaches_on (w_run_t args) t ts t' \<Longrightarrow> t = t0 \<Longrightarrow> chain_le ts"
proof (induction t ts t' rule: reaches_on_rev_induct)
  case (2 s s' v vs s'')
  show ?case
  proof (cases vs rule: rev_cases)
    case (snoc zs z)
    show ?thesis
      using 2(3)[OF 2(4)]
      using chain_le_app[OF _ \<tau>_mono[of "length zs" "Suc (length zs)" \<sigma>]]
        run_t_sound'[OF reaches_on_app[OF 2(1,2), unfolded 2(4)], of "length zs"]
        run_t_sound'[OF reaches_on_app[OF 2(1,2), unfolded 2(4)], of "Suc (length zs)"]
      unfolding snoc
      by (auto simp: nth_append)
  qed (auto intro: chain_le.intros)
qed (auto intro: chain_le.intros)

lemma ts_at_tau: "reaches_on (w_run_t args) t0 (map fst rho) t \<Longrightarrow> i < length rho \<Longrightarrow>
  ts_at rho i = \<tau> \<sigma> i"
  using run_t_sound'
  unfolding ts_at_def
  by fastforce

lemma length_bs_at: "reaches_on (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i < length rho \<Longrightarrow>
  IArray.length (bs_at rho i) = length (collect_subfmlas r [])"
  using run_sub_sound'
  unfolding bs_at_def
  by fastforce

lemma bs_at_nth: "reaches_on (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i < length rho \<Longrightarrow>
  n < IArray.length (bs_at rho i) \<Longrightarrow>
  IArray.sub (bs_at rho i) n \<longleftrightarrow> sat (collect_subfmlas r [] ! n) i"
  using run_sub_sound'
  unfolding bs_at_def
  by fastforce

lemma ts_at_mono: "\<And>i j. reaches_on (w_run_t args) t0 (map fst rho) t \<Longrightarrow>
  i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
  using ts_at_tau
  by fastforce

lemma steps_is_run: "steps (w_step args) rho q ij = run q (sub_bs rho ij)"
  unfolding NFA.run'_def steps_def step_def transs_def qf_def ..

lemma acc_is_accept: "wacc rho q (i, j) = w_accept args (run q (sub_bs rho (i, j)))"
  unfolding acc_def steps_is_run by auto

lemma iarray_list_of: "IArray (IArray.list_of xs) = xs"
  by (cases xs) auto

lemma map_iarray_list_of: "map IArray (map IArray.list_of bss) = bss"
  using iarray_list_of
  by (induction bss) auto

lemma acc_match:
  fixes ts :: "'d list"
  assumes "reaches_on (w_run_sub args) sub (map snd rho) s" "i \<le> j" "j \<le> length rho" "wf_regex r"
  shows "wacc rho {0} (i, j) \<longleftrightarrow> (i, j) \<in> match r"
proof -
  have j_eq: "j = i + length (sub_bs rho (i, j))"
    using assms by auto
  define bs where "bs = map (\<lambda>phi. sat phi j) (collect_subfmlas r [])"
  have IH: "IH r 0 qf [] transs (map IArray.list_of (sub_bs rho (i, j))) bs i"
    unfolding IH_def transs_def qf_def NFA.SQ_def build_nfa_impl_state_cnt bs_def
    using assms run_sub_sound bs_at_nth length_bs_at by fastforce
  interpret NFA_array: nfa_array transs "IArray transs" qf
    by unfold_locales (auto simp: qf_def transs_def build_nfa_impl_state_cnt)
  have run_run': "NFA_array.run R (map IArray.list_of (sub_bs rho (i, j))) = NFA_array.run' R (sub_bs rho (i, j))" for R
    using NFA_array.run'_eq[of "sub_bs rho (i, j)" "map IArray.list_of (sub_bs rho (i, j))"]
    unfolding map_iarray_list_of
    by auto
  show ?thesis
    using nfa_correct[OF IH, unfolded NFA.run_accept_def]
    unfolding run_accept_eps_iff_run_accept[OF assms(4) IH] acc_is_accept NFA.run_accept_def run_run' NFA_array.accept'_eq
    by (simp add: j_eq[symmetric] accept_def assms(2) qf_def transs_def)
qed

lemma accept_match:
  fixes ts :: "'d list"
  shows "reaches_on (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i \<le> j \<Longrightarrow> j \<le> length rho \<Longrightarrow> wf_regex r \<Longrightarrow>
  w_accept args (steps (w_step args) rho {0} (i, j)) \<longleftrightarrow> (i, j) \<in> match r"
  using acc_match acc_is_accept steps_is_run
  by metis

lemma drop_take_drop: "i \<le> j \<Longrightarrow> j \<le> length rho \<Longrightarrow> drop i (take j rho) @ drop j rho = drop i rho"
  apply (induction i arbitrary: j rho)
  by auto (metis append_take_drop_id diff_add drop_drop drop_take)

lemma take_Suc: "drop n xs = y # ys \<Longrightarrow> take n xs @ [y] = take (Suc n) xs"
  by (metis drop_all list.distinct(1) list.sel(1) not_less take_hd_drop)

lemma valid_init_matchP: "valid_matchP I t0 sub [] 0 (init_window args t0 sub)"
  using valid_init_window
  by (fastforce simp: valid_window_matchP_def Let_def intro: reaches_on.intros split: option.splits)

lemma valid_init_matchF: "valid_matchF I t0 sub [] 0 (init_window args t0 sub)"
  using valid_init_window
  by (fastforce simp: valid_window_matchF_def Let_def intro: reaches_on.intros split: option.splits)

lemma valid_eval_matchP:
  assumes valid_before': "valid_matchP I t0 sub rho j w"
    and before_end: "w_run_t args (w_tj w) = Some (tj''', t)" "w_run_sub args (w_sj w) = Some (sj''', b)"
    and wf: "wf_regex r"
  shows "\<exists>w'. eval_mP I w = Some ((\<tau> \<sigma> j, sat (MatchP I r) j), w') \<and>
    t = \<tau> \<sigma> j \<and> valid_matchP I t0 sub (rho @ [(t, b)]) (Suc j) w'"
proof -
  obtain w' where w'_def: "adv_end args w = Some w'"
    using before_end
    by (fastforce simp: adv_end_def Let_def split: prod.splits)
  define st where "st = w_st w'"
  define i where "i = w_i w'"
  define ti where "ti = w_ti w'"
  define si where "si = w_si w'"
  define tj where "tj = w_tj w'"
  define sj where "sj = w_sj w'"
  define s where "s = w_s w'"
  define e where "e = w_e w'"
  define rho' where "rho' = rho @ [(t, b)]"
  have reaches_on': "reaches_on (w_run_t args) t0 (map fst rho') tj'''"
    using valid_before' reach_window_run_tj[OF reach_window_app[OF _ before_end]]
    by (auto simp: valid_window_matchP_def rho'_def)
  have rho_mono: "\<And>t'. t' \<in> set (map fst rho) \<Longrightarrow> t' \<le> t"
    using ts_at_mono[OF reaches_on'] nat_less_le
    by (fastforce simp: rho'_def ts_at_def nth_append in_set_conv_nth split: list.splits)
  have valid_adv_end_w: "valid_window args t0 sub rho' w'"
    using valid_before' valid_adv_end[OF _ before_end rho_mono]
    by (auto simp: valid_window_matchP_def rho'_def w'_def)
  have w_ij_adv_end: "w_i w' = w_i w" "w_j w' = Suc j"
    using valid_before' w'_def
    by (auto simp: valid_window_matchP_def adv_end_def Let_def before_end split: prod.splits)
  have valid_before: "rw t0 sub rho' (i, ti, si, Suc j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho' \<Longrightarrow> ts_at rho' i \<le> ts_at rho' j"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho' i (Suc j) q"
    "valid_s init step st accept rho' i i (Suc j) s"
    "w_j w' = Suc j" "i \<le> Suc j"
    using valid_adv_end_w
    unfolding valid_window_def Let_def ti_def si_def i_def tj_def sj_def s_def e_def w_ij_adv_end st_def
    by auto
  note read_t_def = run_t_read[OF before_end(1)]
  have t_props: "\<forall>l < i. memL (ts_at rho' l) t I"
    using valid_before'
    by (auto simp: valid_window_matchP_def i_def w_ij_adv_end read_t_def rho'_def ts_at_def nth_append)

  note reaches_on_tj = reach_window_run_tj[OF valid_before(1)]
  note reaches_on_sj = reach_window_run_sj[OF valid_before(1)]
  have length_rho': "length rho' = Suc j" "length rho = j"
    using valid_before
    by (auto simp: rho'_def)
  have j_len_rho': "j < length rho'"
    by (auto simp: length_rho')
  have tj_eq: "t = \<tau> \<sigma> j" "t = ts_at rho' j"
    using run_t_sound'[OF reaches_on_tj, of j]
    by (auto simp: rho'_def length_rho' nth_append ts_at_def)
  have bj_def: "b = bs_at rho' j"
    using run_sub_sound'[OF reaches_on_sj, of j]
    by (auto simp: rho'_def length_rho' nth_append bs_at_def)
  define w'' where loop_def: "w'' = while (matchP_cond I t) (adv_start args) w'"
  have inv_before: "matchP_inv I t0 sub rho' (Suc j) tj sj t w'"
    using valid_adv_end_w valid_before t_props
    unfolding matchP_loop_inv_def
    by (auto simp: tj_def sj_def i_def)
  have loop: "matchP_inv I t0 sub rho' (Suc j) tj sj t w'' \<and> \<not>matchP_cond I t w''"
    unfolding loop_def
  proof (rule while_rule_lemma[of "matchP_inv I t0 sub rho' (Suc j) tj sj t"])
    fix w_cur :: "(bool iarray, nat set, 'd, 't, 'e) window"
    assume assms: "matchP_inv I t0 sub rho' (Suc j) tj sj t w_cur" "matchP_cond I t w_cur"
    define st_cur where "st_cur = w_st w_cur"
    define i_cur where "i_cur = w_i w_cur"
    define ti_cur where "ti_cur = w_ti w_cur"
    define si_cur where "si_cur = w_si w_cur"
    define s_cur where "s_cur = w_s w_cur"
    define e_cur where "e_cur = w_e w_cur"
    have valid_loop: "rw t0 sub rho' (i_cur, ti_cur, si_cur, Suc j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho' \<Longrightarrow> ts_at rho' i \<le> ts_at rho' j"
    "\<forall>q. mmap_lookup e_cur q = sup_leadsto init step rho' i_cur (Suc j) q"
    "valid_s init step st_cur accept rho' i_cur i_cur (Suc j) s_cur"
    "w_j w_cur = Suc j"
      using assms(1)[unfolded matchP_loop_inv_def valid_window_matchP_def] valid_before(6)
        ti_cur_def si_cur_def i_cur_def s_cur_def e_cur_def
      by (auto simp: valid_window_def Let_def init_def step_def st_cur_def accept_def
          split: option.splits)
    obtain ti'_cur si'_cur t_cur b_cur where run_si_cur:
      "w_run_t args ti_cur = Some (ti'_cur, t_cur)" "w_run_sub args si_cur = Some (si'_cur, b_cur)"
      "t_cur = ts_at rho' i_cur" "b_cur = bs_at rho' i_cur"
      using assms(2) reach_window_run_si[OF valid_loop(1)] reach_window_run_ti[OF valid_loop(1)]
      unfolding matchP_loop_cond_def valid_loop(5) i_cur_def
      by auto
    have "\<And>l. l < i_cur \<Longrightarrow> memL (ts_at rho' l) t I"
      using assms(1)
      unfolding matchP_loop_inv_def i_cur_def
      by auto
    then have "\<And>l. l < Suc (i_cur) \<Longrightarrow> memL (ts_at rho' l) t I"
      using assms(2) run_t_read[OF run_si_cur(1), unfolded run_si_cur(3)]
      unfolding matchP_loop_cond_def i_cur_def ti_cur_def
      by (auto simp: less_Suc_eq)
    then show "matchP_inv I t0 sub rho' (Suc j) tj sj t (adv_start args w_cur)"
      using assms i_cur_def valid_adv_start valid_adv_start_bounds
      unfolding matchP_loop_inv_def matchP_loop_cond_def
      by fastforce
  next
    {
      fix w1 w2
      assume lassms: "matchP_inv I t0 sub rho' (Suc j) tj sj t w1" "matchP_cond I t w1"
        "w2 = adv_start args w1"
      define i_cur where "i_cur = w_i w1"
      define ti_cur where "ti_cur = w_ti w1"
      define si_cur where "si_cur = w_si w1"
      have valid_loop: "rw t0 sub rho' (i_cur, ti_cur, si_cur, Suc j, tj, sj)" "w_j w1 = Suc j"
        using lassms(1)[unfolded matchP_loop_inv_def valid_window_matchP_def] valid_before(6)
          ti_cur_def si_cur_def i_cur_def
        by (auto simp: valid_window_def Let_def)
      obtain ti'_cur si'_cur t_cur b_cur where run_si_cur:
        "w_run_t args ti_cur = Some (ti'_cur, t_cur)"
        "w_run_sub args si_cur = Some (si'_cur, b_cur)"
        using lassms(2) reach_window_run_si[OF valid_loop(1)] reach_window_run_ti[OF valid_loop(1)]
        unfolding matchP_loop_cond_def valid_loop i_cur_def
        by auto
      have w1_ij: "w_i w1 < Suc j" "w_j w1 = Suc j"
        using lassms
        unfolding matchP_loop_inv_def matchP_loop_cond_def
        by auto
      have w2_ij: "w_i w2 = Suc (w_i w1)" "w_j w2 = Suc j"
        using w1_ij lassms(3) run_si_cur(1,2)
        unfolding ti_cur_def si_cur_def
        by (auto simp: adv_start_def Let_def split: option.splits prod.splits if_splits)
      have "w_j w2 - w_i w2 < w_j w1 - w_i w1"
        using w1_ij w2_ij
        by auto
    }
    then have "{(s', s). matchP_inv I t0 sub rho' (Suc j) tj sj t s \<and> matchP_cond I t s \<and>
      s' = adv_start args s} \<subseteq> measure (\<lambda>w. w_j w - w_i w)"
      by auto
    then show "wf {(s', s). matchP_inv I t0 sub rho' (Suc j) tj sj t s \<and> matchP_cond I t s \<and>
      s' = adv_start args s}"
      using wf_measure wf_subset by auto
  qed (auto simp: inv_before)
  have valid_w': "valid_window args t0 sub rho' w''"
    using conjunct1[OF loop]
    unfolding matchP_loop_inv_def
    by auto
  have w_tsj_w': "w_tj w'' = tj" "w_sj w'' = sj" "w_j w'' = Suc j"
    using loop
    by (auto simp: matchP_loop_inv_def)
  define st' where "st' = w_st w''"
  define ac where "ac = w_ac w''"
  define i' where "i' = w_i w''"
  define ti' where "ti' = w_ti w''"
  define si' where "si' = w_si w''"
  define s' where "s' = w_s w''"
  define e' where "e' = w_e w''"
  define tj' where "tj' = w_tj w''"
  define sj' where "sj' = w_sj w''"
  have i'_le_Suc_j: "i' \<le> Suc j"
    using loop
    unfolding matchP_loop_inv_def
    by (auto simp: valid_window_def Let_def i'_def)
  have valid_after: "rw t0 sub rho' (i', ti', si', Suc j, tj', sj')"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho' \<Longrightarrow> ts_at rho' i \<le> ts_at rho' j"
    "distinct (map fst e')"
    "\<forall>q. mmap_lookup e' q = sup_leadsto init step rho' i' (Suc j) q"
    "\<And>q. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v"
    "valid_s init step st' accept rho' i' i' (Suc j) s'" "i' \<le> Suc j" "Suc j \<le> length rho'"
    using valid_w' i'_le_Suc_j
    unfolding valid_window_def Let_def i'_def ti'_def si'_def s'_def e'_def tj'_def sj'_def ac_def st'_def w_tsj_w'
    by auto
  note lookup_e' = valid_after(3,4,5,6)
  obtain \<beta> ac' where ac'_def: "ex_key e' (\<lambda>t'. memR t' t I)
    (w_accept args) ac = (\<beta>, ac')"
    by fastforce
  have \<beta>_def: "\<beta> = (\<exists>q\<in>mmap_keys e'. memR (the (mmap_lookup e' q)) t I \<and> accept q)"
    "\<And>q. case Mapping.lookup ac' q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v"
    using ex_key_sound[OF valid_after(5) valid_after(3) ac'_def]
    by auto
  have i'_set: "\<And>l. l < w_i w'' \<Longrightarrow> memL (ts_at rho' l) (ts_at rho' j) I"
    using loop length_rho' i'_le_Suc_j
    unfolding matchP_loop_inv_def
    by (auto simp: ts_at_def rho'_def nth_append i'_def)
  have b_alt: "(\<exists>q \<in> mmap_keys e'. memR (the (mmap_lookup e' q)) t I \<and> accept q) \<longleftrightarrow> sat (MatchP I r) j"
  proof (rule iffI)
    assume "\<exists>q \<in> mmap_keys e'. memR (the (mmap_lookup e' q)) t I \<and> accept q"
    then obtain q where q_def: "q \<in> mmap_keys e'"
      "memR (the (mmap_lookup e' q)) t I" "accept q"
      by auto
    then obtain ts' where ts_def: "mmap_lookup e' q = Some ts'"
      by (auto dest: Mapping_keys_dest)
    have "sup_leadsto init step rho' i' (Suc j) q = Some ts'"
      using lookup_e' ts_def q_def valid_after(4,7,8)
      by (auto simp: rho'_def sup_leadsto_app_cong)
    then obtain l where l_def: "l < i'" "steps step rho' init (l,  Suc j) = q"
      "ts_at rho' l = ts'"
      using sup_leadsto_SomeE[OF i'_le_Suc_j]
      unfolding i'_def
      by fastforce
    have l_le_j: "l \<le> j" and l_le_Suc_j: "l \<le> Suc j"
      using l_def(1) i'_le_Suc_j
      by (auto simp: i'_def)
    have tau_l: "l < j \<Longrightarrow> fst (rho ! l) = \<tau> \<sigma> l"
      using run_t_sound'[OF reaches_on_tj, of l] length_rho'
      by (auto simp: rho'_def nth_append)
    have tau_l_left: "memL ts' t I"
      unfolding l_def(3)[symmetric] tj_eq(2)
      using i'_set l_def(1)
      by (auto simp: i'_def)
    have "(l, Suc j) \<in> match r"
      using accept_match[OF reaches_on_sj l_le_Suc_j _ wf] q_def(3) length_rho' init_def l_def(2)
        rho'_def
      by auto
    then show "sat (MatchP I r) j"
      using l_le_j q_def(2) ts_at_tau[OF reaches_on_tj] tau_l_left
      by (auto simp: mem_def tj_eq rho'_def ts_def l_def(3)[symmetric] tau_l tj_def ts_at_def
          nth_append length_rho' intro: exI[of _ l] split: if_splits)
  next
    assume "sat (MatchP I r) j"
    then obtain l where l_def: "l \<le> j" "l \<le> Suc j" "mem (\<tau> \<sigma> l) (\<tau> \<sigma> j) I" "(l, Suc j) \<in> match r"
      by auto
    show "(\<exists>q\<in>mmap_keys e'. memR (the (mmap_lookup e' q)) t I \<and> accept q)"
    proof -
      have l_lt_j: "l < Suc j"
        using l_def(1) by auto
      then have ts_at_l_j: "ts_at rho' l \<le> ts_at rho' j"
        using ts_at_mono[OF reaches_on' _ j_len_rho']
        by (auto simp: rho'_def length_rho')
      have ts_j_l: "memL (ts_at rho' l) (ts_at rho' j) I"
        using l_def(3) ts_at_tau[OF reaches_on_tj] l_lt_j length_rho' tj_eq
        unfolding rho'_def mem_def
        by auto
      have "i' = Suc j \<or> \<not>memL (ts_at rho' i') (ts_at rho' j) I"
      proof (rule Meson.disj_comm, rule disjCI)
        assume "i' \<noteq> Suc j"
        then have i'_j: "i' < Suc j"
          using valid_after
          by auto
        obtain t' b' where tbi_cur_def: "w_read_t args ti' = Some t'"
          "t' = ts_at rho' i'" "b' = bs_at rho' i'"
          using reach_window_run_ti[OF valid_after(1) i'_j]
            reach_window_run_si[OF valid_after(1) i'_j] run_t_read
          by auto
        show "\<not>memL (ts_at rho' i') (ts_at rho' j) I"
          using loop tbi_cur_def(1) i'_j length_rho'
          unfolding matchP_loop_inv_def matchP_loop_cond_def tj_eq(2) ti'_def[symmetric]
          by (auto simp: i'_def tbi_cur_def)
      qed
      then have l_lt_i': "l < i'"
      proof (rule disjE)
        assume assm: "\<not>memL (ts_at rho' i') (ts_at rho' j) I"
        show "l < i'"
        proof (rule ccontr)
          assume "\<not>l < i'"
          then have ts_at_i'_l: "ts_at rho' i' \<le> ts_at rho' l"
            using ts_at_mono[OF reaches_on'] l_lt_j length_rho'
            by (auto simp: rho'_def length_rho')
          show False
            using assm memL_mono[OF ts_j_l ts_at_i'_l]
            by auto
        qed
      qed (auto simp add: l_lt_j)
      define q where q_def: "q = steps step rho' init (l, Suc j)"
      then obtain l' where l'_def: "sup_leadsto init step rho' i' (Suc j) q = Some (ts_at rho' l')"
        "l \<le> l'" "l' < i'"
        using sup_leadsto_SomeI[OF l_lt_i'] by fastforce
      have ts_j_l': "memR (ts_at rho' l') (ts_at rho' j) I"
      proof -
        have ts_at_l_l': "ts_at rho' l \<le> ts_at rho' l'"
          using ts_at_mono[OF reaches_on' l'_def(2)] l'_def(3) valid_after(4,7,8)
          by (auto simp add: rho'_def length_rho' dual_order.order_iff_strict)
        show ?thesis
          using l_def(3) memR_mono[OF _ ts_at_l_l']
            ts_at_tau[OF reaches_on_tj] l'_def(2,3) valid_after(4,7,8)
          by (auto simp: mem_def rho'_def length_rho')
      qed
      have lookup_e'_q: "mmap_lookup e' q = Some (ts_at rho' l')"
        using lookup_e' l'_def(1) valid_after(4,7,8)
        by (auto simp: rho'_def sup_leadsto_app_cong)
      show ?thesis
        using accept_match[OF reaches_on_sj l_def(2) _ wf] l_def(4) ts_j_l' lookup_e'_q tj_eq(2)
        by (auto simp: bs_at_def nth_append init_def length_rho'(1) q_def intro!: bexI[of _ q] Mapping_keys_intro)
    qed
  qed
  have read_tj_Some: "\<And>t' l. w_read_t args tj = Some t' \<Longrightarrow> l < i' \<Longrightarrow> memL (ts_at rho' l) t' I"
  proof -
    fix t' l
    assume lassms: "(w_read_t args) tj = Some t'" "l < i'"
    obtain tj'''' where reaches_on_tj'''':
      "reaches_on (w_run_t args) t0 (map fst (rho' @ [(t', undefined)])) tj''''"
      using reaches_on_app[OF reaches_on_tj] read_t_run[OF lassms(1)]
      by auto
    have "t \<le> t'"
      using ts_at_mono[OF reaches_on_tj'''', of "length rho" "length rho'"]
      by (auto simp: ts_at_def nth_append rho'_def)
    then show "memL (ts_at rho' l) t' I"
      using memL_mono' lassms(2) loop
      unfolding matchP_loop_inv_def
      by (fastforce simp: i'_def)
  qed
  define w''' where "w''' = w''\<lparr>w_ac := ac'\<rparr>"
  have "rw t0 sub rho' (w_i w''', w_ti w''', w_si w''', w_j w''', w_tj w''', w_sj w''')"
    using valid_after(1)
    by (auto simp del: reach_window.simps simp: w'''_def i'_def ti'_def si'_def tj'_def sj'_def w_tsj_w')
  moreover have "valid_window args t0 sub rho' w'''"
    using valid_w'
    by (auto simp: w'''_def valid_window_def Let_def \<beta>_def(2))
  ultimately have "valid_matchP I t0 sub rho' (Suc j) w'''"
    using i'_set read_tj_Some
    by (auto simp: valid_window_matchP_def w'''_def w_tsj_w' i'_def split: option.splits)
  moreover have "eval_mP I w = Some ((t, sat (MatchP I r) j), w''')"
    by (simp add: read_t_def Let_def loop_def[symmetric] ac'_def[unfolded e'_def ac_def] w'''_def w'_def trans[OF \<beta>_def(1) b_alt])
  ultimately show ?thesis
    by (auto simp: tj_eq rho'_def)
qed

lemma valid_eval_matchF_Some:
  assumes valid_before': "valid_matchF I t0 sub rho i w"
  and eval: "eval_mF I w = Some ((t, b), w'')"
  and bounded: "right I \<in> tfin"
  shows "\<exists>rho' tm. reaches_on (w_run_t args) (w_tj w) (map fst rho') (w_tj w'') \<and>
    reaches_on (w_run_sub args) (w_sj w) (map snd rho') (w_sj w'') \<and>
    (w_read_t args) (w_ti w) = Some t \<and>
    (w_read_t args) (w_tj w'') = Some tm \<and>
    \<not>memR t tm I"
proof -
  define st where "st = w_st w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define j where "j = w_j w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "rw t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q"
    "valid_s init step st accept rho i i j s"
    "i = w_i w" "i \<le> j" "length rho = j"
    using valid_before'[unfolded valid_window_matchF_def] ti_def
      si_def j_def tj_def sj_def s_def e_def
    by (auto simp: valid_window_def Let_def init_def step_def st_def accept_def)
  obtain ti''' where tbi_def: "w_run_t args ti = Some (ti''', t)"
    using eval read_t_run
    by (fastforce simp: Let_def ti_def si_def split: option.splits if_splits)
  have t_tau: "t = \<tau> \<sigma> i"
    using run_t_sound[OF _ tbi_def] valid_before(1)
    by auto
  note t_def = run_t_read[OF tbi_def(1)]
  obtain w' where loop_def: "while_break (matchF_cond I t) (adv_end args) w = Some w'"
    using eval
    by (auto simp: ti_def[symmetric] t_def split: option.splits)
  have adv_start_last:
    "adv_start args w' = w''"
    using eval loop_def[symmetric] run_t_read[OF tbi_def(1)]
    by (auto simp: ti_def split: option.splits prod.splits if_splits)
  have inv_before: "matchF_inv' t0 sub rho i ti si j tj sj w"
    using valid_before(1) valid_before'
    unfolding matchF_loop_inv'_def valid_before(6) valid_window_matchF_def
    by (auto simp add: ti_def si_def j_def tj_def sj_def simp del: reach_window.simps
        dest: reach_window_shift_all intro!: exI[of _ "[]"])
  have i_j: "i \<le> j" "length rho = j"
    using valid_before by auto
  define j'' where "j'' = w_j w''"
  define tj'' where "tj'' = w_tj w''"
  define sj'' where "sj'' = w_sj w''"
  have loop: "matchF_inv' t0 sub rho i ti si j tj sj w' \<and> \<not> matchF_cond I t w'"
  proof (rule while_break_sound[of "matchF_inv' t0 sub rho i ti si j tj sj" "matchF_cond I t" "adv_end args" "\<lambda>w'. matchF_inv' t0 sub rho i ti si j tj sj w' \<and> \<not> matchF_cond I t w'" w, unfolded loop_def, simplified])
    fix w_cur w_cur' :: "(bool iarray, nat set, 'd, 't, 'e) window"
    assume assms: "matchF_inv' t0 sub rho i ti si j tj sj w_cur" "matchF_cond I t w_cur" "adv_end args w_cur = Some w_cur'"
    define j_cur where "j_cur = w_j w_cur"
    define tj_cur where "tj_cur = w_tj w_cur"
    define sj_cur where "sj_cur = w_sj w_cur"
    obtain rho' where rho'_def: "valid_window args t0 sub (rho @ rho') w_cur"
      "rw t0 sub (rho @ rho') (j, tj, sj, w_j w_cur, w_tj w_cur, w_sj w_cur)"
      using assms(1)[unfolded matchF_loop_inv'_def valid_window_matchF_def]
      by auto
    obtain tj' x sj' y where append: "w_run_t args tj_cur = Some (tj', x)"
      "w_run_sub args sj_cur = Some (sj', y)"
      using assms(3)
      unfolding tj_cur_def sj_cur_def
      by (auto simp: adv_end_def Let_def split: option.splits)
    note append' = append[unfolded tj_cur_def sj_cur_def]
    define rho'' where "rho'' = rho @ rho'"
    have reach: "reaches_on (w_run_t args) t0 (map fst (rho'' @ [(x, undefined)])) tj'"
      using reaches_on_app[OF reach_window_run_tj[OF rho'_def(2)] append'(1)]
      by (auto simp: rho''_def)
    have mono: "\<And>t'. t' \<in> set (map fst rho'') \<Longrightarrow> t' \<le> x"
      using ts_at_mono[OF reach, of _ "length rho''"] nat_less_le
      by (fastforce simp: ts_at_def nth_append in_set_conv_nth split: list.splits)
    show "matchF_inv' t0 sub rho i ti si j tj sj w_cur'"
      using assms(1,3) reach_window_app[OF rho'_def(2) append[unfolded tj_cur_def sj_cur_def]]
        valid_adv_end[OF rho'_def(1) append' mono] adv_end_bounds[OF append']
      unfolding matchF_loop_inv'_def matchF_loop_cond_def rho''_def
      by auto
  next
    obtain l where l_def: "\<not>\<tau> \<sigma> l \<le> t + right I"
      unfolding t_tau
      using ex_lt_\<tau>[OF bounded]
      by auto
    {
      fix w1 w2
      assume lassms: "matchF_inv' t0 sub rho i ti si j tj sj w1" "matchF_cond I t w1"
        "Some w2 = adv_end args w1"
      define j_cur where "j_cur = w_j w1"
      define tj_cur where "tj_cur = w_tj w1"
      define sj_cur where "sj_cur = w_sj w1"
      obtain rho' where rho'_def: "valid_window args t0 sub (rho @ rho') w1"
        "rw t0 sub (rho @ rho') (j, tj, sj, w_j w1, w_tj w1, w_sj w1)"
        using lassms(1)[unfolded matchF_loop_inv'_def valid_window_matchF_def]
        by auto
      obtain tj' x sj' y where append: "w_run_t args tj_cur = Some (tj', x)"
        "w_run_sub args sj_cur = Some (sj', y)"
        using lassms(3)
        unfolding tj_cur_def sj_cur_def
        by (auto simp: adv_end_def Let_def split: option.splits)
      note append' = append[unfolded tj_cur_def sj_cur_def]
      define rho'' where "rho'' = rho @ rho'"
      have reach: "reaches_on (w_run_t args) t0 (map fst (rho'' @ [(x, undefined)])) tj'"
        using reaches_on_app[OF reach_window_run_tj[OF rho'_def(2)] append'(1)]
        by (auto simp: rho''_def)
      have mono: "\<And>t'. t' \<in> set (map fst rho'') \<Longrightarrow> t' \<le> x"
        using ts_at_mono[OF reach, of _ "length rho''"] nat_less_le
        by (fastforce simp: ts_at_def nth_append in_set_conv_nth split: list.splits)
      have t_cur_tau: "x = \<tau> \<sigma> j_cur"
        using ts_at_tau[OF reach, of "length rho''"] rho'_def(2)
        by (auto simp: ts_at_def j_cur_def rho''_def)
      have "j_cur < l"
        using lassms(2)[unfolded matchF_loop_cond_def] l_def memR_mono'[OF _ \<tau>_mono[of l j_cur \<sigma>]]
        unfolding run_t_read[OF append(1), unfolded t_cur_tau tj_cur_def]
        by (fastforce dest: memR_dest)
      moreover have "w_j w2 = Suc j_cur"
        using adv_end_bounds[OF append']
        unfolding lassms(3)[symmetric] j_cur_def
        by auto
      ultimately have "l - w_j w2 < l - w_j w1"
        unfolding j_cur_def
        by auto
    }
    then have "{(ta, s). matchF_inv' t0 sub rho i ti si j tj sj s \<and> matchF_cond I t s \<and>
      Some ta = adv_end args s} \<subseteq> measure (\<lambda>w. l - w_j w)"
      by auto
    then show "wf {(ta, s). matchF_inv' t0 sub rho i ti si j tj sj s \<and> matchF_cond I t s \<and>
      Some ta = adv_end args s}"
      using wf_measure wf_subset
      by auto
  qed (auto simp: inv_before)
  define i' where "i' = w_i w'"
  define ti' where "ti' = w_ti w'"
  define si' where "si' = w_si w'"
  define j' where "j' = w_j w'"
  define tj' where "tj' = w_tj w'"
  define sj' where "sj' = w_sj w'"
  obtain rho' where rho'_def: "valid_window args t0 sub (rho @ rho') w'"
    "rw t0 sub (rho @ rho') (j, tj, sj, j', tj', sj')"
    "i = i'" "j \<le> j'"
    using loop
    unfolding matchF_loop_inv'_def i'_def j'_def tj'_def sj'_def
    by auto
  obtain tje tm where tm_def: "w_read_t args tj' = Some tm" "w_run_t args tj' = Some (tje, tm)"
    using eval read_t_run loop_def t_def ti_def
    by (auto simp: t_def Let_def tj'_def split: option.splits if_splits)
  have drop_j_rho: "drop j (map fst (rho @ rho')) = map fst rho'"
    using i_j
    by auto
  have "reaches_on (w_run_t args) ti (drop i (map fst rho)) tj"
    using valid_before(1)
    by auto
  then have "reaches_on (w_run_t args) ti
    (drop i (map fst rho) @ (drop j (map fst (rho @ rho')))) tj'"
    using rho'_def reaches_on_trans
    by fastforce
  then have "reaches_on (w_run_t args) ti (drop i (map fst (rho @ rho'))) tj'"
    unfolding drop_j_rho
    by (auto simp: i_j)
  then have reach_tm: "reaches_on (w_run_t args) ti (drop i (map fst (rho @ rho')) @ [tm]) tje"
    using reaches_on_app tm_def(2)
    by fastforce
  have run_tsi': "w_run_t args ti' \<noteq> None"
    using tbi_def loop
    by (auto simp: matchF_loop_inv'_def ti'_def si'_def)
  have memR_t_tm: "\<not> memR t tm I"
    using loop tm_def
    by (auto simp: tj'_def matchF_loop_cond_def)
  have i_le_rho: "i \<le> length rho"
    using valid_before
    by auto
  define rho'' where "rho'' = rho @ rho'"
  have t_tfin: "t \<in> tfin"
    using \<tau>_fin
    by (auto simp: t_tau)
  have i'_lt_j': "i' < j'"
    using rho'_def(1,2,3)[folded rho''_def] i_j reach_tm[folded rho''_def] memR_t_tm tbi_def memR_tfin_refl[OF t_tfin]
    by (cases "i' = j'") (auto dest!: reaches_on_NilD elim!: reaches_on.cases[of _ _ "[tm]"])
  have adv_last_bounds: "j'' = j'" "tj'' = tj'" "sj'' = sj'"
    using valid_adv_start_bounds[OF rho'_def(1) i'_lt_j'[unfolded i'_def j'_def]]
    unfolding adv_start_last j'_def j''_def tj'_def tj''_def sj'_def sj''_def
    by auto
  show ?thesis
    using eval rho'_def run_tsi' i_j(2) adv_last_bounds tj''_def tj_def sj''_def sj_def
      loop_def t_def ti_def tj'_def tm_def memR_t_tm
    by (auto simp: drop_map run_t_read[OF tbi_def(1)] Let_def
        split: option.splits prod.splits if_splits intro!: exI[of _ rho'])
qed

lemma valid_eval_matchF_complete:
  assumes valid_before': "valid_matchF I t0 sub rho i w"
    and before_end: "reaches_on (w_run_t args) (w_tj w) (map fst rho') tj'''"
    "reaches_on (w_run_sub args) (w_sj w) (map snd rho') sj'''"
    "w_read_t args (w_ti w) = Some t" "w_read_t args tj''' = Some tm" "\<not>memR t tm I"
    and wf: "wf_regex r"
  shows "\<exists>w'. eval_mF I w = Some ((\<tau> \<sigma> i, sat (MatchF I r) i), w') \<and>
    valid_matchF I t0 sub (take (w_j w') (rho @ rho')) (Suc i) w'"
proof -
  define st where "st = w_st w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define j where "j = w_j w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "rw t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q"
    "valid_s init step st accept rho i i j s"
    "i = w_i w" "i \<le> j" "length rho = j"
    using valid_before'[unfolded valid_window_matchF_def] ti_def
      si_def j_def tj_def sj_def s_def e_def
    by (auto simp: valid_window_def Let_def init_def step_def st_def accept_def)
  define rho'' where "rho'' = rho @ rho'"
  have ij_le: "i \<le> j" "j = length rho"
    using valid_before
    by auto
  have reach_tj: "reaches_on (w_run_t args) t0 (take j (map fst rho'')) tj"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def simp del: reach_window.simps dest!: reach_window_run_tj)
  have reach_ti: "reaches_on (w_run_t args) t0 (take i (map fst rho'')) ti"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def)
  have reach_si: "reaches_on (w_run_sub args) sub (take i (map snd rho'')) si"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def)
  have reach_sj: "reaches_on (w_run_sub args) sub (take j (map snd rho'')) sj"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def simp del: reach_window.simps dest!: reach_window_run_sj)
  have reach_tj''': "reaches_on (w_run_t args) t0 (map fst rho'') tj'''"
    using reaches_on_trans[OF reach_tj before_end(1)[folded tj_def]] ij_le(2)
    by (auto simp del: map_append simp: rho''_def take_map drop_map map_append[symmetric])
  have rho''_mono: "\<And>i j. i \<le> j \<Longrightarrow> j < length rho'' \<Longrightarrow> ts_at rho'' i \<le> ts_at rho'' j"
    using ts_at_mono[OF reach_tj'''] .
  obtain tm' where reach_tm: "reaches_on (w_run_t args) t0
    (map fst (rho'' @ [(tm, undefined)])) tm'"
    using reaches_on_app[OF reach_tj'''] read_t_run[OF before_end(4)]
    by auto
  have tj'''_eq: "\<And>tj_cur. reaches_on (w_run_t args) t0 (map fst rho'') tj_cur \<Longrightarrow>
    tj_cur = tj'''"
    using reaches_on_inj[OF reach_tj''']
    by blast
  have reach_sj''': "reaches_on (w_run_sub args) sub (map snd rho'') sj'''"
    using reaches_on_trans[OF reach_sj before_end(2)[folded sj_def]] ij_le(2)
    by (auto simp del: map_append simp: rho''_def take_map drop_map map_append[symmetric])
  have sj'''_eq: "\<And>sj_cur. reaches_on (w_run_sub args) sub (map snd rho'') sj_cur \<Longrightarrow>
    sj_cur = sj'''"
    using reaches_on_inj[OF reach_sj''']
    by blast
  have reach_window_i: "rw t0 sub rho'' (i, ti, si, length rho'', tj''', sj''')"
    using reach_windowI[OF reach_ti reach_si reach_tj''' reach_sj''' _ refl] ij_le
    by (auto simp: rho''_def)
  have reach_window_j: "rw t0 sub rho'' (j, tj, sj, length rho'', tj''', sj''')"
    using reach_windowI[OF reach_tj reach_sj reach_tj''' reach_sj''' _ refl] ij_le
    by (auto simp: rho''_def)
  have t_def: "t = \<tau> \<sigma> i"
    using valid_before(6) read_t_run[OF before_end(3)] reaches_on_app[OF reach_ti]
      ts_at_tau[where ?rho="take i rho'' @ [(t, undefined)]"]
    by (fastforce simp: ti_def rho''_def valid_before(5,7) take_map ts_at_def nth_append)
  have t_tfin: "t \<in> tfin"
    using \<tau>_fin
    by (auto simp: t_def)
  have i_lt_rho'': "i < length rho''"
    using ij_le before_end(3,4,5) reach_window_i memR_tfin_refl[OF t_tfin]
    by (cases "i = length rho''") (auto simp: rho''_def ti_def dest!: reaches_on_NilD)
  obtain ti''' si''' b where tbi_def: "w_run_t args ti = Some (ti''', t)"
    "w_run_sub args si = Some (si''', b)" "t = ts_at rho'' i" "b = bs_at rho'' i"
    using reach_window_run_ti[OF reach_window_i i_lt_rho'']
      reach_window_run_si[OF reach_window_i i_lt_rho'']
      read_t_run[OF before_end(3), folded ti_def]
    by auto
  note before_end' = before_end(5)
  have read_ti: "w_read_t args ti = Some t"
    using run_t_read[OF tbi_def(1)] .
  have inv_before: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w"
    using valid_before' before_end(1,2,3) reach_window_j ij_le ti_def si_def j_def tj_def sj_def
    unfolding matchF_loop_inv_def valid_window_matchF_def
    by (auto simp: rho''_def ts_at_def nth_append)
  have i_j: "i \<le> j"
    using valid_before by auto
  have loop: "pred_option' (\<lambda>w'. matchF_inv I t0 sub rho'' i ti si tj''' sj''' w' \<and> \<not> matchF_cond I t w') (while_break (matchF_cond I t) (adv_end args) w)"
  proof (rule while_break_complete[of "matchF_inv I t0 sub rho'' i ti si tj''' sj'''", OF _ _ _ inv_before])
    fix w_cur :: "(bool iarray, nat set, 'd, 't, 'e) window"
    assume assms: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w_cur" "matchF_cond I t w_cur"
    define j_cur where "j_cur = w_j w_cur"
    define tj_cur where "tj_cur = w_tj w_cur"
    define sj_cur where "sj_cur = w_sj w_cur"
    define s_cur where "s_cur = w_s w_cur"
    define e_cur where "e_cur = w_e w_cur"
    have loop: "valid_window args t0 sub (take (w_j w_cur) rho'') w_cur"
      "rw t0 sub rho'' (j_cur, tj_cur, sj_cur, length rho'', tj''', sj''')"
      "\<And>l. l\<in>{w_i w_cur..<w_j w_cur} \<Longrightarrow> memR (ts_at rho'' i) (ts_at rho'' l) I"
      using j_cur_def tj_cur_def sj_cur_def s_cur_def e_cur_def
        assms(1)[unfolded matchF_loop_inv_def]
      by auto
    have j_cur_lt_rho'': "j_cur < length rho''"
      using assms tj'''_eq before_end(4,5)
      unfolding matchF_loop_inv_def matchF_loop_cond_def
      by (cases "j_cur = length rho''") (auto simp: j_cur_def split: option.splits)
    obtain tj_cur' sj_cur' x b_cur where tbi_cur_def: "w_run_t args tj_cur = Some (tj_cur', x)"
      "w_run_sub args sj_cur = Some (sj_cur', b_cur)"
      "x = ts_at rho'' j_cur" "b_cur = bs_at rho'' j_cur"
      using reach_window_run_ti[OF loop(2) j_cur_lt_rho'']
        reach_window_run_si[OF loop(2) j_cur_lt_rho'']
      by auto
    note reach_window_j'_cur = reach_window_shift[OF loop(2) j_cur_lt_rho'' tbi_cur_def(1,2)]
    note tbi_cur_def' = tbi_cur_def(1,2)[unfolded tj_cur_def sj_cur_def]
    have mono: "\<And>t'. t' \<in> set (map fst (take (w_j w_cur) rho'')) \<Longrightarrow> t' \<le> x"
      using rho''_mono[of _ j_cur] j_cur_lt_rho'' nat_less_le
      by (fastforce simp: tbi_cur_def(3) j_cur_def ts_at_def nth_append in_set_conv_nth
          split: list.splits)
    have take_unfold: "take (w_j w_cur) rho'' @ [(x, b_cur)] = (take (Suc (w_j w_cur)) rho'')"
      using j_cur_lt_rho''
      unfolding tbi_cur_def(3,4)
      by (auto simp: ts_at_def bs_at_def j_cur_def take_Suc_conv_app_nth)
    obtain w_cur' where w_cur'_def: "adv_end args w_cur = Some w_cur'"
      by (fastforce simp: adv_end_def Let_def tj_cur_def[symmetric] sj_cur_def[symmetric] tbi_cur_def(1,2) split: prod.splits)
    have "\<And>l. l \<in>{w_i w_cur'..<w_j w_cur'} \<Longrightarrow>
      memR (ts_at rho'' i) (ts_at rho'' l) I"
      using loop(3) assms(2) w_cur'_def
      unfolding adv_end_bounds[OF tbi_cur_def' w_cur'_def] matchF_loop_cond_def
        run_t_read[OF tbi_cur_def(1)[unfolded tj_cur_def]] tbi_cur_def(3) tbi_def(3)
      by (auto simp: j_cur_def elim: less_SucE)
    then show "pred_option' (matchF_inv I t0 sub rho'' i ti si tj''' sj''') (adv_end args w_cur)"
      using assms(1) reach_window_j'_cur valid_adv_end[OF loop(1) tbi_cur_def' mono]
        w_cur'_def adv_end_bounds[OF tbi_cur_def' w_cur'_def]
      unfolding matchF_loop_inv_def j_cur_def take_unfold
      by (auto simp: pred_option'_def)
  next
    {
      fix w1 w2
      assume lassms: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w1" "matchF_cond I t w1"
        "Some w2 = adv_end args w1"
      define j_cur where "j_cur = w_j w1"
      define tj_cur where "tj_cur = w_tj w1"
      define sj_cur where "sj_cur = w_sj w1"
      define s_cur where "s_cur = w_s w1"
      define e_cur where "e_cur = w_e w1"
      have loop: "valid_window args t0 sub (take (w_j w1) rho'') w1"
        "rw t0 sub rho'' (j_cur, tj_cur, sj_cur, length rho'', tj''', sj''')"
        "\<And>l. l\<in>{w_i w1..<w_j w1} \<Longrightarrow> memR (ts_at rho'' i) (ts_at rho'' l) I"
        using j_cur_def tj_cur_def sj_cur_def s_cur_def e_cur_def
          lassms(1)[unfolded matchF_loop_inv_def]
        by auto
      have j_cur_lt_rho'': "j_cur < length rho''"
        using lassms tj'''_eq ij_le before_end(4,5)
        unfolding matchF_loop_inv_def matchF_loop_cond_def
        by (cases "j_cur = length rho''") (auto simp: j_cur_def split: option.splits)
      obtain tj_cur' sj_cur' x b_cur where tbi_cur_def: "w_run_t args tj_cur = Some (tj_cur', x)"
        "w_run_sub args sj_cur = Some (sj_cur', b_cur)"
        "x = ts_at rho'' j_cur" "b_cur = bs_at rho'' j_cur"
        using reach_window_run_ti[OF loop(2) j_cur_lt_rho'']
          reach_window_run_si[OF loop(2) j_cur_lt_rho'']
        by auto
      note tbi_cur_def' = tbi_cur_def(1,2)[unfolded tj_cur_def sj_cur_def]
      have "length rho'' - w_j w2 < length rho'' - w_j w1"
        using j_cur_lt_rho'' adv_end_bounds[OF tbi_cur_def', folded lassms(3)]
        unfolding j_cur_def
        by auto
    }
    then have "{(ta, s). matchF_inv I t0 sub rho'' i ti si tj''' sj''' s \<and> matchF_cond I t s \<and>
      Some ta = adv_end args s} \<subseteq> measure (\<lambda>w. length rho'' - w_j w)"
      by auto
    then show "wf {(ta, s). matchF_inv I t0 sub rho'' i ti si tj''' sj''' s \<and> matchF_cond I t s \<and>
      Some ta = adv_end args s}"
      using wf_measure wf_subset
      by auto
  qed (auto simp add: inv_before)
  obtain w' where w'_def: "while_break (matchF_cond I t) (adv_end args) w = Some w'"
    using loop
    by (auto simp: pred_option'_def split: option.splits)
  define w'' where adv_start_last: "w'' = adv_start args w'"
  define st' where "st' = w_st w'"
  define i' where "i' = w_i w'"
  define ti' where "ti' = w_ti w'"
  define si' where "si' = w_si w'"
  define j' where "j' = w_j w'"
  define tj' where "tj' = w_tj w'"
  define sj' where "sj' = w_sj w'"
  define s' where "s' = w_s w'"
  define e' where "e' = w_e w'"
  have valid_after: "valid_window args t0 sub (take (w_j w') rho'') w'"
    "rw t0 sub rho'' (j', tj', sj', length rho'', tj''', sj''')"
    "\<And>l. l\<in>{i..<j'} \<Longrightarrow> memR (ts_at rho'' i) (ts_at rho'' l) I"
    "i' = i" "ti' = ti" "si' = si"
    using loop
    unfolding matchF_loop_inv_def w'_def i'_def ti'_def si'_def j'_def tj'_def sj'_def
    by (auto simp: pred_option'_def)
  define i'' where "i'' = w_i w''"
  define j'' where "j'' = w_j w''"
  define tj'' where "tj'' = w_tj w''"
  define sj'' where "sj'' = w_sj w''"
  have j'_le_rho'': "j' \<le> length rho''"
    using loop
    unfolding matchF_loop_inv_def valid_window_matchF_def w'_def j'_def
    by (auto simp: pred_option'_def)
  obtain te where tbj'_def: "w_read_t args tj' = Some te"
    "te = ts_at (rho'' @ [(tm, undefined)]) j'"
    proof (cases "j' < length rho''")
      case True
      show ?thesis
        using reach_window_run_ti[OF valid_after(2) True] that True
        by (auto simp: ts_at_def nth_append dest!: run_t_read)
    next
      case False
      then have "tj' = tj'''" "j' = length rho''"
        using valid_after(2) j'_le_rho'' tj'''_eq
        by auto
      then show ?thesis
        using that before_end(4)
        by (auto simp: ts_at_def nth_append)
    qed
  have not_ets_te: "\<not>memR (ts_at rho'' i) te I"
    using loop
    unfolding w'_def
    by (auto simp: pred_option'_def matchF_loop_cond_def tj'_def[symmetric] tbj'_def(1) tbi_def(3) split: option.splits)
  have i'_set: "\<And>l. l \<in> {i..<j'} \<Longrightarrow> memR (ts_at rho'' i) (ts_at rho'' l) I"
    "\<not>memR (ts_at rho'' i) (ts_at (rho'' @ [(tm, undefined)]) j') I"
    using loop tbj'_def not_ets_te valid_after atLeastLessThan_iff
    unfolding matchF_loop_inv_def matchF_loop_cond_def tbi_def(3)
    by (auto simp: tbi_def tj'_def split: option.splits)
  have i_le_j': "i \<le> j'"
    using valid_after(1)
    unfolding valid_after(4)[symmetric]
    by (auto simp: valid_window_def Let_def i'_def j'_def)
  have i_lt_j': "i < j'"
    using i_le_j' i'_set(2) i_lt_rho''
    using memR_tfin_refl[OF \<tau>_fin] ts_at_tau[OF reach_tj''', of j']
    by (cases "i = j'") (auto simp: ts_at_def nth_append)
  then have i'_lt_j': "i' < j'"
    unfolding valid_after
    by auto
  have adv_last_bounds: "i'' = Suc i'" "w_ti w'' = ti'''" "w_si w'' = si'''" "j'' = j'"
    "tj'' = tj'" "sj'' = sj'"
    using valid_adv_start_bounds[OF valid_after(1) i'_lt_j'[unfolded i'_def j'_def]]
      valid_adv_start_bounds'[OF valid_after(1) tbi_def(1,2)[folded valid_after(5,6),
      unfolded ti'_def si'_def]]
    unfolding adv_start_last i'_def i''_def j'_def j''_def tj'_def tj''_def sj'_def sj''_def
    by auto
  have i''_i: "i'' = i + 1"
    using valid_after adv_last_bounds by auto
  have i_le_j': "i \<le> j'"
    using valid_after i'_lt_j'
    by auto
  then have i_le_rho: "i \<le> length rho''"
    using valid_after(2)
    by auto
  have "valid_s init step st' accept (take j' rho'') i i j' s'"
    using valid_after(1,4) i'_def
    by (auto simp: valid_window_def Let_def init_def step_def st'_def accept_def j'_def s'_def)
  note valid_s' = this[unfolded valid_s_def]
  have q0_in_keys: "{0} \<in> mmap_keys s'"
    using valid_s' init_def steps_refl by auto
  then obtain q' tstp where lookup_s': "mmap_lookup s' {0} = Some (q', tstp)"
    by (auto dest: Mapping_keys_dest)
  have lookup_sup_acc: "snd (the (mmap_lookup s' {0})) =
    sup_acc step accept (take j' rho'') {0} i j'"
    using conjunct2[OF valid_s'] lookup_s'
    by auto (smt case_prodD option.simps(5))
  have b_alt: "(case snd (the (mmap_lookup s' {0})) of None \<Rightarrow> False
    | Some tstp \<Rightarrow> memL t (fst tstp) I) \<longleftrightarrow> sat (MatchF I r) i"
  proof (rule iffI)
    assume assm: "case snd (the (mmap_lookup s' {0})) of None \<Rightarrow> False
      | Some tstp \<Rightarrow> memL t (fst tstp) I"
    then obtain ts tp where tstp_def:
      "sup_acc step accept (take j' rho'') {0} i j' = Some (ts, tp)"
      "memL (ts_at rho'' i) ts I"
      unfolding lookup_sup_acc
      by (auto simp: tbi_def split: option.splits)
    then have sup_acc_rho'': "sup_acc step accept rho'' {0} i j' = Some (ts, tp)"
      using sup_acc_concat_cong[of j' "take j' rho''" step accept "drop j' rho''"] j'_le_rho''
      by auto
    have tp_props: "tp \<in> {i..<j'}" "acc step accept rho'' {0} (i, Suc tp)"
      using sup_acc_SomeE[OF sup_acc_rho''] by auto
    have ts_ts_at: "ts = ts_at rho'' tp"
      using sup_acc_Some_ts[OF sup_acc_rho''] .
    have i_le_tp: "i \<le> Suc tp"
      using tp_props by auto
    have "memR (ts_at rho'' i) (ts_at rho'' tp) I"
      using i'_set(1)[OF tp_props(1)] .
    then have "mem (ts_at rho'' i) (ts_at rho'' tp) I"
      using tstp_def(2) unfolding ts_ts_at mem_def by auto
    then show "sat (MatchF I r) i"
      using i_le_tp acc_match[OF reach_sj''' i_le_tp _ wf] tp_props(2) ts_at_tau[OF reach_tj''']
        tp_props(1) j'_le_rho''
      by auto
  next
    assume "sat (MatchF I r) i"
    then obtain l where l_def: "l \<ge> i" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> l) I" "(i, Suc l) \<in> match r"
      by auto
    have l_lt_rho: "l < length rho''"
    proof (rule ccontr)
      assume contr: "\<not>l < length rho''"
      have "tm = ts_at (rho'' @ [(tm, undefined)]) (length rho'')"
        using i_le_rho
        by (auto simp add: ts_at_def rho''_def)
      moreover have "\<dots> \<le> \<tau> \<sigma> l"
        using \<tau>_mono ts_at_tau[OF reach_tm] i_le_rho contr
        by (metis One_nat_def Suc_eq_plus1 length_append lessI list.size(3)
            list.size(4) not_le_imp_less)
      moreover have "memR (\<tau> \<sigma> i) (\<tau> \<sigma> l) I"
        using l_def(2)
        unfolding mem_def
        by auto
      ultimately have "memR (\<tau> \<sigma> i) tm I"
        using memR_mono'
        by auto
      then show "False"
        using before_end' ts_at_tau[OF reach_tj''' i_lt_rho''] tbi_def(3)
        by (auto simp: rho''_def)
    qed
    have l_lt_j': "l < j'"
    proof (rule ccontr)
      assume contr: "\<not>l < j'"
      then have ts_at_j'_l: "ts_at rho'' j' \<le> ts_at rho'' l"
        using ts_at_mono[OF reach_tj'''] l_lt_rho
        by (auto simp add: order.not_eq_order_implies_strict)
      have ts_at_l_iu: "memR (ts_at rho'' i) (ts_at rho'' l) I"
        using l_def(2) ts_at_tau[OF reach_tj''' l_lt_rho] ts_at_tau[OF reach_tj''' i_lt_rho'']
        unfolding mem_def
        by auto
      show "False"
        using i'_set(2) ts_at_j'_l ts_at_l_iu contr l_lt_rho memR_mono'
        by (auto simp: ts_at_def nth_append split: if_splits)
    qed
    have i_le_Suc_l: "i \<le> Suc l"
      using l_def(1)
      by auto
    obtain tp where tstp_def: "sup_acc step accept rho'' {0} i j' = Some (ts_at rho'' tp, tp)"
      "l \<le> tp" "tp < j'"
      using l_def(1,3) l_lt_j' l_lt_rho
      by (meson accept_match[OF reach_sj''' i_le_Suc_l _ wf, unfolded steps_is_run] sup_acc_SomeI[unfolded acc_is_accept, of step accept] acc_is_accept atLeastLessThan_iff less_eq_Suc_le)
    have "memL (ts_at rho'' i) (ts_at rho'' l) I"
      using l_def(2)
      unfolding ts_at_tau[OF reach_tj''' i_lt_rho'', symmetric]
        ts_at_tau[OF reach_tj''' l_lt_rho, symmetric] mem_def
      by auto
    then have "memL (ts_at rho'' i) (ts_at rho'' tp) I"
      using ts_at_mono[OF reach_tj''' tstp_def(2)] tstp_def(3) j'_le_rho'' memL_mono'
      by auto
    then show "case snd (the (mmap_lookup s' {0})) of None \<Rightarrow> False
      | Some tstp \<Rightarrow> memL t (fst tstp) I"
      using lookup_sup_acc tstp_def j'_le_rho''
        sup_acc_concat_cong[of j' "take j' rho''" step accept "drop j' rho''"]
      by (auto simp: tbi_def split: option.splits)
  qed
  have "valid_matchF I t0 sub (take j'' rho'') i'' (adv_start args w')"
  proof -
    have "\<forall>l \<in> {i'..<j'}. memR (ts_at rho'' i') (ts_at rho'' l) I"
      using loop i'_def j'_def valid_after
      unfolding matchF_loop_inv_def
      by auto
    then have "\<forall>l \<in> {i''..<j''}. memR (ts_at rho'' i'') ( ts_at rho'' l) I"
      unfolding i''_i valid_after adv_last_bounds
      apply safe
      subgoal for l
        apply (drule ballE[of _ _ l])
        using ts_at_mono[OF reach_tj''', of i "Suc i"] j'_le_rho'' memR_mono
          apply auto
        done
      done
    moreover have "rw t0 sub (take j'' rho'') (i'', ti''', si''', j'', tj'', sj'')"
    proof -
      have rw: "rw t0 sub (take j' rho'') (i', ti', si', j', tj', sj')"
        using valid_after(1)
        by (auto simp: valid_window_def Let_def i'_def ti'_def si'_def j'_def tj'_def sj'_def)
      show ?thesis
        using reach_window_shift[OF rw i'_lt_j'
            tbi_def(1,2)[unfolded valid_after(5,6)[symmetric]]] adv_last_bounds
        by auto
    qed
    moreover have "valid_window args t0 sub (take j' rho'') w''"
      using valid_adv_start[OF valid_after(1) i'_lt_j'[unfolded i'_def j'_def]]
      unfolding adv_start_last j'_def .
    ultimately show "valid_matchF I t0 sub (take j'' rho'') i'' (adv_start args w')"
      using j'_le_rho''
      unfolding valid_window_matchF_def adv_last_bounds adv_start_last[symmetric] i''_def[symmetric]
        j'_def j''_def[symmetric] tj'_def tj''_def[symmetric] sj'_def sj''_def[symmetric]
      by (auto simp: ts_at_def)
  qed
  moreover have "eval_mF I w = Some ((\<tau> \<sigma> i, sat (MatchF I r) i), w'')"
    unfolding j''_def adv_start_last[symmetric] adv_last_bounds valid_after rho''_def
      eval_matchF.simps run_t_read[OF tbi_def(1)[unfolded ti_def]]
    using tbj'_def[unfolded tj'_def] not_ets_te[folded tbi_def(3)]
      b_alt[unfolded s'_def] t_def adv_start_last w'_def
    by (auto simp only: Let_def split: option.splits if_splits)
  ultimately show ?thesis
    unfolding j''_def adv_start_last[symmetric] adv_last_bounds valid_after rho''_def
    by auto
qed

lemma valid_eval_matchF_sound:
  assumes valid_before: "valid_matchF I t0 sub rho i w"
  and eval: "eval_mF I w = Some ((t, b), w'')"
  and bounded: "right I \<in> tfin"
  and wf: "wf_regex r"
shows "t = \<tau> \<sigma> i \<and> b = sat (MatchF I r) i \<and> (\<exists>rho'. valid_matchF I t0 sub rho' (Suc i) w'')"
proof -
  obtain rho' t tm where rho'_def: "reaches_on (w_run_t args) (w_tj w) (map fst rho') (w_tj w'')"
    "reaches_on (w_run_sub args) (w_sj w) (map snd rho') (w_sj w'')"
    "w_read_t args (w_ti w) = Some t"
    "w_read_t args (w_tj w'') = Some tm"
    "\<not>memR t tm I"
    using valid_eval_matchF_Some[OF assms(1-3)]
    by auto
  show ?thesis
    using valid_eval_matchF_complete[OF assms(1) rho'_def wf]
    unfolding eval
    by blast
qed

thm valid_eval_matchP
thm valid_eval_matchF_sound
thm valid_eval_matchF_complete

end

end
