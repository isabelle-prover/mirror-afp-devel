theory Multitape_One_Tape_Clocks
  imports Multitape_Clock_Interface
begin

section \<open>Two one-tape clocks\<close>

text \<open>The unary walk and marking sweep supply exact linear and quadratic
  clocks for the nondeterministic and deterministic hierarchy instances.
  This theory builds them as plain one-tape machines over the symbols blank \<open>0\<close>, endmarker \<open>1\<close>, mark \<open>2\<close>
  and input \<open>3\<close>, and proves their exact step counts on \<^term>\<open>unary_word n\<close>.\<close>


subsection \<open>One-tape machines\<close>

text \<open>A transition reads and writes a whole vector of symbols, one per
  tape index, and every index at or above the tape count must read and write
  the blank and stay put.  So a one-tape arc is determined by its state
  change, the symbol it reads, the symbol it writes, and one direction:
  \<^const>\<open>one_tape_read\<close> and \<^const>\<open>move_one\<close> at tape \<open>0\<close>.\<close>

definition one_tape_arc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> move
                     \<Rightarrow> nat \<times> (nat \<Rightarrow> nat) \<times> nat \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> move)" where
  "one_tape_arc q x q' y d = (q, one_tape_read x, q', one_tape_read y, move_one 0 d)"

text \<open>States \<open>0\<close> to \<open>4\<close>, start \<open>0\<close>, accept \<open>1\<close>, reject \<open>2\<close>; input
  symbol \<open>3\<close> alone.\<close>

definition one_tape ::
  "(nat \<times> (nat \<Rightarrow> nat) \<times> nat \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> move)) set \<Rightarrow> (nat, nat) ktm" where
  "one_tape D = KTM {0..4} {3} {0..3} 0 1 D 0 1 2 1"

lemma one_tape_fields [simp]:
  "k_ktm (one_tape D) = 1" "delta_ktm (one_tape D) = D"
  "s_ktm (one_tape D) = 0" "t_ktm (one_tape D) = 1" "r_ktm (one_tape D) = 2"
  "bl_ktm (one_tape D) = 0" "le_ktm (one_tape D) = 1"
  "Sigma_ktm (one_tape D) = {3 :: nat}" "\<Gamma>_ktm (one_tape D) = {0 .. 3 :: nat}"
  "Q_ktm (one_tape D) = {0 .. 4 :: nat}"
  by (simp_all add: one_tape_def)

text \<open>The configurations such a machine passes through: tape \<open>0\<close> holds \<open>u\<close>
  with its head at \<open>p\<close>, and every other tape is blank with its head at the
  origin.\<close>

definition one_tape_config :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat, nat) ktc_config" where
  "one_tape_config q u p = KConfig q (\<lambda>j. if j = 0 then u else (\<lambda>_. 0)) (\<lambda>j. if j = 0 then p else 0)"

lemma one_tape_config_state [simp]: "ktc_state (one_tape_config q u p) = q"
  by (simp add: one_tape_config_def)

lemma one_tape_config_step:
  assumes a: "one_tape_arc q x q' y d \<in> D" and x: "u p = x"
  shows "(one_tape_config q u p, one_tape_config q' (u(p := y)) (go_move d p)) \<in> ktm_step D"
proof -
  let ?ts = "\<lambda>j. if j = 0 then u else (\<lambda>_. 0 :: nat)"
  let ?ps = "\<lambda>j. if j = 0 then p else (0 :: nat)"
  have rd: "(\<lambda>k. ?ts k (?ps k)) = one_tape_read x" using x by (auto simp: one_tape_read_def)
  have "(q, (\<lambda>k. ?ts k (?ps k)), q', one_tape_read y, move_one 0 d) \<in> D"
    using a unfolding rd by (simp add: one_tape_arc_def)
  from ktm_step.step [where ts = ?ts and n = ?ps, OF this]
  have "(KConfig q ?ts ?ps,
         KConfig q' (\<lambda>k. (?ts k)(?ps k := one_tape_read y k)) (\<lambda>k. go_move (move_one 0 d k) (?ps k)))
          \<in> ktm_step D" .
  moreover have "(\<lambda>k. (?ts k)(?ps k := one_tape_read y k))
                   = (\<lambda>j. if j = 0 then u(p := y) else (\<lambda>_. 0))"
    by (auto simp: fun_eq_iff one_tape_read_def)
  moreover have "(\<lambda>k. go_move (move_one 0 d k) (?ps k)) = (\<lambda>j. if j = 0 then go_move d p else 0)"
    by (auto simp: fun_eq_iff move_one_def)
  ultimately show ?thesis by (simp add: one_tape_config_def)
qed

text \<open>The input as tape \<open>0\<close> sees it.\<close>

definition one_tape_input :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "one_tape_input n = (\<lambda>m. if m = 0 then 1 else if m \<le> n then 3 else 0)"

lemma one_tape_init: "init_config_ktm (one_tape D) (unary_word n) = one_tape_config 0 (one_tape_input n) 0"
  by (auto simp: one_tape_def one_tape_config_def one_tape_input_def unary_word_def fun_eq_iff)

text \<open>Walks: a state that loops on every symbol it meets, moving one way.\<close>

lemma one_tape_run_right:
  assumes a: "\<And>i. i < m \<Longrightarrow> one_tape_arc q (u (p + i)) q (u (p + i)) MoveR \<in> D"
  shows "(one_tape_config q u p, one_tape_config q u (p + m)) \<in> ktm_step D ^^ m"
  using a
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then have ih: "(one_tape_config q u p, one_tape_config q u (p + m)) \<in> ktm_step D ^^ m" by simp
  have "(one_tape_config q u (p + m), one_tape_config q (u(p + m := u (p + m))) (go_move MoveR (p + m)))
          \<in> ktm_step D"
    by (rule one_tape_config_step [OF Suc.prems]) simp_all
  then have "(one_tape_config q u (p + m), one_tape_config q u (p + Suc m)) \<in> ktm_step D" by simp
  with ih show ?case by (rule relpow_Suc_I)
qed

lemma one_tape_run_left:
  assumes mp: "m \<le> p"
      and a: "\<And>i. i < m \<Longrightarrow> one_tape_arc q (u (p - i)) q (u (p - i)) MoveL \<in> D"
  shows "(one_tape_config q u p, one_tape_config q u (p - m)) \<in> ktm_step D ^^ m"
  using mp a
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then have ih: "(one_tape_config q u p, one_tape_config q u (p - m)) \<in> ktm_step D ^^ m" by simp
  have "(one_tape_config q u (p - m), one_tape_config q (u(p - m := u (p - m))) (go_move MoveL (p - m)))
          \<in> ktm_step D"
    by (rule one_tape_config_step [OF Suc.prems(2)]) simp_all
  moreover have "go_move MoveL (p - m) = p - Suc m" using Suc.prems(1) by simp
  ultimately have "(one_tape_config q u (p - m), one_tape_config q u (p - Suc m)) \<in> ktm_step D" by simp
  with ih show ?case by (rule relpow_Suc_I)
qed


subsection \<open>Structure\<close>

text \<open>What an arc must satisfy for the machine to be well formed: it leaves
  neither halting state, stays within the five states and four symbols, keeps
  the endmarker where it is and steps off it only rightwards, and writes the
  endmarker nowhere else.\<close>

definition one_tape_arc_ok :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> move \<Rightarrow> bool" where
  "one_tape_arc_ok q x q' y d \<longleftrightarrow> q \<in> {0, 3, 4} \<and> q' \<le> 4 \<and> x \<le> 3 \<and> y \<le> 3
                         \<and> (x = 1 \<longrightarrow> y = 1 \<and> d \<noteq> MoveL) \<and> (y = 1 \<longrightarrow> x = 1)"

lemma one_tape_arc_eq [simp]:
  "one_tape_arc q x q' y d = one_tape_arc q2 x2 q2' y2 d2 \<longleftrightarrow> q = q2 \<and> x = x2 \<and> q' = q2' \<and> y = y2 \<and> d = d2"
proof
  assume e: "one_tape_arc q x q' y d = one_tape_arc q2 x2 q2' y2 d2"
  then have "one_tape_read x = one_tape_read x2" "one_tape_read y = one_tape_read y2" "move_one 0 d = move_one 0 d2" "q = q2" "q' = q2'"
    by (simp_all add: one_tape_arc_def)
  moreover have "d = d2" using fun_cong [OF \<open>move_one 0 d = move_one 0 d2\<close>, of 0] by (simp add: move_one_def)
  ultimately show "q = q2 \<and> x = x2 \<and> q' = q2' \<and> y = y2 \<and> d = d2"
    by (auto dest: one_tape_read_inj)
qed simp

lemma one_tape_wf:
  assumes arcs: "\<And>e. e \<in> D \<Longrightarrow> \<exists>q x q' y d. e = one_tape_arc q x q' y d \<and> one_tape_arc_ok q x q' y d"
  shows "well_formed_ktm (one_tape D)"
proof -
  have sub: "D \<subseteq> ({0..4} - {1, 2}) \<times> (UNIV \<rightarrow> {0..3}) \<times> {0..4}
                  \<times> (UNIV \<rightarrow> {0..3}) \<times> (UNIV \<rightarrow> UNIV)"
  proof
    fix e assume "e \<in> D"
    then obtain q x q' y d where e: "e = one_tape_arc q x q' y d" and ok: "one_tape_arc_ok q x q' y d"
      using arcs by blast
    show "e \<in> ({0..4} - {1, 2}) \<times> (UNIV \<rightarrow> {0..3}) \<times> {0..4}
                \<times> (UNIV \<rightarrow> {0..3}) \<times> (UNIV \<rightarrow> UNIV)"
      using ok by (auto simp: e one_tape_arc_def one_tape_read_def one_tape_arc_ok_def)
  qed
  have le: "a' j = 1 \<and> dd j \<in> {MoveN, MoveR}"
    if m: "(q, a, q', a', dd) \<in> D" and aj: "a j = 1" for q a q' a' dd j
  proof -
    obtain q0 x q0' y d where e: "(q, a, q', a', dd) = one_tape_arc q0 x q0' y d"
      and ok: "one_tape_arc_ok q0 x q0' y d" using arcs [OF m] by blast
    have aa: "a = one_tape_read x" "a' = one_tape_read y" "dd = move_one 0 d" using e by (simp_all add: one_tape_arc_def)
    have j0: "j = 0" using aj aa(1) by (simp add: one_tape_read_def split: if_splits)
    show ?thesis using ok aj aa j0 by (cases d) (auto simp: one_tape_arc_ok_def one_tape_read_def move_one_def)
  qed
  have hi: "a j = 0 \<and> a' j = 0 \<and> dd j = MoveN"
    if m: "(q, a, q', a', dd) \<in> D" and j1: "1 \<le> j" for q a q' a' dd j
  proof -
    obtain q0 x q0' y d where e: "(q, a, q', a', dd) = one_tape_arc q0 x q0' y d"
      using arcs [OF m] by blast
    then show ?thesis using j1 by (simp add: one_tape_arc_def one_tape_read_def move_one_def)
  qed
  have lu: "a j = 1" if m: "(q, a, q', a', dd) \<in> D" and aj: "a' j = 1" for q a q' a' dd j
  proof -
    obtain q0 x q0' y d where e: "(q, a, q', a', dd) = one_tape_arc q0 x q0' y d"
      and ok: "one_tape_arc_ok q0 x q0' y d" using arcs [OF m] by blast
    have aa: "a = one_tape_read x" "a' = one_tape_read y" using e by (simp_all add: one_tape_arc_def)
    show ?thesis using ok aj aa by (auto simp: one_tape_arc_ok_def one_tape_read_def split: if_splits)
  qed
  have "valid_ktm (one_tape D)"
    unfolding one_tape_def valid_ktm.simps using sub le hi by auto
  moreover have "le_unique (one_tape D)"
    unfolding le_unique_def using lu by simp
  ultimately show ?thesis by simp
qed

lemma one_tape_det:
  assumes arcs: "\<And>e. e \<in> D \<Longrightarrow> \<exists>q x q' y d. e = one_tape_arc q x q' y d"
      and key: "\<And>q x q1 y1 d1 q2 y2 d2. one_tape_arc q x q1 y1 d1 \<in> D \<Longrightarrow> one_tape_arc q x q2 y2 d2 \<in> D
                  \<Longrightarrow> (q1, y1, d1) = (q2, y2, d2)"
  shows "det_ktm (one_tape D)"
  unfolding det_ktm_def
proof (intro allI impI)
  fix q a p1 b1 d1 p2 b2 d2
  assume m1: "(q, a, p1, b1, d1) \<in> delta_ktm (one_tape D)"
     and m2: "(q, a, p2, b2, d2) \<in> delta_ktm (one_tape D)"
  obtain q0 x q1 y1 e1 where e1: "(q, a, p1, b1, d1) = one_tape_arc q0 x q1 y1 e1"
    using arcs m1 by fastforce
  obtain q0' x' q2 y2 e2 where e2: "(q, a, p2, b2, d2) = one_tape_arc q0' x' q2 y2 e2"
    using arcs m2 by fastforce
  have "q0 = q" "q0' = q" "a = one_tape_read x" "a = one_tape_read x'" using e1 e2 by (simp_all add: one_tape_arc_def)
  then have xx: "x' = x" using one_tape_read_inj by metis
  have "one_tape_arc q x q1 y1 e1 \<in> D" "one_tape_arc q x q2 y2 e2 \<in> D"
    using m1 m2 e1 e2 \<open>q0 = q\<close> \<open>q0' = q\<close> xx by simp_all
  from key [OF this] show "(p1, b1, d1) = (p2, b2, d2)"
    using e1 e2 by (simp add: one_tape_arc_def)
qed

subsection \<open>The walk: a clock for \<open>n + 2\<close>\<close>

text \<open>One state: step off the endmarker, run over the input, and halt on
  the blank above it.\<close>

definition walk_delta where
  "walk_delta = {one_tape_arc 0 1 0 1 MoveR, one_tape_arc 0 3 0 3 MoveR, one_tape_arc 0 0 1 0 MoveN}"

definition walk_clock :: "(nat, nat) ktm" where
  "walk_clock = one_tape walk_delta"

lemma walk_clock_wf: "well_formed_ktm walk_clock"
  unfolding walk_clock_def
  by (rule one_tape_wf) (auto simp: walk_delta_def one_tape_arc_ok_def)

lemma walk_clock_det: "det_ktm walk_clock"
  unfolding walk_clock_def
proof (rule one_tape_det)
  show "\<exists>q x q' y d. e = one_tape_arc q x q' y d" if "e \<in> walk_delta" for e
    using that by (auto simp: walk_delta_def)
  show "(q1, y1, d1) = (q2, y2, d2)"
    if "one_tape_arc q x q1 y1 d1 \<in> walk_delta" "one_tape_arc q x q2 y2 d2 \<in> walk_delta"
    for q x q1 y1 d1 q2 y2 d2
    using that by (auto simp: walk_delta_def)
qed

lemma walk_run:
  "(one_tape_config 0 (one_tape_input n) 0, one_tape_config 1 (one_tape_input n) (Suc n))
     \<in> ktm_step walk_delta ^^ (n + 2)"
proof -
  let ?u = "one_tape_input n"
  have s1: "(one_tape_config 0 ?u 0, one_tape_config 0 ?u 1) \<in> ktm_step walk_delta"
    using one_tape_config_step [of 0 1 0 1 MoveR walk_delta ?u 0]
    by (simp add: walk_delta_def one_tape_input_def fun_upd_idem)
  have s2: "(one_tape_config 0 ?u 1, one_tape_config 0 ?u (1 + n)) \<in> ktm_step walk_delta ^^ n"
    by (rule one_tape_run_right) (simp add: walk_delta_def one_tape_input_def)
  have s3: "(one_tape_config 0 ?u (1 + n), one_tape_config 1 ?u (Suc n)) \<in> ktm_step walk_delta"
    using one_tape_config_step [of 0 0 1 0 MoveN walk_delta ?u "1 + n"]
    by (simp add: walk_delta_def one_tape_input_def fun_upd_idem)
  from relpow_Suc_I [OF relpow_Suc_I2 [OF s1 s2] s3] show ?thesis by simp
qed

theorem time_constructible_walk: "time_constructible (\<lambda>n. n + 2)"
proof -
  have run: "\<forall>n. \<exists>cfg. (init_config_ktm walk_clock (unary_word n), cfg)
                          \<in> ktm_step (delta_ktm walk_clock) ^^ (n + 2)
                        \<and> ktc_state cfg = t_ktm walk_clock"
  proof (intro allI exI conjI)
    fix n
    show "(init_config_ktm walk_clock (unary_word n), one_tape_config 1 (one_tape_input n) (Suc n))
            \<in> ktm_step (delta_ktm walk_clock) ^^ (n + 2)"
      unfolding walk_clock_def one_tape_init one_tape_fields(2) by (rule walk_run)
    show "ktc_state (one_tape_config 1 (one_tape_input n) (Suc n)) = t_ktm walk_clock"
      by (simp add: walk_clock_def)
  qed
  have sig: "3 \<in> Sigma_ktm walk_clock" by (simp add: walk_clock_def)
  show ?thesis unfolding time_constructible_def
    using walk_clock_wf walk_clock_det sig run by blast
qed

subsection \<open>The sweep: a clock for \<open>2 n\<^sup>2 + 3 n + 2\<close>\<close>

text \<open>Each pass marks the first unmarked input cell, runs to the blank above
  the input, and returns to the endmarker; the pass that finds no unmarked
  cell halts.  State \<open>0\<close> seeks, \<open>3\<close> runs right, \<open>4\<close> runs left.  A pass
  costs \<open>2 n + 2\<close> however many marks it finds, which is what makes the count
  a polynomial rather than a sum.\<close>

definition sweep_delta where
  "sweep_delta =
     {one_tape_arc 0 1 0 1 MoveR, one_tape_arc 0 2 0 2 MoveR, one_tape_arc 0 3 3 2 MoveR, one_tape_arc 0 0 1 0 MoveN,
      one_tape_arc 3 2 3 2 MoveR, one_tape_arc 3 3 3 3 MoveR, one_tape_arc 3 0 4 0 MoveL,
      one_tape_arc 4 2 4 2 MoveL, one_tape_arc 4 3 4 3 MoveL, one_tape_arc 4 1 0 1 MoveR}"

definition sweep_clock :: "(nat, nat) ktm" where
  "sweep_clock = one_tape sweep_delta"

lemma sweep_clock_wf: "well_formed_ktm sweep_clock"
  unfolding sweep_clock_def
  by (rule one_tape_wf) (auto simp: sweep_delta_def one_tape_arc_ok_def)

lemma sweep_clock_det: "det_ktm sweep_clock"
  unfolding sweep_clock_def
proof (rule one_tape_det)
  show "\<exists>q x q' y d. e = one_tape_arc q x q' y d" if "e \<in> sweep_delta" for e
    using that by (auto simp: sweep_delta_def)
  show "(q1, y1, d1) = (q2, y2, d2)"
    if "one_tape_arc q x q1 y1 d1 \<in> sweep_delta" "one_tape_arc q x q2 y2 d2 \<in> sweep_delta"
    for q x q1 y1 d1 q2 y2 d2
    using that by (auto simp: sweep_delta_def)
qed

text \<open>The tape after \<open>k\<close> passes.\<close>

definition sweep_tape :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sweep_tape n k = (\<lambda>m. if m = 0 then 1 else if m \<le> k then 2 else if m \<le> n then 3 else 0)"

lemma sweep_tape_0: "sweep_tape n 0 = one_tape_input n"
  by (simp add: sweep_tape_def one_tape_input_def fun_eq_iff)

lemma sweep_pass:
  assumes k: "k < n"
  shows "(one_tape_config 0 (sweep_tape n k) 1, one_tape_config 0 (sweep_tape n (Suc k)) 1) \<in> ktm_step sweep_delta ^^ (2 * n + 2)"
proof -
  let ?R = "ktm_step sweep_delta"
  let ?u = "sweep_tape n k" and ?v = "sweep_tape n (Suc k)"
  have r1: "(one_tape_config 0 ?u 1, one_tape_config 0 ?u (1 + k)) \<in> ?R ^^ k"
    by (rule one_tape_run_right) (simp add: sweep_delta_def sweep_tape_def)
  have vu: "?u(1 + k := 2) = ?v" using k by (auto simp: sweep_tape_def fun_eq_iff)
  have s2': "(one_tape_config 0 ?u (1 + k), one_tape_config 3 (?u(1 + k := 2)) (2 + k)) \<in> ?R"
    using one_tape_config_step [of 0 3 3 2 MoveR sweep_delta ?u "1 + k"] k
    by (simp add: sweep_delta_def sweep_tape_def)
  note s2 = s2' [unfolded vu]
  have r3: "(one_tape_config 3 ?v (2 + k), one_tape_config 3 ?v (2 + k + (n - k - 1))) \<in> ?R ^^ (n - k - 1)"
    by (rule one_tape_run_right) (use k in \<open>auto simp: sweep_delta_def sweep_tape_def\<close>)
  have e3: "2 + k + (n - k - 1) = Suc n" using k by simp
  have s4: "(one_tape_config 3 ?v (Suc n), one_tape_config 4 ?v n) \<in> ?R"
    using one_tape_config_step [of 3 0 4 0 MoveL sweep_delta ?v "Suc n"] k
    by (simp add: sweep_delta_def sweep_tape_def fun_upd_idem)
  have r5: "(one_tape_config 4 ?v n, one_tape_config 4 ?v (n - n)) \<in> ?R ^^ n"
    by (rule one_tape_run_left) (auto simp: sweep_delta_def sweep_tape_def)
  have s6: "(one_tape_config 4 ?v 0, one_tape_config 0 ?v 1) \<in> ?R"
    using one_tape_config_step [of 4 1 0 1 MoveR sweep_delta ?v 0]
    by (simp add: sweep_delta_def sweep_tape_def fun_upd_idem)
  have r5': "(one_tape_config 4 ?v n, one_tape_config 4 ?v 0) \<in> ?R ^^ n" using r5 by simp
  from relpow_Suc_I [OF relpow_trans [OF r1 relpow_Suc_I2 [OF s2
         relpow_trans [OF r3 [unfolded e3] relpow_Suc_I2 [OF s4 r5']]]] s6]
  have "(one_tape_config 0 ?u 1, one_tape_config 0 ?v 1) \<in> ?R ^^ Suc (k + Suc (n - k - 1 + Suc n))" .
  moreover have "Suc (k + Suc (n - k - 1 + Suc n)) = 2 * n + 2" using k by simp
  ultimately show ?thesis by (simp only:)
qed

lemma sweep_passes:
  "k \<le> n \<Longrightarrow> (one_tape_config 0 (sweep_tape n 0) 1, one_tape_config 0 (sweep_tape n k) 1) \<in> ktm_step sweep_delta ^^ (k * (2 * n + 2))"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then have "(one_tape_config 0 (sweep_tape n 0) 1, one_tape_config 0 (sweep_tape n k) 1) \<in> ktm_step sweep_delta ^^ (k * (2 * n + 2))"
    by simp
  from relpow_trans [OF this sweep_pass [of k n]] Suc.prems
  have "(one_tape_config 0 (sweep_tape n 0) 1, one_tape_config 0 (sweep_tape n (Suc k)) 1)
          \<in> ktm_step sweep_delta ^^ (k * (2 * n + 2) + (2 * n + 2))" by simp
  moreover have "k * (2 * n + 2) + (2 * n + 2) = Suc k * (2 * n + 2)" by simp
  ultimately show ?case by (simp only:)
qed

lemma sweep_run:
  "(one_tape_config 0 (one_tape_input n) 0, one_tape_config 1 (sweep_tape n n) (Suc n))
     \<in> ktm_step sweep_delta ^^ (2 * n * n + 3 * n + 2)"
proof -
  let ?R = "ktm_step sweep_delta"
  have s1: "(one_tape_config 0 (sweep_tape n 0) 0, one_tape_config 0 (sweep_tape n 0) 1) \<in> ?R"
    using one_tape_config_step [of 0 1 0 1 MoveR sweep_delta "sweep_tape n 0" 0]
    by (simp add: sweep_delta_def sweep_tape_def fun_upd_idem)
  have r2: "(one_tape_config 0 (sweep_tape n 0) 1, one_tape_config 0 (sweep_tape n n) 1) \<in> ?R ^^ (n * (2 * n + 2))"
    by (rule sweep_passes) simp
  have r3: "(one_tape_config 0 (sweep_tape n n) 1, one_tape_config 0 (sweep_tape n n) (1 + n)) \<in> ?R ^^ n"
    by (rule one_tape_run_right) (simp add: sweep_delta_def sweep_tape_def)
  have s4: "(one_tape_config 0 (sweep_tape n n) (1 + n), one_tape_config 1 (sweep_tape n n) (Suc n)) \<in> ?R"
    using one_tape_config_step [of 0 0 1 0 MoveN sweep_delta "sweep_tape n n" "1 + n"]
    by (simp add: sweep_delta_def sweep_tape_def fun_upd_idem)
  from relpow_Suc_I2 [OF s1 relpow_trans [OF r2 relpow_Suc_I [OF r3 s4]]]
  have "(one_tape_config 0 (sweep_tape n 0) 0, one_tape_config 1 (sweep_tape n n) (Suc n)) \<in> ?R ^^ Suc (n * (2 * n + 2) + Suc n)" .
  moreover have "Suc (n * (2 * n + 2) + Suc n) = 2 * n * n + 3 * n + 2"
    by (simp add: algebra_simps)
  ultimately show ?thesis by (simp only: sweep_tape_0)
qed

theorem time_constructible_sweep: "time_constructible (\<lambda>n. 2 * n * n + 3 * n + 2)"
proof -
  have run: "\<forall>n. \<exists>cfg. (init_config_ktm sweep_clock (unary_word n), cfg)
                          \<in> ktm_step (delta_ktm sweep_clock) ^^ (2 * n * n + 3 * n + 2)
                        \<and> ktc_state cfg = t_ktm sweep_clock"
  proof (intro allI exI conjI)
    fix n
    show "(init_config_ktm sweep_clock (unary_word n), one_tape_config 1 (sweep_tape n n) (Suc n))
            \<in> ktm_step (delta_ktm sweep_clock) ^^ (2 * n * n + 3 * n + 2)"
      unfolding sweep_clock_def one_tape_init one_tape_fields(2) by (rule sweep_run)
    show "ktc_state (one_tape_config 1 (sweep_tape n n) (Suc n)) = t_ktm sweep_clock"
      by (simp add: sweep_clock_def)
  qed
  have sig: "3 \<in> Sigma_ktm sweep_clock" by (simp add: sweep_clock_def)
  show ?thesis unfolding time_constructible_def
    using sweep_clock_wf sweep_clock_det sig run by blast
qed

end
