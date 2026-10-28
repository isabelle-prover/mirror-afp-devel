theory Multitape_Clock_Product
  imports Multitape_Clock_Interface Multitape_Embedding Multitape_Relabelling
begin

section \<open>A machine paired with an exact alarm clock\<close>

text \<open>The product keeps a machine \<open>N\<close> and a clock \<open>D\<close> on disjoint tapes.
  It writes the unary input for the clock, then alternates their steps.
  A step of \<open>N\<close> into its accepting state reaches CAcc, and one into its
  rejecting state reaches CRej; a step of the clock into either terminal state
  reaches CRej.  So the product stops as soon as either factor does: the alarm
  bounds every path, accepting or not.  Each factor's part of the transition
  relation is called its \<^emph>\<open>arm\<close>.  Both arms may step into CRej, which is
  why \<open>arms_alternate\<close> lets a step into a final state carry either turn
  flag.  Nothing here asks \<open>N\<close> to be deterministic, so the product serves
  nondeterministic and deterministic machines alike.\<close>

datatype clock_state =
    CWalk | CBack | CRun nat nat bool | CAcc | CRej


fun cturn :: "clock_state \<Rightarrow> bool" where
  "cturn (CRun q p b) = b"
| "cturn CAcc = False"
| "cturn CWalk = True"
| "cturn CBack = True"
| "cturn CRej = True"


definition clock_tapes :: "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat" where
  "clock_tapes N D = k_ktm N + k_ktm D"

definition clock_Gamma ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat \<Rightarrow> nat set" where
  "clock_Gamma N D one = insert one (\<Gamma>_ktm N \<union> \<Gamma>_ktm D)"

definition clock_Q ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> clock_state set" where
  "clock_Q N D =
     {CWalk, CBack, CAcc, CRej}
       \<union> {CRun q p b | q p b. q \<in> Q_ktm N \<and> p \<in> Q_ktm D}"

definition clock_ctx ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "clock_ctx N D one =
     free_context (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D)"


subsection \<open>Each factor's transitions in the product\<close>


definition arm_N ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat
     \<Rightarrow> (clock_state \<times> (nat \<Rightarrow> nat) \<times> clock_state \<times> (nat \<Rightarrow> nat)
          \<times> (nat \<Rightarrow> move)) set" where
  "arm_N N D one =
     (\<Union>p \<in> Q_ktm D.
        tag_delta (\<lambda>q. CRun q p True)
                  (\<lambda>q'. if q' = t_ktm N then CAcc else if q' = r_ktm N then CRej else CRun q' p False)
                  (embed_delta 0 (k_ktm N) (clock_tapes N D)
                     (clock_Gamma N D one) (bl_ktm N) (delta_ktm N)))"

definition arm_D ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat
     \<Rightarrow> (clock_state \<times> (nat \<Rightarrow> nat) \<times> clock_state \<times> (nat \<Rightarrow> nat)
          \<times> (nat \<Rightarrow> move)) set" where
  "arm_D N D one =
     (\<Union>q \<in> Q_ktm N.
        tag_delta (\<lambda>p. CRun q p False)
                  (\<lambda>p'. if p' = t_ktm D \<or> p' = r_ktm D then CRej
                        else CRun q p' True)
                  (embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
                     (clock_Gamma N D one) (bl_ktm N) (delta_ktm D)))"


subsection \<open>The setup phase\<close>


definition clock_start_state ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> clock_state" where
  "clock_start_state N D =
     (if s_ktm N = t_ktm N then CAcc
      else if s_ktm N = r_ktm N then CRej
      else if s_ktm D = t_ktm D \<or> s_ktm D = r_ktm D then CRej
      else CRun (s_ktm N) (s_ktm D) True)"

text \<open>The last setup step dispatches terminal initial states without an
  extra transition.  The contestant has priority over the alarm, just as a
  contestant step precedes the corresponding alarm step during alternation.
  Thus even a zero-step decision is retained when the alarm is terminal.\<close>

definition move_two :: "nat \<Rightarrow> move \<Rightarrow> (nat \<Rightarrow> move)" where
  "move_two m e = (\<lambda>j. if j = 0 \<or> j = m then e else MoveN)"

definition setup_delta ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat
     \<Rightarrow> (clock_state \<times> (nat \<Rightarrow> nat) \<times> clock_state \<times> (nat \<Rightarrow> nat)
          \<times> (nat \<Rightarrow> move)) set" where
  "setup_delta N D one =
       {(CWalk, a, CWalk, a, move_two (k_ktm N) MoveR)
          | a. a \<in> clock_ctx N D one \<and> a 0 \<noteq> bl_ktm N}
     \<union> {(CWalk, a, CBack, a, move_two (k_ktm N) MoveL)
          | a. a \<in> clock_ctx N D one \<and> a 0 = bl_ktm N
               \<and> a (k_ktm N) \<noteq> le_ktm N}
     \<union> {(CBack, a, CBack, a(k_ktm N := one), move_two (k_ktm N) MoveL)
          | a. a \<in> clock_ctx N D one \<and> a 0 \<noteq> le_ktm N
               \<and> a (k_ktm N) \<noteq> le_ktm N}
     \<union> {(CBack, a, clock_start_state N D, a, \<lambda>_. MoveN)
          | a. a \<in> clock_ctx N D one \<and> a 0 = le_ktm N}"


subsection \<open>The composite machine\<close>


definition clock_product ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat \<Rightarrow> (clock_state, nat) ktm" where
  "clock_product N D one =
     KTM (clock_Q N D) (Sigma_ktm N) (clock_Gamma N D one)
          (bl_ktm N) (le_ktm N)
          (setup_delta N D one \<union> arm_N N D one \<union> arm_D N D one)
          CWalk CAcc CRej (clock_tapes N D)"

lemma clock_product_simps [simp]:
  "Q_ktm (clock_product N D one) = clock_Q N D"
  "Sigma_ktm (clock_product N D one) = Sigma_ktm N"
  "\<Gamma>_ktm (clock_product N D one) = clock_Gamma N D one"
  "bl_ktm (clock_product N D one) = bl_ktm N"
  "le_ktm (clock_product N D one) = le_ktm N"
  "delta_ktm (clock_product N D one)
     = setup_delta N D one \<union> arm_N N D one \<union> arm_D N D one"
  "s_ktm (clock_product N D one) = CWalk"
  "t_ktm (clock_product N D one) = CAcc"
  "r_ktm (clock_product N D one) = CRej"
  "k_ktm (clock_product N D one) = clock_tapes N D"
  by (simp_all add: clock_product_def)


subsection \<open>Validity\<close>


definition clock_ok ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat
     \<Rightarrow> clock_state \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> clock_state \<Rightarrow> (nat \<Rightarrow> nat)
     \<Rightarrow> (nat \<Rightarrow> move) \<Rightarrow> bool" where
  "clock_ok N D one Q A Q' A' E \<longleftrightarrow>
     Q \<in> clock_Q N D - {CAcc, CRej} \<and> Q' \<in> clock_Q N D
     \<and> (\<forall>j. A j \<in> clock_Gamma N D one)
     \<and> (\<forall>j. A' j \<in> clock_Gamma N D one)
     \<and> (\<forall>j. A j = le_ktm N \<longrightarrow> A' j = le_ktm N \<and> E j \<in> {MoveN, MoveR})
     \<and> (\<forall>j \<ge> clock_tapes N D.
           A j = bl_ktm N \<and> A' j = bl_ktm N \<and> E j = MoveN)"


lemma arm_N_ok:
  assumes vN: "valid_ktm N"
      and tr: "(Q, A, Q', A', E) \<in> arm_N N D one"
  shows "clock_ok N D one Q A Q' A' E"
proof -
  from tr obtain p where p: "p \<in> Q_ktm D"
    and tr': "(Q, A, Q', A', E)
                \<in> tag_delta (\<lambda>q. CRun q p True)
                     (\<lambda>q'. if q' = t_ktm N then CAcc else if q' = r_ktm N then CRej else CRun q' p False)
                     (embed_delta 0 (k_ktm N) (clock_tapes N D)
                        (clock_Gamma N D one) (bl_ktm N) (delta_ktm N))"
    by (auto simp: arm_N_def)
  from tr' obtain q a q' a' d b
    where trN: "(q, a, q', a', d) \<in> delta_ktm N"
      and b: "b \<in> free_context (clock_Gamma N D one) (bl_ktm N)
                     (clock_tapes N D)"
      and Q: "Q = CRun q p True"
      and Q': "Q' = (if q' = t_ktm N then CAcc else if q' = r_ktm N then CRej else CRun q' p False)"
      and Aeq: "A = (\<lambda>j. if 0 \<le> j \<and> j < 0 + k_ktm N then a (j - 0) else b j)"
      and A'eq: "A' = (\<lambda>j. if 0 \<le> j \<and> j < 0 + k_ktm N then a' (j - 0) else b j)"
      and Eeq: "E = (\<lambda>j. if 0 \<le> j \<and> j < 0 + k_ktm N then d (j - 0) else MoveN)"
    by (rule arm_source)
  have Aj: "A j = (if j < k_ktm N then a j else b j)" for j by (simp add: Aeq)
  have A'j: "A' j = (if j < k_ktm N then a' j else b j)" for j by (simp add: A'eq)
  have Ej: "E j = (if j < k_ktm N then d j else MoveN)" for j by (simp add: Eeq)

  from valid_ktm_delta_set [OF vN] trN
  have qN: "q \<in> Q_ktm N - {t_ktm N, r_ktm N}" and q'N: "q' \<in> Q_ktm N"
    and aG: "\<forall>j. a j \<in> \<Gamma>_ktm N" and a'G: "\<forall>j. a' j \<in> \<Gamma>_ktm N"
    by (auto simp: Pi_iff)
  from b have bG: "\<forall>j. b j \<in> clock_Gamma N D one"
    and bbl: "\<forall>j \<ge> clock_tapes N D. b j = bl_ktm N"
    by (auto simp: free_context_def)
  have kle: "k_ktm N \<le> clock_tapes N D" by (simp add: clock_tapes_def)

  have "Q \<in> clock_Q N D - {CAcc, CRej}"
    using Q qN p by (auto simp: clock_Q_def)
  moreover have "Q' \<in> clock_Q N D"
    using Q' q'N p by (auto simp: clock_Q_def)
  moreover have "\<forall>j. A j \<in> clock_Gamma N D one"
    using aG bG by (auto simp: Aj clock_Gamma_def)
  moreover have "\<forall>j. A' j \<in> clock_Gamma N D one"
    using a'G bG by (auto simp: A'j clock_Gamma_def)
  moreover
  have "\<forall>j. A j = le_ktm N \<longrightarrow> A' j = le_ktm N \<and> E j \<in> {MoveN, MoveR}"
    using valid_ktm_deltaLE [OF vN trN] by (auto simp: Aj A'j Ej)
  moreover
  have "\<forall>j \<ge> clock_tapes N D. A j = bl_ktm N \<and> A' j = bl_ktm N \<and> E j = MoveN"
    using bbl kle by (auto simp: Aj A'j Ej)
  ultimately show ?thesis by (simp add: clock_ok_def)
qed



lemma arm_D_ok:
  assumes vD: "valid_ktm D"
      and blD: "bl_ktm D = bl_ktm N"
      and leD: "le_ktm D = le_ktm N"
      and tr: "(Q, A, Q', A', E) \<in> arm_D N D one"
  shows "clock_ok N D one Q A Q' A' E"
proof -
  from tr obtain q where q: "q \<in> Q_ktm N"
    and tr': "(Q, A, Q', A', E)
                \<in> tag_delta (\<lambda>p. CRun q p False)
                     (\<lambda>p'. if p' = t_ktm D \<or> p' = r_ktm D then CRej
                           else CRun q p' True)
                     (embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
                        (clock_Gamma N D one) (bl_ktm N) (delta_ktm D))"
    by (auto simp: arm_D_def)
  from tr' obtain p a p' a' d b
    where trD: "(p, a, p', a', d) \<in> delta_ktm D"
      and b: "b \<in> free_context (clock_Gamma N D one) (bl_ktm N)
                     (clock_tapes N D)"
      and Q: "Q = CRun q p False"
      and Q': "Q' = (if p' = t_ktm D \<or> p' = r_ktm D then CRej
                     else CRun q p' True)"
      and Aeq: "A = (\<lambda>j. if k_ktm N \<le> j \<and> j < k_ktm N + k_ktm D
                         then a (j - k_ktm N) else b j)"
      and A'eq: "A' = (\<lambda>j. if k_ktm N \<le> j \<and> j < k_ktm N + k_ktm D
                           then a' (j - k_ktm N) else b j)"
      and Eeq: "E = (\<lambda>j. if k_ktm N \<le> j \<and> j < k_ktm N + k_ktm D
                         then d (j - k_ktm N) else MoveN)"
    by (rule arm_source)
  have win: "\<not> (k_ktm N \<le> j \<and> j < k_ktm N + k_ktm D)"
    if "j \<ge> clock_tapes N D" for j
    using that by (simp add: clock_tapes_def)

  from valid_ktm_delta_set [OF vD] trD
  have pD: "p \<in> Q_ktm D - {t_ktm D, r_ktm D}" and p'D: "p' \<in> Q_ktm D"
    and aG: "\<forall>j. a j \<in> \<Gamma>_ktm D" and a'G: "\<forall>j. a' j \<in> \<Gamma>_ktm D"
    by (auto simp: Pi_iff)
  from b have bG: "\<forall>j. b j \<in> clock_Gamma N D one"
    and bbl: "\<forall>j \<ge> clock_tapes N D. b j = bl_ktm N"
    by (auto simp: free_context_def)

  have "Q \<in> clock_Q N D - {CAcc, CRej}"
    using Q pD q by (auto simp: clock_Q_def)
  moreover have "Q' \<in> clock_Q N D"
    using Q' p'D q by (auto simp: clock_Q_def)
  moreover have "\<forall>j. A j \<in> clock_Gamma N D one"
    using aG bG by (auto simp: Aeq clock_Gamma_def)
  moreover have "\<forall>j. A' j \<in> clock_Gamma N D one"
    using a'G bG by (auto simp: A'eq clock_Gamma_def)
  moreover
  have "\<forall>j. A j = le_ktm N \<longrightarrow> A' j = le_ktm N \<and> E j \<in> {MoveN, MoveR}"
    using valid_ktm_deltaLE [OF vD trD] leD
    by (auto simp: Aeq A'eq Eeq)
  moreover
  have "\<forall>j \<ge> clock_tapes N D. A j = bl_ktm N \<and> A' j = bl_ktm N \<and> E j = MoveN"
    using bbl by (auto simp: Aeq A'eq Eeq win)
  ultimately show ?thesis by (simp add: clock_ok_def)
qed



lemma setup_ok:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and tr: "(Q, A, Q', A', E) \<in> setup_delta N D one"
  shows "clock_ok N D one Q A Q' A' E"
proof -
  have oneG: "one \<in> clock_Gamma N D one" by (simp add: clock_Gamma_def)
  have sN: "s_ktm N \<in> Q_ktm N" using vN by (cases N) auto
  have sD: "s_ktm D \<in> Q_ktm D" using vD by (cases D) auto
  have kless: "k_ktm N < clock_tapes N D"
    using vD by (cases D) (simp add: clock_tapes_def)
  have kpos: "0 < clock_tapes N D"
    using vN by (cases N) (simp add: clock_tapes_def)
  from tr consider
      (walk) a where "Q = CWalk" "A = a" "Q' = CWalk" "A' = a"
                     "E = move_two (k_ktm N) MoveR"
                     "\<forall>j. a j \<in> clock_Gamma N D one"
                     "\<forall>j \<ge> clock_tapes N D. a j = bl_ktm N"
                     "a 0 \<noteq> bl_ktm N"
    | (turn) a where "Q = CWalk" "A = a" "Q' = CBack" "A' = a"
                     "E = move_two (k_ktm N) MoveL"
                     "\<forall>j. a j \<in> clock_Gamma N D one"
                     "\<forall>j \<ge> clock_tapes N D. a j = bl_ktm N"
                     "a 0 = bl_ktm N" "a (k_ktm N) \<noteq> le_ktm N"
    | (rewind) a where "Q = CBack" "A = a" "Q' = CBack"
                     "A' = a(k_ktm N := one)"
                     "E = move_two (k_ktm N) MoveL"
                     "\<forall>j. a j \<in> clock_Gamma N D one"
                     "\<forall>j \<ge> clock_tapes N D. a j = bl_ktm N"
                     "a 0 \<noteq> le_ktm N" "a (k_ktm N) \<noteq> le_ktm N"
    | (home) a where "Q = CBack" "A = a"
                     "Q' = clock_start_state N D" "A' = a"
                     "E = (\<lambda>_. MoveN)"
                     "\<forall>j. a j \<in> clock_Gamma N D one"
                     "\<forall>j \<ge> clock_tapes N D. a j = bl_ktm N"
                     "a 0 = le_ktm N"
    by (auto simp: setup_delta_def clock_ctx_def free_context_def)
  then show ?thesis
  proof cases
    case (walk a)
    then show ?thesis
      using kless kpos by (auto simp: clock_ok_def clock_Q_def move_two_def)
  next
    case (turn a)
    then show ?thesis
      using kless kpos blle
      by (auto simp: clock_ok_def clock_Q_def move_two_def)
  next
    case (rewind a)
    then show ?thesis
      using kless kpos oneG
      by (auto simp: clock_ok_def clock_Q_def move_two_def)
  next
    case (home a)
    then show ?thesis
      using kless kpos sN sD
      by (auto simp: clock_ok_def clock_Q_def move_two_def clock_start_state_def)
  qed
qed



theorem clock_product_valid:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and blD: "bl_ktm D = bl_ktm N" and leD: "le_ktm D = le_ktm N"
  shows "valid_ktm (clock_product N D one)"
proof -
  have vN': "finite (Q_ktm N) \<and> finite (\<Gamma>_ktm N) \<and> Sigma_ktm N \<subseteq> \<Gamma>_ktm N
             \<and> bl_ktm N \<in> \<Gamma>_ktm N \<and> bl_ktm N \<notin> Sigma_ktm N
             \<and> le_ktm N \<in> \<Gamma>_ktm N \<and> le_ktm N \<notin> Sigma_ktm N \<and> 0 < k_ktm N"
    using vN by (cases N) auto
  have vD': "finite (Q_ktm D) \<and> finite (\<Gamma>_ktm D) \<and> 0 < k_ktm D"
    using vD by (cases D) auto

  have ok: "clock_ok N D one Q A Q' A' E"
    if "(Q, A, Q', A', E)
          \<in> setup_delta N D one \<union> arm_N N D one \<union> arm_D N D one"
    for Q A Q' A' E
    using that setup_ok [OF vN vD blle] arm_N_ok [OF vN]
          arm_D_ok [OF vD blD leD] by blast

  have finQ: "finite (clock_Q N D)"
  proof -
    let ?f = "\<lambda>(q, p, b). CRun q p b"
    let ?T = "Q_ktm N \<times> Q_ktm D \<times> (UNIV :: bool set)"
    have "{CRun q p b | q p b. q \<in> Q_ktm N \<and> p \<in> Q_ktm D} \<subseteq> ?f ` ?T"
    proof
      fix x assume "x \<in> {CRun q p b | q p b. q \<in> Q_ktm N \<and> p \<in> Q_ktm D}"
      then obtain q p b where x: "x = CRun q p b"
        and q: "q \<in> Q_ktm N" and p: "p \<in> Q_ktm D" by blast
      from q p have "(q, p, b) \<in> ?T" by simp
      then have "?f (q, p, b) \<in> ?f ` ?T" by (rule imageI)
      with x show "x \<in> ?f ` ?T" by simp
    qed
    moreover have "finite (?f ` ?T)" using vN' vD' by simp
    ultimately have "finite {CRun q p b | q p b. q \<in> Q_ktm N \<and> p \<in> Q_ktm D}"
      by (rule finite_subset)
    then show ?thesis by (simp add: clock_Q_def)
  qed
  have finG: "finite (clock_Gamma N D one)"
    using vN' vD' by (simp add: clock_Gamma_def)
  have SgG: "Sigma_ktm N \<subseteq> clock_Gamma N D one"
    using vN' by (auto simp: clock_Gamma_def)
  have QW: "CWalk \<in> clock_Q N D" and QA: "CAcc \<in> clock_Q N D"
    and QR: "CRej \<in> clock_Q N D" by (auto simp: clock_Q_def)
  have blG: "bl_ktm N \<in> clock_Gamma N D one"
    and leG: "le_ktm N \<in> clock_Gamma N D one"
    using vN' by (auto simp: clock_Gamma_def)
  have kpos: "0 < clock_tapes N D" using vN' by (simp add: clock_tapes_def)

  let ?d = "setup_delta N D one \<union> arm_N N D one \<union> arm_D N D one"
  have dsub: "?d \<subseteq> (clock_Q N D - {CAcc, CRej})
                     \<times> (UNIV \<rightarrow> clock_Gamma N D one)
                     \<times> clock_Q N D
                     \<times> (UNIV \<rightarrow> clock_Gamma N D one)
                     \<times> (UNIV \<rightarrow> UNIV)"
  proof (rule subsetI)
    fix x assume x: "x \<in> ?d"
    obtain Q A Q' A' E where xe: "x = (Q, A, Q', A', E)"
      using prod_cases5 by blast
    from ok [OF x [unfolded xe]] show "x \<in> (clock_Q N D - {CAcc, CRej})
                     \<times> (UNIV \<rightarrow> clock_Gamma N D one)
                     \<times> clock_Q N D
                     \<times> (UNIV \<rightarrow> clock_Gamma N D one)
                     \<times> (UNIV \<rightarrow> UNIV)"
      unfolding xe by (simp add: clock_ok_def Pi_iff)
  qed
  have dle1: "a' j = le_ktm N \<and> d j \<in> {MoveN, MoveR}"
    if "(q, a, q', a', d) \<in> ?d" and "a j = le_ktm N" for q a q' a' d j
    using ok [OF that(1)] that(2) by (simp add: clock_ok_def)
  have dle: "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> ?d \<longrightarrow> a j = le_ktm N
                \<longrightarrow> a' j = le_ktm N \<and> d j \<in> {MoveN, MoveR}"
    using dle1 by blast
  have dsupp1: "a j = bl_ktm N \<and> a' j = bl_ktm N \<and> d j = MoveN"
    if "(q, a, q', a', d) \<in> ?d" and "j \<ge> clock_tapes N D" for q a q' a' d j
    using ok [OF that(1)] that(2) by (simp add: clock_ok_def)
  have dsupp: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> ?d
                  \<longrightarrow> (\<forall>j \<ge> clock_tapes N D.
                          a j = bl_ktm N \<and> a' j = bl_ktm N \<and> d j = MoveN)"
    using dsupp1 by blast

  have tne: "(CAcc :: clock_state) \<noteq> CRej" by simp
  show ?thesis
    unfolding clock_product_def valid_ktm.simps
    using finQ finG SgG QW QA QR blG leG vN' kpos tne dsub dle dsupp by blast
qed


lemma clock_product_le_unique:
  assumes luN: "le_unique N"
      and luD: "le_unique D"
      and leD: "le_ktm D = le_ktm N"
      and one: "one \<noteq> le_ktm N"
  shows "le_unique (clock_product N D one)"
proof -
  have luN': "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> delta_ktm N
                 \<longrightarrow> a' j = le_ktm N \<longrightarrow> a j = le_ktm N"
    using luN unfolding le_unique_def by blast
  have luD': "\<forall>q a q' a' d j. (q, a, q', a', d) \<in> delta_ktm D
                 \<longrightarrow> a' j = le_ktm N \<longrightarrow> a j = le_ktm N"
  proof (intro allI impI)
    fix q a q' a' d and j :: nat
    assume m: "(q, a, q', a', d) \<in> delta_ktm D" and w\<^sub>D: "a' j = le_ktm N"
    from w\<^sub>D leD have "a' j = le_ktm D" by simp
    with luD m have "a j = le_ktm D" unfolding le_unique_def by blast
    with leD show "a j = le_ktm N" by simp
  qed
  show ?thesis
    unfolding le_unique_def
  proof (intro allI impI)
    fix q a q' a' d and j :: nat
    assume mem: "(q, a, q', a', d) \<in> delta_ktm (clock_product N D one)"
       and w: "a' j = le_ktm (clock_product N D one)"
    from w have w': "a' j = le_ktm N" by simp
    from mem
    consider (phase) "(q, a, q', a', d) \<in> setup_delta N D one"
      | (armN) "(q, a, q', a', d) \<in> arm_N N D one"
      | (armD) "(q, a, q', a', d) \<in> arm_D N D one"
      by auto
    then have "a j = le_ktm N"
    proof cases
      case phase
      then show ?thesis
        using w' one by (auto simp: setup_delta_def split: if_split_asm)
    next
      case armN
      then obtain p
        where t: "(q, a, q', a', d)
                    \<in> tag_delta (\<lambda>u. CRun u p True)
                        (\<lambda>u'. if u' = t_ktm N then CAcc else if u' = r_ktm N then CRej else CRun u' p False)
                        (embed_delta 0 (k_ktm N) (clock_tapes N D)
                           (clock_Gamma N D one) (bl_ktm N) (delta_ktm N))"
        unfolding arm_N_def by blast
      show ?thesis
        by (rule tag_delta_le_unique [OF embed_delta_le_unique [OF luN'],
                                      rule_format, OF t w'])
    next
      case armD
      then obtain u
        where t: "(q, a, q', a', d)
                    \<in> tag_delta (\<lambda>p. CRun u p False)
                        (\<lambda>p'. if p' = t_ktm D \<or> p' = r_ktm D then CRej
                              else CRun u p' True)
                        (embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
                           (clock_Gamma N D one) (bl_ktm N) (delta_ktm D))"
        unfolding arm_D_def by blast
      show ?thesis
        by (rule tag_delta_le_unique [OF embed_delta_le_unique [OF luD'],
                                      rule_format, OF t w'])
    qed
    then show "a j = le_ktm (clock_product N D one)" by simp
  qed
qed


subsection \<open>Running the setup phase\<close>


definition setup_tape ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat
     \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "setup_tape N D one w p i m =
     (if i = k_ktm N \<and> p < m \<and> m \<le> length w then one
      else if i < clock_tapes N D
           then (if m = 0 then le_ktm N
                 else if i = 0 \<and> m \<le> length w then w ! (m - 1)
                 else bl_ktm N)
           else bl_ktm N)"

definition setup_pos :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "setup_pos kN p = (\<lambda>j. if j = 0 \<or> j = kN then p else 0)"

lemma clock_init_config:
  "init_config_ktm (clock_product N D one) w
     = KConfig CWalk (setup_tape N D one w (length w)) (setup_pos (k_ktm N) 0)"
  by (simp add: clock_product_def setup_tape_def setup_pos_def fun_eq_iff)


lemma setup_tape_ctx:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and w: "set w \<subseteq> Sigma_ktm N"
  shows "(\<lambda>j. setup_tape N D one w p j (pos j)) \<in> clock_ctx N D one"
proof -
  have vN': "Sigma_ktm N \<subseteq> \<Gamma>_ktm N \<and> bl_ktm N \<in> \<Gamma>_ktm N \<and> le_ktm N \<in> \<Gamma>_ktm N"
    using vN by (cases N) auto
  have SgG: "Sigma_ktm N \<subseteq> clock_Gamma N D one"
    using vN' by (auto simp: clock_Gamma_def)
  have blG: "bl_ktm N \<in> clock_Gamma N D one"
    and leG: "le_ktm N \<in> clock_Gamma N D one"
    using vN' by (auto simp: clock_Gamma_def)
  have oneG: "one \<in> clock_Gamma N D one" by (simp add: clock_Gamma_def)
  have kless: "k_ktm N < clock_tapes N D"
    using vD by (cases D) (simp add: clock_tapes_def)
  have wG: "w ! (m - 1) \<in> clock_Gamma N D one" if "m \<le> length w" and "0 < m"
    for m
  proof -
    from that have "w ! (m - 1) \<in> set w" by simp
    with w SgG show ?thesis by blast
  qed
  show ?thesis
    unfolding clock_ctx_def free_context_def setup_tape_def
    using blG leG oneG wG kless by auto
qed


lemma setup_step:
  assumes tup: "(Q, (\<lambda>j. ts j (pos j)), Q', a', d) \<in> setup_delta N D one"
  shows "(KConfig Q ts pos,
          KConfig Q' (\<lambda>j. (ts j)(pos j := a' j)) (\<lambda>j. go_move (d j) (pos j)))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof (rule ktm_step.step)
  show "(Q, \<lambda>j. ts j (pos j), Q', a', d)
          \<in> delta_ktm (clock_product N D one)"
    using tup by simp
qed



lemma setup_walk_step:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and p: "p \<le> length w"
  shows "(KConfig CWalk (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) p),
          KConfig CWalk (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) (Suc p)))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof -
  let ?ts = "setup_tape N D one w (length w)"
  let ?pos = "setup_pos (k_ktm N) p"
  let ?a = "\<lambda>j. ?ts j (?pos j)"
  have kN: "0 < k_ktm N" using vN by (cases N) auto
  have blS: "bl_ktm N \<notin> Sigma_ktm N" using vN by (cases N) auto
  have a0: "?a 0 \<noteq> bl_ktm N"
  proof (cases "p = 0")
    case True
    then show ?thesis
      using blle kN
      by (simp add: setup_tape_def setup_pos_def clock_tapes_def)
  next
    case False
    with p have "w ! (p - 1) \<in> set w" by simp
    with w blS have "w ! (p - 1) \<noteq> bl_ktm N" by auto
    with False p kN show ?thesis
      by (simp add: setup_tape_def setup_pos_def clock_tapes_def)
  qed
  have mem: "(CWalk, ?a, CWalk, ?a, move_two (k_ktm N) MoveR)
               \<in> setup_delta N D one"
    using setup_tape_ctx [OF vN vD w] a0 by (auto simp: setup_delta_def)
  from setup_step [where ts = "?ts" and pos = "?pos", OF mem]
  have "(KConfig CWalk ?ts ?pos,
         KConfig CWalk (\<lambda>j. (?ts j)(?pos j := ?a j))
                     (\<lambda>j. go_move (move_two (k_ktm N) MoveR j) (?pos j)))
          \<in> ktm_step (delta_ktm (clock_product N D one))" .
  moreover have "(\<lambda>j. (?ts j)(?pos j := ?a j)) = ?ts" by (simp add: fun_eq_iff)
  moreover have "(\<lambda>j. go_move (move_two (k_ktm N) MoveR j) (?pos j))
                   = setup_pos (k_ktm N) (Suc p)"
    by (simp add: fun_eq_iff move_two_def setup_pos_def)
  ultimately show ?thesis by simp
qed


lemma setup_turn_step:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
  shows "(KConfig CWalk (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) (Suc (length w))),
          KConfig CBack (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) (length w)))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof -
  let ?ts = "setup_tape N D one w (length w)"
  let ?pos = "setup_pos (k_ktm N) (Suc (length w))"
  let ?a = "\<lambda>j. ?ts j (?pos j)"
  have kN: "0 < k_ktm N" using vN by (cases N) auto
  have kless: "k_ktm N < clock_tapes N D"
    using vD by (cases D) (simp add: clock_tapes_def)
  have a0: "?a 0 = bl_ktm N"
    using kN by (simp add: setup_tape_def setup_pos_def clock_tapes_def)
  have ak: "?a (k_ktm N) \<noteq> le_ktm N"
    using kN kless blle by (simp add: setup_tape_def setup_pos_def)
  have mem: "(CWalk, ?a, CBack, ?a, move_two (k_ktm N) MoveL)
               \<in> setup_delta N D one"
    using setup_tape_ctx [OF vN vD w] a0 ak by (auto simp: setup_delta_def)
  from setup_step [where ts = "?ts" and pos = "?pos", OF mem]
  have "(KConfig CWalk ?ts ?pos,
         KConfig CBack (\<lambda>j. (?ts j)(?pos j := ?a j))
                     (\<lambda>j. go_move (move_two (k_ktm N) MoveL j) (?pos j)))
          \<in> ktm_step (delta_ktm (clock_product N D one))" .
  moreover have "(\<lambda>j. (?ts j)(?pos j := ?a j)) = ?ts" by (simp add: fun_eq_iff)
  moreover have "(\<lambda>j. go_move (move_two (k_ktm N) MoveL j) (?pos j))
                   = setup_pos (k_ktm N) (length w)"
    by (simp add: fun_eq_iff move_two_def setup_pos_def)
  ultimately show ?thesis by simp
qed



lemma setup_rewind_step:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and p1: "0 < p" and pn: "p \<le> length w"
  shows "(KConfig CBack (setup_tape N D one w p) (setup_pos (k_ktm N) p),
          KConfig CBack (setup_tape N D one w (p - 1))
                      (setup_pos (k_ktm N) (p - 1)))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof -
  let ?ts = "setup_tape N D one w p"
  let ?pos = "setup_pos (k_ktm N) p"
  let ?a = "\<lambda>j. ?ts j (?pos j)"
  have kN: "0 < k_ktm N" using vN by (cases N) auto
  have leS: "le_ktm N \<notin> Sigma_ktm N" using vN by (cases N) auto
  have kless: "k_ktm N < clock_tapes N D"
    using vD by (cases D) (simp add: clock_tapes_def)
  from p1 pn have "w ! (p - 1) \<in> set w" by simp
  with w leS have wne: "w ! (p - 1) \<noteq> le_ktm N" by auto
  have a0: "?a 0 \<noteq> le_ktm N"
    using wne p1 pn kN by (simp add: setup_tape_def setup_pos_def clock_tapes_def)
  have ak: "?a (k_ktm N) \<noteq> le_ktm N"
    using kN kless p1 blle by (simp add: setup_tape_def setup_pos_def)
  have mem: "(CBack, ?a, CBack, ?a(k_ktm N := one), move_two (k_ktm N) MoveL)
               \<in> setup_delta N D one"
    using setup_tape_ctx [OF vN vD w] a0 ak by (auto simp: setup_delta_def)
  from setup_step [where ts = "?ts" and pos = "?pos", OF mem]
  have "(KConfig CBack ?ts ?pos,
         KConfig CBack (\<lambda>j. (?ts j)(?pos j := (?a(k_ktm N := one)) j))
                     (\<lambda>j. go_move (move_two (k_ktm N) MoveL j) (?pos j)))
          \<in> ktm_step (delta_ktm (clock_product N D one))" .
  moreover
  have "(\<lambda>j. (?ts j)(?pos j := (?a(k_ktm N := one)) j))
          = setup_tape N D one w (p - 1)"
    using p1 pn kN kless by (auto simp: fun_eq_iff setup_tape_def setup_pos_def)
  moreover have "(\<lambda>j. go_move (move_two (k_ktm N) MoveL j) (?pos j))
                   = setup_pos (k_ktm N) (p - 1)"
    by (simp add: fun_eq_iff move_two_def setup_pos_def)
  ultimately show ?thesis by simp
qed


lemma setup_home_step:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and w: "set w \<subseteq> Sigma_ktm N"
  shows "(KConfig CBack (setup_tape N D one w 0) (setup_pos (k_ktm N) 0),
          KConfig (clock_start_state N D) (setup_tape N D one w 0)
                  (setup_pos (k_ktm N) 0))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof -
  let ?ts = "setup_tape N D one w 0"
  let ?pos = "setup_pos (k_ktm N) 0"
  let ?a = "\<lambda>j. ?ts j (?pos j)"
  have kN: "0 < k_ktm N" using vN by (cases N) auto
  have a0: "?a 0 = le_ktm N"
    using kN by (simp add: setup_tape_def setup_pos_def clock_tapes_def)
  have mem: "(CBack, ?a, clock_start_state N D, ?a, \<lambda>_. MoveN)
               \<in> setup_delta N D one"
    using setup_tape_ctx [OF vN vD w] a0 by (auto simp: setup_delta_def)
  from setup_step [where ts = "?ts" and pos = "?pos", OF mem]
  have "(KConfig CBack ?ts ?pos,
         KConfig (clock_start_state N D)
                 (\<lambda>j. (?ts j)(?pos j := ?a j))
                 (\<lambda>j. go_move ((\<lambda>_. MoveN) j) (?pos j)))
          \<in> ktm_step (delta_ktm (clock_product N D one))" .
  moreover have "(\<lambda>j. (?ts j)(?pos j := ?a j)) = ?ts" by (simp add: fun_eq_iff)
  moreover have "(\<lambda>j. go_move ((\<lambda>_. MoveN) j) (?pos j)) = ?pos"
    by (simp add: fun_eq_iff)
  ultimately show ?thesis by simp
qed



lemma setup_walk_run:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and p: "p \<le> Suc (length w)"
  shows "(KConfig CWalk (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) 0),
          KConfig CWalk (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) p))
           \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ p"
  using p
proof (induction p)
  case 0
  show ?case by simp
next
  case (Suc q)
  from Suc.prems have q: "q \<le> length w" by simp
  then have q': "q \<le> Suc (length w)" by simp
  from Suc.IH [OF q'] setup_walk_step [OF vN vD blle w q]
  show ?case by (rule relpow_Suc_I)
qed

lemma setup_rewind_run:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and r: "r \<le> length w"
  shows "(KConfig CBack (setup_tape N D one w (length w))
                      (setup_pos (k_ktm N) (length w)),
          KConfig CBack (setup_tape N D one w (length w - r))
                      (setup_pos (k_ktm N) (length w - r)))
           \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ r"
  using r
proof (induction r)
  case 0
  show ?case by simp
next
  case (Suc r)
  from Suc.prems have r: "r \<le> length w" by simp
  have pos: "0 < length w - r" using Suc.prems by simp
  have le: "length w - r \<le> length w" by simp
  from Suc.IH [OF r] setup_rewind_step [OF vN vD blle w pos le]
  have "(KConfig CBack (setup_tape N D one w (length w))
                     (setup_pos (k_ktm N) (length w)),
         KConfig CBack (setup_tape N D one w (length w - r - 1))
                     (setup_pos (k_ktm N) (length w - r - 1)))
          \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ Suc r"
    by (rule relpow_Suc_I)
  then show ?case by simp
qed


lemma setup_run:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
  shows "(init_config_ktm (clock_product N D one) w,
          KConfig (clock_start_state N D) (setup_tape N D one w 0)
                  (setup_pos (k_ktm N) 0))
           \<in> (ktm_step (delta_ktm (clock_product N D one)))
                ^^ (2 * length w + 3)"
proof -
  let ?R = "ktm_step (delta_ktm (clock_product N D one))"
  let ?ts = "setup_tape N D one w (length w)"
  let ?n = "length w"
  have walk: "(KConfig CWalk ?ts (setup_pos (k_ktm N) 0),
               KConfig CWalk ?ts (setup_pos (k_ktm N) (Suc ?n))) \<in> ?R ^^ Suc ?n"
    by (rule setup_walk_run [OF vN vD blle w le_refl])
  from walk setup_turn_step [OF vN vD blle w]
  have turned: "(KConfig CWalk ?ts (setup_pos (k_ktm N) 0),
                 KConfig CBack ?ts (setup_pos (k_ktm N) ?n))
                  \<in> ?R ^^ Suc (Suc ?n)"
    by (rule relpow_Suc_I)
  have homeward: "(KConfig CBack ?ts (setup_pos (k_ktm N) ?n),
               KConfig CBack (setup_tape N D one w 0) (setup_pos (k_ktm N) 0))
                \<in> ?R ^^ ?n"
    using setup_rewind_run [OF vN vD blle w le_refl] by simp
  from turned homeward
  have "(KConfig CWalk ?ts (setup_pos (k_ktm N) 0),
         KConfig CBack (setup_tape N D one w 0) (setup_pos (k_ktm N) 0))
          \<in> ?R ^^ (Suc (Suc ?n) + ?n)"
    unfolding relpow_add by (rule relcompI)
  from this setup_home_step [OF vN vD w]
  have whole: "(KConfig CWalk ?ts (setup_pos (k_ktm N) 0),
                KConfig (clock_start_state N D) (setup_tape N D one w 0)
                        (setup_pos (k_ktm N) 0))
                 \<in> ?R ^^ Suc (Suc (Suc ?n) + ?n)"
    by (rule relpow_Suc_I)
  have eq: "2 * ?n + 3 = Suc (Suc (Suc ?n) + ?n)" by simp
  show ?thesis unfolding clock_init_config eq by (rule whole)
qed



definition setup_config ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat
     \<Rightarrow> (nat, clock_state) ktc_config" where
  "setup_config N D one w i =
     (if i \<le> Suc (length w)
      then KConfig CWalk (setup_tape N D one w (length w))
                        (setup_pos (k_ktm N) i)
      else if i \<le> 2 * length w + 2
      then KConfig CBack (setup_tape N D one w (2 * length w + 2 - i))
                        (setup_pos (k_ktm N) (2 * length w + 2 - i))
      else KConfig (clock_start_state N D)
                   (setup_tape N D one w 0) (setup_pos (k_ktm N) 0))"

lemma setup_config_0:
  "setup_config N D one w 0 = init_config_ktm (clock_product N D one) w"
  by (simp add: setup_config_def clock_init_config)

lemma setup_config_end:
  "setup_config N D one w (2 * length w + 3)
     = KConfig (clock_start_state N D)
               (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
  by (simp add: setup_config_def)


lemma setup_config_step:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and i: "i < 2 * length w + 3"
  shows "(setup_config N D one w i, setup_config N D one w (Suc i))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof -
  let ?n = "length w"
  consider (Walk) "i \<le> ?n" | (Turn) "i = Suc ?n"
    | (Back) "Suc ?n < i" and "i \<le> 2 * ?n + 1"
    | (Home) "i = 2 * ?n + 2"
    using i by linarith
  then show ?thesis
  proof cases
    case Walk
    then have "setup_config N D one w i
                 = KConfig CWalk (setup_tape N D one w ?n) (setup_pos (k_ktm N) i)"
      and "setup_config N D one w (Suc i)
                 = KConfig CWalk (setup_tape N D one w ?n)
                                (setup_pos (k_ktm N) (Suc i))"
      by (simp_all add: setup_config_def)
    with setup_walk_step [OF vN vD blle w Walk] show ?thesis by simp
  next
    case Turn
    then have "setup_config N D one w i
                 = KConfig CWalk (setup_tape N D one w ?n)
                                (setup_pos (k_ktm N) (Suc ?n))"
      and "setup_config N D one w (Suc i)
                 = KConfig CBack (setup_tape N D one w ?n) (setup_pos (k_ktm N) ?n)"
      by (simp_all add: setup_config_def)
    with setup_turn_step [OF vN vD blle w] show ?thesis by simp
  next
    case Back
    define p where "p = 2 * ?n + 2 - i"
    from Back have p1: "0 < p" and pn: "p \<le> ?n" by (simp_all add: p_def)
    from Back have "setup_config N D one w i
                      = KConfig CBack (setup_tape N D one w p) (setup_pos (k_ktm N) p)"
      by (simp add: setup_config_def p_def)
    moreover from Back have "setup_config N D one w (Suc i)
                      = KConfig CBack (setup_tape N D one w (p - 1))
                                     (setup_pos (k_ktm N) (p - 1))"
      by (simp add: setup_config_def p_def)
    ultimately show ?thesis
      using setup_rewind_step [OF vN vD blle w p1 pn] by simp
  next
    case Home
    then have "setup_config N D one w i
                 = KConfig CBack (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
      and "setup_config N D one w (Suc i)
                 = KConfig (clock_start_state N D)
                           (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
      by (simp_all add: setup_config_def)
    with setup_home_step [OF vN vD w] show ?thesis by simp
  qed
qed


subsection \<open>A step of a factor is a step of the product\<close>


lemma arm_N_step:
  assumes p: "p \<in> Q_ktm D"
      and step: "(proj_config 0 (k_ktm N) (bl_ktm N) C, c')
                   \<in> ktm_step (delta_ktm N)"
      and ctx: "(\<lambda>j. ktc_tape C j (ktc_pos C j))
                  \<in> free_context (clock_Gamma N D one) (bl_ktm N)
                        (clock_tapes N D)"
  shows "(ktc_set_state (CRun (ktc_state C) p True) C,
          ktc_set_state (if ktc_state c' = t_ktm N then CAcc
                   else if ktc_state c' = r_ktm N then CRej
                   else CRun (ktc_state c') p False)
                  (embed_update 0 (k_ktm N) C c'))
           \<in> ktm_step (arm_N N D one)"
proof -
  let ?u = "\<lambda>q. CRun q p True"
  let ?v = "\<lambda>q'. if q' = t_ktm N then CAcc else if q' = r_ktm N then CRej else CRun q' p False"
  let ?E = "embed_delta 0 (k_ktm N) (clock_tapes N D)
              (clock_Gamma N D one) (bl_ktm N) (delta_ktm N)"
  have inner: "(ktc_set_state (?u (ktc_state C)) C,
                ktc_set_state (?v (ktc_state c')) (embed_update 0 (k_ktm N) C c'))
                 \<in> ktm_step (tag_delta ?u ?v ?E)"
    using tag_step [where u = ?u and v = ?v, OF embed_step [OF step ctx]]
    by (simp only: embed_update_state)
  have sub: "tag_delta ?u ?v ?E \<subseteq> arm_N N D one"
    using p by (auto simp: arm_N_def)
  from ktm_step_mono [OF sub] inner show ?thesis by blast
qed

lemma arm_D_step:
  assumes q: "q \<in> Q_ktm N"
      and step: "(proj_config (k_ktm N) (k_ktm D) (bl_ktm N) C, c')
                   \<in> ktm_step (delta_ktm D)"
      and ctx: "(\<lambda>j. ktc_tape C j (ktc_pos C j))
                  \<in> free_context (clock_Gamma N D one) (bl_ktm N)
                        (clock_tapes N D)"
  shows "(ktc_set_state (CRun q (ktc_state C) False) C,
          ktc_set_state (if ktc_state c' = t_ktm D \<or> ktc_state c' = r_ktm D then CRej
                   else CRun q (ktc_state c') True)
                  (embed_update (k_ktm N) (k_ktm D) C c'))
           \<in> ktm_step (arm_D N D one)"
proof -
  let ?u = "\<lambda>r. CRun q r False"
  let ?v = "\<lambda>r'. if r' = t_ktm D \<or> r' = r_ktm D then CRej else CRun q r' True"
  let ?E = "embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
              (clock_Gamma N D one) (bl_ktm N) (delta_ktm D)"
  have inner: "(ktc_set_state (?u (ktc_state C)) C,
                ktc_set_state (?v (ktc_state c'))
                        (embed_update (k_ktm N) (k_ktm D) C c'))
                 \<in> ktm_step (tag_delta ?u ?v ?E)"
    using tag_step [where u = ?u and v = ?v, OF embed_step [OF step ctx]]
    by (simp only: embed_update_state)
  have sub: "tag_delta ?u ?v ?E \<subseteq> arm_D N D one"
    using q by (auto simp: arm_D_def)
  from ktm_step_mono [OF sub] inner show ?thesis by blast
qed


subsection \<open>One turn of the clock\<close>


definition clock_inv ::
  "(nat, nat) ktm \<Rightarrow> (nat, nat) ktm \<Rightarrow> nat
     \<Rightarrow> (nat, nat) ktc_config \<Rightarrow> (nat, nat) ktc_config \<Rightarrow> (nat, nat) ktc_config
     \<Rightarrow> bool" where
  "clock_inv N D one C cN cD \<longleftrightarrow>
     proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C) = cN
   \<and> proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state (ktc_state cD) C) = cD
   \<and> (\<forall>j m. ktc_tape C j m \<in> clock_Gamma N D one)
   \<and> (\<forall>j m. clock_tapes N D \<le> j \<longrightarrow> ktc_tape C j m = bl_ktm N)"


lemma clock_inv_ctx:
  assumes "clock_inv N D one C cN cD"
  shows "(\<lambda>j. ktc_tape (ktc_set_state Q C) j (ktc_pos (ktc_set_state Q C) j))
           \<in> free_context (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D)"
  using assms by (auto simp: clock_inv_def free_context_def)


lemma clock_inv_set_state [simp]:
  "clock_inv N D one (ktc_set_state p C) cN cD = clock_inv N D one C cN cD"
  by (simp add: clock_inv_def)


lemma clock_step_N:
  assumes p: "p \<in> Q_ktm D"
      and inv: "clock_inv N D one C cN cD"
      and step: "(cN, cN') \<in> ktm_step (delta_ktm N)"
      and tapes: "ktc_tapes_fit (\<Gamma>_ktm N) (bl_ktm N) (k_ktm N) cN'"
      and heads: "heads_parked (k_ktm N) cN'"
      and nacc: "ktc_state cN' \<noteq> t_ktm N"
      and nrej: "ktc_state cN' \<noteq> r_ktm N"
  obtains C'
  where "(ktc_set_state (CRun (ktc_state cN) p True) C,
          ktc_set_state (CRun (ktc_state cN') p False) C')
           \<in> ktm_step (delta_ktm (clock_product N D one))"
    and "clock_inv N D one C' cN' cD"
proof -
  let ?C = "ktc_set_state (ktc_state cN) C"
  let ?C' = "embed_update 0 (k_ktm N) C cN'"
  from inv have pN: "proj_config 0 (k_ktm N) (bl_ktm N) ?C = cN"
    and pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state (ktc_state cD) C) = cD"
    and tG: "\<And>j m. ktc_tape C j m \<in> clock_Gamma N D one"
    and tB: "\<And>j m. clock_tapes N D \<le> j \<Longrightarrow> ktc_tape C j m = bl_ktm N"
    by (auto simp: clock_inv_def)

  have step': "(proj_config 0 (k_ktm N) (bl_ktm N) ?C, cN') \<in> ktm_step (delta_ktm N)"
    using pN step by simp
  have arm: "(ktc_set_state (CRun (ktc_state cN) p True) C,
              ktc_set_state (CRun (ktc_state cN') p False) ?C')
               \<in> ktm_step (arm_N N D one)"
    using arm_N_step [OF p step' clock_inv_ctx [OF inv]] nacc nrej by simp
  have sub: "arm_N N D one \<subseteq> delta_ktm (clock_product N D one)" by auto
  from ktm_step_mono [OF sub] arm
  have theStep: "(ktc_set_state (CRun (ktc_state cN) p True) C,
                  ktc_set_state (CRun (ktc_state cN') p False) ?C')
                   \<in> ktm_step (delta_ktm (clock_product N D one))" by blast

  have pN': "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN') ?C') = cN'"
    by (simp add: proj_embed_update [OF frame_tail [OF tapes heads]])
  have pD': "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
               (ktc_set_state (ktc_state cD) ?C') = cD"
    using pD by (simp add: proj_embed_update_disjoint)

  have inside: "ktc_tape cN' j m \<in> clock_Gamma N D one" for j m
    using tapes by (auto simp: ktc_tapes_fit_def clock_Gamma_def)
  have tG': "ktc_tape ?C' j m \<in> clock_Gamma N D one" for j m
    using inside tG by (simp add: embed_update_def)
  have tB': "ktc_tape ?C' j m = bl_ktm N" if "clock_tapes N D \<le> j" for j m
  proof -
    from that have "\<not> j < k_ktm N" by (simp add: clock_tapes_def)
    with that show ?thesis using tB by (simp add: embed_update_def)
  qed
  have inv': "clock_inv N D one ?C' cN' cD"
    unfolding clock_inv_def using pN' pD' tG' tB' by blast
  from theStep inv' show thesis by (rule that)
qed


lemma clock_step_D:
  assumes q: "q \<in> Q_ktm N"
      and inv: "clock_inv N D one C cN cD"
      and step: "(cD, cD') \<in> ktm_step (delta_ktm D)"
      and tapes: "ktc_tapes_fit (\<Gamma>_ktm D) (bl_ktm N) (k_ktm D) cD'"
      and heads: "heads_parked (k_ktm D) cD'"
      and nhalt: "ktc_state cD' \<noteq> t_ktm D" "ktc_state cD' \<noteq> r_ktm D"
  obtains C'
  where "(ktc_set_state (CRun q (ktc_state cD) False) C,
          ktc_set_state (CRun q (ktc_state cD') True) C')
           \<in> ktm_step (delta_ktm (clock_product N D one))"
    and "clock_inv N D one C' cN cD'"
proof -
  let ?C = "ktc_set_state (ktc_state cD) C"
  let ?C' = "embed_update (k_ktm N) (k_ktm D) C cD'"
  from inv have pN: "proj_config 0 (k_ktm N) (bl_ktm N)
                       (ktc_set_state (ktc_state cN) C) = cN"
    and pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N) ?C = cD"
    and tG: "\<And>j m. ktc_tape C j m \<in> clock_Gamma N D one"
    and tB: "\<And>j m. clock_tapes N D \<le> j \<Longrightarrow> ktc_tape C j m = bl_ktm N"
    by (auto simp: clock_inv_def)

  have step': "(proj_config (k_ktm N) (k_ktm D) (bl_ktm N) ?C, cD')
                 \<in> ktm_step (delta_ktm D)"
    using pD step by simp
  have arm: "(ktc_set_state (CRun q (ktc_state cD) False) C,
              ktc_set_state (CRun q (ktc_state cD') True) ?C')
               \<in> ktm_step (arm_D N D one)"
    using arm_D_step [OF q step' clock_inv_ctx [OF inv]] nhalt by simp
  have sub: "arm_D N D one \<subseteq> delta_ktm (clock_product N D one)" by auto
  from ktm_step_mono [OF sub] arm
  have theStep: "(ktc_set_state (CRun q (ktc_state cD) False) C,
                  ktc_set_state (CRun q (ktc_state cD') True) ?C')
                   \<in> ktm_step (delta_ktm (clock_product N D one))" by blast

  have pD': "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
               (ktc_set_state (ktc_state cD') ?C') = cD'"
    by (simp add: proj_embed_update [OF frame_tail [OF tapes heads]])
  have pN': "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) ?C') = cN"
    using pN by (simp add: proj_embed_update_disjoint)

  have inside: "ktc_tape cD' j m \<in> clock_Gamma N D one" for j m
    using tapes by (auto simp: ktc_tapes_fit_def clock_Gamma_def)
  have tG': "ktc_tape ?C' j m \<in> clock_Gamma N D one" for j m
    using inside tG by (simp add: embed_update_def)
  have tB': "ktc_tape ?C' j m = bl_ktm N" if "clock_tapes N D \<le> j" for j m
  proof -
    from that have "\<not> j < k_ktm N + k_ktm D" by (simp add: clock_tapes_def)
    with that show ?thesis using tB by (simp add: embed_update_def)
  qed
  have inv': "clock_inv N D one ?C' cN cD'"
    unfolding clock_inv_def using pN' pD' tG' tB' by blast
  from theStep inv' show thesis by (rule that)
qed


lemma clock_tick:
  assumes inv: "clock_inv N D one C cN cD"
      and blD: "bl_ktm D = bl_ktm N"
      and qD: "ktc_state cD \<in> Q_ktm D"
      and stepN: "(cN, cN') \<in> ktm_step (delta_ktm N)"
      and stepD: "(cD, cD') \<in> ktm_step (delta_ktm D)"
      and vcN: "valid_config_ktm N cN'"
      and vcD: "valid_config_ktm D cD'"
      and headsN: "heads_parked (k_ktm N) cN'"
      and headsD: "heads_parked (k_ktm D) cD'"
      and nacc: "ktc_state cN' \<noteq> t_ktm N"
      and nrej: "ktc_state cN' \<noteq> r_ktm N"
      and nhalt: "ktc_state cD' \<noteq> t_ktm D" "ktc_state cD' \<noteq> r_ktm D"
  obtains C'
  where "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C,
          ktc_set_state (CRun (ktc_state cN') (ktc_state cD') True) C')
           \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ 2"
    and "clock_inv N D one C' cN' cD'"
proof -
  have tN: "ktc_tapes_fit (\<Gamma>_ktm N) (bl_ktm N) (k_ktm N) cN'"
    by (rule valid_config_tapes_fit [OF vcN])
  have tD: "ktc_tapes_fit (\<Gamma>_ktm D) (bl_ktm N) (k_ktm D) cD'"
    using valid_config_tapes_fit [OF vcD] blD by simp
  have qN': "ktc_state cN' \<in> Q_ktm N" by (rule valid_config_state [OF vcN])

  from clock_step_N [OF qD inv stepN tN headsN nacc nrej]
  obtain C1
    where s1: "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C,
                ktc_set_state (CRun (ktc_state cN') (ktc_state cD) False) C1)
                 \<in> ktm_step (delta_ktm (clock_product N D one))"
      and inv1: "clock_inv N D one C1 cN' cD" by blast
  from clock_step_D [OF qN' inv1 stepD tD headsD nhalt]
  obtain C2
    where s2: "(ktc_set_state (CRun (ktc_state cN') (ktc_state cD) False) C1,
                ktc_set_state (CRun (ktc_state cN') (ktc_state cD') True) C2)
                 \<in> ktm_step (delta_ktm (clock_product N D one))"
      and inv2: "clock_inv N D one C2 cN' cD'" by blast

  have both: "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C,
               ktc_set_state (CRun (ktc_state cN') (ktc_state cD') True) C2)
                \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ 2"
    using relcompI [OF s1 s2] by (simp add: numeral_2_eq_2)
  from both inv2 show thesis by (rule that)
qed


lemma clock_run:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blD: "bl_ktm D = bl_ktm N"
      and vcN0: "valid_config_ktm N cN\<^sub>0"
      and vcD0: "valid_config_ktm D cD\<^sub>0"
      and hN0: "heads_parked (k_ktm N) cN\<^sub>0"
      and hD0: "heads_parked (k_ktm D) cD\<^sub>0"
      and inv0: "clock_inv N D one C\<^sub>0 cN\<^sub>0 cD\<^sub>0"
      and runN: "(cN\<^sub>0, cN) \<in> (ktm_step (delta_ktm N)) ^^ m"
      and runD: "(cD\<^sub>0, cD) \<in> (ktm_step (delta_ktm D)) ^^ m"
      and nacc: "ktc_state cN \<noteq> t_ktm N"
      and nrej: "ktc_state cN \<noteq> r_ktm N"
      and nhalt: "ktc_state cD \<noteq> t_ktm D" "ktc_state cD \<noteq> r_ktm D"
    shows "\<exists>C. (ktc_set_state (CRun (ktc_state cN\<^sub>0) (ktc_state cD\<^sub>0) True) C\<^sub>0,
                ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C)
                 \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ (2 * m)
             \<and> clock_inv N D one C cN cD"
  using runN runD nacc nrej nhalt
proof (induction m arbitrary: cN cD)
  case 0
  then show ?case using inv0 by auto
next
  case (Suc m)
  from Suc.prems(1) obtain c
    where cRun: "(cN\<^sub>0, c) \<in> (ktm_step (delta_ktm N)) ^^ m"
      and cStep: "(c, cN) \<in> ktm_step (delta_ktm N)" by auto
  from Suc.prems(2) obtain d
    where dRun: "(cD\<^sub>0, d) \<in> (ktm_step (delta_ktm D)) ^^ m"
      and dStep: "(d, cD) \<in> ktm_step (delta_ktm D)" by auto

  from cStep have cAlive: "ktc_state c \<notin> {t_ktm N, r_ktm N}"
    using halt_state_sink [OF vN] by blast
  from dStep have dAlive: "ktc_state d \<notin> {t_ktm D, r_ktm D}"
    using halt_state_sink [OF vD] by blast

  from Suc.IH [OF cRun dRun] cAlive dAlive obtain C1
    where prefix: "(ktc_set_state (CRun (ktc_state cN\<^sub>0) (ktc_state cD\<^sub>0) True) C\<^sub>0,
                    ktc_set_state (CRun (ktc_state c) (ktc_state d) True) C1)
                     \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ (2 * m)"
      and inv1: "clock_inv N D one C1 c d" by auto

  have qD: "ktc_state d \<in> Q_ktm D"
    by (rule valid_config_state [OF valid_reach_relpow_ktm [OF vD vcD0 dRun]])
  have vcN: "valid_config_ktm N cN"
    by (rule valid_reach_relpow_ktm [OF vN vcN0 Suc.prems(1)])
  have vcD: "valid_config_ktm D cD"
    by (rule valid_reach_relpow_ktm [OF vD vcD0 Suc.prems(2)])
  have hN: "heads_parked (k_ktm N) cN" by (rule heads_parked_run [OF vN hN0 Suc.prems(1)])
  have hD: "heads_parked (k_ktm D) cD" by (rule heads_parked_run [OF vD hD0 Suc.prems(2)])

  from clock_tick [OF inv1 blD qD cStep dStep vcN vcD hN hD
                      Suc.prems(3) Suc.prems(4) Suc.prems(5) Suc.prems(6)]
  obtain C2
    where tick: "(ktc_set_state (CRun (ktc_state c) (ktc_state d) True) C1,
                  ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C2)
                   \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ 2"
      and inv2: "clock_inv N D one C2 cN cD" by blast

  have arith: "2 * Suc m = 2 * m + 2" by simp
  from prefix tick
  have "(ktc_set_state (CRun (ktc_state cN\<^sub>0) (ktc_state cD\<^sub>0) True) C\<^sub>0,
         ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C2)
          \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ (2 * Suc m)"
    unfolding arith relpow_add by (rule relcompI)
  with inv2 show ?case by blast
qed


lemma clock_setup_inv:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blD: "bl_ktm D = bl_ktm N" and leD: "le_ktm D = le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
  shows "clock_inv N D one
           (KConfig Q (setup_tape N D one w 0) (setup_pos (k_ktm N) 0))
           (init_config_ktm N w)
           (init_config_ktm D (replicate (length w) one))"
proof -
  from vN have kN: "0 < k_ktm N" and SG: "Sigma_ktm N \<subseteq> \<Gamma>_ktm N"
    and blG: "bl_ktm N \<in> \<Gamma>_ktm N" and leG: "le_ktm N \<in> \<Gamma>_ktm N" by (cases N, auto)+
  from vD have kD: "0 < k_ktm D" by (cases D) auto
  have kt: "clock_tapes N D = k_ktm N + k_ktm D" by (simp add: clock_tapes_def)

  have pN: "proj_config 0 (k_ktm N) (bl_ktm N)
              (ktc_set_state (ktc_state (init_config_ktm N w))
                       (KConfig Q (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)))
                = init_config_ktm N w" (is "?L = ?R")
  proof (rule ktc_config.expand, intro conjI)
    show "ktc_tape ?L = ktc_tape ?R"
      using kN kD
      by (simp add: setup_tape_def kt ktc_tape_init_config fun_eq_iff)
  qed (simp_all add: setup_pos_def fun_eq_iff)

  have pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
              (ktc_set_state (ktc_state (init_config_ktm D (replicate (length w) one)))
                       (KConfig Q (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)))
                = init_config_ktm D (replicate (length w) one)" (is "?L = ?R")
  proof (rule ktc_config.expand, intro conjI)
    have rep: "replicate (length w) one ! (m - Suc 0) = one"
      if "0 < m" and "m \<le> length w" for m
      using that by simp
    show "ktc_tape ?L = ktc_tape ?R"
      using kN kD blD leD
      by (simp add: setup_tape_def kt ktc_tape_init_config fun_eq_iff rep)
  qed (simp_all add: setup_pos_def fun_eq_iff)

  have wG: "w ! (m - 1) \<in> \<Gamma>_ktm N" if "m \<le> length w" and "0 < m" for m
  proof -
    from that have "w ! (m - 1) \<in> set w" by simp
    with w SG show ?thesis by blast
  qed
  have tG: "setup_tape N D one w 0 j m \<in> clock_Gamma N D one" for j m
    using wG blG leG by (auto simp: setup_tape_def clock_Gamma_def)
  have tB: "setup_tape N D one w 0 j m = bl_ktm N" if "clock_tapes N D \<le> j" for j m
  proof -
    from that kD have "j \<noteq> k_ktm N" and "\<not> j < clock_tapes N D" by (auto simp: kt)
    then show ?thesis by (simp add: setup_tape_def)
  qed
  show ?thesis unfolding clock_inv_def using pN pD tG tB by simp
qed


lemma clock_accept_step:
  assumes p: "p \<in> Q_ktm D"
      and inv: "clock_inv N D one C cN cD"
      and step: "(cN, cN') \<in> ktm_step (delta_ktm N)"
      and acc: "ktc_state cN' = t_ktm N"
  shows "(ktc_set_state (CRun (ktc_state cN) p True) C,
          ktc_set_state CAcc (embed_update 0 (k_ktm N) C cN'))
           \<in> ktm_step (delta_ktm (clock_product N D one))"
proof -
  from inv have pN: "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C) = cN"
    by (simp add: clock_inv_def)
  have step': "(proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C), cN')
                 \<in> ktm_step (delta_ktm N)"
    using pN step by simp
  have arm: "(ktc_set_state (CRun (ktc_state cN) p True) C,
              ktc_set_state CAcc (embed_update 0 (k_ktm N) C cN'))
               \<in> ktm_step (arm_N N D one)"
    using arm_N_step [OF p step' clock_inv_ctx [OF inv]] acc by simp
  have sub: "arm_N N D one \<subseteq> delta_ktm (clock_product N D one)" by auto
  from ktm_step_mono [OF sub] arm show ?thesis by blast
qed


subsection \<open>Routing a step by its source state\<close>


lemma setup_delta_src:
  assumes "(q, a, q', a', d) \<in> setup_delta N D one"
  shows "q = CWalk \<or> q = CBack"
  using assms by (auto simp: setup_delta_def)

lemma arm_N_src:
  assumes "(q, a, q', a', d) \<in> arm_N N D one"
  obtains r p where "q = CRun r p True"
  using assms by (auto simp: arm_N_def tag_delta_def)

lemma arm_D_src:
  assumes "(q, a, q', a', d) \<in> arm_D N D one"
  obtains r p where "q = CRun r p False"
  using assms by (auto simp: arm_D_def tag_delta_def)

lemma clock_step_cases:
  assumes step: "(C, C') \<in> ktm_step (delta_ktm (clock_product N D one))"
  obtains (Setup) "(C, C') \<in> ktm_step (setup_delta N D one)"
              and "ktc_state C = CWalk \<or> ktc_state C = CBack"
    | (ArmN) r p where "(C, C') \<in> ktm_step (arm_N N D one)"
              and "ktc_state C = CRun r p True"
    | (ArmD) r p where "(C, C') \<in> ktm_step (arm_D N D one)"
              and "ktc_state C = CRun r p False"
proof -
  from step have "(C, C') \<in> ktm_step (setup_delta N D one)
                            \<union> ktm_step (arm_N N D one)
                            \<union> ktm_step (arm_D N D one)"
    by (simp add: ktm_step_Un)
  then consider "(C, C') \<in> ktm_step (setup_delta N D one)"
    | "(C, C') \<in> ktm_step (arm_N N D one)"
    | "(C, C') \<in> ktm_step (arm_D N D one)" by blast
  then show thesis
  proof cases
    case 1
    then obtain a a' d
      where t: "(ktc_state C, a, ktc_state C', a', d) \<in> setup_delta N D one"
      by (rule ktm_step_states)
    from 1 setup_delta_src [OF t] show thesis by (rule Setup)
  next
    case 2
    then obtain a a' d
      where t: "(ktc_state C, a, ktc_state C', a', d) \<in> arm_N N D one"
      by (rule ktm_step_states)
    obtain r p where "ktc_state C = CRun r p True" by (rule arm_N_src [OF t])
    with 2 show thesis by (rule ArmN)
  next
    case 3
    then obtain a a' d
      where t: "(ktc_state C, a, ktc_state C', a', d) \<in> arm_D N D one"
      by (rule ktm_step_states)
    obtain r p where "ktc_state C = CRun r p False" by (rule arm_D_src [OF t])
    with 3 show thesis by (rule ArmD)
  qed
qed

lemma clock_step_setup:
  assumes step: "(C, C') \<in> ktm_step (delta_ktm (clock_product N D one))"
      and q: "ktc_state C = CWalk \<or> ktc_state C = CBack"
  shows "(C, C') \<in> ktm_step (setup_delta N D one)"
proof (rule clock_step_cases [OF step])
  assume "(C, C') \<in> ktm_step (setup_delta N D one)"
  then show ?thesis .
next
  fix r p assume "ktc_state C = CRun r p True"
  with q show ?thesis by simp
next
  fix r p assume "ktc_state C = CRun r p False"
  with q show ?thesis by simp
qed


lemma setup_delta_det:
  assumes "(q, a, q\<^sub>1, a\<^sub>1, d\<^sub>1) \<in> setup_delta N D one"
      and "(q, a, q\<^sub>2, a\<^sub>2, d\<^sub>2) \<in> setup_delta N D one"
  shows "(q\<^sub>1, a\<^sub>1, d\<^sub>1) = (q\<^sub>2, a\<^sub>2, d\<^sub>2)"
  using assms by (auto simp: setup_delta_def)

lemma arm_N_det:
  assumes vN: "valid_ktm N" and detN: "det_ktm N"
      and tr\<^sub>1: "(Q, A, Q\<^sub>1, A\<^sub>1, E\<^sub>1)
                    \<in> arm_N N D one"
      and tr\<^sub>2: "(Q, A, Q\<^sub>2, A\<^sub>2, E\<^sub>2)
                    \<in> arm_N N D one"
  shows "(Q\<^sub>1, A\<^sub>1, E\<^sub>1) = (Q\<^sub>2, A\<^sub>2, E\<^sub>2)"
proof -
  from tr\<^sub>1 obtain p\<^sub>1 where p\<^sub>1: "p\<^sub>1 \<in> Q_ktm D"
    and t\<^sub>1: "(Q, A, Q\<^sub>1, A\<^sub>1, E\<^sub>1)
       \<in> tag_delta (\<lambda>q. CRun q p\<^sub>1 True)
          (\<lambda>q'. if q' = t_ktm N then CAcc
                else if q' = r_ktm N then CRej else CRun q' p\<^sub>1 False)
          (embed_delta 0 (k_ktm N) (clock_tapes N D)
             (clock_Gamma N D one) (bl_ktm N) (delta_ktm N))"
    by (auto simp: arm_N_def)
  from tr\<^sub>2 obtain p\<^sub>2 where p\<^sub>2: "p\<^sub>2 \<in> Q_ktm D"
    and t\<^sub>2: "(Q, A, Q\<^sub>2, A\<^sub>2, E\<^sub>2)
       \<in> tag_delta (\<lambda>q. CRun q p\<^sub>2 True)
          (\<lambda>q'. if q' = t_ktm N then CAcc
                else if q' = r_ktm N then CRej else CRun q' p\<^sub>2 False)
          (embed_delta 0 (k_ktm N) (clock_tapes N D)
             (clock_Gamma N D one) (bl_ktm N) (delta_ktm N))"
    by (auto simp: arm_N_def)
  have peq: "p\<^sub>1 = p\<^sub>2" using t\<^sub>1 t\<^sub>2 by (auto simp: tag_delta_def)
  have det': "\<And>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
      (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> delta_ktm N \<Longrightarrow>
      (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> delta_ktm N \<Longrightarrow>
      (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
    using detN unfolding det_ktm_def by blast
  have sup: "\<And>q a p b d. (q, a, p, b, d) \<in> delta_ktm N \<Longrightarrow>
      (\<And>j. k_ktm N \<le> j \<Longrightarrow> a j = bl_ktm N)"
    using valid_ktm_delta_support [OF vN] by blast
  note t\<^sub>2' = t\<^sub>2 [unfolded peq [symmetric]]
  show ?thesis
  proof (rule tag_delta_det [OF _ _ t\<^sub>1 t\<^sub>2'])
    show "inj (\<lambda>q. CRun q p\<^sub>1 True)" by (auto intro: injI)
  qed (use det' sup in
        \<open>rule embed_delta_det [where D = "delta_ktm N" and k = "k_ktm N" and bl = "bl_ktm N"]\<close>)
qed

lemma arm_D_det:
  assumes vD: "valid_ktm D" and detD: "det_ktm D"
      and blD: "bl_ktm D = bl_ktm N"
      and tr\<^sub>1: "(Q, A, Q\<^sub>1, A\<^sub>1, E\<^sub>1)
                    \<in> arm_D N D one"
      and tr\<^sub>2: "(Q, A, Q\<^sub>2, A\<^sub>2, E\<^sub>2)
                    \<in> arm_D N D one"
  shows "(Q\<^sub>1, A\<^sub>1, E\<^sub>1) = (Q\<^sub>2, A\<^sub>2, E\<^sub>2)"
proof -
  from tr\<^sub>1 obtain p\<^sub>1 where p\<^sub>1: "p\<^sub>1 \<in> Q_ktm N"
    and t\<^sub>1: "(Q, A, Q\<^sub>1, A\<^sub>1, E\<^sub>1)
       \<in> tag_delta (\<lambda>p. CRun p\<^sub>1 p False)
          (\<lambda>p'. if p' = t_ktm D \<or> p' = r_ktm D then CRej
                else CRun p\<^sub>1 p' True)
          (embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
             (clock_Gamma N D one) (bl_ktm N) (delta_ktm D))"
    by (auto simp: arm_D_def)
  from tr\<^sub>2 obtain p\<^sub>2 where p\<^sub>2: "p\<^sub>2 \<in> Q_ktm N"
    and t\<^sub>2: "(Q, A, Q\<^sub>2, A\<^sub>2, E\<^sub>2)
       \<in> tag_delta (\<lambda>p. CRun p\<^sub>2 p False)
          (\<lambda>p'. if p' = t_ktm D \<or> p' = r_ktm D then CRej
                else CRun p\<^sub>2 p' True)
          (embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
             (clock_Gamma N D one) (bl_ktm N) (delta_ktm D))"
    by (auto simp: arm_D_def)
  have peq: "p\<^sub>1 = p\<^sub>2" using t\<^sub>1 t\<^sub>2 by (auto simp: tag_delta_def)
  have det': "\<And>q a p\<^sub>1 b\<^sub>1 d\<^sub>1 p\<^sub>2 b\<^sub>2 d\<^sub>2.
      (q, a, p\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> delta_ktm D \<Longrightarrow>
      (q, a, p\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> delta_ktm D \<Longrightarrow>
      (p\<^sub>1, b\<^sub>1, d\<^sub>1) = (p\<^sub>2, b\<^sub>2, d\<^sub>2)"
    using detD unfolding det_ktm_def by blast
  have sup: "\<And>q a p b d. (q, a, p, b, d) \<in> delta_ktm D \<Longrightarrow>
      (\<And>j. k_ktm D \<le> j \<Longrightarrow> a j = bl_ktm N)"
  proof -
    fix q a p b d
    assume tr: "(q, a, p, b, d) \<in> delta_ktm D"
    show "\<And>j. k_ktm D \<le> j \<Longrightarrow> a j = bl_ktm N"
    proof -
      fix j
      assume j: "k_ktm D \<le> j"
      from valid_ktm_delta_support [OF vD tr j]
        show "a j = bl_ktm N" using blD by simp
    qed
  qed
  note t\<^sub>2' = t\<^sub>2 [unfolded peq [symmetric]]
  show ?thesis
  proof (rule tag_delta_det [OF _ _ t\<^sub>1 t\<^sub>2'])
    show "inj (\<lambda>p. CRun p\<^sub>1 p False)" by (auto intro: injI)
  qed (use det' sup in
        \<open>rule embed_delta_det [where D = "delta_ktm D" and k = "k_ktm D" and bl = "bl_ktm N"]\<close>)
qed

lemma clock_product_det:
  assumes vN: "valid_ktm N" and detN: "det_ktm N"
      and vD: "valid_ktm D" and detD: "det_ktm D"
      and blD: "bl_ktm D = bl_ktm N"
  shows "det_ktm (clock_product N D one)"
proof -
  show ?thesis
    unfolding det_ktm_def
  proof (intro allI impI)
    fix q a q\<^sub>1 b\<^sub>1 d\<^sub>1 q\<^sub>2 b\<^sub>2 d\<^sub>2
    assume t\<^sub>1: "(q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1)
                    \<in> delta_ktm (clock_product N D one)"
       and t\<^sub>2: "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2)
                    \<in> delta_ktm (clock_product N D one)"
    have t\<^sub>1':
        "(q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> setup_delta N D one
       \<or> (q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> arm_N N D one
       \<or> (q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> arm_D N D one"
      using t\<^sub>1 by (simp add: clock_product_simps)
    have t\<^sub>2':
        "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> setup_delta N D one
       \<or> (q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_N N D one
       \<or> (q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_D N D one"
      using t\<^sub>2 by (simp add: clock_product_simps)
    from t\<^sub>1' consider
        (S\<^sub>1) "(q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> setup_delta N D one"
      | (N\<^sub>1) "(q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> arm_N N D one"
      | (D\<^sub>1) "(q, a, q\<^sub>1, b\<^sub>1, d\<^sub>1) \<in> arm_D N D one"
      by blast
    then show "(q\<^sub>1, b\<^sub>1, d\<^sub>1) = (q\<^sub>2, b\<^sub>2, d\<^sub>2)"
    proof cases
      case S\<^sub>1
      from t\<^sub>2' consider
          (S\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> setup_delta N D one"
        | (N\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_N N D one"
        | (D\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_D N D one"
        by blast
      then show ?thesis
      proof cases
        case S\<^sub>2
        show ?thesis
          by (rule setup_delta_det [OF S\<^sub>1 S\<^sub>2])
      next
        case N\<^sub>2
        obtain r p where "q = CRun r p True"
          by (rule arm_N_src [OF N\<^sub>2])
        moreover have "q = CWalk \<or> q = CBack"
          by (rule setup_delta_src [OF S\<^sub>1])
        ultimately show ?thesis by simp
      next
        case D\<^sub>2
        obtain r p where "q = CRun r p False"
          by (rule arm_D_src [OF D\<^sub>2])
        moreover have "q = CWalk \<or> q = CBack"
          by (rule setup_delta_src [OF S\<^sub>1])
        ultimately show ?thesis by simp
      qed
    next
      case N\<^sub>1
      from t\<^sub>2' consider
          (S\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> setup_delta N D one"
        | (N\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_N N D one"
        | (D\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_D N D one"
        by blast
      then show ?thesis
      proof cases
        case S\<^sub>2
        obtain r p where "q = CRun r p True"
          by (rule arm_N_src [OF N\<^sub>1])
        moreover have "q = CWalk \<or> q = CBack"
          by (rule setup_delta_src [OF S\<^sub>2])
        ultimately show ?thesis by simp
      next
        case N\<^sub>2
        show ?thesis
          by (rule arm_N_det [OF vN detN N\<^sub>1 N\<^sub>2])
      next
        case D\<^sub>2
        obtain r p where "q = CRun r p True"
          by (rule arm_N_src [OF N\<^sub>1])
        moreover obtain r' p' where "q = CRun r' p' False"
          by (rule arm_D_src [OF D\<^sub>2])
        ultimately show ?thesis by simp
      qed
    next
      case D\<^sub>1
      from t\<^sub>2' consider
          (S\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> setup_delta N D one"
        | (N\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_N N D one"
        | (D\<^sub>2) "(q, a, q\<^sub>2, b\<^sub>2, d\<^sub>2) \<in> arm_D N D one"
        by blast
      then show ?thesis
      proof cases
        case S\<^sub>2
        obtain r p where "q = CRun r p False"
          by (rule arm_D_src [OF D\<^sub>1])
        moreover have "q = CWalk \<or> q = CBack"
          by (rule setup_delta_src [OF S\<^sub>2])
        ultimately show ?thesis by simp
      next
        case N\<^sub>2
        obtain r p where "q = CRun r p False"
          by (rule arm_D_src [OF D\<^sub>1])
        moreover obtain r' p' where "q = CRun r' p' True"
          by (rule arm_N_src [OF N\<^sub>2])
        ultimately show ?thesis by simp
      next
        case D\<^sub>2
        show ?thesis
          by (rule arm_D_det [OF vD detD blD D\<^sub>1 D\<^sub>2])
      qed
    qed
  qed
qed

lemma clock_setup_det:
  assumes q: "ktc_state C = CWalk \<or> ktc_state C = CBack"
      and s\<^sub>1: "(C, C\<^sub>1) \<in> ktm_step (delta_ktm (clock_product N D one))"
      and s\<^sub>2: "(C, C\<^sub>2) \<in> ktm_step (delta_ktm (clock_product N D one))"
  shows "C\<^sub>1 = C\<^sub>2"
  by (rule ktm_step_functional
        [OF _ clock_step_setup [OF s\<^sub>1 q] clock_step_setup [OF s\<^sub>2 q]])
     (use setup_delta_det in blast)



lemma arm_N_tgt:
  assumes "(q, a, q', a', d) \<in> arm_N N D one"
  shows "q' \<noteq> CWalk \<and> q' \<noteq> CBack"
  using assms by (auto simp: arm_N_def tag_delta_def split: if_splits)

lemma arm_D_tgt:
  assumes "(q, a, q', a', d) \<in> arm_D N D one"
  shows "q' \<noteq> CWalk \<and> q' \<noteq> CBack"
  using assms by (auto simp: arm_D_def tag_delta_def split: if_splits)


lemma arm_D_acc:
  assumes "(q, a, q', a', d) \<in> arm_D N D one"
  shows "q' \<noteq> CAcc"
  using assms by (auto simp: arm_D_def tag_delta_def split: if_splits)

lemma arm_N_turn:
  "\<forall>q a q' a' d. (q, a, q', a', d) \<in> arm_N N D one
      \<longrightarrow> cturn q \<and> \<not> (q = CAcc \<or> q = CRej)
          \<and> (cturn q' \<longrightarrow> q' = CAcc \<or> q' = CRej)"
  by (auto simp: arm_N_def tag_delta_def split: if_splits)

lemma arm_D_turn:
  "\<forall>q a q' a' d. (q, a, q', a', d) \<in> arm_D N D one
      \<longrightarrow> \<not> cturn q \<and> \<not> (q = CAcc \<or> q = CRej)
          \<and> (\<not> cturn q' \<longrightarrow> q' = CAcc \<or> q' = CRej)"
  by (auto simp: arm_D_def tag_delta_def split: if_splits)


lemma clock_arm_run:
  assumes run: "(C, C') \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ K"
      and qW: "ktc_state C \<noteq> CWalk" and qB: "ktc_state C \<noteq> CBack"
  shows "(C, C') \<in> (ktm_step (arm_N N D one \<union> arm_D N D one)) ^^ K"
  using run qW qB
proof (induction K arbitrary: C)
  case 0
  then show ?case by simp
next
  case (Suc K)
  from Suc.prems(1) obtain y
    where step: "(C, y) \<in> ktm_step (delta_ktm (clock_product N D one))"
      and rest: "(y, C') \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ K"
    by (blast dest: relpow_Suc_D2)
  from step have arm: "(C, y) \<in> ktm_step (arm_N N D one \<union> arm_D N D one)"
  proof (rule clock_step_cases)
    assume "ktc_state C = CWalk \<or> ktc_state C = CBack"
    with Suc.prems(2,3) show ?thesis by simp
  next
    fix r p assume "(C, y) \<in> ktm_step (arm_N N D one)"
    then show ?thesis by (simp add: ktm_step_Un)
  next
    fix r p assume "(C, y) \<in> ktm_step (arm_D N D one)"
    then show ?thesis by (simp add: ktm_step_Un)
  qed
  from arm obtain a a' d
    where t: "(ktc_state C, a, ktc_state y, a', d)
                \<in> arm_N N D one \<union> arm_D N D one"
    by (rule ktm_step_states)
  from t have yW: "ktc_state y \<noteq> CWalk" and yB: "ktc_state y \<noteq> CBack"
    using arm_N_tgt arm_D_tgt by blast+
  from arm Suc.IH [OF rest yW yB] show ?case by (rule relpow_Suc_I2)
qed


lemma clock_alternates:
  assumes run: "(C, C') \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ K"
      and qW: "ktc_state C \<noteq> CWalk" and qB: "ktc_state C \<noteq> CBack"
      and turn: "cturn (ktc_state C)"
  obtains f where "f 0 = C" and "f K = C'"
    and "\<And>i. i \<le> K \<Longrightarrow> ktc_state (f i) \<noteq> CAcc \<Longrightarrow> ktc_state (f i) \<noteq> CRej
               \<Longrightarrow> cturn (ktc_state (f i)) = even i"
    and "\<And>i. i < K \<Longrightarrow> even i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_N N D one)"
    and "\<And>i. i < K \<Longrightarrow> odd i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_D N D one)"
proof (rule arms_alternate
         [where final = "\<lambda>q. q = CAcc \<or> q = CRej",
          OF arm_N_turn arm_D_turn clock_arm_run [OF run qW qB] turn])
  fix f
  assume f0: "f 0 = C" and fK: "f K = C'"
    and par: "\<And>i. i \<le> K \<Longrightarrow> \<not> (ktc_state (f i) = CAcc \<or> ktc_state (f i) = CRej)
               \<Longrightarrow> cturn (ktc_state (f i)) = even i"
    and aN: "\<And>i. i < K \<Longrightarrow> even i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_N N D one)"
    and aD: "\<And>i. i < K \<Longrightarrow> odd i \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_D N D one)"
  have par': "\<And>i. i \<le> K \<Longrightarrow> ktc_state (f i) \<noteq> CAcc \<Longrightarrow> ktc_state (f i) \<noteq> CRej
                \<Longrightarrow> cturn (ktc_state (f i)) = even i"
    using par by blast
  show thesis by (rule that [OF f0 fK par' aN aD])
qed


lemma clock_alternates_reach:
  assumes armN: "\<And>i. i < K \<Longrightarrow> even i
                   \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_N N D one)"
      and armD: "\<And>i. i < K \<Longrightarrow> odd i
                   \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_D N D one)"
      and i: "i \<le> K"
  shows "(f 0, f i) \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ i"
  using i
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  from Suc.prems have ilt: "i < K" and ile: "i \<le> K" by simp_all
  have "(f i, f (Suc i)) \<in> ktm_step (arm_N N D one \<union> arm_D N D one)"
    using armN [OF ilt] armD [OF ilt] by (cases "even i") (simp_all add: ktm_step_Un)
  then have "(f i, f (Suc i)) \<in> ktm_step (delta_ktm (clock_product N D one))"
    by (simp add: ktm_step_Un)
  with Suc.IH [OF ile] show ?case by (rule relpow_Suc_I)
qed




subsection \<open>A product step of one factor is a step of that factor\<close>


lemma clock_inv_from_tapes:
  assumes pN: "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C) = cN"
      and pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                 (ktc_set_state (ktc_state cD) C) = cD"
      and tapes: "ktc_tapes_fit (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D) C"
  shows "clock_inv N D one C cN cD"
  unfolding clock_inv_def using pN pD tapes by (simp add: ktc_tapes_fit_def)

lemma arm_N_rev:
  assumes vN: "valid_ktm N"
      and inv: "clock_inv N D one C cN cD"
      and step: "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C, C\<^sub>2)
                   \<in> ktm_step (arm_N N D one)"
  obtains cN'
  where "(cN, cN') \<in> ktm_step (delta_ktm N)"
    and "ktc_state C\<^sub>2 = (if ktc_state cN' = t_ktm N then CAcc
                        else if ktc_state cN' = r_ktm N then CRej
                        else CRun (ktc_state cN') (ktc_state cD) False)"
    and "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN') C\<^sub>2) = cN'"
    and "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
           (ktc_set_state (ktc_state cD) C\<^sub>2) = cD"
proof -
  let ?C\<^sub>1 = "ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) C"
  let ?E = "embed_delta 0 (k_ktm N) (clock_tapes N D)
              (clock_Gamma N D one) (bl_ktm N) (delta_ktm N)"
  from step obtain p where p: "p \<in> Q_ktm D"
    and stepp: "(?C\<^sub>1, C\<^sub>2) \<in> ktm_step
                   (tag_delta (\<lambda>q. CRun q p True)
                      (\<lambda>q'. if q' = t_ktm N then CAcc else if q' = r_ktm N then CRej else CRun q' p False) ?E)"
    unfolding arm_N_def ktm_step_UN by blast
  from tag_step_rev [OF stepp] obtain q q'
    where s\<^sub>1: "ktc_state ?C\<^sub>1 = CRun q p True"
      and s\<^sub>2: "ktc_state C\<^sub>2 = (if q' = t_ktm N then CAcc else if q' = r_ktm N then CRej else CRun q' p False)"
      and emb: "(ktc_set_state q ?C\<^sub>1, ktc_set_state q' C\<^sub>2) \<in> ktm_step ?E"
    by blast
  from s\<^sub>1 have q: "q = ktc_state cN" and pd: "p = ktc_state cD" by simp_all

  have supp: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> delta_ktm N
                 \<longrightarrow> (\<forall>j \<ge> k_ktm N. a j = bl_ktm N \<and> a' j = bl_ktm N
                                     \<and> d j = MoveN)"
    using valid_ktm_delta_support [OF vN] by blast
  from embed_step_rev [OF emb supp]
  have proj: "(proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q ?C\<^sub>1),
               proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q' C\<^sub>2))
                \<in> ktm_step (delta_ktm N)" .
  from inv have pN: "proj_config 0 (k_ktm N) (bl_ktm N)
                       (ktc_set_state (ktc_state cN) C) = cN"
    and pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
               (ktc_set_state (ktc_state cD) C) = cD"
    by (simp_all add: clock_inv_def)
  have src: "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q ?C\<^sub>1) = cN"
    using pN q by simp

  have outT: "ktc_tape C\<^sub>2 j = ktc_tape C j" if "k_ktm N \<le> j" for j
    using embed_step_outside [OF emb, of j] that by (simp add: ktc_set_state_def)
  have outP: "ktc_pos C\<^sub>2 j = ktc_pos C j" if "k_ktm N \<le> j" for j
    using embed_step_outside [OF emb, of j] that by (simp add: ktc_set_state_def)
  have frozen: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                  (ktc_set_state (ktc_state cD) C\<^sub>2)
                  = proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                      (ktc_set_state (ktc_state cD) C)"
    by (rule ktc_config.expand, intro conjI)
       (simp_all add: proj_config_def ktc_set_state_def fun_eq_iff outT outP)

  show thesis
  proof (rule that)
    show "(cN, proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q' C\<^sub>2))
            \<in> ktm_step (delta_ktm N)" using proj src by simp
    show "ktc_state C\<^sub>2
            = (if ktc_state (proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q' C\<^sub>2))
                    = t_ktm N
               then CAcc
               else if ktc_state (proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q' C\<^sub>2))
                    = r_ktm N
               then CRej
               else CRun (ktc_state (proj_config 0 (k_ktm N) (bl_ktm N)
                                      (ktc_set_state q' C\<^sub>2))) (ktc_state cD) False)"
      using s\<^sub>2 pd by (simp add: proj_config_state)
    show "proj_config 0 (k_ktm N) (bl_ktm N)
            (ktc_set_state (ktc_state (proj_config 0 (k_ktm N) (bl_ktm N)
                                  (ktc_set_state q' C\<^sub>2))) C\<^sub>2)
            = proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state q' C\<^sub>2)"
      by (simp add: proj_config_state)
    show "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
            (ktc_set_state (ktc_state cD) C\<^sub>2) = cD" using frozen pD by simp
  qed
qed



lemma arm_D_rev:
  assumes vD: "valid_ktm D" and blD: "bl_ktm D = bl_ktm N"
      and inv: "clock_inv N D one C cN cD"
      and step: "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) False) C, C\<^sub>2)
                   \<in> ktm_step (arm_D N D one)"
  obtains cD'
  where "(cD, cD') \<in> ktm_step (delta_ktm D)"
    and "ktc_state C\<^sub>2 = (if ktc_state cD' = t_ktm D \<or> ktc_state cD' = r_ktm D
                        then CRej
                        else CRun (ktc_state cN) (ktc_state cD') True)"
    and "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
           (ktc_set_state (ktc_state cD') C\<^sub>2) = cD'"
    and "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C\<^sub>2) = cN"
proof -
  let ?C\<^sub>1 = "ktc_set_state (CRun (ktc_state cN) (ktc_state cD) False) C"
  let ?E = "embed_delta (k_ktm N) (k_ktm D) (clock_tapes N D)
              (clock_Gamma N D one) (bl_ktm N) (delta_ktm D)"
  from step obtain r where r: "r \<in> Q_ktm N"
    and stepr: "(?C\<^sub>1, C\<^sub>2) \<in> ktm_step
                   (tag_delta (\<lambda>p. CRun r p False)
                      (\<lambda>p'. if p' = t_ktm D \<or> p' = r_ktm D then CRej
                            else CRun r p' True) ?E)"
    unfolding arm_D_def ktm_step_UN by blast
  from tag_step_rev [OF stepr] obtain p p'
    where s\<^sub>1: "ktc_state ?C\<^sub>1 = CRun r p False"
      and s\<^sub>2: "ktc_state C\<^sub>2 = (if p' = t_ktm D \<or> p' = r_ktm D then CRej
                             else CRun r p' True)"
      and emb: "(ktc_set_state p ?C\<^sub>1, ktc_set_state p' C\<^sub>2) \<in> ktm_step ?E"
    by blast
  from s\<^sub>1 have rn: "r = ktc_state cN" and p: "p = ktc_state cD" by simp_all

  have supp: "\<forall>q a q' a' d. (q, a, q', a', d) \<in> delta_ktm D
                 \<longrightarrow> (\<forall>j \<ge> k_ktm D. a j = bl_ktm N \<and> a' j = bl_ktm N
                                     \<and> d j = MoveN)"
  proof (intro allI impI)
    fix q a q' a' d j
    assume "(q, a, q', a', d) \<in> delta_ktm D" and "k_ktm D \<le> j"
    from valid_ktm_delta_support [OF vD this(1) this(2)]
    show "a j = bl_ktm N \<and> a' j = bl_ktm N \<and> d j = MoveN" by (simp add: blD)
  qed
  from embed_step_rev [OF emb supp]
  have proj: "(proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state p ?C\<^sub>1),
               proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state p' C\<^sub>2))
                \<in> ktm_step (delta_ktm D)" .
  from inv have pN: "proj_config 0 (k_ktm N) (bl_ktm N)
                       (ktc_set_state (ktc_state cN) C) = cN"
    and pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
               (ktc_set_state (ktc_state cD) C) = cD"
    by (simp_all add: clock_inv_def)
  have src: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state p ?C\<^sub>1) = cD"
    using pD p by simp

  have outT: "ktc_tape C\<^sub>2 j = ktc_tape C j" if "j < k_ktm N" for j
    using embed_step_outside [OF emb, of j] that by (simp add: ktc_set_state_def)
  have outP: "ktc_pos C\<^sub>2 j = ktc_pos C j" if "j < k_ktm N" for j
    using embed_step_outside [OF emb, of j] that by (simp add: ktc_set_state_def)
  have frozen: "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C\<^sub>2)
                  = proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C)"
    by (rule ktc_config.expand, intro conjI)
       (simp_all add: proj_config_def ktc_set_state_def fun_eq_iff outT outP)

  show thesis
  proof (rule that)
    show "(cD, proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state p' C\<^sub>2))
            \<in> ktm_step (delta_ktm D)" using proj src by simp
    show "ktc_state C\<^sub>2
            = (if ktc_state (proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                              (ktc_set_state p' C\<^sub>2)) = t_ktm D
                  \<or> ktc_state (proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                                 (ktc_set_state p' C\<^sub>2)) = r_ktm D
               then CRej
               else CRun (ktc_state cN)
                         (ktc_state (proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                                      (ktc_set_state p' C\<^sub>2))) True)"
      using s\<^sub>2 rn by (simp add: proj_config_state)
    show "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
            (ktc_set_state (ktc_state (proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                                  (ktc_set_state p' C\<^sub>2))) C\<^sub>2)
            = proj_config (k_ktm N) (k_ktm D) (bl_ktm N) (ktc_set_state p' C\<^sub>2)"
      by (simp add: proj_config_state)
    show "proj_config 0 (k_ktm N) (bl_ktm N) (ktc_set_state (ktc_state cN) C\<^sub>2) = cN"
      using frozen pN by simp
  qed
qed


subsection \<open>The setup phase is forced\<close>


lemma setup_config_state:
  assumes "i < 2 * length w + 3"
  shows "ktc_state (setup_config N D one w i) = CWalk
       \<or> ktc_state (setup_config N D one w i) = CBack"
  using assms by (auto simp: setup_config_def)

lemma setup_forced:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and run: "(init_config_ktm (clock_product N D one) w, z)
                  \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ i"
      and i: "i \<le> 2 * length w + 3"
  shows "z = setup_config N D one w i"
  using run i
proof (induction i arbitrary: z)
  case 0
  then show ?case by (simp add: setup_config_0)
next
  case (Suc i)
  from Suc.prems(1) obtain y
    where run: "(init_config_ktm (clock_product N D one) w, y)
                  \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ i"
      and step: "(y, z) \<in> ktm_step (delta_ktm (clock_product N D one))" by auto
  from Suc.prems(2) have ilt: "i < 2 * length w + 3" by simp
  from Suc.IH [OF run less_imp_le [OF ilt]] have y: "y = setup_config N D one w i" .
  have fwd: "(setup_config N D one w i, setup_config N D one w (Suc i))
               \<in> ktm_step (delta_ktm (clock_product N D one))"
    by (rule setup_config_step [OF vN vD blle w ilt])
  show ?case
    using clock_setup_det [OF setup_config_state [OF ilt] fwd step [unfolded y]]
    by simp
qed


lemma setup_forced_ge:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and run: "(init_config_ktm (clock_product N D one) w, z)
                  \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ M"
      and M: "2 * length w + 3 \<le> M"
  shows "(KConfig (clock_start_state N D)
                  (setup_tape N D one w 0) (setup_pos (k_ktm N) 0), z)
           \<in> (ktm_step (delta_ktm (clock_product N D one)))
                ^^ (M - (2 * length w + 3))"
proof -
  let ?R = "ktm_step (delta_ktm (clock_product N D one))"
  let ?m = "2 * length w + 3"
  from M have "M = ?m + (M - ?m)" by simp
  with run have "(init_config_ktm (clock_product N D one) w, z)
                   \<in> ?R ^^ ?m O ?R ^^ (M - ?m)"
    by (metis relpow_add)
  then obtain y
    where ay: "(init_config_ktm (clock_product N D one) w, y) \<in> ?R ^^ ?m"
      and yz: "(y, z) \<in> ?R ^^ (M - ?m)" by auto
  from setup_forced [OF vN vD blle w ay le_refl]
  have "y = setup_config N D one w ?m" .
  with yz show ?thesis by (simp add: setup_config_end)
qed

lemma clock_terminal_run:
  assumes terminal: "ktc_state C \<in> {CAcc, CRej}"
      and run: "(C, C') \<in>
        (ktm_step (delta_ktm (clock_product N D one))) ^^ m"
  shows "m = 0 \<and> C' = C"
proof -
  have sink: "(C, E) \<notin> ktm_step (delta_ktm (clock_product N D one))" for E
  proof
    assume step: "(C, E) \<in> ktm_step (delta_ktm (clock_product N D one))"
    show False
      by (rule clock_step_cases [OF step]) (use terminal in auto)
  qed
  have zero: "m = 0"
  proof (cases m)
    case 0
    then show ?thesis .
  next
    case (Suc n)
    from run [unfolded Suc] obtain E
      where "(C, E) \<in> ktm_step (delta_ktm (clock_product N D one))"
      by (blast dest: relpow_Suc_D2)
    with sink show ?thesis by blast
  qed
  with run show ?thesis by simp
qed

lemma clock_setup_terminal_run:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and run: "(init_config_ktm (clock_product N D one) w, z)
        \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ M"
      and M: "2 * length w + 3 \<le> M"
      and terminal: "clock_start_state N D \<in> {CAcc, CRej}"
  shows "M = 2 * length w + 3 \<and> ktc_state z = clock_start_state N D"
proof -
  have tail: "(KConfig (clock_start_state N D)
      (setup_tape N D one w 0) (setup_pos (k_ktm N) 0), z)
      \<in> (ktm_step (delta_ktm (clock_product N D one)))
        ^^ (M - (2 * length w + 3))"
    by (rule setup_forced_ge [OF vN vD blle w run M])
  have terminal': "ktc_state (KConfig (clock_start_state N D)
      (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)) \<in> {CAcc, CRej}"
    using terminal by simp
  from clock_terminal_run [OF terminal' tail] M show ?thesis by auto
qed

lemma setup_forced_length:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and w: "set w \<subseteq> Sigma_ktm N"
      and run: "(init_config_ktm (clock_product N D one) w, z)
                  \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ M"
      and acc: "ktc_state z = CAcc"
  shows "2 * length w + 3 \<le> M"
proof (rule ccontr)
  assume "\<not> 2 * length w + 3 \<le> M"
  then have M: "M < 2 * length w + 3" by simp
  from setup_forced [OF vN vD blle w run less_imp_le [OF M]]
  have "z = setup_config N D one w M" .
  with setup_config_state [where N = N and D = D and one = one, OF M] acc
  show False by simp
qed


subsection \<open>The forward run\<close>


lemma clock_accepts:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and st: "s_ktm N \<noteq> t_ktm N"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and blD: "bl_ktm D = bl_ktm N" and leD: "le_ktm D = le_ktm N"
      and oneD: "one \<in> Sigma_ktm D"
      and gn: "length w \<le> g (length w)"
      and alarm: "\<exists>cfg. (init_config_ktm D (replicate (length w) one), cfg)
                           \<in> (ktm_step (delta_ktm D)) ^^ (g (length w))"
      and w: "set w \<subseteq> Sigma_ktm N"
      and acc: "accepts_in_time_ktm N w (g (length w))"
    shows "accepts_in_time_ktm (clock_product N D one) w (4 * g (length w) + 2)"
proof -
  let ?n = "length w"
  let ?R = "ktm_step (delta_ktm (clock_product N D one))"
  let ?cN\<^sub>0 = "init_config_ktm N w"
  let ?cD\<^sub>0 = "init_config_ktm D (replicate ?n one)"
  let ?C\<^sub>0 = "KConfig (undefined :: nat)
                      (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"

  from acc obtain m cN where mle: "m \<le> g ?n"
    and runN: "(?cN\<^sub>0, cN) \<in> (ktm_step (delta_ktm N)) ^^ m"
    and accN: "ktc_state cN = t_ktm N"
    unfolding accepts_in_time_ktm_def by blast

  have "m \<noteq> 0"
  proof
    assume "m = 0"
    with runN accN st show False by auto
  qed
  then obtain m' where m: "m = Suc m'" by (cases m) auto
  from runN [unfolded m] obtain cN'
    where runN': "(?cN\<^sub>0, cN') \<in> (ktm_step (delta_ktm N)) ^^ m'"
      and stepN: "(cN', cN) \<in> ktm_step (delta_ktm N)" by auto
  from stepN have aliveN: "ktc_state cN' \<notin> {t_ktm N, r_ktm N}"
    using halt_state_sink [OF vN] by blast
  then have naccN: "ktc_state cN' \<noteq> t_ktm N" and nrejN: "ktc_state cN' \<noteq> r_ktm N"
    by simp_all

  from mle m have m'lt: "m' < g ?n" by simp
  from alarm obtain cfg
    where alarmD: "(?cD\<^sub>0, cfg) \<in> (ktm_step (delta_ktm D)) ^^ (g ?n)" ..
  have mpos: "0 < m" by (simp add: m)
  have gpos: "0 < g ?n" using mle m by simp
  have home: "clock_start_state N D = CRun (s_ktm N) (s_ktm D) True"
    using alarm_start_alive [OF vN runN mpos]
      alarm_start_alive [OF vD alarmD gpos]
    by (simp add: clock_start_state_def)
  from ktm_relpow_not_halted [OF vD alarmD m'lt] obtain cD'
    where runD': "(?cD\<^sub>0, cD') \<in> (ktm_step (delta_ktm D)) ^^ m'"
      and aliveD: "ktc_state cD' \<notin> {t_ktm D, r_ktm D}" by blast
  from aliveD have nhaltD: "ktc_state cD' \<noteq> t_ktm D" "ktc_state cD' \<noteq> r_ktm D"
    by simp_all

  have vcN\<^sub>0: "valid_config_ktm N ?cN\<^sub>0" by (rule valid_init_config_ktm [OF vN w])
  have wD: "set (replicate ?n one) \<subseteq> Sigma_ktm D"
    using oneD by (auto simp: in_set_replicate)
  have vcD\<^sub>0: "valid_config_ktm D ?cD\<^sub>0" by (rule valid_init_config_ktm [OF vD wD])
  have inv\<^sub>0: "clock_inv N D one ?C\<^sub>0 ?cN\<^sub>0 ?cD\<^sub>0"
    by (rule clock_setup_inv [OF vN vD blD leD w])

  have setup_phase: "(init_config_ktm (clock_product N D one) w,
                      ktc_set_state (CRun (ktc_state ?cN\<^sub>0) (ktc_state ?cD\<^sub>0) True) ?C\<^sub>0)
                       \<in> ?R ^^ (2 * ?n + 3)"
    using setup_run [OF vN vD blle w] by (simp add: home ktc_set_state_def)

  from clock_run [OF vN vD blD vcN\<^sub>0 vcD\<^sub>0 heads_parked_init heads_parked_init inv\<^sub>0
                     runN' runD' naccN nrejN nhaltD(1) nhaltD(2)]
  obtain C
    where ticks: "(ktc_set_state (CRun (ktc_state ?cN\<^sub>0) (ktc_state ?cD\<^sub>0) True) ?C\<^sub>0,
                   ktc_set_state (CRun (ktc_state cN') (ktc_state cD') True) C)
                    \<in> ?R ^^ (2 * m')"
      and inv: "clock_inv N D one C cN' cD'" by blast

  from setup_phase ticks
  have prefix: "(init_config_ktm (clock_product N D one) w,
                 ktc_set_state (CRun (ktc_state cN') (ktc_state cD') True) C)
                  \<in> ?R ^^ ((2 * ?n + 3) + 2 * m')"
    unfolding relpow_add by (rule relcompI)

  have qD: "ktc_state cD' \<in> Q_ktm D"
    by (rule valid_config_state [OF valid_reach_relpow_ktm [OF vD vcD\<^sub>0 runD']])
  from prefix clock_accept_step [OF qD inv stepN accN]
  have whole: "(init_config_ktm (clock_product N D one) w,
                ktc_set_state CAcc (embed_update 0 (k_ktm N) C cN))
                 \<in> ?R ^^ Suc ((2 * ?n + 3) + 2 * m')"
    by (rule relpow_Suc_I)

  have bound: "Suc ((2 * ?n + 3) + 2 * m') \<le> 4 * g ?n + 2"
    using gn mle m by simp
  have accC: "ktc_state (ktc_set_state CAcc (embed_update 0 (k_ktm N) C cN))
                = t_ktm (clock_product N D one)"
    by (simp add: ktc_set_state_def)
  show ?thesis
    unfolding accepts_in_time_ktm_def using bound whole accC by blast
qed


subsection \<open>The reverse run\<close>


lemma clock_run_rev:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D"
      and blD: "bl_ktm D = bl_ktm N"
      and inv\<^sub>0: "clock_inv N D one C\<^sub>0 cN\<^sub>0 cD\<^sub>0"
      and aliveD\<^sub>0: "ktc_state cD\<^sub>0 \<noteq> t_ktm D" "ktc_state cD\<^sub>0 \<noteq> r_ktm D"
      and f0: "f 0 = ktc_set_state (CRun (ktc_state cN\<^sub>0) (ktc_state cD\<^sub>0) True) C\<^sub>0"
      and armN: "\<And>i. i < K \<Longrightarrow> even i
                   \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_N N D one)"
      and armD: "\<And>i. i < K \<Longrightarrow> odd i
                   \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_D N D one)"
      and tapes: "\<And>i. i \<le> K \<Longrightarrow>
                    ktc_tapes_fit (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D) (f i)"
      and j: "2 * j < K"
  shows "\<exists>cN cD. (cN\<^sub>0, cN) \<in> (ktm_step (delta_ktm N)) ^^ j
               \<and> (cD\<^sub>0, cD) \<in> (ktm_step (delta_ktm D)) ^^ j
               \<and> ktc_state cD \<noteq> t_ktm D \<and> ktc_state cD \<noteq> r_ktm D
               \<and> ktc_state (f (2 * j)) = CRun (ktc_state cN) (ktc_state cD) True
               \<and> clock_inv N D one (ktc_set_state (0::nat) (f (2 * j))) cN cD"
  using j
proof (induction j)
  case 0
  have "(cN\<^sub>0, cN\<^sub>0) \<in> (ktm_step (delta_ktm N)) ^^ 0"
   and "(cD\<^sub>0, cD\<^sub>0) \<in> (ktm_step (delta_ktm D)) ^^ 0" by simp_all
  moreover have "ktc_state (f (2 * 0)) = CRun (ktc_state cN\<^sub>0) (ktc_state cD\<^sub>0) True"
    by (simp add: f0)
  moreover have "clock_inv N D one (ktc_set_state (0::nat) (f (2 * 0))) cN\<^sub>0 cD\<^sub>0"
    using inv\<^sub>0 by (simp add: f0)
  ultimately show ?case using aliveD\<^sub>0 by blast
next
  case (Suc j)
  have idx: "2 * Suc j = Suc (Suc (2 * j))" by simp
  from Suc.prems [unfolded idx] have lt3: "Suc (Suc (2 * j)) < K" .
  note lt2 = Suc_lessD [OF lt3]
  note lt1 = Suc_lessD [OF lt2]
  from Suc.IH [OF lt1] obtain cN cD
    where runN: "(cN\<^sub>0, cN) \<in> (ktm_step (delta_ktm N)) ^^ j"
      and runD: "(cD\<^sub>0, cD) \<in> (ktm_step (delta_ktm D)) ^^ j"
      and stf: "ktc_state (f (2 * j)) = CRun (ktc_state cN) (ktc_state cD) True"
      and inv: "clock_inv N D one (ktc_set_state (0::nat) (f (2 * j))) cN cD"
    by blast
  have ev1: "even (2 * j)" and od2: "odd (Suc (2 * j))"
   and ev3: "even (Suc (Suc (2 * j)))" by simp_all
  note sN = armN [OF lt1 ev1] and sD = armD [OF lt2 od2]
   and sN2 = armN [OF lt3 ev3]

  have srcN: "ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) (f (2 * j)) = f (2 * j)"
    unfolding stf [symmetric] by simp
  have sN': "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True)
                      (ktc_set_state (0::nat) (f (2 * j))), f (Suc (2 * j)))
               \<in> ktm_step (arm_N N D one)"
    using sN by (simp add: srcN)
  from arm_N_rev [OF vN inv sN'] obtain cN'
    where stepN: "(cN, cN') \<in> ktm_step (delta_ktm N)"
      and tgtN: "ktc_state (f (Suc (2 * j)))
                   = (if ktc_state cN' = t_ktm N then CAcc
                      else if ktc_state cN' = r_ktm N then CRej
                      else CRun (ktc_state cN') (ktc_state cD) False)"
      and pN: "proj_config 0 (k_ktm N) (bl_ktm N)
                 (ktc_set_state (ktc_state cN') (f (Suc (2 * j)))) = cN'"
      and pD: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                 (ktc_set_state (ktc_state cD) (f (Suc (2 * j)))) = cD"
    by blast

  from sD obtain a a' d
    where tD: "(ktc_state (f (Suc (2 * j))), a,
                ktc_state (f (Suc (Suc (2 * j)))), a', d) \<in> arm_D N D one"
    by (rule ktm_step_states)
  from tD obtain r p where srcD: "ktc_state (f (Suc (2 * j))) = CRun r p False"
    by (rule arm_D_src)
  from srcD tgtN have nacc: "ktc_state cN' \<noteq> t_ktm N" "ktc_state cN' \<noteq> r_ktm N"
    by (auto split: if_splits)
  with tgtN have tgtN': "ktc_state (f (Suc (2 * j)))
                           = CRun (ktc_state cN') (ktc_state cD) False" by simp

  have inv1: "clock_inv N D one (ktc_set_state (0::nat) (f (Suc (2 * j)))) cN' cD"
  proof (rule clock_inv_from_tapes)
    show "proj_config 0 (k_ktm N) (bl_ktm N)
            (ktc_set_state (ktc_state cN') (ktc_set_state (0::nat) (f (Suc (2 * j))))) = cN'"
      using pN by simp
    show "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
            (ktc_set_state (ktc_state cD) (ktc_set_state (0::nat) (f (Suc (2 * j))))) = cD"
      using pD by simp
    show "ktc_tapes_fit (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D)
            (ktc_set_state (0::nat) (f (Suc (2 * j))))"
      using tapes [OF less_imp_le [OF lt2]] by simp
  qed

  have srcD': "ktc_set_state (CRun (ktc_state cN') (ktc_state cD) False) (f (Suc (2 * j)))
                 = f (Suc (2 * j))"
    unfolding tgtN' [symmetric] by simp
  have sD': "(ktc_set_state (CRun (ktc_state cN') (ktc_state cD) False)
                      (ktc_set_state (0::nat) (f (Suc (2 * j)))), f (Suc (Suc (2 * j))))
               \<in> ktm_step (arm_D N D one)"
    using sD by (simp add: srcD')
  from arm_D_rev [OF vD blD inv1 sD'] obtain cD'
    where stepD: "(cD, cD') \<in> ktm_step (delta_ktm D)"
      and tgtD: "ktc_state (f (Suc (Suc (2 * j))))
                   = (if ktc_state cD' = t_ktm D \<or> ktc_state cD' = r_ktm D then CRej
                      else CRun (ktc_state cN') (ktc_state cD') True)"
      and pD2: "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
                  (ktc_set_state (ktc_state cD') (f (Suc (Suc (2 * j))))) = cD'"
      and pN2: "proj_config 0 (k_ktm N) (bl_ktm N)
                  (ktc_set_state (ktc_state cN') (f (Suc (Suc (2 * j))))) = cN'"
    by blast

  from sN2 obtain a\<^sub>2 a\<^sub>2' d\<^sub>2
    where t2: "(ktc_state (f (Suc (Suc (2 * j)))), a\<^sub>2,
                ktc_state (f (Suc (Suc (Suc (2 * j))))), a\<^sub>2', d\<^sub>2) \<in> arm_N N D one"
    by (rule ktm_step_states)
  from t2 obtain r\<^sub>2 p\<^sub>2
    where srcN2: "ktc_state (f (Suc (Suc (2 * j)))) = CRun r\<^sub>2 p\<^sub>2 True"
    by (rule arm_N_src)
  from srcN2 tgtD have aliveD': "ktc_state cD' \<noteq> t_ktm D" "ktc_state cD' \<noteq> r_ktm D"
    by (auto split: if_splits)
  with tgtD have tgtD': "ktc_state (f (Suc (Suc (2 * j))))
                           = CRun (ktc_state cN') (ktc_state cD') True" by simp

  have inv2: "clock_inv N D one (ktc_set_state (0::nat) (f (Suc (Suc (2 * j))))) cN' cD'"
  proof (rule clock_inv_from_tapes)
    show "proj_config 0 (k_ktm N) (bl_ktm N)
            (ktc_set_state (ktc_state cN') (ktc_set_state (0::nat) (f (Suc (Suc (2 * j)))))) = cN'"
      using pN2 by simp
    show "proj_config (k_ktm N) (k_ktm D) (bl_ktm N)
            (ktc_set_state (ktc_state cD') (ktc_set_state (0::nat) (f (Suc (Suc (2 * j)))))) = cD'"
      using pD2 by simp
    show "ktc_tapes_fit (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D)
            (ktc_set_state (0::nat) (f (Suc (Suc (2 * j)))))"
      using tapes [OF less_imp_le [OF lt3]] by simp
  qed

  have rN: "(cN\<^sub>0, cN') \<in> (ktm_step (delta_ktm N)) ^^ Suc j"
    using runN stepN by (rule relpow_Suc_I)
  have rD: "(cD\<^sub>0, cD') \<in> (ktm_step (delta_ktm D)) ^^ Suc j"
    using runD stepD by (rule relpow_Suc_I)
  show ?case using rN rD aliveD' tgtD' inv2 unfolding idx by blast
qed


lemma clock_accepts_rev:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D" and det: "det_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and blD: "bl_ktm D = bl_ktm N" and leD: "le_ktm D = le_ktm N"
      and startD: "s_ktm D \<noteq> t_ktm D" "s_ktm D \<noteq> r_ktm D"
      and alarm: "(init_config_ktm D (replicate (length w) one), cfg)
                     \<in> (ktm_step (delta_ktm D)) ^^ (g (length w))"
      and halt: "ktc_state cfg = t_ktm D"
      and w: "set w \<subseteq> Sigma_ktm N"
      and run: "(init_config_ktm (clock_product N D one) w, z)
                  \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ M"
      and accz: "ktc_state z = CAcc"
    shows "accepts_in_time_ktm N w (g (length w))"
proof -
  let ?n = "length w"
  let ?R = "ktm_step (delta_ktm (clock_product N D one))"
  let ?cN\<^sub>0 = "init_config_ktm N w"
  let ?cD\<^sub>0 = "init_config_ktm D (replicate ?n one)"
  let ?C\<^sub>0 = "KConfig (undefined :: nat)
                      (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
  let ?H = "KConfig (CRun (s_ktm N) (s_ktm D) True)
                    (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
  have cpv: "valid_ktm (clock_product N D one)"
    by (rule clock_product_valid [OF vN vD blle blD leD])

  from setup_forced_length [OF vN vD blle w run accz] have Mge: "2 * ?n + 3 \<le> M" .
  show ?thesis
  proof (cases "clock_start_state N D \<in> {CAcc, CRej}")
    case True
    from clock_setup_terminal_run [OF vN vD blle w run Mge True] accz
    have start: "s_ktm N = t_ktm N"
      by (auto simp: clock_start_state_def split: if_splits)
    show ?thesis
      unfolding accepts_in_time_ktm_def
      by (intro exI [where x = 0] exI [where x = "init_config_ktm N w"])
        (simp add: start)
  next
    case False
    have home: "clock_start_state N D = CRun (s_ktm N) (s_ktm D) True"
      using False by (auto simp: clock_start_state_def split: if_splits)
    from setup_forced_ge [OF vN vD blle w run Mge]
    have tail: "(?H, z) \<in> ?R ^^ (M - (2 * ?n + 3))" by (simp add: home)
    define K where "K = M - (2 * ?n + 3)"
    with tail have tailK: "(?H, z) \<in> ?R ^^ K" by simp

    have qW: "ktc_state ?H \<noteq> CWalk" and qB: "ktc_state ?H \<noteq> CBack"
     and turn: "cturn (ktc_state ?H)" by simp_all
    from clock_alternates [OF tailK qW qB turn] obtain f
      where f0H: "f 0 = ?H" and fK: "f K = z"
        and armN: "\<And>i. i < K \<Longrightarrow> even i
                     \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_N N D one)"
        and armD: "\<And>i. i < K \<Longrightarrow> odd i
                     \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_D N D one)"
      by blast

    have Kpos: "K \<noteq> 0"
    proof
      assume K0: "K = 0"
      have zH: "z = ?H" by (rule sym [OF trans [OF f0H [symmetric] fK [unfolded K0]]])
      from accz [unfolded zH] show False by simp
    qed
    then obtain K' where K: "K = Suc K'" by (cases K) auto

    have K'lt: "K' < K" by (simp add: K)
    have evK': "even K'"
    proof (rule ccontr)
      assume odd: "\<not> even K'"
      from armD [OF K'lt] odd obtain a a' d
        where "(ktc_state (f K'), a, ktc_state (f (Suc K')), a', d) \<in> arm_D N D one"
        by (blast elim: ktm_step_states)
      from arm_D_acc [OF this] fK accz show False by (simp add: K)
    qed
    then obtain m where m: "K' = 2 * m" by blast
    have mlt: "2 * m < K" using K'lt m by simp

    have wsig: "set w \<subseteq> Sigma_ktm (clock_product N D one)" using w by simp
    have vinit: "valid_config_ktm (clock_product N D one)
                   (init_config_ktm (clock_product N D one) w)"
      by (rule valid_init_config_ktm [OF cpv wsig])
    have tapes: "ktc_tapes_fit (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D) (f i)"
      if ile: "i \<le> K" for i
    proof -
      have setup_phase:
        "(init_config_ktm (clock_product N D one) w, f 0) \<in> ?R ^^ (2 * ?n + 3)"
        using setup_run [OF vN vD blle w] by (simp add: home f0H)
      have arm: "(f 0, f i) \<in> ?R ^^ i"
        by (rule clock_alternates_reach [where f = f and K = K, OF armN armD ile])
      from setup_phase arm
      have "(init_config_ktm (clock_product N D one) w, f i)
              \<in> ?R ^^ ((2 * ?n + 3) + i)"
        unfolding relpow_add by (rule relcompI)
      from valid_reach_relpow_ktm [OF cpv vinit this]
      show ?thesis using valid_config_tapes_fit by fastforce
    qed

    have inv\<^sub>0: "clock_inv N D one ?C\<^sub>0 ?cN\<^sub>0 ?cD\<^sub>0"
      by (rule clock_setup_inv [OF vN vD blD leD w])
    have f0: "f 0 = ktc_set_state (CRun (ktc_state ?cN\<^sub>0) (ktc_state ?cD\<^sub>0) True) ?C\<^sub>0"
      by (simp add: f0H ktc_state_init_config ktc_set_state_def)
    have aliveD\<^sub>0: "ktc_state ?cD\<^sub>0 \<noteq> t_ktm D" "ktc_state ?cD\<^sub>0 \<noteq> r_ktm D"
      using startD by (simp_all add: ktc_state_init_config)

    from clock_run_rev [OF vN vD blD inv\<^sub>0 aliveD\<^sub>0 f0 armN armD tapes mlt]
    obtain cN cD
      where runN: "(?cN\<^sub>0, cN) \<in> (ktm_step (delta_ktm N)) ^^ m"
        and runD: "(?cD\<^sub>0, cD) \<in> (ktm_step (delta_ktm D)) ^^ m"
        and aliveD: "ktc_state cD \<noteq> t_ktm D" "ktc_state cD \<noteq> r_ktm D"
        and stf: "ktc_state (f (2 * m)) = CRun (ktc_state cN) (ktc_state cD) True"
        and inv: "clock_inv N D one (ktc_set_state (0::nat) (f (2 * m))) cN cD"
      by blast

    have mg: "m < g ?n"
      by (rule alarm_running_lt [OF vD det alarm halt runD aliveD])

    have srcN: "ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True) (f (2 * m)) = f (2 * m)"
      unfolding stf [symmetric] by simp
    have sN': "(ktc_set_state (CRun (ktc_state cN) (ktc_state cD) True)
                        (ktc_set_state (0::nat) (f (2 * m))), f (Suc (2 * m)))
                 \<in> ktm_step (arm_N N D one)"
      using armN [OF mlt] by (simp add: srcN)
    from arm_N_rev [OF vN inv sN'] obtain cN'
      where stepN: "(cN, cN') \<in> ktm_step (delta_ktm N)"
        and tgtN: "ktc_state (f (Suc (2 * m)))
                     = (if ktc_state cN' = t_ktm N then CAcc
                        else if ktc_state cN' = r_ktm N then CRej
                        else CRun (ktc_state cN') (ktc_state cD) False)"
      by blast
    have accN: "ktc_state cN' = t_ktm N"
      using tgtN fK accz by (simp add: K m split: if_splits)

    have runN': "(?cN\<^sub>0, cN') \<in> (ktm_step (delta_ktm N)) ^^ Suc m"
      using runN stepN by (rule relpow_Suc_I)
    show ?thesis
      unfolding accepts_in_time_ktm_def
    proof (intro exI conjI)
      show "Suc m \<le> g ?n" using mg by simp
      show "(?cN\<^sub>0, cN') \<in> (ktm_step (delta_ktm N)) ^^ Suc m" by (rule runN')
      show "ktc_state cN' = t_ktm N" by (rule accN)
    qed
  qed
qed

text \<open>Every path, not only the accepting ones, ends within
  \<open>2 n + 3 + 2 g n\<close> steps.  The argument is \<open>clock_accepts_rev\<close>'s without the
  acceptance: past the setup, a run whose arm phase holds \<^term>\<open>g n\<close> full
  ticks would leave the constructor alive after \<^term>\<open>g n\<close> steps, which the
  alarm forbids.  This is the bound of Hopcroft and Ullman's convention for
  nondeterministic time, where no sequence of choices may run longer than the
  bound.\<close>

lemma clock_run_bounded:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D" and det: "det_ktm D"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and blD: "bl_ktm D = bl_ktm N" and leD: "le_ktm D = le_ktm N"
      and startD: "s_ktm D \<noteq> t_ktm D" "s_ktm D \<noteq> r_ktm D"
      and alarm: "(init_config_ktm D (replicate (length w) one), cfg)
                     \<in> (ktm_step (delta_ktm D)) ^^ (g (length w))"
      and halt: "ktc_state cfg = t_ktm D"
      and w: "set w \<subseteq> Sigma_ktm N"
      and run: "(init_config_ktm (clock_product N D one) w, z)
                  \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ M"
    shows "M \<le> 2 * length w + 3 + 2 * g (length w)"
proof (cases "2 * length w + 3 \<le> M")
  case False
  then show ?thesis by simp
next
  case Mge: True
  show ?thesis
  proof (cases "clock_start_state N D \<in> {CAcc, CRej}")
    case True
    from clock_setup_terminal_run [OF vN vD blle w run Mge True]
    show ?thesis by simp
  next
    case False
    have home: "clock_start_state N D = CRun (s_ktm N) (s_ktm D) True"
      using False by (auto simp: clock_start_state_def split: if_splits)
    let ?n = "length w"
    let ?R = "ktm_step (delta_ktm (clock_product N D one))"
    let ?cN\<^sub>0 = "init_config_ktm N w"
    let ?cD\<^sub>0 = "init_config_ktm D (replicate ?n one)"
    let ?C\<^sub>0 = "KConfig (undefined :: nat)
                        (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
    let ?H = "KConfig (CRun (s_ktm N) (s_ktm D) True)
                      (setup_tape N D one w 0) (setup_pos (k_ktm N) 0)"
    have cpv: "valid_ktm (clock_product N D one)"
      by (rule clock_product_valid [OF vN vD blle blD leD])
    from setup_forced_ge [OF vN vD blle w run Mge]
    have tail: "(?H, z) \<in> ?R ^^ (M - (2 * ?n + 3))" by (simp add: home)
    define K where "K = M - (2 * ?n + 3)"
    with tail have tailK: "(?H, z) \<in> ?R ^^ K" by simp
    have qW: "ktc_state ?H \<noteq> CWalk" and qB: "ktc_state ?H \<noteq> CBack"
     and turn: "cturn (ktc_state ?H)" by simp_all
    from clock_alternates [OF tailK qW qB turn] obtain f
      where f0H: "f 0 = ?H"
        and armN: "\<And>i. i < K \<Longrightarrow> even i
                     \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_N N D one)"
        and armD: "\<And>i. i < K \<Longrightarrow> odd i
                     \<Longrightarrow> (f i, f (Suc i)) \<in> ktm_step (arm_D N D one)"
      by blast
    have "K \<le> 2 * g ?n"
    proof (rule ccontr)
      assume "\<not> K \<le> 2 * g ?n"
      then have glt: "2 * g ?n < K" by simp
      have wsig: "set w \<subseteq> Sigma_ktm (clock_product N D one)" using w by simp
      have vinit: "valid_config_ktm (clock_product N D one)
                     (init_config_ktm (clock_product N D one) w)"
        by (rule valid_init_config_ktm [OF cpv wsig])
      have tapes: "ktc_tapes_fit (clock_Gamma N D one) (bl_ktm N) (clock_tapes N D) (f i)"
        if ile: "i \<le> K" for i
      proof -
        have setup_phase:
          "(init_config_ktm (clock_product N D one) w, f 0) \<in> ?R ^^ (2 * ?n + 3)"
        using setup_run [OF vN vD blle w] by (simp add: home f0H)
        have arm: "(f 0, f i) \<in> ?R ^^ i"
          by (rule clock_alternates_reach [where f = f and K = K, OF armN armD ile])
        from setup_phase arm
        have "(init_config_ktm (clock_product N D one) w, f i)
                \<in> ?R ^^ ((2 * ?n + 3) + i)"
          unfolding relpow_add by (rule relcompI)
        from valid_reach_relpow_ktm [OF cpv vinit this]
        show ?thesis using valid_config_tapes_fit by fastforce
      qed
      have inv\<^sub>0: "clock_inv N D one ?C\<^sub>0 ?cN\<^sub>0 ?cD\<^sub>0"
        by (rule clock_setup_inv [OF vN vD blD leD w])
      have f0: "f 0 = ktc_set_state (CRun (ktc_state ?cN\<^sub>0) (ktc_state ?cD\<^sub>0) True) ?C\<^sub>0"
        by (simp add: f0H ktc_state_init_config ktc_set_state_def)
      have aliveD\<^sub>0: "ktc_state ?cD\<^sub>0 \<noteq> t_ktm D" "ktc_state ?cD\<^sub>0 \<noteq> r_ktm D"
        using startD by (simp_all add: ktc_state_init_config)
      from clock_run_rev [OF vN vD blD inv\<^sub>0 aliveD\<^sub>0 f0 armN armD tapes glt]
      obtain cD
        where runD: "(?cD\<^sub>0, cD) \<in> (ktm_step (delta_ktm D)) ^^ g ?n"
          and aliveD: "ktc_state cD \<noteq> t_ktm D" "ktc_state cD \<noteq> r_ktm D"
        by blast
      from alarm_running_lt [OF vD det alarm halt runD aliveD] show False by simp
    qed
    then show ?thesis unfolding K_def by simp
  qed
qed

lemma clock_lang:
  assumes vN: "valid_ktm N" and vD: "valid_ktm D" and det: "det_ktm D"
      and st: "s_ktm N \<noteq> t_ktm N"
      and blle: "bl_ktm N \<noteq> le_ktm N"
      and blD: "bl_ktm D = bl_ktm N" and leD: "le_ktm D = le_ktm N"
      and oneD: "one \<in> Sigma_ktm D"
      and gn: "\<And>n. n \<le> g n"
      and alarm: "\<And>n. \<exists>cfg. (init_config_ktm D (replicate n one), cfg)
                              \<in> (ktm_step (delta_ktm D)) ^^ (g n)
                           \<and> ktc_state cfg = t_ktm D"
    shows "Lang_ktm (clock_product N D one)
             = {w. set w \<subseteq> Sigma_ktm N
                 \<and> accepts_in_time_ktm N w (g (length w))}"
proof -
  from alarm [of 1] obtain cfg\<^sub>1
    where a\<^sub>1: "(init_config_ktm D (replicate 1 one), cfg\<^sub>1)
                 \<in> (ktm_step (delta_ktm D)) ^^ (g 1)" by blast
  have "0 < g 1" using gn [of 1] by simp
  from alarm_start_alive [OF vD a\<^sub>1 this]
  have startD: "s_ktm D \<noteq> t_ktm D" "s_ktm D \<noteq> r_ktm D" by simp_all

  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix w assume "w \<in> Lang_ktm (clock_product N D one)"
    then have wsig: "set w \<subseteq> Sigma_ktm N"
      and ex: "\<exists>n. accepts_in_time_ktm (clock_product N D one) w n"
      unfolding Lang_ktm_iff by simp_all
    from ex obtain M z
      where run: "(init_config_ktm (clock_product N D one) w, z)
                    \<in> (ktm_step (delta_ktm (clock_product N D one))) ^^ M"
        and accz: "ktc_state z = t_ktm (clock_product N D one)"
      unfolding accepts_in_time_ktm_def by blast
    from accz have accz': "ktc_state z = CAcc" by simp
    from alarm [of "length w"] obtain cfg
      where al: "(init_config_ktm D (replicate (length w) one), cfg)
                   \<in> (ktm_step (delta_ktm D)) ^^ (g (length w))"
        and hl: "ktc_state cfg = t_ktm D" by blast
    from clock_accepts_rev [where g = g and w = w,
                            OF vN vD det blle blD leD startD al hl wsig run accz']
    show "w \<in> {w. set w \<subseteq> Sigma_ktm N
                \<and> accepts_in_time_ktm N w (g (length w))}"
      using wsig by simp
  next
    fix w assume "w \<in> {w. set w \<subseteq> Sigma_ktm N
                        \<and> accepts_in_time_ktm N w (g (length w))}"
    then have wsig: "set w \<subseteq> Sigma_ktm N"
      and acc: "accepts_in_time_ktm N w (g (length w))" by simp_all
    have alarmw: "\<exists>cfg. (init_config_ktm D (replicate (length w) one), cfg)
                          \<in> (ktm_step (delta_ktm D)) ^^ (g (length w))"
      using alarm [of "length w"] by blast
    from clock_accepts [where g = g and w = w,
                        OF vN vD st blle blD leD oneD gn [of "length w"]
                           alarmw wsig acc]
    show "w \<in> Lang_ktm (clock_product N D one)"
      unfolding Lang_ktm_iff using wsig by auto
  qed
qed

end
