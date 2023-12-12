section \<open>Knuth-Morris-Pratt fast string search algorithm\<close>

text \<open>Development based on Filliâtre's verification using Why3\<close>

theory KnuthMorrisPratt imports "Collections.Diff_Array"

begin

subsection \<open>General definitions\<close>

abbreviation "array \<equiv> new_array"
abbreviation length_array :: "'a array \<Rightarrow> nat" ("\<parallel>_\<parallel>") 
    where "length_array \<equiv> array_length"
notation array_get (infixl "!!" 100)
notation array_set ("_[_ ::= _]" [1000,0,0] 900)

definition matches :: "'a array \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "matches a i b j n = (i+n \<le> \<parallel>a\<parallel> \<and> j+n \<le> \<parallel>b\<parallel> 
                           \<and> (\<forall>k<n. a!!(i+k) = b!!(j+k)))"

lemma matches_empty [simp]: "matches a i b j 0 \<longleftrightarrow> i \<le> \<parallel>a\<parallel> \<and> j \<le> \<parallel>b\<parallel>"
  by (simp add: matches_def)

lemma matches_right_extension:
  "\<lbrakk>matches a i b j n;
    Suc (i+n) \<le> \<parallel>a\<parallel>;
    Suc (j+n) \<le> \<parallel>b\<parallel>;
    a!!(i+n) = b!!(j+n)\<rbrakk> \<Longrightarrow>
    matches a i b j (Suc n)"
  by (auto simp: matches_def less_Suc_eq)

lemma matches_contradiction_at_first:
  "\<lbrakk>0 < n; a!!i \<noteq> b!!j\<rbrakk> \<Longrightarrow> \<not> matches a i b j n"
  by (auto simp: matches_def)

lemma matches_contradiction_at_i:
  "\<lbrakk>a!!(i+k) \<noteq> b!!(j+k); k < n\<rbrakk> \<Longrightarrow> \<not> matches a i b j n"
  by (auto simp: matches_def)

lemma matches_right_weakening:
  "\<lbrakk>matches a i b j n; n' \<le> n\<rbrakk> \<Longrightarrow> matches a i b j n'"
  by (auto simp: matches_def)

lemma matches_left_weakening_add:
  assumes "matches a i b j n" "k\<le>n"
  shows "matches a (i+k) b (j+k) (n-k)"
  using assms by (auto simp: matches_def less_diff_conv algebra_simps)

lemma matches_left_weakening:
  assumes "matches a (i - (n - n')) b (j - (n - n')) n"
      and "n' \<le> n"                                                   
      and "n - n' \<le> i"
      and "n - n' \<le> j"
    shows "matches a i b j n'"
  by (metis assms diff_diff_cancel diff_le_self le_add_diff_inverse2 matches_left_weakening_add)

lemma matches_sym: "matches a i b j n \<Longrightarrow> matches b j a i n"
  by (simp add: matches_def)

lemma matches_trans:
  "\<lbrakk>matches a i b j n; matches b j c k n\<rbrakk> \<Longrightarrow> matches a i c k n"
  by (simp add: matches_def)

text \<open>Denotes the maximal @{term "n < j"} such that the first @{term n} elements of @{term p}
      match the last @{term n} elements of @{term p}[0..@{term "j-1"}]
The first @{term n} characters of the pattern have a copy starting at @{term "j-n"}.\<close>
definition is_next :: "'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_next p j n =
     (n < j \<and> matches p (j-n) p 0 n \<and> (\<forall>m. n < m \<and> m < j \<longrightarrow> \<not> matches p (j-m) p 0 m))"

lemma next_iteration:
  assumes "matches a (i-j) p 0 j" "is_next p j n" "j \<le> i" 
  shows "matches a (i-n) p 0 n"
proof -
  have "matches a (i-n) p (j-n) n"
    using assms by (auto simp: algebra_simps is_next_def intro: matches_left_weakening [where n=j])
  moreover have "matches p (j-n) p 0 n"
    using is_next_def assms by blast
  ultimately show ?thesis
    using matches_trans by blast
qed

lemma next_is_maximal:
  assumes "matches a (i-j) p 0 j" "is_next p j n"
    and "j \<le> i" "n < m" "m < j"
  shows "\<not> matches a (i-m) p 0 m"
proof -
  have "matches a (i-m) p (j-m) m"
    by (rule matches_left_weakening [where n=j]) (use assms in auto)
  with assms show ?thesis
    by (meson is_next_def matches_sym matches_trans)
qed

text \<open>Filliâtre's version of the lemma above\<close>
corollary next_is_maximal':
  assumes match: "matches a (i-j) p 0 j" "is_next p j n"
    and more: "j \<le> i" "i-j < k" "k < i-n"
  shows "\<not> matches a k p 0 \<parallel>p\<parallel>"
proof -
  have "\<not> matches a k p 0 (i-k)"
    using next_is_maximal [OF match] more
    by (metis add.commute diff_diff_cancel diff_le_self le_trans less_diff_conv less_or_eq_imp_le)
  moreover have "i-k < \<parallel>p\<parallel>"
    using assms by (auto simp: matches_def)
  ultimately show ?thesis
    using matches_right_weakening nless_le by blast
qed

lemma next_1_0 [simp]: "is_next p 1 0 \<longleftrightarrow> 1 \<le> \<parallel>p\<parallel>"
  by (auto simp add: is_next_def matches_def)

subsection \<open>The Build-table routine\<close>

definition buildtab_step :: "'a array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<times> nat \<times> nat" where
  "buildtab_step p nxt i j =
       (if p!!i = p!!j then (nxt[Suc i::=Suc j], Suc i, Suc j)
           else if j=0 then (nxt[Suc i::=0], Suc i, j)
                else (nxt, i, nxt!!j))"

text \<open>The conjunction of the invariants given in the Why3 development\<close>
definition buildtab_invariant :: "'a array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "buildtab_invariant p nxt i j = 
     (\<parallel>nxt\<parallel> = \<parallel>p\<parallel> \<and> i \<le> \<parallel>p\<parallel> 
   \<and> j<i \<and> matches p (i-j) p 0 j
   \<and> (\<forall>k. 0 < k \<and> k \<le> i \<longrightarrow> is_next p k (nxt!!k))
   \<and> (\<forall>k. Suc j < k \<and> k < Suc i \<longrightarrow> \<not> matches p (Suc i - k) p 0 k))"

text \<open>The invariant trivially holds upon initialisation\<close>

lemma buildtab_invariant_init: "\<parallel>p\<parallel> \<ge> 2 \<Longrightarrow> buildtab_invariant p (array 0 \<parallel>p\<parallel>) 1 0"
  by (auto simp: buildtab_invariant_def is_next_def)

subsubsection \<open>The invariant holds after an iteration\<close>
text \<open>each conjunct is proved separately\<close>

lemma length_invariant:
  shows "let (nxt',i',j') = buildtab_step p nxt i j in \<parallel>nxt'\<parallel> = \<parallel>nxt\<parallel>"
  by (simp add: buildtab_step_def)

lemma i_invariant:
  assumes "Suc i < m"
  shows "let (nxt',i',j') = buildtab_step p nxt i j in i' \<le> m"
  using assms by (simp add: buildtab_step_def)

lemma ji_invariant:
  assumes "buildtab_invariant p nxt i j" 
  shows "let (nxt',i',j') = buildtab_step p nxt i j in j'<i'"
proof -
  have j: "0 < j \<Longrightarrow> nxt !! j < j"
    using assms by (simp add: buildtab_invariant_def is_next_def)
  show ?thesis
    using assms by (auto simp add: buildtab_invariant_def buildtab_step_def intro: order.strict_trans j)
qed

lemma matches_invariant:
  assumes "buildtab_invariant p nxt i j" and "Suc i < \<parallel>p\<parallel>"
  shows "let (nxt',i',j') = buildtab_step p nxt i j in matches p (i' - j') p 0 j'"
  using assms by (auto simp: buildtab_invariant_def buildtab_step_def matches_right_extension intro: next_iteration)

lemma is_next_invariant:
  assumes "buildtab_invariant p nxt i j" and "Suc i < \<parallel>p\<parallel>"
  shows "let (nxt',i',j') = buildtab_step p nxt i j in \<forall>k. 0 < k \<longrightarrow> k \<le> i' \<longrightarrow> is_next p k (nxt'!!k)"
proof (cases "p!!i = p!!j")
  case True
  with assms have "matches p (i-j) p 0 (Suc j)"
    by (simp add: buildtab_invariant_def matches_right_extension)
  then have "is_next p (Suc i) (Suc j)"
    using assms by (auto simp: is_next_def buildtab_invariant_def)
  with True assms show ?thesis
    by (simp add: buildtab_invariant_def buildtab_step_def array_get_array_set_other le_Suc_eq)
next
  case neq: False
  show ?thesis
  proof (cases "j=0")
    case True
    then have "\<not> matches p (i-j) p 0 (Suc j)"
      using matches_contradiction_at_first neq by fastforce
    with True assms have "is_next p (Suc i) 0"
      unfolding is_next_def buildtab_invariant_def
      by (metis Suc_leI diff_Suc_Suc diff_zero matches_empty nat_less_le zero_less_Suc)
    with assms neq show ?thesis
      by (simp add: buildtab_invariant_def buildtab_step_def array_get_array_set_other le_Suc_eq)
  next
    case False
    with assms neq show ?thesis
      by (simp add: buildtab_invariant_def buildtab_step_def)
  qed
qed

lemma non_matches_aux: 
  assumes "Suc (Suc j) < k" "matches p (Suc (Suc i) - k) p 0 k" 
  shows "matches p (Suc i - (k - Suc 0)) p 0 (k - Suc 0)"
  using matches_right_weakening assms by fastforce

lemma non_matches_invariant:
  assumes bt: "buildtab_invariant p nxt i j" and "\<parallel>p\<parallel> \<ge> 2" "Suc i < \<parallel>p\<parallel>"
  shows "let (nxt',i',j') = buildtab_step p nxt i j in \<forall>k. Suc j' < k \<longrightarrow> k < Suc i' \<longrightarrow> \<not> matches p (Suc i' - k) p 0 k"
proof (cases "p!!i = p!!j")
  case True
  with non_matches_aux bt show ?thesis
    by (fastforce simp add: Suc_less_eq2 buildtab_step_def buildtab_invariant_def)
next
  case neq: False
  have "j < i"
    using bt by (auto simp: buildtab_invariant_def)
  then have no_match_Sj: "\<not> matches p (Suc i - Suc j) p 0 (Suc j)"
    using neq by (force simp: matches_def)
  show ?thesis
  proof (cases "j=0")
    case True
    have "\<not> matches p (Suc (Suc i) - k) p 0 k"
      if "Suc 0 < k" and "k < Suc (Suc i)" for k 
    proof (cases "k = Suc (Suc 0)")
      case True
      with assms neq that show ?thesis
        by (auto simp add: matches_contradiction_at_first \<open>j=0\<close>)
    next
      case False
      then have "Suc 0 < k - Suc 0"
        using that by linarith
      with bt that have "\<not> matches p (Suc i - (k - Suc 0)) p 0 (k - Suc 0)"
        using True by (force simp add: buildtab_invariant_def)
      then show ?thesis
        by (metis False Suc_lessI non_matches_aux that(1))
    qed
    with True show ?thesis
      by (auto simp: buildtab_invariant_def buildtab_step_def)
  next
    case False
    then have "0 < j"
      by auto
    have False if lessK: "Suc (nxt!!j) < k" and "k < Suc i" and contra: "matches p (Suc i - k) p 0 k" for k
    proof (cases "Suc j < k")
      case True
      then show ?thesis
        using bt that by (auto simp: buildtab_invariant_def)        
    next
      case False
      then have "k \<le> j"
        using less_Suc_eq_le no_match_Sj contra by fastforce
      obtain k' where k': "k = Suc k'" "k' < i"
        using \<open>k < Suc i\<close> lessK not0_implies_Suc by fastforce
      have "is_next p j (nxt!!j)"
        using bt that \<open>j>0\<close> by (auto simp: buildtab_invariant_def)
      with no_match_Sj k' have "\<not> matches p (j - k') p 0 k'"
        by (metis Suc_less_eq \<open>k \<le> j\<close> is_next_def lessK less_Suc_eq_le)
      moreover 
      have "matches p 0 p (i-j) j"
        using bt buildtab_invariant_def by (metis matches_sym)
      then have "matches p (j-k') p (i - k') k'"
        using \<open>j<i\<close> False k' matches_left_weakening
        by (smt (verit, best) Nat.diff_diff_eq Suc_leI Suc_le_lessD \<open>k \<le> j\<close> diff_diff_cancel diff_is_0_eq lessI nat_less_le)
      moreover have "matches p (i - k') p 0 k'"
        using contra k' matches_right_weakening by fastforce
      ultimately show False
        using matches_trans by blast
    qed
    with assms neq False show ?thesis
      by (auto simp: buildtab_invariant_def buildtab_step_def)
  qed   
qed

lemma buildtab_invariant:
  assumes ini: "buildtab_invariant p nxt i j"
  and "Suc i < \<parallel>p\<parallel>" "(nxt',i',j') = buildtab_step p nxt i j"
  shows "buildtab_invariant p nxt' i' j'"
  unfolding buildtab_invariant_def
  using assms i_invariant [of concl: p nxt i j] length_invariant [of p nxt i j]
    ji_invariant [OF ini] matches_invariant [OF ini] non_matches_invariant [OF ini] is_next_invariant [OF ini]
  by (simp add: buildtab_invariant_def split: prod.split_asm)

subsubsection \<open>The build-table loop and its correctness\<close>

partial_function (tailrec) buildtab :: "'a array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array" where
  "buildtab p nxt i j =
     (if Suc i < \<parallel>p\<parallel>
      then let (nxt',i',j') = buildtab_step p nxt i j in buildtab p nxt' i' j'
      else nxt)"
declare buildtab.simps[code]

definition "rel_buildtab m = inv_image (lex_prod (measure (\<lambda>i. m-i)) (measure id)) snd"

lemma wf_rel_buildtab: "wf (rel_buildtab m)"
  unfolding rel_buildtab_def
  by (auto intro: wf_same_fst)

lemma buildtab_correct:
  assumes k: "0<k \<and> k < \<parallel>p\<parallel>" and ini: "buildtab_invariant p nxt i j"
  shows "is_next p k (buildtab p nxt i j !! k)"
  using ini
proof (induction "(nxt,i,j)" arbitrary: nxt i j rule: wf_induct_rule[OF wf_rel_buildtab [of "\<parallel>p\<parallel>"]])
  case (1 nxt i j)
  show ?case
  proof (cases "Suc i < \<parallel>p\<parallel>")
    case True
    then obtain nxt' i' j' 
        where eq: "(nxt', i', j') = buildtab_step p nxt i j" and invar': "buildtab_invariant p nxt' i' j'"
      using "1.prems" buildtab_invariant by (metis surj_pair)
    then have "j>0 \<Longrightarrow> nxt'!!j < j"
      using "1.prems"
      by (auto simp: buildtab_invariant_def is_next_def buildtab_step_def split: if_split_asm)
    then have decreasing: "((nxt', i', j'), nxt, i, j) \<in> rel_buildtab \<parallel>p\<parallel>"
      using eq True by (auto simp: rel_buildtab_def buildtab_step_def split: if_split_asm)
    show ?thesis
      using "1.hyps" [OF decreasing invar'] "1.prems" eq True
        by(auto simp add: buildtab.simps[of p nxt] split: prod.splits)
  next
    case False
    with 1 k show ?thesis
      by (auto simp: buildtab_invariant_def buildtab.simps)
  qed
qed

text \<open>Before building the table, check for the degenerate case\<close>
definition table :: "'a array \<Rightarrow> nat array" where
 "table p = (if \<parallel>p\<parallel> > 1 then buildtab p (array 0 \<parallel>p\<parallel>) 1 0 
            else array 0 \<parallel>p\<parallel>)"
declare table_def[code]

lemma is_next_table:
  assumes "0 < j \<and> j < \<parallel>p\<parallel>"
  shows "is_next p j (table p !!j)"
  using buildtab_correct[of _ p] buildtab_invariant_init[of p] assms by (simp add: table_def)


subsubsection \<open>Linearity of @{term buildtab}\<close>

partial_function (tailrec) T_buildtab :: "'a array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "T_buildtab p nxt i j t =
     (if Suc i < \<parallel>p\<parallel>
      then let (nxt',i',j') = buildtab_step p nxt i j in T_buildtab p nxt' i' j' (Suc t)
      else t)"

lemma T_buildtab_correct:
  assumes ini: "buildtab_invariant p nxt i j"
  shows "T_buildtab p nxt i j t \<le> 2*\<parallel>p\<parallel> - 2*i + j + t"
  using ini
proof (induction "(nxt,i,j)" arbitrary: nxt i j t rule: wf_induct_rule[OF wf_rel_buildtab [of "\<parallel>p\<parallel>"]])
  case 1
  have *: "Suc (T_buildtab p nxt' i' j' t) \<le> 2*\<parallel>p\<parallel> - 2*i + j + t"
    if eq: "buildtab_step p nxt i j = (nxt', i', j')" and "Suc i < \<parallel>p\<parallel>"
    for nxt' i' j' t
  proof -
    have invar': "buildtab_invariant p nxt' i' j'"
      using "1.prems" buildtab_invariant that by fastforce
    then have nextj: "j>0 \<Longrightarrow> nxt'!!j < j"
      using eq "1.prems"
      by (auto simp: buildtab_invariant_def is_next_def buildtab_step_def split: if_split_asm)
    then have decreasing: "((nxt', i', j'), nxt, i, j) \<in> rel_buildtab \<parallel>p\<parallel>"
      using that by (auto simp: rel_buildtab_def same_fst_def buildtab_step_def split: if_split_asm)
    then have "T_buildtab p nxt' i' j' t \<le> 2 * \<parallel>p\<parallel> - 2 * i' + j' + t"
      using "1.hyps" invar' by blast
    then show ?thesis
      using "1.prems" that nextj
      by (force simp: T_buildtab.simps [of p nxt' i' j'] buildtab_step_def split: if_split_asm)
  qed             
  show ?case
    using * [where t = "Suc t"] by (auto simp add: T_buildtab.simps split: prod.split)
qed

lemma T_buildtab_linear:
  assumes "2 \<le> \<parallel>p\<parallel>" 
  shows "T_buildtab p (array 0 \<parallel>p\<parallel>) 1 0 0 \<le> 2*(\<parallel>p\<parallel> - 1)"
  using assms T_buildtab_correct [OF buildtab_invariant_init, of p 0] by auto

subsection \<open>The actual string search algorithm\<close>

definition 
  "KMP_step p nxt a i j =
      (if a!!i = p!!j then (Suc i, Suc j)
       else if j=0 then (Suc i, 0) else (i, nxt!!j))"

text \<open>The conjunction of the invariants given in the Why3 development\<close>
definition KMP_invariant :: "'a array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 "KMP_invariant p a i j = 
      (j \<le> \<parallel>p\<parallel> \<and> j\<le>i \<and> i \<le> \<parallel>a\<parallel> \<and> matches a (i-j) p 0 j
    \<and> (\<forall>k < i-j. \<not> matches a k p 0 \<parallel>p\<parallel>))"

text \<open>The invariant trivially holds upon initialisation\<close>

lemma KMP_invariant_init: "KMP_invariant p a 0 0"
  by (auto simp: KMP_invariant_def)

text \<open>The invariant holds after an iteration\<close>

lemma KMP_invariant:
  assumes ini: "KMP_invariant p a i j"
    and j: "j < \<parallel>p\<parallel>" and i: "i < \<parallel>a\<parallel>"
  shows "let (i',j') = KMP_step p (table p) a i j in KMP_invariant p a i' j'"
proof (cases "a!!i = p!!j")
  case True
  then show ?thesis
    using assms by (simp add: KMP_invariant_def KMP_step_def matches_right_extension)
next
  case neq: False
  show ?thesis
  proof (cases "j=0")
    case True
    with neq assms show ?thesis
      by (simp add: matches_contradiction_at_first KMP_invariant_def KMP_step_def less_Suc_eq)
  next
    case False
    then have is_nxt: "is_next p j (table p !!j)"
      using assms is_next_table j by blast
    then have "table p !! j \<le> j"
      by (simp add: is_next_def)
    moreover have "matches a (i - table p !! j) p 0 (table p !! j)"
      by (meson is_nxt KMP_invariant_def ini next_iteration)
    moreover
    have False if k: "k < i - table p !! j" and ma: "matches a k p 0 \<parallel>p\<parallel>" for k
    proof -
      have "k \<noteq> i-j"
        by (metis KMP_invariant_def add_0 ini j le_add_diff_inverse2 ma matches_contradiction_at_i neq)
      then show False
        by (meson KMP_invariant_def ini is_nxt k linorder_cases ma next_is_maximal')
    qed
    ultimately show ?thesis 
      using neq assms False by (auto simp: KMP_invariant_def KMP_step_def)
  qed
qed

text \<open>The first three arguments are precomputed so that they are not part of the inner loop.\<close>
partial_function (tailrec) search :: "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat * nat" where
  "search m n nxt p a i j =
     (if j < m \<and> i < n then let (i',j') = KMP_step p nxt a i j in search m n nxt p a i' j'
      else (i,j))"
declare search.simps[code]

definition "rel_KMP n = lex_prod (measure (\<lambda>i. n-i)) (measure id)"

lemma wf_rel_KMP: "wf (rel_KMP n)"
  unfolding rel_KMP_def by (auto intro: wf_same_fst)

text \<open>Also expresses the absence of a match, when @{term "r = \<parallel>a\<parallel>"}\<close>
definition first_occur :: "'a array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> bool"
  where "first_occur p a r = ((r < \<parallel>a\<parallel> \<longrightarrow> matches a r p 0 \<parallel>p\<parallel>) \<and> (\<forall>k<r. \<not> matches a k p 0 \<parallel>p\<parallel>))"

lemma KMP_correct:
  assumes ini: "KMP_invariant p a i j"  
  defines [simp]: "nxt \<equiv> table p" 
  shows "let (i',j') = search \<parallel>p\<parallel> \<parallel>a\<parallel> nxt p a i j in first_occur p a (if j' = \<parallel>p\<parallel> then i' - \<parallel>p\<parallel> else i')"
  using ini
proof (induction "(i,j)" arbitrary: i j rule: wf_induct_rule[OF wf_rel_KMP [of "\<parallel>a\<parallel>"]])
  case (1 i j)
  then have ij: "j \<le> \<parallel>p\<parallel>" "j \<le> i"  "i \<le> \<parallel>a\<parallel>" 
    and match: "matches a (i - j) p 0 j" 
    and nomatch: "(\<forall>k<i - j. \<not> matches a k p 0 \<parallel>p\<parallel>)"
    by (auto simp: KMP_invariant_def)
  show ?case
  proof (cases "j < \<parallel>p\<parallel> \<and> i < \<parallel>a\<parallel>")
    case True
    have "first_occur p a (if j'' = \<parallel>p\<parallel> then i'' - \<parallel>p\<parallel> else i'')"
      if eq: "KMP_step p (table p) a i j = (i', j')" and eq': "search \<parallel>p\<parallel> \<parallel>a\<parallel> nxt p a i' j' = (i'',j'')"
      for i' j' i'' j''
    proof -
      have decreasing: "((i',j'), i, j) \<in> rel_KMP \<parallel>a\<parallel>"
        using that is_next_table [of j] True
        by (auto simp: rel_KMP_def KMP_step_def is_next_def split: if_split_asm)
      show ?thesis
        using "1.hyps" [OF decreasing] "1.prems" KMP_invariant that True by fastforce
    qed
    with True show ?thesis
      by (smt (verit, best) case_prodI2 nxt_def prod.case_distrib search.simps)
  next
    case False
    have "False" if "matches a k p 0 \<parallel>p\<parallel>" "j < \<parallel>p\<parallel>" "i = \<parallel>a\<parallel>" for k
    proof -
      have "\<parallel>p\<parallel>+k \<le> i"
        using that by (simp add: matches_def)
      with that nomatch show False by auto
    qed
    with False ij show ?thesis
      apply (simp add: first_occur_def split: prod.split)
      by (metis le_less_Suc_eq match nomatch not_less_eq prod.inject search.simps)
  qed
qed

definition KMP_search :: "'a array \<Rightarrow> 'a array \<Rightarrow> nat \<times> nat" where
  "KMP_search p a = search \<parallel>p\<parallel> \<parallel>a\<parallel> (table p) p a 0 0"
declare KMP_search_def[code]

lemma KMP_search:
   "(i,j) = KMP_search p a \<Longrightarrow> first_occur p a (if j = \<parallel>p\<parallel> then i - \<parallel>p\<parallel> else i)"
unfolding KMP_search_def
using KMP_correct[OF KMP_invariant_init[of p a]] by auto


subsection \<open>Examples\<close>

definition "Knuth_pattern = array_of_list [1,2,3,1,2,3,1,3,1,2::nat]"

value "list_of_array (table Knuth_pattern)"

definition "CLR_pattern = array_of_list [1,2,1,2,1,2,1,2,3,1::nat]"

value "list_of_array (table CLR_pattern)"

definition bad_list :: "nat \<Rightarrow> nat list"
  where "bad_list n = replicate n 0 @ [Suc 0]"

definition "bad_pattern = array_of_list (bad_list 1000)"

definition "bad_string = array_of_list (bad_list 2000000)"

definition "worse_string = array_of_list (replicate 2000000 (0::nat))"

definition "lousy_string = array_of_list (concat (replicate 2002 (bad_list 999)))"

value "list_of_array (table bad_pattern)"

text \<open>A successful search\<close>
value "KMP_search bad_pattern bad_string"

lemma "matches bad_string (2000001-1001) bad_pattern 0 1001"
  by eval

text \<open>Unsuccessful searches\<close>
value "KMP_search bad_pattern worse_string"

lemma "\<forall>k<2000000. \<not> matches worse_string k bad_pattern 0 1001"
  by eval

value "KMP_search lousy_string bad_string"

lemma "\<forall>k < \<parallel>lousy_string\<parallel>. \<not> matches lousy_string k bad_pattern 0 1001"
  by eval

end
