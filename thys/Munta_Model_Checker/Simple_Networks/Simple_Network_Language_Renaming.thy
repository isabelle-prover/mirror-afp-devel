section \<open>Renaming Identifiers in Simple Networks\<close>

theory Simple_Network_Language_Renaming
  imports Simple_Network_Language_Model_Checking
begin

text \<open>The part justifies a ``renaming'' step to normalize identifiers in the input.\<close>

unbundle no_library_syntax
notation (input) TAG ("_ \<bbar> _" [40, 40] 41)

text \<open>Helpful methods and theorems to work with tags:\<close>

lemmas TAG_cong = arg_cong[where f = "TAG t" for t]

lemma TAG_mp:
  assumes "TAG t x" "x \<Longrightarrow> y"
  shows "TAG t y"
  using assms unfolding TAG_def by blast

lemma TAG_mp':
  assumes "TAG t x" "x \<Longrightarrow> y"
  shows y
  using assms unfolding TAG_def by blast


lemmas all_mono_rule = all_mono[THEN mp, OF impI, rotated]

lemma imp_mono_rule:
  assumes "P1 \<longrightarrow> P2"
    and "Q1 \<Longrightarrow> P1"
    and "Q1 \<Longrightarrow> P2 \<Longrightarrow> Q2"
  shows "Q1 \<longrightarrow> Q2"
  using assms by blast

lemma Ball_mono:
  assumes "\<forall>x \<in> S. P x" "\<And>x. x \<in> S \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "\<forall>x \<in> S. Q x"
  using assms by blast

method prop_monos =
  erule all_mono_rule
  | erule (1) imp_mono_rule
  | erule disj_mono[rule_format, rotated 2]

locale Prod_TA_Defs_urge =
  fixes A :: "('a, 's, 'c, 't :: {zero}, 'x, 'v :: linorder) nta" and urge :: 'c
begin

definition
  "add_reset \<equiv> \<lambda>(C, U, T, I).
    (C, {}, (\<lambda>(l, b, g, a, f, r, l'). (l, b, g, a, f, urge # r, l')) ` T, I)"

definition
  "add_inv \<equiv> \<lambda>(C, U, T, I). (C, U, T,
    (\<lambda>l. if l \<in> U then acconstraint.LE urge 0 # I l else I l))"

definition "A_urge \<equiv>
  (fst A, map add_reset (map add_inv (fst (snd A))), snd (snd A))"

definition
  "N_urge i \<equiv> map add_reset (map add_inv (fst (snd A))) ! i"

end

locale Prod_TA_sem_urge =
  Prod_TA_Defs_urge A urge + Prod_TA_sem A
  for A :: "('a, 's, 'c, 't :: {zero, time}, 'x, 'v :: linorder) nta" and urge :: 'c +
  assumes urge_not_in_invariants:
    "\<forall>(_, _, _, I) \<in> set (fst (snd A)). \<forall>l. urge \<notin> constraint_clk ` set (I l)"
  assumes urge_not_in_guards:
    "\<forall>(_, _, T, _) \<in> set (fst (snd A)). \<forall>(l, b, g, a, f, r, l') \<in> T. urge \<notin> constraint_clk ` set g"
  assumes urge_not_in_resets:
    "\<forall>(_, _, T, _) \<in> set (fst (snd A)). \<forall>(l, b, g, a, f, r, l') \<in> T. urge \<notin> set r"
begin

lemma N_urge_simp:
  "N_urge i = add_reset (add_inv (N i))" if "i < n_ps"
  using that unfolding N_urge_def N_def by (simp add: n_ps_def)

lemma inv_add_reset:
  "inv (add_reset A') = inv A'"
  unfolding inv_def add_reset_def by (simp split: prod.splits)

lemma inv_add_inv:
  "inv (add_inv (C, U, T, I)) = (\<lambda>l. if l \<in> U then acconstraint.LE urge 0 # I l else I l)"
  unfolding add_inv_def inv_def by simp

definition
  "is_urgent L \<equiv> \<exists>p<n_ps. L ! p \<in> urgent (N p)"

lemma map_nth':
  "map ((!) xs) [0..<n] = xs" if "n = length xs"
  using that List.map_nth by simp

lemma A_urge_split:
  "A_urge = (broadcast, map N_urge [0..<n_ps], bounds)"
  unfolding broadcast_def N_urge_def bounds_def n_ps_def A_urge_def by (cases A)(simp add: map_nth')

lemma inv_add_inv':
  "inv (add_inv A') =
  (\<lambda>l. if l \<in> urgent A' then acconstraint.LE urge 0 # inv A' l else inv A' l)"
  apply (cases A')
  apply (simp add: inv_add_inv urgent_def)
  unfolding inv_def
  apply auto
  done

lemma A_split':
  "A = (fst A, fst (snd A), snd (snd A))"
  by auto

lemma is_urgent_simp:
  "(\<exists>p<n_ps. L ! p \<in> urgent (map N [0..<n_ps] ! p)) \<longleftrightarrow> is_urgent L"
  unfolding is_urgent_def by auto

lemma urgent_N_urge:
  "urgent (N_urge p) = {}" if "p < n_ps"
  using that unfolding N_def N_urge_def n_ps_def urgent_def add_reset_def add_inv_def
  by (auto split: prod.split_asm)

lemma committed_N_urge:
  "committed (N_urge p) = committed (N p)" if "p < n_ps"
  using that unfolding N_def N_urge_def n_ps_def committed_def add_reset_def add_inv_def
  by (auto split: prod.split)

lemma is_urgent_simp2:
  "(\<exists>p<n_ps. L ! p \<in> urgent (map N_urge [0..<n_ps] ! p)) \<longleftrightarrow> False"
  unfolding is_urgent_def by (auto simp: urgent_N_urge)

lemma inv_add_invI1:
  "u \<turnstile> inv (add_inv (N p)) (L ! p)" if "u \<turnstile> inv (N p) (L ! p)" "\<not> is_urgent L" "p < n_ps"
  using that unfolding inv_add_inv' is_urgent_def by simp

lemma inv_add_invI2:
  "u \<turnstile> inv (add_inv (N p)) (L ! p)" if "u \<turnstile> inv (N p) (L ! p)" "u urge \<le> 0" "p < n_ps"
  using that unfolding inv_add_inv' is_urgent_def by (auto elim: guard_consI[rotated])

lemma inv_add_invD:
  "u \<turnstile> inv A' l" if "u \<turnstile> inv (add_inv A') l"
  using that unfolding inv_add_inv' by (auto split: if_split_asm simp: clock_val_def)

lemma inv_N_urge:
  "inv (N_urge p) = inv (add_inv (N p))" if "p < n_ps"
  using that by (simp add: N_urge_simp inv_add_reset)

lemma N_urge_trans_simp:
  "trans (N_urge i) = (\<lambda>(l, b, g, a, f, r, l'). (l, b, g, a, f, urge # r, l')) ` (trans (N i))"
  if "i < n_ps"
  unfolding N_urge_simp[OF that] add_inv_def add_reset_def trans_def by (simp split: prod.splits)

lemma trans_N_urgeD:
  "(l, b, g, a, f, urge # r, l') \<in> trans (N_urge p)"
  if "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  using that by (force simp add: N_urge_trans_simp)

lemma trans_N_urgeE:
  assumes "(l, b, g, a, f, r, l') \<in> trans (N_urge p)" "p < n_ps"
  obtains "(l, b, g, a, f, tl r, l') \<in> trans (N p)" "r = urge # tl r"
  using assms by (force simp add: N_urge_trans_simp)

lemma urge_not_in_inv:
  "urge \<notin> constraint_clk ` set (inv (N p) l)" if "p < n_ps"
  using urge_not_in_invariants that unfolding N_def inv_def n_ps_def by (fastforce dest! :nth_mem)

lemma urge_not_in_guards':
  assumes "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  shows "urge \<notin> constraint_clk ` set g"
  using urge_not_in_guards assms unfolding N_def trans_def n_ps_def by (fastforce dest! :nth_mem)

lemma urge_not_in_resets':
  assumes "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  shows "urge \<notin> set r"
  using urge_not_in_resets assms unfolding N_def trans_def n_ps_def by (fastforce dest! :nth_mem)

lemma clk_upd_clock_val_a_simp:
  "u(c := d) \<turnstile>\<^sub>a ac \<longleftrightarrow> u \<turnstile>\<^sub>a ac" if "c \<noteq> constraint_clk ac"
  using that by (cases ac) auto

lemma clk_upd_clock_val_simp:
  "u(c := d) \<turnstile> cc \<longleftrightarrow> u \<turnstile> cc" if "c \<notin> constraint_clk ` set cc"
  using that unfolding clock_val_def list_all_def
  by (force simp: image_def clk_upd_clock_val_a_simp)

lemma inv_N_urgeI:
  assumes "u \<turnstile> inv (N p) l" "p < n_ps"
  shows "u(urge := 0) \<turnstile> inv (N_urge p) l"
  using assms urge_not_in_inv[of p]
  by (auto simp: inv_N_urge inv_add_inv' clk_upd_clock_val_simp intro!: guard_consI)

lemma inv_N_urge_updI:
  assumes "u \<turnstile> inv (N p) l" "p < n_ps"
  shows "u(urge := d) \<turnstile> inv (N p) l"
  using assms urge_not_in_inv[of p] by (auto simp: clk_upd_clock_val_simp)

lemma inv_N_urge_upd_simp:
  assumes "p < n_ps"
  shows "u(urge := d) \<turnstile> inv (N p) l \<longleftrightarrow> u \<turnstile> inv (N p) l"
  using assms urge_not_in_inv[of p] by (auto simp: clk_upd_clock_val_simp)

lemma inv_N_urge_updD:
  assumes "u(urge := d) \<turnstile> inv (N p) l" "p < n_ps"
  shows "u \<turnstile> inv (N p) l"
  using assms urge_not_in_inv[of p] by (auto simp: clk_upd_clock_val_simp)

lemma inv_N_urgeD:
  assumes "u \<turnstile> inv (N_urge p) l" "p < n_ps"
  shows "u(urge := d) \<turnstile> inv (N p) l"
  using assms urge_not_in_inv[of p]
  by (auto simp: inv_N_urge inv_add_inv' clk_upd_clock_val_simp split: if_split_asm elim: guard_consE)

lemma inv_N_urge_urges:
  assumes "\<forall>p<n_ps. u(urge := 0) \<oplus> d \<turnstile> inv (N_urge p) (L ! p)" "is_urgent L"
  shows "d \<le> 0"
proof -
  from \<open>is_urgent L\<close> obtain p where "p < n_ps" "L ! p \<in> urgent (N p)"
    unfolding is_urgent_def by auto
  then have "acconstraint.LE urge 0 \<in> set (inv (N_urge p) (L ! p))"
    by (simp add: inv_N_urge inv_add_inv')
  with assms \<open>p < n_ps \<close> have "u(urge := 0) \<oplus> d \<turnstile>\<^sub>a acconstraint.LE urge 0"
    unfolding clock_val_def list_all_iff by auto
  then show ?thesis
    by (auto simp: cval_add_def)
qed

lemma trans_urge_upd_iff:
  assumes "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  shows "u(urge := d) \<turnstile> g \<longleftrightarrow> u \<turnstile> g"
  using assms urge_not_in_guards' by (auto simp: clk_upd_clock_val_simp)

lemma cval_add_0[simp]:
  "u \<oplus> (0 :: 'tt :: time) = u"
  unfolding cval_add_def by simp

lemma clock_val_reset_delay:
  "u(c := 0) \<oplus> (d :: 'tt :: time) = (u \<oplus> d)(c := d)"
  unfolding cval_add_def by auto

lemma clock_set_upd_simp:
  "[r \<rightarrow> d]u(c := d') = [r \<rightarrow> d]u" if "c \<in> set r"
  using that
  apply (induction r arbitrary: u)
   apply auto
  oops

lemma fun_upd_twist2:
  "f(a := x, b := x) = f(b := x, a := x)"
  by auto

lemma clock_set_upd_simp:
  "[c # r \<rightarrow> d]u(c := d') = [c # r \<rightarrow> d]u"
  apply (induction r arbitrary: u)
   apply simp
  apply simp
  apply (subst fun_upd_twist2)
  apply auto
  done

lemma clock_set_commute_single:
  "[r \<rightarrow> d]u(c := d') = ([r \<rightarrow> d]u)(c := d')" if "c \<notin> set r"
  using that by (induction r) auto

lemma clock_set_upd_simp2:
  "([xs @ c # ys \<rightarrow> d]u)(c := d') = ([xs @ ys \<rightarrow> d]u)(c := d')"
  apply (induction xs)
   apply (solves auto)
  apply (intro ext)
  subgoal for a xs x
    by (drule fun_cong[where x = x]) auto
  done

lemma clock_set_upd_simp3:
  "([xs \<rightarrow> d]u)(c := d') = ([filter (\<lambda>x. x \<noteq> c) xs \<rightarrow> d]u)(c := d')"
  apply (induction xs)
   apply (solves auto)
  apply (rule ext)
  apply (clarsimp, safe)
  apply clarsimp
  subgoal for xs x
    by (drule fun_cong[where x = x]) auto
  subgoal for a xs x
    by (drule fun_cong[where x = x]) auto
  done

interpretation urge: Prod_TA_sem A_urge .

lemma urge_n_ps_eq:
  "urge.n_ps = n_ps"
  unfolding urge.n_ps_def n_ps_def unfolding A_urge_def by simp

lemma urge_N_simp[simp]:
  "urge.N = N_urge"
  unfolding urge.N_def N_urge_def unfolding A_urge_def by simp

lemma urge_states_eq:
  "urge.states = states"
  unfolding states_def urge.states_def urge_n_ps_eq
  by (auto simp add: N_urge_trans_simp split: prod.splits)

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' A L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' A_urge L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = L \<and> s' = s \<and> u' = u(urge := 0)"
  "\<lambda>(L, s, u). L \<in> states" "\<lambda>(L, s, u). True"
proof -
  \<^cancel>\<open>case (1 L s u L' s' u')
  then show ?case\<close>
  have "A_urge \<turnstile> \<langle>L, s, u (urge := 0)\<rangle> \<rightarrow> \<langle>L', s', u'(urge := 0)\<rangle>"
    if steps: "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" "L \<in> states"
    for L :: "'s list"
      and s :: "'x \<Rightarrow> 'v option"
      and u :: "'c \<Rightarrow> 't"
      and L' :: "'s list"
      and s' :: "'x \<Rightarrow> 'v option"
      and u' :: "'c \<Rightarrow> 't"
    using that
  proof cases
    case steps: (1 L'' s'' u'' a)
    have *: "(u \<oplus> d)(urge := (u \<oplus> d) urge - u urge) = u(urge := 0) \<oplus> d" for d
      by (auto simp: cval_add_def)
    from steps(1) \<open>L \<in> states\<close> have "L'' \<in> states"
      by (rule states_inv)
    then have [simp]: "length L'' = n_ps"
      by (rule states_lengthD)
    from steps(1) have
      "A_urge \<turnstile> \<langle>L, s, u(urge := 0)\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L'', s'', u''(urge := u'' urge - u urge)\<rangle>"
      apply cases
      apply (subst A_urge_split)
      apply (subst (asm) A_split)
      apply (drule sym)
      apply simp
      unfolding TAG_def[of "''urgent''"]
      apply (simp add: is_urgent_simp *)
      apply (rule step_u.intros)
      apply tag
      apply simp
      subgoal
        by (cases "is_urgent L")
          (auto 4 3
            intro: inv_N_urge_updI inv_add_invI1 inv_add_invI2
            simp: inv_N_urge clock_val_reset_delay)
      by (tag, simp add: is_urgent_simp2)+
    moreover from steps(3,2) have
      "A_urge \<turnstile> \<langle>L'', s'', u''(urge := u'' urge - u urge)\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'(urge := 0)\<rangle>"
      apply (cases; subst A_urge_split; subst (asm) A_split)
         apply (all \<open>drule sym\<close>)
      subgoal delay
        by simp
      subgoal internal premises prems[tagged] for l b g a' f r l' N p B broadcast
        using prems apply tag usingT "''range''"
        apply simp
        apply (rule step_u.intros)
        preferT \<open>TRANS ''silent''\<close>
          apply (solves \<open>tag, simp, drule (1) trans_N_urgeD, subst nth_map, simp, simp\<close>)
        preferT \<open>''committed''\<close>
          apply (solves \<open>tag, subst nth_map, simp, simp add: committed_N_urge\<close>)
        preferT \<open>''bexp''\<close>
          apply (tag, assumption)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "''guard''" "TRANS _"; auto simp: trans_urge_upd_iff\<close>)
        preferT \<open>''new valuation''\<close>
          apply (tag, unfold clock_set.simps(2)[symmetric] clock_set_upd_simp, simp; fail)
        by (tag; auto intro: inv_N_urgeI)+
      subgoal binary premises prems[tagged]
        for a' broadcast' l1 b1 g1 f1 r1 l1' N' p l2 b2 g2 f2 r2 l2' q s'' B
        using prems apply tag
        usingT "RECV ''range''" "SEND ''range''"
        apply simp
        apply (rule step_u.intros)
        preferT \<open>''not broadcast''\<close>
          apply (tag; simp; fail)
        preferT \<open>TRANS ''in''\<close>
          apply (solves \<open>tag, simp, drule (1) trans_N_urgeD, subst nth_map, simp, simp\<close>)
        preferT \<open>TRANS ''out''\<close>
          apply (solves \<open>tag, simp, drule (1) trans_N_urgeD, subst nth_map, simp, simp\<close>)
        preferT \<open>''committed''\<close>
          apply (solves \<open>tag, subst nth_map, simp, simp add: committed_N_urge\<close>)
        preferT \<open>''bexp''\<close>
          apply (tag, assumption)
        preferT \<open>''bexp''\<close>
          apply (tag, assumption)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "''guard''" "TRANS _"; auto simp: trans_urge_upd_iff\<close>)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "''guard''" "TRANS _"; auto simp: trans_urge_upd_iff\<close>)
        preferT \<open>''new valuation''\<close>
          apply (solves \<open>tag, simp, unfold clock_set.simps(2)[symmetric] clock_set_upd_simp,
            simp add: clock_set_upd_simp2\<close>)
        by (solves \<open>tag; auto intro: inv_N_urgeI; simp\<close>)+
      subgoal broadcast premises prems[tagged]
        for a' broadcast' l b g f r l' N' p ps bs gs fs rs ls' s'' B
        using prems apply tag
        usingT "SEL ''range''" "SEND ''range''"
        apply (simp add: subset_nat_0_atLeastLessThan_conv)
        apply (rule step_u.intros)
        preferT \<open>''broadcast''\<close>
          apply (tag; simp; fail)
        preferT \<open>TRANS ''out''\<close>
          apply (solves \<open>tag, simp, drule (1) trans_N_urgeD, subst nth_map, simp, simp\<close>)
        preferT \<open>TRANS ''in''\<close>
          apply (solves \<open>tag, auto 4 3 dest: trans_N_urgeD\<close>)
        preferT \<open>''committed''\<close>
          apply (solves \<open>tag, subst nth_map, simp, simp add: committed_N_urge\<close>)
        preferT \<open>''bexp''\<close>
          apply (tag, assumption)
        preferT \<open>''bexp''\<close>
          apply (tag, assumption)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "''guard''" "TRANS _"; auto simp: trans_urge_upd_iff\<close>)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "''guard''" "TRANS _"; auto simp: trans_urge_upd_iff\<close>)
        preferT \<open>''maximal''\<close>
          apply (all \<open>tag; auto intro: inv_N_urgeI; fail | succeed\<close>)
        preferT \<open>''maximal''\<close>
          apply (solves \<open>tag; auto; erule (1) trans_N_urgeE, force simp: trans_urge_upd_iff\<close>)
        preferT \<open>''new valuation''\<close> subgoal
          apply tag
          apply clarsimp
          unfolding clock_set.simps(2)[symmetric] clock_set_upd_simp
          apply simp
          apply (subst (2) clock_set_upd_simp3)
          apply (subst clock_set_upd_simp3)
          apply (simp add: filter_concat comp_def)
          done
        done
      done
    ultimately show "A_urge \<turnstile> \<langle>L, s, u(urge := 0)\<rangle> \<rightarrow> \<langle>L', s', u'(urge := 0)\<rangle>"
      using \<open>a \<noteq> _\<close> by (intro step_u'.intros)
  qed
\<^cancel>\<open>next
  case (2 L s u L' s' u')\<close>
  moreover have "\<exists>ba. A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', ba\<rangle> \<and> u' = ba(urge := 0)"
    if "A_urge \<turnstile> \<langle>L, s, u (urge := 0)\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
      and "L \<in> states"
    for L :: "'s list"
      and s :: "'x \<Rightarrow> 'v option"
      and u :: "'c \<Rightarrow> 't"
      and L' :: "'s list"
      and s' :: "'x \<Rightarrow> 'v option"
      and u' :: "'c \<Rightarrow> 't"
    using that
  proof cases
    case steps: (1 L'' s'' u'' a)
    have *: "(u(urge := 0) \<oplus> d)(urge := (u(urge := 0) \<oplus> d) urge + u urge) = u \<oplus> d" for d
      unfolding cval_add_def by auto
    from steps(1) \<open>L \<in> states\<close> have "L'' \<in> states"
      by (rule urge.states_inv[unfolded urge_states_eq])
    then have [simp]: "length L'' = n_ps"
      by (rule states_lengthD)
    have 1: "([r\<rightarrow>0]u'') urge = 0" if "r = urge # xs" for r xs
      by (subst that) simp
    have 2: "filter (\<lambda>x. x \<noteq> urge) r = filter (\<lambda>x. x \<noteq> urge) (tl r)" if "r = urge # tl r" for r
      by (subst that) simp
    from steps(3,2) have "u' urge = 0"
      apply (cases; subst (asm) A_urge_split)
         apply (all \<open>drule sym\<close>)
         apply (simp; fail)
      subgoal delay
        by (tag- "''new valuation''" "TRANS _" "''range''")
           (solves \<open>auto elim!: trans_N_urgeE simp: 1\<close>)
      subgoal binary for a' broadcast' l1 b1 g1 f1 r1 l1' N p l2 b2 g2 f2 r2 l2' q s'' B
        by (tag- "''new valuation''" "TRANS _" "RECV ''range''")
          (auto elim!: trans_N_urgeE simp: 1[of _ "tl r1 @ r2"])
      subgoal broadcast for a' broadcast' l b g f r l' N p ps bs gs fs rs ls' s'a B
        by (tag- "''new valuation''" "TRANS _"  "SEND ''range''")
          (auto elim!: trans_N_urgeE simp: 1[of _ "tl r @ concat (map rs ps)"])
      done
    have **: "
      ([r\<rightarrow>0]u'')(urge := u'' urge + u urge) = ([tl r\<rightarrow>0]u'')(urge := u'' urge + u urge)"
      if "r = urge # tl r" for r
      by (subst that) simp
    from steps(1) have "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L'', s'', u''(urge := u'' urge + u urge)\<rangle>"
      apply cases
      apply (subst (asm) A_urge_split)
      apply (subst A_split)
      apply (drule sym)
      apply simp
      unfolding TAG_def[of "''urgent''"]
      apply (simp add: is_urgent_simp *)
      apply (rule step_u.intros)
      subgoal
        by tag (auto dest!: inv_add_invD inv_N_urge_updD simp: inv_N_urge clock_val_reset_delay)
        apply (tag, assumption)
       apply (tag- "''target invariant''" "''nonnegative''")
       apply (auto simp add: is_urgent_simp2 is_urgent_simp dest: inv_N_urge_urges)
      done
    moreover from steps(3,2) have
      "A \<turnstile> \<langle>L'', s'', u''(urge := u'' urge + u urge)\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'(urge := u'' urge + u urge)\<rangle>"
      apply (cases; subst (asm) A_urge_split; subst A_split)
         apply (all \<open>drule sym\<close>)
      subgoal delay
        by simp
      subgoal internal premises prems[tagged] for l b g a' f r l' N p B broadcast
        using prems apply del_tags
        usingT "''range''"
        apply simp
        apply (rule step_u.intros)
        preferT \<open>TRANS ''silent''\<close>
          apply (solves \<open>tag, simp, erule (1) trans_N_urgeE, subst nth_map, simp, simp\<close>)
        preferT \<open>''committed''\<close>
          apply (solves \<open>tag, subst nth_map, simp, simp add: committed_N_urge\<close>)
        preferT \<open>''bexp''\<close>
          apply (tag; assumption)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "TRANS _"; auto intro: trans_N_urgeE simp: trans_urge_upd_iff\<close>)
        preferT \<open>''target invariant''\<close>
          apply (all \<open>tag; auto intro: inv_N_urgeD; fail | succeed\<close>)
        preferT \<open>''new valuation''\<close>
          apply (solves \<open>tag "TRANS _", simp, erule (1) trans_N_urgeE,
            subst clock_set_commute_single, rule urge_not_in_resets', (simp add: **)+\<close>)
        done
      subgoal binary premises prems[tagged]
        for a' broadcast' l1 b1 g1 f1 r1 l1' Na p l2 b2 g2 f2 r2 l2' q s'' B
        using prems apply del_tags
        usingT "RECV ''range''" "SEND ''range''"
        apply simp
        apply (rule step_u.intros)
        preferT \<open>''not broadcast''\<close> apply (tag; simp; fail)
        preferT \<open>TRANS ''in''\<close>
          apply (solves \<open>tag, simp, erule (1) trans_N_urgeE, subst nth_map, simp, simp\<close>)
        preferT \<open>TRANS ''out''\<close>
          apply (solves \<open>tag, simp, erule (1) trans_N_urgeE, subst nth_map, simp, simp\<close>)
        preferT \<open>''committed''\<close>
          apply (solves \<open>tag, subst nth_map, simp, simp add: committed_N_urge\<close>)
        preferT \<open>''bexp''\<close>
          apply (tag; assumption)
        preferT \<open>''bexp''\<close>
          apply (tag; assumption)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "TRANS _"; auto intro: trans_N_urgeE simp: trans_urge_upd_iff\<close>)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "TRANS _"; auto intro: trans_N_urgeE simp: trans_urge_upd_iff\<close>)
        preferT \<open>''new valuation''\<close> subgoal premises prems[tagged]
          using prems apply tag
          apply (tag "TRANS _", simp, erule (1) trans_N_urgeE, erule (1) trans_N_urgeE)
          apply (subst clock_set_upd_simp3)
          apply (subst clock_set_commute_single)
           apply (simp; rule conjI; erule (1) urge_not_in_resets'; fail)
          apply (rule arg_cong)
          subgoal premises prems
            using urge_not_in_resets'[OF prems(7) \<open>p < n_ps\<close>]
                  urge_not_in_resets'[OF prems(9) \<open>q < n_ps\<close>]
            by (subst \<open>r1 = _\<close>, subst \<open>r2 = _\<close>, simp) (subst filter_True, auto)+
          done
        by (solves \<open>tag; auto intro: inv_N_urgeD\<close>)+
      subgoal broadcast premises prems[tagged]
        for a' broadcast' l b g f r l' N' p ps bs gs fs rs ls' s2 B
        using prems apply del_tags
        usingT "SEL ''range''" "SEND ''range''"
        apply (simp add: subset_nat_0_atLeastLessThan_conv)
        apply (rule step_u.intros)
        preferT \<open>TRANS ''out''\<close>
          \<comment> \<open>instantiates schematics\<close>
          apply (solves \<open>tag, simp, erule (1) trans_N_urgeE, subst nth_map, simp, simp\<close>)
        preferT \<open>TRANS ''in''\<close>
          apply (tag, auto 4 3 elim: trans_N_urgeE; fail) \<comment> \<open>instantiates schematics\<close>
        preferT \<open>''broadcast''\<close>
          apply (tag; simp; fail)
        preferT \<open>''committed''\<close>
          apply (solves \<open>tag, subst nth_map, simp, simp add: committed_N_urge\<close>)
        preferT \<open>''guard''\<close>
          apply (solves \<open>tag "TRANS _"; auto elim: trans_N_urgeE simp: trans_urge_upd_iff\<close>)
        preferT \<open>''guard''\<close> subgoal guards
          by (tag "TRANS _"; auto elim!: trans_N_urgeE simp: trans_urge_upd_iff)
        preferT \<open>''maximal''\<close> subgoal maximal
          by (tag, force simp: trans_urge_upd_iff dest: trans_N_urgeD)
        preferT \<open>''new valuation''\<close> subgoal new_valuation premises prems[tagged]
          apply (tag "TRANS _")
          using prems apply tag
          apply (subst [[get_tagged \<open>''new valuation''\<close>]])
          apply (subst clock_set_upd_simp3)
          apply (simp add: filter_concat comp_def)
          apply (subst clock_set_commute_single[symmetric], (simp; fail))
          apply (rule arg_cong)
          apply (fo_rule arg_cong2)
          subgoal
            by (auto simp: 2 urge_not_in_resets' filter_id_conv elim!: trans_N_urgeE)
          subgoal
            apply (fo_rule arg_cong)
            apply (fastforce elim: trans_N_urgeE simp: 2 urge_not_in_resets' filter_id_conv)+
            done
          done
        by (solves \<open>tag; auto intro: inv_N_urgeD\<close>)+
      done
    ultimately show ?thesis
      using \<open>a \<noteq> _\<close> \<open>u' urge = 0\<close> by  (intros add: step_u'.intros) auto
  qed
  moreover have "ab \<in> states"
    if "a \<in> states"
      and "A \<turnstile> \<langle>a, aa, b\<rangle> \<rightarrow> \<langle>ab, ac, ba\<rangle>"
    for a :: "'s list"
      and aa :: "'x \<Rightarrow> 'v option"
      and b :: "'c \<Rightarrow> 't"
      and ab :: "'s list"
      and ac :: "'x \<Rightarrow> 'v option"
      and ba :: "'c \<Rightarrow> 't"
    using that by (elim step_u'_elims states_inv)
  ultimately show
    "Bisimulation_Invariant
     (\<lambda>(L, s, u) (L', s', u').
         A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u').
         A_urge \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u').
         L' = L \<and> s' = s \<and> u' = u(urge := 0))
     (\<lambda>(L, s, u). L \<in> states) (\<lambda>(L, s, u). True)"
    by - (standard; clarsimp)
qed

lemmas urge_bisim = Bisimulation_Invariant_axioms

end (* Prod TA sem urge *)


context Simple_Network_Impl_Defs
begin

lemma dom_bounds: "dom bounds = fst ` set bounds'"
  unfolding bounds_def by (simp add: dom_map_of_conv_image_fst)

lemma mem_trans_N_iff:
  "t \<in> Simple_Network_Language.trans (N i) \<longleftrightarrow> t \<in> set (fst (snd (snd (automata ! i))))"
  if "i < n_ps"
  unfolding N_eq[OF that] by (auto split: prod.splits simp: automaton_of_def trans_def)

lemma length_automata_eq_n_ps:
  "length automata = n_ps"
  unfolding n_ps_def by simp

lemma N_p_trans_eq:
  "Simple_Network_Language.trans (N p) = set (fst (snd (snd (automata ! p))))" if "p < n_ps"
  using mem_trans_N_iff[OF that] by auto

lemma loc_set_compute:
  "loc_set = \<Union> ((\<lambda>(_, _, t, _). \<Union> ((\<lambda>(l, _, _, _, _, _, l'). {l, l'}) ` set t)) ` set automata)"
  unfolding loc_set_def setcompr_eq_image
  apply (safe; clarsimp simp: N_p_trans_eq n_ps_def)
     apply (drule nth_mem, erule bexI[rotated], force)+
   apply (drule mem_nth, force)+
  done

lemma var_set_compute:
  "var_set =
  (\<Union>S \<in> (\<lambda>t. (fst \<circ> snd) ` set t) ` ((\<lambda>(_, _, t, _). t) `  set automata). \<Union>b \<in> S. vars_of_bexp b) \<union>
  (\<Union>S \<in> (\<lambda>t. (fst \<circ> snd o snd \<circ> snd \<circ> snd) ` set t) ` ((\<lambda>(_, _, t, _). t) `  set automata).
    \<Union>f \<in> S. \<Union> (x, e) \<in> set f. {x} \<union> vars_of_exp e)"
  unfolding var_set_def setcompr_eq_image
  by (rule arg_cong2[where f = "(\<union>)"]; auto simp: N_p_trans_eq n_ps_def,
     (drule nth_mem, erule bexI[rotated],
      metis (no_types, lifting) insert_iff mem_case_prodI prod.collapse)+,
      (drule mem_nth, force)+)

lemma states_loc_setD:
  "set L \<subseteq> loc_set" if "L \<in> states"
  using states_loc_set that by auto

end (* Simple Network Impl Defs *)


context Simple_Network_Impl
begin

lemma sem_bounds_eq: "sem.bounds = bounds"
  unfolding sem.bounds_def bounds_def unfolding sem_def by simp

lemma n_ps_eq[simp]:
  "sem.n_ps = n_ps"
  unfolding n_ps_def sem.n_ps_def unfolding sem_def by auto

lemma sem_loc_set_eq:
  "sem.loc_set = loc_set"
  unfolding sem.loc_set_def loc_set_def n_ps_eq setcompr_eq_image
  apply (simp add: sem_N_eq N_eq)
  apply (rule arg_cong2[where f = "(\<union>)"])
  apply (safe; clarsimp;
      force split: prod.splits simp:  conv_automaton_def trans_def automaton_of_def n_ps_def)+
  done

lemma sem_states_eq:
  "sem.states = states"
  unfolding sem.states_def states_def n_ps_eq setcompr_eq_image
  by (clarsimp simp: sem_N_eq N_eq;
      force simp:  conv_automaton_def trans_def automaton_of_def n_ps_def split: prod.splits)+

end (* Simple Network Impl *)


locale Simple_Network_Rename_Defs =
  Simple_Network_Impl_Defs automata broadcast bounds' for automata ::
    "('s list \<times> 's list \<times> (('a :: countable) act, 's, 'c, 't, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, 't) cconstraint) list) list"
    and broadcast bounds' +
  fixes renum_acts   :: "'a \<Rightarrow> nat"
    and renum_vars   :: "'x \<Rightarrow> nat"
    and renum_clocks :: "'c \<Rightarrow> nat"
    and renum_states :: "nat \<Rightarrow> 's \<Rightarrow> nat"
begin

definition
  "map_cconstraint f g xs = map (map_acconstraint f g) xs"

definition
  "renum_cconstraint = map_cconstraint renum_clocks id"

definition
  "renum_act = map_act renum_acts"

definition
  "renum_bexp = map_bexp renum_vars"

definition
  "renum_exp = map_exp renum_vars"

definition
  "renum_upd = (\<lambda>(x, upd). (renum_vars x, renum_exp upd))"

abbreviation
  "renum_upds \<equiv> map renum_upd"

definition
  "renum_reset = map renum_clocks"

definition renum_automaton where
  "renum_automaton i \<equiv> \<lambda>(committed, urgent, trans, inv). let
    committed' = map (renum_states i) committed;
    urgent' = map (renum_states i) urgent;
    trans' = map (\<lambda>(l, b, g, a, upd, r, l').
      (renum_states i l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upds upd,
       renum_reset r,  renum_states i l')
    ) trans;
    inv' = map (\<lambda>(l, g). (renum_states i l, renum_cconstraint g)) inv
  in (committed', urgent', trans', inv')
"

definition
  "vars_inv \<equiv> the_inv renum_vars"

definition
  "map_st \<equiv> \<lambda>(L, s). (map_index renum_states L, s o vars_inv)"

definition
  "clocks_inv \<equiv> the_inv renum_clocks"

definition
  "map_u u = u o clocks_inv"

lemma map_u_add[simp]:
  "map_u (u \<oplus> d) = map_u u \<oplus> d"
  by (auto simp: map_u_def cval_add_def)

definition renum_label where
  "renum_label = map_label renum_acts"

sublocale renum: Simple_Network_Impl_Defs
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,p). (renum_vars a, p)) bounds'"
  .

lemma renum_n_ps_simp[simp]:
  "renum.n_ps = n_ps"
  unfolding n_ps_def renum.n_ps_def by simp

end (* Simple Network Rename Defs *)


locale Simple_Network_Rename_Defs_int =
  Simple_Network_Rename_Defs automata +
  Simple_Network_Impl automata
  for automata ::
    "('s list \<times> 's list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list"
begin

sublocale renum: Simple_Network_Impl
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,p). (renum_vars a, p)) bounds'"
  .

end (* Simple Network Rename Defs int *)

lemma
  fixes f :: "'b :: countable \<Rightarrow> nat"
  assumes "inj_on f S" "finite S" "infinite (UNIV :: 'b set)"
  shows extend_bij_inj: "inj (extend_bij f S)" and extend_bij_surj: "surj (extend_bij f S)"
    and extend_bij_extends: "\<forall>x \<in> S. extend_bij f S x = f x"
proof -
  have "infinite (\<nat> :: nat set)"
    unfolding Nats_def by simp
  from assms this have "bij (extend_bij f S)"
    by (intro extend_bij_bij) auto
  then show "inj (extend_bij f S)" and "surj (extend_bij f S)"
    unfolding bij_def by fast+
  from assms \<open>infinite \<nat>\<close> show "\<forall>x \<in> S. extend_bij f S x = f x"
    by (intro extend_bij_extends) auto
qed

lemma default_map_of_map:
  "default_map_of y (map (\<lambda>(a, b). (f a, g b)) xs) (f a) = g (default_map_of x xs a)"
  if "inj f" "y = g x"
  using that unfolding default_map_of_alt_def
  by (auto 4 4 dest: injD[OF that(1)] map_of_SomeD simp: map_of_eq_None_iff map_of_mapk_SomeI)

lemma default_map_of_map_2:
  "default_map_of y (map (\<lambda>(a, b). (a, g b)) xs) a = g (default_map_of x xs a)" if "y = g x"
  unfolding default_map_of_alt_def using that by (auto simp: map_of_map)

lemma map_of_map':
  "map_of (map (\<lambda>(k, v). (k, f k v)) xs)
  = (\<lambda>k. case map_of xs k of Some v \<Rightarrow> Some (f k v) | _ \<Rightarrow> None)"
  by (induct xs) (auto simp: fun_eq_iff)

lemma default_map_of_map_3:
  "default_map_of y (map (\<lambda>(a, b). (a, g a b)) xs) a = g a (default_map_of x xs a)"
  if "\<And>k. y = g k x"
  unfolding default_map_of_alt_def using that by (auto simp: map_of_map')

lemma dom_map_of_map:
  "dom (map_of (map (\<lambda> (a, b). (f a, g b)) xs)) = f ` fst ` set xs"
  unfolding dom_map_of_conv_image_fst by (auto 4 3)

lemma inj_image_eqI:
  "S = T" if "inj f" "f ` S = f ` T"
  using that by (meson inj_image_eq_iff)

lemmas [finite_intros] = finite_set

lemma map_of_NoneI:
  "map_of xs x = None" if "x \<notin> fst ` set xs"
  by (simp add: map_of_eq_None_iff that)

lemma bij_f_the_inv_f:
  "f (the_inv f x) = x" if "bij f"
  using that f_the_inv_f unfolding bij_def by (simp add: f_the_inv_f)


fun map_sexp ::
  "(nat \<Rightarrow> 's \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'a1) \<Rightarrow> ('b \<Rightarrow> 'b1) \<Rightarrow> (nat, 's, 'a, 'b) sexp
    \<Rightarrow> (nat, 's1, 'a1, 'b1) sexp"
  where
  "map_sexp _ _ _ sexp.true = sexp.true" |
  "map_sexp f g h (not e) = not (map_sexp f g h e)" |
  "map_sexp f g h (and e1 e2) = and (map_sexp f g h e1) (map_sexp f g h e2)" |
  "map_sexp f g h (sexp.or e1 e2) = sexp.or (map_sexp f g h e1) (map_sexp f g h e2)" |
  "map_sexp f g h (imply e1 e2) = imply (map_sexp f g h e1) (map_sexp f g h e2)" |
  "map_sexp f g h (eq i x) = eq (g i) (h x)" |
  "map_sexp f g h (lt i x) = lt (g i) (h x)" |
  "map_sexp f g h (le i x) = le (g i) (h x)" |
  "map_sexp f g h (ge i x) = ge (g i) (h x)" |
  "map_sexp f g h (gt i x) = gt (g i) (h x)" |
  "map_sexp f g h (loc i x) = loc i (f i x)"

fun map_formula ::
  "(nat \<Rightarrow> 's \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'a1) \<Rightarrow> ('b \<Rightarrow> 'b1)
  \<Rightarrow> (nat, 's, 'a, 'b) formula \<Rightarrow> (nat, 's1, 'a1, 'b1) formula"
where
  "map_formula f g h (formula.EX \<phi>) = formula.EX (map_sexp f g h \<phi>)" |
  "map_formula f g h (EG \<phi>) = EG (map_sexp f g h \<phi>)" |
  "map_formula f g h (AX \<phi>) = AX (map_sexp f g h \<phi>)" |
  "map_formula f g h (AG \<phi>) = AG (map_sexp f g h \<phi>)" |
  "map_formula f g h (Leadsto \<phi> \<psi>) = Leadsto (map_sexp f g h \<phi>) (map_sexp f g h \<psi>)"


locale Simple_Network_Impl_real =
  fixes automata ::
    "('s list \<times> 's list \<times> ('a act, 's, 'c, real, 'x, int) transition list
      \<times> ('s \<times> ('c, real) cconstraint) list) list"
    and broadcast :: "'a list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
begin

sublocale Simple_Network_Impl_Defs automata broadcast bounds' .

abbreviation "sem \<equiv> (set broadcast, map automaton_of automata, map_of bounds')"

sublocale Prod_TA_sem "(set broadcast, map automaton_of automata, map_of bounds')" .

end

context Simple_Network_Impl
begin

lemma sem_state_guard_eq:
  "(fst \<circ> snd) ` trans (sem.N p) = (fst \<circ> snd) ` trans (N p)" if "p < n_ps"
  unfolding sem_N_eq[OF \<open>p < n_ps\<close>] N_eq[OF \<open>p < n_ps\<close>]
  unfolding automaton_of_def conv_automaton_def trans_def
  by (force split: prod.splits)

lemma sem_state_update_eq:
  "(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (sem.N p) = (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p)"
  if "p < n_ps"
  unfolding sem_N_eq[OF \<open>p < n_ps\<close>] N_eq[OF \<open>p < n_ps\<close>]
  unfolding automaton_of_def conv_automaton_def trans_def
  by (force split: prod.splits)

lemma sem_var_set_eq:
  "sem.var_set = var_set"
  unfolding sem.var_set_def var_set_def n_ps_eq using sem_state_guard_eq sem_state_update_eq
  by (simp cong: image_cong_simp add: setcompr_eq_image)

end

locale Simple_Network_Rename_Defs_real =
  Simple_Network_Rename_Defs automata +
  Simple_Network_Impl_real automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, real, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, real) cconstraint) list) list"
begin

sublocale renum: Simple_Network_Impl_real
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,p). (renum_vars a, p)) bounds'"
  .

end (* Simple Network Rename Defs *)

locale Simple_Network_Rename' =
  Simple_Network_Rename_Defs where automata = automata for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, 't, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, 't) cconstraint) list) list" +
  assumes bij_renum_clocks: "bij renum_clocks"
      and renum_states_inj: "\<forall>p<n_ps. inj (renum_states p)"
      and bij_renum_vars: "bij renum_vars"
      and bounds'_var_set: "fst ` set bounds' = var_set"
      and inj_renum_acts: "inj renum_acts"

locale Simple_Network_Rename_real =
  Simple_Network_Rename_Defs_real where automata = automata +
  Simple_Network_Rename' where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, real, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, real) cconstraint) list) list" +
  assumes urgency_removed: "\<forall>i < n_ps. urgent (N i) = {}"
begin

lemma aux_1:
  "(\<lambda>x. case case x of
          (l, g) \<Rightarrow> (renum_states p l, renum_cconstraint g) of
     (s, cc) \<Rightarrow> (s, map conv_ac cc))
  = (\<lambda> (l, g). (renum_states p l, map conv_ac (renum_cconstraint g)))
"
  by auto

lemma clocks_inv_inv:
  "clocks_inv (renum_clocks a) = a"
  unfolding clocks_inv_def by (subst the_inv_f_f; rule bij_renum_clocks[THEN bij_is_inj] HOL.refl)

lemma map_u_renum_cconstraint_clock_valI:
  "map_u u \<turnstile> renum_cconstraint cc" if "u \<turnstile> cc"
  using that
  unfolding clock_val_def list_all_length
  unfolding renum_cconstraint_def map_cconstraint_def
  unfolding map_u_def
  apply clarsimp
  subgoal for n
    by (cases "cc ! n") (auto 4 4 simp: clocks_inv_inv split: acconstraint.split)
  done

lemma map_u_renum_cconstraint_clock_valD:
  "u \<turnstile> cc" if "map_u u \<turnstile> renum_cconstraint cc"
  using that
  unfolding clock_val_def list_all_length
  unfolding renum_cconstraint_def map_cconstraint_def
  unfolding map_u_def
  apply clarsimp
  subgoal for n
    by (cases "cc ! n") (auto 4 4 simp: clocks_inv_inv split: acconstraint.split)
  done

lemma inj_renum_states: "inj (renum_states p)" if "p < n_ps"
  using renum_states_inj \<open>p < n_ps\<close> by blast

lemma inv_renum_sem_I:
  assumes
    "u \<turnstile> Simple_Network_Language.inv (N p) l" "p < n_ps" "l \<in> loc_set"
  shows
    "map_u u \<turnstile> Simple_Network_Language.inv (renum.N p) (renum_states p l)"
  using assms
  unfolding inv_def
  apply -
  apply (subst (asm) N_eq, assumption)
  apply (subst renum.N_eq, subst renum_n_ps_simp, assumption)
  apply (subst nth_map_index, simp add: n_ps_def)
  unfolding conv_automaton_def automaton_of_def
  apply (clarsimp split: prod.split_asm simp: renum_automaton_def comp_def)
  unfolding aux_1
  apply (subst default_map_of_map[where x = "[]"])
  subgoal
    by (intro inj_renum_states \<open>p < n_ps\<close>)
   apply (simp add: renum_cconstraint_def map_cconstraint_def; fail)
  apply (erule map_u_renum_cconstraint_clock_valI)
  done

lemma inv_renum_sem_D:
  assumes
    "map_u u \<turnstile> Simple_Network_Language.inv (renum.N p) (renum_states p l)" "p < n_ps" "l \<in> loc_set"
  shows
    "u \<turnstile> Simple_Network_Language.inv (N p) l"
  using assms
  unfolding inv_def
  apply -
  apply (subst N_eq, assumption)
  apply (subst (asm) renum.N_eq, subst renum_n_ps_simp, assumption)
  apply (subst (asm) nth_map_index, simp add: n_ps_def)
  unfolding conv_automaton_def automaton_of_def
  apply (clarsimp split: prod.split simp: renum_automaton_def comp_def)
  unfolding aux_1
  apply (subst (asm) default_map_of_map[where x = "[]"])
  subgoal
    by (intro inj_renum_states \<open>p < n_ps\<close>)
   apply (simp add: renum_cconstraint_def map_cconstraint_def; fail)
  apply (erule map_u_renum_cconstraint_clock_valD)
  done

lemma dom_the_inv_comp:
  "dom (m o the_inv f) = f ` dom m" if "inj f" "range f = UNIV"
  unfolding dom_def
  apply (clarsimp, safe)
  subgoal for x y
    apply (subgoal_tac "f (the_inv f x) = x")
     apply force
    using that by (auto intro: f_the_inv_f)
  subgoal for x y
    using that by (auto simp: the_inv_f_f)
  done

lemma inj_renum_vars:
  "inj renum_vars"
  using bij_renum_vars unfolding bij_def ..

lemma surj_renum_vars:
  "surj renum_vars"
  using bij_renum_vars unfolding bij_def ..

lemma map_of_inv_map:
  "map_of xs (the_inv f x) = map_of (map (\<lambda> (a, b). (f a, b)) xs) x"
  if "inj f" "surj f" "the_inv f x \<in> dom (map_of xs)"
  apply (subgoal_tac "x = f (the_inv f x)")
  subgoal premises prems
    using domD[OF that(3)] \<open>inj f\<close>
    apply (subst (2) prems)
    apply safe
    apply (subst map_of_mapk_SomeI; assumption)
    done
  subgoal
    apply (rule sym, rule f_the_inv_f)
    using that by auto
  done

lemma dom_vars_invD:
  assumes "x \<in> dom (s \<circ> vars_inv)"
  shows "x \<in> renum_vars ` dom s" (is ?A) and "the_inv renum_vars x \<in> dom s" (is ?B)
proof -
  show ?A
    using assms unfolding vars_inv_def dom_the_inv_comp[OF inj_renum_vars surj_renum_vars] .
  then show ?B
    apply (elim imageE)
    apply simp
    apply (subst the_inv_f_f, rule inj_renum_vars, assumption)
    done
qed

lemma bounded_renumI:
  assumes "bounded (map_of bounds') s"
  shows "bounded (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds')) (s o vars_inv)"
  using assms unfolding bounded_def
  apply elims
  apply intros
  subgoal
    unfolding dom_map_of_conv_image_fst vars_inv_def
    by (auto intro!: image_cong simp: dom_the_inv_comp[OF inj_renum_vars surj_renum_vars] image_comp)
  subgoal for x
    apply (frule dom_vars_invD)
    apply (frule dom_vars_invD(2))
    apply (drule bspec, assumption)
    apply (auto simp: map_of_inv_map[OF inj_renum_vars surj_renum_vars] vars_inv_def)
    done
  subgoal for x
    apply (frule dom_vars_invD)
    apply (frule dom_vars_invD(2))
    apply (drule bspec, assumption)
    apply (auto simp: map_of_inv_map[OF inj_renum_vars surj_renum_vars] vars_inv_def)
    done
  done

lemma map_of_renum_vars_simp:
  assumes
    "dom (s o vars_inv)
     = dom (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds'))"
    "x \<in> dom s" "dom s \<subseteq> var_set"
  shows "map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds') (renum_vars x) = map_of bounds' x"
proof -
  have *:
    "map (\<lambda>(a, y). (renum_vars a, y)) bounds' = map (\<lambda>(a, y). (renum_vars a, y)) bounds'"
    by auto
  have "x \<in> dom (map_of bounds')"
    unfolding dom_map_of_conv_image_fst
    using assms
    unfolding vars_inv_def
    apply -
    apply (subst (asm) dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
    apply (subst (asm) dom_map_of_map)
    apply clarsimp
    apply (subst (asm) inj_on_image_eq_iff[OF inj_renum_vars])
    by auto
  then obtain y where "map_of bounds' x = Some y"
    by auto
  then show ?thesis
    by (subst map_of_mapk_SomeI) (auto intro: inj_renum_vars)
qed

lemma bounded_renumD:
  assumes
    "Simple_Network_Language.bounded
     (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds')) (s o vars_inv)"
    and "dom s \<subseteq> var_set"
  shows "Simple_Network_Language.bounded (map_of bounds') s"
proof -
  show ?thesis
    using assms(1)
    unfolding bounded_def
    apply elims
    apply intros
    subgoal
      unfolding vars_inv_def
      apply (subst (asm) dom_the_inv_comp[OF inj_renum_vars surj_renum_vars])
      apply (subst (asm) dom_map_of_map)
      apply (rule inj_image_eqI[OF inj_renum_vars], simp add: dom_map_of_conv_image_fst)
      done
    subgoal for x
      using assms(2) unfolding vars_inv_def
      apply (subst (asm) (2) dom_the_inv_comp[OF inj_renum_vars surj_renum_vars])
      apply (drule bspec, erule imageI)
      apply (simp add: the_inv_f_f[OF inj_renum_vars] map_of_renum_vars_simp[unfolded vars_inv_def])
      done
    subgoal for x
      using assms(2) unfolding vars_inv_def
      apply (subst (asm) (2) dom_the_inv_comp[OF inj_renum_vars surj_renum_vars])
      apply (drule bspec, erule imageI)
      apply (simp add: the_inv_f_f[OF inj_renum_vars] map_of_renum_vars_simp[unfolded vars_inv_def])
      done
    done
qed

lemma dom_bounds_var_set: "dom bounds = var_set"
  unfolding dom_bounds using bounds'_var_set .

lemma sem_states_loc_setD: "L ! p \<in> loc_set" if "p < length automata" "L \<in> states" for L p
  using that states_loc_set by (force simp: n_ps_def)

lemma trans_N_renumD:
  assumes "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  shows "(renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upds f, renum_reset r, renum_states p l')
  \<in> Simple_Network_Language.trans (renum.N p)"
  using assms
  unfolding mem_trans_N_iff[OF assms(2)] renum.mem_trans_N_iff[unfolded renum_n_ps_simp, OF assms(2)]
  by (force split: prod.split simp: renum_automaton_def n_ps_def)

lemma match_assumption2:
  assumes "P a1 b1" "a1 = a" "b1 = b" shows "P a b"
  using assms by auto

lemma inj_pair:
  assumes "inj f" "inj g"
  shows "inj (\<lambda>(a, b). (f a, g b))"
  using assms unfolding inj_on_def by auto

lemma injective_functions:
  "inj renum_reset" "inj renum_upd" "inj renum_act" "inj renum_cconstraint" "inj renum_bexp"
  "\<And>p. p < length automata \<Longrightarrow> inj (renum_states p)"
  subgoal
    unfolding renum_reset_def using bij_renum_clocks[THEN bij_is_inj] by simp
  subgoal
    unfolding renum_upd_def renum_exp_def using bij_renum_vars[THEN bij_is_inj]
    by (intro inj_pair exp.inj_map inj_mapI)
  subgoal
    unfolding renum_act_def using inj_renum_acts by (rule act.inj_map)
  subgoal
    unfolding renum_cconstraint_def map_cconstraint_def
    by (intro inj_mapI acconstraint.inj_map bij_renum_clocks bij_is_inj bij_id)
  subgoal
    unfolding renum_bexp_def by (intro bexp.inj_map inj_renum_vars)
  subgoal
    by (rule inj_renum_states, simp add: n_ps_def)
  done

lemma trans_N_renumI:
  assumes "(
    renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upds f, renum_reset r,
    renum_states p l')
  \<in> trans (renum.N p)"  "p < n_ps"
  shows "(l, b, g, a, f, r, l') \<in> trans (N p)"
  using assms
  unfolding mem_trans_N_iff[OF assms(2)] renum.mem_trans_N_iff[unfolded renum_n_ps_simp, OF assms(2)]
  apply (clarsimp split: prod.split_asm simp: renum_automaton_def n_ps_def)
  apply (fo_rule match_assumption2, assumption)
   apply (auto elim!: injD[rotated, THEN sym] intro: injective_functions)
  done

lemma renum_acconstraint_eq_convD:
  assumes "map_acconstraint renum_clocks id g = conv_ac g'"
  obtains g1 where "g = conv_ac g1" "g' = map_acconstraint renum_clocks id g1"
  subgoal premises
    using assms
    apply (cases g'; cases g; clarsimp)
    subgoal for m c
      by (rule that[of "acconstraint.LT c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.LE c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.EQ c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.GT c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.GE c m"]; simp)
    done
  done

lemma renum_cconstraint_eq_convD:
  assumes "renum_cconstraint g = conv_cc g'"
  obtains g1 where "g = conv_cc g1" "g' = renum_cconstraint g1"
proof -
  let ?f = "\<lambda>(ac, ac'). SOME ac1. ac = conv_ac ac1 \<and> ac' = map_acconstraint renum_clocks id ac1"
  let ?g = "map ?f (zip g g')"
  from assms have "length g = length g'"
    unfolding renum_cconstraint_def map_cconstraint_def by -(drule arg_cong[where f = length], simp)
  then have "g = conv_cc ?g \<and> g' = renum_cconstraint ?g"
    using assms
    by (simp add: comp_def renum_cconstraint_def map_cconstraint_def)
       (induction rule: list_induct2; simp; elim conjE renum_acconstraint_eq_convD; smt someI)
  then show ?thesis
    by (blast intro: that)
qed

lemma trans_sem_N_renumI:
  assumes "(
  renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upds f, renum_reset r,
  renum_states p l')
  \<in> trans (renum.N p)" "p < n_ps"
  shows "(l, b, g, a, f, r, l') \<in> trans (N p)"
  using assms(1) \<open>p < n_ps\<close> by (simp add: trans_N_renumI)

lemma trans_sem_N_renumI':
  assumes "(renum_states p l, b, g, a, f, r, l') \<in> trans (renum.N p)" "p < n_ps"
  shows "\<exists> b' g' a' f' r' l1.
    TRANS ''orig'' \<bbar> (l, b', g', a', f', r', l1) \<in> Simple_Network_Language.trans (N p)
    \<and> ''renum bexp''   \<bbar> b = renum_bexp b'  \<and> ''renum guard'' \<bbar> g = renum_cconstraint g'
    \<and> ''renum action'' \<bbar> a = renum_act a'   \<and> ''renum upds''  \<bbar> f = renum_upds f'
    \<and> ''renum reset''  \<bbar> r = renum_reset r' \<and> ''renum loc''   \<bbar> l' = renum_states p l1"
proof -
  obtain b' g' a' f' r' l1 where "b = renum_bexp b'" "g = renum_cconstraint g'" "f = renum_upds f'"
    "a = renum_act a'" "r = renum_reset r'" "l' = renum_states p l1"
    using assms
    unfolding N_eq[OF assms(2)] renum.N_eq[unfolded renum_n_ps_simp, OF assms(2)]
    apply (subst (asm) nth_map_index)
    subgoal
      by (simp add: n_ps_def)
    unfolding renum_automaton_def automaton_of_def trans_def by (auto split: prod.split_asm)
  with assms show ?thesis
    by untag (fastforce dest!: trans_sem_N_renumI)
qed

lemma committed_renum_eq:
  "committed (renum.N p) = renum_states p ` committed (N p)" if "p < n_ps"
  unfolding
    committed_def N_eq[OF \<open>p < n_ps\<close>] renum.N_eq[unfolded renum_n_ps_simp, OF \<open>p < n_ps\<close>]
  apply (subst nth_map_index)
  subgoal
    using \<open>p < n_ps\<close> by (simp add: n_ps_def)
  unfolding automaton_of_def conv_automaton_def renum_automaton_def by (simp split: prod.split)

lemma urgent_renum_eq:
  "urgent (renum.N p) = renum_states p ` urgent (N p)" if "p < n_ps"
  unfolding
    urgent_def N_eq[OF \<open>p < n_ps\<close>] renum.N_eq[unfolded renum_n_ps_simp, OF \<open>p < n_ps\<close>]
  apply (subst nth_map_index)
  subgoal
    using \<open>p < n_ps\<close> by (simp add: n_ps_def)
  unfolding automaton_of_def conv_automaton_def renum_automaton_def by (simp split: prod.split)

lemma renum_urgency_removed:
  "\<forall>i < n_ps. urgent (renum.N i) = {}"
  using urgency_removed
  apply intros
  apply (simp only: urgent_renum_eq)
  apply simp
  done

lemma check_bexp_renumD:
  "check_bexp s b bv \<Longrightarrow> check_bexp (s o vars_inv) (renum_bexp b) bv"
and is_val_renumD:
  "is_val s e v \<Longrightarrow> is_val (s o vars_inv) (renum_exp e) v"
   apply (induction rule: check_bexp_is_val.inducts)
   apply (solves \<open>
    auto
      intro: check_bexp_is_val.intros
      simp: renum_bexp_def renum_exp_def vars_inv_def the_inv_f_f[OF inj_renum_vars]
  \<close>)+
  subgoal
    apply (clarsimp simp: renum_bexp_def renum_exp_def vars_inv_def, safe)
    using is_val.simps apply fastforce+
    done
  apply (auto intro: check_bexp_is_val.intros simp: renum_exp_def)
  done

method solve_case =
  auto 
    intro: check_bexp_is_val.intros
    simp: renum_bexp_def renum_exp_def vars_inv_def the_inv_f_f[OF inj_renum_vars];
  fail
| use is_val.simps in fastforce

lemma check_bexp_renumI:
  "check_bexp (s o vars_inv) (renum_bexp b) bv \<Longrightarrow> check_bexp s b bv"
  and is_val_renumI:
  "is_val (s o vars_inv) (renum_exp e) v \<Longrightarrow> is_val s e v"
  apply (induction
      "s o vars_inv" "renum_bexp b" bv and "s o vars_inv" "renum_exp e" _
      arbitrary: b and e rule: check_bexp_is_val.inducts)
  subgoal for b
    by (cases b; solve_case)
  subgoal for e bv b
    by (cases b; solve_case)
  subgoal for e1 a e2 bv b
    by (cases b; solve_case)
  subgoal for e1 a e2 bv b
    by (cases b; solve_case)
  subgoal for e1 a e2 bv b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for c e
    by (cases e; solve_case)
  subgoal for x v e
    by (cases e; solve_case)
  subgoal for e1 v1 e2 v2 b bv e
    by (clarsimp simp: renum_bexp_def renum_exp_def; safe; cases e; solve_case)
  subgoal for e1 v1 e2 v2 f e
    by (clarsimp simp: renum_bexp_def renum_exp_def; cases e; solve_case)
  subgoal for e1 v f e
    by (cases e; solve_case)
  done

lemma renum_reset_map_u:
  "[renum_reset r\<rightarrow>0]map_u u = map_u ([r\<rightarrow>0]u)"
  unfolding map_u_def
  apply (rule ext)
  subgoal for x
    apply (cases "clocks_inv x \<in> set r"; simp add: clocks_inv_def)
    subgoal
      using bij_renum_clocks[THEN bij_is_surj]
      by (auto
            simp: renum_reset_def f_the_inv_f[OF bij_is_inj, OF bij_renum_clocks]
            dest: imageI[where f = renum_clocks]
         )
    subgoal
      by (subst clock_set_id)
         (auto simp: renum_reset_def the_inv_f_f[OF bij_is_inj, OF bij_renum_clocks])
    done
  done

lemma bounded_renumI':
  assumes "bounded bounds s'"
  shows "bounded renum.bounds (s' o vars_inv)"
  using assms unfolding renum.bounds_def bounds_def by (simp add: bounded_renumI)

lemma bounded_renumD':
  assumes "bounded renum.bounds (s' o vars_inv)" "dom s' \<subseteq> var_set"
  shows "bounded bounds s'"
  using assms unfolding renum.bounds_def bounds_def by (simp add: bounded_renumD)

lemma is_upd_renumD:
  assumes "is_upd s f s'"
  shows "is_upd (s o vars_inv) (renum_upd f) (s' o vars_inv)"
  using assms
  unfolding is_upd_def renum_upd_def
  by (force dest!: is_val_renumD
            simp: bij_f_the_inv_f[OF bij_renum_vars] the_inv_f_f[OF inj_renum_vars] vars_inv_def)

lemma is_upds_renumD:
  assumes "is_upds s1 ps s'"
  shows "is_upds (s1 o vars_inv) (renum_upds ps) (s' o vars_inv)"
  using assms by induction (auto intro: is_upds.intros simp: comp_def dest!: is_upd_renumD)

lemma is_upds_concat_renumD:
  assumes "is_upds s1 (concat ps) s'"
  shows "is_upds (s1 o vars_inv) (concat_map renum_upds ps) (s' o vars_inv)"
  using assms by (induction ps arbitrary: s1) (auto simp: comp_def map_concat dest!: is_upds_renumD)

lemma Ball_mono:
  assumes "\<forall>x \<in> S. P x" "\<And>x. x \<in> S \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "\<forall>x \<in> S. Q x"
  using assms by blast

lemma atLeastLessThan_upperD:
  assumes "S \<subseteq> {l..<u}" "x \<in> S"
  shows "x < u"
  using assms by auto

lemma imp_mono_rule:
  assumes "P1 \<longrightarrow> P2"
    and "Q1 \<Longrightarrow> P1"
    and "Q1 \<Longrightarrow> P2 \<Longrightarrow> Q2"
  shows "Q1 \<longrightarrow> Q2"
  using assms by blast

lemma inj_id:
  "inj id"
  by auto

lemma step_single_renumD:
  assumes "step_u sem L s u a L' s' u'" "L \<in> states" "dom s \<subseteq> var_set"
  shows "step_u renum.sem
    (map_index renum_states L) (s o vars_inv) (map_u u)
    (renum_label a)
    (map_index renum_states L') (s' o vars_inv) (map_u u')"
  using assms(1-3)
  apply (cases a)

     supply [simp del] = map_map_index set_map
     \<comment> \<open>To keep the simplifier from breaking through locale abstractions\<close>

  \<comment> \<open>Delay\<close>
  subgoal
    supply [simp] = length_automata_eq_n_ps L_len
    apply (subst (asm) A_split)
    apply (subst renum.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp)
    apply (erule step_u_elims')
    apply simp
    apply (rule step_u.intros)
    preferT \<open>''target invariant''\<close> subgoal
      by tag (auto 4 3 simp: dest: inv_renum_sem_I[OF _ _ sem_states_loc_setD])
    preferT \<open>''nonnegative''\<close> subgoal
      by assumption
    preferT \<open>''urgent''\<close> subgoal
      using renum_urgency_removed by - (tag, auto)
    preferT \<open>''bounded''\<close> subgoal
      by tag (rule bounded_renumI')
    done

  \<comment> \<open>Internal\<close>
  subgoal for a'
    supply [simp] = length_automata_eq_n_ps L_len
    apply (subst (asm) A_split)
    apply (subst renum.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp)
    apply (erule step_u_elims')
    unfolding TAG_def[of "''range''"]
    apply simp
    apply (rule step_u.intros)
    preferT \<open>TRANS ''silent''\<close>
      apply (solves \<open>tag, drule (1) trans_N_renumD, subst nth_map, (simp add: renum_act_def)+\<close>)
    preferT \<open>''committed''\<close> subgoal
      by tag (auto simp: committed_renum_eq dest!: inj_renum_states[THEN injD, rotated])
    preferT \<open>''bexp''\<close> subgoal
      by tag (erule check_bexp_renumD)
    preferT \<open>''guard''\<close> subgoal
      by tag (rule map_u_renum_cconstraint_clock_valI)
    preferT \<open>''target invariant''\<close> subgoal
      apply (tag- "''new loc''" "TRANS ''silent''")
      apply clarsimp
      apply (rule inv_renum_sem_I[OF _ _ sem_states_loc_setD[OF _ state_preservation_updI]])
          apply fastforce+
      done
    preferT \<open>''loc''\<close>
      apply (tag, simp; fail)
    preferT \<open>''range''\<close>
      apply (tag, simp; fail)
    preferT \<open>''new loc''\<close>
      apply (tag, simp only: map_index_update; fail)
    preferT \<open>''new valuation''\<close>
      apply (tag, simp only: renum_reset_map_u; fail)
    preferT \<open>''is_upd''\<close> subgoal
      by (tag, erule is_upds_renumD)
    preferT \<open>''bounded''\<close>
      apply (tag, erule bounded_renumI'; fail)
    done

  \<comment> \<open>Binary\<close>
  subgoal for a'
    supply [simp] = length_automata_eq_n_ps L_len
    apply (subst (asm) A_split)
    apply (subst renum.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp)
    apply (erule step_u_elims')
    unfolding TAG_def[of "RECV ''range''"] TAG_def[of "SEND ''range''"]
    apply simp
    apply (rule step_u.intros)
    preferT \<open>''not broadcast''\<close> subgoal
      apply tag
      unfolding renum.broadcast_def
      apply (clarsimp simp: set_map)
      apply (drule injD[OF inj_renum_acts])
      apply (subst (asm) broadcast_def, simp)
      done
    preferT \<open>TRANS ''in''\<close>
      apply (solves \<open>tag, drule (1) trans_N_renumD, subst nth_map, (simp add: renum_act_def)+\<close>)
    preferT \<open>TRANS ''out''\<close>
      apply (solves \<open>tag, drule (1) trans_N_renumD, subst nth_map, (simp add: renum_act_def)+\<close>)
    preferT \<open>''committed''\<close> subgoal
      by tag (auto simp: committed_renum_eq dest!: inj_renum_states[THEN injD, rotated])

    preferT \<open>''bexp''\<close> subgoal
      by tag (erule check_bexp_renumD)

    preferT \<open>''bexp''\<close> subgoal
      by tag (erule check_bexp_renumD)

    preferT \<open>''guard''\<close> subgoal
      by tag (rule map_u_renum_cconstraint_clock_valI)

    preferT \<open>''guard''\<close> subgoal
      by tag (rule map_u_renum_cconstraint_clock_valI)

    preferT \<open>''target invariant''\<close> subgoal
      apply (tag- "''new loc''" "TRANS _")
      apply clarsimp
      apply (rule inv_renum_sem_I[OF _ _ sem_states_loc_setD[OF _ state_preservation_updI]])
          apply (fastforce intro!: state_preservation_updI)+
      done
    preferT \<open>''new loc''\<close>
      apply (tag, simp add: map_index_update; fail)
    preferT \<open>''new valuation''\<close>
      apply (tag, simp add: renum_reset_map_u[symmetric] renum_reset_def; fail)
    preferT \<open>''upd''\<close>
      apply (tag, erule is_upds_renumD; fail)
    preferT \<open>''upd''\<close>
      apply (tag, erule is_upds_renumD; fail)
    preferT \<open>''bounded''\<close>
      apply (tag, erule bounded_renumI'; fail)
    apply (tag, simp; fail)+
    done

  \<comment> \<open>Broadcast\<close>
  subgoal for a'
    supply [simp] = length_automata_eq_n_ps L_len
    apply (subst (asm) A_split)
    apply (subst renum.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp)
    apply (erule step_u_elims')
    apply simp
    unfolding TAG_def[of "SEND ''range''"]

    apply (rule step_u.intros)

    preferT \<open>''broadcast''\<close> subgoal
      unfolding renum.broadcast_def by (tag, subst (asm) broadcast_def, simp add: set_map)

    preferT \<open>TRANS ''out''\<close>
    apply (solves\<open>tag, simp, drule (1) trans_N_renumD, subst nth_map, (simp add: renum_act_def)+\<close>)

    preferT \<open>TRANS ''in''\<close>
      apply (tag- "SEL _")
      apply (solves \<open>auto dest!: trans_N_renumD simp add: renum_act_def atLeastLessThan_upperD\<close>)

    preferT \<open>''committed''\<close> subgoal
      apply (tag- "SEL _")
      apply (simp add: committed_renum_eq)
      apply (erule disj_mono[rule_format, rotated 2], (simp; fail))
      apply (erule disj_mono[rule_format, rotated 2])
      subgoal
        apply clarify
        apply (rule rev_bexI, assumption)
        apply (auto simp: committed_renum_eq)
        done
      apply (auto simp: committed_renum_eq dest!: inj_renum_states[THEN injD, rotated]; fail)
      done

    preferT \<open>''maximal''\<close> subgoal
      apply tag
      apply simp
      apply (erule all_mono[THEN mp, OF impI, rotated])
      apply (erule (1) imp_mono_rule)
      apply (erule (1) imp_mono_rule)
      apply clarify
      apply (drule trans_sem_N_renumI', assumption)
      apply (untag, clarsimp simp: renum_act_def)
      apply (drule check_bexp_renumI)
      apply (drule InD2[OF inj_renum_acts])
      apply (fastforce dest!: map_u_renum_cconstraint_clock_valD)
      done

    preferT \<open>''target invariant''\<close> subgoal for l b g f r l' p ps bs gs fs rs ls' s'
      apply (tag- "SEL _" "''new loc''" "TRANS _")
      apply (subgoal_tac "fold (\<lambda>p L. L[p := ls' p]) ps L \<in> states")
      subgoal
        apply simp
        apply (erule all_mono[THEN mp, OF impI, rotated], erule (1) imp_mono_rule,
               drule (1) inv_renum_sem_I)
        subgoal
          apply (rule sem_states_loc_setD, simp)
          apply (rule state_preservation_updI)
          subgoal
            by blast
          .
        subgoal
          apply (fo_rule match_assumption2[where P = clock_val], assumption, rule HOL.refl)
          apply (drule states_lengthD, simp)
          done
        done
      subgoal
        apply (rule state_preservation_fold_updI)
         apply (erule Ball_mono)
         apply (simp add: atLeastLessThan_upperD; blast)
        by simp
      done

    preferT \<open>''bexp''\<close>
      apply (tag, erule check_bexp_renumD; fail)
    preferT \<open>''bexp''\<close>
      apply (solves \<open>tag, auto elim: check_bexp_renumD\<close>)
    preferT \<open>''guard''\<close>
      apply (tag, erule map_u_renum_cconstraint_clock_valI; fail)
    preferT \<open>''guard''\<close>
      apply (solves \<open>tag, auto elim: map_u_renum_cconstraint_clock_valI\<close>)
    preferT \<open>''new loc''\<close>
      apply (tag, simp add: map_trans_broad_aux1[symmetric] map_index_update; fail)
    preferT \<open>''new valuation''\<close>
      apply (tag, simp add: renum_reset_map_u[symmetric] renum_reset_def map_concat comp_def; fail)
    preferT \<open>''upd''\<close>
      apply (tag, erule is_upds_renumD; fail)
    preferT \<open>''upds''\<close>
      apply (tag, drule is_upds_concat_renumD, simp add: comp_def; fail)
    preferT \<open>''bounded''\<close>
      apply (tag, erule bounded_renumI'; fail)
    apply (tag, simp; fail)+
    done
  done

lemma inj_the_inv:
  "inj (the_inv f)" if "bij f"
  by (auto simp: bij_f_the_inv_f[OF that] dest: arg_cong[where f = f] intro!: injI)

lemma inj_vars_inv:
  "inj vars_inv"
  using bij_renum_vars unfolding vars_inv_def by (rule inj_the_inv)

lemma comp_vars_inv_upd_commute:
  "(s o vars_inv)(x \<mapsto> y) = s(vars_inv x \<mapsto> y) o vars_inv"
  by (intro ext) (auto dest: injD[OF inj_vars_inv])

lemma is_upd_renumI:
  assumes "is_upd (s o vars_inv) (renum_upd f) s'"
  shows "is_upd s f (s' o renum_vars)"
  using assms
  unfolding is_upd_def renum_upd_def
  by (clarsimp dest!: is_val_renumI split: prod.split_asm simp: comp_vars_inv_upd_commute)
     (force simp: the_inv_f_f[OF inj_renum_vars] vars_inv_def)

lemma is_upd_renumI':
  assumes "is_upd (s o vars_inv) (renum_upd f) s'"
  obtains s1 where "is_upd s f s1" "s1 = s' o renum_vars"
  by (simp add: assms is_upd_renumI)

lemma is_upd_renumI'':
  assumes "is_upd s (renum_upd f) s'"
  shows "is_upd (s o renum_vars) f (s' o renum_vars)"
proof -
  have "s = (s o renum_vars) o vars_inv"
    by (intro ext) (auto simp: bij_f_the_inv_f[OF bij_renum_vars] vars_inv_def)
  with assms  show ?thesis
    by (intro is_upd_renumI) simp
qed

lemma is_upds_renumI:
  assumes "is_upds (s o vars_inv) (renum_upds upds) s'"
  shows "\<exists>s1. is_upds s upds s1 \<and> s1 = s' o renum_vars"
  using assms apply (induction "s o vars_inv" "renum_upds upds" s' arbitrary: upds s)
  subgoal for upds s
    apply simp
    apply (subgoal_tac "s o vars_inv o renum_vars = s")
     apply (solves \<open>auto intro: is_upds.intros simp: comp_def\<close>)
    apply (rule ext)
    apply (simp add: vars_inv_def the_inv_f_f[OF inj_renum_vars])
    done

  apply clarsimp
  apply (erule is_upd_renumI')
  apply (auto simp: vars_inv_def bij_f_the_inv_f[OF bij_renum_vars] comp_def intro!: is_upds.intros)
  done

lemma is_upds_renumI':
  assumes "is_upds (s o vars_inv) (renum_upds f) s'"
  shows "is_upds s f (s' o renum_vars)"
  using is_upds_renumI[OF assms] by simp

lemma is_upds_renumI'':
  assumes "is_upds s (renum_upds ps) s'"
  shows "is_upds (s o renum_vars) ps (s' o renum_vars)"
  using assms
  by (induction "renum_upds ps" s' arbitrary: ps) (auto 4 3 intro: is_upd_renumI'' is_upds.intros)

lemma is_upds_concat_renumI'':
  assumes "is_upds s (concat_map renum_upds ps) s'"
  shows "is_upds (s o renum_vars) (concat ps) (s' o renum_vars)"
  apply (rule is_upds_renumI'')
  using assms by (simp add: map_concat)

lemma bounded_renumD1:
  assumes "bounded renum.bounds s'" "dom (s' \<circ> renum_vars) \<subseteq> var_set"
  shows "bounded bounds (s' o renum_vars)"
  using assms
  by (intro bounded_renumD') (auto simp: vars_inv_def bij_f_the_inv_f[OF bij_renum_vars] comp_def)

lemma renum_reset_append:
  "renum_reset xs @ renum_reset ys = renum_reset (xs @ ys)"
  unfolding renum_reset_def by simp

lemma if_eq_distrib:
  "(if i = j then f i a else f j b) = (f j (if i = j then a else b))"
  by auto

lemma dom_comp_eq_vimage:
  "dom (s o f) = f -` dom s"
  unfolding dom_def by auto

lemma dom_comp_vars_inv_eqD:
  assumes "dom s' = dom (s o vars_inv)"
  shows "dom (s' o renum_vars) = dom s"
  using assms inj_renum_vars surj_renum_vars unfolding vars_inv_def
  by (subst (asm) dom_the_inv_comp) (auto simp: dom_comp_eq_vimage dest: injD)

lemma sem_trans_upd_domD:
  assumes "(L ! p, b, g', a, f, r, l1) \<in> trans (N p)" "p < n_ps"
  shows "fst ` set f \<subseteq> var_set"
proof -
  from assms have "fst ` set f \<subseteq> var_set"
    unfolding var_set_def
    apply -
    apply (rule semilattice_sup_class.sup.coboundedI2)
    apply clarsimp
    apply (inst_existentials "(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p)" p)
      apply force+
    done
  then show ?thesis .
qed

lemma SilD:
  fixes map_action
  assumes "Sil a = map_act map_action a1"
  obtains a' where "a1 = Sil a'" "a = map_action a'"
  using assms by (cases a1) auto

lemma InD:
  fixes map_action
  assumes "In a = map_act map_action a1"
  obtains a' where "a1 = In a'" "a = map_action a'"
  using assms by (cases a1) auto

lemma OutD:
  fixes map_action
  assumes "Out a = map_act map_action a1"
  obtains a' where "a1 = Out a'" "a = map_action a'"
  using assms by (cases a1) auto

lemma In_OutD:
  assumes "In a = renum_act a1" "Out a = renum_act a2"
  obtains a' where "a = renum_acts a'" "a1 = In a'" "a2 = Out a'"
  using assms unfolding renum_act_def by (elim InD OutD) (auto simp: injD[OF inj_renum_acts])

lemma renum_sem_broadcast_eq:
  "renum.broadcast = renum_acts ` set broadcast"
  unfolding renum.broadcast_def by simp

lemma inj_eq_iff:
  "f x = f y \<longleftrightarrow> x = y" if "inj f"
  using that unfolding inj_def by auto

lemma trans_sem_N_renum_broadcastI:
  assumes
    "\<forall>p\<in>set ps. (renum_states p (L ! p), bs p, gs p, In a, fs p, rs p, ls p) \<in> trans (renum.N p)"
    "set ps \<subseteq> {0..<n_ps}"
  obtains bs' gs' fs' rs' ls' a' where
    "\<forall>p\<in>set ps. (L ! p, bs' p, gs' p, In a', fs' p, rs' p, ls' p) \<in> trans (N p)"
    "\<forall>p\<in>set ps. bs p = renum_bexp (bs' p)"
    "\<forall>p\<in>set ps. gs p = renum_cconstraint (gs' p)"
    "ps \<noteq> [] \<longrightarrow> a = renum_acts a'"
    "\<forall>p\<in>set ps. fs p = renum_upds (fs' p)"
    "\<forall>p\<in>set ps. rs p = renum_reset (rs' p)"
    "\<forall>p\<in>set ps. ls p = renum_states p (ls' p)"
proof -
  define t where
    "t p \<equiv> SOME (b', g', a', f', r', l1). (L ! p, b', g', a', f', r', l1) \<in> trans (N p)
    \<and> bs p = renum_bexp b' \<and> gs p = renum_cconstraint g' \<and> In a = renum_act a' \<and> fs p = renum_upds f'
    \<and> rs p = renum_reset r' \<and> ls p = renum_states p l1" for p
  define bs' where "bs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> b'" for p
  define gs' where "gs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> g'" for p
  define as' where "as' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> a'" for p
  define fs' where "fs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> f'" for p
  define rs' where "rs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> r'" for p
  define ls' where "ls' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> l1" for p

  have *: "case t p of (b', g', a', f', r', l1) \<Rightarrow>
    (L ! p, b', g', a', f', r', l1) \<in> trans (N p)
    \<and> bs p = renum_bexp b' \<and> gs p = renum_cconstraint g' \<and> In a = renum_act a' \<and> fs p = renum_upds f'
    \<and> rs p = renum_reset r' \<and> ls p = renum_states p l1" if "p \<in> set ps" for p
    using assms(1)
    apply -
    apply (drule bspec[OF _ that])
    apply (drule trans_sem_N_renumI')
    subgoal
      using assms(2) that by auto
    unfolding t_def by (untag, elims, fo_rule someI, auto)

  show ?thesis
  proof (cases "ps")
    case Nil
    then show ?thesis
      by (auto intro: that)
  next
    case (Cons p ps')
    then have "p \<in> set ps"
      by auto
    define a' where "a' = as' p"
    have 1: "as' q = a'" and "In a = renum_act a'" if "q \<in> set ps" for q
      unfolding as'_def a'_def using *[OF that] *[OF \<open>p \<in> set ps\<close>]
      by (auto dest: injD[OF injective_functions(3)])
    then obtain a1 where "a' = In a1" "a = renum_acts a1"
      using \<open>p \<in> set ps\<close> unfolding renum_act_def by (auto elim!: InD)
    then show ?thesis
      apply -
      apply (rule that[of bs' gs' a1 fs' rs' ls'])
      unfolding bs'_def gs'_def fs'_def rs'_def ls'_def
      by (solves \<open>(intros, frule *)?, auto simp: as'_def dest: 1\<close>)+
  qed
qed

lemmas all_mono_rule = all_mono[THEN mp, OF impI, rotated]

method prop_monos =
  erule all_mono_rule
  | erule (1) imp_mono_rule
  | erule disj_mono[rule_format, rotated 2]

lemma inv_sem_N_renum_broadcastI:
  assumes
"\<forall>pa<n_ps.
  [renum_reset r @ concat (map rs ps)\<rightarrow>0]map_u u
    \<turnstile> inv (renum.N pa)
        ((fold (\<lambda>p L. L[p := ls p]) ps (map_index renum_states L)) [p := renum_states p l1] ! pa)"
"\<forall>p\<in>set ps. rs p = renum_reset (rs' p)"
"\<forall>p\<in>set ps. ls p = renum_states p (ls' p)"
"\<forall>p\<in>set ps. ls' p \<in> (\<Union>(l, b, g, a, r, u, l') \<in> trans (N p). {l, l'})"
"l1 \<in> (\<Union>(l, b, g, a, r, u, l') \<in> trans (N p). {l, l'})"
"L \<in> states"
shows
"\<forall>pa<n_ps.
  [r @ concat (map rs' ps)\<rightarrow>0]u \<turnstile> inv (N pa) ((fold (\<lambda>p L. L[p := ls' p]) ps L) [p := l1] ! pa)"
proof -
  have [simp]: "renum_reset r @ concat (map rs ps) = renum_reset (r @ concat (map rs' ps))"
    using assms(2) by (simp cong: map_cong add: map_concat renum_reset_def)
  have [simp]: "length L = n_ps"
    using \<open>L \<in> states\<close> by auto
  have [simp]:
    "((fold (\<lambda>p L. L[p := ls p]) ps (map_index renum_states L)) [p := renum_states p l1] ! q)
    = renum_states q ((fold (\<lambda>p L. L[p := ls' p]) ps L) [p := l1] ! q)"
    if "q < n_ps" for q
    using assms(4-) that
    apply (cases "p = q")
     apply (simp add: fold_upds_aux_length)
    apply (simp
        add: assms(3) map_trans_broad_aux1[symmetric] fold_upds_aux_length
        cong: fold_cong)
    done
  have "(fold (\<lambda>p L. L[p := ls' p]) ps L)[p := l1] ! q \<in> loc_set" if "q < n_ps" for q
    using assms(4-)
    apply (intro sem_states_loc_setD)
    subgoal
      using that by (simp add: n_ps_def)
    apply (erule state_preservation_updI)
    by (rule state_preservation_fold_updI)
  then show ?thesis
    using assms
    by (auto dest: inv_renum_sem_D simp: renum_reset_map_u simp del: map_map_index set_map)
qed

method solve_triv =
  assumption
  | erule (1) bounded_renumD'; fail
  | rule inv_renum_sem_D[OF _ _ sem_states_loc_setD]; simp; fail
  | rule check_bexp_renumI; simp; fail
  | rule map_u_renum_cconstraint_clock_valD; simp; fail
  | rule is_upd_renumI is_upd_renumI'' is_upds_renumI' is_upds_renumI'' is_upds_concat_renumI'',
    simp; fail
  | simp; fail
  | simp add:
      vars_inv_def bij_f_the_inv_f[OF bij_renum_vars] renum_reset_map_u[symmetric] map_index_update
      renum_reset_append;
    fail
  | subst nth_map, (simp; fail)+; fail
  | (rule state_preservation_updI, blast)+, simp; fail

lemma trans_sem_upd_domI:
  assumes "(L ! p, b', g', a, f', r', l1) \<in> trans (N p)" "dom s = var_set" "p < n_ps"
  shows "\<forall>(x, _)\<in>set (renum_upds f'). x \<in> dom (s o vars_inv)"
  unfolding renum_upd_def using assms
  by (auto simp: dom_comp_eq_vimage vars_inv_def the_inv_f_f[OF inj_renum_vars]
           dest!: sem_trans_upd_domD)

lemma step_single_renumI:
  assumes
    "step_u renum.sem
      (map_index renum_states L) (s o vars_inv) (map_u u) a L' s' u'"
    "L \<in> states" "dom s \<subseteq> var_set" "dom s = var_set"
  shows "\<exists> a1 L1 s1 u1. step_u sem L s u a1 L1 s1 u1 \<and> renum_label a1 = a \<and>
    L' = map_index renum_states L1 \<and> s' = s1 o vars_inv \<and> u' = map_u u1"
  using assms(1-3)
  supply [simp] = length_automata_eq_n_ps L_len
  supply [simp del] = map_map_index set_map
  apply (subst A_split)
  apply (subst (asm) renum.A_split)
  apply (simp only: renum_label_def label.map renum_n_ps_simp)

  using [[goals_limit=2]]

  apply (cases a)

  \<comment> \<open>Delay\<close>
  subgoal
    apply (simp only:)
    apply (erule step_u_elims')
    apply intros
    apply (rule step_u.intros)
    preferT \<open>''nonnegative''\<close>
      apply assumption
    preferT \<open>''urgent''\<close> subgoal
      using urgency_removed by - (tag, auto)
    preferT \<open>''target invariant''\<close>
      apply (solves \<open>tag, simp, prop_monos+, solve_triv+\<close>)
    apply (tag, solve_triv)+
    done

  \<comment> \<open>Internal\<close>
  subgoal for a'
    apply (simp only:)
    apply (erule step_u_elims')
    subgoal premises prems[tagged] for l b g f r l' p
    using prems apply tag
    using sym[OF [[get_tagged \<open>''loc''\<close>]]]
    usingT "TRANS _" \<open>''range''\<close>
    apply simp
    apply (drule (1) trans_sem_N_renumI', untag)
    apply elims
    unfolding renum_act_def
    apply (rule SilD, assumption)

    apply intros
    apply (rule step_u.intros(2))

    preferT \<open>TRANS ''silent''\<close> apply (tag, solve_triv)

    preferT \<open>''committed''\<close>
    apply (solves \<open>tag, prop_monos; auto simp: committed_renum_eq dest: injD[OF inj_renum_states]\<close>)

    preferT \<open>''bexp''\<close> apply (tag, solve_triv)
    preferT \<open>''guard''\<close> apply (tag, solve_triv)

    preferT \<open>''target invariant''\<close>
      apply (solves \<open>tag "''new valuation''" "''new loc''",
        simp add: map_index_update[symmetric] renum_reset_map_u, prop_monos+,
        rule inv_renum_sem_D[OF _ _ sem_states_loc_setD],
        solve_triv+\<close>)

    preferT \<open>''is_upd''\<close>
      apply (tag, solve_triv)

    preferT \<open>''bounded''\<close> subgoal
      apply (tag \<open>''is_upd''\<close>, erule bounded_renumD1)
      apply (drule is_upds_dom)
      subgoal
        apply (simp add: dom_comp_eq_vimage)
        unfolding renum_upd_def
        apply (clarsimp simp: vars_inv_def the_inv_f_f[OF inj_renum_vars] set_map)
        apply (drule (1) sem_trans_upd_domD)
        using assms(4)
        apply auto
        done
      apply (drule dom_comp_vars_inv_eqD, simp)
      done

    apply (tag, solve_triv)+
    usingT \<open>''new loc''\<close> apply solve_triv

(* or: auto *)
    apply (rule ext)
    usingT \<open>''new valuation''\<close> apply solve_triv+
    done
  done

  \<comment> \<open>Binary\<close>
  subgoal for a'
    apply (simp only:)
    apply (erule step_u_elims')
    subgoal premises prems[tagged] for l1 b1 g1 f1 r1 l1' p l2 b2 g2 f2 r2 l2' q s'a
    using prems apply tag
    apply (tag "RECV ''loc''" "SEND ''loc''")
    apply (drule sym[of "map_index renum_states L ! _"])+
    apply (tag "TRANS _" "RECV ''range''" "SEND ''range''")
    apply simp
    apply (drule (1) trans_sem_N_renumI')
    apply (drule (1) trans_sem_N_renumI', untag)
    apply elims
    apply (rule In_OutD, assumption, assumption)

    apply intros
        apply (rule step_u.intros(3))
                        preferT \<open>''not broadcast''\<close>
                        apply (tag, simp add: renum_sem_broadcast_eq broadcast_def)
    using inj_renum_acts
    apply auto[1]
    preferT \<open>TRANS ''in''\<close> apply (tag, solve_triv)
    preferT \<open>TRANS ''out''\<close> apply (tag, solve_triv)
    preferT \<open>''committed''\<close> subgoal
      by (tag, auto simp: committed_renum_eq inj_eq_iff[OF inj_renum_states])
    preferT \<open>''target invariant''\<close>
      apply (
        solves \<open>tag "''new valuation''" "''new loc''",
        simp add: map_index_update[symmetric] renum_reset_map_u renum_reset_append,
        prop_monos+,
        rule inv_renum_sem_D[OF _ _ sem_states_loc_setD],
        solve_triv+\<close>)

    preferT \<open>''upd''\<close> apply (tag, solve_triv)
    preferT \<open>''upd''\<close> apply (tag, solve_triv)

    preferT \<open>''bounded''\<close> subgoal
      usingT- \<open>''upd''\<close>
      apply -
      apply (tag, erule bounded_renumD1)
      apply (drule is_upds_dom)
      subgoal
        using assms(4) by - (drule trans_sem_upd_domI; simp split: prod.splits)
      apply (drule is_upds_dom)
      subgoal
        using assms(4) by - (drule trans_sem_upd_domI; simp split: prod.splits)
      apply (simp, drule dom_comp_vars_inv_eqD, simp)
      done
    apply (tag, solve_triv)+
    apply (tag "''new loc''", solve_triv)
    apply (rule ext; solve_triv)
    apply (tag "''new valuation''", solve_triv)
    done
  done

  \<comment> \<open>Broadcast\<close>
  subgoal for a'
    apply (simp only:)
    apply (erule step_u_elims')
    subgoal premises prems[tagged] for l b g f r l' p ps bs gs fs rs ls' s'a
    using prems apply (tag "SEND ''range''" "TRANS ''out''")
    using sym[OF [[get_tagged \<open>SEND ''loc''\<close>]]]
    apply simp
    apply (frule (1) trans_sem_N_renumI')
    apply elims
    subgoal premises prems[tagged] for b' g' a'a f' r' l1
      using prems(1-6) usingT- "TRANS ''in''" "SEL _" \<open>''renum action''\<close>
      unfolding renum_act_def
      apply -
      apply (rule OutD, assumption)
      apply (simp add: atLeastLessThan_upperD)
      apply (erule(1) trans_sem_N_renum_broadcastI)
      apply (subgoal_tac "map fs ps = map renum_upds (map fs' ps)")
       defer
       apply (simp; fail)

      subgoal for a1 bs' gs' fs' rs' ls1 a2

        apply intros
            apply (rule step_u.intros(4)[where ps = ps])

        preferT \<open>TRANS ''out''\<close> apply (tag \<open>TRANS ''orig''\<close>, solve_triv)

        preferT \<open>''broadcast''\<close>
          apply (tag,
            clarsimp simp: renum_sem_broadcast_eq inj_eq_iff[OF inj_renum_acts] broadcast_def; fail)

        preferT \<open>TRANS ''in''\<close>
        apply (tag,
            cases "ps = []"; simp add: atLeastLessThan_upperD inj_eq_iff[OF inj_renum_acts]; fail)

        preferT \<open>''committed''\<close> subgoal
          apply (tag, prop_monos)
          apply (solves \<open>auto simp: committed_renum_eq inj_eq_iff[OF inj_renum_states]\<close>)
          apply prop_monos
          subgoal
            by (auto simp: committed_renum_eq inj_eq_iff[OF inj_renum_states] atLeastLessThan_upperD)
          subgoal premises prems
            using \<open>L \<in> states\<close> prems(21) (* last premise only *)
            by (auto simp: inj_eq_iff[OF inj_renum_states] committed_renum_eq)
          done

        preferT \<open>''bexp''\<close> apply (tag \<open>''renum bexp''\<close>, solve_triv)

        preferT \<open>''bexp''\<close> apply (tag, erule Ball_mono, solve_triv; fail)

        preferT \<open>''guard''\<close> apply (tag \<open>''renum guard''\<close>, solve_triv)

        preferT \<open>''guard''\<close> apply (tag, erule Ball_mono, solve_triv)

        preferT \<open>''maximal''\<close> subgoal
          apply tag
          apply simp
          apply prop_monos+
          apply clarify
          apply (drule (1) trans_N_renumD)+
          apply (simp add: renum_act_def)
          apply (drule check_bexp_renumD)
          apply (drule map_u_renum_cconstraint_clock_valI)
          apply blast
          done

        preferT \<open>''target invariant''\<close>
          apply (tag "''new loc''" "''new valuation''" "''renum reset''" "''renum loc''" "TRANS _")
          apply (simp add: atLeastLessThan_upperD)
          apply (solves \<open>erule (2) inv_sem_N_renum_broadcastI, blast, fast, solve_triv\<close>)

        preferT \<open>''upds''\<close>
          apply (tag "''renum upds''", simp only:, solve_triv)

        preferT \<open>''bounded''\<close> subgoal
          apply (tag "''upd''" "''upds''" "''renum upds''", simp only:)
          apply (erule bounded_renumD1)
          apply (drule is_upds_dom)
          subgoal
            using assms(4) usingT \<open>TRANS ''orig''\<close> by (intro trans_sem_upd_domI)

          apply (drule is_upds_dom)
          subgoal
            using assms(4) usingT \<open>''upd''\<close> \<open>''upds''\<close>
            apply (simp add: set_map)
            apply (erule Ball_mono, drule trans_sem_upd_domI, assumption)
             apply (simp add: atLeastLessThan_upperD set_map; fail)+
            done
          apply (simp, drule dom_comp_vars_inv_eqD, simp)
          done

        preferT \<open>''upd''\<close> apply (tag "''renum upds''", solve_triv)
        
        apply (tag, solve_triv)+

        apply (tag "''new loc''" "''renum loc''",
          simp add: map_trans_broad_aux1 map_index_update cong: fold_cong; fail)

        apply (solves \<open>auto simp: vars_inv_def bij_f_the_inv_f[OF bij_renum_vars]\<close>)
        apply (tag "''new valuation''" "''renum reset''",
          simp add: renum_reset_map_u[symmetric] renum_reset_def map_concat comp_def cong: map_cong;
          fail)
        done
      done
    done
    done
  done

lemma step_u_var_set_invariant:
  assumes "step_u sem L s u a L' s' u'" "dom s = var_set"
  shows "dom s' = var_set"
  using assms dom_bounds_var_set by (auto 4 4 dest!: bounded_inv simp: bounded_def)

lemmas step_u_invariants = states_inv step_u_var_set_invariant

interpretation single: Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u renum.sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> states \<and> dom s = var_set" "\<lambda>_. True"
  apply standard
  supply [simp del] = map_map_index set_map
     apply clarsimp
  subgoal for L s u L' s' u' a
    by (drule (1) step_single_renumD, auto)
  subgoal
    by clarsimp (drule step_single_renumI[rotated]; blast)
  subgoal
    by clarsimp (intro conjI; elim step_u_invariants)
  subgoal
    .
  done

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> states \<and> dom s = var_set" "\<lambda>_. True"
proof -
  define rsem where "rsem = renum.sem"
  note step_single_renumD = step_single_renumD[folded rsem_def]
  have "rsem \<turnstile> \<langle>map_index renum_states L, (s \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars, map_u u\<rangle> \<rightarrow> \<langle>map_index renum_states L', (s' \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars, map_u u'\<rangle>"
    if "sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
      and "L \<in> states"
      and "dom s = var_set"
    for L :: "'s list"
      and s :: "'x \<Rightarrow> int option"
      and u :: "'c \<Rightarrow> real"
      and L' :: "'s list"
      and s' :: "'x \<Rightarrow> int option"
      and u' :: "'c \<Rightarrow> real"
  proof -
    from that(1) obtain L1 s1 u1 a where
      "sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L1, s1, u1\<rangle>" "a \<noteq> Del" "sem \<turnstile> \<langle>L1, s1, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      by (elim step_u'_elims)
    with that(2-) show ?thesis
      apply -
      apply (rule step_u'.intros[where a = "renum_label a"])
        apply (erule (1) step_single_renumD[where a = Del, unfolded renum_label_def, simplified], blast)
       apply (cases a; (fast | simp add: renum_label_def))
      apply (erule step_single_renumD)
       apply (blast dest: step_u_invariants)+
      done
  qed
  moreover have "\<exists>a aa b. sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>a, aa, b\<rangle> \<and> L' = map_index renum_states a \<and> s' = (aa \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars \<and> u' = map_u b"
    if "L \<in> states"
      and "dom s = var_set"
      and "rsem \<turnstile> \<langle>map_index renum_states L, (s \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars, map_u u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    for L :: "'s list"
      and s :: "'x \<Rightarrow> int option"
      and u :: "'c \<Rightarrow> real"
      and L' :: "nat list"
      and s' :: "nat \<Rightarrow> int option"
      and u' :: "nat \<Rightarrow> real"
  proof -
    from that(3) obtain L1 s1 u1 a where
      "rsem \<turnstile> \<langle>map_index renum_states  L, (s o vars_inv), map_u u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L1, s1, u1\<rangle>"
      "a \<noteq> Del" "rsem \<turnstile> \<langle>L1, s1, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      by (elim step_u'_elims)
    with that(1,2) show ?thesis
      apply -
      apply (drule (1) step_single_renumI[folded rsem_def], blast)
      apply safe
      subgoal premises prems for a1 L1a s1a u1a
      proof -
        { fix a1a L1b s1b u1b
          have "
           L \<in> states \<Longrightarrow>
           dom s = var_set \<Longrightarrow>
           renum_label a1a \<noteq>
           Simple_Network_Language.label.Del \<Longrightarrow>
           sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a1\<^esub> \<langle>L1a, s1a, u1a\<rangle> \<Longrightarrow>
           renum_label a1 =
           Simple_Network_Language.label.Del \<Longrightarrow>
           L1 = map_index renum_states L1a \<Longrightarrow>
           u1 = map_u u1a \<Longrightarrow>
           s1 =
           (s1a \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv)
            renum_vars \<Longrightarrow>
           sem \<turnstile> \<langle>L1a, s1a, u1a\<rangle> \<rightarrow>\<^bsub>a1a\<^esub> \<langle>L1b, s1b, u1b\<rangle> \<Longrightarrow>
           a = renum_label a1a \<Longrightarrow>
           L' = map_index renum_states L1b \<Longrightarrow>
           s' =
           (s1b \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv)
            renum_vars \<Longrightarrow>
           u' = map_u u1b \<Longrightarrow>
           a1 = Simple_Network_Language.label.Del"
            by (cases a1; simp add: renum_label_def)
        } note * = this
        from prems show ?thesis
          apply -
        apply (drule step_single_renumI[folded rsem_def])
          apply (blast dest: step_u_invariants)+
        apply (subgoal_tac "a1 = Del")
         apply clarsimp
         apply intros
            apply (erule step_u'.intros)
        apply (auto intro: *)
        done
    qed
    done
  qed
  moreover have "x1b \<in> states \<and> dom x1c = var_set"
    if "x1 \<in> states"
      and "dom x1a = var_set"
      and "sem \<turnstile> \<langle>x1, x1a, x2a\<rangle> \<rightarrow> \<langle>x1b, x1c, x2c\<rangle>"
    for x1 :: "'s list"
      and x1a :: "'x \<Rightarrow> int option"
      and x2a :: "'c \<Rightarrow> real"
      and x1b :: "'s list"
      and x1c :: "'x \<Rightarrow> int option"
      and x2c :: "'c \<Rightarrow> real"
    using that by (elim step_u'_elims) (auto 4 4 dest: step_u_invariants)
  moreover note * = calculation
  show "Bisimulation_Invariant
     (\<lambda>(L, s, u) (L', s', u'). sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u'). renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u').
         L' = map_index renum_states L \<and>
         s' = (s o vars_inv) \<and>
         u' = map_u u)
     (\<lambda>(L, s, u). L \<in> states \<and> dom s = var_set) (\<lambda>_. True)"
    unfolding rsem_def[symmetric]
    apply (standard; clarsimp split: prod.splits)
    by (rule *; assumption)+
qed

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> states \<and> dom s = var_set" "\<lambda>_. True"
proof -
  define rsem where "rsem = renum.sem"
  note step_single_renumD = step_single_renumD[folded rsem_def]
  have "rsem \<turnstile> \<langle>map_index renum_states L, (s \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars, map_u u\<rangle> \<rightarrow> \<langle>map_index renum_states L', (s' \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars, map_u u'\<rangle>"
    if "sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
      and "L \<in> states"
      and "dom s = var_set"
    for L :: "'s list"
      and s :: "'x \<Rightarrow> int option"
      and u :: "'c \<Rightarrow> real"
      and L' :: "'s list"
      and s' :: "'x \<Rightarrow> int option"
      and u' :: "'c \<Rightarrow> real"
  proof -
    from that(1) obtain L1 s1 u1 a where
      "sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L1, s1, u1\<rangle>" "a \<noteq> Del" "sem \<turnstile> \<langle>L1, s1, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      by (elim step_u'_elims)
    with that(2-) show ?thesis
      apply -
      apply (rule step_u'.intros[where a = "renum_label a"])
        apply (erule (1) step_single_renumD[where a = Del, unfolded renum_label_def, simplified], blast)
       apply (cases a; (fast | simp add: renum_label_def))
      apply (erule step_single_renumD)
       apply (blast dest: step_u_invariants)+
      done
  qed
  moreover have "\<exists>a aa b. sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>a, aa, b\<rangle> \<and> L' = map_index renum_states a \<and> s' = (aa \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars \<and> u' = map_u b"
    if "L \<in> states"
      and "dom s = var_set"
      and "rsem \<turnstile> \<langle>map_index renum_states L, (s \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv) renum_vars, map_u u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    for L :: "'s list"
      and s :: "'x \<Rightarrow> int option"
      and u :: "'c \<Rightarrow> real"
      and L' :: "nat list"
      and s' :: "nat \<Rightarrow> int option"
      and u' :: "nat \<Rightarrow> real"
  proof -
    from that(3) obtain L1 s1 u1 a where
      "rsem \<turnstile> \<langle>map_index renum_states  L, (s o vars_inv), map_u u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L1, s1, u1\<rangle>"
      "a \<noteq> Del" "rsem \<turnstile> \<langle>L1, s1, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      by (elim step_u'_elims)
    with that(1,2) show ?thesis
      apply -
      apply (drule (1) step_single_renumI[folded rsem_def], blast)
      apply safe
      subgoal premises prems for a1 L1a s1a u1a
      proof -
        {fix a1a L1b s1b u1b
          have "
           L \<in> states \<Longrightarrow>
           dom s = var_set \<Longrightarrow>
           renum_label a1a \<noteq>
           Simple_Network_Language.label.Del \<Longrightarrow>
           sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a1\<^esub> \<langle>L1a, s1a, u1a\<rangle> \<Longrightarrow>
           renum_label a1 =
           Simple_Network_Language.label.Del \<Longrightarrow>
           L1 = map_index renum_states L1a \<Longrightarrow>
           u1 = map_u u1a \<Longrightarrow>
           s1 =
           (s1a \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv)
            renum_vars \<Longrightarrow>
           sem \<turnstile> \<langle>L1a, s1a, u1a\<rangle> \<rightarrow>\<^bsub>a1a\<^esub> \<langle>L1b, s1b, u1b\<rangle> \<Longrightarrow>
           a = renum_label a1a \<Longrightarrow>
           L' = map_index renum_states L1b \<Longrightarrow>
           s' =
           (s1b \<circ>\<circ> Simple_Network_Rename_Defs.vars_inv)
            renum_vars \<Longrightarrow>
           u' = map_u u1b \<Longrightarrow>
           a1 = Simple_Network_Language.label.Del"
           by (cases a1; simp add: renum_label_def)
        } note ** = this
        from prems show ?thesis
          apply -
          apply (drule step_single_renumI[folded rsem_def])
            apply (blast dest: step_u_invariants)+
          apply (subgoal_tac "a1 = Del")
           apply clarsimp
           apply intros
              apply (erule step_u'.intros)
          apply (auto intro: **)
          done
    qed
    done
  qed
  moreover have "x1b \<in> states \<and> dom x1c = var_set"
    if "x1 \<in> states"
      and "dom x1a = var_set"
      and "sem \<turnstile> \<langle>x1, x1a, x2a\<rangle> \<rightarrow> \<langle>x1b, x1c, x2c\<rangle>"
    for x1 :: "'s list"
      and x1a :: "'x \<Rightarrow> int option"
      and x2a :: "'c \<Rightarrow> real"
      and x1b :: "'s list"
      and x1c :: "'x \<Rightarrow> int option"
      and x2c :: "'c \<Rightarrow> real"
    using that by (elim step_u'_elims) (auto 4 4 dest: step_u_invariants)
  moreover note * = calculation
  show "Bisimulation_Invariant
     (\<lambda>(L, s, u) (L', s', u'). sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u'). renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u').
         L' = map_index renum_states L \<and>
         s' = (s o vars_inv) \<and>
         u' = map_u u)
     (\<lambda>(L, s, u). L \<in> states \<and> dom s = var_set) (\<lambda>_. True)"
    unfolding rsem_def[symmetric]
    apply (standard; clarsimp split: prod.splits)
    by (rule *; assumption)+
qed

lemmas renum_bisim = Bisimulation_Invariant_axioms

end

locale Simple_Network_Impl_Formula_real =
  Simple_Network_Rename_real where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, real, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, real) cconstraint) list) list" +
  fixes \<Phi> :: "(nat, 's, 'x, int) formula"
    and s\<^sub>0 :: "('x \<times> int) list"
    and L\<^sub>0 :: "'s list"
begin

definition \<Phi>' where
  "\<Phi>' = map_formula renum_states renum_vars id \<Phi>"

definition a\<^sub>0 where
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition a\<^sub>0' where
  "a\<^sub>0' = (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_. 0)"

context
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
  assumes s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
begin

(* Refine to subset of var_set? *)
lemma state_eq_aux:
  assumes "x \<notin> renum_vars ` var_set"
  shows "vars_inv x \<notin> var_set"
  unfolding vars_inv_def
proof safe
  assume "the_inv renum_vars x \<in> var_set"
  then have "renum_vars (the_inv renum_vars x) = x"
    by (intro f_the_inv_f inj_renum_vars) (simp add: surj_renum_vars)
  with assms \<open>_ \<in> var_set\<close> show False
    by force
qed

lemma state_eq:
  assumes "fst ` set s\<^sub>0 = var_set" "distinct (map fst s\<^sub>0)"
  shows "map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0) = (map_of s\<^sub>0 \<circ>\<circ>\<circ> the_inv_into) UNIV renum_vars"
    (is "?l = ?r")
proof (rule ext)
  fix x
  show "?l x = ?r x"
  proof (cases "x \<in> renum_vars ` fst ` set s\<^sub>0")
    case True
    then show ?thesis
      apply clarsimp
      apply (subst map_of_mapk_SomeI')
      subgoal
        using inj_renum_vars by (auto intro: inj_on_subset)
       apply (rule map_of_is_SomeI, rule assms, assumption)
      apply (simp add: the_inv_f_f[OF inj_renum_vars] s\<^sub>0_distinct)
      done
  next
    case False
    then have "vars_inv x \<notin> fst ` set s\<^sub>0"
      using state_eq_aux assms(1) unfolding vars_inv_def by auto
    with False show ?thesis
      apply -
      apply (frule map_of_NoneI)
      apply (simp add: vars_inv_def)
      apply (auto simp: map_of_eq_None_iff)
      done
  qed
qed

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> states \<and> dom s = var_set" "\<lambda>_. True"
  by (rule renum_bisim)

lemma start_equiv:
  "A_B.equiv' a\<^sub>0 a\<^sub>0'"
  unfolding A_B.equiv'_def a\<^sub>0_def a\<^sub>0'_def
  apply (clarsimp simp: vars_inv_def, intro conjI)
  subgoal
    by (intro state_eq s\<^sub>0_dom s\<^sub>0_distinct)
  subgoal
    unfolding map_u_def by auto
  subgoal
    by (rule L\<^sub>0_states)
  subgoal
    using s\<^sub>0_dom dom_map_of_conv_image_fst[of s\<^sub>0] by fastforce
  done

lemma check_sexp_equiv:
  assumes "A_B.equiv' (L, s, u) (L', s', u')" "locs_of_sexp e \<subseteq> {0..<n_ps}"
  shows
  "check_sexp e L (the \<circ> s) \<longleftrightarrow>
   check_sexp (map_sexp renum_states renum_vars id e) L' (the \<circ> s')"
  using assms unfolding A_B.equiv'_def
  by (induction e)
     (simp add: inj_eq states_lengthD renum_states_inj vars_inv_def the_inv_f_f[OF inj_renum_vars])+

lemma models_iff:
  "sem,a\<^sub>0 \<Turnstile> \<Phi> = renum.sem,a\<^sub>0' \<Turnstile> \<Phi>'" if "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
proof -
  have "rel_ctl_formula compatible (ctl_of \<Phi>) (ctl_of \<Phi>')"
    using that unfolding \<Phi>'_def
    by (cases \<Phi>; auto simp: check_sexp_equiv prop_of_def rel_fun_def)
  with start_equiv show ?thesis
    by (simp add: models_ctl_iff CTL_compatible[THEN rel_funD, symmetric])
qed

lemma has_deadlock_iff:
  "has_deadlock sem a\<^sub>0 \<longleftrightarrow> has_deadlock renum.sem a\<^sub>0'"
  unfolding has_deadlock_def using start_equiv by (intro deadlock_iff, unfold A_B.equiv'_def) auto

end (* Context for assumptions *)

end (* Simple Network Rename real *)


lemma Bisimulation_Invariants_Bisimulation_Invariant:
  assumes "Bisimulation_Invariants A B sim PA PA PB PB"
  shows "Bisimulation_Invariant A B sim PA PB"
proof -
  interpret Bisimulation_Invariants A B sim PA PA PB PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step)
qed

lemma Bisimulation_Invariants_Bisimulation_Invariant_iff:
  "Bisimulation_Invariants A B sim PA PA PB PB \<longleftrightarrow> Bisimulation_Invariant A B sim PA PB"
  using
    Bisimulation_Invariants_Bisimulation_Invariant Bisimulation_Invariant_Bisimulation_Invariants
  by blast

lemmas Bisimulation_Invariant_composition =
  Bisimulation_Invariant_Invariants_composition[
    THEN Bisimulation_Invariants_Bisimulation_Invariant,
    OF _ Bisimulation_Invariant_Bisimulation_Invariants]

lemma Bisimulation_Invariant_refl:
  "Bisimulation_Invariant A A (=) P P" if "\<And>a b. P a \<Longrightarrow> A a b \<Longrightarrow> P b"
  by (rule Bisimulation_Invariant.intro) (auto intro: that)


locale Simple_Network_Rename_int =
  Simple_Network_Rename_Defs_int where automata = automata +
  Simple_Network_Rename' where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  assumes urgency_removed: "\<forall> (_, U, _, _) \<in> set automata. U = []"
begin

lemma n_ps_eq1:
  "Prod_TA_Defs.n_ps
        (set broadcast, map automaton_of (map conv_automaton automata),
         map_of bounds') = n_ps"
  unfolding n_ps_def Prod_TA_Defs.n_ps_def by simp

lemma var_set_eq1:
  "Prod_TA_Defs.var_set
     (set broadcast, map automaton_of (map conv_automaton automata),
      map_of bounds') = var_set"
  unfolding sem_def sem_var_set_eq[symmetric] by simp

lemma urgency_removed':
  "\<forall>i<n_ps. urgent
  (Prod_TA_Defs.N (set broadcast, map automaton_of (map conv_automaton automata), map_of bounds') i)
  = {}"
  unfolding urgent_def n_ps_def Prod_TA_Defs.n_ps_def Prod_TA_Defs.N_def
  unfolding conv_automaton_def automaton_of_def
  using urgency_removed by (fastforce dest: nth_mem split: prod.split)

sublocale real: Simple_Network_Rename_real where automata = "map conv_automaton automata"
  apply standard
  unfolding n_ps_eq1 var_set_eq1
  by (rule bij_renum_clocks renum_states_inj bij_renum_vars bounds'_var_set inj_renum_acts
           urgency_removed')+

lemma sem_unfold1:
  "real.sem = sem"
  unfolding sem_def by simp

lemma var_set_eq:
  "real.var_set = sem.var_set"
  unfolding sem_unfold1[symmetric] ..

lemma map_acconstraint_conv_ac_commute:
  "map_acconstraint renum_clocks id (conv_ac ac) = conv_ac (map_acconstraint renum_clocks id ac)"
  by (cases ac; simp)

lemma map_ccconstraint_conv_cc_commute:
  "renum_cconstraint (conv_cc g) = conv_cc (renum_cconstraint g)"
  unfolding renum_cconstraint_def map_cconstraint_def by (simp add: map_acconstraint_conv_ac_commute)

lemma rename_conv_automaton_commute:
  "real.renum_automaton n (conv_automaton x) = conv_automaton (real.renum_automaton n x)"
  unfolding real.renum_automaton_def conv_automaton_def
  by (clarsimp split: prod.split simp: map_ccconstraint_conv_cc_commute)

lemma sem_unfold2:
  "real.renum.sem = renum.sem"
  by (simp add: Simple_Network_Impl.sem_def rename_conv_automaton_commute)

sublocale renum_bisim: Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s = var_set" "\<lambda>_. True"
  apply (rule Bisimulation_Invariant_sim_replace)
   apply (rule Bisimulation_Invariant_composition)
    apply (rule real.renum_bisim[unfolded sem_unfold1 sem_unfold2 sem_var_set_eq])
   apply (rule Bisimulation_Invariant_refl)
   apply auto
  done

lemmas renum_bisim = renum_bisim.Bisimulation_Invariant_axioms

end

locale Simple_Network_Rename_Start' =
  Simple_Network_Rename' where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, 't, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, 't) cconstraint) list) list" +
  fixes s\<^sub>0 :: "('x \<times> int) list"
    and L\<^sub>0 :: "'s list"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
  assumes s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
begin

end

locale Simple_Network_Rename_Start_int =
  Simple_Network_Rename_int where automata = automata +
  Simple_Network_Rename_Start' where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list"
begin

definition a\<^sub>0 where
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition a\<^sub>0' where
  "a\<^sub>0' = (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_. 0)"

(* Refine to subset of var_set? *)
lemma state_eq_aux:
  assumes "x \<notin> renum_vars ` var_set"
  shows "vars_inv x \<notin> var_set"
  unfolding vars_inv_def
proof safe
  assume "the_inv renum_vars x \<in> var_set"
  then have "renum_vars (the_inv renum_vars x) = x"
    by (intro f_the_inv_f real.inj_renum_vars) (simp add: real.surj_renum_vars)
  with assms \<open>_ \<in> var_set\<close> show False
    by force
qed

lemma state_eq:
  assumes "fst ` set s\<^sub>0 = var_set" "distinct (map fst s\<^sub>0)"
  shows "map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0) = (map_of s\<^sub>0 \<circ>\<circ>\<circ> the_inv_into) UNIV renum_vars"
    (is "?l = ?r")
proof (rule ext)
  fix x
  show "?l x = ?r x"
  proof (cases "x \<in> renum_vars ` fst ` set s\<^sub>0")
    case True
    then show ?thesis
      apply clarsimp
      apply (subst map_of_mapk_SomeI')
      subgoal
        using real.inj_renum_vars by (auto intro: inj_on_subset)
       apply (rule map_of_is_SomeI, rule assms, assumption)
      apply (simp add: the_inv_f_f[OF real.inj_renum_vars] s\<^sub>0_distinct)
      done
  next
    case False
    then have "vars_inv x \<notin> fst ` set s\<^sub>0"
      using state_eq_aux assms(1) unfolding vars_inv_def by auto
    with False show ?thesis
      apply -
      apply (frule map_of_NoneI)
      apply (simp add: vars_inv_def)
      apply (auto simp: map_of_eq_None_iff)
      done
  qed
qed

lemma start_equiv:
  "renum_bisim.A_B.equiv' a\<^sub>0 a\<^sub>0'"
  unfolding renum_bisim.A_B.equiv'_def a\<^sub>0_def a\<^sub>0'_def
  apply (clarsimp simp: vars_inv_def, intro conjI)
  subgoal
    by (intro state_eq s\<^sub>0_dom s\<^sub>0_distinct)
  subgoal
    unfolding map_u_def by auto
  subgoal
    unfolding sem_states_eq by (rule L\<^sub>0_states)
  subgoal
    using s\<^sub>0_dom dom_map_of_conv_image_fst[of s\<^sub>0] by fastforce
  done

lemma check_sexp_equiv:
  assumes "renum_bisim.A_B.equiv' (L, s, u) (L', s', u')" "locs_of_sexp e \<subseteq> {0..<n_ps}"
  shows
  "check_sexp e L (the \<circ> s) \<longleftrightarrow>
   check_sexp (map_sexp renum_states renum_vars id e) L' (the \<circ> s')"
  using assms unfolding renum_bisim.A_B.equiv'_def
  by (induction e)
     (simp add:
       inj_eq sem.states_lengthD renum_states_inj vars_inv_def the_inv_f_f[OF real.inj_renum_vars])+

lemma check_sexp_compatible:
  assumes "locs_of_sexp e \<subseteq> {0..<n_ps}"
  shows "renum_bisim.compatible
    (\<lambda>(L, s, u). check_sexp e L (the \<circ> s))
    (\<lambda>(L', s', u'). check_sexp (map_sexp renum_states renum_vars id e) L' (the \<circ> s'))"
  using check_sexp_equiv[OF _ assms] by auto

lemma has_deadlock_iff:
  "has_deadlock sem a\<^sub>0 \<longleftrightarrow> has_deadlock renum.sem a\<^sub>0'"
  unfolding has_deadlock_def using start_equiv
  by (intro renum_bisim.deadlock_iff, unfold renum_bisim.A_B.equiv'_def) auto

lemma state_formula_compatible:
  "(\<Union>x \<in> set_state_formula \<phi>. locs_of_sexp x) \<subseteq> {0..<n_ps} \<Longrightarrow>
  rel_state_formula renum_bisim.compatible
    (map_state_formula (\<lambda>P (L, s, _). check_sexp P L (the o s)) \<phi>)
    (map_state_formula (\<lambda>P (L, s, _).
      check_sexp (map_sexp (\<lambda>p. renum_states p) renum_vars id P) L (the o s))
     \<phi>)" and path_formula_compatible:
  "(\<Union>x \<in> set_path_formula \<psi>. locs_of_sexp x) \<subseteq> {0..<n_ps} \<Longrightarrow>
  rel_path_formula renum_bisim.compatible
    (map_path_formula (\<lambda>P (L, s, _). check_sexp P L (the o s)) \<psi>)
    (map_path_formula (\<lambda>P (L, s, _).
      check_sexp (map_sexp (\<lambda>p. renum_states p) renum_vars id P) L (the o s))
     \<psi>)"
   by (induction \<phi> and \<psi>) (auto simp: check_sexp_equiv prop_of_def rel_fun_def)

lemmas models_state_compatible = renum_bisim.models_state_compatible[OF state_formula_compatible]

end

locale Simple_Network_Rename_Formula_int =
  Simple_Network_Rename_Start_int where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes \<Phi> :: "(nat, 's, 'x, int) formula"
begin

definition \<Phi>' where
  "\<Phi>' = map_formula renum_states renum_vars id \<Phi>"

lemma models_iff:
  "sem,a\<^sub>0 \<Turnstile> \<Phi> = renum.sem,a\<^sub>0' \<Turnstile> \<Phi>'" if "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
proof -
  have "rel_ctl_formula renum_bisim.compatible (ctl_of \<Phi>) (ctl_of \<Phi>')"
    using that unfolding \<Phi>'_def
    by (cases \<Phi>; auto simp: check_sexp_equiv prop_of_def rel_fun_def)
  with start_equiv show ?thesis
    by (simp add: models_ctl_iff renum_bisim.CTL_compatible[THEN rel_funD, symmetric])
qed

end (* Simple Network Rename Formula int *)



lemma vars_of_bexp_finite[finite_intros]:
  "finite (vars_of_bexp (b::('a, 'b) bexp))"
and vars_of_exp_finite[finite_intros]:
  "finite (vars_of_exp (e::('a, 'b) exp))"
  by (induction b and e) auto

lemma set_bexp_vars_of_bexp:
  "set_bexp (b::('a, 'b) bexp) = vars_of_bexp b"
and set_exp_vars_of_exp:
  "set_exp (e::('a, 'b) exp) = vars_of_exp e"
  by (induction b and e) auto

definition (in Prod_TA_Defs)
  "act_set \<equiv> (\<Union> p \<in> {0..<n_ps}. \<Union> (l, e, g, a, _) \<in> trans (N p). act.set_act a) \<union> broadcast"

lemma (in Simple_Network_Impl) act_set_compute:
  "act_set =
  \<Union> ((\<lambda>(_, _, t, _). \<Union> ((\<lambda>(l, e, g, a, _). act.set_act a) ` set t)) ` set automata) \<union> set broadcast"
  unfolding act_set_def
  apply (fo_rule arg_cong2)
  apply (clarsimp simp: N_p_trans_eq n_ps_def act_set_def broadcast_def)
  apply safe
     apply (clarsimp simp: N_p_trans_eq n_ps_def act_set_def broadcast_def)
     apply (drule nth_mem, erule bexI[rotated], force)
    apply (drule mem_nth, force)
  unfolding broadcast_def
  apply simp+
  done

lemma set1_acconstraint_elim:
  assumes "c \<in> set1_acconstraint ac"
  obtains x where "(c, x) = constraint_pair ac"
  using assms by (cases ac) auto

lemma (in Simple_Network_Impl)
  assumes "(x1, x2, T, I) \<in> set automata" "(l, b, g, a, f, r, l') \<in> set T"
  shows clk_set'I1[intro]: "c \<in> set r \<Longrightarrow> c \<in> clk_set'"
    and clk_set'I2[intro]: "ac \<in> set g \<Longrightarrow> c \<in> set1_acconstraint ac \<Longrightarrow> c \<in> clk_set'"
    and loc_setI1[intro]: "l \<in> loc_set" and loc_setI2[intro]: "l' \<in> loc_set"
    and act_setI[intro]: "a' \<in> set_act a \<Longrightarrow> a' \<in> act_set"
    and var_setI1[intro]: "v \<in> set_bexp b \<Longrightarrow> v \<in> var_set"
    and var_setI2[intro]: "(x, e) \<in> set f \<Longrightarrow> x \<in> var_set"
    and var_setI3[intro]: "(x, e) \<in> set f \<Longrightarrow> v \<in> set_exp e \<Longrightarrow> v \<in> var_set"
  using assms unfolding
    loc_set_compute act_set_compute var_set_compute set_bexp_vars_of_bexp set_exp_vars_of_exp
    clk_set'_def
         apply -
         apply force
        apply (fastforce elim: set1_acconstraint_elim simp: clkp_set'_def collect_clock_pairs_def)
       apply (simp; blast)+
  done

lemma (in Simple_Network_Impl) clk_set'I3[intro]:
  assumes "(x1, x2, T, I) \<in> set automata"
  shows "(l, g') \<in> set I \<Longrightarrow> ac \<in> set g' \<Longrightarrow> c \<in> set1_acconstraint ac \<Longrightarrow> c \<in> clk_set'"
  using assms unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
  by (force elim!: set1_acconstraint_elim)


definition
  "find_remove P = map_option (\<lambda>(xs, x, ys). (x, xs @ ys)) o List.extract P"

fun merge_pairs :: "('a \<times> 'b list) list \<Rightarrow> ('a \<times> 'b list) list \<Rightarrow> ('a \<times> 'b list) list" where
  "merge_pairs [] ys = ys" |
  "merge_pairs ((k, v) # xs) ys = (case find_remove (\<lambda>(k', _). k' = k) ys of
    None \<Rightarrow> (k, v) # merge_pairs xs ys
  | Some ((_, v'), ys) \<Rightarrow> (k, v @ v') # merge_pairs xs ys
  )"

(*
definition
  "conv_urge urge \<equiv> \<lambda>(committed, urgent, trans, inv).
    (committed,
     [],
     map (\<lambda>(l, b, g, a, f, r, l'). (l, b, g, a, f, urge # r, l')) trans,
     map (\<lambda>(l, cc). (l, if l \<in> set urgent then acconstraint.LE urge 0 # cc else cc)) inv)"
*)

definition
  "conv_urge urge \<equiv> \<lambda>(committed, urgent, trans, inv).
    (committed,
     [],
     map (\<lambda>(l, b, g, a, f, r, l'). (l, b, g, a, f, urge # r, l')) trans,
     merge_pairs (map (\<lambda>l. (l, [acconstraint.LE urge 0])) urgent) inv)"

(* Generalized version. Move to library *)
lemma map_of_distinct_upd2:
  assumes "x \<notin> set (map fst xs)"
  shows "map_of (xs @ (x,y) # ys) = (map_of (xs @ ys))(x \<mapsto> y)"
  using assms by (induction xs) auto

(* Generalized version. Move to library *)
lemma map_of_distinct_lookup:
  assumes "x \<notin> set (map fst xs)"
  shows "map_of (xs @ (x,y) # ys) x = Some y"
  using map_of_distinct_upd2[OF assms] by auto

lemma find_remove_SomeD:
  assumes "find_remove P xs = Some (x, ys)"
  shows "\<exists>as bs. xs = as @ x # bs \<and> ys = as @ bs \<and> (\<forall>x \<in> set as. \<not> P x) \<and> P x"
  using assms unfolding find_remove_def by (auto dest: extract_SomeE)

lemma find_map:
  "find Q (map f xs) = map_option f (find P xs)" if "\<forall>x \<in> set xs. Q (f x) \<longleftrightarrow> P x"
  using that by (induction xs) auto

lemma find_remove_map:
  "find_remove Q (map f xs) = map_option (\<lambda>(x, xs). (f x, map f xs)) (find_remove P xs)"
  if "\<forall>x \<in> set xs. Q (f x) \<longleftrightarrow> P x"
  using that
  by (induction xs)
     (auto simp: find_remove_def extract_Nil_code extract_Cons_code split: option.split)

lemma map_merge_pairs2:
  "map (\<lambda>(k, v). (g k, map f v)) (merge_pairs xs ys)
  = merge_pairs (map (\<lambda>(k, v). (g k, map f v)) xs) (map (\<lambda>(k, v). (g k, map f v)) ys)"
  if inj: "inj_on g (fst ` (set xs \<union> set ys))"
proof -
  have *:
    "find_remove (\<lambda>(k', _). k' = g k) (map (\<lambda>(k, v). (g k, map f v)) ys)
   = map_option
      (\<lambda>((k, v), ys). ((g k, map f v), map (\<lambda>(k, v). (g k, map f v)) ys))
      (find_remove (\<lambda>(k', _). k' = k) ys)"
    if "inj_on g (fst ` (set xs \<union> set ys))" "k \<in> fst ` set xs" for k xs ys
    using that
    by (subst find_remove_map[where P = "(\<lambda>(k', _). k' = k)"])
      (auto elim: inj_onD[rotated, where A = "fst ` (set xs \<union> set ys)"]
        intro!: arg_cong2[where f = map_option])
  show ?thesis
    using inj
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      apply (clarsimp split: prod.split option.split simp: *[OF Cons(2)])
      apply (subst Cons.IH)
       apply (drule find_remove_SomeD)
       apply auto
      done
  qed
qed

lemma map_merge_pairs:
  "map (\<lambda>(k, v). (k, map f v)) (merge_pairs xs ys)
  = merge_pairs (map (\<lambda>(k, v). (k, map f v)) xs) (map (\<lambda>(k, v). (k, map f v)) ys)"
  using map_merge_pairs2[where g = id] by auto

lemma map_map_commute:
  "map f (map g xs) = map g (map f xs)" if "\<forall>x \<in> set xs. f (g x) = g (f x)"
  using that by simp

lemma conv_automaton_conv_urge_commute:
  "conv_automaton (conv_urge c A) = conv_urge c (conv_automaton A)"
  unfolding comp_def conv_automaton_def conv_urge_def
  by (simp split: prod.split add: map_merge_pairs comp_def)

lemma conv_automaton_conv_urge_commute':
  "conv_automaton o conv_urge c = conv_urge c o conv_automaton"
  unfolding comp_def conv_automaton_conv_urge_commute ..

locale Simple_Network_Rename_Defs_int_urge =
  Simple_Network_Rename_Defs_int where automata = automata for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list"
  + fixes urge :: 'c

lemma (in Simple_Network_Rename_Defs) conv_automaton_of:
  "Simple_Network_Language.conv_A (automaton_of A) = automaton_of (conv_automaton A)"
  unfolding automaton_of_def conv_automaton_def
    Simple_Network_Language.conv_A_def
  by (force
      simp: default_map_of_alt_def map_of_map Simple_Network_Language.conv_t_def split: prod.splits
     )

locale Simple_Network_Rename =
  Simple_Network_Rename_Defs_int_urge where automata = automata for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj: "inj_on renum_clocks (insert urge clk_set')"
  and renum_vars_inj:   "inj_on renum_vars var_set"
  and renum_acts_inj: "inj_on renum_acts act_set"
  and infinite_types:
    "infinite (UNIV :: 'c set)" "infinite (UNIV :: 'x set)" "infinite (UNIV :: 's set)"
    "infinite (UNIV :: 'a set)"
  and bounds'_var_set: "fst ` set bounds' = var_set"
  and loc_set_invs: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd o snd) automata)) \<subseteq> loc_set"
  and loc_set_committed: "\<Union> ((set o fst) ` set automata) \<subseteq> loc_set"
  and loc_set_urgent: "\<Union> ((set o (fst o snd)) ` set automata) \<subseteq> loc_set"
  and urge_not_in_clk_set: "urge \<notin> clk_set'"
begin

lemma clk_set'_finite:
  "finite clk_set'"
  unfolding clk_set'_def unfolding clkp_set'_def by (intro finite_intros) auto

lemmas [finite_intros] = trans_N_finite

lemma set_act_finite[finite_intros]:
  "finite (set_act a)"
  by (cases a) auto

lemma loc_set_finite:
  "finite loc_set"
  unfolding loc_set_def by (auto intro!: finite_intros)

lemma var_set_finite[finite_intros]:
  "finite var_set"
  unfolding var_set_def by (auto intro!: finite_intros)

lemma act_set_finite:
  "finite act_set"
  unfolding act_set_def broadcast_def by (auto intro!: finite_intros)

lemma bij_extend_bij_renum_clocks:
  "bij (extend_bij renum_clocks (insert urge clk_set'))"
  by (intro extend_bij_bij renum_clocks_inj clk_set'_finite infinite_types finite.insertI) simp

lemma renum_vars_bij_extends[simp]:
  "extend_bij renum_vars var_set x = renum_vars x" if "x \<in> var_set"
  by (intro extend_bij_extends[rule_format] renum_vars_inj var_set_finite infinite_types that)

lemma bij_extend_bij_renum_states:
  "bij (extend_bij renum_vars var_set)"
  by (intro extend_bij_bij renum_vars_inj var_set_finite infinite_types) simp

lemma inj_extend_bij_renum_states: "inj (extend_bij (renum_states p) loc_set)" if "p < n_ps"
  using renum_states_inj infinite_types loc_set_finite \<open>p < n_ps\<close>
  by (intro extend_bij_inj) (auto intro!: inj_onI)

lemma renum_states_extend:
  "extend_bij (renum_states p) loc_set l = renum_states p l" if "l \<in> loc_set" "p < n_ps"
  using renum_states_inj infinite_types loc_set_finite \<open>p < n_ps\<close> \<open>l \<in> loc_set\<close>
  by (intro extend_bij_extends[rule_format]) (auto intro!: inj_onI)

lemma renum_acts_bij_extends[simp]:
  "extend_bij renum_acts act_set x = renum_acts x" if "x \<in> act_set"
  by (intro extend_bij_extends[rule_format] renum_acts_inj act_set_finite infinite_types that)

lemma inj_extend_bij_renum_acts: "inj (extend_bij renum_acts act_set)"
  using renum_acts_inj infinite_types act_set_finite by (intro extend_bij_inj) auto

lemma constraint_clk_conv_ac:
  "constraint_clk (conv_ac ac) = constraint_clk ac"
  by (cases ac) auto

interpretation urge: Prod_TA_sem_urge
  "(set broadcast, map (Simple_Network_Language.conv_A o automaton_of) automata, map_of bounds')"
  urge
  apply (standard; clarsimp)
  subgoal
    using urge_not_in_clk_set
    unfolding conv_automaton_of
    unfolding automaton_of_def conv_automaton_def
    apply (clarsimp split: prod.split_asm)
    apply (drule default_map_of_in_listD)
    unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
    apply clarsimp
    subgoal premises prems
      using prems(1,7,8,10)
      unfolding constraint_clk_conv_ac unfolding constraint_clk_constraint_pair
      by force
    done
  subgoal
    using urge_not_in_clk_set
    unfolding conv_automaton_of
    unfolding automaton_of_def conv_automaton_def
    apply (clarsimp split: prod.split_asm)
    unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
    unfolding constraint_clk_conv_ac unfolding constraint_clk_constraint_pair
    apply force
    done

  subgoal
    using urge_not_in_clk_set
    unfolding conv_automaton_of
    unfolding automaton_of_def conv_automaton_def
    apply (clarsimp split: prod.split_asm)
    unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
    apply force
    done
  done


sublocale rename: Simple_Network_Rename_Defs_int
  broadcast bounds'
  "extend_bij renum_acts act_set"
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks (insert urge clk_set')"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  "map (conv_urge urge) automata"
  .

sublocale rename: Simple_Network_Rename_int
  broadcast bounds'
  "extend_bij renum_acts act_set"
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks (insert urge clk_set')"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  "map (conv_urge urge) automata"
  apply (standard;
      (intro allI impI bij_extend_bij_renum_clocks inj_extend_bij_renum_states
        inj_extend_bij_renum_acts bij_extend_bij_renum_states bounds'_var_set)?)
    apply (simp add: Prod_TA_Defs.n_ps_def; fail)
  subgoal
    unfolding bounds'_var_set rename.var_set_compute var_set_compute unfolding conv_urge_def
    by (fo_rule arg_cong2; fastforce)
  subgoal
    unfolding conv_urge_def by auto
  done

definition
  "renum_upd' = map (\<lambda>(x, upd). (renum_vars x, map_exp renum_vars upd))"

definition
  "renum_reset' = map renum_clocks"

definition renum_automaton' where
  "renum_automaton' i \<equiv> \<lambda>(committed, trans, inv). let
    committed' = map (renum_states i) committed;
    trans' = map (\<lambda>(l, g, a, upd, r, l').
      (renum_states i l,
      map_cconstraint renum_clocks id g, renum_act a, renum_upd' upd, map renum_clocks r, 
      renum_states i l')
    ) trans;
    inv' = map (\<lambda>(l, g). (renum_states i l, map_cconstraint renum_clocks id g)) inv
  in (committed', trans', inv')
"

lemmas renum_automaton'_alt_def = renum_automaton'_def[unfolded
  renum_reset'_def renum_upd'_def map_cconstraint_def renum_act_def
  ]

lemma renum_automaton_eq:
  "rename.renum_automaton p (automata ! p) = renum_automaton p (automata ! p)"
  if "p < n_ps"
proof -
  have renum_clocks: "extend_bij renum_clocks (insert urge clk_set') c = renum_clocks c"
    if "c \<in> clk_set'" for c
    apply (rule extend_bij_extends[rule_format])
       apply (rule renum_clocks_inj clk_set'_finite finite.insertI)+
    using that infinite_types by auto
  have renum_cconstraint: "rename.renum_cconstraint g = renum_cconstraint g"
    if "\<Union> (set1_acconstraint ` (set g)) \<subseteq> clk_set'" for g
    unfolding rename.renum_cconstraint_def renum_cconstraint_def map_cconstraint_def
    apply (rule map_cong, rule HOL.refl)
    apply (rule acconstraint.map_cong_pred, rule HOL.refl)
    using that
    apply (auto intro: renum_clocks[simplified] simp: pred_acconstraint_def)
    done
  show ?thesis
    using that[folded length_automata_eq_n_ps]
    unfolding rename.renum_automaton_def renum_automaton_def
    apply (clarsimp split: prod.split)
    apply safe
    subgoal committed
      using loc_set_committed
      by (subst renum_states_extend) (auto 4 3 simp: n_ps_def dest!: nth_mem)
    subgoal urgent
      using loc_set_urgent
      by (subst renum_states_extend) (auto 4 3 simp: n_ps_def dest!: nth_mem)
    subgoal start_locs
      by (subst renum_states_extend) (auto simp: n_ps_def dest!: nth_mem)
    subgoal state
      unfolding rename.renum_bexp_def renum_bexp_def
      by (auto dest!: nth_mem intro!: renum_vars_bij_extends bexp.map_cong_pred simp: pred_bexp_def)
    subgoal guards
      by (auto dest!: nth_mem intro!: renum_cconstraint)
    subgoal actions
      unfolding rename.renum_act_def renum_act_def
      by (auto simp: pred_act_def dest!: nth_mem intro!: renum_acts_bij_extends act.map_cong_pred)
    subgoal upds
      unfolding renum_upd_def rename.renum_upd_def rename.renum_exp_def renum_exp_def
      by (auto dest!: nth_mem intro!: renum_vars_bij_extends exp.map_cong_pred simp: pred_exp_def)
    subgoal clock_resets
      unfolding rename.renum_reset_def renum_reset_def by (auto dest!: nth_mem intro!: renum_clocks)
    subgoal dest_locs
      by (subst renum_states_extend) (auto simp: n_ps_def dest!: nth_mem)
    subgoal inv_locs
      using loc_set_invs
      by (subst renum_states_extend) (auto 4 4 simp: n_ps_def dest!: nth_mem)
    subgoal renum_clocks
      by (auto dest!: nth_mem intro!: renum_cconstraint)
    done
qed

lemma renum_urge_automaton_eq1:
  "renum_automaton p (conv_urge urge (automata ! p))
  = conv_urge (renum_clocks urge) (renum_automaton p (automata ! p))" if "p < n_ps"
  unfolding renum_automaton_def conv_urge_def
  apply (simp split: prod.split)
  apply safe
  subgoal
    unfolding renum_reset_def by simp
  unfolding renum_cconstraint_def map_cconstraint_def
  apply (subst map_merge_pairs2)
  subgoal
    using loc_set_urgent loc_set_invs \<open>p < n_ps\<close> unfolding inj_on_def n_ps_def
    by (auto; force
        elim!: renum_states_inj[unfolded n_ps_def, simplified, rule_format, rotated -1]
        intro: nth_mem)
  apply (fo_rule arg_cong2; simp)
  done

lemma renum_urge_automaton_eq2:
  "rename.real.renum_automaton p (conv_urge urge (automata ! p))
  = conv_urge
      (extend_bij renum_clocks (insert urge clk_set') urge)
      (rename.renum_automaton p (automata ! p))"
  if "p < n_ps"
  unfolding rename.renum_automaton_def conv_urge_def
  apply (simp split: prod.split)
  apply safe
  subgoal
    unfolding rename.renum_reset_def by simp
  unfolding rename.renum_cconstraint_def map_cconstraint_def
  apply (subst map_merge_pairs2)
  subgoal
    by (rule inj_extend_bij_renum_states that subset_UNIV inj_on_subset)+
  apply (fo_rule arg_cong2)
   apply simp+
  done

lemma renum_urge_automaton_eq:
  "rename.real.renum_automaton p (conv_urge urge (automata ! p)) =
   renum_automaton p (conv_urge urge (automata ! p))" if "p < n_ps"
  using that
  unfolding renum_urge_automaton_eq1[OF that] renum_urge_automaton_eq2[OF that]
  apply (fo_rule arg_cong2)
  subgoal
    by (intro
      extend_bij_extends[rule_format] renum_clocks_inj clk_set'_finite finite.insertI infinite_types
      ) auto
  by (rule renum_automaton_eq)

lemma rename_N_eq_sem:
  "rename.renum.sem =
  Simple_Network_Language_Model_Checking.N
    (map renum_acts broadcast)
    (map_index renum_automaton (map (conv_urge urge) automata))
    (map (\<lambda>(a,p). (renum_vars a,p)) bounds')
  "
  unfolding rename.renum.sem_def
  unfolding Simple_Network_Language.conv_def
  apply simp
  apply (intro conjI)
  subgoal
    by (rule image_cong; intro HOL.refl renum_acts_bij_extends; simp add: act_set_def broadcast_def)
  subgoal
    apply (rule map_index_cong)
    unfolding conv_automaton_of
    apply safe
    apply (fo_rule arg_cong)+
    apply (erule renum_urge_automaton_eq[folded length_automata_eq_n_ps])
    done
  subgoal
    using bounds'_var_set by - (fo_rule arg_cong, auto intro: renum_vars_bij_extends)
  done

lemma map_of_merge_pairs:
  "map_of (merge_pairs xs ys) = (\<lambda>x.
  (if x \<in> fst ` set xs \<and> x \<in> fst ` set ys then Some (the (map_of xs x) @ the (map_of ys x))
   else if x \<in> fst ` set xs then map_of xs x
   else map_of ys x))"
proof -
  have 1: False if "find_remove (\<lambda>(k', _). k' = k) ys = None" "(k, x) \<in> set ys" for k x ys
    using that unfolding find_remove_def by (auto simp: extract_None_iff)
  have 2: "map_of xs k = Some x" if
    "find_remove (\<lambda>(k', _). k' = k) xs = Some ((k', x), ys)" for k k' x xs ys
    using that
    by (auto 4 4 split: option.split dest: map_of_SomeD find_remove_SomeD simp: map_add_def)
  show ?thesis
    apply (rule ext)
    apply (induction xs arbitrary: ys)
     apply (simp; fail)
    apply (clarsimp split: if_split_asm option.split)
    apply (auto 4 3 split: option.split simp: map_add_def dest: find_remove_SomeD 2 1)
    done
qed

lemma default_map_of_merge_pairs:
  "default_map_of [] (merge_pairs xs ys) = (\<lambda>x.
  (if x \<in> fst ` set xs then the (map_of xs x) @ default_map_of [] ys x
   else default_map_of [] ys x))"
  unfolding default_map_of_alt_def map_of_merge_pairs
  by (rule ext) (auto 4 3 dest: map_of_SomeD weak_map_of_SomeI split: if_split_asm)

lemma automaton_of_conv_urge_commute:
  "automaton_of (conv_urge urge A) = urge.add_reset (urge.add_inv (automaton_of A))"
  unfolding conv_urge_def urge.add_reset_def urge.add_inv_def automaton_of_def
  apply (clarsimp split: prod.splits)
  apply (rule ext)
  unfolding default_map_of_merge_pairs
  apply (clarsimp, safe)
  apply (clarsimp)
  subgoal premises prems for _ urgent _ _ l
  proof -
    have *: "map_of (map (\<lambda>x. (x, [acconstraint.LE urge 0])) urgent)
      = (\<lambda>l. if l \<in> set urgent then Some [acconstraint.LE urge 0] else None)"
      using map_of_map_keys[where
          m = "\<lambda>l. if l \<in> set urgent then Some [acconstraint.LE urge 0] else None"]
      by (force cong: map_cong simp: dom_def)
    from \<open>l \<in> set urgent\<close> show ?thesis
      by (subst *) auto
  qed
  by auto

lemma urge_commute:
  "rename.sem = urge.A_urge"
  unfolding rename.sem_def urge.A_urge_def
  apply simp
  unfolding conv_automaton_conv_urge_commute conv_automaton_of automaton_of_conv_urge_commute
  by fast

lemma conv_automaton_of':
  "automaton_of \<circ> conv_automaton = Simple_Network_Language.conv_A o automaton_of"
  unfolding comp_def conv_automaton_of ..

sublocale urge_bisim: Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' rename.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = L \<and> s' = s \<and> u' = u(urge := 0)"
  "\<lambda> (L, s, u). L \<in> states" "\<lambda>(L, s, u). True"
  unfolding urge_commute sem_def conv_automaton_of' by (rule urge.urge_bisim[unfolded conv_states])

lemma check_sexp_equiv:
  assumes "urge_bisim.A_B.equiv' (L, s, u) (L', s', u')"
  shows "check_sexp e L (the o s) = check_sexp e L' (the o s')"
  using assms unfolding urge_bisim.A_B.equiv'_def by simp

context
  fixes a\<^sub>0 :: "'s list \<times> ('x \<Rightarrow> int option) \<times> ('c \<Rightarrow> real)"
  assumes start: "fst a\<^sub>0 \<in> states" "snd (snd a\<^sub>0) urge = 0"
begin

lemma start_equiv: "urge_bisim.A_B.equiv' a\<^sub>0 a\<^sub>0"
  using start unfolding urge_bisim.A_B.equiv'_def by auto

lemma urge_models_iff:
  "sem,a\<^sub>0 \<Turnstile> \<Phi> \<longleftrightarrow> rename.sem,a\<^sub>0 \<Turnstile> \<Phi>"
proof -
  have "rel_ctl_formula urge_bisim.compatible (ctl_of \<Phi>) (ctl_of \<Phi>)"
    by (cases \<Phi>) (auto simp: prop_of_def rel_fun_def check_sexp_equiv)
  with start_equiv show ?thesis
    by (simp only: models_ctl_iff urge_bisim.CTL_compatible[THEN rel_funD, symmetric])
qed

lemma urge_has_deadlock_iff:
  "has_deadlock sem a\<^sub>0 \<longleftrightarrow> has_deadlock rename.sem a\<^sub>0"
  unfolding has_deadlock_def using start_equiv
  by (intro urge_bisim.deadlock_iff, unfold urge_bisim.A_B.equiv'_def) auto

lemma state_formula_compatible:
  "(\<Union>x \<in> set_state_formula \<phi>. locs_of_sexp x) \<subseteq> {0..<n_ps} \<Longrightarrow>
  rel_state_formula urge_bisim.compatible
    (map_state_formula (\<lambda>P (L, s, _). check_sexp P L (the o s)) \<phi>)
    (map_state_formula (\<lambda>P (L, s, _). check_sexp P L (the o s)) \<phi>)" and path_formula_compatible:
  "(\<Union>x \<in> set_path_formula \<psi>. locs_of_sexp x) \<subseteq> {0..<n_ps} \<Longrightarrow>
  rel_path_formula urge_bisim.compatible
    (map_path_formula (\<lambda>P (L, s, _). check_sexp P L (the o s)) \<psi>)
    (map_path_formula (\<lambda>P (L, s, _). check_sexp P L (the o s)) \<psi>)"
   by (induction \<phi> and \<psi>) (auto simp: check_sexp_equiv prop_of_def rel_fun_def)

lemmas urge_models_state_compatible =
  urge_bisim.models_state_compatible[OF state_formula_compatible]

end (* Start State *)

end (* Simple_Network_Rename *)


locale Simple_Network_Rename_Start =
  Simple_Network_Rename where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes s\<^sub>0 :: "('x \<times> int) list"
    and L\<^sub>0 :: "'s list"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
      and s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
begin

lemma rename_n_ps_eq:
  "rename.n_ps = n_ps"
  unfolding rename.length_automata_eq_n_ps[symmetric] n_ps_def by simp

lemma rename_states_eq:
  "rename.states = states"
  unfolding rename.states_def states_def rename_n_ps_eq
  by (simp add: rename.N_eq[unfolded rename_n_ps_eq] N_eq n_ps_def del: map_map)
     (auto simp: automaton_of_def conv_urge_def trans_def split: prod.splits)

lemma state_eq:
  "map_of (map (\<lambda>(x, y). (extend_bij renum_vars var_set x, y)) s\<^sub>0) =
    map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0)"
  using s\<^sub>0_dom by - (rule arg_cong, auto intro: renum_vars_bij_extends)

lemma sexp_eq:
  assumes
    \<open>vars_of_sexp e \<subseteq> var_set\<close>
    \<open>set2_sexp e \<subseteq> loc_set\<close>
    \<open>locs_of_sexp e \<subseteq> {0..<n_ps}\<close>
  shows \<open>map_sexp (\<lambda>p. extend_bij (renum_states p) loc_set) (extend_bij renum_vars var_set) id e =
         map_sexp renum_states renum_vars id e\<close>
  using assms by (induction e; clarsimp simp: renum_states_extend)

lemma L\<^sub>0_dom:
  "length L\<^sub>0 = n_ps" "set L\<^sub>0 \<subseteq> loc_set"
  using L\<^sub>0_states by (auto intro!: states_loc_setD)

definition
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition
  "a\<^sub>0' = (
    map_index (\<lambda>p. renum_states p) L\<^sub>0,
    map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0),
    \<lambda>_. 0)"

sublocale rename: Simple_Network_Rename_Start_int
  broadcast bounds'
  "extend_bij renum_acts act_set"
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks (insert urge clk_set')"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  s\<^sub>0 L\<^sub>0
  "map (conv_urge urge) automata"
  apply (standard; (rule L\<^sub>0_states[folded rename_states_eq] s\<^sub>0_distinct)?)
  unfolding s\<^sub>0_dom rename.bounds'_var_set[symmetric] bounds'_var_set ..

lemma rename_a\<^sub>0_eq:
  "rename.a\<^sub>0 = a\<^sub>0"
  unfolding rename.a\<^sub>0_def a\<^sub>0_def ..

lemma rename_a\<^sub>0'_eq:
  "rename.a\<^sub>0' = a\<^sub>0'"
  unfolding a\<^sub>0'_def rename.a\<^sub>0'_def
  apply (clarsimp, rule conjI)
  subgoal
    using L\<^sub>0_dom by (auto intro!: map_index_cong renum_states_extend)
  subgoal
    unfolding vars_inv_def using s\<^sub>0_dom s\<^sub>0_distinct
    by (auto simp: state_eq Simple_Network_Rename_Defs.vars_inv_def)
  done

lemma has_deadlock_iff:
  "has_deadlock rename.renum.sem a\<^sub>0' \<longleftrightarrow> has_deadlock sem a\<^sub>0"
proof -
  have "has_deadlock sem a\<^sub>0 \<longleftrightarrow> has_deadlock rename.sem a\<^sub>0"
    by (rule urge_has_deadlock_iff) (auto intro: L\<^sub>0_states simp: a\<^sub>0_def)
  also have "\<dots> \<longleftrightarrow> has_deadlock rename.renum.sem a\<^sub>0'"
    by (rule rename.has_deadlock_iff[unfolded rename_a\<^sub>0_eq rename_a\<^sub>0'_eq])
  finally show ?thesis ..
qed

lemma N_eq_sem:
  "Simple_Network_Language_Model_Checking.N broadcast automata bounds' = sem"
  unfolding conv_alt_def sem_def
  by safe (rule nth_equalityI; simp add: conv_N_eq N_eq sem_N_eq conv_automaton_of n_ps_def)

lemma rename_N_eq_sem':
  "Simple_Network_Language_Model_Checking.N
    (map renum_acts broadcast)
    (map_index renum_automaton automata)
    (map (\<lambda>(a,p). (renum_vars a,p)) bounds')
  = renum.sem"
  unfolding renum.sem_def
  unfolding renum.conv_alt_def
  by safe (rule nth_equalityI; simp add: conv_N_eq N_eq sem_N_eq conv_automaton_of n_ps_def)

lemmas has_deadlock_iff' =
  has_deadlock_iff[unfolded rename_N_eq_sem, folded N_eq_sem, unfolded a\<^sub>0_def a\<^sub>0'_def]

lemmas start_equiv = start_equiv[of a\<^sub>0, unfolded a\<^sub>0_def, simplified, OF L\<^sub>0_states]

lemmas urge_models_state_compatible =
  urge_models_state_compatible[THEN rel_funD, OF _ _ _ start_equiv,
    of a\<^sub>0, unfolded a\<^sub>0_def, simplified, OF L\<^sub>0_states]

lemmas rename_models_state_compatible =
  rename.models_state_compatible[THEN rel_funD, OF _ rename.start_equiv,
    unfolded rename_a\<^sub>0_eq a\<^sub>0_def rename_n_ps_eq rename_a\<^sub>0'_eq a\<^sub>0'_def]

lemmas models_state_compatible =
  transp_on_equality[THEN transpD, OF urge_models_state_compatible rename_models_state_compatible]

lemmas models_state_compatible' = models_state_compatible[unfolded rename_N_eq_sem, folded N_eq_sem]

end

locale Simple_Network_Rename_Formula =
  Simple_Network_Rename_Start where automata = automata
  for automata ::
    "('s list \<times> 's list
      \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes \<Phi> :: "(nat, 's, 'x, int) formula"
  assumes formula_dom:
    "set2_formula \<Phi> \<subseteq> loc_set"
    "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
    "vars_of_formula \<Phi> \<subseteq> var_set"
begin

sublocale rename: Simple_Network_Rename_Formula_int
  broadcast bounds'
  "extend_bij renum_acts act_set"
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks (insert urge clk_set')"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  s\<^sub>0 L\<^sub>0
  "map (conv_urge urge) automata"
  apply (standard; (rule L\<^sub>0_states[folded rename_states_eq] s\<^sub>0_distinct)?)
  unfolding s\<^sub>0_dom rename.bounds'_var_set[symmetric] bounds'_var_set .

definition
  "\<Phi>' = map_formula (\<lambda>p. renum_states p) renum_vars id \<Phi>"

lemma rename_\<Phi>'_eq:
  "rename.\<Phi>' = \<Phi>'"
  using formula_dom unfolding rename.\<Phi>'_def \<Phi>'_def by (induction \<Phi>; clarsimp simp: sexp_eq)

lemma models_iff1:
  "rename.renum.sem,a\<^sub>0' \<Turnstile> \<Phi>' \<longleftrightarrow> rename.sem,a\<^sub>0 \<Turnstile> \<Phi>"
  by (intro rename.models_iff[unfolded rename_a\<^sub>0_eq rename_a\<^sub>0'_eq rename_\<Phi>'_eq rename_n_ps_eq]
       formula_dom sym)

lemma models_iff2:
  "rename.sem,a\<^sub>0 \<Turnstile> \<Phi> \<longleftrightarrow> sem,a\<^sub>0 \<Turnstile> \<Phi>"
  by (rule sym, intro urge_models_iff formula_dom) (auto intro: formula_dom L\<^sub>0_states simp: a\<^sub>0_def)

lemma models_iff:
  "rename.renum.sem,a\<^sub>0' \<Turnstile> \<Phi>' \<longleftrightarrow> sem,a\<^sub>0 \<Turnstile> \<Phi>"
  unfolding models_iff1 models_iff2 ..

lemmas models_iff' =
  models_iff[unfolded rename_N_eq_sem, folded N_eq_sem, unfolded a\<^sub>0_def a\<^sub>0'_def \<Phi>'_def]

end (* Simple_Network_Rename_Formula *)

end (* Theory *)