(* Author: Felipe Escallon and Tobias Nipkow *)

theory Two_Way_DFA_HF       
  imports "Finite_Automata_HF.Finite_Automata_HF"
begin

text \<open>A formalization of two-way deterministic finite automata (2DFA), 
based on Paulson's theory of DFAs using hereditarily finite sets \<^cite>\<open>Paulson\<close>.
Both the definition of 2DFAs and the proof follow Kozen \<^cite>\<open>Kozen\<close>.\<close>

section \<open>Definition of Two-Way Deterministic Finite Automata\<close>

subsection \<open>Basic Definitions\<close>

type_synonym state = hf

datatype dir = Left | Right

text \<open>Left and right markers to prevent the 2DFA from reading out of bounds. The input for a 2DFA 
      with alphabet \<open>\<Sigma>\<close> is \<open>\<turnstile>w\<stileturn>\<close> for some \<open>w \<in> \<Sigma>\<^sup>*\<close>. Note that \<open>\<turnstile>,\<stileturn> \<notin> \<Sigma>\<close>:\<close>

datatype 'a symbol = Letter 'a | Marker dir

abbreviation left_marker :: "'a symbol" ("\<turnstile>") where
  "\<turnstile> \<equiv> Marker Left"

abbreviation right_marker :: "'a symbol" ("\<stileturn>") where
  "\<stileturn> \<equiv> Marker Right"

record 'a dfa2 = states :: "state set"
                 init   :: "state"
                 acc    :: "state"
                 rej    :: "state"
                 nxt    :: "state \<Rightarrow> 'a symbol \<Rightarrow> state \<times> dir"


text \<open>2DFA configurations. A 2DFA \<open>M\<close> is in a configuration \<open>(u, q, v)\<close> if \<open>M\<close> is in state \<open>q\<close>,
      reading \<open>hd v\<close>, the substring \<open>rev u\<close> is to the left and \<open>tl v\<close> is to the right:\<close>

type_synonym 'a config = "'a symbol list \<times> state \<times> 'a symbol list"

text \<open>Some abbreviations to guarantee the validity of the input:\<close>

abbreviation \<Sigma> :: "'a list \<Rightarrow>'a symbol list" where
  "\<Sigma> w \<equiv> map Letter w"

abbreviation marker_map :: "'a list \<Rightarrow> 'a symbol list" ("\<langle>_\<rangle>" 70) where
  "\<langle>w\<rangle> \<equiv> \<turnstile> # (\<Sigma> w) @ [\<stileturn>]"

abbreviation marker_mapl :: "'a list \<Rightarrow> 'a symbol list" ("\<langle>_\<langle>" 70) where
  "\<langle>w\<langle> \<equiv> \<turnstile> # (\<Sigma> w)"

abbreviation marker_mapr :: "'a list \<Rightarrow> 'a symbol list" ("\<rangle>_\<rangle>" 70) where
  "\<rangle>w\<rangle> \<equiv> (\<Sigma> w) @ [\<stileturn>]"

lemma mapl_app_mapr_eq_map: 
  "\<langle>u\<langle> @ \<rangle>v\<rangle> = \<langle>u @ v\<rangle>" by simp

subsection \<open>Steps and Reachability\<close>

locale dfa2 =
  fixes M :: "'a dfa2"
  assumes init:         "init M \<in> states M"
      and accept:       "acc M \<in> states M"
      and reject:       "rej M \<in> states M"
      and neq_final:    "acc M \<noteq> rej M"
      and finite:       "finite (states M)"
      and nxt:          "\<lbrakk>q \<in> states M; nxt M q x = (p, d)\<rbrakk> \<Longrightarrow> p \<in> states M"
      and left_nxt:     "\<lbrakk>q \<in> states M; nxt M q \<turnstile> = (p, d)\<rbrakk> \<Longrightarrow> d = Right"
      and right_nxt:    "\<lbrakk>q \<in> states M; nxt M q \<stileturn> = (p, d)\<rbrakk> \<Longrightarrow> d = Left"
      and final_nxt_r:  "\<lbrakk>x \<noteq> \<stileturn>; q = acc M \<or> q = rej M\<rbrakk> \<Longrightarrow> nxt M q x = (q, Right)"
      and final_nxt_l:  "q = acc M \<or> q = rej M \<Longrightarrow> nxt M q \<stileturn> = (q, Left)"
begin

text \<open>A single \<close>
inductive step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55) where
  step_left[intro]:  "nxt M p a = (q, Left) \<Longrightarrow> (x # xs, p, a # ys) \<rightarrow> (xs, q, x # a # ys)" |
  step_right[intro]: "nxt M p a = (q, Right) \<Longrightarrow> (xs, p, a # ys) \<rightarrow> (a # xs, q, ys)"


inductive_cases step_foldedE[elim]: "a \<rightarrow> b"
inductive_cases step_leftE [elim]:  "(a#u, q, v) \<rightarrow> (u, p, a#v)"
inductive_cases step_rightE [elim]: "(u, q, a#v) \<rightarrow> (a#u, p, v)"

text \<open>The reflexive transitive closure of \<open>\<rightarrow>\<close>:\<close>
abbreviation steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

text \<open>And the nth power of \<open>\<rightarrow>\<close>:\<close>
abbreviation stepn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>'(_') _" 55) where
  "stepn c n \<equiv> (step ^^ n) c"

lemma rtranclp_induct3[consumes 1, case_names refl step]:
  "\<lbrakk>r\<^sup>*\<^sup>* (ax, ay, az) (bx, by, bz); P ax ay az;
     \<And>u p v x q z.
        \<lbrakk>r\<^sup>*\<^sup>* (ax, ay, az) (u, p, v); r (u, p, v) (x, q, z); P u p v\<rbrakk>
        \<Longrightarrow> P x q z\<rbrakk>
    \<Longrightarrow> P bx by bz"
by (rule rtranclp_induct[of _ "(ax, ay, az)" "(bx, by, bz)", split_rule])

text \<open>The initial configuration of \<open>M\<close> on input word \<open>w \<in> \<Sigma>\<^sup>*\<close> is \<open>([], init M, \<turnstile>w\<stileturn>)\<close>. 
      A configuration \<open>c\<close> is reachable by \<open>w\<close> if the initial configuration of \<open>M\<close> on input \<open>w\<close>
      reaches \<open>c\<close>:\<close>
abbreviation reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>**\<close> 55) where
  "w \<rightarrow>** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>* c" 

abbreviation nreachable :: "'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>*'(_') _" 55) where
  "nreachable w n c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>(n) c"

lemma step_unique:
  "\<lbrakk> c0 \<rightarrow> c1; c0 \<rightarrow> c2 \<rbrakk> \<Longrightarrow> c1 = c2"
by fastforce

lemma steps_impl_in_states:
  assumes "p \<in> states M"
  shows "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> q \<in> states M"
by (induction rule: rtranclp_induct3) (use assms nxt in auto)

corollary reachable_impl_in_states:
  "w \<rightarrow>** (u, q, v) \<Longrightarrow> q \<in> states M"
using init steps_impl_in_states by blast


subsection \<open>Basic Properties of 2DFAs\<close>

text \<open>The language accepted by \<open>M\<close>:\<close>

definition Lang :: "'a list set" where
  "Lang \<equiv> {w. \<exists>u v.  w \<rightarrow>** (u, acc M, v)}" 

lemma unchanged_substrings:
  "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> rev u @ v = rev u' @ v'"
proof (induction rule: rtranclp_induct3)
  case (step a q' b c q'' d)
  then obtain p' d' where qd_def: "nxt M q' (hd b) = (p', d')" by fastforce
  then show ?case
  proof (cases d')
    case Left
    hence "(c, q'', d) = (tl a, p', hd a # b)"  
      using step(2) qd_def step.simps by force
    then show ?thesis
      using step.IH step.hyps(2) by fastforce
  next
    case Right
    hence "(c, q'', d) = (hd b # a, p', tl b)" using step(2) qd_def step.simps by fastforce
    then show ?thesis using step step.cases by fastforce
  qed
qed simp

lemma unchanged_final:
  assumes "p = acc M \<or> p = rej M"
  shows "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> p = q"
proof (induction rule: rtranclp_induct3)
  case (step a q' b c q'' d)
  then show ?case
    by (smt (verit) assms final_nxt_l final_nxt_r prod.inject step.cases)
qed simp

corollary unchanged_word:
  "([], p, w) \<rightarrow>* (u, q, v) \<Longrightarrow> w = rev u @ v"
using unchanged_substrings by fastforce

lemma step_tl_indep:
  assumes "(u, p, w @ v) \<rightarrow> (y, q, z @ v)"
          "w \<noteq> []"
  shows "(u, p, w @ v') \<rightarrow> (y, q, z @ v')"
using assms(1) proof cases
  case (step_left a x ys)
  with assms obtain as where "w = a # as" by (meson append_eq_Cons_conv) 
  moreover with step_left have "(u, p, w @ v') \<rightarrow> (y, q, x # w @ v')" by auto
  ultimately show ?thesis using step_left by auto
next
  case (step_right a)
  with assms obtain as where "w = a # as" by (meson append_eq_Cons_conv) 
  then show ?thesis using step_right by auto
qed

lemma steps_app [simp, intro]:
  "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> (u, p, v @ xs) \<rightarrow>* (u', q, v' @ xs)"
proof (induction rule: rtranclp_induct3) 
  case (step w q' x y p' z)
  from step(2) have "(w, q', x @ xs) \<rightarrow> (y, p', z @ xs)" by fastforce
  then show ?case using step(3) by simp
qed simp

lemma left_to_right_impl_substring:
  assumes "(u, p, v) \<rightarrow>* (w, q, y)"
          "length u \<le> length w"
  obtains us where "us @ u = w"
using assms proof (induction arbitrary: thesis rule: rtranclp_induct3)
  case (step u' p' v' x q z)
  then consider (len_u_lt_x) "length u < length x" | (len_u_eq_x) "length u = length x" by linarith
  then show ?case
  proof cases
    case len_u_lt_x
    then have "length u \<le> length u'" using step by fastforce
    with step(3) obtain us where us_app_u: "us @ u = u'" by blast
    then show thesis by (cases us) (use step us_app_u in auto)
  next
    case len_u_eq_x
    with step(1,2) unchanged_substrings have "u = x"
    by (metis rev_rev_ident rev_append[of "rev x" z] rev_append[of "rev u" v]
        append_eq_append_conv r_into_rtranclp)
    then show thesis using step(4) by simp
  qed
qed simp

lemma acc_impl_reachable_substring:
  assumes "w \<rightarrow>** (u, acc M, v)"
          "xs \<noteq> []"
          "ys \<noteq> []"
  shows "v = xs @ ys \<Longrightarrow> (u, acc M, v) \<rightarrow>* (rev xs @ u, acc M, ys)"
using assms
proof (induction v arbitrary: u xs ys)
  case (Cons a v)
  consider (not_right_marker) b where "a = Letter b \<or> a = \<turnstile>" | (right_marker) "a = \<stileturn>"  
    by (metis dir.exhaust symbol.exhaust)
  then show ?case 
  proof cases
    case not_right_marker
    hence step: "(u, acc M, a # v) \<rightarrow> (a # u, acc M, v)" using final_nxt_r by auto
    with Cons(3) have reach: "w \<rightarrow>** (a # u, acc M, v)" by simp
    from this obtain xs' where xs'_def: "v = xs' @ ys" 
      by (metis Cons.prems(1,3) append_eq_Cons_conv)
    from xs'_def Cons(2) have "a # xs' = xs" by simp
    then show ?thesis using Cons Cons(1)[of xs' ys "a # u", OF xs'_def reach] step by fastforce
  next
    case right_marker
    note unchanged = unchanged_word[OF Cons(3)]
    have "v = []"
    proof -
      have "length u = length (\<langle>w\<langle>)"
      proof (rule ccontr)
        assume "length u \<noteq> length (\<langle>w\<langle>)"
        with unchanged obtain n where n_len: "n < length (\<langle>w\<langle>)"
                                  and n_idx: "(rev u @ a # v) ! n = \<stileturn>"
          using right_marker
          by (metis append_assoc length_Cons length_append length_append_singleton length_rev 
              length_tl linorder_neqE_nat list.sel(3) not_add_less1 nth_append_length)
        have "(\<langle>w\<rangle>) ! n \<noteq> \<stileturn>"
        proof (cases n)
          case 0
          then show ?thesis by simp
        next
          case (Suc k)
          hence n_gt_0: "n > 0" by simp
          hence "(\<langle>w\<rangle>) ! n = (\<langle>w\<langle>) ! n" using n_len
            by (simp add: nth_append_left)
          also have "... = \<Sigma> w ! (n - 1)" using Suc by simp
          finally show ?thesis
            by (metis n_gt_0 One_nat_def Suc_less_eq Suc_pred length_Cons length_map n_len nth_map
                symbol.distinct(1))
        qed
        with n_idx unchanged show False by argo 
      qed
      with unchanged have "length (a # v) = Suc 0" 
        by (metis add_left_cancel length_Cons length_append length_rev list.size(3,4))
      thus ?thesis by simp
    qed
    then show ?thesis using Cons right_marker by (metis append_assoc snoc_eq_iff_butlast)
  qed
qed simp

lemma all_geq_left_impl_left_indep:
  assumes upv_reachable: "w \<rightarrow>** (u, p, v)"
      and "(u, p, v) \<rightarrow>(n) (vs @ u, q, x)"
          "\<forall>i\<le>n. \<forall>u' p' v'. ((u, p, v) \<rightarrow>(i) (u', p', v')) \<longrightarrow> length u' \<ge> length u"
  shows "((u', p, v) \<rightarrow>(n) (vs @ u', q, x))
         \<and> (\<forall>i\<le>n. \<forall>y p' v'. ((u', p, v) \<rightarrow>(i) (y, p', v')) \<longrightarrow> length y \<ge> length u')"
using assms(2,3) proof (induction n arbitrary: vs q x)
  case (Suc n)
  then obtain vs' q' x' where 
    nsteps: "(u, p, v) \<rightarrow>(n) (vs' @ u, q', x')" "(vs' @ u, q', x') \<rightarrow> (vs @ u, q, x)"
  proof -
    from Suc(2) obtain y q' x' where nstep: 
      "(u, p, v) \<rightarrow>(n) (y, q', x')" "(y, q', x') \<rightarrow> (vs @ u, q, x)" by auto
    moreover with Suc(3) have y_gt_u: "length y \<ge> length u" by (meson Suc_leD order_refl)
    ultimately obtain vs' where "y = vs' @ u" using left_to_right_impl_substring 
      by (metis relpowp_imp_rtranclp)
    then show thesis using nstep that by blast
  qed
  with Suc(1) have u'_stepn: "(u', p, v) \<rightarrow>(n) (vs' @ u', q', x')" 
               and u'_n_geq: "\<forall>i\<le>n. \<forall>y p' v'. ((u', p, v) \<rightarrow>(i) (y, p', v')) 
                              \<longrightarrow> length u' \<le> length y" 
    using Suc.IH Suc.prems(2) le_SucI le_Suc_eq  nsteps(1) by blast+
  moreover from u'_stepn nsteps(2) have Sucn_steps: "(u', p, v) \<rightarrow>(Suc n) (vs @ u', q, x)" by force
  moreover have "\<forall>i\<le>Suc n. \<forall>y p' v'. ((u', p, v) \<rightarrow>(i) (y, p', v')) \<longrightarrow> length y \<ge> length u'" 
  proof ((rule allI)+, (rule impI))+
    fix i y p' v'
    assume i_lt_Suc: "i \<le> Suc n"
        and stepi: "(u', p, v) \<rightarrow>(i) (y, p', v')"
    then consider (Suc) "i = Suc n" | (lt_Suc) "i < Suc n" by force
    then show "length u' \<le> length y"
    proof cases
      case Suc
      with stepi Sucn_steps show ?thesis
        by (metis leI length_append not_add_less2 prod.inject relpowp_right_unique step_unique)
    next
      case lt_Suc
      then show ?thesis using u'_n_geq stepi using less_Suc_eq_le by auto
    qed
  qed
  ultimately show ?case by auto
qed simp

lemma reachable_configs_impl_reachable:
  assumes "c0 \<rightarrow>* c1"
          "c0 \<rightarrow>* c2"
  shows "c1 \<rightarrow>* c2 \<or> c2 \<rightarrow>* c1"  
proof -
  from assms obtain n m where "c0 \<rightarrow>(n) c1" "c0 \<rightarrow>(m) c2"
    by (metis rtranclp_power)
  from this(1) show ?thesis 
  proof (induction n arbitrary: c1)
    case 0
    hence "c0 = c1" by simp
    then show ?case using assms(2) by auto
  next
    case (Suc n)
    then obtain c' where c'_defs: "c0 \<rightarrow>(n) c'" "c' \<rightarrow> c1" by auto
    with Suc.IH have "c' \<rightarrow>* c2 \<or> c2 \<rightarrow>* c'" by simp
    then consider (c'_eq_c2) "c' = c2" "c' \<rightarrow>* c2" | 
                  (c'_reaches_c2) "c' \<noteq> c2" "c' \<rightarrow>* c2" | 
                  (c2_reaches_c') "c2 \<rightarrow>* c'" by blast
    then show ?case
    proof cases
      case c'_eq_c2
      then show ?thesis using c'_defs by blast
    next
      case c'_reaches_c2
      then obtain c'' where "c' \<rightarrow> c''" "c'' \<rightarrow>* c2" by (metis converse_rtranclpE)
      then show ?thesis using c'_defs step_unique by metis
    next
      case c2_reaches_c'
      then show ?thesis using c'_defs(2) by (meson rtranclp.rtrancl_into_rtrancl)
    qed
  qed
qed

end


section \<open>Boundary Crossings\<close>

subsection \<open>Basic Definitions\<close>

text \<open>In order to describe boundary crossings in general, we describe the behavior of \<open>M\<close> for a
      fixed, non-empty string \<open>x\<close> and  input word \<open>xz\<close>, where \<open>z\<close> is an arbitrary string:\<close>

locale dfa2_transition = dfa2 +
  fixes x :: "'a list"
  assumes "x \<noteq> []"
begin 

definition x_init :: "'a symbol list" where
  "x_init \<equiv> butlast (\<langle>x\<langle>)"

definition x_end :: "'a symbol" where
  "x_end \<equiv> last (\<langle>x\<langle>)"

lemmas x_defs = x_init_def x_end_def

lemma x_is_init_app_end:
  "\<langle>x\<langle> = x_init @ [x_end]" unfolding x_defs by simp

subsubsection \<open>Left steps, right steps, and their reachabilities\<close>

text \<open>A 2DFA is in a left configuration for input \<open>xz\<close> if it is currently reading \<open>x\<close>.
      Otherwise, it is in a right configuration:\<close>
definition left_config :: "'a config \<Rightarrow> bool" where
  "left_config c \<equiv> \<exists>u q v. c = (u, q, v) \<and> length u < length (\<langle>x\<langle>)"

definition right_config :: "'a config \<Rightarrow> bool" where
  "right_config c \<equiv> \<exists>u q v. c = (u, q, v) \<and> length u \<ge> length (\<langle>x\<langle>)"

lemma left_config_is_not_right_config:
  "left_config c \<longleftrightarrow> \<not>right_config c"
unfolding left_config_def right_config_def
by (metis linorder_not_less prod.inject prod_cases3)

lemma left_config_lt_right_config:
  "\<lbrakk> left_config (u, p, v); right_config (w, q, y) \<rbrakk> \<Longrightarrow> length u < length w"
using left_config_def right_config_def by simp

text\<open>For configurations \<open>c\<^sub>0\<close> and \<open>c\<^sub>1\<close>, a step \<open>c\<^sub>0 \<rightarrow> c\<^sub>1\<close> is a left step \<open>c\<^sub>0 \<rightarrow>\<^sup>L c\<^sub>1\<close>
     if both \<open>c\<^sub>0\<close> and \<open>c\<^sub>1\<close> are in \<open>x\<close>:\<close>
inductive left_step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L\<close> 55) where
  lstep [intro]: "\<lbrakk>c0 \<rightarrow> c1; left_config c0; left_config c1\<rbrakk> \<Longrightarrow> c0 \<rightarrow>\<^sup>L c1"
                     
inductive_cases lstepE [elim]: "c0 \<rightarrow>\<^sup>L c1"

abbreviation left_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L*\<close> 55) where
  "left_steps \<equiv> left_step\<^sup>*\<^sup>*"

abbreviation left_stepn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>L'(_') _" 55) where
  "left_stepn c n \<equiv> (left_step ^^ n) c"

text \<open>\<open>c\<close> is left reachable by a word \<open>w\<close>
      if \<open>w \<rightarrow>** c\<close> and \<open>M\<close> does not cross the boundary before reaching \<open>c\<close>:\<close>
abbreviation left_reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L**\<close> 55) where
  "w \<rightarrow>\<^sup>L** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L* c" 

abbreviation left_nreachable :: "'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>L*'(_') _" 55) where
  "w \<rightarrow>\<^sup>L*(n) c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L(n) c"  

text \<open>Right steps are defined analogously:\<close>

inductive right_step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R\<close> 55) where
  rstep [intro]: "\<lbrakk>c0 \<rightarrow> c1; right_config c0; right_config c1\<rbrakk> \<Longrightarrow> c0 \<rightarrow>\<^sup>R c1"

inductive_cases rstepE [elim]: "c0 \<rightarrow>\<^sup>R c1"

abbreviation right_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R*\<close> 55) where
  "right_steps \<equiv> right_step\<^sup>*\<^sup>*"

abbreviation right_stepn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>R'(_') _" 55) where
  "right_stepn c n \<equiv> (right_step ^^ n) c"

subsubsection \<open>Properties of left and right steps\<close>

lemma left_steps_impl_steps [dest]:
  "c0 \<rightarrow>\<^sup>L* c1 \<Longrightarrow> c0 \<rightarrow>* c1"
by (induction rule: rtranclp_induct) auto

lemma right_steps_impl_steps [dest]:
  "c0 \<rightarrow>\<^sup>R* c1 \<Longrightarrow> c0 \<rightarrow>* c1"
by (induction rule: rtranclp_induct) auto

lemma left_steps_impl_left_config[dest]:
  "\<lbrakk>c0 \<rightarrow>\<^sup>L* c1; left_config c0\<rbrakk> \<Longrightarrow> left_config c1"
by (induction rule: rtranclp_induct) auto

lemma left_steps_impl_left_config_conv[dest]:
  "\<lbrakk>c0 \<rightarrow>\<^sup>L* c1; left_config c1\<rbrakk> \<Longrightarrow> left_config c0" 
by (induction rule: rtranclp_induct) auto

lemma left_reachable_impl_left_config:
  "w \<rightarrow>\<^sup>L** c \<Longrightarrow> left_config c" 
using left_config_def left_steps_impl_left_config by auto

lemma right_steps_impl_right_config[dest]: 
  "\<lbrakk>c0 \<rightarrow>\<^sup>R* c1; right_config c0\<rbrakk> \<Longrightarrow> right_config c1"
by (induction rule: rtranclp_induct) auto

lemma left_step_tl_indep:
  "\<lbrakk> (u, p, w @ v) \<rightarrow>\<^sup>L (y, q, z @ v); w \<noteq> [] \<rbrakk> \<Longrightarrow> (u, p, w @ v') \<rightarrow>\<^sup>L (y, q, z @ v')"
using step_tl_indep left_config_is_not_right_config left_config_lt_right_config left_step.cases lstep
by (meson order.irrefl)

lemma right_stepn_impl_interm_right_stepn:
  assumes "c0 \<rightarrow>\<^sup>R(n) c2"
          "c0 \<rightarrow>(m) c1"
          "m \<le> n"
  shows "c0 \<rightarrow>\<^sup>R(m) c1"
proof -
  from assms(1) obtain f where f_def:
    "f 0 = c0"
    "f n = c2"
    "\<forall>i<n. f i \<rightarrow>\<^sup>R f (Suc i)" 
    by (metis relpowp_fun_conv)
  from assms(2) obtain g where g_def:
    "g 0 = c0"
    "g m = c1"
    "\<forall>i<m. g i \<rightarrow> g (Suc i)"
    by (metis relpowp_fun_conv)
  have "i<m \<Longrightarrow> g i = f i" for i
  proof (induction i)
    case 0
    then show ?case using f_def g_def by blast
  next
    case (Suc n)
    then have "g n = f n" by linarith
    with Suc f_def g_def show ?case using right_step.cases step_unique
      by (metis Suc_lessD assms(3) order_less_le_trans)
  qed
  with f_def g_def have "\<forall>i<m. g i \<rightarrow>\<^sup>R g (Suc i)" using right_step.cases step_unique
    by (metis assms(3) order_less_le_trans)
  with g_def show ?thesis by (metis relpowp_fun_conv)
qed

text \<open>These \<open>list\<close> lemmas are necessary for the two following \<open>substring\<close> lemmas:\<close>
lemma list_deconstruct1:
  assumes "m \<le> length xs"
  obtains ys zs where "length ys = m" "ys @ zs = xs" using assms
by (metis append_take_drop_id dual_order.eq_iff length_take min_def) 

lemma list_deconstruct2:
  assumes "m \<le> length xs"
  obtains ys zs where "length zs = m" "ys @ zs = xs"
proof -
  from assms have "m \<le> length (rev xs)" by simp
  then obtain ys zs where "length ys = m" "ys @ zs = rev xs"
    using list_deconstruct1 by blast
  then show thesis using list_deconstruct1 that by (auto simp: append_eq_rev_conv)
qed

lemma lstar_impl_substring_x:
  assumes app_eq: "rev u @ v = \<langle>x @ z\<rangle>"
      and in_x:   "length u < length (\<langle>x\<langle>)"
      and lsteps: "(u, p, v) \<rightarrow>\<^sup>L* (u', q, v')"
  obtains y where " rev u' @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v'" 
proof -
  have leftconfig: "left_config (u, p, v)" unfolding left_config_def using in_x by blast
  hence u'_lt_x: "length u' < length (\<langle>x\<langle>)" using lsteps left_config_def by force
  from lsteps show thesis
  proof (induction arbitrary: u p v rule: rtranclp_induct3)
    case refl 
    from unchanged_word app_eq lsteps have app: "\<langle>x @ z\<rangle> = rev u' @ v'"
      by (metis left_steps_impl_steps unchanged_substrings)
    moreover with u'_lt_x
    obtain y where "rev u' @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v'"
    proof -
      from u'_lt_x list_deconstruct1
      obtain xs ys where "length xs = length u'" and xapp: "xs @ ys = \<langle>x\<langle>"
        using Nat.less_imp_le_nat by metis
      moreover from this have  "length (ys @ \<rangle>z\<rangle>) = length v'" using app 
        by (smt (verit) append_assoc append_eq_append_conv length_rev
            mapl_app_mapr_eq_map) 
      ultimately have xs_is_rev: "xs = rev u'"
        by (metis (no_types) app append_Cons append_assoc append_eq_append_conv map_append) 
      then have "ys @ \<rangle>z\<rangle> = v'" using xapp app
        by (metis (no_types) append_assoc same_append_eq[of xs v' "ys @ \<Sigma> z @ [\<stileturn>]"] mapl_app_mapr_eq_map)
      thus thesis using that xs_is_rev xapp by presburger
    qed
    ultimately show ?case using that by simp
  qed blast
qed

corollary left_reachable_impl_substring_x:
  assumes "x @ z \<rightarrow>\<^sup>L** (u, q, v)"
  obtains y where " rev u @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v"
using lstar_impl_substring_x assms left_config_def left_reachable_impl_left_config by blast

corollary reachable_lconfig_impl_substring_x:
  assumes "x @ z \<rightarrow>** (u, p, v)"
      and "length u < length (\<langle>x\<langle>)"
      and "(u, p, v) \<rightarrow>\<^sup>L* (u', q, v')"
  obtains y where " rev u' @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v'" 
using unchanged_word[OF assms(1)] lstar_impl_substring_x assms by metis 

lemma star_rconfig_impl_substring_z:
  assumes app_eq: "x @ z \<rightarrow>** (u, p, v)"
      and reach: "(u, p, v) \<rightarrow>* (u', q, v')"
      and rconf: "right_config (u', q, v')"
  obtains y where " rev (\<langle>x\<langle> @ y) = u'" "y @ v' = \<rangle>z\<rangle>"
proof -
  from right_config_def have u'_ge_x: "length (\<langle>x\<langle>) \<le> length u'"
    using rconf by force
  from reach show thesis
  proof (induction arbitrary: u p v rule: rtranclp_induct3)
    case refl
    from unchanged_word app_eq have app: "\<langle>x @ z\<rangle> = rev u' @ v'"
      by (metis reach unchanged_substrings)
    moreover with u'_ge_x
    obtain x' where "rev (\<langle>x\<langle> @ x') = u'" "x' @ v' = \<rangle>z\<rangle>"
    proof -
      have "length v' \<le> length (\<rangle>z\<rangle>)" 
      proof (rule ccontr)
        assume "\<not>?thesis"
        hence "length v' > length (\<rangle>z\<rangle>)" by simp
        with u'_ge_x
        have "length (rev u' @ v') > length (\<langle>x @ z\<rangle>)" by simp
        thus False using app by (metis nat_less_le)
      qed
      from list_deconstruct2[OF this]
      obtain xs ys where "length ys = length v'" and zapp: "xs @ ys = \<rangle>z\<rangle>"
        by metis
      moreover from this have "length (\<langle>x\<langle> @ xs) = length u'" using app
        by (metis (no_types, lifting) append.assoc append_eq_append_conv length_rev
            mapl_app_mapr_eq_map)
      ultimately have ys_is_v': "ys = v'"
        by (metis app append_assoc append_eq_append_conv mapl_app_mapr_eq_map)
      then have x_app_xs_eq_rev_u': "\<langle>x\<langle> @ xs = rev u'" using zapp app
        by (metis (no_types, lifting) append_assoc append_eq_append_conv
            mapl_app_mapr_eq_map)
      hence "rev (\<langle>x\<langle> @ xs) = u'" by simp
      thus thesis using ys_is_v' zapp that by presburger
    qed
    ultimately show ?case using that by simp
  qed blast
qed

corollary reachable_right_conf_impl_substring_z:
  assumes "x @ z \<rightarrow>** (u, q, v)"
          "right_config (u, q, v)"
  obtains y where "rev (\<langle>x\<langle> @ y) = u" "y @ v = \<rangle>z\<rangle>"
using assms star_rconfig_impl_substring_z right_config_def by blast

lemma lsteps_indep:
  assumes "(u, p, v @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (w, q, y @ \<rangle>z\<rangle>)"
          "rev u @ v @ \<rangle>z\<rangle> = \<langle>x @ z\<rangle>"
  shows "(u, p, v @ \<rangle>z'\<rangle>) \<rightarrow>\<^sup>L* (w, q, y @ \<rangle>z'\<rangle>)"
proof -
  from assms obtain n where nsteps: "(u, p, v @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L(n) (w, q, y @ \<rangle>z\<rangle>)" 
    using rtranclp_power by meson
  then show ?thesis using assms(2)
  proof (induction n arbitrary: w q y)
    case (Suc n)
    obtain w' q' y' where lstepn: "(u, p, v @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L(n) (w', q', y' @ \<rangle>z\<rangle>)"
                      and lstep:  "(w', q', y' @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L (w, q, y @ \<rangle>z\<rangle>)"
    proof -
      from Suc.prems obtain w' q' y' where lstepn: "(u, p, v @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L(n) (w', q', y')"
                                       and lstep: "(w', q', y') \<rightarrow>\<^sup>L (w, q, y @ \<rangle>z\<rangle>)" by auto
      hence w'_left: "left_config (w', q', y')" by blast
      then obtain xs where "xs @ \<rangle>z\<rangle> = y'"
      proof -
        from lstepn have "(u, p, v @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (w', q', y')"
          by (simp add: relpowp_imp_rtranclp)
        moreover have "length u < length (\<langle>x\<langle>)"
          by (meson calculation left_config_lt_right_config left_steps_impl_left_config_conv
              linorder_le_less_linear order_less_imp_not_eq2 right_config_def w'_left)
        ultimately show thesis using Suc.prems(2) that by (meson lstar_impl_substring_x)
      qed
      with lstepn lstep show thesis using that by auto
    qed
    with Suc.IH have "(u, p, v @ \<rangle>z'\<rangle>) \<rightarrow>\<^sup>L* (w', q', y' @ \<rangle>z'\<rangle>)"
      by (simp add: Suc.prems(2))
    moreover have "(w', q', y' @ \<rangle>z'\<rangle>) \<rightarrow>\<^sup>L (w, q, y @ \<rangle>z'\<rangle>)"
    proof -
      have y'_not_empty: "y' \<noteq> []"
      proof 
        assume "y' = []"
        hence "(u, p, v @ \<rangle>z'\<rangle>) \<rightarrow>\<^sup>L* (w', q', \<rangle>z'\<rangle>)" using calculation by auto
        moreover have "left_config (u, p, v @ \<rangle>z\<rangle>)"
          by (meson Suc.prems(1) \<open>(w', q', y' @ \<Sigma> z @ [\<stileturn>]) \<rightarrow>\<^sup>L (w, q, y @ \<Sigma> z @ [\<stileturn>])\<close>
              dfa2_transition.left_steps_impl_left_config_conv dfa2_transition_axioms left_step.cases
              relpowp_imp_rtranclp)
        ultimately have lc: "left_config (w', q', \<rangle>z'\<rangle>)" 
          using left_config_is_not_right_config left_config_lt_right_config by blast
        have "rev u @ v @ \<rangle>z'\<rangle> = \<langle>x @ z'\<rangle>"
          using assms(2) by force
        hence "rev w' @ \<rangle>z'\<rangle> = ..."
          by (metis \<open>(u, p, v @ \<Sigma> z' @ [\<stileturn>]) \<rightarrow>\<^sup>L* (w', q', y' @ \<Sigma> z' @ [\<stileturn>])\<close> \<open>y' = []\<close> left_steps_impl_steps
              self_append_conv2 unchanged_substrings) 
        hence "length w' = length (\<langle>x\<langle>)" by simp
        with lc show False using left_config_def by simp
      qed
      with left_step_tl_indep[OF lstep] show ?thesis by simp
    qed
    ultimately show ?case by simp
  qed simp
qed

lemma left_reachable_indep:
  assumes "x @ y \<rightarrow>\<^sup>L** (u, q, v @ \<rangle>y\<rangle>)"
  shows "x @ z \<rightarrow>\<^sup>L** (u, q, v @ \<rangle>z\<rangle>)"
proof -
  from assms obtain n where "([], init M, \<langle>x @ y\<rangle>) \<rightarrow>\<^sup>L(n) (u, q, v @ \<rangle>y\<rangle>)"
    by (meson rtranclp_power)
  hence "([], init M, \<langle>x @ z\<rangle>) \<rightarrow>\<^sup>L(n) (u, q, v @ \<rangle>z\<rangle>)"
  proof (induction n arbitrary: u q v)
    case (Suc n)
    from Suc(2) obtain u' p v' 
      where stepn: "x @ y \<rightarrow>\<^sup>L*(n) (u', p, v' @ \<rangle>y\<rangle>)" 
        and "(u', p, v' @ \<rangle>y\<rangle>) \<rightarrow>\<^sup>L(1) (u, q, v @ \<rangle>y\<rangle>)"
    proof -
      from Suc(2) obtain u' p v'' 
        where "x @ y \<rightarrow>\<^sup>L*(n) (u', p, v'')"
              "(u', p, v'') \<rightarrow>\<^sup>L(1) (u, q, v @ \<rangle>y\<rangle>)" by auto
      moreover with left_reachable_impl_substring_x obtain v' where "v'' = v' @ \<rangle>y\<rangle>" 
        using rtranclp_power by metis
      ultimately show thesis using that by blast
    qed
    from this have y_lstep: "(u', p, v' @ \<rangle>y\<rangle>) \<rightarrow>\<^sup>L (u, q, v @ \<rangle>y\<rangle>)" 
      by fastforce
    hence "(u', p, v' @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L (u, q, v @ \<rangle>z\<rangle>)"
    proof -
      from y_lstep have left_configs: 
        "left_config (u', p, v' @ \<rangle>y\<rangle>)" 
        "left_config (u, q, v @ \<rangle>y\<rangle>)" by blast+
      hence "left_config (u', p, v' @ \<rangle>z\<rangle>)" 
            "left_config (u, q, v @ \<rangle>z\<rangle>)"
        unfolding left_config_def by auto
      moreover have "(u', p, v' @ \<rangle>z\<rangle>) \<rightarrow> (u, q, v @ \<rangle>z\<rangle>)"
      proof -
        from y_lstep have y_step: "(u', p, v' @ \<rangle>y\<rangle>) \<rightarrow> (u, q, v @ \<rangle>y\<rangle>)" by blast
        obtain c vs where v'_def: "v' = c # vs"
        proof -
          from unchanged_word have "rev u' @ v' @ \<rangle>y\<rangle> = \<langle>x @ y\<rangle>"
            by (metis left_steps_impl_steps relpowp_imp_rtranclp stepn)
          hence rev_u'_app_v': "rev u' @ v' = \<langle>x\<langle>" by simp
          have "v' \<noteq> []"
            by (rule ccontr) (use rev_u'_app_v' left_config_def left_configs in auto)
          thus thesis using that list.exhaust by blast
        qed
        with y_step have "(u', p, c # vs @ \<rangle>y\<rangle>) \<rightarrow> (u, q, v @ \<rangle>y\<rangle>)" by simp
        hence "(u', p, c # vs @ \<rangle>z\<rangle>) \<rightarrow> (u, q, v @ \<rangle>z\<rangle>)" by fastforce
        with v'_def show ?thesis by simp
      qed 
      ultimately show ?thesis by blast
    qed
    moreover from Suc(1)[OF stepn] have "x @ z \<rightarrow>\<^sup>L*(n) (u', p, v' @ \<rangle>z\<rangle>)" .
    ultimately show ?case by auto
  qed simp
  then show ?thesis by (meson rtranclp_power)
qed

subsection \<open>A Formal Definition of Boundary Crossings\<close>

text \<open>\<open>c\<^sub>0 \<rightarrow>\<^sup>X(n) c\<^sub>1\<close> if \<open>c\<^sub>0\<close> reaches \<open>c\<^sub>1\<close> crossing the boundary \<open>n\<close> times:\<close>
inductive crossn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>X'(_') _" 55) where
  no_crossl:   "\<lbrakk>left_config c0; c0 \<rightarrow>\<^sup>L* c1\<rbrakk> \<Longrightarrow> c0 \<rightarrow>\<^sup>X(0) c1" |
  no_crossr:   "\<lbrakk>right_config c0; c0 \<rightarrow>\<^sup>R* c1\<rbrakk> \<Longrightarrow> c0 \<rightarrow>\<^sup>X(0) c1" |
  crossn_rtol:  "\<lbrakk>c0 \<rightarrow>\<^sup>X(n) (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>); 
                  (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>);
                  (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* c1\<rbrakk> \<Longrightarrow> c0 \<rightarrow>\<^sup>X(Suc n) c1" |
  crossn_ltor:  "\<lbrakk> c0 \<rightarrow>\<^sup>X(n) (rev x_init, p, x_end # \<rangle>z\<rangle>); 
                   (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>);
                   (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* c1\<rbrakk> \<Longrightarrow> c0 \<rightarrow>\<^sup>X(Suc n) c1"

declare crossn.intros[intro]

inductive_cases no_crossE[elim]: "c0 \<rightarrow>\<^sup>X(0) c1"
inductive_cases crossE[elim]: "c0 \<rightarrow>\<^sup>X(Suc n) c1"

abbreviation word_crossn :: "'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>X*'(_') _" 55) where
  "word_crossn w n c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>X(n) c" 

lemma self_nocross[simp]:
  "c \<rightarrow>\<^sup>X(0) c" using left_config_is_not_right_config by blast

lemma no_cross_impl_same_side:
  "c0 \<rightarrow>\<^sup>X(0) c1 \<Longrightarrow> left_config c0 = left_config c1"
using left_config_is_not_right_config by blast

lemma left_config_impl_rtol_cross:
  assumes "c0 \<rightarrow>\<^sup>X(Suc n) c1"
          "left_config c1"
  obtains p q z where "c0 \<rightarrow>\<^sup>X(n) (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)" 
                      "(rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>)"
                      "(rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* c1"
using assms(1) proof cases
  case (crossn_rtol p z q)
  then show ?thesis using that by blast
next
  case (crossn_ltor p z q)
  from crossn_ltor(3) have "right_config c1" 
    using right_config_def right_steps_impl_right_config by auto
  then show ?thesis using assms left_config_is_not_right_config by auto
qed

lemma right_config_impl_ltor_cross:
  assumes "c0 \<rightarrow>\<^sup>X(Suc n) c1"
          "right_config c1"
  obtains p q z where "c0 \<rightarrow>\<^sup>X(n) (rev x_init, p, x_end # \<rangle>z\<rangle>)" 
                      "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
                      "(rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* c1"
using assms(1) proof cases
  case (crossn_rtol p z q)
  from crossn_rtol(3) have "left_config c1" 
    using left_config_def left_steps_impl_left_config
    by (simp add: x_is_init_app_end)
  then show ?thesis using assms left_config_is_not_right_config by auto
next
  case (crossn_ltor p z q)
    then show ?thesis using that by blast
qed

lemma crossn_decompose:
  assumes "c0 \<rightarrow>\<^sup>X(Suc n) c2"
  obtains c1 where "c0 \<rightarrow>\<^sup>X(n) c1" "c1 \<rightarrow>\<^sup>X(Suc 0) c2" 
using assms proof cases
  case (crossn_rtol p z q)
  moreover have "(rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow>\<^sup>X(Suc 0) c2" 
    by (rule crossn.intros(3)[OF self_nocross])
        (use crossn_rtol in auto)
  ultimately show ?thesis using that by blast
next
  case (crossn_ltor p z q)
  moreover have "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>X(Suc 0) c2" 
    by (rule crossn.intros(4)[OF self_nocross])
        (use crossn_ltor in auto)
  ultimately show ?thesis using that by blast
qed 

lemma step_impl_crossn:
  assumes "c0 \<rightarrow> c1"
          "c0 = (u, p, v)"
          "rev u @ v = \<langle>x @ z\<rangle>"
  shows "(c0 \<rightarrow>\<^sup>X(0) c1) \<or> (c0 \<rightarrow>\<^sup>X(Suc 0) c1)"
proof (cases "left_config c0 = left_config c1")
  case True  
  consider "left_config c0" | "right_config c0" using left_config_is_not_right_config by blast
  then show ?thesis
    by cases
    ((use assms True in auto), 
      (simp add: left_config_is_not_right_config no_crossr r_into_rtranclp rstep))
next
  case False
  consider (left) "left_config c0" | (right) "right_config c0" 
    using left_config_is_not_right_config by blast
  then show ?thesis
  proof cases
    case left
    with False obtain q where "c0 = (rev x_init, p, x_end # \<rangle>z\<rangle>)"
                                  "c1 = (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
    proof -
      obtain y q w where c1_def: "c1 = (y, q, w)" using prod_cases3 by blast
      have "length u = length (\<langle>x\<langle>) - 1" "length y = length (\<langle>x\<langle>)" 
      proof -
        from left assms(2) have "length u < length (\<langle>x\<langle>)" using left_config_def by auto
        moreover from left False right_config_def c1_def have "length y \<ge> length (\<langle>x\<langle>)" 
          using left_config_is_not_right_config by simp
        moreover from assms(1,2) c1_def have "length u = Suc (length y) \<or> length y = Suc (length u)"
          by fastforce
        ultimately show "length u = length (\<langle>x\<langle>) - 1" "length y = length (\<langle>x\<langle>)"
          by force+
      qed
      with assms(2,3) have "u = rev x_init" 
        by (smt (verit, ccfv_threshold) append_assoc append_eq_append_conv mapl_app_mapr_eq_map
             length_butlast length_rev rev_swap x_init_def x_is_init_app_end)
      from this have "v = x_end # \<rangle>z\<rangle>" 
        by (smt (verit) append.assoc append_eq_append_conv append_eq_rev_conv assms(3) mapl_app_mapr_eq_map
            rev.simps(2) rev_rev_ident rev_singleton_conv x_is_init_app_end)
      have "y = rev (\<langle>x\<langle>)" 
        using \<open>length y = length (\<turnstile> # \<Sigma> x)\<close> \<open>u = rev x_init\<close> \<open>v = x_end # \<Sigma> z @ [\<stileturn>]\<close> assms(1,2) c1_def
          x_is_init_app_end by auto
      moreover from this have "w = \<rangle>z\<rangle>" 
        using \<open>length u = length (\<turnstile> # \<Sigma> x) - 1\<close> \<open>v = x_end # \<Sigma> z @ [\<stileturn>]\<close> assms(1,2) c1_def by auto
      ultimately have "c1 = (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" using c1_def by simp
      moreover have "c0 = (rev x_init, p, x_end # \<rangle>z\<rangle>)" 
        by (simp add: \<open>u = rev x_init\<close> \<open>v = x_end # \<Sigma> z @ [\<stileturn>]\<close> assms(2))
      ultimately show thesis using that by blast
    qed
    then show ?thesis
      using assms(1) dfa2_transition.self_nocross dfa2_transition_axioms by blast
  next
    case right
    with False obtain q where "c0 = (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)"
                              "c1 = (rev x_init, q, x_end # \<rangle>z\<rangle>)"
    proof -
      obtain y q w where c1_def: "c1 = (y, q, w)" using prod_cases3 by blast
      have "length u = length (\<langle>x\<langle>)" "length y = length (\<langle>x\<langle>) - 1" 
      proof -
        from right assms(2) have "length u \<ge> length (\<langle>x\<langle>)" using right_config_def by auto
        moreover from right False left_config_def c1_def have "length y < length (\<langle>x\<langle>)" 
          using left_config_is_not_right_config by blast
        moreover from assms(1,2) c1_def have "length u = Suc (length y) \<or> length y = Suc (length u)"
          by fastforce
        ultimately show "length u = length (\<langle>x\<langle>)" "length y = length (\<langle>x\<langle>) - 1"
          by force+
      qed
      with assms(2,3) have "u = rev (\<langle>x\<langle>)" 
        by (smt (verit, ccfv_threshold) append_assoc append_eq_append_conv mapl_app_mapr_eq_map
             length_butlast length_rev rev_swap x_init_def x_is_init_app_end)
      from this have "v = \<rangle>z\<rangle>"
        by (smt (verit) append.assoc append_eq_append_conv append_eq_rev_conv assms(3) mapl_app_mapr_eq_map
            rev.simps(2) rev_rev_ident rev_singleton_conv x_is_init_app_end)
      have "y = rev x_init" 
        using \<open>length y = length (\<turnstile> # \<Sigma> x) - 1\<close> \<open>u = rev (\<langle>x\<langle>)\<close> \<open>v = \<Sigma> z @ [\<stileturn>]\<close> assms(1,2) c1_def
          x_is_init_app_end by auto
      moreover from this have "w = x_end # \<rangle>z\<rangle>" 
        by (smt (verit) \<open>length u = length (\<turnstile> # \<Sigma> x)\<close> \<open>length y = length (\<turnstile> # \<Sigma> x) - 1\<close>
            \<open>u = rev (\<turnstile> # \<Sigma> x)\<close> \<open>v = \<Sigma> z @ [\<stileturn>]\<close> assms(1,2) c1_def diff_le_self impossible_Cons last_snoc
            prod.inject rev_eq_Cons_iff step_foldedE x_end_def)
      ultimately have "c1 = (rev x_init, q, x_end # \<rangle>z\<rangle>)" using c1_def by simp  
      moreover have "c0 = (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)" 
        by (simp add: \<open>u = rev (\<langle>x\<langle>)\<close> \<open>v = \<Sigma> z @ [\<stileturn>]\<close> assms(2))
      ultimately show thesis using that by blast
    qed
    then show ?thesis 
      using assms(1) dfa2_transition.self_nocross dfa2_transition_axioms by blast
  qed
qed

lemma crossn_no_cross_eq_crossn:
  assumes "c0 \<rightarrow>\<^sup>X(n) c1"
          "c1 \<rightarrow>\<^sup>X(0) c2"
  shows "c0 \<rightarrow>\<^sup>X(n) c2"
using assms(1) proof cases
  case no_crossl
  then show ?thesis using left_steps_impl_left_config 
    assms left_config_is_not_right_config by (meson crossn.no_crossl no_crossE rtranclp_trans)
next
  case no_crossr
  then show ?thesis using right_steps_impl_right_config
    assms left_config_is_not_right_config by (meson crossn.no_crossr no_crossE rtranclp_trans)
next
  case (crossn_rtol n p z q)
  from crossn_rtol(4) have "left_config c1" using left_steps_impl_left_config left_config_def 
    x_is_init_app_end by auto
  with assms(2) have "c1 \<rightarrow>\<^sup>L* c2" using left_config_is_not_right_config by blast
  then show ?thesis using crossn_rtol by auto
next
  case (crossn_ltor n p z q)
  from crossn_ltor(4) have "right_config c1" using right_steps_impl_right_config right_config_def
    x_is_init_app_end by auto
  with assms(2) have "c1 \<rightarrow>\<^sup>R* c2" using left_config_is_not_right_config by blast
  then show ?thesis using crossn_ltor by auto
qed    

lemma crossn_trans:
  assumes "c0 \<rightarrow>\<^sup>X(n) c1"
  shows "c1 \<rightarrow>\<^sup>X(m) c2 \<Longrightarrow> c0 \<rightarrow>\<^sup>X(n+m) c2"
proof (induction m arbitrary: c2)
  case 0
  from assms show ?case 
  proof cases
    case no_crossl
    then show ?thesis 
      by (metis "0.prems"(1) add_is_0 crossn.no_crossl left_config_is_not_right_config no_crossE
          no_cross_impl_same_side rtranclp_trans)
  next
    case no_crossr
    then show ?thesis 
      by (metis "0.prems"(1) add_0_right crossn.no_crossr left_config_is_not_right_config no_crossE
          right_steps_impl_right_config rtranclp_trans)
  next
    case (crossn_rtol n p z q)
    then show ?thesis
      by (smt (verit, best) "0.prems"(1) Nat.add_0_right crossn.crossn_rtol left_config_def
          left_config_is_not_right_config left_steps_impl_left_config length_append_singleton length_rev
          lessI no_crossE rtranclp_trans x_is_init_app_end)
  next
    case (crossn_ltor n p z q)
    from crossn_ltor(4) have "right_config c1" using right_steps_impl_right_config 
      by (simp add: right_config_def)
    with 0(1) have "c1 \<rightarrow>\<^sup>R* c2" using left_config_is_not_right_config by blast
    with crossn_ltor(4) have "(rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* c2" by simp
    with crossn_ltor(1,2,3) show ?thesis by auto
  qed
next
  case (Suc m)
  from Suc(2) crossn_decompose obtain c' where "c1 \<rightarrow>\<^sup>X(m) c'" 
                                          and c'_cross: "c' \<rightarrow>\<^sup>X(Suc 0) c2" by blast
  with Suc(1) have c0_nm_cross: "c0 \<rightarrow>\<^sup>X(n+m) c'" by blast
  from c'_cross show ?case
  proof cases
    case (crossn_rtol r w s)
    moreover with c0_nm_cross crossn_no_cross_eq_crossn have 
      "c0 \<rightarrow>\<^sup>X(n+m) (rev (\<langle>x\<langle>), r, \<rangle>w\<rangle>)" by blast
    ultimately show ?thesis by auto
  next
    case (crossn_ltor r w s)
    moreover with c0_nm_cross crossn_no_cross_eq_crossn have
      "c0 \<rightarrow>\<^sup>X(n+m) (rev x_init, r, x_end # \<rangle>w\<rangle>)" by blast
    ultimately show ?thesis by auto
  qed
qed
  
lemma crossn_impl_reachable:
  assumes "c0 \<rightarrow>\<^sup>X(n) c1"
  shows "c0 \<rightarrow>* c1"
using assms by induction auto

lemma reachable_xz_impl_crossn:
  assumes "c0 \<rightarrow>* c1"
          "c0 = (u, p, v)"
          "rev u @ v = \<langle>x @ z\<rangle>"
  obtains n where "c0 \<rightarrow>\<^sup>X(n) c1"
using assms proof (induction arbitrary: u p v thesis)
  case base
  then show ?case using self_nocross by blast
next
  case (step c1 c2)
  then obtain n where ncross: "c0 \<rightarrow>\<^sup>X(n) c1" by blast
  obtain w q y where "c1 = (w, q, y)" using prod_cases3 by blast
  moreover from this have "rev w @ y = \<langle>x @ z\<rangle>" 
     using unchanged_substrings step(1,5,6) by simp
  ultimately obtain m where "c1 \<rightarrow>\<^sup>X(m) c2" using step(2) step_impl_crossn by metis
  then show ?case using ncross crossn_trans step(4) by blast
qed

subsection \<open>The Transition Relation \<open>T\<^sub>x\<close>\<close>

text \<open>\<open>T\<^sub>x p q\<close> for a non-empty string \<open>x\<close> describes the behavior of 
      a 2DFA \<open>M\<close> when it crosses the boundary between \<open>x\<close> and any string \<open>z\<close> for the 
      input string \<open>xz\<close>. Intuitively, \<open>T\<^sub>x (Some p) (Some q)\<close> if whenever \<open>M\<close> enters \<open>x\<close> from the right in 
      state \<open>p\<close>, when it re-enters \<open>z\<close> in the future, it will do so in state \<open>q\<close>. 
      \<open>T\<^sub>x None (Some q)\<close> denotes the state in which \<open>M\<close> first enters \<open>z\<close>, while \<open>T\<^sub>x (Some p) None\<close> 
      denotes that if \<open>M\<close> ever enters \<open>x\<close> in state \<open>p\<close>, it will never enter \<open>z\<close> in the future, and 
      therefore does not terminate.\<close>

inductive T :: "state option \<Rightarrow> state option \<Rightarrow> bool" where
  init_tr: "\<lbrakk> x @ z \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z\<rangle>); 
             (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T None (Some q)" |

  init_no_tr: "\<nexists>q z. x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<Longrightarrow> T None None" |

  some_tr: "\<lbrakk> p' \<in> states M; (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, p, x_end # \<rangle>z\<rangle>); 
             (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>); 
             (rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T (Some p) (Some q)" |
                             
  no_tr:   "\<lbrakk> p' \<in> states M; (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, p, x_end # \<rangle>z\<rangle>); 
              \<nexists>q' q'' z. (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>) \<and>
              (rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T (Some p) None" 

declare T.intros[intro]

inductive_cases init_trNoneE[elim]: "T None None"
inductive_cases init_trSomeE[elim]: "T  None (Some q)"
inductive_cases no_trE[elim]:   "T (Some q) None"
inductive_cases some_trE[elim]: "T (Some q) (Some p)"

text \<open>Lemmas for the independence of \<open>T\<^sub>x\<close> from \<open>z\<close>. This is a fundamental property to show
      the main theorem:\<close>
lemma init_tr_indep:
  assumes "T None (Some q)"
  obtains p where "x @ z \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z\<rangle>)"
                  "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
proof -
  from assms obtain p z' where prems: "x @ z' \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z'\<rangle>)"
                               "(rev x_init, p, x_end # \<rangle>z'\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z'\<rangle>)"
    by auto
  with left_reachable_indep[of _ _ _ "[x_end]"] have "x @ z \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z\<rangle>)" 
    by auto
  moreover from prems(2) have "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
    by fastforce
  ultimately show thesis using that by simp
qed

lemma init_no_tr_indep:
  "T None None \<Longrightarrow> \<nexists>q. x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" 
by auto

lemma some_tr_indep:
  assumes "T (Some p) (Some q)"
  obtains q' where "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>)"
                   "(rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
proof -
  from assms obtain p' q' z' where prems:
    "(rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>) \<rightarrow> (rev x_init, p, x_end # \<rangle>z'\<rangle>)"
    "(rev x_init, p, x_end # \<rangle>z'\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z'\<rangle>)"
    "(rev x_init, q', x_end # \<rangle>z'\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z'\<rangle>)" by auto
  with lsteps_indep[of "rev x_init" p "[x_end]" z' "rev x_init" q' "[x_end]" z] have
            "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>)"
            "(rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" 
      using x_is_init_app_end by auto
  thus thesis using that by simp
qed

lemma T_None_Some_impl_reachable:
  assumes "T None (Some q)"
  shows "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
proof -
 obtain q' z' where "x @ z' \<rightarrow>\<^sup>L** (rev x_init, q', x_end # \<rangle>z'\<rangle>)"
                               "(rev x_init, q', x_end # \<rangle>z'\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z'\<rangle>)" 
    using assms by auto
  with left_reachable_indep[of z' "rev x_init" q' "[x_end]"] have "x @ z \<rightarrow>\<^sup>L** (rev x_init, q', x_end # \<rangle>z\<rangle>)"
                               "(rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" 
    by fastforce+
  thus "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by auto
qed

lemma T_impl_in_states:
  assumes "T p q"
  shows "p = Some p' \<Longrightarrow> p' \<in> states M"
        "q = Some q' \<Longrightarrow> q' \<in> states M"
proof -
  assume somep: "p = Some p'"
  with assms obtain p'' z where
      "p'' \<in> states M"
      "(rev (\<langle>x\<langle>), p'', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, p', x_end # \<rangle>z\<rangle>)"
    by (cases q) auto
  then show "p' \<in> states M" using nxt by blast
next
  assume someq: "q = Some q'"
  then show "q' \<in> states M" 
  proof (cases p)
    case None
    then show ?thesis using reachable_impl_in_states assms someq
      using T_None_Some_impl_reachable by blast
  next
    case (Some a)
    with someq assms obtain p' z where
      "p' \<in> states M"
      "(rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, a, x_end # \<rangle>z\<rangle>)"
      "(rev x_init, a, x_end # \<rangle>z\<rangle>) \<rightarrow>* (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)"
      by (smt (verit) T.cases left_steps_impl_steps option.discI option.inject
          rtranclp.rtrancl_into_rtrancl)
    then show ?thesis using steps_impl_in_states by blast
  qed
qed

text \<open>With \<open>crossn\<close> we show there is always a first boundary cross if a 2DFA ever crosses the 
      boundary:\<close>
lemma T_none_none_iff_not_some:
  "(\<exists>q. T None (Some q)) \<longleftrightarrow> \<not>T None None"
proof
  assume "\<exists>q. T None (Some q)"
  then show "\<not>T None None"
    by (metis T_None_Some_impl_reachable init_no_tr_indep)

next
  assume "\<not> T None None"
  then obtain q z where reach: "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by blast
  then obtain n where "x @ z \<rightarrow>\<^sup>X*(Suc n) (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" 
    proof -
    from reach obtain n where ncross: "x @ z \<rightarrow>\<^sup>X*(n) (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" 
      using reachable_xz_impl_crossn by blast
    moreover from this obtain m where "n = Suc m"
      proof -
        have "\<exists>m. n = Suc m"
        proof (rule ccontr)
          assume "\<not>?thesis"
          hence "n = 0" by presburger
          with ncross have "x @ z \<rightarrow>\<^sup>X*(0) (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by simp
          moreover have "left_config ([], init M, \<langle>x @ z\<rangle>)" unfolding left_config_def by simp
          moreover have "right_config (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" unfolding right_config_def by simp
          ultimately show False 
            using left_config_is_not_right_config no_cross_impl_same_side by auto 
        qed
        thus thesis using that by blast
      qed
     ultimately show thesis using that by blast
   qed
   then show "\<exists>q. T None (Some q)"
   proof (induction n arbitrary: q rule: less_induct)
     case (less n)
     then show ?case
     proof (cases n)
       case 0
       then obtain p p' where "x @ z \<rightarrow>\<^sup>X*(0) (rev x_init, p, x_end # \<rangle>z\<rangle>)"
                         "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>)"
                         "(rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
       proof -
         have "right_config (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" unfolding right_config_def by simp
         from right_config_impl_ltor_cross[OF less(2) this]
         obtain p p' z' where "x @ z \<rightarrow>\<^sup>X*(0) (rev x_init, p, x_end # \<rangle>z'\<rangle>)"
                           "(rev x_init, p, x_end # \<rangle>z'\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>)"
                           "(rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>) \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" using 0 by metis
         moreover from this unchanged_word have "\<rangle>z'\<rangle> = \<rangle>z\<rangle>" 
           by (meson right_steps_impl_steps same_append_eq unchanged_substrings)
         ultimately show thesis using that by auto
       qed
       hence "T None (Some p')" 
         by (metis Nil_is_append_conv init_tr left_config_def left_config_is_not_right_config length_0_conv
             length_greater_0_conv no_crossE not_Cons_self2 x_is_init_app_end)
       then show ?thesis by blast
     next
       case (Suc k)
       then obtain p p' where Suc_k_cross: "x @ z \<rightarrow>\<^sup>X*(Suc k) (rev x_init, p, x_end # \<rangle>z\<rangle>)"
                         "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>)"
                         "(rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
       proof -
         have "right_config (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" unfolding right_config_def by simp
         from right_config_impl_ltor_cross[OF less(2) this]
         obtain p p' z' where "x @ z \<rightarrow>\<^sup>X*(Suc k) (rev x_init, p, x_end # \<rangle>z'\<rangle>)"
                           "(rev x_init, p, x_end # \<rangle>z'\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>)"
                           "(rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>) \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" using Suc by metis
         moreover from this have "\<rangle>z'\<rangle> = \<rangle>z\<rangle>" 
           by (meson right_steps_impl_steps same_append_eq unchanged_substrings)
         ultimately show thesis using that by auto
       qed
       then obtain q' m where "x @ z \<rightarrow>\<^sup>X*(Suc m) (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" 
                              "k = Suc m"
       proof -
         from Suc_k_cross(1) obtain q' z' where k_steps: "x @ z \<rightarrow>\<^sup>X*(k) (rev (\<langle>x\<langle>), q', \<rangle>z'\<rangle>)" 
           using right_config_impl_ltor_cross
           by (smt (verit, del_insts) append.assoc append_Cons append_Nil crossn_impl_reachable
               left_config_impl_rtol_cross left_config_is_not_right_config list.distinct(1)
               reachable_right_conf_impl_substring_z rev.simps(2) rev_append rev_is_rev_conv rev_swap
               self_append_conv x_is_init_app_end)
         moreover from this have "\<rangle>z\<rangle> = \<rangle>z'\<rangle>"
           by (metis crossn_impl_reachable reach same_append_eq unchanged_substrings)
         moreover obtain m where "k = Suc m" 
         proof -
           have "k \<noteq> 0"
           proof
             assume "k = 0"
             with k_steps no_cross_impl_same_side show False 
               using left_config_def right_config_def left_config_is_not_right_config
               by (metis (no_types, lifting) add_0 bot_nat_0.extremum le_add_same_cancel2 length_0_conv
                   length_Suc_conv length_rev zero_less_Suc)
           qed
           thus thesis using that using not0_implies_Suc by auto
         qed
         ultimately show thesis using that by auto 
       qed
       then show ?thesis using less(1) Suc using less_Suc_eq by auto
     qed
   qed
qed

end


section \<open>2DFAs and Regular Languages\<close>

subsection \<open>Every Language Accepted by 2DFAs is Regular\<close>

context dfa2
begin

abbreviation "T \<equiv> dfa2_transition.T M" 
abbreviation "left_reachable \<equiv> dfa2_transition.left_reachable M"
abbreviation "left_config \<equiv> dfa2_transition.left_config"
abbreviation "right_config \<equiv> dfa2_transition.right_config" 
abbreviation "pf_init \<equiv> dfa2_transition.x_init"
abbreviation "pf_end \<equiv> dfa2_transition.x_end" 

abbreviation left_step' :: "'a config \<Rightarrow> 'a list \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>L\<lparr>_\<rparr> _" 55) where
  "c0 \<rightarrow>\<^sup>L\<lparr>x\<rparr> c1 \<equiv> dfa2_transition.left_step M x c0 c1"

abbreviation left_steps' :: "'a config \<Rightarrow> 'a list \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>L*\<lparr>_\<rparr> _" 55) where
  "c0 \<rightarrow>\<^sup>L*\<lparr>x\<rparr> c1 \<equiv> dfa2_transition.left_steps M x c0 c1"

abbreviation right_step' :: "'a config \<Rightarrow> 'a list \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>R\<lparr>_\<rparr> _" 55) where
  "c0 \<rightarrow>\<^sup>R\<lparr>x\<rparr> c1 \<equiv> dfa2_transition.right_step M x c0 c1"

abbreviation right_steps' :: "'a config \<Rightarrow> 'a list \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>R*\<lparr>_\<rparr> _" 55) where
  "c0 \<rightarrow>\<^sup>R*\<lparr>x\<rparr> c1 \<equiv> dfa2_transition.right_steps M x c0 c1"

abbreviation right_stepn' :: "'a config \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" 
                                                          ("_ \<rightarrow>\<^sup>R'(_,_') _" 55) where
  "c0 \<rightarrow>\<^sup>R(x,n) c1 \<equiv> dfa2_transition.right_stepn M x c0 n c1"

abbreviation left_reachable' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>L**\<lparr>_\<rparr> _" 55) where
  "w \<rightarrow>\<^sup>L**\<lparr>x\<rparr> c \<equiv> dfa2_transition.left_reachable M x w c"

abbreviation crossn' :: "'a config \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>X'(_,_') _" 55) where
  "w \<rightarrow>\<^sup>X(x,n) y \<equiv> dfa2_transition.crossn M x w n y"

abbreviation word_crossn' :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>X*'(_,_') _" 55) where
  "w \<rightarrow>\<^sup>X*(x, n) c \<equiv> dfa2_transition.word_crossn M x w n c" 

lemma T_eq_impl_rconf_reachable:
  assumes x_stepn:    "x @ z \<rightarrow>\<^sup>X*(x,n) (zs @ rev (\<langle>x\<langle>), q, v)"
      and not_empty:  "x \<noteq> []" "y \<noteq> []"
      and T_eq:       "T x = T y"
    shows "y @ z \<rightarrow>\<^sup>X*(y,n) (zs @ rev (\<langle>y\<langle>), q, v)"
using x_stepn proof (induction n arbitrary: zs q v rule: less_induct)
  case (less n)
  have T_axioms: "dfa2_transition M x" "dfa2_transition M y" using not_empty
     dfa2_axioms dfa2_transition_axioms_def dfa2_transition_def by auto
  have n_gt_0: "n > 0"
  proof (rule ccontr)
    assume "\<not>?thesis"
    hence "n = 0" by blast
    with less(2) have "(x @ z \<rightarrow>\<^sup>L**\<lparr>x\<rparr> (zs @ rev (\<langle>x\<langle>), q, v)) 
                     \<or> (([], init M, \<langle>x @ z\<rangle>) \<rightarrow>\<^sup>R*\<lparr>x\<rparr> (zs @ rev (\<langle>x\<langle>), q, v))" 
      using T_axioms(1) dfa2_transition.no_crossE by blast
    moreover have "left_config x ([], init M, \<langle>x @ z\<rangle>)" 
      unfolding dfa2_transition.left_config_def[OF T_axioms(1)] by simp
    moreover have "right_config x (zs @ rev (\<langle>x\<langle>), q, v)" 
      unfolding dfa2_transition.right_config_def[OF T_axioms(1)] by simp
    ultimately show False
      using T_axioms(1) \<open>n = 0\<close> dfa2_transition.left_config_is_not_right_config
        dfa2_transition.no_cross_impl_same_side less.prems by blast
  qed
  then obtain m where m_def: "n = Suc m" using not0_implies_Suc by auto
  obtain p q' where ltor: "x @ z \<rightarrow>\<^sup>X*(x,m) (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)"
                    "(rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)"
                    "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R*\<lparr>x\<rparr> (zs @ rev (\<langle>x\<langle>), q, v)"
  proof -
    have "right_config x (zs @ rev (\<langle>x\<langle>), q, v)" 
      using dfa2_transition.right_config_def[OF T_axioms(1)] by auto
    from m_def less(2) dfa2_transition.right_config_impl_ltor_cross[OF T_axioms(1)]
    obtain p q' z' where ltor': "x @ z \<rightarrow>\<^sup>X*(x,m) (rev (pf_init x), p, pf_end x # \<rangle>z'\<rangle>)"
                    "(rev (pf_init x), p, pf_end x # \<rangle>z'\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q', \<rangle>z'\<rangle>)"
                    "(rev (\<langle>x\<langle>), q', \<rangle>z'\<rangle>) \<rightarrow>\<^sup>R*\<lparr>x\<rparr> (zs @ rev (\<langle>x\<langle>), q, v)"
      by (metis \<open>dfa2_transition.right_config x (zs @ rev (\<turnstile> # \<Sigma> x), q, v)\<close>)
    moreover have "\<rangle>z\<rangle> = \<rangle>z'\<rangle>"
    proof -
      from ltor' have "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z'\<rangle>)" 
        using dfa2_transition.crossn_impl_reachable[OF T_axioms(1)]
        by (meson rtranclp.rtrancl_into_rtrancl)
      with unchanged_word show ?thesis by force
    qed
    ultimately show thesis using that by presburger
  qed
  have y_rsteps_zs: "(rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R*\<lparr>y\<rparr> (zs @ rev (\<langle>y\<langle>), q, v)"
  proof -
      from ltor have xq'z_reach: "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" 
        by (meson T_axioms(1) dfa2_transition.crossn_impl_reachable rtranclp.rtrancl_into_rtrancl)
      from ltor(3) obtain i where rstepi:
        "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R(x,i) (zs @ rev (\<langle>x\<langle>), q, v)" 
        by (meson rtranclp_imp_relpowp)
      hence stepi: "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>(i) (zs @ rev (\<langle>x\<langle>), q, v)"
        by (metis T_axioms(1) dfa2_transition.right_step.simps relpowp_mono)
      moreover have 
        x_all_geq: "\<forall>j\<le>i. \<forall>u' p' v'. ((rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)\<rightarrow>(j) (u', p', v')) 
                \<longrightarrow> length (rev (\<langle>x\<langle>)) \<le> length u'"
      proof ((rule allI)+, rule impI)+
        fix j u' p' v'
        assume j_lt_i: "j \<le> i"
           and stepj: "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)\<rightarrow>(j) (u', p', v')"
        with dfa2_transition.right_stepn_impl_interm_right_stepn[OF T_axioms(1)]
        have "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)\<rightarrow>\<^sup>R(x,j) (u', p', v')"
          using rstepi by blast
        hence "right_config x (u', p', v')" using dfa2_transition.right_config_def[OF T_axioms(1)]
          by (metis T_axioms(1) dfa2_transition.rstepE length_rev nat_le_linear relpowp_E)
        thus "length (rev (\<langle>x\<langle>)) \<le> length u'" using dfa2_transition.right_config_def[OF T_axioms(1)]
          by auto        
      qed
      ultimately have stepi_y: "(rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>(i) (zs @ rev (\<langle>y\<langle>), q, v)" 
                      and y_all_geq: 
                      "\<forall>j\<le>i. \<forall>u' p' v'. ((rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)\<rightarrow>(j) (u', p', v')) 
                        \<longrightarrow> length (rev (\<langle>y\<langle>)) \<le> length u'"
        using all_geq_left_impl_left_indep[OF xq'z_reach stepi x_all_geq] by blast+
      thus ?thesis 
      proof -
        note rconf_def_y = dfa2_transition.right_config_def[OF T_axioms(2)]
        from stepi_y obtain f where f_def:
          "f 0 = (rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)"
          "f i = (zs @ rev (\<langle>y\<langle>), q, v)"
          "\<forall>n<i. f n \<rightarrow> f (Suc n)" 
          by (metis relpowp_fun_conv[of i "(\<rightarrow>)" "(rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)" "(zs @ rev (\<langle>y\<langle>), q, v)"])
        hence "\<forall>n<i. (f 0 \<rightarrow>(n) f n)"
          by (metis Suc_lessD less_trans_Suc relpowp_fun_conv)
        have rstepn_fn: "\<forall>n<i. ((rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R(y,n) f n)"
        proof (rule allI, rule impI)
          fix n
          assume n_lt_i: "n < i"
          then show "((rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R(y,n) f n)"
          proof (induction n)
            case (Suc n)
            hence rstepn: "((rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R(y,n) f n)" by simp
            moreover from this have fn_rconf: "right_config y (f n)" 
              by (metis T_axioms(2) dfa2_transition.rstepE le_refl length_rev rconf_def_y relpowp_E)
            moreover have "f n \<rightarrow>\<^sup>R\<lparr>y\<rparr> f (Suc n)"
            proof -
              from f_def Suc have "f n \<rightarrow> f (Suc n)" by simp
              moreover from this rstepn have "(rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>(Suc n) f (Suc n)"
                using Suc.prems \<open>\<forall>n<i. ((\<rightarrow>) ^^ n) (f 0) (f n)\<close> f_def(1) by auto
              moreover have "right_config y (f (Suc n))" 
              proof -
                obtain u p v where "f (Suc n) = (u, p, v)" using prod_cases3 by blast
                moreover from this y_all_geq have "right_config y (u, p, v)"
                  using rstepn 
                  by (metis Suc.prems \<open>((\<rightarrow>) ^^ Suc n) (rev (\<turnstile> # \<Sigma> y), q', \<Sigma> z @ [\<stileturn>]) (f (Suc n))\<close> 
                      length_rev nat_less_le rconf_def_y)
                ultimately show ?thesis by simp
              qed
              ultimately show ?thesis 
                by (simp add: T_axioms(2) dfa2_transition.right_step.simps fn_rconf)
            qed
            ultimately show ?case by auto
          qed (use f_def in simp)
        qed
        thus ?thesis 
        proof (cases i)
          case 0
          then show ?thesis using f_def by simp
        next
          case (Suc k)
          with rstepn_fn have stepk: "(rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R(y,k) f k" by blast
          moreover have "... \<rightarrow>\<^sup>R\<lparr>y\<rparr> (zs @ rev (\<langle>y\<langle>), q, v)"
          proof -
            from Suc f_def have "f k \<rightarrow> (zs @ rev (\<langle>y\<langle>), q, v)" by auto
            moreover have "right_config y (f k)" 
              using stepk 
              by (metis T_axioms(2) dfa2_transition.right_config_def dfa2_transition.right_step.simps 
                  length_rev less_or_eq_imp_le relpowp_E)
            moreover have "right_config y (zs @ rev (\<langle>y\<langle>), q, v)"
              unfolding rconf_def_y by simp
            ultimately show ?thesis
              by (simp add: T_axioms(2) dfa2_transition.right_step.simps)
          qed
          ultimately show ?thesis 
            by (meson relpowp_imp_rtranclp rtranclp.rtrancl_into_rtrancl) 
        qed
      qed
  qed
  show ?case
  proof (cases m)
    case 0
    with ltor have "x @ z \<rightarrow>\<^sup>L**\<lparr>x\<rparr> (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)"
      by (metis T_axioms(1) dfa2_transition.left_config_lt_right_config
          dfa2_transition.left_reachable_impl_left_config dfa2_transition.no_crossE length_greater_0_conv
          list.size(3) rtranclp.rtrancl_refl)
    with ltor have "T x None (Some q')"
      using T_axioms(1) dfa2_transition.init_tr by blast
    with T_eq obtain p' where "y @ z \<rightarrow>\<^sup>L**\<lparr>y\<rparr> (rev (pf_init y), p', pf_end y # \<rangle>z\<rangle>)"
                              "(rev (pf_init y), p', pf_end y # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)"
      using dfa2_transition.init_tr_indep[OF T_axioms(2)] by auto
    hence "y @ z \<rightarrow>\<^sup>X*(y,Suc 0) (rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)"
      by (meson T_axioms(2) dfa2_transition.crossn_ltor dfa2_transition.left_reachable_impl_left_config
          dfa2_transition.no_crossl rtranclp.rtrancl_refl)
    then have "y @ z \<rightarrow>\<^sup>X*(y,Suc 0) (zs @ rev (\<langle>y\<langle>), q, v)"
      using dfa2_transition.crossn_trans[OF T_axioms(2)] y_rsteps_zs
      by (meson T_axioms(2)
          \<open>\<And>thesis. (\<And>p'. \<lbrakk>y @ z \<rightarrow>\<^sup>L**\<lparr>y\<rparr> (rev (pf_init y), p', pf_end y # \<rangle>z\<rangle>); 
                    (rev (pf_init y), p', pf_end y # \<rangle>z\<rangle>) \<rightarrow> (rev (\<turnstile> # \<Sigma> y), q', \<Sigma> z @ [\<stileturn>])\<rbrakk> 
          \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
          dfa2_transition.crossn_ltor dfa2_transition.left_reachable_impl_left_config
          dfa2_transition.left_steps_impl_left_config_conv dfa2_transition.no_crossl)
    then show ?thesis using 0 m_def by blast
  next
    case (Suc k)
    with ltor(1) obtain p' q'' where rtol:
      "x @ z \<rightarrow>\<^sup>X*(x,k) (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>)"
      "(rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow> (rev (pf_init x), q'', pf_end x # \<rangle>z\<rangle>)"
      "(rev (pf_init x), q'', pf_end x # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L*\<lparr>x\<rparr> (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)"
    proof -
      note lconf_def_x = dfa2_transition.left_config_def[OF T_axioms(1)]
      have "left_config x (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)" 
        using lconf_def_x dfa2_transition.x_defs[OF T_axioms(1)] by auto
      with ltor(1) Suc dfa2_transition.left_config_impl_rtol_cross[OF T_axioms(1)]
      obtain p' q'' z' where
        "x @ z \<rightarrow>\<^sup>X*(x,k) (rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>)"
        "(rev (\<langle>x\<langle>), p', \<rangle>z'\<rangle>) \<rightarrow> (rev (pf_init x), q'', pf_end x # \<rangle>z'\<rangle>)"
        "(rev (pf_init x), q'', pf_end x # \<rangle>z'\<rangle>) \<rightarrow>\<^sup>L*\<lparr>x\<rparr> (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)"
        by metis
      moreover from this have "\<rangle>z'\<rangle> = \<rangle>z\<rangle>" using unchanged_word 
        by (metis T_axioms(1) dfa2_transition.crossn_impl_reachable mapl_app_mapr_eq_map 
            rev_rev_ident same_append_eq)
      ultimately show thesis using that by simp
    qed
    with ltor(2) have Tx_Some: "T x (Some q'') (Some q')"
      by (metis T_axioms(1) dfa2_transition.crossn_impl_reachable
          dfa2_transition.some_tr init steps_impl_in_states)
    from Suc m_def have "k < n" by simp
    with rtol(1) have "y @ z \<rightarrow>\<^sup>X*(y,k) (rev (\<langle>y\<langle>), p', \<rangle>z\<rangle>)"
      using less(1)[of _ "[]"] by simp 
    moreover have "... \<rightarrow> (rev (pf_init y), q'', pf_end y # \<rangle>z\<rangle>)"
    proof -
      have z_nempty: "\<rangle>z\<rangle> \<noteq> []" by simp
      with rtol(2) have p'_nxt: "nxt M p' (hd (\<rangle>z\<rangle>)) = (q'', Left)" by auto
      have "(rev (\<langle>y\<langle>), p', \<rangle>z\<rangle>) = (rev (pf_init y @ [pf_end y]), p', \<rangle>z\<rangle>)"
        using dfa2_transition.x_defs[OF T_axioms(2)] by simp
      also have "... = (pf_end y # rev (pf_init y), p', \<rangle>z\<rangle>)" by simp
      also have "... \<rightarrow> (rev (pf_init y), q'', pf_end y # \<rangle>z\<rangle>)" using p'_nxt z_nempty 
        by (metis list.exhaust list.sel(1) step_left)
      finally show ?thesis .
    qed
    moreover from Tx_Some T_eq obtain r where 
      "... \<rightarrow>\<^sup>L*\<lparr>y\<rparr> (rev (pf_init y), r, pf_end y # \<rangle>z\<rangle>)"
      "(rev (pf_init y), r, pf_end y # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)"
        using that dfa2_transition.some_tr_indep[OF T_axioms(2)] by metis
    ultimately show ?thesis using y_rsteps_zs 
      using Suc T_axioms(2) dfa2_transition.crossn_ltor dfa2_transition.crossn_rtol m_def
      by blast
  qed
qed



text \<open>The initial implication:\<close>
theorem T_eq_impl_eq_app_right:
  assumes not_empty:  "x \<noteq> []" "y \<noteq> []"
      and T_eq:       "T x = T y"
      and xz_in_lang: "x @ z \<in> Lang"
    shows "y @ z \<in> Lang"
proof -
  from not_empty dfa2_axioms have T_axioms: "dfa2_transition M x" "dfa2_transition M y"
    using dfa2_transition_def unfolding dfa2_transition_axioms_def by auto
  with xz_in_lang obtain u v where x_acc_reachable: "x @ z \<rightarrow>** (u, acc M, v)" 
    unfolding Lang_def by blast
  with dfa2_transition.reachable_xz_impl_crossn[OF T_axioms(1)] 
  obtain n where "x @ z \<rightarrow>\<^sup>X*(x,n) (u, acc M, v)" by blast
  consider (left) "left_config x (u, acc M, v)" | (right) "right_config x (u, acc M, v)"
    unfolding dfa2_transition.left_config_def[OF T_axioms(1)]
              dfa2_transition.right_config_def[OF T_axioms(1)] 
    by fastforce
  then show ?thesis
  proof cases
    case left
    then obtain xs where "rev u @ xs = \<langle>x\<langle>" "xs @ \<rangle>z\<rangle> = v" "xs \<noteq> []"
    proof -
      obtain xs where "rev u @ xs = \<langle>x\<langle>" "xs @ \<rangle>z\<rangle> = v"
        by (smt (verit, ccfv_threshold) left T_axioms(1) dfa2_transition.left_config_def
            dfa2_transition.reachable_lconfig_impl_substring_x rtranclp.rtrancl_refl x_acc_reachable)
      moreover from this left have "xs \<noteq> []" using dfa2_transition.left_config_def[OF T_axioms(1)] by auto
      ultimately show thesis using that by blast
    qed
    with acc_impl_reachable_substring have revxsu_reach: "x @ z \<rightarrow>** (rev xs @ u, acc M, \<rangle>z\<rangle>)" 
      by (smt (verit, ccfv_SIG) rtranclp_trans snoc_eq_iff_butlast x_acc_reachable)
    obtain m where "x @ z \<rightarrow>\<^sup>X*(x,m) (rev (\<langle>x\<langle>), acc M, \<rangle>z\<rangle>)"
    proof -
      from revxsu_reach dfa2_transition.reachable_xz_impl_crossn[OF T_axioms(1)] 
      obtain m where "x @ z \<rightarrow>\<^sup>X*(x,m) (rev xs @ u, acc M, \<rangle>z\<rangle>)" by blast
      moreover have "rev xs @ u = rev (\<langle>x\<langle>)"
        by (metis \<open>rev u @ xs = \<turnstile> # \<Sigma> x\<close> rev_append rev_rev_ident)
      ultimately show thesis using that by simp
    qed
    with T_eq_impl_rconf_reachable[OF _ not_empty T_eq, of _ _ "[]"] 
    have "y @ z \<rightarrow>\<^sup>X*(y,m) (rev (\<langle>y\<langle>), acc M, \<rangle>z\<rangle>)"
      by auto      
    hence "y @ z \<rightarrow>** (rev (\<langle>y\<langle>), acc M, \<rangle>z\<rangle>)" using dfa2_transition.crossn_impl_reachable[OF T_axioms(2)]
      by blast
    then show ?thesis using Lang_def by blast
  next
    case right
    from x_acc_reachable dfa2_transition.reachable_xz_impl_crossn[OF T_axioms(1)]
    obtain n where x_crossn: "x @ z \<rightarrow>\<^sup>X*(x,n) (u, acc M, v)" by blast
    from right obtain zs where zs_defs: "rev zs @ rev (\<langle>x\<langle>) = u" "zs @ v = \<rangle>z\<rangle>" 
      by (metis T_axioms(1) dfa2_transition.reachable_right_conf_impl_substring_z rev_append
          x_acc_reachable)
    with T_eq_impl_rconf_reachable[OF _ not_empty T_eq] have 
      "y @ z \<rightarrow>\<^sup>X*(y,n) (rev zs @ rev (\<langle>y\<langle>), acc M, v)"
      using x_crossn by blast
    then show ?thesis using dfa2_transition.crossn_impl_reachable[OF T_axioms(2)] 
      unfolding Lang_def by blast
  qed
qed

text \<open>There are finitely many transitions:\<close>
definition \<T> :: "'a list \<Rightarrow> (state option \<times> state option) set" where
  "\<T> x \<equiv> {(q, p). dfa2_transition M x \<and> T x q p}"

lemma \<T>_subset_states_none:
  shows "\<T> x \<subseteq> ({Some q | q. q \<in> states M} \<union> {None}) \<times> ({Some q | q. q \<in> states M} \<union> {None})"
    (is "_ \<subseteq> ?S \<times> _")
proof (cases x)
  case Nil
  then show ?thesis unfolding \<T>_def 
    by (simp add: dfa2_transition_axioms_def dfa2_transition_def)
next
  case (Cons a as)
  show ?thesis 
  proof 
    from Cons have trans: "dfa2_transition M x" 
      unfolding dfa2_transition_axioms_def dfa2_transition_def 
      by (simp add: dfa2_axioms)
    fix pq :: "state option \<times> state option"
    assume "pq \<in> \<T> x"
    then obtain p q where pq_def: "pq = (p, q)" "(p, q) \<in> \<T> x"
      by (metis surj_pair)
    have "(p, q) \<in> ?S \<times> ?S"
      using pq_def(2) dfa2_transition.T_impl_in_states[OF trans] unfolding \<T>_def 
      by fast
    thus "pq \<in> ?S \<times> ?S" using pq_def by simp
  qed
qed

lemma \<T>_Nil_eq_\<T>_Nil:
  assumes "\<T> x = \<T> []"
  shows "x = []"
proof (rule ccontr)
  assume nempty: "x \<noteq> []"
  then obtain p q where "T x p q" 
    using dfa2_transition.T_none_none_iff_not_some 
    by (metis dfa2_axioms dfa2_transition_axioms_def dfa2_transition_def)
  moreover from nempty have "dfa2_transition M x" 
    by (simp add: dfa2_axioms dfa2_transition.intro dfa2_transition_axioms_def)
  moreover from assms have "\<T> x = {}" unfolding \<T>_def
    by (simp add: dfa2_transition_axioms_def dfa2_transition_def) 
  ultimately show False unfolding \<T>_def by blast 
qed

lemma T_eq_is_\<T>_eq:
  assumes "dfa2_transition M x"
          "dfa2_transition M y"
        shows "T x = T y \<longleftrightarrow> \<T> x = \<T> y"
  using assms \<T>_def by fastforce

(* TODO: rm after next release because in devel *)

definition kern :: "('b \<Rightarrow> 'c) \<Rightarrow> ('b \<times> 'b) set" where
  "kern f \<equiv> {(x, y). f x = f y}"

lemma equiv_kern:
  "equiv UNIV (kern f)"
  unfolding kern_def by (simp add: equivI refl_on_def sym_def trans_def eq_app_right_def)

lemma inj_on_vimage_image: "inj_on (\<lambda>b. f -` {b}) (f ` A)"
  using inj_on_def by fastforce

lemma kern_Image: "kern f `` A = f -` (f ` A)"
  unfolding kern_def by (auto simp: rev_image_eqI)

lemma quotient_kern_eq_image: "A // kern f = (\<lambda>b. f-` {b}) ` f ` A"
  by (auto simp: quotient_def kern_Image)

lemma bij_betw_image_quotient_kern: 
  "bij_betw (\<lambda>b. f -` {b}) (f ` A) (A // kern f)"
  unfolding bij_betw_def 
  by (simp add: inj_on_vimage_image quotient_kern_eq_image)

lemma finite_quotient_kern_iff_finite_image:
  "finite (A // kern \<T>) = finite (\<T> ` A)"
  by (metis bij_betw_finite bij_betw_image_quotient_kern)
(* end of rm *)

theorem \<T>_finite_image:
  "finite (\<T> ` UNIV)"
proof -
  let ?S = "{Some q | q. q \<in> states M} \<union> {None}"
  have finite_state_options: "finite ?S" using finite by simp 
  hence "\<T> ` UNIV \<subseteq> Pow (?S \<times> ?S)" using \<T>_subset_states_none by blast
  moreover have "finite (Pow (?S \<times> ?S))" using finite_state_options by simp
  ultimately show "finite (\<T> ` UNIV)" by (simp add: finite_subset)
qed

lemma kern_\<T>_subset_eq_app_right:
  "kern \<T> \<subseteq> eq_app_right Lang"
proof 
  fix xy
  assume "xy \<in> kern \<T>"
  then obtain x y where xy_def: "xy = (x, y)" "\<T> x = \<T> y" 
    unfolding kern_def by blast
  show "xy \<in> eq_app_right Lang"
  proof (cases x)
    case Nil
    with xy_def have "y = []" using \<T>_Nil_eq_\<T>_Nil by simp
    with xy_def Nil have "(x, y) = ([], [])" by simp
    then show ?thesis using xy_def unfolding eq_app_right_def by simp
  next
    case (Cons a as)
    moreover from this \<T>_Nil_eq_\<T>_Nil xy_def have "y \<noteq> []" by auto
    ultimately have T_axioms: "dfa2_transition M x"
                              "dfa2_transition M y"
      by (simp add: dfa2_axioms dfa2_transition.intro dfa2_transition_axioms.intro)+
    then show ?thesis using T_eq_impl_eq_app_right
      unfolding eq_app_right_def
      by (smt (verit) T_eq_is_\<T>_eq \<T>_Nil_eq_\<T>_Nil case_prod_conv mem_Collect_eq xy_def(1,2))
  qed
qed

text \<open>Lastly, \<open>eq_app_right\<close> is of finite index, from which the theorem follows by Myhill-Nerode:\<close>
theorem dfa2_Lang_regular:
  "regular Lang"
proof -
  from \<T>_finite_image have "finite (UNIV // kern \<T>)"
    using finite_quotient_kern_iff_finite_image by blast
  then have "finite (UNIV // eq_app_right Lang)" 
    using equiv_kern equiv_eq_app_right finite_refines_finite kern_\<T>_subset_eq_app_right 
    by blast
  then show "regular Lang" using L3_1 by auto
qed

end


subsection \<open>Every Regular Language is Accepted by Some 2DFA\<close>

abbreviation step' :: "'a config \<Rightarrow> 'a dfa2 \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>\<lparr>_\<rparr> _" 55) where
  "c0 \<rightarrow>\<lparr>M\<rparr> c1 \<equiv> dfa2.step M c0 c1"

abbreviation steps' :: "'a config \<Rightarrow> 'a dfa2 \<Rightarrow> 'a config \<Rightarrow> bool" ("_ \<rightarrow>*\<lparr>_\<rparr> _" 55) where
  "c0 \<rightarrow>*\<lparr>M\<rparr> c1 \<equiv> dfa2.steps M c0 c1"

(* TODO rm after next release *)
lemma finite_arbitrarily_large_disj:
  "\<lbrakk> infinite(UNIV::'a set); finite (A::'a set) \<rbrakk> \<Longrightarrow> \<exists>B. finite B \<and> card B = n \<and> A \<inter> B = {}"
using infinite_arbitrarily_large[of "UNIV - A"]
by fastforce

lemma infinite_UNIV_state: "infinite(UNIV :: state set)"
  using hmem_HF_iff by blast

text \<open>Let \<open>L \<subseteq> \<Sigma>\<^sup>*\<close> be regular. Then there exists a DFA \<open>M = (Q, q\<^sub>0, F, \<delta>)\<close>\footnote{We define automata
      in accordance with the records @{typ "'a dfa"} and @{typ "'a dfa2"}, which do not define an
      alphabet explicitly. Hence, we implicitly set \<open>\<Sigma>\<close> as the input alphabet for \<open>M\<close> and \<open>M'\<close>.} 
      that accepts \<open>L\<close>. Furthermore, let \<open>q\<^sub>0, q\<^sub>a, q\<^sub>r \<notin> Q\<close> be pairwise distinct states.
      We construct the 2DFA \<open>M' = (Q \<union> {q\<^sub>0', q\<^sub>a, q\<^sub>r}, q\<^sub>0', q\<^sub>a, q\<^sub>r, \<delta>')\<close> where\newline
      \[ 
      \delta'(q,a) = \begin{cases} 

          (\delta(q,a), Right) & \text{if } q \in Q \text{ and } a \in \Sigma \\
          (q_a, Right) & \text{if } q = q_a \text{ and } a \in \Sigma \\
          (q_r, Right) & \text{if } q \in \{q_0', q_r\} \text{ and } a \in \Sigma \\

          (q_0, Right) & \text{if } (q,a) = (q_0', \vdash) \\
          (q_a, Right) & \text{if } (q,a) = (q_a, \vdash) \\
          (q_r, Right) & \text{if } q \in Q \cup \{q_r\} \text{ and } a = \vdash \\

          (q_a, Left) & \text{if } q \in F \cup \{q_a\} \text{ and } a = \dashv \\
          (q_r, Left) & \text{otherwise}
          \end{cases}
      \]\newline
      Intuitively, \<open>M'\<close> executes \<open>M\<close> on a word \<open>w \<in> \<Sigma>\<^sup>*\<close>, and accepts it if and only if \<open>M\<close> does so:\newline
      Recall that the input of \<open>M'\<close> for \<open>w\<close> is \<open>\<turnstile>w\<stileturn>\<close>, and therefore, \<open>M'\<close> always reads \<open>\<turnstile>\<close> in its 
      initial configuration. The start state of \<open>M'\<close>, \<open>q\<^sub>0'\<close>, moves the head of \<open>M'\<close> to the 
      first character of \<open>w\<close>, and \<open>M'\<close> goes into state \<open>q\<^sub>0\<close>, the start state of \<open>M\<close>. Then, \<open>M'\<close>
      reads each character of \<open>w\<close> moving exclusively to the right, mimicking the behavior of a 
      traditional DFA. Since \<open>M'\<close> computes its next state with \<open>\<delta>\<close>, it behaves exactly like \<open>M\<close> until 
      the entire word is read.\newline When \<open>M'\<close> finishes reading \<open>w\<close>, the head is on \<open>\<stileturn>\<close>, and its 
      current state is the same state \<open>M\<close> is in after reading \<open>w\<close>. It is worth noting that, since
      the markers aren't in \<open>\<Sigma>\<close>, \<open>M'\<close> will not reach \<open>\<stileturn>\<close> while simulating the execution of \<open>M\<close>.
      Hence, if the state of \<open>M'\<close> when reading \<open>\<stileturn>\<close> is in \<open>F\<close>, \<open>M\<close> accepts \<open>w\<close>, and \<open>M'\<close> goes into its accepting state, \<open>q\<^sub>a\<close>.
      Otherwise, it goes into its rejecting state \<open>q\<^sub>r\<close>. At this point, the simulation of \<open>M\<close> is over,
      and \<open>M'\<close> behaves in accordance to the formal definition of 2DFAs. In particular, it always
      remains in its current state, and it moves to the right for all symbols except for \<open>\<stileturn>\<close>.\newline
      We now formally prove that \<open>L(M') = L(M)\<close>:\<close>
     
theorem regular_language_impl_dfa2:
  assumes "regular L"
  obtains M M' q0 qa qr where 
    "dfa M" "dfa.language M = L"
    "{q0, qa, qr} \<inter> dfa.states M = {}"
    "qa \<noteq> qr" 
    "qa \<noteq> q0"
    "qr \<noteq> q0"
    "dfa2 M'" "dfa2.Lang M' = L"
    "M' = (let \<delta> = (\<lambda>q a. case a of 
            Letter a' \<Rightarrow> (if q \<in> dfa.states M then ((dfa.nxt M) q a', Right) 
                          else if q = qa then (qa, Right) else (qr, Right)) |
            Marker Left \<Rightarrow> (if q = q0 then (dfa.init M, Right) 
                          else if q = qa then (qa, Right) else (qr, Right)) |
            Marker Right \<Rightarrow> (if q \<in> dfa.final M \<or> q = qa then (qa, Left) else (qr, Left))) 
          in \<lparr>dfa2.states = dfa.states M \<union> {q0, qa, qr},
                      dfa2.init = q0,
                      dfa2.acc = qa,
                      dfa2.rej = qr,
                      dfa2.nxt = \<delta>\<rparr>)"
proof -
  from assms obtain M where M_def: "dfa M" "dfa.language M = L"
    unfolding regular_def by blast
  then obtain q0 qa qr where q_defs:
    "{q0, qa, qr} \<inter> dfa.states M = {}"
    "qa \<noteq> qr" 
    "qa \<noteq> q0"
    "qr \<noteq> q0"
  proof -
    from dfa.finite[OF \<open>dfa M\<close>] obtain Q where
      "card Q = Suc (Suc (Suc 0))"
      "Q \<inter> dfa.states M = {}"
      using infinite_UNIV_state
      by (metis finite_arbitrarily_large_disj inf_commute)
    thus thesis using that distinct_def
      by (smt (verit, ccfv_SIG) card_Suc_eq insertCI)
  qed
  
  let ?\<delta> = "(\<lambda>q a. case a of 
            Letter a' \<Rightarrow> (if q \<in> dfa.states M then ((dfa.nxt M) q a', Right) 
                          else if q = qa then (qa, Right) else (qr, Right)) |
            Marker Left \<Rightarrow> (if q = q0 then (dfa.init M, Right) 
                          else if q = qa then (qa, Right) else (qr, Right)) |
            Marker Right \<Rightarrow> (if q \<in> dfa.final M \<or> q = qa then (qa, Left) else (qr, Left)))"

  let ?M' = "\<lparr>dfa2.states = dfa.states M \<union> {q0, qa, qr},
                      dfa2.init = q0,
                      dfa2.acc = qa,
                      dfa2.rej = qr,
                      dfa2.nxt = ?\<delta>\<rparr>"
    
  interpret M: dfa2 ?M'
  proof (standard, goal_cases)
    case (6 p a q d)
    then show ?case 
    proof (cases a)
      case (Letter a')
      with 6 have d_eq_ite: "?\<delta> p a = (if p \<in> dfa.states M then (dfa.nxt M p a', Right) 
         else if p = qa then (qa, Right) else (qr, Right))" (is "_ = ?ite") by simp
      then show ?thesis 
      proof (cases "p \<in> dfa.states M")
        case True
        then show ?thesis using Letter dfa.nxt[OF \<open>dfa M\<close> True] 6 by fastforce
      next
        case False
        then show ?thesis using 6 using Letter 
          by (smt (verit) Un_def dfa2.select_convs(1,5) insert_compr mem_Collect_eq old.prod.inject
              symbol.simps(5))
      qed
    next
      case (Marker d')
      then show ?thesis using 6 
        by (smt (verit) Un_iff \<open>dfa M\<close> dfa.init dfa2.select_convs(1,5) dir.exhaust dir.simps(3,4) 
            insertCI  old.prod.inject symbol.simps(6))
    qed   
  next
    case (7 q p d)
    then show ?case 
      by (smt (verit, best) dfa2.select_convs(5) dir.simps(3) prod.inject symbol.simps(6))
  next
    case (8 q p d)
    then show ?case 
      by (smt (verit, best) dfa2.select_convs(5) dir.simps(4) prod.inject symbol.simps(6))
  next
    case (9 a q)
    then consider (acc) "q = qa" | (rej) "q = qr" by auto
    then show ?case
    proof cases
      case acc
      then show ?thesis
      proof (cases a)
        case (Letter a')
        then show ?thesis using acc q_defs by simp
      next
        case (Marker d)
        then show ?thesis
          by (smt (verit, ccfv_SIG) "9"(1) acc dfa2.select_convs(5) dir.exhaust dir.simps(3) q_defs(3)
              symbol.simps(6))
      qed 
    next
      case rej
      then show ?thesis
      proof (cases a)
        case (Letter a')
        then show ?thesis using rej q_defs by simp
      next
        case (Marker d)
        then show ?thesis
          by (smt (verit) "9"(1) dfa2.select_convs(5) dir.exhaust dir.simps(3) q_defs(4) rej
              symbol.simps(6))
      qed
    qed
  next
    case (10 q)
    then show ?case using \<open>dfa M\<close> dfa_def q_defs(1) by auto
  qed (use q_defs dfa.finite[OF \<open>dfa M\<close>] in simp)+

  have nextl_reachable:
         "\<forall>w. (([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<langle>w\<langle>), (dfa.nextl M (dfa.init M) w, [\<stileturn>])))"
  proof
    fix w
    have step: "([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>\<lparr>?M'\<rparr> ([\<turnstile>], dfa.init M, \<rangle>w\<rangle>)"
      using M.step_right by auto
    have reach:
      "\<forall>u. \<forall>q\<in>dfa.states M. ((u, q, \<rangle>w\<rangle>) 
        \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<Sigma> w) @ u, dfa.nextl M q w, [\<stileturn>]))" 
    proof (standard, standard)
      fix u q
      assume in_Q: "q \<in> dfa.states M"
      show "(u, q, \<rangle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<Sigma> w) @ u, (dfa.nextl M q w, [\<stileturn>]))"
        using in_Q proof (induction w arbitrary: q u)
        case Nil
        moreover from this have "dfa.nextl M q [] = q" 
          by (simp add: \<open>dfa M\<close> dfa.nextl.simps(1))
        moreover from this have "(u, q, \<rangle>[]\<rangle>) = (rev (\<Sigma> []) @ u, dfa.nextl M q [], [\<stileturn>])" by simp
        ultimately show ?case by simp 
      next
        case (Cons x xs)
        from Cons(2) have step1: "(u, q, \<rangle>x # xs\<rangle>) \<rightarrow>\<lparr>?M'\<rparr> (Letter x # u, dfa.nxt M q x, \<rangle>xs\<rangle>)"
                          "dfa.nxt M q x \<in> dfa.states M"
          using M.step.simps by (auto simp add: \<open>dfa M\<close> dfa.nxt)
        with Cons(1) have 
          "(Letter x # u, dfa.nxt M q x, \<rangle>xs\<rangle>) 
            \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<Sigma> xs) @ (Letter x # u), dfa.nextl M (dfa.nxt M q x) xs, [\<stileturn>])"
          by simp
        moreover have "... = (rev (\<Sigma> (x # xs)) @ u, dfa.nextl M q (x # xs), [\<stileturn>])"
          by (simp add: \<open>dfa M\<close> dfa.nextl.simps(2))
        ultimately show ?case using step1 by auto
      qed
    qed
    hence steps: "([\<turnstile>], dfa.init M, \<rangle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<langle>w\<langle>), (dfa.nextl M (dfa.init M) w, [\<stileturn>]))"
    proof -
      have "dfa.init M \<in> dfa.states M" using \<open>dfa M\<close> dfa.init by blast
      with reach show ?thesis by simp
    qed
    with step show "([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<langle>w\<langle>), (dfa.nextl M (dfa.init M) w, [\<stileturn>]))"
      by simp
  qed

  have "M.Lang = dfa.language M"
  proof 
    show "M.Lang \<subseteq> dfa.language M"
    proof
      fix w
      assume "w \<in> M.Lang"
      then obtain u v where acc_reachable: "([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (u, dfa2.acc ?M', v)"
        using M.Lang_def by blast
      from nextl_reachable obtain q where final_state:
        "([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<langle>w\<langle>), q, [\<stileturn>])"
        "q \<in> dfa.states M"  "dfa.nextl M (dfa.init M) w = q" 
        using \<open>dfa M\<close> dfa.nextl_init_state by blast
      with acc_reachable have acc_step:
        "(rev (\<langle>w\<langle>), q, [\<stileturn>]) \<rightarrow>\<lparr>?M'\<rparr> (tl (rev (\<langle>w\<langle>)), dfa2.acc ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>])" 
      proof -
        have disj: "((rev (\<langle>w\<langle>), q, [\<stileturn>]) \<rightarrow>\<lparr>?M'\<rparr> (tl (rev (\<langle>w\<langle>)), dfa2.acc ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>])) 
              \<or> ((rev (\<langle>w\<langle>), q, [\<stileturn>]) \<rightarrow>\<lparr>?M'\<rparr> (tl (rev (\<langle>w\<langle>)), dfa2.rej ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>]))"
              (is "?acc_step \<or> ?rej_step")
        proof (cases "q \<in> dfa.final M")
          case True
          hence "nxt ?M' q \<stileturn> = (dfa2.acc ?M', Left)" by auto
          hence ?acc_step using M.step.simps by fastforce
          then show ?thesis by simp
        next
          case False
          moreover from q_defs final_state have "q \<noteq> dfa2.acc ?M'" by auto
          ultimately have "nxt ?M' q \<stileturn> = (dfa2.rej ?M', Left)" by auto
          hence ?rej_step using M.step.simps by fastforce
          then show ?thesis by simp
        qed
        show ?thesis
        proof (rule ccontr)
          assume "\<not>?thesis"
          with disj have ?rej_step by blast
          hence rej_reachable: 
            "([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (tl (rev (\<langle>w\<langle>)), dfa2.rej ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>])"
            using final_state by auto
          with acc_reachable  consider 
            "((tl (rev (\<langle>w\<langle>)), dfa2.rej ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>]) \<rightarrow>*\<lparr>?M'\<rparr> (u, dfa2.acc ?M', v))" |
            "(u, dfa2.acc ?M', v) \<rightarrow>*\<lparr>?M'\<rparr> (tl (rev (\<langle>w\<langle>)), dfa2.rej ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>])" 
            using M.reachable_configs_impl_reachable by blast
          then show False
            by cases (use M.unchanged_final M.neq_final in fastforce)+  
          qed
      qed
      have "q \<in> dfa.final M"
      proof (rule ccontr)
        assume "q \<notin> dfa.final M"
        with final_state(2) have "dfa2.nxt ?M' q \<stileturn> = (dfa2.rej ?M', Left)" 
          using q_defs(1) by auto
        with acc_step show False using q_defs(2) by fastforce
      qed
      thus "w \<in> dfa.language M" 
        using final_state(3) dfa.language_def[OF \<open>dfa M\<close>] by blast
    qed
  next
    show "dfa.language M \<subseteq> M.Lang" 
    proof
      fix w
      assume "w \<in> dfa.language M"
      then obtain q where "dfa.nextl M (dfa.init M) w = q" and in_final: "q \<in> dfa.final M"
        by (simp add: \<open>dfa M\<close> dfa.language_def)
      with nextl_reachable have "([], dfa2.init ?M', \<langle>w\<rangle>) \<rightarrow>*\<lparr>?M'\<rparr> (rev (\<langle>w\<langle>), q, [\<stileturn>])"
        by blast
      also from this in_final have "... \<rightarrow>\<lparr>?M'\<rparr> (tl (rev (\<langle>w\<langle>)), dfa2.acc ?M', hd (rev (\<langle>w\<langle>)) # [\<stileturn>])"
        using M.step.simps by auto
      finally show "w \<in> M.Lang" unfolding M.Lang_def by blast
    qed
  qed
  then show thesis using that \<open>dfa.language M = L\<close> M.dfa2_axioms M_def q_defs by presburger
qed 

text \<open>The equality follows trivially:\<close>

corollary dfa2_accepts_regular_languages:
  "regular L = (\<exists>M. dfa2 M \<and> dfa2.Lang M = L)"
using dfa2.dfa2_Lang_regular regular_language_impl_dfa2 by fastforce

end
