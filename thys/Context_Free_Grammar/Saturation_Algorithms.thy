(* Author: Tobias Nipkow *)

section \<open>Compute Productive, Nullable, Reachable, Prestar\<close>

theory Saturation_Algorithms
imports
  "HOL-Library.While_Combinator"
  Context_Free_Grammar
begin               

text \<open>Saturation algorithms (using \<open>while_sat\<close>) for a number of elementary CFG problems -
directly, without using the \<open>Pre_Star_CFG\<close> entry.
Currently: productive, nullable and reachable nonterminals, and prestar.\<close>

subsection \<open>Productive\<close>

definition productive_fun :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
"productive_fun P N = (\<Union>(A,\<alpha>) \<in> P. if \<forall>B \<in> Nts_syms \<alpha>. B \<in> N then {A} else {})"

definition productive_sat :: "('n,'t)Prods \<Rightarrow> 'n set" where
"productive_sat P = the (while_saturate (productive_fun P) {})"

lemma mono_productive_fun:
  "mono (productive_fun P)"
unfolding mono_def productive_fun_def by(fastforce split: prod.splits if_splits)

lemma productive_Some: assumes "finite P"
shows "\<exists>N. while_saturate (productive_fun P) {} = Some N"
apply(rule while_saturate_finite_subset_Some[OF mono_productive_fun _ finite_Nts[OF assms]])
unfolding productive_fun_def by (auto simp add: Nts_Lhss_Rhs_Nts in_LhssI split: prod.splits if_splits)

lemma productive_sat_sound: assumes "finite P" and "A \<in> productive_sat P"
shows "productive P A"
proof -
  obtain N where w: "while_saturate (productive_fun P) {} = Some N"
    using assms(1) productive_Some by blast
  hence "A \<in> N" using assms(2) unfolding productive_sat_def by simp
  let ?P = "productive P"
  have "?P A" if PM: "\<And>B. B \<in> M \<Longrightarrow> ?P B" and A: "A \<in> productive_fun P M" for M A
  proof -
    from A obtain \<alpha> where "(A,\<alpha>) \<in> P" "\<forall>B\<in>Nts_syms \<alpha>. B \<in> M"
      unfolding productive_fun_def by (auto split: if_splits)
    hence "\<forall>B\<in>Nts_syms \<alpha>. productive P B" using PM by blast
    thus ?thesis using \<open>(A,\<alpha>) \<in> P\<close> productives_if_Nts_productive[of \<alpha> P] 
      by (metis converse_rtranclp_into_rtranclp derive_singleton in_Nts_syms)
  qed
  thus ?thesis using while_saturate_rule1[of ?P _ _ N A] w \<open>A \<in> N\<close> by blast
qed

lemma productive_sat_complete: assumes "finite P"
shows "P \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w \<Longrightarrow> A \<in> productive_sat P"
proof (induction n arbitrary: A w rule: less_induct)
  case (less n)
  then obtain \<alpha> m where "(A,\<alpha>) \<in> P" and der: "P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w" and "n = Suc m"
    by (meson deriven_start1)
  from deriven_decomp_Tm[OF der] have "\<forall>B \<in> Nts_syms \<alpha>. \<exists>u k. P \<turnstile> [Nt B] \<Rightarrow>(k) map Tm u \<and> k \<le> m"
    by(fastforce simp: Nts_syms_def in_set_conv_nth elem_le_sum_list)
  then have "\<forall>B \<in> Nts_syms \<alpha>. B \<in> productive_sat P" using less \<open>n = Suc m\<close> le_imp_less_Suc by blast
  with \<open>(A,\<alpha>) \<in> P\<close> show ?case 
    using productive_Some[OF assms] while_saturate_saturated
    unfolding productive_sat_def productive_fun_def by fastforce
qed

corollary productive_sat_productive: "finite P \<Longrightarrow> productive_sat P = {A. productive P A}"
using productive_sat_sound productive_sat_complete unfolding rtranclp_power by fastforce

text \<open>Test:\<close>
lemma "productive_sat {(0,[Nt 1, Nt 1]), (1,[Tm 1]), (2,[Nt 2]), (2,[Nt 0,Nt 2]::(int,nat)syms)} = {0,1}"
by eval


subsection \<open>Nullable\<close>

text \<open>Nullable means \<open>[] \<in> Lang P A\<close>\<close>

definition nullable_fun :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
"nullable_fun P N = (\<Union>(A,\<alpha>) \<in> P. if Tms_syms \<alpha> = {} \<and> (\<forall>B \<in> Nts_syms \<alpha>. B \<in> N) then {A} else {})"

definition nullable :: "('n,'t)Prods \<Rightarrow> 'n set" where
"nullable P = the (while_saturate (nullable_fun P) {})"

lemma mono_nullable_fun:
  "mono (nullable_fun P)"
unfolding mono_def nullable_fun_def by(force split: prod.splits if_splits)

lemma nullable_Some: assumes "finite P"
shows "\<exists>N. while_saturate (nullable_fun P) {} = Some N"
apply(rule while_saturate_finite_subset_Some[OF mono_nullable_fun _ finite_Nts[OF assms]])
unfolding nullable_fun_def by (auto simp add: Nts_Lhss_Rhs_Nts in_LhssI split: prod.splits if_splits)

lemma nullable_if_Nts_nullable:
  "\<lbrakk> Tms_syms \<alpha> = {}; \<forall>A\<in>Nts_syms \<alpha>. \<exists>u. P \<turnstile> [Nt A] \<Rightarrow>* [] \<rbrakk> \<Longrightarrow> \<exists>u. P \<turnstile> \<alpha> \<Rightarrow>* []"
proof (induction \<alpha>)
  case (Cons s \<alpha>)
  show ?case
  proof (cases s)
    case (Nt x1)
    then show ?thesis
      using Cons.IH Cons.prems by (fastforce simp: derives_Cons_decomp map_eq_append_conv)
  next
    case (Tm x2)
    then show ?thesis using Cons.IH Cons.prems by (auto simp: derives_Tm_Cons map_eq_Cons_conv)
  qed
qed simp

lemma nullable_sound: assumes "finite P" and "A \<in> nullable P"
shows "\<exists>w. P \<turnstile> [Nt A] \<Rightarrow>* []"
proof -
  obtain N where w: "while_saturate (nullable_fun P) {} = Some N"
    using assms(1) nullable_Some by blast
  hence "A \<in> N" using assms(2) unfolding nullable_def by simp
  let ?P = "\<lambda>A. P \<turnstile> [Nt A] \<Rightarrow>* []"
  have "?P A" if PM: "\<And>B. B \<in> M \<Longrightarrow> ?P B" and A: "A \<in> nullable_fun P M" for M A
  proof -
    from A obtain \<alpha> where "(A,\<alpha>) \<in> P" "Tms_syms \<alpha> = {}" "\<forall>B\<in>Nts_syms \<alpha>. B \<in> M"
      unfolding nullable_fun_def by (auto split: if_splits)
    hence "\<forall>B\<in>Nts_syms \<alpha>. P \<turnstile> [Nt B] \<Rightarrow>* []" using PM by blast
    thus ?thesis using \<open>(A,\<alpha>) \<in> P\<close> nullable_if_Nts_nullable[OF \<open>Tms_syms \<alpha> = {}\<close>]
      by (meson derives_Cons_Nil rtranclp.rtrancl_refl)
  qed
  thus ?thesis using while_saturate_rule1[of ?P _ _ N A] w \<open>A \<in> N\<close> by blast
qed

lemma nullable_complete: assumes "finite P"
shows "P \<turnstile> [Nt A] \<Rightarrow>(n) [] \<Longrightarrow> A \<in> nullable P"
proof (induction n arbitrary: A rule: less_induct)
  case (less n)
  obtain \<alpha> m where "(A,\<alpha>) \<in> P" and der: "P \<turnstile> \<alpha> \<Rightarrow>(m) []" and "n = Suc m"
    using deriven_start1[where w= "[]", simplified, OF less.prems] by auto
  from deriven_decomp[OF der] have "Tms_syms \<alpha> = {}"
    unfolding Tms_syms_def in_set_conv_nth
    using deriven_Tm_Cons nth_mem by fastforce
  from deriven_decomp[OF der] have "\<forall>B \<in> Nts_syms \<alpha>. \<exists>u k. P \<turnstile> [Nt B] \<Rightarrow>(k) [] \<and> k \<le> m"
    by(simp add: Nts_syms_def in_set_conv_nth) (metis elem_le_sum_list in_set_conv_nth)
  then have "\<forall>B \<in> Nts_syms \<alpha>. B \<in> nullable P" using less.IH \<open>n = Suc m\<close> le_imp_less_Suc by metis
  with \<open>(A,\<alpha>) \<in> P\<close> show ?case 
    using nullable_Some[OF assms] while_saturate_saturated \<open>Tms_syms \<alpha> = {}\<close>
    unfolding nullable_def nullable_fun_def by fastforce
qed

text \<open>Test:\<close>
lemma "nullable {(0,[Nt 1, Nt 1]), (1,[]), (2,[Nt 2]), (2,[Nt 0,Nt 2]::(int,nat)syms)} = {0,1}"
by eval


subsection \<open>Prestar\<close>

text \<open>Prestar computes the set of words from which some set of words is reachable via \<open>P\<close>.\<close>

definition prestar_fun :: "('n,'t)Prods \<Rightarrow> ('n,'t) syms set \<Rightarrow> ('n,'t) syms set" where
"prestar_fun P S = (\<Union>(A,\<alpha>) \<in> P. \<Union>\<beta> \<in> S. if length \<alpha> \<le> length \<beta> then \<Union>i \<le> length \<beta> - length \<alpha>.
  if take (length \<alpha>) (drop i \<beta>) = \<alpha> then {take i \<beta> @ [Nt A] @ drop (i + length \<alpha>) \<beta>} else {} else {})"

lemma prestar_fun1: "\<beta> \<in> prestar_fun P S \<Longrightarrow> \<exists>\<beta>' \<in> S. P \<turnstile> \<beta> \<Rightarrow> \<beta>'"
apply(auto simp: prestar_fun_def derive.simps)
by (metis (no_types, lifting) add.commute append_take_drop_id drop_drop)

lemma prestar_fun2: assumes "\<beta>' \<in> S" "P \<turnstile> \<beta> \<Rightarrow> \<beta>'" shows "\<beta> \<in> prestar_fun P S"
proof -
  from assms obtain A \<alpha> \<beta>1 \<beta>2 where "(A,\<alpha>) \<in> P" "\<beta> = \<beta>1 @ [Nt A] @ \<beta>2" "\<beta>' = \<beta>1 @ \<alpha> @ \<beta>2"
    by (meson derive.simps)
  hence **: "length \<alpha> \<le> length \<beta>' \<and> length \<beta>1 \<le> length \<beta>' - length \<alpha>"
  "take (length \<alpha>) (drop (length \<beta>1) \<beta>') = \<alpha>"
    and *: "\<beta> = take (length \<beta>1) \<beta>' @ [Nt A] @ drop (length \<beta>1 + length \<alpha>) \<beta>'" by simp+
  from ** show ?thesis unfolding prestar_fun_def * using \<open>(A,\<alpha>) \<in> P\<close> \<open>\<beta>' \<in> S\<close>
    by auto
qed

definition prestar :: "('n,'t)Prods \<Rightarrow> ('n,'t) syms set \<Rightarrow> ('n,'t) syms set" where
"prestar P S = the (while_saturate (prestar_fun P) S)"

lemma mono_prestar_fun:
  "mono (prestar_fun P)"
unfolding mono_def prestar_fun_def by(fastforce split: prod.splits if_splits)

lemma derive_set_subset2:
  "P \<turnstile> u \<Rightarrow> v \<Longrightarrow> set u \<subseteq> set v \<union> Syms P"
by (auto simp: derive_iff Syms_def)

lemma prestar_Some: assumes "finite P" "Eps_free P" "finite S0"
shows "\<exists>S. while_saturate (prestar_fun P) S0 = Some S"
proof -
  let ?Z = "Syms P \<union> \<Union>(set ` S0)"
  let ?S = "{\<beta>. set \<beta> \<subseteq> ?Z \<and> length \<beta> \<le> Max (length ` S0)}"
  have "finite (?Z)" using assms(1,3) finite_Syms by blast
  from finite_lists_length_le[OF this] have "finite ?S" by blast
  have "S0 \<subseteq> ?S" using assms(3) by fastforce
  have "prestar_fun P X \<subseteq> ?S" if "X \<subseteq> ?S" for X
  proof
    fix \<beta> assume "\<beta> \<in> prestar_fun P X"
    from prestar_fun1[OF this] obtain \<beta>' where \<beta>': "\<beta>' \<in> X" "P \<turnstile> \<beta> \<Rightarrow> \<beta>'" by blast
    hence "length \<beta> \<le> length \<beta>'" using assms(2) derives_measures_if_Eps_free by blast
    hence "length \<beta> \<le> Max (length ` S0)" using \<open>\<beta>' \<in> X\<close> that by auto
    moreover have "set \<beta> \<subseteq> ?Z" using \<beta>' that derive_set_subset2[of P \<beta> \<beta>'] by auto
    ultimately show "\<beta> \<in> ?S" by blast
  qed
  from while_saturate_finite_subset_Some[OF mono_prestar_fun this \<open>finite ?S\<close> \<open>S0 \<subseteq> ?S\<close>]
  show ?thesis .
qed

lemma prestar_sound: assumes "finite P" "Eps_free P" "finite S0" and "\<beta> \<in> prestar P S0"
shows "\<exists>\<beta>' \<in> S0. P \<turnstile> \<beta> \<Rightarrow>* \<beta>'"
proof -
  obtain S where w: "while_saturate (prestar_fun P) S0 = Some S"
    using assms(1-3) prestar_Some by blast
  hence "\<beta> \<in> S" using assms(4) unfolding prestar_def by simp
  let ?P = "\<lambda>\<beta>. \<exists>\<beta>' \<in> S0. P \<turnstile> \<beta> \<Rightarrow>* \<beta>'"
  have "?P \<beta>" if PM: "\<And>B. B \<in> M \<Longrightarrow> ?P B" and "\<beta> \<in> prestar_fun P M" for M \<beta>
  proof -
    from \<open>\<beta> \<in> _\<close> obtain \<beta>' where "\<beta>' \<in> M" "P \<turnstile> \<beta> \<Rightarrow> \<beta>'" by (metis prestar_fun1)
    thus ?thesis using PM
      by (meson converse_rtranclp_into_rtranclp)
  qed
  thus ?thesis using while_saturate_rule1[of ?P, OF _ w] \<open>\<beta> \<in> S\<close> by blast
qed

lemma prestar_complete: assumes "finite P" "Eps_free P" "finite S0"
shows "\<beta>' \<in> S0 \<Longrightarrow> P \<turnstile> \<beta> \<Rightarrow>(n) \<beta>' \<Longrightarrow> \<beta> \<in> prestar P S0"
proof (induction n arbitrary: \<beta> rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis unfolding prestar_def
      using less.prems prestar_Some[OF assms(1-3)] while_saturate_incr by fastforce
  next
    case (Suc m)
    then obtain \<beta>'' where "P \<turnstile> \<beta> \<Rightarrow> \<beta>''" "P \<turnstile> \<beta>'' \<Rightarrow>(m) \<beta>'"
      by (metis less.prems(2) relpowp_Suc_D2)
    then have "\<beta>'' \<in> prestar P S0" using Suc less.IH[of m] less.prems(1) by blast
    then show ?thesis unfolding prestar_def
      using prestar_Some[OF assms(1-3)] while_saturate_saturated[of "(prestar_fun P)" S0]
        prestar_fun2[OF _ \<open>P \<turnstile> \<beta> \<Rightarrow> \<beta>''\<close>]
      by fastforce 
  qed
qed

text \<open>Test:\<close>
lemma "prestar {(0,[Nt 1, Nt 1]), (1,[Tm 0]), (2,[Nt 2]), (2,[Nt 0,Nt 2]::(int,nat)syms)}
  {[Tm 0], [Tm 0, Tm 0]} = {[Tm 0], [Tm 0, Tm 0], [Nt 1], [Nt 1, Tm 0], [Tm 0, Nt 1], [Nt 1, Nt 1], [Nt 0]}"
by eval


subsection \<open>Reachable\<close>

definition reachable_fun :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
"reachable_fun P R = \<Union> (Nts_syms ` (\<Union>(Rhss P ` R)))"

definition reachable_sat :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
"reachable_sat P S = the (while_saturate (reachable_fun P) S)"

lemma mono_reachable_fun:
  "mono (reachable_fun P)"
unfolding mono_def reachable_fun_def by(fastforce split: prod.splits if_splits)

locale finP =
fixes P :: "('n,'t)Prods"
assumes finP: "finite P"
begin

(* TODO: get rid of \<open>S \<subseteq> Nts P\<close> by generalizing while_saturate_finite_subset_Some *)
lemma reachable_Some: assumes "S \<subseteq> Nts P"
shows "\<exists>N. while_saturate (reachable_fun P) S = Some N"
apply(rule while_saturate_finite_subset_Some[OF mono_reachable_fun _ finite_Nts[OF finP]])
unfolding reachable_fun_def using assms
by (auto simp add: Nts_Lhss_Rhs_Nts Rhs_Nts_def Lhss_def Nts_syms_def Rhss_def split: prod.splits if_splits)

lemma reachable_sat_sound: assumes "S \<subseteq> Nts P" and "B \<in> reachable_sat P S"
shows "\<exists>A \<in> S. \<exists>\<beta>. P \<turnstile> [Nt A] \<Rightarrow>* \<beta> \<and> Nt B \<in> set \<beta>"
proof -
  obtain R where w: "while_saturate (reachable_fun P) S = Some R"
    using reachable_Some[OF assms(1)] by blast
  hence "B \<in> R" using assms(2) unfolding reachable_sat_def by simp
  let ?P = "\<lambda>B. \<exists>A \<in> S. \<exists>\<beta>. P \<turnstile> [Nt A] \<Rightarrow>* \<beta> \<and> Nt B \<in> set \<beta>"
  have 0: "?P B" if PM: "\<And>B. B \<in> R \<Longrightarrow> ?P B" and B: "B \<in> reachable_fun P R" for R B
  proof -
    from B obtain A \<beta> where A: "A \<in> R" "P \<turnstile> [Nt A] \<Rightarrow> \<beta>" "Nt B \<in> set \<beta>"
      unfolding reachable_fun_def by (auto simp: derive_singleton Nts_syms_def Rhss_def split: if_splits)
    from PM[OF \<open>A \<in> R\<close>] obtain A0 \<beta>0 where "A0\<in>S" "P \<turnstile> [Nt A0] \<Rightarrow>* \<beta>0" "Nt A \<in> set \<beta>0"
      by (auto)
    from split_list[OF this(3)] obtain \<beta>1 \<beta>2 where "\<beta>0 = \<beta>1 @ [Nt A] @ \<beta>2" by auto
    then have "P \<turnstile> [Nt A0] \<Rightarrow>* \<beta>1 @ \<beta> @ \<beta>2" using A(2) \<open>A0\<in>S\<close> \<open>P \<turnstile> [Nt A0] \<Rightarrow>* \<beta>0\<close>
      by (meson derives_append derives_prepend r_into_rtranclp rtranclp_trans)
    then show ?thesis using \<open>A0\<in>S\<close> A(3) by fastforce
  qed
  show ?thesis using while_saturate_rule1[OF _ w, of "?P", OF _ _ \<open>B \<in> R\<close>] 0
    by fastforce
qed

lemma reachable_sat_closed: assumes "S \<subseteq> Nts P" "A \<in> reachable_sat P S" "(A,\<alpha>) \<in> P" "Nt B \<in> set \<alpha>"
shows "B \<in> reachable_sat P S"
proof -
  obtain R where w: "while_saturate (reachable_fun P) S = Some R"
    using reachable_Some[OF assms(1)]  by blast
  from while_saturate_saturated[OF w] assms(2-) w
  show ?thesis unfolding reachable_sat_def reachable_fun_def
    by(auto simp:Rhss_def Nts_syms_def)
qed

lemma reachable_sat_complete: assumes "S \<subseteq> Nts P" and "A \<in> S"
shows "P \<turnstile> [Nt A] \<Rightarrow>(n) \<beta> \<Longrightarrow> Nt B \<in> set \<beta> \<Longrightarrow> B \<in> reachable_sat P S"
proof (induction n arbitrary: B \<beta> rule: less_induct)
  case (less n)
  obtain R where w: "while_saturate (reachable_fun P) S = Some R"
    using reachable_Some[OF assms(1)] by blast
  show ?case
  proof (cases n)
    case 0 thus ?thesis using less.prems \<open>A \<in> S\<close> while_saturate_incr[OF w] w
      unfolding reachable_sat_def by auto
  next
    case (Suc m)
    with less.prems(1) obtain \<alpha> where 0: "P \<turnstile> [Nt A] \<Rightarrow>(m) \<alpha>" "P \<turnstile> \<alpha> \<Rightarrow> \<beta>" by auto
    from this(2) obtain \<alpha>1 \<alpha>2 A' \<alpha>' where "(A',\<alpha>') \<in> P" "\<alpha> = \<alpha>1 @ [Nt A'] @ \<alpha>2" "\<beta> = \<alpha>1 @ \<alpha>' @ \<alpha>2"
      by (meson derive.cases)
    thus ?thesis using Suc less.prems(2) less.IH[OF _ 0(1)] reachable_sat_closed[OF assms(1) _ \<open>(A',\<alpha>') \<in> P\<close>]
      by auto
  qed
qed

end

end