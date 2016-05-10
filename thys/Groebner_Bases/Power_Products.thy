(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Abstract Power-Products\<close>

theory Power_Products
imports Complex_Main
begin

text \<open>This theory formalizes the concept of "power-products". A power-product can be thought of as
  the product of some indeterminates, such as $x$, $x^2\,y$, $x\,y^3\,z^7$, etc., without any
  scalar coefficient.\<close>

subsection \<open>Class of Abstract Power-Products\<close>

subsubsection \<open>Class of Unordered Power-Products\<close>

class powerprod = comm_monoid_mult +
  fixes div::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "divide" 70)
  fixes lcm::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes dummy_dvd::"'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes dummy_dvd_iff: "dummy_dvd s t \<longleftrightarrow> s dvd t"
  assumes cancel: "s * u = t * u \<Longrightarrow> s = t"
  assumes times_eq_one: "s * t = 1 \<Longrightarrow> s = 1"
  assumes times_divide: "(s * t) divide t = s"
  assumes ndvd_divide: "\<not> s dvd t \<Longrightarrow> t divide s = 1"
  assumes dvd_lcm: "s dvd (lcm s t)"
  assumes lcm_comm: "lcm s t = lcm t s"
  assumes lcm_min: "s dvd u \<Longrightarrow> t dvd u \<Longrightarrow> (lcm s t) dvd u"
  assumes dickson: "\<And>seq::nat \<Rightarrow> 'a. (\<exists>i j::nat. i < j \<and> seq i dvd seq j)"
begin

lemma cancel_left:
  "u * s = u * t \<Longrightarrow> s = t"
by (simp add: mult_commute, rule cancel)

lemma mult_left_cancel [simp]:
  "u * s = u * t \<longleftrightarrow> s = t"
by (blast dest: cancel_left)

lemma mult_right_cancel [simp]:
  "s * u = t * u \<longleftrightarrow> s = t"
by (blast dest: cancel)

lemma times_eq_one_2:
  assumes "s * t = 1"
  shows "t = 1"
using assms
by (simp only: mult_commute[of s t] times_eq_one)

lemma dvd_one:
  shows "s dvd 1 \<longleftrightarrow> (s = 1)"
proof
  assume "s dvd 1"
  from this obtain k where "1 = s * k" unfolding dvd_def ..
  from this times_eq_one[of s k] show "s = 1" by simp
next
  assume "s = 1"
  thus "s dvd 1" by simp
qed

lemma dvd_canc:
  shows "s * u dvd t * u \<longleftrightarrow> s dvd t"
proof
  assume "s * u dvd t * u"
  thus "s dvd t" unfolding dvd_def
  proof
    fix k
    assume "t * u = s * u * k"
    from this cancel[of t u "s * k"] have "t = s * k" by (simp add: ac_simps)
    show "\<exists>k. t = s * k" by (rule exI[of _ k], fact)
  qed
next
  assume "s dvd t"
  thus "s * u dvd t * u" unfolding dvd_def
  proof
    fix k
    assume t: "t = s * k"
    show "\<exists>k. t * u = s * u * k" by (rule exI[of _ k], simp add: t ac_simps)
  qed
qed

lemma dvd_canc_2:
  shows "u * s dvd u * t \<longleftrightarrow> s dvd t"
by (simp add: mult_commute dvd_canc)

lemma times_divide_2:
  shows "(s * t) divide s = t"
by (simp add: mult_commute[of s t] times_divide)

lemma divide_same:
  shows "t divide t = 1"
using times_divide[of 1 t] by simp

lemma divide_one:
  shows "t divide 1 = t"
using times_divide[of t 1] by simp

lemma divide_divide:
  shows "(s divide t) divide u = s divide (t * u)"
proof (cases "t dvd s")
  assume "t dvd s"
  from this obtain k where k: "s = t * k" unfolding dvd_def ..
  hence eq1: "(s divide t) = k" by (simp add: mult_commute times_divide)
  show ?thesis
  proof (cases "u dvd k")
    assume "u dvd k"
    from this obtain l where l: "k = u * l" unfolding dvd_def ..
    from eq1 this have eq2: "(s divide t) divide u = l" by (simp add: mult_commute times_divide)
    from k l have "s = l * (t * u)" by (simp add: ac_simps)
    hence eq3: "s divide (t * u) = l" by (simp add: times_divide)
    from eq2 eq3 show ?thesis by simp
  next
    assume "\<not> u dvd k"
    from ndvd_divide[OF this] eq1 have eq4: "(s divide t) divide u = 1" by simp
    have "\<not> (t * u) dvd s" by (simp add: k dvd_canc_2, fact)
    from ndvd_divide[OF this] eq4 show ?thesis by simp
  qed
next
  assume "\<not> t dvd s"
  from ndvd_divide[OF this] have eq5: "s divide t = 1" .
  show ?thesis
  proof (cases "u dvd 1")
    assume "u dvd 1"
    from this dvd_one[of u] have "u = 1" by simp
    thus ?thesis by (simp add: divide_one)
  next
    assume "\<not> u dvd 1"
    from ndvd_divide[OF this] eq5 have eq6: "(s divide t) divide u = 1" by simp
    have "\<not> (t * u) dvd s"
    proof
      assume "(t * u) dvd s"
      from this obtain k where "s = t * (u * k)" unfolding dvd_def by (auto simp add: ac_simps)
      have "t dvd s" unfolding dvd_def by (rule exI[of _ "u * k"], fact)
      from this \<open>\<not> t dvd s\<close> show False by simp
    qed
    from eq6 ndvd_divide[OF this] show ?thesis by simp
  qed
qed

lemma dvd_divide:
  assumes "s dvd t"
  shows "(t divide s) * s = t"
proof -
  from assms dvd_def[of s t] obtain u where u: "t = u * s" by (auto simp: ac_simps)
  hence "t divide s = u" using times_divide[of u s] by simp
  thus ?thesis using u by simp
qed

lemma times_dvd_1:
  assumes "(s * t) dvd u"
  shows "s dvd (u divide t)"
proof -
  from assms dvd_divide[OF dvd_mult_right[OF assms]] have "(s * t) dvd ((u divide t) * t)" by simp
  thus ?thesis using dvd_canc[of s t "u divide t"] by simp
qed

lemma times_dvd_2:
  assumes "t dvd u" and "s dvd (u divide t)"
  shows "(s * t) dvd u"
proof -
  from \<open>t dvd u\<close> obtain k where k: "u = k * t" unfolding dvd_def by (auto simp add: ac_simps)
  hence "u divide t = k" using times_divide[of k t] by simp
  from this \<open>s dvd (u divide t)\<close> have "s dvd k" by simp
  from this obtain l where l: "k = l * s" unfolding dvd_def by (auto simp add: ac_simps)
  from this k have "u = (s * t) * l" by (simp add: ac_simps)
  show "(s * t) dvd u" unfolding dvd_def by (rule exI[of _ l], fact)
qed

lemma times_dvd:
  shows "(s * t) dvd u \<longleftrightarrow> (t dvd u \<and> s dvd (u divide t))"
proof
  assume a1: "(s * t) dvd u"
  show "t dvd u \<and> s dvd (u divide t)"
  proof
    from dvd_mult_right[OF a1] show "t dvd u" .
  next
    from times_dvd_1[OF a1] show "s dvd (u divide t)" .
  qed
next
  assume "t dvd u \<and> s dvd (u divide t)"
  hence "t dvd u" and "s dvd (u divide t)" by auto
  from times_dvd_2[OF \<open>t dvd u\<close> \<open>s dvd (u divide t)\<close>] show "(s * t) dvd u" .
qed

lemma divide_times:
  assumes "s dvd t"
  shows "(t divide s) * u = (t * u) divide s"
proof -
  from assms obtain k where k: "t = s * k" unfolding dvd_def ..
  hence "t divide s = k" using times_divide[of k s] by (simp add: ac_simps)
  also from k have "(t * u) divide s = k * u" using times_divide[of "k * u" s]
    by (simp add: ac_simps)
  finally show ?thesis by simp
qed

lemma divide_times_divide:
  assumes "s dvd t" and "u dvd v"
  shows "(t divide s) * (v divide u) = (t * v) divide (s * u)"
using
  divide_times[OF \<open>s dvd t\<close>, of "v divide u"]
  divide_times[OF \<open>u dvd v\<close>, of t]
  divide_divide[of "t * v" u s]
by (simp add: ac_simps)

lemma divide_times_divide_cancel:
  assumes "u dvd t" and "s dvd u"
  shows "(t divide u) * (u divide s) = t divide s"
proof -
  from dvd_trans[OF \<open>s dvd u\<close> \<open>u dvd t\<close>] have "s dvd t" .
  have "u dvd u" by simp
  have "(t divide u) * (u divide s) = (t * u) divide (u * s)"
    using divide_times_divide[OF \<open>u dvd t\<close> \<open>s dvd u\<close>] by simp
  also have "\<dots> = (u * t) divide (u * s)" by (simp only: ac_simps)
  also have "\<dots> = (u divide u) * (t divide s)"
    using divide_times_divide[OF \<open>u dvd u\<close> \<open>s dvd t\<close>] by simp
  finally show ?thesis by (simp add: divide_same)
qed

lemma dvd_lcm_2:
  shows "t dvd (lcm s t)"
by (simp add: lcm_comm[of s t], rule dvd_lcm)

end

subsubsection \<open>Class of Ordered Power-Products\<close>

lemma wfP_chain:
  fixes r::"'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<not>(\<exists>f. \<forall>i. r (f (Suc i)) (f i))"
  shows "wfP r"
proof -
  from assms wf_iff_no_infinite_down_chain[of "{(x, y). r x y}"] have "wf {(x, y). r x y}" by auto
  thus "wfP r" unfolding wfP_def .
qed

locale ordered_powerprod = 
  fixes ord::"'a \<Rightarrow> 'a::powerprod \<Rightarrow> bool" (infixl "\<preceq>" 50)
  assumes ord_refl: "s \<preceq> s"
  assumes ord_antisym: "s \<preceq> t \<Longrightarrow> t \<preceq> s \<Longrightarrow> s = t"
  assumes ord_trans: "s \<preceq> t \<Longrightarrow> t \<preceq> u \<Longrightarrow> s \<preceq> u"
  assumes ord_lin: "s \<preceq> t \<or> t \<preceq> s"
  assumes one_min: "1 \<preceq> t"
  assumes times_monotone: "s \<preceq> t \<Longrightarrow> s * u \<preceq> t * u"
begin

definition ord_strict::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<prec>" 50) where
  "ord_strict s t \<equiv> (s \<preceq> t \<and> \<not> t \<preceq> s)"

sublocale ordered_powerprod_lin: linorder "op \<preceq>" "op \<prec>"
proof
  fix s t
  show "(s \<prec> t) = (s \<preceq> t \<and> \<not> t \<preceq> s)" unfolding ord_strict_def ..
next
  fix s
  from ord_refl[of s] show "s \<preceq> s" .
next
  fix s t u
  assume "s \<preceq> t" and "t \<preceq> u"
  from ord_trans[OF this] show "s \<preceq> u" .
next
  fix s t
  assume "s \<preceq> t" and "t \<preceq> s"
  from ord_antisym[OF this] show "s = t" .
next
  fix s t
  from ord_lin[of s t] show "s \<preceq> t \<or> t \<preceq> s" .
qed

lemma ord_canc:
  assumes "s * u \<preceq> t * u"
  shows "s \<preceq> t"
proof (rule ordered_powerprod_lin.le_cases[of s t], simp)
  assume "t \<preceq> s"
  from assms times_monotone[OF this, of u] have "t * u = s * u"
    using ordered_powerprod_lin.eq_iff by simp
  hence "t = s" by simp
  thus "s \<preceq> t" by simp
qed

lemma ord_dvd:
  assumes "s dvd t"
  shows "s \<preceq> t"
proof -
  from assms have "\<exists>u. t = s * u" unfolding dvd_def by simp
  then obtain k where "t = s * k" ..
  thus ?thesis using times_monotone[OF one_min[of k], of s] by (simp add: ac_simps)
qed

lemma wf_ord_strict:
  shows "wfP (op \<prec>)"
proof (rule wfP_chain)
  show "\<not> (\<exists>seq. \<forall>i. seq (Suc i) \<prec> seq i)"
  proof
    assume "\<exists>seq. \<forall>i. seq (Suc i) \<prec> seq i"
    then obtain seq::"nat \<Rightarrow> 'a" where seq: "\<forall>i. seq (Suc i) \<prec> seq i" ..

    (*The following holds for transitive relations in general!*)
    have seq_decr: "\<forall>i j. i < j \<longrightarrow> seq j \<prec> seq i"
    proof (rule, rule, rule)
      fix i j::nat
      assume "i < j"
      have "\<forall>k. seq (i + Suc k) \<prec> seq i"
      proof
        fix k::nat
        show "seq (i + Suc k) \<prec> seq i"
        proof (induct k)
          case 0
          from seq have "seq (Suc i) \<prec> seq i" ..
          thus ?case by simp
        next
          case (Suc k)
          from seq have "seq (Suc (Suc i + k)) \<prec> seq (Suc (i + k))" by simp
          also have "\<dots> \<prec> seq i" using Suc.hyps by simp
          finally show ?case by simp
        qed
      qed
      hence "seq (i + Suc(j - i - 1)) \<prec> seq i" ..
      thus "seq j \<prec> seq i" using \<open>i < j\<close> by simp
    qed
    from dickson[of seq] obtain i j::nat where "i < j \<and> seq i dvd seq j" by auto
    hence "i < j" and i_dvd_j: "seq i dvd seq j" by auto
    from seq_decr[rule_format, OF \<open>i < j\<close>] have "seq j \<preceq> seq i \<and> seq j \<noteq> seq i" by auto
    hence "seq j \<preceq> seq i" and "seq j \<noteq> seq i" by simp_all
    from \<open>seq j \<noteq> seq i\<close> \<open>seq j \<preceq> seq i\<close> ord_dvd[OF i_dvd_j]
         ordered_powerprod_lin.eq_iff[of "seq j" "seq i"]
      show False by simp
  qed
qed

end

subsection \<open>Type @{term pp}\<close>

text \<open>Power-products are represented as (possibly infinite) functions from a type of indeterminates
  to nat.\<close>

typedef 'a pp = "UNIV::('a \<Rightarrow> nat) set"
  morphisms exp Abs_pp by auto

setup_lifting type_definition_pp

lemma pp_eq_intro:
  shows "(\<And>x. exp s x = exp t x) \<Longrightarrow> s = t"
proof transfer
  fix s t::"'a \<Rightarrow> nat"
  assume "\<And>x. s x = t x"
  thus "s = t" ..
qed

subsubsection \<open>@{typ "'a pp"} belongs to class @{class one}\<close>

instantiation pp :: (type) one
begin
lift_definition one_pp::"'a pp" is "(\<lambda>t::'a. 0::nat)" .

instance ..
end

subsubsection \<open>@{typ "'a pp"} belongs to class @{class equal}\<close>

instantiation pp :: (type) equal
begin
definition equal_pp::"'a pp \<Rightarrow> 'a pp \<Rightarrow> bool" where "equal_pp s t \<equiv> (\<forall>x::'a. exp s x = exp t x)"

instance by (standard, simp only: equal_pp_def, transfer, auto)
end

subsubsection \<open>@{typ "'a pp"} belongs to class @{class comm_monoid_mult}\<close>

instantiation pp :: (type) comm_monoid_mult
begin

lift_definition times_pp::"'a pp \<Rightarrow> 'a pp \<Rightarrow> 'a pp" is "\<lambda>s t. \<lambda>x. s x + t x" .

lemma times_pp_one_neutral:
  shows "1 * s = (s::'a pp)"
by transfer simp

lemma times_pp_assoc:
  shows "(s * t) * u = s * (t * (u::'a pp))"
by transfer auto

lemma times_pp_comm:
  shows "s * t = t * (s::'a pp)"
by transfer auto

instance
apply standard
subgoal by (rule times_pp_assoc)
subgoal by (rule times_pp_comm)
subgoal by (rule times_pp_one_neutral)
done

end

lemma dvd_pp:
  shows "s dvd (t::'a pp) \<longleftrightarrow> (\<forall>x. exp s x \<le> exp t x)"
unfolding dvd_def
proof
  assume "\<exists>k. t = s * k"
  from this obtain k where "t = s * k" ..
  thus "\<forall>x. exp s x \<le> exp t x"
  proof transfer
    fix s t k::"'a \<Rightarrow> nat"
    assume eq: "t = (\<lambda>x. s x + k x)"
    show "\<forall>x. s x \<le> t x" by (rule, simp add: eq)
  qed
next
  assume "\<forall>x. exp s x \<le> exp t x"
  thus "\<exists>k. t = s * k"
  proof transfer
    fix s t::"'a \<Rightarrow> nat"
    assume a: "\<forall>x. s x \<le> t x"
    show "\<exists>k. t = (\<lambda>x. s x + k x)"
    proof (rule exI[of _ "\<lambda>x. t x - s x"], rule)
      fix x
      from a have "s x \<le> t x" ..
      thus "t x = s x + (t x - s x)" by simp
    qed
  qed
qed

subsection \<open>Power-products in a given set of indeterminates.\<close>

lift_definition in_indets::"'a set \<Rightarrow> 'a pp \<Rightarrow> bool" is "\<lambda>V s. \<forall>x. x \<notin> V \<longrightarrow> s x = 0" .

lift_definition truncate::"'a set \<Rightarrow> 'a pp \<Rightarrow> 'a pp" is "\<lambda>V s. \<lambda>x. (if x \<in> V then s x else 0)" .

lemma univ_indets:
  shows "in_indets (UNIV::'a set) s"
by (simp add: in_indets_def)

lemma empty_indets:
  shows "in_indets {} s = (s = 1)"
proof -
  from assms
  show ?thesis
  proof transfer
    fix s::"'a \<Rightarrow> nat"
    show "(\<forall>x. x \<notin> {} \<longrightarrow> s x = 0) = (s = (\<lambda>x. 0))"
    proof
      assume prem1: "\<forall>x. x \<notin> {} \<longrightarrow> s x = 0"
      show "s = (\<lambda>x. 0)"
      proof
        fix x
        from prem1 have "x \<notin> {} \<longrightarrow> s x = 0" by simp
        thus "s x = 0" by auto
      qed
    next
      assume prem2: "s = (\<lambda>x. 0)"
      show "\<forall>x. x \<notin> {} \<longrightarrow> s x = 0"
      proof
        fix x
        show "x \<notin> {} \<longrightarrow> s x = 0" by (rule, simp only: prem2)
      qed
    qed
  qed
qed

lemma truncate_in:
  shows "in_indets V (truncate V s)"
by (transfer, rule, rule, simp)

lemma mult_union:
  fixes V U::"'a set" and s t::"'a pp"
  assumes "in_indets V s" and "in_indets U t"
  shows "in_indets (V \<union> U) (s * t)"
proof -
  from assms
  show ?thesis
  proof transfer
    fix V U::"'a set" and s t::"'a \<Rightarrow> nat"
    assume asm1: "\<forall>x. x \<notin> V \<longrightarrow> s x = 0" and asm2: "\<forall>x. x \<notin> U \<longrightarrow> t x = 0"
    show "\<forall>x. x \<notin> (V \<union> U) \<longrightarrow> s x + t x = 0"
    proof
      fix x
      show "x \<notin> (V \<union> U) \<longrightarrow> s x + t x = 0"
      proof
        assume "x \<notin> V \<union> U"
        hence "x \<notin> V" and "x \<notin> U" by auto
        hence "s x = 0" and "t x = 0" using asm1 asm2 by auto
        thus "s x + t x = 0" by simp
      qed
    qed
  qed
qed

lemma dvd_insert_indets:
  assumes "in_indets (insert v V) s" and "in_indets (insert v V) t"
  shows "s dvd t = (truncate V s dvd truncate V t \<and> exp s v \<le> exp t v)"
using assms unfolding dvd_pp
proof transfer
  fix V::"'a set" and v::'a and s t::"'a \<Rightarrow> nat"
  assume s_in: "\<forall>x. x \<notin> insert v V \<longrightarrow> s x = 0"
    and t_in: "\<forall>x. x \<notin> insert v V \<longrightarrow> t x = 0"
  show "(\<forall>x. s x \<le> t x) = ((\<forall>x. (if x \<in> V then s x else 0) \<le> (if x \<in> V then t x else 0)) \<and> s v \<le> t v)"
    (is "?L = (?A \<and> ?B)")
  proof
    assume s_le_t: ?L
    show "?A \<and> ?B"
    proof
      show ?A
      proof
        fix x
        have "s x \<le> t x" using s_le_t by simp
        thus "(if x \<in> V then s x else 0) \<le> (if x \<in> V then t x else 0)" by simp
      qed
    next
      show ?B using s_le_t by simp
    qed
  next
    assume "?A \<and> ?B"
    then have a: ?A and b: ?B by auto
    show ?L
    proof
      fix x
      show "s x \<le> t x"
      proof (cases "x \<in> insert v V")
        case True
        hence "x = v \<or> x \<in> V" by auto
        thus ?thesis
        proof
          assume "x = v"
          thus ?thesis using b by simp
        next
          assume x_in_V: "x \<in> V"
          have "(if x \<in> V then s x else 0) \<le> (if x \<in> V then t x else 0)" using a by simp
          thus ?thesis using x_in_V by simp
        qed
      next
        case False
        hence "s x = 0" and "t x = 0" using s_in t_in by simp_all
        thus ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

(*The following lemma was provided by Manuel Eberl*)
lemma nat_incr_subsequence:
  fixes f :: "nat \<Rightarrow> nat"
  obtains g where "subseq g" "incseq (f \<circ> g)"
proof -
  from seq_monosub[of f] obtain g
    where subseq: "subseq g" and mono: "monoseq (f \<circ> g)" by (auto simp: o_def)
  from mono show ?thesis unfolding monoseq_iff
  proof
    assume decseq: "decseq (f \<circ> g)"
    def M \<equiv> "LEAST n. n \<in> range (f \<circ> g)"
    have "M \<in> range (f \<circ> g)" unfolding M_def by (rule LeastI_ex) blast
    then obtain n where n: "f (g n) = M" unfolding o_def by blast

    have "subseq (g \<circ> (\<lambda>x. x + n))" by (intro subseq_o subseq) (auto simp: subseq_def)
    moreover {
      fix m assume "m \<ge> n"
      from \<open>m \<ge> n\<close> and decseq
        have "f (g m) \<le> f (g n)" unfolding decseq_def by simp
      with n have "f (g m) \<le> M" by simp
      moreover have "M \<le> f (g m)" unfolding M_def by (rule Least_le) simp
      ultimately have "f (g m) = M" by simp
    }
    hence "incseq (f \<circ> (g \<circ> (\<lambda>x. x + n)))" by (auto simp: incseq_def)
    ultimately show ?thesis by (rule that)
  qed (rule that[OF subseq])
qed

lemma pp_incr_subsequence:
  fixes V::"'a set" and f::"nat \<Rightarrow> 'a pp"
  assumes fin: "finite V" and "\<forall>k. in_indets V (f k)"
  shows "\<exists>m::nat \<Rightarrow> nat. (subseq m) \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i dvd (f o m) j)"
  using assms
proof (induct V arbitrary: f)
  fix f::"nat \<Rightarrow> 'a pp"
  assume "\<forall>k. in_indets {} (f k)"
  hence "\<forall>k. f k = 1" by (intro allI, simp_all only: empty_indets)
  thus "\<exists>m. subseq m \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i dvd (f o m) j)" unfolding dvd_pp
  proof transfer
    fix f::"nat \<Rightarrow> 'a \<Rightarrow> nat"
    assume all_one: "\<forall>k. f k = (\<lambda>_. 0)"
    show "\<exists>m. subseq m \<and> (\<forall>i j. i < j \<longrightarrow> (\<forall>x. (f o m) i x \<le> (f o m) j x))"
    proof
      from all_one show "subseq id \<and> (\<forall>i j. i < j \<longrightarrow> (\<forall>x. (f o id) i x \<le> (f o id) j x))"
        by (simp add: subseq_def)
    qed
  qed
next
  fix v::'a and F::"'a set" and f::"nat \<Rightarrow> 'a pp"
  assume "finite F" and "v \<notin> F"
    and IH: "(\<And>f. (\<forall>k. in_indets F (f k)) \<Longrightarrow>
                (\<exists>m. subseq m \<and> ( \<forall>i j. i < j \<longrightarrow> (f o m) i dvd (f o m) j)))"
    and seq_in_insert: "\<forall>k. in_indets (insert v F) (f k)"

  (*Construction of first mapping*)
  have IH_prem: "\<forall>k. in_indets F ((truncate F o f) k)"
  proof
    fix k::nat
    show "in_indets F ((truncate F o f) k)" by (simp add: truncate_in)
  qed
  from IH[OF IH_prem] obtain m1::"nat \<Rightarrow> nat" where
    "subseq m1 \<and> (\<forall>i j. i < j \<longrightarrow> ((truncate F) o f o m1) i dvd ((truncate F) o f o m1) j)" ..
  hence m1_subseq: "subseq m1"
    and m1_div: "\<forall>i j. i < j \<longrightarrow> ((truncate F) o f o m1) i dvd ((truncate F) o f o m1) j"
    by simp_all

  (*Construction of second mapping (using lemma nat_incr_subsequence for backward reasoning)*)
  show "\<exists>m. subseq m \<and> (\<forall>i j. i < j \<longrightarrow> ((f o m) i) dvd ((f o m) j))"
  proof (rule nat_incr_subsequence[of "(\<lambda>x. exp x v) o f o m1"])
    fix m2::"nat \<Rightarrow> nat"
    assume m2_subseq: "subseq m2" and "incseq ((\<lambda>x. exp x v) \<circ> f \<circ> m1 \<circ> m2)"
    hence m2_div: "\<forall>i j. i < j \<longrightarrow> ((\<lambda>x. exp x v) \<circ> f \<circ> (m1 o m2)) i \<le> ((\<lambda>x. exp x v) \<circ> f \<circ> (m1 o m2)) j"
      by (simp add: incseq_def)
    
    let ?m = "(m1 o m2)"
    show "\<exists>m. subseq m \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i dvd (f o m) j)"
    proof (rule, rule)
      show "subseq ?m" using m1_subseq m2_subseq by (intro subseq_o)
    next
      show "\<forall>i j. i < j \<longrightarrow> (f o ?m) i dvd (f o ?m) j"
      proof (rule, rule, rule)
        fix i j::nat
        assume i_less_j: "i < j"

        (*i-th and j-th element are in (insert v F)*)
        from seq_in_insert have in_indets_i:"in_indets (insert v F) ((f o ?m) i)"
          and in_indets_j: "in_indets (insert v F) ((f o ?m) j)" by simp_all

        (*v-component of i-th element is leq v-component of j-th element*)
        from m2_div have m2_div_i_j: "i < j \<longrightarrow> ((\<lambda>x. exp x v) \<circ> f \<circ> ?m) i \<le> ((\<lambda>x. exp x v) \<circ> f \<circ> ?m) j"
          by simp
        hence v_div: "(exp ((f o ?m) i) v) \<le> (exp ((f o ?m) j) v)" using i_less_j by simp

        (*F-components of i-th element divide F-components of j-th element*)
        from m1_div have m1_div_i_j: "m2 i < m2 j \<longrightarrow> ((truncate F) o f o ?m) i dvd ((truncate F) o f o ?m) j"
          by simp
        hence F_div: "truncate F ((f o ?m) i) dvd truncate F ((f o ?m) j)"
          using i_less_j m2_subseq by (simp add: subseq_def)

        show "(f o ?m) i dvd (f o ?m) j" using in_indets_i in_indets_j v_div F_div
          by (simp add: dvd_insert_indets)
      qed
    qed
  qed
qed

text \<open>Another version of Dickson's lemma is proved in @{cite Sternagel2012}.\<close>

lemma Dickson_pp:
  fixes V::"'a set" and seq::"nat \<Rightarrow> 'a pp"
  assumes "finite V" and "\<forall>k. in_indets V (seq k)"
  shows "\<exists>i j::nat. i < j \<and> seq i dvd seq j"
proof -
  from pp_incr_subsequence[OF assms] obtain m::"nat \<Rightarrow> nat" where
    "subseq m \<and> (\<forall>i j. i < j \<longrightarrow> (seq o m) i dvd (seq o m) j)" ..
  hence m_subseq: "subseq m" and m_div: "\<forall>i j. i < j \<longrightarrow> (seq o m) i dvd (seq o m) j" by simp_all
  let ?i = "m 0" and ?j = "m 1"
  show "\<exists>i j::nat. i < j \<and> seq i dvd seq j"
  proof (rule, rule)
    show "?i < ?j \<and> seq ?i dvd seq ?j" using m_subseq m_div by (simp add: subseq_def)
  qed
qed

lemma Dickson_pp_finite:
  fixes seq::"nat \<Rightarrow> 'a::finite pp"
  shows "\<exists>i j::nat. i < j \<and> seq i dvd seq j"
proof -
  have fin: "finite (UNIV::'a set)" by simp
  have indets: "\<forall>k. in_indets UNIV (seq k)"
  proof
    fix k::nat
    show "in_indets UNIV (seq k)" using univ_indets .
  qed
  show ?thesis using Dickson_pp[OF fin indets] .
qed

subsubsection \<open>@{typ "'a pp"} belongs to class @{class powerprod}\<close>

instantiation pp :: (finite) powerprod
begin

lift_definition lcm_pp::"'a pp \<Rightarrow> 'a pp \<Rightarrow> 'a pp" is
  "\<lambda>s t. \<lambda>x. max (s x) (t x)" .
lift_definition div_pp::"'a pp \<Rightarrow> 'a pp \<Rightarrow> 'a pp" is
  "\<lambda>s t. (if (\<forall>x. t x \<le> s x) then (\<lambda>x. s x - t x) else (\<lambda>_. 0))" .
lift_definition dummy_dvd_pp::"'a pp \<Rightarrow> 'a pp \<Rightarrow> bool" is
  "\<lambda>s t. (\<forall>x. s x \<le> t x)" .

lemma dummy_dvd_pp_dvd:
  shows "dummy_dvd s t \<longleftrightarrow> s dvd (t::'a pp)"
unfolding dvd_pp by (transfer, simp)

lemma cancel_pp:
  assumes "s * u = t * (u::'a pp)"
  shows "s = t"
proof -
  from assms
  show ?thesis
  proof transfer
    fix s t u::"'a \<Rightarrow> nat"
    assume eq: "(\<lambda>x. (s x) + (u x)) = (\<lambda>x. (t x) + (u x))"
    show "s = t"
    proof
      fix x::'a
      from eq have "(s x) + (u x) = (t x) + (u x)" by meson
      thus "s x = t x" by simp
    qed
  qed
qed

lemma times_eq_one_pp:
  assumes "s * t = (1::'a pp)"
  shows "s = 1"
using assms
proof transfer
  fix s t::"'a \<Rightarrow> nat"
  assume a: "(\<lambda>x. s x + t x) = (\<lambda>_. 0)"
  show "s = (\<lambda>_. 0)"
  proof
    fix x
    from a have "s x + t x = 0" by metis
    thus "s x = 0" by simp
  qed
qed

lemma exp_div_pp:
  shows "exp (s divide t) x = (if t dvd s then (exp s x - exp t x) else 0)"
unfolding dvd_pp by (transfer, simp)

lemma divide1_pp:
  shows "(s * t) divide t = (s::'a pp)"
proof transfer
  fix s t::"'a \<Rightarrow> nat"
  show "(if \<forall>x. t x \<le> s x + t x then \<lambda>x. s x + t x - t x else (\<lambda>_. 0)) = s" by (rule, simp)
qed

lemma divide2_pp:
  assumes "\<not> s dvd (t::'a pp)"
  shows "t divide s = 1"
by (intro pp_eq_intro, simp add: exp_div_pp assms, transfer, rule)

lemma dvd_lcm_pp:
  shows "s dvd (lcm s (t::'a pp))"
unfolding dvd_pp by (rule, transfer, simp)

lemma lcm_comm_pp:
  shows "lcm s t = lcm t (s::'a pp)"
by (transfer, rule, simp)

lemma lcm_min_pp:
  assumes "s dvd u" and "t dvd (u::'a pp)"
  shows "(lcm s t) dvd u"
using assms unfolding dvd_pp by (transfer, simp)

instance
apply standard
subgoal by (rule dummy_dvd_pp_dvd)
subgoal by (erule cancel_pp)
subgoal by (erule times_eq_one_pp)
subgoal by (rule divide1_pp)
subgoal by (erule divide2_pp)
subgoal by (rule dvd_lcm_pp)
subgoal by (rule lcm_comm_pp)
subgoal by (erule lcm_min_pp, simp)
subgoal by (rule Dickson_pp_finite)
done

end

subsection \<open>Term orders\<close>

text \<open>Term orders are certain linear orders on power-products, satisfying additional requirements.
  Further information on term orders can be found, e.\,g., in @{cite Robbiano1985}.\<close>

context linorder
begin

lemma ex_max:
  assumes "finite (A::'a set)" and "A \<noteq> {}"
  shows "\<exists>y\<in>A. (\<forall>z\<in>A. z \<le> y)"
using assms
proof (induct rule: finite_induct)
  assume "{} \<noteq> {}"
  thus "\<exists>y\<in>{}. \<forall>z\<in>{}. z \<le> y" by simp
next
  fix a::'a and A::"'a set"
  assume "a \<notin> A" and IH: "A \<noteq> {} \<Longrightarrow> \<exists>y\<in>A. (\<forall>z\<in>A. z \<le> y)"
  show "\<exists>y\<in>insert a A. (\<forall>z\<in>insert a A. z \<le> y)"
  proof (cases "A = {}")
    case True
    show ?thesis
    proof (rule bexI[of _ a], intro ballI)
      fix z
      assume "z \<in> insert a A"
      from this True have "z = a" by simp
      thus "z \<le> a" by simp
    qed (simp)
  next
    case False
    from IH[OF False] obtain y where "y \<in> A" and y_min: "\<forall>z\<in>A. z \<le> y" by auto
    from linear[of a y] show ?thesis
    proof
      assume "a \<le> y"
      show ?thesis
      proof (rule bexI[of _ y], intro ballI)
        fix z
        assume "z \<in> insert a A"
        hence "z = a \<or> z \<in> A" by simp
        thus "z \<le> y"
        proof
          assume "z = a"
          from this \<open>a \<le> y\<close> show "z \<le> y" by simp
        next
          assume "z \<in> A"
          from y_min[rule_format, OF this] show "z \<le> y" .
        qed
      next
        from \<open>y \<in> A\<close> show "y \<in> insert a A" by simp
      qed
    next
      assume "y \<le> a"
      show ?thesis
      proof (rule bexI[of _ a], intro ballI)
        fix z
        assume "z \<in> insert a A"
        hence "z = a \<or> z \<in> A" by simp
        thus "z \<le> a"
        proof
          assume "z = a"
          from this show "z \<le> a" by simp
        next
          assume "z \<in> A"
          from y_min[rule_format, OF this] \<open>y \<le> a\<close> show "z \<le> a" by simp
        qed
      qed (simp)
    qed
  qed
qed

end (* linorder *)

class finite_linorder = finite + linorder
begin

lemma neq_alt:
  assumes "s \<noteq> (t::'a pp)"
  obtains x where "exp s x \<noteq> exp t x" and "\<And>y. exp s y \<noteq> exp t y \<Longrightarrow> y \<le> x"
proof -
  assume a: "\<And>x. exp s x \<noteq> exp t x \<Longrightarrow> (\<And>y. exp s y \<noteq> exp t y \<Longrightarrow> y \<le> x) \<Longrightarrow> thesis"
  from assms pp_eq_intro[of s t] obtain x0 where exp_x0: "exp s x0 \<noteq> exp t x0" by auto
  let ?A = "{x::'a. exp s x \<noteq> exp t x}"
  have fin: "finite ?A" by simp
  from exp_x0 have "x0 \<in> ?A" by simp
  hence "?A \<noteq> {}" by auto
  from ex_max[OF fin this] obtain x where x_in: "x \<in> ?A" and x_max: "\<forall>z\<in>?A. z \<le> x" by auto
  from x_in have exp_x: "exp s x \<noteq> exp t x" by simp
  from x_max have x_max': "\<And>y. exp s y \<noteq> exp t y \<Longrightarrow> y \<le> x" by simp
  from a[OF exp_x x_max'] show ?thesis .
qed

subsubsection \<open>Lexicographic Term Order\<close>

definition lex::"'a pp \<Rightarrow> 'a pp \<Rightarrow> bool" where
  "lex s t \<equiv> (\<forall>x. exp s x \<le> exp t x \<or> (\<exists>y. y > x \<and> exp s y \<noteq> exp t y))"

lemma lex_alt:
  shows "lex s t = (s = t \<or> (\<exists>x. exp s x < exp t x \<and> (\<forall>y>x. exp s y = exp t y)))" (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (cases "s = t")
    assume "s = t"
    thus ?R by simp
  next
    assume "s \<noteq> t"
    from neq_alt[OF this] obtain x0
      where x0_neq: "exp s x0 \<noteq> exp t x0" and x0_max: "\<And>z. exp s z \<noteq> exp t z \<Longrightarrow> z \<le> x0" by auto
    show ?R
    proof (intro disjI2, rule exI[of _ x0], intro conjI)
      from \<open>?L\<close> have "exp s x0 \<le> exp t x0 \<or> (\<exists>y. y > x0 \<and> exp s y \<noteq> exp t y)" unfolding lex_def ..
      thus "exp s x0 < exp t x0"
      proof
        assume "exp s x0 \<le> exp t x0"
        from this x0_neq show ?thesis by simp
      next
        assume "\<exists>y. y > x0 \<and> exp s y \<noteq> exp t y"
        then obtain y where "y > x0" and y_neq: "exp s y \<noteq> exp t y" by auto
        from \<open>y > x0\<close> x0_max[OF y_neq] show ?thesis by simp
      qed
    next
      show "\<forall>y>x0. exp s y = exp t y"
      proof (rule, rule)
        fix y
        assume "x0 < y"
        hence "\<not> y \<le> x0" by simp
        from this x0_max[of y] show "exp s y = exp t y" by auto
      qed
    qed
  qed
next
  assume ?R
  thus ?L
  proof
    assume "s = t"
    thus ?thesis unfolding lex_def by simp
  next
    assume "\<exists>x. exp s x < exp t x \<and> (\<forall>y>x. exp s y = exp t y)"
    then obtain y where y_exp: "exp s y < exp t y" and y_max: "\<forall>z>y. exp s z = exp t z" by auto
    show ?thesis unfolding lex_def
    proof
      fix x
      show "exp s x \<le> exp t x \<or> (\<exists>y>x. exp s y \<noteq> exp t y)"
      proof (cases "exp s x \<le> exp t x")
        assume "exp s x \<le> exp t x"
        thus ?thesis by simp
      next
        assume s_exp: "\<not> exp s x \<le> exp t x"
        show ?thesis
        proof (intro disjI2, rule exI[of _ y], intro conjI)
          have "\<not> y \<le> x"
          proof
            assume "y \<le> x"
            hence "y < x \<or> y = x" by auto
            thus False
            proof
              assume "y < x"
              from s_exp y_max[rule_format, OF this] show ?thesis by simp
            next
              assume "y = x"
              from this s_exp y_exp show ?thesis by simp
            qed
          qed
          thus "x < y" by simp
        next
          from y_exp show "exp s y \<noteq> exp t y" by simp
        qed
      qed
    qed
  qed
qed

lemma lex_refl:
  shows "lex s s"
unfolding lex_alt by simp

lemma lex_antisym:
  assumes "lex s t" and "lex t s"
  shows "s = t"
proof (rule pp_eq_intro)
  fix x
  from \<open>lex s t\<close> have "s = t \<or> (\<exists>x. exp s x < exp t x \<and> (\<forall>y>x. exp s y = exp t y))"
    unfolding lex_alt .
  thus "exp s x = exp t x"
  proof
    assume "s = t"
    thus ?thesis by simp
  next
    assume "\<exists>x. exp s x < exp t x \<and> (\<forall>y>x. exp s y = exp t y)"
    then obtain x0 where exp_x0: "exp s x0 < exp t x0" and x0_max: "\<forall>y>x0. exp s y = exp t y" by auto
    from \<open>lex t s\<close> have "t = s \<or> (\<exists>x. exp t x < exp s x \<and> (\<forall>y>x. exp t y = exp s y))"
      unfolding lex_alt .
    thus ?thesis
    proof
      assume "t = s"
      thus ?thesis by simp
    next
      assume "\<exists>x. exp t x < exp s x \<and> (\<forall>y>x. exp t y = exp s y)"
      then obtain x1 where exp_x1: "exp t x1 < exp s x1" and x1_max: "\<forall>y>x1. exp t y = exp s y"
        by auto
      have "x0 < x1 \<or> x1 < x0 \<or> x1 = x0" using local.antisym_conv3 by auto
      show ?thesis
      proof (rule linorder_cases[of x0 x1])
        assume "x0 < x1"
        from x0_max[rule_format, OF this] exp_x1 show ?thesis by simp
      next
        assume "x0 = x1"
        from this exp_x0 exp_x1 show ?thesis by simp
      next
        assume "x1 < x0"
        from x1_max[rule_format, OF this] exp_x0 show ?thesis by simp
      qed
    qed
  qed
qed

lemma lex_trans:
  assumes "lex s t" and "lex t u"
  shows "lex s u"
proof -
  from \<open>lex s t\<close> have "s = t \<or> (\<exists>x. exp s x < exp t x \<and> (\<forall>y>x. exp s y = exp t y))"
    unfolding lex_alt .
  thus ?thesis
  proof
    assume "s = t"
    from this \<open>lex t u\<close> show ?thesis by simp
  next
    assume "\<exists>x. exp s x < exp t x \<and> (\<forall>y>x. exp s y = exp t y)"
    then obtain x0 where exp_x0: "exp s x0 < exp t x0" and x0_max: "\<forall>y>x0. exp s y = exp t y"
      by auto
    from \<open>lex t u\<close> have "t = u \<or> (\<exists>x. exp t x < exp u x \<and> (\<forall>y>x. exp t y = exp u y))"
      unfolding lex_alt .
    thus ?thesis
    proof
      assume "t = u"
      from this \<open>lex s t\<close> show ?thesis by simp
    next
      assume "\<exists>x. exp t x < exp u x \<and> (\<forall>y>x. exp t y = exp u y)"
      then obtain x1 where exp_x1: "exp t x1 < exp u x1" and x1_max: "\<forall>y>x1. exp t y = exp u y"
        by auto
      show ?thesis unfolding lex_alt
      proof (intro disjI2)
        show "\<exists>x. exp s x < exp u x \<and> (\<forall>y>x. exp s y = exp u y)"
        proof (rule linorder_cases[of x0 x1])
          assume "x0 < x1"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from x0_max[rule_format, OF \<open>x0 < x1\<close>] exp_x1 show "exp s x1 < exp u x1" by simp
          next
            show "\<forall>y>x1. exp s y = exp u y"
            proof (intro allI, intro impI)
              fix y
              assume "x1 < y"
              from this \<open>x0 < x1\<close> have "x0 < y" by simp
              from x0_max[rule_format, OF this] x1_max[rule_format, OF \<open>x1 < y\<close>]
                show "exp s y = exp u y" by simp
            qed
          qed
        next
          assume "x1 < x0"
          show ?thesis
          proof (rule exI[of _ x0], intro conjI)
            from x1_max[rule_format, OF \<open>x1 < x0\<close>] exp_x0 show "exp s x0 < exp u x0" by simp
          next
            show "\<forall>y>x0. exp s y = exp u y"
            proof (intro allI, intro impI)
              fix y
              assume "x0 < y"
              from this \<open>x1 < x0\<close> have "x1 < y" by simp
              from x0_max[rule_format, OF \<open>x0 < y\<close>] x1_max[rule_format, OF this]
                show "exp s y = exp u y" by simp
            qed
          qed
        next
          assume "x0 = x1"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from \<open>x0 = x1\<close> exp_x0 exp_x1 show "exp s x1 < exp u x1" by simp
          next
            show "\<forall>y>x1. exp s y = exp u y"
            proof (intro allI, intro impI)
              fix y
              assume "x1 < y"
              hence "x0 < y" using \<open>x0 = x1\<close> by simp
              from x0_max[rule_format, OF this] x1_max[rule_format, OF \<open>x1 < y\<close>]
                show "exp s y = exp u y" by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma lex_lin:
  shows "lex s t \<or> lex t s"
proof (intro disjCI)
  assume "\<not> lex t s"
  hence a: "\<forall>x. \<not> (exp t x < exp s x) \<or> (\<exists>y>x. exp t y \<noteq> exp s y)" unfolding lex_alt by auto
  show "lex s t" unfolding lex_def
  proof
    fix x
    from a have "\<not> (exp t x < exp s x) \<or> (\<exists>y>x. exp t y \<noteq> exp s y)" ..
    thus "exp s x \<le> exp t x \<or> (\<exists>y>x. exp s y \<noteq> exp t y)" by auto
  qed
qed

lemma lex_one_min:
  shows "lex 1 s"
unfolding lex_def
by (intro allI, intro disjI1, transfer, simp)

lemma lex_times_monotone:
  assumes "lex s t"
  shows "lex (s * u) (t * u)"
unfolding lex_def
proof
  fix x
  from assms have "exp s x \<le> exp t x \<or> (\<exists>y>x. exp s y \<noteq> exp t y)" unfolding lex_def ..
  thus "exp (s * u) x \<le> exp (t * u) x \<or> (\<exists>y>x. exp (s * u) y \<noteq> exp (t * u) y)"
  proof
    assume a1: "exp s x \<le> exp t x"
    show ?thesis
    proof (intro disjI1)
      from a1 show "exp (s * u) x \<le> exp (t * u) x" by (transfer, simp)
    qed
  next
    assume "\<exists>y>x. exp s y \<noteq> exp t y"
    then obtain y where "x < y" and a2: "exp s y \<noteq> exp t y" by auto
    show ?thesis
    proof (intro disjI2, rule exI[of _ y], intro conjI, fact)
      from a2 show "exp (s * u) y \<noteq> exp (t * u) y" by (transfer, simp)
    qed
  qed
qed

subsubsection \<open>General Degree-Orders\<close>

definition deg::"'a pp \<Rightarrow> nat" where "deg s \<equiv> \<Sum>x\<in>(UNIV::'a set). exp s x"

lemma setsum_nat_cong:
  fixes f g::"'a \<Rightarrow> nat" and A::"'a set"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows "(\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. g x)" (is "?L = ?R")
using assms unfolding setsum_def
by (meson add.comm_monoid_axioms comm_monoid_set.cong comm_monoid_set_def)

lemma deg_one:
  shows "deg 1 = 0"
proof -
  have fin: "finite (UNIV::'a set)" by simp
  have "\<forall>x\<in>UNIV. exp 1 x = 0" by (intro ballI, transfer, simp)
  from this setsum_eq_0_iff[OF fin] show ?thesis unfolding deg_def by simp
qed

lemma deg_times:
  shows "deg (s * t) = deg s + deg t"
proof -
  have "deg (s * t) = (\<Sum>x\<in>UNIV. exp s x + exp t x)" unfolding deg_def
    by (rule setsum_nat_cong, transfer, simp)
  also have "\<dots> = deg s + deg t" using setsum.distrib[of "exp s" "exp t" "UNIV::'a set"]
    unfolding deg_def .
  finally show ?thesis .
qed

definition dord::"('a pp \<Rightarrow> 'a pp \<Rightarrow> bool) \<Rightarrow> 'a pp \<Rightarrow> 'a pp \<Rightarrow> bool" where
  "dord ord s t \<equiv> (let d1 = deg s; d2 = deg t in (d1 < d2 \<or> (d1 = d2 \<and> ord s t)))"

lemma dord_degE:
  assumes "dord ord s t"
  shows "deg s \<le> deg t"
using assms unfolding dord_def Let_def by auto

lemma dord_refl:
  assumes "ord s s"
  shows "dord ord s s"
using assms unfolding dord_def by simp

lemma dord_antisym:
  assumes "dord ord s t" and "dord ord t s" and ord_antisym: "ord s t \<Longrightarrow> ord t s \<Longrightarrow> s = t"
  shows "s = t"
proof -
  from \<open>dord ord t s\<close> have ts: "deg t < deg s \<or> (deg t = deg s \<and> ord t s)"
    unfolding dord_def Let_def .
  from \<open>dord ord s t\<close> have st: "deg s < deg t \<or> (deg s = deg t \<and> ord s t)"
    unfolding dord_def Let_def .
  thus ?thesis
  proof
    assume "deg s < deg t"
    thus ?thesis using ts by simp
  next
    assume "deg s = deg t \<and> ord s t"
    hence "deg s = deg t" and "ord s t" by simp_all
    from \<open>deg s = deg t\<close> ts have "ord t s" by simp
    from ord_antisym[OF \<open>ord s t\<close> this] show ?thesis .
  qed
qed

lemma dord_trans:
  assumes "dord ord s t" and "dord ord t u" and ord_trans: "ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u"
  shows "dord ord s u"
proof -
  from \<open>dord ord t u\<close> have ts: "deg t < deg u \<or> (deg t = deg u \<and> ord t u)"
    unfolding dord_def Let_def .
  from \<open>dord ord s t\<close> have st: "deg s < deg t \<or> (deg s = deg t \<and> ord s t)"
    unfolding dord_def Let_def .
  thus ?thesis
  proof
    assume "deg s < deg t"
    from this dord_degE[OF \<open>dord ord t u\<close>] have "deg s < deg u" by simp
    thus ?thesis unfolding dord_def Let_def by simp
  next
    assume "deg s = deg t \<and> ord s t"
    hence "deg s = deg t" and "ord s t" by simp_all
    from ts show ?thesis
    proof
      assume "deg t < deg u"
      hence "deg s < deg u" using \<open>deg s = deg t\<close> by simp
      thus ?thesis unfolding dord_def Let_def by simp
    next
      assume "deg t = deg u \<and> ord t u"
      hence "deg t = deg u" and "ord t u" by simp_all
      from ord_trans[OF \<open>ord s t\<close> \<open>ord t u\<close>] \<open>deg s = deg t\<close> \<open>deg t = deg u\<close> show ?thesis
        unfolding dord_def Let_def by simp
    qed
  qed
qed

lemma dord_lin:
  assumes "ord s t \<or> ord t s"
  shows "dord ord s t \<or> dord ord t s"
proof (intro disjCI)
  assume "\<not> dord ord t s"
  hence "deg s \<le> deg t \<and> (deg t \<noteq> deg s \<or> \<not> ord t s)" unfolding dord_def Let_def by auto
  hence "deg s \<le> deg t" and dis1: "deg t \<noteq> deg s \<or> \<not> ord t s" by simp_all
  show "dord ord s t" unfolding dord_def Let_def
  proof (intro disjCI)
    assume "\<not> (deg s = deg t \<and> ord s t)"
    hence dis2: "deg s \<noteq> deg t \<or> \<not> ord s t" by simp
    show "deg s < deg t"
    proof (cases "deg s = deg t")
      case True
      from True dis1 have "\<not> ord t s" by simp
      from True dis2 have "\<not> ord s t" by simp
      from \<open>\<not> ord s t\<close> \<open>\<not> ord t s\<close> assms show ?thesis by simp
    next
      case False
      from this \<open>deg s \<le> deg t\<close> show ?thesis by simp
    qed
  qed
qed

lemma dord_one_min:
  assumes "ord 1 s"
  shows "dord ord 1 s"
using assms unfolding dord_def Let_def deg_one by auto

lemma dord_times_monotone:
  assumes "dord ord s t" and ord_monotone: "ord s t \<Longrightarrow> ord (s * u) (t * u)"
  shows "dord ord (s * u) (t * u)"
proof -
  from \<open>dord ord s t\<close> have "deg s < deg t \<or> (deg s = deg t \<and> ord s t)" unfolding dord_def Let_def .
  thus ?thesis
  proof
    assume "deg s < deg t"
    hence "deg (s * u) < deg (t * u)" using deg_times by simp
    thus ?thesis unfolding dord_def Let_def by simp
  next
    assume "deg s = deg t \<and> ord s t"
    hence "deg s = deg t" and "ord s t" by simp_all
    from \<open>deg s = deg t\<close> deg_times have "deg (s * u) = deg (t * u)" by simp
    from this ord_monotone[OF \<open>ord s t\<close>] show ?thesis unfolding dord_def Let_def by simp
  qed
qed

subsubsection \<open>Degree-Lexicographic Term Order\<close>

definition dlex::"'a pp \<Rightarrow> 'a pp \<Rightarrow> bool" where "dlex \<equiv> dord lex"

lemma dlex_refl:
  shows "dlex s s"
unfolding dlex_def by (rule dord_refl, rule lex_refl)

lemma dlex_antisym:
  assumes "dlex s t" and "dlex t s"
  shows "s = t"
using assms unfolding dlex_def by (rule dord_antisym[OF _ _ lex_antisym], simp_all)

lemma dlex_trans:
  assumes "dlex s t" and "dlex t u"
  shows "dlex s u"
using assms unfolding dlex_def by (rule dord_trans[OF _ _ lex_trans], simp_all)

lemma dlex_lin:
  shows "dlex s t \<or> dlex t s"
unfolding dlex_def by (rule dord_lin, rule lex_lin)

lemma dlex_one_min:
  shows "dlex 1 s"
unfolding dlex_def by (rule dord_one_min, rule lex_one_min)

lemma dlex_times_monotone:
  assumes "dlex s t"
  shows "dlex (s * u) (t * u)"
using assms unfolding dlex_def by (rule dord_times_monotone[of lex s t, OF _ lex_times_monotone], simp)

end (* finite_linorder *)

subsubsection \<open>@{typ "'a pp"} belongs to class @{class linorder}\<close>

text \<open>We now prove that @{typ "'a pp"} is linearly ordered, with @{term "op \<le>"} instantiated by
  @{term lex}. This is only relevant for general multiplication of polynomials, but not for anything
  directly related to Gröbner bases.
  Note further that there is nothing special about the use of @{term lex} here; @{emph \<open>any\<close>} linear
  order on @{typ "'a pp"} would be fine (it does not even have to be a term order).\<close>

text \<open>The term order to be used when computing Gröbner bases has to be specified when interpreting
  locale @{term ordered_powerprod}; see theory "PolyLists.thy".\<close>

instantiation pp :: (finite_linorder) linorder
begin

definition "less_eq_pp \<equiv> lex"
definition less_pp::"'a pp \<Rightarrow> 'a pp \<Rightarrow> bool" where "less_pp s t \<equiv> s \<le> t \<and> \<not> (t \<le> s)"

instance
apply standard
subgoal unfolding less_pp_def ..
apply (simp_all only: less_eq_pp_def)
subgoal by (rule lex_refl)
subgoal by (erule lex_trans, simp)
subgoal by (erule lex_antisym, simp)
subgoal by (rule lex_lin)
done

end

end