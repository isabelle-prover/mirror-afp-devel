(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Abstract Power-Products\<close>

theory Power_Products
  imports Complex_Main
  "Deep_Learning.PP_More_MPoly"
begin

text \<open>This theory formalizes the concept of "power-products". A power-product can be thought of as
  the product of some indeterminates, such as $x$, $x^2\,y$, $x\,y^3\,z^7$, etc., without any
  scalar coefficient.

The approach in this theory is to capture the notion of "power-product" (also called "monomial") as
type class. A canonical instance for power-product is the type @{typ "'var \<Rightarrow>\<^sub>0 nat"}, which is
interpreted as mapping from variables in the power-product to exponents.

A slightly unintuitive (but fitting better with the standard type class instantiations of
@{typ "'a \<Rightarrow>\<^sub>0 'b"}) approach is to write addition to denote "multiplication" of power products.
For example, $x^2y$ would be represented as a function \<open>p = (X \<mapsto> 2, Y \<mapsto> 1)\<close>, $xz$ as a
function \<open>q = (X \<mapsto> 1, Z \<mapsto> 1)\<close>. With the (pointwise) instantiation of addition of @{typ "'a \<Rightarrow>\<^sub>0 'b"},
we will write \<open>p + q = (X \<mapsto> 3, Y \<mapsto> 1, Z \<mapsto> 1)\<close> for the product $x^2y \cdot xz = x^3yz$
\<close>

subsection \<open>Class of Abstract Power-Products\<close>

subsubsection \<open>Class of Unordered Power-Products\<close>

subsection \<open>'divisibility' on additive structures\<close>

context plus begin

definition adds :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "adds" 50)
  where "b adds a \<longleftrightarrow> (\<exists>k. a = b + k)"

lemma addsI [intro?]: "a = b + k \<Longrightarrow> b adds a"
  unfolding adds_def ..

lemma addsE [elim?]: "b adds a \<Longrightarrow> (\<And>k. a = b + k \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding adds_def by blast

end

context comm_monoid_add
begin

lemma adds_refl [simp]: "a adds a"
proof
  show "a = a + 0" by simp
qed

lemma adds_trans [trans]:
  assumes "a adds b" and "b adds c"
  shows "a adds c"
proof -
  from assms obtain v where "b = a + v"
    by (auto elim!: addsE)
  moreover from assms obtain w where "c = b + w"
    by (auto elim!: addsE)
  ultimately have "c = a + (v + w)"
    by (simp add: add.assoc)
  then show ?thesis ..
qed

lemma subset_divisors_adds: "{c. c adds a} \<subseteq> {c. c adds b} \<longleftrightarrow> a adds b"
  by (auto simp add: subset_iff intro: adds_trans)

lemma strict_subset_divisors_adds: "{c. c adds a} \<subset> {c. c adds b} \<longleftrightarrow> a adds b \<and> \<not> b adds a"
  by (auto simp add: subset_iff intro: adds_trans)

lemma zero_adds [simp]: "0 adds a"
  by (auto intro!: addsI)

lemma adds_plus [simp]: "a adds c \<Longrightarrow> a adds (b + c)"
  by (auto intro!: add.left_commute addsI elim!: addsE)

lemma adds_plus2 [simp]: "a adds b \<Longrightarrow> a adds (b + c)"
  using adds_plus [of a b c] by (simp add: ac_simps)

lemma adds_triv_right [simp]: "a adds b + a"
  by (rule adds_plus) (rule adds_refl)

lemma adds_triv_left [simp]: "a adds a + b"
  by (rule adds_plus2) (rule adds_refl)

lemma plus_adds_mono:
  assumes "a adds b"
    and "c adds d"
  shows "a + c adds b + d"
proof -
  from \<open>a adds b\<close> obtain b' where "b = a + b'" ..
  moreover from \<open>c adds d\<close> obtain d' where "d = c + d'" ..
  ultimately have "b + d = (a + c) + (b' + d')"
    by (simp add: ac_simps)
  then show ?thesis ..
qed

lemma adds_plus_left: "a + b adds c \<Longrightarrow> a adds c"
  by (simp add: adds_def add.assoc) blast

lemma adds_plus_right: "a + b adds c \<Longrightarrow> b adds c"
  using adds_plus_left [of b a c] by (simp add: ac_simps)

end

class comm_powerprod = cancel_comm_monoid_add
begin

lemma adds_canc: "s + u adds t + u \<longleftrightarrow> s adds t" for s t u::'a
  unfolding adds_def
  apply auto
   apply (metis local.add.left_commute local.add_diff_cancel_left' local.add_diff_cancel_right')
  using add_assoc add_commute by auto

lemma dvd_canc_2: "u + s adds u + t \<longleftrightarrow> s adds t"
  by (simp add: adds_canc ac_simps)

lemma add_minus_2: "(s + t) - s = t"
  by simp

lemma adds_minus:
  assumes "s adds t"
  shows "(t - s) + s = t"
proof -
  from assms adds_def[of s t] obtain u where u: "t = u + s" by (auto simp: ac_simps)
  then have "t - s = u"
    by simp
  thus ?thesis using u by simp
qed

lemma plus_adds_0:
  assumes "(s + t) adds u"
  shows "s adds (u - t)"
proof -
  from assms adds_minus[OF adds_plus_right[OF assms]] have "(s + t) adds ((u - t) + t)" by simp
  thus ?thesis using adds_canc[of s t "u - t"] by simp
qed

lemma plus_adds_2:
  assumes "t adds u" and "s adds (u - t)"
  shows "(s + t) adds u"
  by (metis adds_canc adds_minus assms)

lemma plus_adds:
  shows "(s + t) adds u \<longleftrightarrow> (t adds u \<and> s adds (u - t))"
proof
  assume a1: "(s + t) adds u"
  show "t adds u \<and> s adds (u - t)"
  proof
    from adds_plus_right[OF a1] show "t adds u" .
  next
    from plus_adds_0[OF a1] show "s adds (u - t)" .
  qed
next
  assume "t adds u \<and> s adds (u - t)"
  hence "t adds u" and "s adds (u - t)" by auto
  from plus_adds_2[OF \<open>t adds u\<close> \<open>s adds (u - t)\<close>] show "(s + t) adds u" .
qed

lemma minus_plus:
  assumes "s adds t"
  shows "(t - s) + u = (t + u) - s"
proof -
  from assms obtain k where k: "t = s + k" unfolding adds_def ..
  hence "t - s = k" by simp
  also from k have "(t + u) - s = k + u"
    by (simp add: add_assoc)
  finally show ?thesis by simp
qed

lemma minus_plus_minus:
  assumes "s adds t" and "u adds v"
  shows "(t - s) + (v - u) = (t + v) - (s + u)"
  using add_commute assms(1) assms(2) diff_diff_add minus_plus by auto

lemma minus_plus_minus_cancel:
  assumes "u adds t" and "s adds u"
  shows "(t - u) + (u - s) = t - s"
  by (metis assms(1) assms(2) local.add_diff_cancel_left' local.add_diff_cancel_right local.addsE minus_plus)

end

text \<open>Instances of class \<open>lcs_powerprod\<close> are types of commutative power-products admitting
  @{emph \<open>unique\<close>} least common sums (inspired from least common multiplies).
  Note that if the components of indeterminates are arbitrary integers (as for instance in Laurent
  polynomials), then no such unique lcss exist.\<close>
class lcs_powerprod = comm_powerprod +
  fixes lcs::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes adds_lcs: "s adds (lcs s t)"
  assumes lcs_min: "s adds u \<Longrightarrow> t adds u \<Longrightarrow> (lcs s t) adds u"
  assumes lcs_comm: "lcs s t = lcs t s"
  assumes plus_eq_one: "s + t = 0 \<Longrightarrow> s = 0"
begin

lemma adds_lcs_2: "t adds (lcs s t)"
  by (simp add: lcs_comm[of s t], rule adds_lcs)

lemma plus_eq_one_2: "t = 0" if "s + t = 0"
  using that
  by (simp only: add_commute[of s t] plus_eq_one)

lemma adds_one: "s adds 0 \<longleftrightarrow> (s = 0)"
proof
  assume "s adds 0"
  from this obtain k where "0 = s + k" unfolding adds_def ..
  from this plus_eq_one[of s k] show "s = 0"
    by blast
next
  assume "s = 0"
  thus "s adds 0" by simp
qed

lemma adds_antisym:
  assumes "s adds t" "t adds s"
  shows "s = t"
proof -
  from \<open>s adds t\<close> obtain u where u_def: "t = s + u" unfolding adds_def ..
  from \<open>t adds s\<close> obtain v where v_def: "s = t + v" unfolding adds_def ..
  from u_def v_def have "s = (s + u) + v" by (simp add: ac_simps)
  hence "s + 0 = s + (u + v)" by (simp add: ac_simps)
  hence "u + v = 0" by simp
  hence "u = 0" using plus_eq_one[of u v] by simp
  thus ?thesis using u_def by simp
qed

end

text \<open>Instances of class \<open>dickson_powerprod\<close> are types of commutative power-products satisfying the
  Dickson property.\<close>
class dickson_powerprod = lcs_powerprod +
  assumes dickson: "\<And>seq::nat \<Rightarrow> 'a. (\<exists>i j::nat. i < j \<and> seq i adds seq j)"

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
  ordered_powerprod_lin: linorder ord ord_strict
  for ord::"'a \<Rightarrow> 'a::comm_powerprod \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict::"'a \<Rightarrow> 'a::comm_powerprod \<Rightarrow> bool" (infixl "\<prec>" 50) +
  assumes one_min: "0 \<preceq> t"
  assumes plus_monotone: "s \<preceq> t \<Longrightarrow> s + u \<preceq> t + u"
begin

lemma ord_canc:
  assumes "s + u \<preceq> t + u"
  shows "s \<preceq> t"
proof (rule ordered_powerprod_lin.le_cases[of s t], simp)
  assume "t \<preceq> s"
  from assms plus_monotone[OF this, of u] have "t + u = s + u"
    using ordered_powerprod_lin.eq_iff by simp
  hence "t = s" by simp
  thus "s \<preceq> t" by simp
qed

lemma ord_adds:
  assumes "s adds t"
  shows "s \<preceq> t"
proof -
  from assms have "\<exists>u. t = s + u" unfolding adds_def by simp
  then obtain k where "t = s + k" ..
  thus ?thesis using plus_monotone[OF one_min[of k], of s] by (simp add: ac_simps)
qed

end

text \<open>Instances of \<open>od_powerprod\<close> must satisfy the Dickson property.\<close>
locale od_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"'a \<Rightarrow> 'a::dickson_powerprod \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and ord_strict (infixl "\<prec>" 50)
begin

lemma wf_ord_strict:
  shows "wfP (\<prec>)"
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
    from dickson[of seq] obtain i j::nat where "i < j \<and> seq i adds seq j" by auto
    hence "i < j" and i_adds_j: "seq i adds seq j" by auto
    from seq_decr[rule_format, OF \<open>i < j\<close>] have "seq j \<preceq> seq i \<and> seq j \<noteq> seq i" by auto
    hence "seq j \<preceq> seq i" and "seq j \<noteq> seq i" by simp_all
    from \<open>seq j \<noteq> seq i\<close> \<open>seq j \<preceq> seq i\<close> ord_adds[OF i_adds_j]
         ordered_powerprod_lin.eq_iff[of "seq j" "seq i"]
      show False by simp
  qed
qed

end

subsection \<open>Type @{type poly_mapping}\<close>

lemma in_keys_iff: "x \<in> (keys s) = (lookup s x \<noteq> 0)"
  by (transfer, simp)

lemma finite_neq_0:
  assumes fin_A: "finite {x. f x \<noteq> 0}" and fin_B: "finite {x. g x \<noteq> 0}" and "\<And>x. h x 0 0 = 0"
  shows "finite {x. h x (f x) (g x) \<noteq> 0}"
proof -
  from fin_A fin_B have  "finite ({x. f x \<noteq> 0} \<union> {x. g x \<noteq> 0})" by (intro finite_UnI)
  hence finite_union: "finite {x. (f x \<noteq> 0) \<or> (g x \<noteq> 0)}" by (simp only: Collect_disj_eq)
  have "{x. h x (f x) (g x) \<noteq> 0} \<subseteq> {x. (f x \<noteq> 0) \<or> (g x \<noteq> 0)}"
  proof (intro Collect_mono, rule)
    fix x::'a
    assume h_not_zero: "h x (f x) (g x) \<noteq> 0"
    have "f x = 0 \<Longrightarrow> g x \<noteq> 0"
    proof
      assume "f x = 0" "g x = 0"
      thus False using h_not_zero \<open>h x 0 0 = 0\<close>  by simp
    qed
    thus "f x \<noteq> 0 \<or> g x \<noteq> 0" by auto
  qed
  from finite_subset[OF this] finite_union show "finite {x. h x (f x) (g x) \<noteq> 0}" .
qed

lemma finite_neq_0':
  assumes "finite {x. f x \<noteq> 0}" and "finite {x. g x \<noteq> 0}" and "h 0 0 = 0"
  shows "finite {x. h (f x) (g x) \<noteq> 0}"
using assms by (rule finite_neq_0)

lemma adds_pp: "s adds t \<longleftrightarrow> (\<forall>x. lookup s x \<le> lookup t x)"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::{canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}"
unfolding adds_def
proof
  assume "\<exists>k. t = s + k"
  from this obtain k where "t = s + k" ..
  thus "\<forall>x. lookup s x \<le> lookup t x"
  proof transfer
    fix s t k::"'a \<Rightarrow> 'b"
    assume eq: "t = (\<lambda>x. s x + k x)"
    show "\<forall>x. s x \<le> t x" by (rule, simp add: eq)
  qed
next
  assume "\<forall>x. lookup s x \<le> lookup t x"
  thus "\<exists>k. t = s + k"
  proof transfer
    fix s t::"'a \<Rightarrow> 'b"
    assume "finite {x. t x \<noteq> 0}" and "finite {x. s x \<noteq> 0}"
    from finite_neq_0'[OF this, of "(-)"] have fin: "finite {x. t x - s x \<noteq> 0}" by simp
    assume a: "\<forall>x. s x \<le> t x"
    show "\<exists>k\<in>{f. finite {t. f t \<noteq> 0}}. t = (\<lambda>x. s x + k x)"
    proof (rule bexI[of _ "\<lambda>x. t x - s x"], rule)
      fix x
      from a have "s x \<le> t x" ..
      thus "t x = s x + (t x - s x)"
        by (metis add_diff_cancel_left' le_iff_add)
    next
      from fin show "(\<lambda>k. t k - s k) \<in> {f. finite {x. f x \<noteq> 0}}" by blast
    qed
  qed
qed

subsubsection \<open>@{typ "('a , 'b) poly_mapping"} belongs to class @{class comm_powerprod}\<close>

lemma poly_mapping_eq_iff: "a = b \<longleftrightarrow> (\<forall>i. lookup a i = lookup b i)"
  using poly_mapping_eqI by blast

instance poly_mapping :: (type, cancel_comm_monoid_add) comm_powerprod
  by standard


subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class lcs_powerprod}\<close>

instantiation poly_mapping :: (type, "{ordered_ab_semigroup_monoid_add_imp_le,canonically_ordered_monoid_add,linorder}") lcs_powerprod
begin

lift_definition lcs_poly_mapping::"('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is "\<lambda>s t. \<lambda>x. max (s x) (t x)"
proof -
  fix fun1 fun2::"'a \<Rightarrow> 'b"
  assume "finite {t. fun1 t \<noteq> 0}" and "finite {t. fun2 t \<noteq> 0}"
  from finite_neq_0'[OF this, of max] show "finite {t. max (fun1 t) (fun2 t) \<noteq> 0}"
    by (auto simp: max_def)
qed

lemma adds_lcs_poly_mapping:
  shows "s adds (lcs s (t::'a \<Rightarrow>\<^sub>0 'b))"
  unfolding adds_pp
  by transfer (auto simp: max_def)

lemma lcs_comm_pp:  "lcs s t = lcs t (s::'a \<Rightarrow>\<^sub>0 'b)"
  by transfer (auto simp: max_def intro!: ext)

lemma lcs_min_pp:
  assumes "s adds u" and "t adds (u::'a \<Rightarrow>\<^sub>0 'b)"
  shows "(lcs s t) adds u"
using assms unfolding adds_pp by (transfer, simp)

lemma plus_eq_zero_pp:
  assumes "s + t = (0::'a \<Rightarrow>\<^sub>0 'b)"
  shows "s = 0"
using assms
proof transfer
  fix s t::"'a \<Rightarrow> 'b"
  assume a: "(\<lambda>x. s x + t x) = (\<lambda>_. 0)"
  show "s = (\<lambda>_. 0)"
  proof
    fix x
    from a have "s x + t x = 0" by metis
    thus "s x = 0" by simp
  qed
qed

instance
  apply standard
  subgoal by (rule adds_lcs_poly_mapping)
  subgoal by (rule lcs_min_pp)
  subgoal by (rule lcs_comm_pp)
  subgoal using plus_eq_zero_pp by blast
  done

end

subsection \<open>Power-products in a given set of indeterminates.\<close>

definition in_keys::"'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool" where "in_keys V s \<longleftrightarrow> keys s \<subseteq> V"

lift_definition truncate::"'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero)"
  is "\<lambda>V s. \<lambda>x. (if x \<in> V then s x else 0)"
proof -
  fix V::"'a set" and s::"'a \<Rightarrow> 'b"
  assume fin: "finite {x. s x \<noteq> 0}"
  have "finite {_. 0 \<noteq> 0}" by simp
  from finite_neq_0[OF fin this, of "\<lambda>x t f. (if x \<in> V then t else f)"]
    show "finite {x. (if x \<in> V then s x else 0) \<noteq> 0}" by simp
qed

lemma univ_keys: "in_keys (UNIV::'a set) s"
by (simp add: in_keys_def)

lemma empty_keys: "in_keys {} s = (s = 0)"
  unfolding in_keys_def
  by transfer auto

lemma truncate_in: "in_keys V (truncate V s)"
  unfolding in_keys_def
  by transfer auto

lemma add_union_in_keys:
  fixes V U::"'a set" and s t::"'a \<Rightarrow>\<^sub>0 'b::monoid_add"
  assumes "in_keys V s" and "in_keys U t"
  shows "in_keys (V \<union> U) (s + t)"
  using assms
  unfolding in_keys_def
  by transfer force

lemma adds_insert_keys:
  fixes s t::"'a \<Rightarrow>\<^sub>0 'b::{canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}"
  assumes "in_keys (insert v V) s" and "in_keys (insert v V) t"
  shows "s adds t = (truncate V s adds truncate V t \<and> lookup s v \<le> lookup t v)"
  using assms unfolding adds_pp in_keys_def
  by transfer (auto; force)

subsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

(*The following lemma was provided by Manuel Eberl*)
lemma nat_incr_subsequence:
  fixes f :: "nat \<Rightarrow> 'a::wellorder"
  obtains g where "strict_mono g" "incseq (f \<circ> g)"
proof -
  from seq_monosub[of f] obtain g
    where subseq: "strict_mono g" and mono: "monoseq (f \<circ> g)" by (auto simp: o_def)
  from mono show ?thesis unfolding monoseq_iff
  proof
    assume decseq: "decseq (f \<circ> g)"
    define M where "M \<equiv> LEAST n. n \<in> range (f \<circ> g)"
    have "M \<in> range (f \<circ> g)" unfolding M_def by (rule LeastI_ex) blast
    then obtain n where n: "f (g n) = M" unfolding o_def by blast

    have "strict_mono (g \<circ> (\<lambda>x. x + n))" 
      by (intro strict_mono_o subseq) (auto simp: strict_mono_def)
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
  fixes V::"'a set"
    and f::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b::{wellorder,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}"
  assumes fin: "finite V" and "\<forall>k. in_keys V (f k)"
  shows "\<exists>m::nat \<Rightarrow> nat. (strict_mono m) \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i adds (f o m) j)"
  using assms
proof (induct V arbitrary: f)
  fix f::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  assume "\<forall>k. in_keys {} (f k)"
  then have "\<forall>k. f k = 0" by (intro allI, simp_all only: empty_keys)
  then show "\<exists>m. strict_mono (m::nat\<Rightarrow>nat) \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i adds (f o m) j)" unfolding adds_pp
  proof transfer
    fix f::"nat \<Rightarrow> 'a \<Rightarrow> 'b"
    assume all_one: "\<forall>k. f k = (\<lambda>_. 0)"
    show "\<exists>m. strict_mono (m::nat\<Rightarrow>nat) \<and> (\<forall>i j. i < j \<longrightarrow> (\<forall>x. (f o m) i x \<le> (f o m) j x))"
    proof
      from all_one show "strict_mono id \<and> (\<forall>i j. i < j \<longrightarrow> (\<forall>x. (f \<circ> id) i x \<le> (f \<circ> id) j x))"
        by (simp add: strict_mono_def)
    qed
  qed
next
  fix v::'a and F::"'a set" and f::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  assume "finite F" and "v \<notin> F"
    and IH: "(\<And>f:: nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b. (\<forall>k. in_keys F (f k)) \<Longrightarrow>
                (\<exists>m::nat\<Rightarrow>nat. strict_mono m \<and> ( \<forall>i j. i < j \<longrightarrow> (f o m) i adds (f o m) j)))"
    and seq_in_insert: "\<forall>k. in_keys (insert v F) (f k)"

  (*Construction of first mapping*)
  have IH_prem: "\<forall>k. in_keys F ((truncate F o f) k)"
  proof
    fix k::nat
    show "in_keys F ((truncate F o f) k)" by (simp add: truncate_in)
  qed
  from IH[OF IH_prem] obtain m1::"nat \<Rightarrow> nat" where
    "strict_mono m1 \<and> (\<forall>i j. i < j \<longrightarrow> ((truncate F) o f o m1) i adds ((truncate F) o f o m1) j)" ..
  then have m1_subseq: "strict_mono m1"
    and m1_div: "\<forall>i j. i < j \<longrightarrow> ((truncate F) o f o m1) i adds ((truncate F) o f o m1) j"
    by simp_all

  (*Construction of second mapping (using lemma nat_incr_subsequence for backward reasoning)*)
  show "\<exists>m. strict_mono (m::nat\<Rightarrow>nat) \<and> (\<forall>i j. i < j \<longrightarrow> ((f o m) i) adds ((f o m) j))"
  proof (rule nat_incr_subsequence[of "(\<lambda>x. lookup x v) o f o m1"])
    fix m2::"nat \<Rightarrow> nat"
    assume m2_subseq: "strict_mono m2" and "incseq ((\<lambda>x. lookup x v) \<circ> f \<circ> m1 \<circ> m2)"
    then have m2_div: "\<forall>i j. i < j \<longrightarrow> ((\<lambda>x. lookup x v) \<circ> f \<circ> (m1 o m2)) i \<le> ((\<lambda>x. lookup x v) \<circ> f \<circ> (m1 o m2)) j"
      by (simp add: incseq_def)
    
    let ?m = "(m1 o m2)"
    show "\<exists>m. strict_mono (m::nat\<Rightarrow>nat) \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i adds (f o m) j)"
    proof (rule, rule)
      show "strict_mono ?m" using m1_subseq m2_subseq by (intro strict_mono_o)
    next
      show "\<forall>i j. i < j \<longrightarrow> (f o ?m) i adds (f o ?m) j"
      proof (rule, rule, rule)
        fix i j::nat
        assume i_less_j: "i < j"

        (*i-th and j-th element are in (insert v F)*)
        from seq_in_insert have in_indets_i:"in_keys (insert v F) ((f o ?m) i)"
          and in_indets_j: "in_keys (insert v F) ((f o ?m) j)" by simp_all

        (*v-component of i-th element is leq v-component of j-th element*)
        from m2_div have m2_div_i_j: "i < j \<longrightarrow> ((\<lambda>x. lookup x v) \<circ> f \<circ> ?m) i \<le> ((\<lambda>x. lookup x v) \<circ> f \<circ> ?m) j"
          by simp
        hence v_div: "(lookup ((f o ?m) i) v) \<le> (lookup ((f o ?m) j) v)" using i_less_j by simp

        (*F-components of i-th element divide F-components of j-th element*)
        from m1_div have m1_div_i_j: "m2 i < m2 j \<longrightarrow> ((truncate F) o f o ?m) i adds ((truncate F) o f o ?m) j"
          by simp
        hence F_div: "truncate F ((f o ?m) i) adds truncate F ((f o ?m) j)"
          using i_less_j m2_subseq by (simp add: strict_mono_def)

        show "(f o ?m) i adds (f o ?m) j" using in_indets_i in_indets_j v_div F_div
          by (simp add: adds_insert_keys)
      qed
    qed
  qed
qed

text \<open>Another version of Dickson's lemma is proved in @{cite Sternagel2012}.\<close>

lemma Dickson_pp:
  fixes V::"'a set"
    and seq::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b::{wellorder,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}"
  assumes "finite V" and "\<forall>k. in_keys V (seq k)"
  shows "\<exists>i j::nat. i < j \<and> seq i adds seq j"
proof -
  from pp_incr_subsequence[OF assms] obtain m::"nat \<Rightarrow> nat" where
    "strict_mono m \<and> (\<forall>i j. i < j \<longrightarrow> (seq o m) i adds (seq o m) j)" ..
  then have m_subseq: "strict_mono m" and m_div: "\<forall>i j. i < j \<longrightarrow> (seq o m) i adds (seq o m) j" by simp_all
  let ?i = "m 0" and ?j = "m 1"
  show "\<exists>i j::nat. i < j \<and> seq i adds seq j"
  proof (rule, rule)
    show "?i < ?j \<and> seq ?i adds seq ?j" using m_subseq m_div by (simp add: strict_mono_def)
  qed
qed

lemma Dickson_pp_finite:
  fixes seq::"nat \<Rightarrow> 'a::finite \<Rightarrow>\<^sub>0 'b::{wellorder,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}"
  shows "\<exists>i j::nat. i < j \<and> seq i adds seq j"
proof -
  have fin: "finite (UNIV::'a set)" by simp
  have indets: "\<forall>k. in_keys UNIV (seq k)"
  proof
    fix k::nat
    show "in_keys UNIV (seq k)" using univ_keys .
  qed
  show ?thesis using Dickson_pp[OF fin indets] .
qed

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class dickson_powerprod}\<close>

instantiation poly_mapping ::
  (finite,"{wellorder,canonically_ordered_monoid_add,ordered_ab_semigroup_monoid_add_imp_le}")
  dickson_powerprod
begin

instance
apply standard
subgoal by (rule Dickson_pp_finite)
done

end

subsection \<open>Term orders\<close>

text \<open>Term orders are certain linear orders on power-products, satisfying additional requirements.
  Further information on term orders can be found, e.\,g., in @{cite Robbiano1985}.\<close>

subsubsection \<open>Lexicographic Term Order\<close>

context wellorder
begin

lemma neq_alt:
  assumes "s \<noteq> (t::'a \<Rightarrow>\<^sub>0'b::zero)"
  obtains x where "lookup s x \<noteq> lookup t x" and "\<And>y. lookup s y \<noteq> lookup t y \<Longrightarrow> x \<le> y"
proof -
  from assms poly_mapping_eqI[of s t] have "\<exists>x. lookup s x \<noteq> lookup t x" by auto
  with exists_least_iff[of "\<lambda>x. lookup s x \<noteq> lookup t x"]
  obtain x where x1: "lookup s x \<noteq> lookup t x" and x2: "\<And>y. y < x \<Longrightarrow> lookup s y = lookup t y"
    by auto
  show ?thesis
  proof
    from x1 show "lookup s x \<noteq> lookup t x" .
  next
    fix y
    assume "lookup s y \<noteq> lookup t y"
    with x2[of y] have "\<not> y < x" by auto
    thus "x \<le> y" by simp
  qed
qed

definition lex::"('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::ordered_comm_monoid_add) \<Rightarrow> bool" where
  "lex s t \<equiv> (\<forall>x. lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y))"

text \<open>Attention! @{term lex} reverses the order of the indeterminates: if @{term x} is smaller than
  @{term y} w.r.t. the order on @{typ 'a}, then the @{emph \<open>power-product\<close>} @{term x} is
  @{emph \<open>greater\<close>} than the @{emph \<open>power-product\<close>} @{term y}.\<close>

lemma lex_alt:
  shows "lex s t = (s = t \<or> (\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y)))" (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (cases "s = t")
    assume "s = t"
    thus ?R by simp
  next
    assume "s \<noteq> t"
    from neq_alt[OF this] obtain x0
      where x0_neq: "lookup s x0 \<noteq> lookup t x0" and x0_min: "\<And>z. lookup s z \<noteq> lookup t z \<Longrightarrow> x0 \<le> z" by auto
    show ?R
    proof (intro disjI2, rule exI[of _ x0], intro conjI)
      from \<open>?L\<close> have "lookup s x0 \<le> lookup t x0 \<or> (\<exists>y. y < x0 \<and> lookup s y \<noteq> lookup t y)" unfolding lex_def ..
      thus "lookup s x0 < lookup t x0"
      proof
        assume "lookup s x0 \<le> lookup t x0"
        from this x0_neq show ?thesis by simp
      next
        assume "\<exists>y. y < x0 \<and> lookup s y \<noteq> lookup t y"
        then obtain y where "y < x0" and y_neq: "lookup s y \<noteq> lookup t y" by auto
        from \<open>y < x0\<close> x0_min[OF y_neq] show ?thesis by simp
      qed
    next
      show "\<forall>y<x0. lookup s y = lookup t y"
      proof (rule, rule)
        fix y
        assume "y < x0"
        hence "\<not> x0 \<le> y" by simp
        from this x0_min[of y] show "lookup s y = lookup t y" by auto
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
    assume "\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y)"
    then obtain y where y_lookup: "lookup s y < lookup t y" and y_min: "\<forall>z<y. lookup s z = lookup t z" by auto
    show ?thesis unfolding lex_def
    proof
      fix x
      show "lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y)"
      proof (cases "lookup s x \<le> lookup t x")
        assume "lookup s x \<le> lookup t x"
        thus ?thesis by simp
      next
        assume s_lookup: "\<not> lookup s x \<le> lookup t x"
        show ?thesis
        proof (intro disjI2, rule exI[of _ y], intro conjI)
          have "\<not> x \<le> y"
          proof
            assume "x \<le> y"
            hence "x < y \<or> y = x" by auto
            thus False
            proof
              assume "x < y"
              from s_lookup y_min[rule_format, OF this] show ?thesis by simp
            next
              assume "y = x"
              from this s_lookup y_lookup show ?thesis
                by (auto simp: preorder_class.less_le_not_le)
            qed
          qed
          thus "y < x" by simp
        next
          from y_lookup show "lookup s y \<noteq> lookup t y" by simp
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
proof (rule poly_mapping_eqI)
  fix x
  from \<open>lex s t\<close> have "s = t \<or> (\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y))"
    unfolding lex_alt .
  thus "lookup s x = lookup t x"
  proof
    assume "s = t"
    thus ?thesis by simp
  next
    assume "\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y)"
    then obtain x0 where lookup_x0: "lookup s x0 < lookup t x0" and x0_min: "\<forall>y<x0. lookup s y = lookup t y" by auto
    from \<open>lex t s\<close> have "t = s \<or> (\<exists>x. lookup t x < lookup s x \<and> (\<forall>y<x. lookup t y = lookup s y))"
      unfolding lex_alt .
    thus ?thesis
    proof
      assume "t = s"
      thus ?thesis by simp
    next
      assume "\<exists>x. lookup t x < lookup s x \<and> (\<forall>y<x. lookup t y = lookup s y)"
      then obtain x1 where lookup_x1: "lookup t x1 < lookup s x1" and x1_min: "\<forall>y<x1. lookup t y = lookup s y"
        by auto
      have "x0 < x1 \<or> x1 < x0 \<or> x1 = x0" using local.antisym_conv3 by auto
      show ?thesis
      proof (rule linorder_cases[of x0 x1])
        assume "x1 < x0"
        from x0_min[rule_format, OF this] lookup_x1 show ?thesis by simp
      next
        assume "x0 = x1"
        from this lookup_x0 lookup_x1 show ?thesis by simp
      next
        assume "x0 < x1"
        from x1_min[rule_format, OF this] lookup_x0 show ?thesis by simp
      qed
    qed
  qed
qed

lemma lex_trans:
  assumes "lex s t" and "lex t u"
  shows "lex s u"
proof -
  from \<open>lex s t\<close> have "s = t \<or> (\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y))"
    unfolding lex_alt .
  thus ?thesis
  proof
    assume "s = t"
    from this \<open>lex t u\<close> show ?thesis by simp
  next
    assume "\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y)"
    then obtain x0 where lookup_x0: "lookup s x0 < lookup t x0" and x0_min: "\<forall>y<x0. lookup s y = lookup t y"
      by auto
    from \<open>lex t u\<close> have "t = u \<or> (\<exists>x. lookup t x < lookup u x \<and> (\<forall>y<x. lookup t y = lookup u y))"
      unfolding lex_alt .
    thus ?thesis
    proof
      assume "t = u"
      from this \<open>lex s t\<close> show ?thesis by simp
    next
      assume "\<exists>x. lookup t x < lookup u x \<and> (\<forall>y<x. lookup t y = lookup u y)"
      then obtain x1 where lookup_x1: "lookup t x1 < lookup u x1" and x1_min: "\<forall>y<x1. lookup t y = lookup u y"
        by auto
      show ?thesis unfolding lex_alt
      proof (intro disjI2)
        show "\<exists>x. lookup s x < lookup u x \<and> (\<forall>y<x. lookup s y = lookup u y)"
        proof (rule linorder_cases[of x0 x1])
          assume "x1 < x0"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from x0_min[rule_format, OF \<open>x1 < x0\<close>] lookup_x1 show "lookup s x1 < lookup u x1" by simp
          next
            show "\<forall>y<x1. lookup s y = lookup u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x1"
              from this \<open>x1 < x0\<close> have "y < x0" by simp
              from x0_min[rule_format, OF this] x1_min[rule_format, OF \<open>y < x1\<close>]
                show "lookup s y = lookup u y" by simp
            qed
          qed
        next
          assume "x0 < x1"
          show ?thesis
          proof (rule exI[of _ x0], intro conjI)
            from x1_min[rule_format, OF \<open>x0 < x1\<close>] lookup_x0 show "lookup s x0 < lookup u x0" by simp
          next
            show "\<forall>y<x0. lookup s y = lookup u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x0"
              from this \<open>x0 < x1\<close> have "y < x1" by simp
              from x0_min[rule_format, OF \<open>y < x0\<close>] x1_min[rule_format, OF this]
                show "lookup s y = lookup u y" by simp
            qed
          qed
        next
          assume "x0 = x1"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from \<open>x0 = x1\<close> lookup_x0 lookup_x1 show "lookup s x1 < lookup u x1" by simp
          next
            show "\<forall>y<x1. lookup s y = lookup u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x1"
              hence "y < x0" using \<open>x0 = x1\<close> by simp
              from x0_min[rule_format, OF this] x1_min[rule_format, OF \<open>y < x1\<close>]
                show "lookup s y = lookup u y" by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma lex_lin: "lex s t \<or> lex t s" for s t::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, linorder}"
proof (intro disjCI)
  assume "\<not> lex t s"
  hence a: "\<forall>x. \<not> (lookup t x < lookup s x) \<or> (\<exists>y<x. lookup t y \<noteq> lookup s y)" unfolding lex_alt by auto
  show "lex s t" unfolding lex_def
  proof
    fix x
    from a have "\<not> (lookup t x < lookup s x) \<or> (\<exists>y<x. lookup t y \<noteq> lookup s y)" ..
    thus "lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y)" by auto
  qed
qed

lemma lex_zero_min: "lex 0 s" for s::"'a \<Rightarrow>\<^sub>0 'b::canonically_ordered_monoid_add"
  by (simp add: local.lex_def)

lemma lex_plus_monotone:
  "lex (s + u) (t + u)" if "lex s t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::ordered_cancel_comm_monoid_add"
unfolding lex_def
proof
  fix x
  from that have "lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y)" unfolding lex_def ..
  thus "lookup (s + u) x \<le> lookup (t + u) x \<or> (\<exists>y<x. lookup (s + u) y \<noteq> lookup (t + u) y)"
  proof
    assume a1: "lookup s x \<le> lookup t x"
    show ?thesis
    proof (intro disjI1)
      from a1 show "lookup (s + u) x \<le> lookup (t + u) x"
        by (auto simp: lookup_add add_right_mono)
    qed
  next
    assume "\<exists>y<x. lookup s y \<noteq> lookup t y"
    then obtain y where "y < x" and a2: "lookup s y \<noteq> lookup t y" by auto
    show ?thesis
    proof (intro disjI2, rule exI[of _ y], intro conjI, fact)
      from a2 show "lookup (s + u) y \<noteq> lookup (t + u) y"
        by (auto simp: lookup_add add_right_mono)
    qed
  qed
qed

end (* wellorder *)

subsubsection \<open>General Degree-Orders\<close>

context linorder
begin

lemma ex_min:
  assumes "finite (A::'a set)" and "A \<noteq> {}"
  shows "\<exists>y\<in>A. (\<forall>z\<in>A. y \<le> z)"
using assms
proof (induct rule: finite_induct)
  assume "{} \<noteq> {}"
  thus "\<exists>y\<in>{}. \<forall>z\<in>{}. y \<le> z" by simp
next
  fix a::'a and A::"'a set"
  assume "a \<notin> A" and IH: "A \<noteq> {} \<Longrightarrow> \<exists>y\<in>A. (\<forall>z\<in>A. y \<le> z)"
  show "\<exists>y\<in>insert a A. (\<forall>z\<in>insert a A. y \<le> z)"
  proof (cases "A = {}")
    case True
    show ?thesis
    proof (rule bexI[of _ a], intro ballI)
      fix z
      assume "z \<in> insert a A"
      from this True have "z = a" by simp
      thus "a \<le> z" by simp
    qed (simp)
  next
    case False
    from IH[OF False] obtain y where "y \<in> A" and y_min: "\<forall>z\<in>A. y \<le> z" by auto
    from linear[of a y] show ?thesis
    proof
      assume "y \<le> a"
      show ?thesis
      proof (rule bexI[of _ y], intro ballI)
        fix z
        assume "z \<in> insert a A"
        hence "z = a \<or> z \<in> A" by simp
        thus "y \<le> z"
        proof
          assume "z = a"
          from this \<open>y \<le> a\<close> show "y \<le> z" by simp
        next
          assume "z \<in> A"
          from y_min[rule_format, OF this] show "y \<le> z" .
        qed
      next
        from \<open>y \<in> A\<close> show "y \<in> insert a A" by simp
      qed
    next
      assume "a \<le> y"
      show ?thesis
      proof (rule bexI[of _ a], intro ballI)
        fix z
        assume "z \<in> insert a A"
        hence "z = a \<or> z \<in> A" by simp
        thus "a \<le> z"
        proof
          assume "z = a"
          from this show "a \<le> z" by simp
        next
          assume "z \<in> A"
          from y_min[rule_format, OF this] \<open>a \<le> y\<close> show "a \<le> z" by simp
        qed
      qed (simp)
    qed
  qed
qed


definition deg::"('a \<Rightarrow>\<^sub>0 'b::comm_monoid_add) \<Rightarrow> 'b" where "deg s \<equiv> \<Sum>x\<in>(keys s). lookup s x"

lemma deg_zero[simp]: "deg 0 = 0"
  by (auto simp: deg_def)

lemma deg_eq_0_iff[simp]: "deg s = 0 \<longleftrightarrow> s = 0"
  for s::"'a \<Rightarrow>\<^sub>0 'b::canonically_ordered_monoid_add"
  by (auto simp: deg_def intro!: poly_mapping_eqI)

lemma deg_superset:
  fixes A::"'a set"
  assumes "keys s \<subseteq> A" and "finite A"
  shows "deg s = (\<Sum>x\<in>A. lookup s x)"
  unfolding deg_def
  by (rule sum.mono_neutral_cong_left) (auto simp: assms)

lemma keys_plus[simp]: "keys (s + t) = keys s \<union> keys t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::canonically_ordered_monoid_add"
  by transfer auto

lemma deg_plus: "deg (s + t) = deg s + deg t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::canonically_ordered_monoid_add"
proof -
  have "deg (s + t) = (\<Sum>x\<in>(keys (s + t)). lookup s x + lookup t x)"
    unfolding deg_def by (auto simp: lookup_add)
  also have "\<dots> = (\<Sum>x\<in>(keys (s + t)). lookup s x) + (\<Sum>x\<in>(keys (s + t)). lookup t x)"
    by (rule sum.distrib)
  also have "(\<Sum>x\<in>(keys (s + t)). lookup s x) = deg s"
    unfolding deg_def
    by (rule sum.mono_neutral_cong_right) (auto simp:)
  also have "(\<Sum>x\<in>(keys (s + t)). lookup t x) = deg t"
    unfolding deg_def
    by (rule sum.mono_neutral_cong_right) (auto simp:)
  finally show ?thesis .
qed

definition dord::"(('a \<Rightarrow>\<^sub>0 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "dord ord s t \<equiv> (let d1 = deg s; d2 = deg t in (d1 < d2 \<or> (d1 = d2 \<and> ord s t)))"

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
    thus ?thesis using ts by auto
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
  "dord ord s t \<or> dord ord t s"
  if "ord s t \<or> ord t s"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, linorder}"
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
      from \<open>\<not> ord s t\<close> \<open>\<not> ord t s\<close> that show ?thesis by simp
    next
      case False
      from this \<open>deg s \<le> deg t\<close> show ?thesis by simp
    qed
  qed
qed

lemma dord_zero_min: "dord ord 0 s"
  if ord_refl: "\<And>t. ord t t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::{canonically_ordered_monoid_add, linorder}"
  unfolding dord_def Let_def deg_zero
proof (rule disjCI)
  assume "\<not> (0 = deg s \<and> ord 0 s)"
  hence dis: "deg s \<noteq> 0 \<or> \<not> ord 0 s" by simp
  show "0 < deg s"
  proof (cases "deg s = 0")
    case True
    hence "s = 0" using deg_eq_0_iff by auto
    hence "ord 0 s" using ord_refl by simp
    with True dis show ?thesis by simp
  next
    case False
    thus ?thesis
      by (auto simp: zero_less_iff_neq_zero)
  qed
qed

lemma dord_plus_monotone:
  fixes s t u ::"'a \<Rightarrow>\<^sub>0 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes "dord ord s t" and ord_monotone: "ord s t \<Longrightarrow> ord (s + u) (t + u)"
  shows "dord ord (s + u) (t + u)"
proof -
  from \<open>dord ord s t\<close> have "deg s < deg t \<or> (deg s = deg t \<and> ord s t)" unfolding dord_def Let_def .
  thus ?thesis
  proof
    assume "deg s < deg t"
    hence "deg (s + u) < deg (t + u)" by (auto simp: deg_plus)
    thus ?thesis unfolding dord_def Let_def by simp
  next
    assume "deg s = deg t \<and> ord s t"
    hence "deg s = deg t" and "ord s t" by simp_all
    from \<open>deg s = deg t\<close> have "deg (s + u) = deg (t + u)"
      by (auto simp: deg_plus)
    from this ord_monotone[OF \<open>ord s t\<close>] show ?thesis unfolding dord_def Let_def by simp
  qed
qed

end (* linorder *)

subsubsection \<open>Degree-Lexicographic Term Order\<close>

context wellorder
begin

definition dlex::"('a \<Rightarrow>\<^sub>0 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool" where "dlex \<equiv> dord lex"

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

lemma dlex_lin: "dlex s t \<or> dlex t s"
  for s t::"('a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add,linorder})"
unfolding dlex_def by (rule dord_lin, rule lex_lin)

lemma dlex_zero_min: "dlex 0 s"
  for s t::"('a \<Rightarrow>\<^sub>0 'b::{canonically_ordered_monoid_add,linorder})"
  unfolding dlex_def by (rule dord_zero_min, rule lex_refl)

lemma dlex_plus_monotone:
  fixes s t::"'a \<Rightarrow>\<^sub>0 'b::{canonically_ordered_monoid_add, ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add}"
  assumes "dlex s t"
  shows "dlex (s + u) (t + u)"
  using assms unfolding dlex_def
  by (rule dord_plus_monotone[of lex s t, OF _ lex_plus_monotone[of s]], simp)

end (* wellorder *)

text\<open>Every finite linear ordering is also a well-ordering. This fact is particularly useful when
  working with fixed finite sets of indeterminates.\<close>
class finite_linorder = finite + linorder
begin

subclass wellorder
proof
  fix P::"'a \<Rightarrow> bool" and a
  assume hyp: "\<And>x. (\<And>y. (y < x) \<Longrightarrow> P y) \<Longrightarrow> P x"
  show "P a"
  proof (rule ccontr)
    assume "\<not> P a"
    have "finite {x. \<not> P x}" (is "finite ?A") by simp
    from \<open>\<not> P a\<close> have "a \<in> ?A" by simp
    hence "?A \<noteq> {}" by auto
    from ex_min[OF \<open>finite ?A\<close> this] obtain b where "b \<in> ?A" and b_min: "\<forall>y\<in>?A. b \<le> y" by auto
    from \<open>b \<in> ?A\<close> have "\<not> P b" by simp
    with hyp[of b] obtain y where "y < b" and "\<not> P y" by auto
    from \<open>\<not> P y\<close> have "y \<in> ?A" by simp
    with b_min have "b \<le> y" by simp
    with \<open>y < b\<close> show False by simp
  qed
qed

end

end
