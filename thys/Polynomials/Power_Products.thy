(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Abstract Power-Products\<close>

theory Power_Products
  imports Complex_Main
  "HOL-Library.Function_Algebras"
  "More_MPoly_Type"
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

subsection \<open>'Divisibility' on Additive Structures\<close>

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

lemma adds_plus_right [simp]: "a adds c \<Longrightarrow> a adds (b + c)"
  by (auto intro!: add.left_commute addsI elim!: addsE)

lemma adds_plus_left [simp]: "a adds b \<Longrightarrow> a adds (b + c)"
  using adds_plus_right [of a b c] by (simp add: ac_simps)

lemma adds_triv_right [simp]: "a adds b + a"
  by (rule adds_plus_right) (rule adds_refl)

lemma adds_triv_left [simp]: "a adds a + b"
  by (rule adds_plus_left) (rule adds_refl)

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

lemma plus_adds_left: "a + b adds c \<Longrightarrow> a adds c"
  by (simp add: adds_def add.assoc) blast

lemma plus_adds_right: "a + b adds c \<Longrightarrow> b adds c"
  using plus_adds_left [of b a c] by (simp add: ac_simps)

end

class ninv_comm_monoid_add = comm_monoid_add +
  assumes plus_eq_zero: "s + t = 0 \<Longrightarrow> s = 0"
begin

lemma plus_eq_zero_2: "t = 0" if "s + t = 0"
  using that
  by (simp only: add_commute[of s t] plus_eq_zero)

lemma adds_zero: "s adds 0 \<longleftrightarrow> (s = 0)"
proof
  assume "s adds 0"
  from this obtain k where "0 = s + k" unfolding adds_def ..
  from this plus_eq_zero[of s k] show "s = 0"
    by blast
next
  assume "s = 0"
  thus "s adds 0" by simp
qed

end

context canonically_ordered_monoid_add
begin
subclass ninv_comm_monoid_add by (standard, simp)
end

class comm_powerprod = cancel_comm_monoid_add
begin

lemma adds_canc: "s + u adds t + u \<longleftrightarrow> s adds t" for s t u::'a
  unfolding adds_def
  apply auto
   apply (metis local.add.left_commute local.add_diff_cancel_left' local.add_diff_cancel_right')
  using add_assoc add_commute by auto

lemma adds_canc_2: "u + s adds u + t \<longleftrightarrow> s adds t"
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
  from assms have "(s + t) adds ((u - t) + t)" using adds_minus local.plus_adds_right by presburger
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
    from plus_adds_right[OF a1] show "t adds u" .
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
  (not necessarily unique) least common sums (inspired from least common multiplies).
  Note that if the components of indeterminates are arbitrary integers (as for instance in Laurent
  polynomials), then no unique lcss exist.\<close>
class lcs_powerprod = comm_powerprod +
  fixes lcs::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes adds_lcs: "s adds (lcs s t)"
  assumes lcs_adds: "s adds u \<Longrightarrow> t adds u \<Longrightarrow> (lcs s t) adds u"
  assumes lcs_comm: "lcs s t = lcs t s"
begin

lemma adds_lcs_2: "t adds (lcs s t)"
  by (simp only: lcs_comm[of s t], rule adds_lcs)

lemma lcs_adds_plus: "lcs s t adds s + t" by (simp add: lcs_adds)

text \<open>"gcs" stands for "greatest common summand".\<close>
definition gcs :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where "gcs s t = (s + t) - (lcs s t)"

lemma gcs_plus_lcs: "(gcs s t) + (lcs s t) = s + t"
  unfolding gcs_def by (rule adds_minus, fact lcs_adds_plus)

lemma gcs_adds: "(gcs s t) adds s"
proof -
  have "t adds (lcs s t)" (is "t adds ?l") unfolding lcs_comm[of s t] by (fact adds_lcs)
  then obtain u where eq1: "?l = t + u" unfolding adds_def ..
  from lcs_adds_plus[of s t] obtain v where eq2: "s + t = ?l + v" unfolding adds_def ..
  hence "t + s = t + (u + v)" unfolding eq1 by (simp add: ac_simps)
  hence s: "s = u + v" unfolding add_left_cancel .
  show ?thesis unfolding eq2 gcs_def unfolding s by simp
qed

lemma gcs_comm: "gcs s t = gcs t s" unfolding gcs_def by (simp add: lcs_comm ac_simps)

lemma gcs_adds_2: "(gcs s t) adds t"
  by (simp only: gcs_comm[of s t], rule gcs_adds)

end

class ulcs_powerprod = lcs_powerprod + ninv_comm_monoid_add
begin

lemma adds_antisym:
  assumes "s adds t" "t adds s"
  shows "s = t"
proof -
  from \<open>s adds t\<close> obtain u where u_def: "t = s + u" unfolding adds_def ..
  from \<open>t adds s\<close> obtain v where v_def: "s = t + v" unfolding adds_def ..
  from u_def v_def have "s = (s + u) + v" by (simp add: ac_simps)
  hence "s + 0 = s + (u + v)" by (simp add: ac_simps)
  hence "u + v = 0" by simp
  hence "u = 0" using plus_eq_zero[of u v] by simp
  thus ?thesis using u_def by simp
qed

lemma lcs_unique:
  assumes "s adds l" and "t adds l" and *: "\<And>u. s adds u \<Longrightarrow> t adds u \<Longrightarrow> l adds u"
  shows "l = lcs s t"
  by (rule adds_antisym, rule *, fact adds_lcs, fact adds_lcs_2, rule lcs_adds, fact+)

lemma lcs_plus_left: "lcs (u + s) (u + t) = u + lcs s t" 
proof (rule lcs_unique[symmetric], simp_all only: adds_canc_2, fact adds_lcs, fact adds_lcs_2,
    simp add: add.commute[of u] plus_adds)
  fix v
  assume "u adds v \<and> s adds v - u"
  hence "s adds v - u" ..
  assume "t adds v - u"
  with \<open>s adds v - u\<close> show "lcs s t adds v - u" by (rule lcs_adds)
qed

lemma lcs_plus_right: "lcs (s + u) (t + u) = (lcs s t) + u"
  using lcs_plus_left[of u s t] by (simp add: ac_simps)

lemma adds_gcs:
  assumes "u adds s" and "u adds t"
  shows "u adds (gcs s t)"
proof -
  from assms have "s + u adds s + t" and "t + u adds t + s"
    by (simp_all add: plus_adds_mono)
  hence "lcs (s + u) (t + u) adds s + t"
    by (auto intro: lcs_adds simp add: ac_simps)
  hence "u + (lcs s t) adds s + t" unfolding lcs_plus_right by (simp add: ac_simps)
  hence "u adds (s + t) - (lcs s t)" unfolding plus_adds ..
  thus ?thesis unfolding gcs_def .
qed

lemma gcs_unique:
  assumes "g adds s" and "g adds t" and *: "\<And>u. u adds s \<Longrightarrow> u adds t \<Longrightarrow> u adds g"
  shows "g = gcs s t"
  by (rule adds_antisym, rule adds_gcs, fact, fact, rule *, fact gcs_adds, fact gcs_adds_2)

lemma gcs_plus_left: "gcs (u + s) (u + t) = u + gcs s t"
proof -
  have "u + s + (u + t) - (u + lcs s t) = u + s + (u + t) - u - lcs s t" by (simp only: diff_diff_add)
  also have "... = u + s + t + (u - u) - lcs s t" by (simp add: add.left_commute)
  also have "... = u + s + t - lcs s t" by simp
  also have "... =  u + (s + t - lcs s t)"
    using add_assoc add_commute local.lcs_adds_plus local.minus_plus by auto
  finally show ?thesis unfolding gcs_def lcs_plus_left .
qed

lemma gcs_plus_right: "gcs (s + u) (t + u) = (gcs s t) + u"
  using gcs_plus_left[of u s t] by (simp add: ac_simps)

lemma lcs_same [simp]: "lcs s s = s"
proof -
  have "lcs s s adds s" by (rule lcs_adds, simp_all)
  moreover have "s adds lcs s s" by (rule adds_lcs)
  ultimately show ?thesis by (rule adds_antisym)
qed

lemma gcs_same [simp]: "gcs s s = s"
proof -
  have "gcs s s adds s" by (rule gcs_adds)
  moreover have "s adds gcs s s" by (rule adds_gcs, simp_all)
  ultimately show ?thesis by (rule adds_antisym)
qed

end

text \<open>Instances of class \<open>dickson_powerprod\<close> are types of commutative power-products satisfying the
  Dickson property.\<close>
class dickson_powerprod = ulcs_powerprod +
  assumes dickson: "\<And>seq::nat \<Rightarrow> 'a. (\<exists>i j::nat. i < j \<and> seq i adds seq j)"

subsection \<open>Additive Linear Orderings\<close>
  
lemma group_eq_aux: "a + (b - a) = (b::'a::ab_group_add)"
proof -
  have "a + (b - a) = b - a + a" by simp
  also have "... = b" by simp
  finally show ?thesis .
qed

class semi_canonically_ordered_monoid_add = ordered_comm_monoid_add +
  assumes le_imp_add: "a \<le> b \<Longrightarrow> (\<exists>c. b = a + c)"

context canonically_ordered_monoid_add
begin
subclass semi_canonically_ordered_monoid_add
  by (standard, simp only: le_iff_add)
end

class add_linorder_group = ordered_ab_semigroup_add_imp_le + ab_group_add + linorder

class add_linorder = ordered_ab_semigroup_add_imp_le + cancel_comm_monoid_add + semi_canonically_ordered_monoid_add + linorder
begin

subclass ordered_comm_monoid_add ..

subclass ordered_cancel_comm_monoid_add ..

lemma le_imp_inv:
  assumes "a \<le> b"
  shows "b = a + (b - a)"
  using le_imp_add[OF assms] by auto

lemma max_eq_sum:
  obtains y where "max a b = a + y"
  unfolding max_def
proof (cases "a \<le> b")
  case True
  hence "b = a + (b - a)" by (rule le_imp_inv)
  then obtain c where eq: "b = a + c" ..
  show ?thesis
  proof
    from True show "max a b = a + c" unfolding max_def eq by simp
  qed
next
  case False
  show ?thesis
  proof
    from False show "max a b = a + 0" unfolding max_def by simp
  qed
qed
  
lemma min_plus_max:
  shows "(min a b) + (max a b) = a + b"
proof (cases "a \<le> b")
  case True
  thus ?thesis unfolding min_def max_def by simp
next
  case False
  thus ?thesis unfolding min_def max_def by (simp add: ac_simps)
qed

end (* add_linorder *)

class add_linorder_min = add_linorder +
  assumes zero_min: "0 \<le> x"
begin

subclass ninv_comm_monoid_add
proof
  fix x y
  assume *: "x + y = 0"
  show "x = 0"
  proof -
    from zero_min[of x] have "0 = x \<or> x > 0" by auto
    thus ?thesis
    proof
      assume "x > 0"
      have "0 \<le> y" by (fact zero_min)
      also have "... = 0 + y" by simp
      also from \<open>x > 0\<close> have "... < x + y" by (rule add_strict_right_mono)
      finally have "0 < x + y" .
      hence "x + y \<noteq> 0" by simp
      from this * show ?thesis ..
    qed simp
  qed
qed
  
lemma leq_add_right:
  shows "x \<le> x + y"
  using add_left_mono[OF zero_min[of y], of x] by simp

lemma leq_add_left:
  shows "x \<le> y + x"
  using add_right_mono[OF zero_min[of y], of x] by simp

subclass canonically_ordered_monoid_add
  by (standard, rule, elim le_imp_add, elim exE, simp add: leq_add_right)

end (* add_linorder_min *)
  
class add_wellorder = add_linorder_min + wellorder
  
instantiation nat :: add_linorder
begin

instance by (standard, simp)

end (* add_linorder *)
  
instantiation nat :: add_linorder_min
begin
instance by (standard, simp)
end
  
instantiation nat :: add_wellorder
begin
instance ..
end
  
context add_linorder_group
begin
  
subclass add_linorder
proof (standard, intro exI)
  fix a b
  show "b = a + (b - a)" using add_commute local.diff_add_cancel by auto
qed

end (* add_linorder_group *)
  
instantiation int :: add_linorder_group
begin
instance ..
end

instantiation rat :: add_linorder_group
begin
instance ..
end

instantiation real :: add_linorder_group
begin
instance ..
end

subsection \<open>Ordered Power-Products\<close>

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
  assumes zero_min: "0 \<preceq> t"
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
  thus ?thesis using plus_monotone[OF zero_min[of k], of s] by (simp add: ac_simps)
qed

lemma ord_canc_left:
  assumes "u + s \<preceq> u + t"
  shows "s \<preceq> t"
  using assms unfolding add.commute[of u] by (rule ord_canc)

lemma ord_strict_canc:
  assumes "s + u \<prec> t + u"
  shows "s \<prec> t"
  using assms ord_canc[of s u t] add_right_cancel[of s u t]
    ordered_powerprod_lin.le_imp_less_or_eq ordered_powerprod_lin.order.strict_implies_order by blast

lemma ord_strict_canc_left:
  assumes "u + s \<prec> u + t"
  shows "s \<prec> t"
  using assms unfolding add.commute[of u] by (rule ord_strict_canc)

lemma plus_monotone_left:
  assumes "s \<preceq> t"
  shows "u + s \<preceq> u + t"
  using assms
  by (simp add: add.commute, rule plus_monotone)

lemma plus_monotone_strict:
  assumes "s \<prec> t"
  shows "s + u \<prec> t + u"
  using assms
  by (simp add: ordered_powerprod_lin.order.strict_iff_order plus_monotone)

lemma plus_monotone_strict_left:
  assumes "s \<prec> t"
  shows "u + s \<prec> u + t"
  using assms
  by (simp add: ordered_powerprod_lin.order.strict_iff_order plus_monotone_left)

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

subsection \<open>Functions as Power-Products\<close>

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

lemma finite_neq_0_inv:
  assumes fin_A: "finite {x. h x (f x) (g x) \<noteq> 0}" and fin_B: "finite {x. f x \<noteq> 0}" and "\<And>x y. h x 0 y = y"
  shows "finite {x. g x \<noteq> 0}"
proof -
  from fin_A and fin_B have "finite ({x. h x (f x) (g x) \<noteq> 0} \<union> {x. f x \<noteq> 0})" by (intro finite_UnI)
  hence finite_union: "finite {x. (h x (f x) (g x) \<noteq> 0) \<or> f x \<noteq> 0}" by (simp only: Collect_disj_eq)
  have "{x. g x \<noteq> 0} \<subseteq> {x. (h x (f x) (g x) \<noteq> 0) \<or> f x \<noteq> 0}"
    by (intro Collect_mono, rule, rule disjCI, simp add: assms(3))
  from this finite_union show "finite {x. g x \<noteq> 0}" by (rule finite_subset)
qed

lemma finite_neq_0_inv':
  assumes inf_A: "finite {x. h (f x) (g x) \<noteq> 0}" and fin_B: "finite {x. f x \<noteq> 0}" and "\<And>x. h 0 x = x"
  shows "finite {x. g x \<noteq> 0}"
  using assms by (rule finite_neq_0_inv)

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class comm_powerprod}\<close>

instance "fun" :: (type, cancel_comm_monoid_add) comm_powerprod
  by standard

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class ninv_comm_monoid_add}\<close>

instance "fun" :: (type, ninv_comm_monoid_add) ninv_comm_monoid_add
  by (standard, simp only: plus_fun_def zero_fun_def fun_eq_iff, intro allI, rule plus_eq_zero, auto)

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class lcs_powerprod}\<close>

instantiation "fun" :: (type, add_linorder) lcs_powerprod
begin

definition lcs_fun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where "lcs f g = (\<lambda>x. max (f x) (g x))"

lemma adds_funI:
  assumes "s \<le> t"
  shows "s adds (t::'a \<Rightarrow> 'b)"
proof (rule addsI, rule)
  fix x
  from assms have "s x \<le> t x" unfolding le_fun_def ..
  hence "t x = s x + (t x - s x)" by (rule le_imp_inv)
  thus "t x = (s + (t - s)) x" by simp
qed

lemma adds_fun_iff: "f adds (g::'a \<Rightarrow> 'b) \<longleftrightarrow> (\<forall>x. f x adds g x)"
  unfolding adds_def plus_fun_def by metis

lemma adds_fun_iff': "f adds (g::'a \<Rightarrow> 'b) \<longleftrightarrow> (\<forall>x. \<exists>y. g x = f x + y)"
  unfolding adds_fun_iff unfolding adds_def plus_fun_def ..

lemma adds_lcs_fun:
  shows "s adds (lcs s (t::'a \<Rightarrow> 'b))"
  by (rule adds_funI, simp only: le_fun_def lcs_fun_def, auto simp: max_def)

lemma lcs_comm_fun:  "lcs s t = lcs t (s::'a \<Rightarrow> 'b)"
  unfolding lcs_fun_def
  by (auto simp: max_def intro!: ext)

lemma lcs_adds_fun:
  assumes "s adds u" and "t adds (u::'a \<Rightarrow> 'b)"
  shows "(lcs s t) adds u"
  using assms unfolding lcs_fun_def adds_fun_iff'
proof -
  assume a1: "\<forall>x. \<exists>y. u x = s x + y" and a2: "\<forall>x. \<exists>y. u x = t x + y"
  show "\<forall>x. \<exists>y. u x = max (s x) (t x) + y"
  proof
    fix x
    from a1 have b1: "\<exists>y. u x = s x + y" ..
    from a2 have b2: "\<exists>y. u x = t x + y" ..
    show "\<exists>y. u x = max (s x) (t x) + y" unfolding max_def
      by (split if_split, intro conjI impI, rule b2, rule b1)
  qed
qed

instance
  apply standard
  subgoal by (rule adds_lcs_fun)
  subgoal by (rule lcs_adds_fun)
  subgoal by (rule lcs_comm_fun)
  done

end

lemma leq_lcs_fun_1: "s \<le> (lcs s (t::'a \<Rightarrow> 'b::add_linorder))"
  by (simp add: lcs_fun_def le_fun_def)

lemma leq_lcs_fun_2: "t \<le> (lcs s (t::'a \<Rightarrow> 'b::add_linorder))"
  by (simp add: lcs_fun_def le_fun_def)

lemma lcs_leq_fun:
  assumes "s \<le> u" and "t \<le> (u::'a \<Rightarrow> 'b::add_linorder)"
  shows "(lcs s t) \<le> u"
  using assms by (simp add: lcs_fun_def le_fun_def)

lemma adds_fun: "s adds t \<longleftrightarrow> s \<le> t"
  for s t::"'a \<Rightarrow> 'b::add_linorder_min"
proof
  assume "s adds t"
  from this obtain k where "t = s + k" ..
  show "s \<le> t" unfolding \<open>t = s + k\<close> le_fun_def plus_fun_def le_iff_add by (simp add: leq_add_right)
qed (rule adds_funI)

lemma gcs_fun: "gcs s (t::'a \<Rightarrow> ('b::add_linorder)) = (\<lambda>x. min (s x) (t x))"
proof -
  show ?thesis unfolding gcs_def lcs_fun_def fun_diff_def
  proof (simp, rule)
    fix x
    have eq: "s x + t x = max (s x) (t x) + min (s x) (t x)" by (metis add.commute min_def max_def)
    thus "s x + t x - max (s x) (t x) = min (s x) (t x)" by simp
  qed
qed

lemma gcs_leq_fun_1: "(gcs s (t::'a \<Rightarrow> 'b::add_linorder)) \<le> s"
  by (simp add: gcs_fun le_fun_def)

lemma gcs_leq_fun_2: "(gcs s (t::'a \<Rightarrow> 'b::add_linorder)) \<le> t"
  by (simp add: gcs_fun le_fun_def)

lemma leq_gcs_fun:
  assumes "u \<le> s" and "u \<le> (t::'a \<Rightarrow> 'b::add_linorder)"
  shows "u \<le> (gcs s t)"
  using assms by (simp add: gcs_fun le_fun_def)

subsubsection \<open>@{typ "'a \<Rightarrow> 'b"} belongs to class @{class ulcs_powerprod}\<close>

instance "fun" :: (type, add_linorder_min) ulcs_powerprod ..

subsubsection \<open>Power-products in a given set of indeterminates\<close>

definition supp_fun::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where "supp_fun f = {x. f x \<noteq> 0}"
definition sub_supp::"'a set \<Rightarrow> ('a \<Rightarrow> 'b::zero) \<Rightarrow> bool" where "sub_supp V s \<longleftrightarrow> supp_fun s \<subseteq> V"

text \<open>@{term supp_fun} for general functions is like @{term keys} for @{type poly_mapping},
  but does not need to be finite.\<close>

lemma keys_eq_supp: "keys s = supp_fun (lookup s)"
  unfolding supp_fun_def by (transfer, rule)

definition truncate_fun::"'a set \<Rightarrow> ('a \<Rightarrow> 'b::zero) \<Rightarrow> ('a \<Rightarrow> 'b::zero)"
  where "truncate_fun V f = (\<lambda>x. (if x \<in> V then f x else 0))"

lemma fun_eq_zeroI:
  assumes "\<And>x. x \<in> supp_fun f \<Longrightarrow> f x = 0"
  shows "f = 0"
proof (rule, simp)
  fix x
  show "f x = 0"
  proof (cases "x \<in> supp_fun f")
    case True
    then show ?thesis by (rule assms)
  next
    case False
    then show ?thesis by (simp add: supp_fun_def)
  qed
qed

lemma sub_supp_univ: "sub_supp (UNIV::'a set) f"
by (simp add: sub_supp_def)

lemma sub_supp_empty: "sub_supp {} s = (s = 0)"
  unfolding sub_supp_def supp_fun_def by auto

lemma sub_supp_supp: "sub_supp (supp_fun s) s"
  by (simp add: sub_supp_def)

lemma sub_supp_truncate: "sub_supp V (truncate_fun V s)"
  unfolding sub_supp_def truncate_fun_def supp_fun_def by auto

lemma sub_supp_union_add:
  fixes V U::"'a set" and s t::"'a \<Rightarrow> 'b::monoid_add"
  assumes "sub_supp V s" and "sub_supp U t"
  shows "sub_supp (V \<union> U) (s + t)"
  using assms unfolding sub_supp_def supp_fun_def by force

corollary supp_add_subset: "supp_fun (s + t) \<subseteq> supp_fun s \<union> supp_fun (t::'a \<Rightarrow> 'b::monoid_add)"
proof -
  have "sub_supp (supp_fun s) s" and "sub_supp (supp_fun t) t" by (rule sub_supp_supp)+
  hence "sub_supp (supp_fun s \<union> supp_fun t) (s + t)" by (rule sub_supp_union_add)
  thus ?thesis by (simp only: sub_supp_def)
qed

lemma adds_insert_supp:
  fixes s t::"'a \<Rightarrow> 'b::add_linorder"
  assumes "sub_supp (insert v V) s" and "sub_supp (insert v V) t"
  shows "s adds t = (truncate_fun V s adds truncate_fun V t \<and> s v adds t v)"
  using assms unfolding sub_supp_def supp_fun_def truncate_fun_def adds_fun_iff
  by (auto; force)

subsubsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

text \<open>The following lemma was kindly provided by Manuel Eberl.\<close>
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

lemma fun_incr_subsequence:
  fixes V::"'a set" and f::"nat \<Rightarrow> 'a \<Rightarrow> 'b::add_wellorder"
  assumes "finite V" and sub_supp: "\<And>k. sub_supp V (f k)"
  shows "\<exists>m::nat \<Rightarrow> nat. (strict_mono m) \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i adds (f o m) j)"
  using assms
proof (induct V arbitrary: f)
  case empty
  hence all_zero: "\<And>k. f k = 0" by (simp only: sub_supp_empty)
  show ?case
  proof (intro exI conjI)
    show "strict_mono id" by (simp add: strict_mono_def)
  next
    from all_zero show "\<forall>i j. i < j \<longrightarrow> (f \<circ> id) i adds (f \<circ> id) j" by simp
  qed
next
  case ind: (insert v V)

  (*Construction of first mapping*)
  have IH_prem: "(\<And>k. sub_supp V ((truncate_fun V o f) k))" by (simp add: sub_supp_truncate)
  hence "\<exists>m. strict_mono m \<and> (\<forall>i j::nat. i < j \<longrightarrow> (truncate_fun V \<circ> f \<circ> m) i adds (truncate_fun V \<circ> f \<circ> m) j)"
    by (rule ind.hyps(3))
  then obtain m1 where m1_strict_mono: "strict_mono m1" and
    m1_div: "\<forall>i j::nat. i < j \<longrightarrow> (truncate_fun V \<circ> f \<circ> m1) i adds (truncate_fun V \<circ> f \<circ> m1) j" by auto

  (*Construction of second mapping*)
  show ?case
  proof (rule nat_incr_subsequence)
    fix m2::"nat \<Rightarrow> nat"
    let ?m = "(m1 o m2)"
    assume m2_strict_mono: "strict_mono m2" and "incseq ((\<lambda>x. x v) o f \<circ> m1 \<circ> m2)"
    hence "\<forall>i j. i < j \<longrightarrow> ((\<lambda>x. x v) o f \<circ> ?m) i \<le> ((\<lambda>x. x v) o f \<circ> ?m) j"
      by (simp add: incseq_def)
    hence m2_adds: "\<forall>i j. i < j \<longrightarrow> ((\<lambda>x. x v) o f \<circ> ?m) i adds ((\<lambda>x. x v) o f \<circ> ?m) j"
      using addsI le_imp_inv by fastforce
        
    show "\<exists>m. strict_mono m \<and> (\<forall>i j::nat. i < j \<longrightarrow> (f o m) i adds (f o m) j)"
    proof (intro exI conjI allI impI)
      show "strict_mono ?m" using m1_strict_mono m2_strict_mono by (intro strict_mono_o)
    next
      fix i j::nat
      assume "i < j"
        
      (*i-th and j-th element are in (insert v V)*)
      from ind(4) have sub_supp_i: "sub_supp (insert v V) ((f o ?m) i)"
        and sub_supp_j: "sub_supp (insert v V) ((f o ?m) j)" by simp_all
          
      (*v-component of i-th element is leq v-component of j-th element*)
      from m2_adds have m2_adds_i_j: "i < j \<longrightarrow> ((\<lambda>x. x v) \<circ> f \<circ> ?m) i adds ((\<lambda>x. x v) \<circ> f \<circ> ?m) j"
        by simp
      hence v_adds: "((f o ?m) i) v adds ((f o ?m) j) v" using \<open>i < j\<close> by simp
          
      (*F-components of i-th element divide F-components of j-th element*)
      from m1_div have m1_div_i_j: "m2 i < m2 j \<longrightarrow> ((truncate_fun V) o f o ?m) i adds ((truncate_fun V) o f o ?m) j"
        by simp
      hence V_adds: "truncate_fun V ((f o ?m) i) adds truncate_fun V ((f o ?m) j)"
        using \<open>i < j\<close> m2_strict_mono by (simp add: strict_mono_def)
      
      show "(f \<circ> ?m) i adds (f \<circ> ?m) j"
        by (simp only: adds_insert_supp[OF sub_supp_i sub_supp_j], rule, fact V_adds, fact v_adds)
    qed
  qed
qed

text \<open>Another version of Dickson's lemma is proved in @{cite Sternagel2012}.\<close>

lemma Dickson_fun:
  fixes seq::"nat \<Rightarrow> 'a \<Rightarrow> 'b::add_wellorder"
  assumes "finite V" and "\<And>k. sub_supp V (seq k)"
  shows "\<exists>i j::nat. i < j \<and> seq i adds seq j"
proof -
  from fun_incr_subsequence[OF assms] obtain m::"nat \<Rightarrow> nat" where
    "strict_mono m \<and> (\<forall>i j. i < j \<longrightarrow> (seq o m) i adds (seq o m) j)" ..
  then have m_subseq: "strict_mono m" and m_div: "\<forall>i j. i < j \<longrightarrow> (seq o m) i adds (seq o m) j" by simp_all
  let ?i = "m 0" and ?j = "m 1"
  show "\<exists>i j::nat. i < j \<and> seq i adds seq j"
  proof (rule, rule)
    show "?i < ?j \<and> seq ?i adds seq ?j" using m_subseq m_div by (simp add: strict_mono_def)
  qed
qed

instance "fun" :: (finite, add_wellorder) dickson_powerprod
proof
  fix seq::"nat \<Rightarrow> 'a \<Rightarrow> 'b"
  have "finite (UNIV::'a set)" by simp
  moreover have "\<And>k. sub_supp UNIV (seq k)" by (rule sub_supp_univ)
  ultimately show "\<exists>i j. i < j \<and> seq i adds seq j" by (rule Dickson_fun)
qed

subsubsection \<open>Lexicographic Term Order\<close>

text \<open>Term orders are certain linear orders on power-products, satisfying additional requirements.
  Further information on term orders can be found, e.\,g., in @{cite Robbiano1985}.\<close>

context wellorder
begin

lemma neq_fun_alt:
  assumes "s \<noteq> (t::'a \<Rightarrow> 'b)"
  obtains x where "s x \<noteq> t x" and "\<And>y. s y \<noteq> t y \<Longrightarrow> x \<le> y"
proof -
  from assms ext[of s t] have "\<exists>x. s x \<noteq> t x" by auto
  with exists_least_iff[of "\<lambda>x. s x \<noteq> t x"]
  obtain x where x1: "s x \<noteq> t x" and x2: "\<And>y. y < x \<Longrightarrow> s y = t y"
    by auto
  show ?thesis
  proof
    from x1 show "s x \<noteq> t x" .
  next
    fix y
    assume "s y \<noteq> t y"
    with x2[of y] have "\<not> y < x" by auto
    thus "x \<le> y" by simp
  qed
qed

definition lex_fun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "lex_fun s t \<equiv> (\<forall>x. s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y))"

text \<open>Attention! @{term lex_fun} reverses the order of the indeterminates: if @{term x} is smaller than
  @{term y} w.r.t. the order on @{typ 'a}, then the @{emph \<open>power-product\<close>} @{term x} is
  @{emph \<open>greater\<close>} than the @{emph \<open>power-product\<close>} @{term y}.\<close>

lemma lex_fun_alt:
  shows "lex_fun s t = (s = t \<or> (\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)))" (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof (cases "s = t")
    assume "s = t"
    thus ?R by simp
  next
    assume "s \<noteq> t"
    from neq_fun_alt[OF this] obtain x0
      where x0_neq: "s x0 \<noteq> t x0" and x0_min: "\<And>z. s z \<noteq> t z \<Longrightarrow> x0 \<le> z" by auto
    show ?R
    proof (intro disjI2, rule exI[of _ x0], intro conjI)
      from \<open>?L\<close> have "s x0 \<le> t x0 \<or> (\<exists>y. y < x0 \<and> s y \<noteq> t y)" unfolding lex_fun_def ..
      thus "s x0 < t x0"
      proof
        assume "s x0 \<le> t x0"
        from this x0_neq show ?thesis by simp
      next
        assume "\<exists>y. y < x0 \<and> s y \<noteq> t y"
        then obtain y where "y < x0" and y_neq: "s y \<noteq> t y" by auto
        from \<open>y < x0\<close> x0_min[OF y_neq] show ?thesis by simp
      qed
    next
      show "\<forall>y<x0. s y = t y"
      proof (rule, rule)
        fix y
        assume "y < x0"
        hence "\<not> x0 \<le> y" by simp
        from this x0_min[of y] show "s y = t y" by auto
      qed
    qed
  qed
next
  assume ?R
  thus ?L
  proof
    assume "s = t"
    thus ?thesis by (simp add: lex_fun_def)
  next
    assume "\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)"
    then obtain y where y: "s y < t y" and y_min: "\<forall>z<y. s z = t z" by auto
    show ?thesis unfolding lex_fun_def
    proof
      fix x
      show "s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y)"
      proof (cases "s x \<le> t x")
        assume "s x \<le> t x"
        thus ?thesis by simp
      next
        assume x: "\<not> s x \<le> t x"
        show ?thesis
        proof (intro disjI2, rule exI[of _ y], intro conjI)
          have "\<not> x \<le> y"
          proof
            assume "x \<le> y"
            hence "x < y \<or> y = x" by auto
            thus False
            proof
              assume "x < y"
              from x y_min[rule_format, OF this] show ?thesis by simp
            next
              assume "y = x"
              from this x y show ?thesis
                by (auto simp: preorder_class.less_le_not_le)
            qed
          qed
          thus "y < x" by simp
        next
          from y show "s y \<noteq> t y" by simp
        qed
      qed
    qed
  qed
qed

lemma lex_fun_refl:
  shows "lex_fun s s"
unfolding lex_fun_alt by simp

lemma lex_fun_antisym:
  assumes "lex_fun s t" and "lex_fun t s"
  shows "s = t"
proof
  fix x
  from assms(1) have "s = t \<or> (\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y))"
    unfolding lex_fun_alt .
  thus "s x = t x"
  proof
    assume "s = t"
    thus ?thesis by simp
  next
    assume "\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)"
    then obtain x0 where x0: "s x0 < t x0" and x0_min: "\<forall>y<x0. s y = t y" by auto
    from assms(2) have "t = s \<or> (\<exists>x. t x < s x \<and> (\<forall>y<x. t y = s y))" unfolding lex_fun_alt .
    thus ?thesis
    proof
      assume "t = s"
      thus ?thesis by simp
    next
      assume "\<exists>x. t x < s x \<and> (\<forall>y<x. t y = s y)"
      then obtain x1 where x1: "t x1 < s x1" and x1_min: "\<forall>y<x1. t y = s y" by auto
      have "x0 < x1 \<or> x1 < x0 \<or> x1 = x0" using local.antisym_conv3 by auto
      show ?thesis
      proof (rule linorder_cases[of x0 x1])
        assume "x1 < x0"
        from x0_min[rule_format, OF this] x1 show ?thesis by simp
      next
        assume "x0 = x1"
        from this x0 x1 show ?thesis by simp
      next
        assume "x0 < x1"
        from x1_min[rule_format, OF this] x0 show ?thesis by simp
      qed
    qed
  qed
qed

lemma lex_fun_trans:
  assumes "lex_fun s t" and "lex_fun t u"
  shows "lex_fun s u"
proof -
  from assms(1) have "s = t \<or> (\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y))" unfolding lex_fun_alt .
  thus ?thesis
  proof
    assume "s = t"
    from this assms(2) show ?thesis by simp
  next
    assume "\<exists>x. s x < t x \<and> (\<forall>y<x. s y = t y)"
    then obtain x0 where x0: "s x0 < t x0" and x0_min: "\<forall>y<x0. s y = t y"
      by auto
    from assms(2) have "t = u \<or> (\<exists>x. t x < u x \<and> (\<forall>y<x. t y = u y))" unfolding lex_fun_alt .
    thus ?thesis
    proof
      assume "t = u"
      from this assms(1) show ?thesis by simp
    next
      assume "\<exists>x. t x < u x \<and> (\<forall>y<x. t y = u y)"
      then obtain x1 where x1: "t x1 < u x1" and x1_min: "\<forall>y<x1. t y = u y" by auto
      show ?thesis unfolding lex_fun_alt
      proof (intro disjI2)
        show "\<exists>x. s x < u x \<and> (\<forall>y<x. s y = u y)"
        proof (rule linorder_cases[of x0 x1])
          assume "x1 < x0"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from x0_min[rule_format, OF \<open>x1 < x0\<close>] x1 show "s x1 < u x1" by simp
          next
            show "\<forall>y<x1. s y = u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x1"
              from this \<open>x1 < x0\<close> have "y < x0" by simp
              from x0_min[rule_format, OF this] x1_min[rule_format, OF \<open>y < x1\<close>]
                show "s y = u y" by simp
            qed
          qed
        next
          assume "x0 < x1"
          show ?thesis
          proof (rule exI[of _ x0], intro conjI)
            from x1_min[rule_format, OF \<open>x0 < x1\<close>] x0 show "s x0 < u x0" by simp
          next
            show "\<forall>y<x0. s y = u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x0"
              from this \<open>x0 < x1\<close> have "y < x1" by simp
              from x0_min[rule_format, OF \<open>y < x0\<close>] x1_min[rule_format, OF this]
                show "s y = u y" by simp
            qed
          qed
        next
          assume "x0 = x1"
          show ?thesis
          proof (rule exI[of _ x1], intro conjI)
            from \<open>x0 = x1\<close> x0 x1 show "s x1 < u x1" by simp
          next
            show "\<forall>y<x1. s y = u y"
            proof (intro allI, intro impI)
              fix y
              assume "y < x1"
              hence "y < x0" using \<open>x0 = x1\<close> by simp
              from x0_min[rule_format, OF this] x1_min[rule_format, OF \<open>y < x1\<close>]
                show "s y = u y" by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma lex_fun_lin: "lex_fun s t \<or> lex_fun t s" for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
proof (intro disjCI)
  assume "\<not> lex_fun t s"
  hence a: "\<forall>x. \<not> (t x < s x) \<or> (\<exists>y<x. t y \<noteq> s y)" unfolding lex_fun_alt by auto
  show "lex_fun s t" unfolding lex_fun_def
  proof
    fix x
    from a have "\<not> (t x < s x) \<or> (\<exists>y<x. t y \<noteq> s y)" ..
    thus "s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y)" by auto
  qed
qed

lemma lex_fun_zero_min: "lex_fun 0 s" for s::"'a \<Rightarrow> 'b::add_linorder_min"
  by (simp add: lex_fun_def zero_min)

lemma lex_fun_plus_monotone:
  "lex_fun (s + u) (t + u)" if "lex_fun s t"
  for s t::"'a \<Rightarrow> 'b::ordered_cancel_comm_monoid_add"
unfolding lex_fun_def
proof
  fix x
  from that have "s x \<le> t x \<or> (\<exists>y<x. s y \<noteq> t y)" unfolding lex_fun_def ..
  thus "(s + u) x \<le> (t + u) x \<or> (\<exists>y<x. (s + u) y \<noteq> (t + u) y)"
  proof
    assume a1: "s x \<le> t x"
    show ?thesis
    proof (intro disjI1)
      from a1 show "(s + u) x \<le> (t + u) x" by (auto simp: add_right_mono)
    qed
  next
    assume "\<exists>y<x. s y \<noteq> t y"
    then obtain y where "y < x" and a2: "s y \<noteq> t y" by auto
    show ?thesis
    proof (intro disjI2, rule exI[of _ y], intro conjI, fact)
      from a2 show "(s + u) y \<noteq> (t + u) y" by (auto simp: add_right_mono)
    qed
  qed
qed

end (* wellorder *)

subsubsection \<open>Degree\<close>

definition deg_fun::"('a \<Rightarrow> 'b::comm_monoid_add) \<Rightarrow> 'b" where "deg_fun s \<equiv> \<Sum>x\<in>(supp_fun s). s x"

lemma deg_fun_zero[simp]: "deg_fun 0 = 0"
  by (auto simp: deg_fun_def)

lemma deg_fun_eq_0_iff:
  assumes "finite (supp_fun (s::'a \<Rightarrow> 'b::add_linorder_min))"
  shows "deg_fun s = 0 \<longleftrightarrow> s = 0"
proof
  assume "deg_fun s = 0"
  hence *: "(\<Sum>x\<in>(supp_fun s). s x) = 0" by (simp only: deg_fun_def)
  have **: "\<And>x. 0 \<le> s x" by (rule zero_min)
  from * have "\<And>x. x \<in> supp_fun s \<Longrightarrow> s x = 0" by (simp only: sum_nonneg_eq_0_iff[OF assms **])
  thus "s = 0" by (rule fun_eq_zeroI)
qed simp

lemma deg_fun_superset:
  fixes A::"'a set"
  assumes "supp_fun s \<subseteq> A" and "finite A"
  shows "deg_fun s = (\<Sum>x\<in>A. s x)"
  unfolding deg_fun_def
proof (rule sum.mono_neutral_cong_left, fact, fact, rule)
  fix x
  assume "x \<in> A - supp_fun s"
  hence "x \<notin> supp_fun s" by simp
  thus "s x = 0" by (simp add: supp_fun_def)
qed rule

lemma deg_fun_plus:
  assumes "finite (supp_fun s)" and "finite (supp_fun t)"
  shows "deg_fun (s + t) = deg_fun s + deg_fun (t::'a \<Rightarrow> 'b::comm_monoid_add)"
proof -
  from assms have fin: "finite (supp_fun s \<union> supp_fun t)" by simp
  have "deg_fun (s + t) = (\<Sum>x\<in>(supp_fun (s + t)). s x + t x)" by (simp add: deg_fun_def)
  also from fin have "... = (\<Sum>x\<in>(supp_fun s \<union> supp_fun t). s x + t x)"
  proof (rule sum.mono_neutral_cong_left)
    show "\<forall>x\<in>supp_fun s \<union> supp_fun t - supp_fun (s + t). s x + t x = 0"
    proof
      fix x
      assume "x \<in> supp_fun s \<union> supp_fun t - supp_fun (s + t)"
      hence "x \<notin> supp_fun (s + t)" by simp
      thus "s x + t x = 0" by (simp add: supp_fun_def)
    qed
  qed (rule supp_add_subset, rule)
  also have "\<dots> = (\<Sum>x\<in>(supp_fun s \<union> supp_fun t). s x) + (\<Sum>x\<in>(supp_fun s \<union> supp_fun t). t x)"
    by (rule sum.distrib)
  also from fin have "(\<Sum>x\<in>(supp_fun s \<union> supp_fun t). s x) = deg_fun s" unfolding deg_fun_def
  proof (rule sum.mono_neutral_cong_right)
    show "\<forall>x\<in>supp_fun s \<union> supp_fun t - supp_fun s. s x = 0"
    proof
      fix x
      assume "x \<in> supp_fun s \<union> supp_fun t - supp_fun s"
      hence "x \<notin> supp_fun s" by simp
      thus "s x = 0" by (simp add: supp_fun_def)
    qed
  qed simp_all
  also from fin have "(\<Sum>x\<in>(supp_fun s \<union> supp_fun t). t x) = deg_fun t" unfolding deg_fun_def
  proof (rule sum.mono_neutral_cong_right)
  show "\<forall>x\<in>supp_fun s \<union> supp_fun t - supp_fun t. t x = 0"
    proof
      fix x
      assume "x \<in> supp_fun s \<union> supp_fun t - supp_fun t"
      hence "x \<notin> supp_fun t" by simp
      thus "t x = 0" by (simp add: supp_fun_def)
    qed
  qed simp_all
  finally show ?thesis .
qed

lemma deg_fun_leq:
  assumes "finite (supp_fun s)" and "finite (supp_fun t)" and "s \<le> (t::'a \<Rightarrow> 'b::ordered_comm_monoid_add)"
  shows "deg_fun s \<le> deg_fun t"
proof -
  let ?A = "supp_fun s \<union> supp_fun t"
  from assms(1) assms(2) have 1: "finite ?A" by simp
  have s: "supp_fun s \<subseteq> ?A" and t: "supp_fun t \<subseteq> ?A" by simp_all
  show ?thesis unfolding deg_fun_superset[OF s 1] deg_fun_superset[OF t 1]
  proof (rule sum_mono)
    fix i
    from assms(3) show "s i \<le> t i" unfolding le_fun_def ..
  qed
qed

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

definition dord_fun::"(('a \<Rightarrow> 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "dord_fun ord s t \<equiv> (let d1 = deg_fun s; d2 = deg_fun t in (d1 < d2 \<or> (d1 = d2 \<and> ord s t)))"

lemma dord_fun_degD:
  assumes "dord_fun ord s t"
  shows "deg_fun s \<le> deg_fun t"
  using assms unfolding dord_fun_def Let_def by auto

lemma dord_fun_refl:
  assumes "ord s s"
  shows "dord_fun ord s s"
  using assms unfolding dord_fun_def by simp

lemma dord_fun_antisym:
  assumes ord_antisym: "ord s t \<Longrightarrow> ord t s \<Longrightarrow> s = t" and "dord_fun ord s t" and "dord_fun ord t s"
  shows "s = t"
proof -
  from assms(3) have ts: "deg_fun t < deg_fun s \<or> (deg_fun t = deg_fun s \<and> ord t s)"
    unfolding dord_fun_def Let_def .
  from assms(2) have st: "deg_fun s < deg_fun t \<or> (deg_fun s = deg_fun t \<and> ord s t)"
    unfolding dord_fun_def Let_def .
  thus ?thesis
  proof
    assume "deg_fun s < deg_fun t"
    thus ?thesis using ts by auto
  next
    assume "deg_fun s = deg_fun t \<and> ord s t"
    hence "deg_fun s = deg_fun t" and "ord s t" by simp_all
    from \<open>deg_fun s = deg_fun t\<close> ts have "ord t s" by simp
    with \<open>ord s t\<close> show ?thesis by (rule ord_antisym)
  qed
qed

lemma dord_fun_trans:
  assumes ord_trans: "ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u" and "dord_fun ord s t" and "dord_fun ord t u"
  shows "dord_fun ord s u"
proof -
  from assms(3) have ts: "deg_fun t < deg_fun u \<or> (deg_fun t = deg_fun u \<and> ord t u)"
    unfolding dord_fun_def Let_def .
  from assms(2) have st: "deg_fun s < deg_fun t \<or> (deg_fun s = deg_fun t \<and> ord s t)"
    unfolding dord_fun_def Let_def .
  thus ?thesis
  proof
    assume "deg_fun s < deg_fun t"
    from this dord_fun_degD[OF assms(3)] have "deg_fun s < deg_fun u" by simp
    thus ?thesis by (simp add: dord_fun_def Let_def)
  next
    assume "deg_fun s = deg_fun t \<and> ord s t"
    hence "deg_fun s = deg_fun t" and "ord s t" by simp_all
    from ts show ?thesis
    proof
      assume "deg_fun t < deg_fun u"
      hence "deg_fun s < deg_fun u" using \<open>deg_fun s = deg_fun t\<close> by simp
      thus ?thesis by (simp add: dord_fun_def Let_def)
    next
      assume "deg_fun t = deg_fun u \<and> ord t u"
      hence "deg_fun t = deg_fun u" and "ord t u" by simp_all
      from ord_trans[OF \<open>ord s t\<close> \<open>ord t u\<close>] \<open>deg_fun s = deg_fun t\<close> \<open>deg_fun t = deg_fun u\<close> show ?thesis
        by (simp add: dord_fun_def Let_def)
    qed
  qed
qed

lemma dord_fun_lin:
  "dord_fun ord s t \<or> dord_fun ord t s"
  if "ord s t \<or> ord t s"
  for s t::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder}"
proof (intro disjCI)
  assume "\<not> dord_fun ord t s"
  hence "deg_fun s \<le> deg_fun t \<and> (deg_fun t \<noteq> deg_fun s \<or> \<not> ord t s)"
    unfolding dord_fun_def Let_def by auto
  hence "deg_fun s \<le> deg_fun t" and dis1: "deg_fun t \<noteq> deg_fun s \<or> \<not> ord t s" by simp_all
  show "dord_fun ord s t" unfolding dord_fun_def Let_def
  proof (intro disjCI)
    assume "\<not> (deg_fun s = deg_fun t \<and> ord s t)"
    hence dis2: "deg_fun s \<noteq> deg_fun t \<or> \<not> ord s t" by simp
    show "deg_fun s < deg_fun t"
    proof (cases "deg_fun s = deg_fun t")
      case True
      from True dis1 have "\<not> ord t s" by simp
      from True dis2 have "\<not> ord s t" by simp
      from \<open>\<not> ord s t\<close> \<open>\<not> ord t s\<close> that show ?thesis by simp
    next
      case False
      from this \<open>deg_fun s \<le> deg_fun t\<close> show ?thesis by simp
    qed
  qed
qed

lemma dord_fun_zero_min:
  fixes s t::"'a \<Rightarrow> 'b::add_linorder_min"
  assumes ord_refl: "\<And>t. ord t t" and "finite (supp_fun s)"
  shows "dord_fun ord 0 s"
  unfolding dord_fun_def Let_def deg_fun_zero
proof (rule disjCI)
  assume "\<not> (0 = deg_fun s \<and> ord 0 s)"
  hence dis: "deg_fun s \<noteq> 0 \<or> \<not> ord 0 s" by simp
  show "0 < deg_fun s"
  proof (cases "deg_fun s = 0")
    case True
    hence "s = 0" using deg_fun_eq_0_iff[OF assms(2)] by auto
    hence "ord 0 s" using ord_refl by simp
    with True dis show ?thesis by simp
  next
    case False
    thus ?thesis by (auto simp: zero_less_iff_neq_zero)
  qed
qed

lemma dord_fun_plus_monotone:
  fixes s t u ::"'a \<Rightarrow> 'b::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes ord_monotone: "ord s t \<Longrightarrow> ord (s + u) (t + u)" and "finite (supp_fun s)"
    and "finite (supp_fun t)" and "finite (supp_fun u)" and "dord_fun ord s t"
  shows "dord_fun ord (s + u) (t + u)"
proof -
  from assms(5) have "deg_fun s < deg_fun t \<or> (deg_fun s = deg_fun t \<and> ord s t)"
    unfolding dord_fun_def Let_def .
  thus ?thesis
  proof
    assume "deg_fun s < deg_fun t"
    hence "deg_fun (s + u) < deg_fun (t + u)" by (auto simp: deg_fun_plus[OF _ assms(4)] assms(2) assms(3))
    thus ?thesis unfolding dord_fun_def Let_def by simp
  next
    assume "deg_fun s = deg_fun t \<and> ord s t"
    hence "deg_fun s = deg_fun t" and "ord s t" by simp_all
    from \<open>deg_fun s = deg_fun t\<close> have "deg_fun (s + u) = deg_fun (t + u)"
      by (auto simp: deg_fun_plus[OF _ assms(4)] assms(2) assms(3))
    from this ord_monotone[OF \<open>ord s t\<close>] show ?thesis unfolding dord_fun_def Let_def by simp
  qed
qed

end (* linorder *)

subsubsection \<open>Degree-Lexicographic Term Order\<close>

context wellorder
begin

definition dlex_fun::"('a \<Rightarrow> 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "dlex_fun \<equiv> dord_fun lex_fun"

lemma dlex_fun_refl:
  shows "dlex_fun s s"
unfolding dlex_fun_def by (rule dord_fun_refl, rule lex_fun_refl)

thm dord_fun_antisym
lemma dlex_fun_antisym:
  assumes "dlex_fun s t" and "dlex_fun t s"
  shows "s = t"
  by (rule dord_fun_antisym, erule lex_fun_antisym, assumption,
      simp_all only: dlex_fun_def[symmetric], fact+)

lemma dlex_fun_trans:
  assumes "dlex_fun s t" and "dlex_fun t u"
  shows "dlex_fun s u"
  by (simp only: dlex_fun_def, rule dord_fun_trans, erule lex_fun_trans, assumption,
      simp_all only: dlex_fun_def[symmetric], fact+)

lemma dlex_fun_lin: "dlex_fun s t \<or> dlex_fun t s"
  for s t::"('a \<Rightarrow> 'b::{ordered_comm_monoid_add, linorder})"
unfolding dlex_fun_def by (rule dord_fun_lin, rule lex_fun_lin)

lemma dlex_fun_zero_min:
  fixes s t::"('a \<Rightarrow> 'b::add_linorder_min)"
  assumes "finite (supp_fun s)"
  shows "dlex_fun 0 s"
  unfolding dlex_fun_def by (rule dord_fun_zero_min, rule lex_fun_refl, fact)

lemma dlex_fun_plus_monotone:
  fixes s t u::"'a \<Rightarrow> 'b::{ordered_cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes "finite (supp_fun s)" and "finite (supp_fun t)" and "finite (supp_fun u)" and "dlex_fun s t"
  shows "dlex_fun (s + u) (t + u)"
  using lex_fun_plus_monotone[of s t u] assms unfolding dlex_fun_def
  by (rule dord_fun_plus_monotone)

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


subsection \<open>Type @{type poly_mapping}\<close>

lemma poly_mapping_eq_zeroI:
  assumes "\<And>x. x \<in> keys s \<Longrightarrow> lookup s x = 0"
  shows "s = (0::('a, 'b::zero) poly_mapping)"
proof (rule poly_mapping_eqI, simp)
  fix x
  show "lookup s x = 0"
  proof (cases "x \<in> keys s")
    case True
    then show ?thesis by (rule assms)
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma lookup_zero_fun: "lookup 0 = 0"
  by (simp only: zero_poly_mapping.rep_eq zero_fun_def)

lemma lookup_plus_fun: "lookup (s + t) = lookup s + lookup t"
  by (simp only: plus_poly_mapping.rep_eq plus_fun_def)

lemma lookup_uminus_fun: "lookup (- s) = - lookup s"
  by (fact uminus_poly_mapping.rep_eq)

lemma lookup_minus_fun: "lookup (s - (t::'a \<Rightarrow>\<^sub>0 'b::ab_group_add)) = lookup s - lookup t"
  by (simp only: diff_conv_add_uminus, simp only: lookup_plus_fun lookup_uminus_fun)

lemma poly_mapping_adds_iff: "s adds t \<longleftrightarrow> lookup s adds lookup t"
  unfolding adds_def
proof
  assume "\<exists>k. t = s + k"
  then obtain k where *: "t = s + k" ..
  show "\<exists>k. lookup t = lookup s + k"
  proof
    from * show "lookup t = lookup s + lookup k" by (simp only: lookup_plus_fun)
  qed
next
  assume "\<exists>k. lookup t = lookup s + k"
  then obtain k where *: "lookup t = lookup s + k" ..
  have **: "k \<in> {f. finite {x. f x \<noteq> 0}}"
  proof
    have "finite {x. lookup t x \<noteq> 0}" by transfer
    hence "finite {x. lookup s x + k x \<noteq> 0}" by (simp only: * plus_fun_def)
    moreover have "finite {x. lookup s x \<noteq> 0}" by transfer
    ultimately show "finite {x. k x \<noteq> 0}" by (rule finite_neq_0_inv', simp)
  qed
  show "\<exists>k. t = s + k"
  proof
    thm Abs_poly_mapping_inverse[OF **]
    show "t = s + Abs_poly_mapping k"
      by (rule poly_mapping_eqI, simp add: * lookup_add Abs_poly_mapping_inverse[OF **])
  qed
qed

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class comm_powerprod}\<close>

instance poly_mapping :: (type, cancel_comm_monoid_add) comm_powerprod
  by standard

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class ninv_comm_monoid_add}\<close>

instance poly_mapping :: (type, ninv_comm_monoid_add) ninv_comm_monoid_add
proof (standard, transfer)
  fix s t::"'a \<Rightarrow> 'b"
  assume "(\<lambda>k. s k + t k) = (\<lambda>_. 0)"
  hence "s + t = 0" by (simp only: plus_fun_def zero_fun_def)
  hence "s = 0" by (rule plus_eq_zero)
  thus "s = (\<lambda>_. 0)" by (simp only: zero_fun_def)
qed

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class lcs_powerprod}\<close>

instantiation poly_mapping :: (type, add_linorder) lcs_powerprod
begin

lift_definition lcs_poly_mapping::"('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is "\<lambda>s t. \<lambda>x. max (s x) (t x)"
proof -
  fix fun1 fun2::"'a \<Rightarrow> 'b"
  assume "finite {t. fun1 t \<noteq> 0}" and "finite {t. fun2 t \<noteq> 0}"
  from finite_neq_0'[OF this, of max] show "finite {t. max (fun1 t) (fun2 t) \<noteq> 0}"
    by (auto simp: max_def)
qed

lemma adds_poly_mappingI:
  assumes "lookup s \<le> lookup (t::'a \<Rightarrow>\<^sub>0 'b)"
  shows "s adds t"
  unfolding poly_mapping_adds_iff using assms by (rule adds_funI)

lemma lookup_lcs_fun: "lookup (lcs s t) = lcs (lookup s) (lookup (t:: 'a \<Rightarrow>\<^sub>0 'b))"
  by (simp only: lcs_poly_mapping.rep_eq lcs_fun_def)

instance
  by (standard, simp_all only: poly_mapping_adds_iff lookup_lcs_fun, rule adds_lcs, elim lcs_adds,
      assumption, rule poly_mapping_eqI, simp only: lookup_lcs_fun lcs_comm)

end

lemma adds_poly_mapping: "s adds t \<longleftrightarrow> lookup s \<le> lookup t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  by (simp only: poly_mapping_adds_iff adds_fun)

lemma lookup_gcs_fun: "lookup (gcs s (t::'a \<Rightarrow>\<^sub>0 ('b::add_linorder_group))) = gcs (lookup s) (lookup t)"
  by (simp only: gcs_def lookup_minus_fun lookup_plus_fun lookup_lcs_fun)

subsubsection \<open>@{typ "('a, 'b) poly_mapping"} belongs to class @{class ulcs_powerprod}\<close>

instance poly_mapping :: (type, add_linorder_min) ulcs_powerprod ..

subsubsection \<open>Power-products in a given set of indeterminates.\<close>

definition sub_keys::"'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> bool" where "sub_keys V s \<longleftrightarrow> keys s \<subseteq> V"

lift_definition truncate_poly_mapping::"'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero)"
  is truncate_fun
proof (simp only: truncate_fun_def)
  fix V::"'a set" and s::"'a \<Rightarrow> 'b"
  assume fin: "finite {x. s x \<noteq> 0}"
  have "finite {_. 0 \<noteq> 0}" by simp
  from finite_neq_0[OF fin this, of "\<lambda>x t f. (if x \<in> V then t else f)"]
    show "finite {x. (if x \<in> V then s x else 0) \<noteq> 0}" by simp
qed

lemma sub_keys_iff: "sub_keys V s \<longleftrightarrow> sub_supp V (lookup s)"
  unfolding sub_keys_def sub_supp_def supp_fun_def by (transfer, rule)

lemma lookup_truncate_fun: "lookup (truncate_poly_mapping V s) = truncate_fun V (lookup s)"
  by (fact truncate_poly_mapping.rep_eq)

lemma sub_keys_univ: "sub_keys (UNIV::'a set) s"
  by (simp only: sub_keys_iff, fact sub_supp_univ)

lemma sub_keys_empty: "sub_keys {} s = (s = 0)"
  by (simp only: sub_keys_iff poly_mapping_eq_iff lookup_zero_fun, fact sub_supp_empty)

lemma sub_keys_truncate: "sub_keys V (truncate_poly_mapping V s)"
  by (simp only: sub_keys_iff lookup_truncate_fun, fact sub_supp_truncate)

lemma sub_keys_union_add:
  fixes V U::"'a set" and s t::"'a \<Rightarrow>\<^sub>0 'b::monoid_add"
  assumes "sub_keys V s" and "sub_keys U t"
  shows "sub_keys (V \<union> U) (s + t)"
  using assms by (simp only: sub_keys_iff lookup_plus_fun, elim sub_supp_union_add)

lemma adds_insert_keys:
  fixes s t::"'a \<Rightarrow>\<^sub>0 'b::add_linorder"
  assumes "sub_keys (insert v V) s" and "sub_keys (insert v V) t"
  shows "s adds t = (truncate_poly_mapping V s adds truncate_poly_mapping V t \<and> lookup s v adds lookup t v)"
  using assms by (simp only: sub_keys_iff poly_mapping_adds_iff lookup_truncate_fun, elim adds_insert_supp)

subsubsection \<open>Dickson's lemma for power-products in finitely many indeterminates\<close>

lemma poly_mapping_incr_subsequence:
  fixes V::"'a set"
    and f::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b::add_wellorder"
  assumes "finite V" and "\<And>k. sub_keys V (f k)"
  shows "\<exists>m::nat \<Rightarrow> nat. (strict_mono m) \<and> (\<forall>i j. i < j \<longrightarrow> (f o m) i adds (f o m) j)"
proof -
  have *: "\<And>m i. lookup ((f \<circ> m) i) = ((lookup \<circ> f) \<circ> m) i" by simp
  from assms(2) have "\<And>k. sub_supp V ((lookup \<circ> f) k)" by (simp add: sub_keys_iff)
  with assms(1) show ?thesis by (simp only: poly_mapping_adds_iff *, rule fun_incr_subsequence)
qed

lemma Dickson_poly_mapping:
  fixes seq::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b::add_wellorder"
  assumes "finite V" and "\<And>k. sub_keys V (seq k)"
  shows "\<exists>i j::nat. i < j \<and> seq i adds seq j"
proof -
  from poly_mapping_incr_subsequence[OF assms] obtain m::"nat \<Rightarrow> nat" where
    "strict_mono m \<and> (\<forall>i j. i < j \<longrightarrow> (seq o m) i adds (seq o m) j)" ..
  then have m_subseq: "strict_mono m" and m_div: "\<forall>i j. i < j \<longrightarrow> (seq o m) i adds (seq o m) j" by simp_all
  let ?i = "m 0" and ?j = "m 1"
  show "\<exists>i j::nat. i < j \<and> seq i adds seq j"
  proof (rule, rule)
    show "?i < ?j \<and> seq ?i adds seq ?j" using m_subseq m_div by (simp add: strict_mono_def)
  qed
qed

instance poly_mapping :: (finite, add_wellorder) dickson_powerprod
proof
  fix seq::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  have "finite (UNIV::'a set)" by simp
  moreover have "\<And>k. sub_keys UNIV (seq k)" by (rule sub_keys_univ)
  ultimately show "\<exists>i j. i < j \<and> seq i adds seq j" by (rule Dickson_poly_mapping)
qed

subsubsection \<open>Lexicographic Term Order\<close>

context wellorder
begin

lemma neq_poly_mapping_alt:
  assumes "s \<noteq> (t::'a \<Rightarrow>\<^sub>0 'b::zero)"
  obtains x where "lookup s x \<noteq> lookup t x" and "\<And>y. lookup s y \<noteq> lookup t y \<Longrightarrow> x \<le> y"
  using assms unfolding poly_mapping_eq_iff by (rule neq_fun_alt, auto)

lift_definition lex_pm::"('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::{zero,order}) \<Rightarrow> bool" is lex_fun .

lemma lex_pm_alt: "lex_pm s t = (s = t \<or> (\<exists>x. lookup s x < lookup t x \<and> (\<forall>y<x. lookup s y = lookup t y)))"
  by (simp only: lex_pm.rep_eq lex_fun_alt poly_mapping_eq_iff)

lemma lex_pm_refl: "lex_pm s s"
  by (simp only: lex_pm.rep_eq lex_fun_refl)

lemma lex_pm_antisym:
  assumes "lex_pm s t" and "lex_pm t s"
  shows "s = t"
  using assms by (simp only: lex_pm.rep_eq poly_mapping_eq_iff, elim lex_fun_antisym)

lemma lex_pm_trans:
  assumes "lex_pm s t" and "lex_pm t u"
  shows "lex_pm s u"
  using assms by (simp only: lex_pm.rep_eq, elim lex_fun_trans[of "lookup s" "lookup t"])

lemma lex_pm_lin: "lex_pm s t \<or> lex_pm t s" for s t::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, linorder}"
  by (simp only: lex_pm.rep_eq, fact lex_fun_lin)

lemma lex_pm_zero_min: "lex_pm 0 s" for s::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  by (simp only: lex_pm.rep_eq lookup_zero_fun, fact lex_fun_zero_min)

lemma lex_pm_plus_monotone:
  "lex_pm (s + u) (t + u)" if "lex_pm s t"
for s t::"'a \<Rightarrow>\<^sub>0 'b::ordered_cancel_comm_monoid_add"
  using that by (simp only: lex_pm.rep_eq lookup_plus_fun, elim lex_fun_plus_monotone)

end (* wellorder *)

subsubsection \<open>Degree\<close>

lift_definition deg_pm::"('a \<Rightarrow>\<^sub>0 'b::comm_monoid_add) \<Rightarrow> 'b" is deg_fun .

lemma deg_pm_zero[simp]: "deg_pm 0 = 0"
  by (simp add: deg_pm.rep_eq lookup_zero_fun)

lemma deg_pm_eq_0_iff[simp]: "deg_pm s = 0 \<longleftrightarrow> s = 0" for s::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  by (simp only: deg_pm.rep_eq poly_mapping_eq_iff lookup_zero_fun, rule deg_fun_eq_0_iff,
      simp add: keys_eq_supp[symmetric])

lemma deg_pm_superset:
  assumes "keys s \<subseteq> A" and "finite A"
  shows "deg_pm s = (\<Sum>x\<in>A. lookup s x)"
  using assms by (simp only: deg_pm.rep_eq keys_eq_supp, elim deg_fun_superset)

lemma deg_pm_plus: "deg_pm (s + t) = deg_pm s + deg_pm (t::'a \<Rightarrow>\<^sub>0 'b::comm_monoid_add)"
  by (simp only: deg_pm.rep_eq lookup_plus_fun, rule deg_fun_plus, simp_all add: keys_eq_supp[symmetric])

subsubsection \<open>General Degree-Orders\<close>

context linorder
begin

lift_definition dord_pm::"(('a \<Rightarrow>\<^sub>0 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  is dord_fun by (metis local.dord_fun_def) 

lemma dord_pm_degD:
  assumes "dord_pm ord s t"
  shows "deg_pm s \<le> deg_pm t"
  using assms by (simp only: dord_pm.rep_eq deg_pm.rep_eq, elim dord_fun_degD)

lemma dord_pm_refl:
  assumes "ord s s"
  shows "dord_pm ord s s"
  using assms by (simp only: dord_pm.rep_eq, intro dord_fun_refl, simp add: lookup_inverse)

lemma dord_pm_antisym:
  assumes "ord s t \<Longrightarrow> ord t s \<Longrightarrow> s = t" and "dord_pm ord s t" and "dord_pm ord t s"
  shows "s = t"
  using assms
proof (simp only: dord_pm.rep_eq poly_mapping_eq_iff)
  assume 1: "(ord s t \<Longrightarrow> ord t s \<Longrightarrow> lookup s = lookup t)"
  assume 2: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup s) (lookup t)"
  assume 3: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup t) (lookup s)"
  from _ 2 3 show "lookup s = lookup t" by (rule dord_fun_antisym, simp add: lookup_inverse 1)
qed

lemma dord_pm_trans:
  assumes "ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u" and "dord_pm ord s t" and "dord_pm ord t u"
  shows "dord_pm ord s u"
  using assms
proof (simp only: dord_pm.rep_eq poly_mapping_eq_iff)
  assume 1: "(ord s t \<Longrightarrow> ord t u \<Longrightarrow> ord s u)"
  assume 2: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup s) (lookup t)"
  assume 3: "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup t) (lookup u)"
  from _ 2 3 show "dord_fun (map_fun Abs_poly_mapping id \<circ> ord \<circ> Abs_poly_mapping) (lookup s) (lookup u)"
    by (rule dord_fun_trans, simp add: lookup_inverse 1)
qed

lemma dord_pm_lin:
  "dord_pm ord s t \<or> dord_pm ord t s"
  if "ord s t \<or> ord t s"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, linorder}"
  using that by (simp only: dord_pm.rep_eq, intro dord_fun_lin, simp add: lookup_inverse)

lemma dord_pm_zero_min: "dord_pm ord 0 s"
  if ord_refl: "\<And>t. ord t t"
  for s t::"'a \<Rightarrow>\<^sub>0 'b::add_linorder_min"
  using that
  by (simp only: dord_pm.rep_eq lookup_zero_fun, intro dord_fun_zero_min,
      simp add: lookup_inverse, simp add: keys_eq_supp[symmetric])

lemma dord_pm_plus_monotone:
  fixes s t u ::"'a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le}"
  assumes "dord_pm ord s t" and ord_monotone: "ord s t \<Longrightarrow> ord (s + u) (t + u)"
  shows "dord_pm ord (s + u) (t + u)"
  using assms
  by (simp only: dord_pm.rep_eq lookup_plus_fun, intro dord_fun_plus_monotone,
      simp add: lookup_inverse lookup_plus_fun[symmetric],
      simp add: keys_eq_supp[symmetric],
      simp add: keys_eq_supp[symmetric],
      simp add: keys_eq_supp[symmetric],
      simp add: lookup_inverse)

end (* linorder *)

subsubsection \<open>Degree-Lexicographic Term Order\<close>

context wellorder
begin

definition dlex_pm::"('a \<Rightarrow>\<^sub>0 'b::ordered_comm_monoid_add) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool" where "dlex_pm \<equiv> dord_pm lex_pm"

lemma dlex_pm_iff: "dlex_pm s t \<longleftrightarrow> dlex_fun (lookup s) (lookup t)"
  by (simp add: dlex_pm_def dlex_fun_def dord_fun_def dord_pm_def lex_pm.rep_eq lookup_inverse)

lemma dlex_pm_refl: "dlex_pm s s"
  by (simp only: dlex_pm_iff, fact dlex_fun_refl)

lemma dlex_pm_antisym:
  assumes "dlex_pm s t" and "dlex_pm t s"
  shows "s = t"
  using assms by (simp only: dlex_pm_iff poly_mapping_eq_iff, elim dlex_fun_antisym)

lemma dlex_pm_trans:
  assumes "dlex_pm s t" and "dlex_pm t u"
  shows "dlex_pm s u"
  using assms by (simp only: dlex_pm_iff, elim dlex_fun_trans[of "lookup s" "lookup t"])

lemma dlex_pm_lin: "dlex_pm s t \<or> dlex_pm t s"
  for s t::"('a \<Rightarrow>\<^sub>0 'b::{ordered_comm_monoid_add, linorder})"
  by (simp only: dlex_pm_iff, fact dlex_fun_lin)

lemma dlex_pm_zero_min: "dlex_pm 0 s"
  for s t::"('a \<Rightarrow>\<^sub>0 'b::add_linorder_min)"
  by (simp only: dlex_pm_iff lookup_zero_fun, rule dlex_fun_zero_min, simp add: keys_eq_supp[symmetric])

lemma dlex_pm_plus_monotone:
  fixes s t::"'a \<Rightarrow>\<^sub>0 'b::{ordered_ab_semigroup_add_imp_le, ordered_cancel_comm_monoid_add}"
  assumes "dlex_pm s t"
  shows "dlex_pm (s + u) (t + u)"
  using assms
  by (simp only: dlex_pm_iff lookup_plus_fun, intro dlex_fun_plus_monotone,
      simp_all add: keys_eq_supp[symmetric])

end (* wellorder *)

end (* theory *)
