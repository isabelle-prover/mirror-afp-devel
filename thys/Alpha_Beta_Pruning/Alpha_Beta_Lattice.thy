chapter \<open>Distributive Lattices\<close>

theory Alpha_Beta_Lattice
imports Alpha_Beta_Linear
begin

class distrib_bounded_lattice = distrib_lattice + bounded_lattice

(* For quickcheck: *)
instance bool :: distrib_bounded_lattice ..
instance ereal :: distrib_bounded_lattice ..
instance set :: (type) distrib_bounded_lattice ..

unbundle lattice_syntax

section \<open>Game Tree Evaluation\<close>

fun sups :: "('a::bounded_lattice) list \<Rightarrow> 'a" where
"sups [] = \<bottom>" |
"sups (x#xs) = x \<squnion> sups xs"

fun infs :: "('a::bounded_lattice) list \<Rightarrow> 'a" where
"infs [] = \<top>" |
"infs (x#xs) = x \<sqinter> infs xs"

fun supinf :: "('a::distrib_bounded_lattice) tree \<Rightarrow> 'a"
and infsup :: "('a::distrib_bounded_lattice) tree \<Rightarrow> 'a" where
"supinf (Lf x) = x" |
"supinf (Nd ts) = sups (map infsup ts)" |
"infsup (Lf x) = x" |
"infsup (Nd ts) = infs (map supinf ts)"


section \<open>Distributive Lattices\<close>

lemma sup_inf_assoc:
  "(a::_::distrib_lattice) \<le> b \<Longrightarrow> a \<squnion> (x \<sqinter> b) = (a \<squnion> x) \<sqinter> b"
by (metis inf.orderE inf_sup_distrib2)

lemma sup_inf_assoc_iff:
  "(a::_::distrib_lattice) \<squnion> x \<sqinter> b = a \<squnion> y \<sqinter> b \<longleftrightarrow> (a \<squnion> x) \<sqinter> b = (a \<squnion> y) \<sqinter> b"
by (metis (no_types, opaque_lifting) inf.left_idem inf_commute inf_sup_distrib1 sup.left_idem sup_inf_distrib1)

text \<open>Generalization of Knuth and Moore's equivalence modulo:\<close>
abbreviation
  eq_mod :: "('a::lattice) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_ \<simeq>/ _/ '(mod _,_'))" [51,51,0,0]) where
 "eq_mod x y a b \<equiv> a \<squnion> x \<sqinter> b = a \<squnion> y \<sqinter> b"

notation (latex output) eq_mod ("(_ \<simeq>/ _/ '(\<^latex>\<open>\\textup{mod}\<close> _,_'))" [51,51,0,0])

text \<open>\<open>ab\<close> is bounded by \<open>v\<close> mod \<open>a,b\<close>, or the other way around.\<close>
abbreviation "bounded (a::_::lattice) b v ab \<equiv> b \<sqinter> v \<le> ab \<and> ab \<le> a \<squnion> v"

abbreviation bounded2 :: "('a::lattice) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_ \<sqsubseteq>/ _/ '(mod _,_'))" [51,51,0,0])
where "bounded2 ab v a b \<equiv> bounded a b v ab"

notation (latex output) bounded2 ("(_ \<sqsubseteq>/ _/ '(\<^latex>\<open>\\textup{mod}\<close> _,_'))" [51,51,0,0])

lemma bounded_bot_top:
fixes v ab :: "'a::distrib_bounded_lattice"
shows "bounded \<bottom> \<top> v ab \<Longrightarrow> ab = v"
by (simp add: order_eq_iff)

text \<open>\<open>bounded\<close> implies eq-mod, but not the other way around:\<close>

text \<open>\<open>bounded\<close> implies eq-mod:\<close>
lemma eq_mod_if_bounded: assumes "bounded a b v ab"
shows "a \<squnion> ab \<sqinter> b = a \<squnion> v \<sqinter> (b::_::distrib_lattice)"
proof(rule antisym)
  have "a \<le> a \<squnion> v \<sqinter> b" by simp
  moreover have "ab \<sqinter> b \<le> a \<squnion> v \<sqinter> b"
  proof -
    have "ab \<sqinter> b \<le> (a \<squnion> v) \<sqinter> b" by(fact inf_mono[OF conjunct2[OF assms] order.refl])
    also have "\<dots> = a \<sqinter> b \<squnion> v \<sqinter> b" by (fact inf_sup_distrib2)
    also have "\<dots> \<le> a \<squnion> v \<sqinter> b" by (fact sup.mono[OF  inf.cobounded1 order.refl])
    finally show ?thesis .
  qed
  ultimately show "a \<squnion> ab \<sqinter> b \<le> a \<squnion> v \<sqinter> b" by(metis sup.bounded_iff)
next
  have "a \<le> a \<squnion> ab \<sqinter> b" by simp
  moreover have "v \<sqinter> b \<le> a \<squnion> ab \<sqinter> b"
  proof -
    have "v \<sqinter> b = (v \<sqinter> b) \<sqinter> b" by simp
    also have "\<dots> \<le> ab \<sqinter> b" by(metis inf.commute inf.mono[OF conjunct1[OF assms] order.refl])
    also have "\<dots> \<le> a \<squnion> ab \<sqinter> b" by simp
    finally show ?thesis .
  qed
  ultimately show "a \<squnion> v \<sqinter> b \<le> a \<squnion> ab \<sqinter> b" by(metis sup.bounded_iff)
qed

text \<open>Converse is not true, even for \<open>linorder\<close>, even if \<open>a < b\<close>:\<close>
lemma "let a=0; b=1; ab=2; v=1
  in a \<squnion> ab \<sqinter> b = a \<squnion> v \<sqinter> (b::nat) \<and> \<not>(b \<sqinter> v \<le> ab \<and> ab \<le> a \<squnion> v)"
by eval

text \<open>Because for \<open>linord\<close> we have:
  \<open>bounded = fishburn\<close> (@{thm fishburn_iff_min_max}) and \<open>eq_mod = knuth\<close> (@{thm mm_iff_knuth})
  but we know \<open>fishburn\<close> is stronger than \<open>knuth\<close>.

These equivalences do not even hold as implications in \<open>distrib_lattice\<close>, even if \<open>a < b\<close>.
(We need to redefine \<open>knuth\<close> and \<open>fishburn\<close> for \<open>distrib_lattice\<close> first)
\<close>

context
begin

definition
 "knuth' (a::_::distrib_lattice) b x y ==
  ((y \<le> a \<longrightarrow> x \<le> a) \<and> (a < y \<and> y < b \<longrightarrow> y = x) \<and> (b \<le> y \<longrightarrow> b \<le> x))"

lemma "let a={}; b={1::int}; ab={}; v={0}
  in \<not> (a \<squnion> ab \<sqinter> b = a \<squnion> v \<sqinter> b \<longrightarrow> knuth' a b v ab)"
by eval

lemma "let a={}; b={1::int}; ab={0}; v={1}
  in \<not> (knuth' a b v ab \<longrightarrow> a \<squnion> ab \<sqinter> b = a \<squnion> v \<sqinter> b)"
by eval

definition
 "fishburn' (a::_::distrib_lattice) b v ab ==
  ((ab \<le> a \<longrightarrow> v \<le> ab) \<and> (a < ab \<and> ab < b \<longrightarrow> ab = v) \<and> (b \<le> ab \<longrightarrow> ab \<le> v))"

text \<open>Same counterexamples as above:\<close>

lemma "let a={}; b={1::int}; ab={}; v={0}
  in \<not> (bounded a b v ab \<longrightarrow> fishburn' a b v ab)"
by eval

lemma "let a={}; b={1::int}; ab={0}; v={1}
  in \<not> (fishburn' a b v ab \<longrightarrow> bounded a b v ab)"
by eval

end

subsection \<open>Fail-Hard\<close>

subsubsection "Basic \<open>ab_sup\<close>"

text \<open>Improved version of Bird and Hughes. No squashing in base case.\<close>

fun ab_sup :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::distrib_lattice)tree \<Rightarrow> 'a" and ab_sups and ab_inf and ab_infs where
"ab_sup a b (Lf x) = x" |
"ab_sup a b (Nd ts) = ab_sups a b ts" |
"ab_sups a b [] = a" |
"ab_sups a b (t#ts) = (let a' = a \<squnion> ab_inf a b t in if a' \<ge> b then a' else ab_sups a' b ts)" |
"ab_inf a b (Lf x) = x" |
"ab_inf a b (Nd ts) = ab_infs a b ts" |
"ab_infs a b [] = b" |
"ab_infs a b (t#ts) = (let b' = b \<sqinter> ab_sup a b t in if b' \<le> a then b' else ab_infs a b' ts)"

lemma ab_sups_ge_a: "ab_sups a b ts \<ge> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def)(use le_sup_iff in blast)

lemma ab_infs_le_b: "ab_infs a b ts \<le> b"
apply(induction ts arbitrary: b)
by (auto simp: Let_def)(use le_inf_iff in blast)

lemma eq_mod_ab_val_auto:
shows "a \<squnion> ab_sup a b t \<sqinter> b = a \<squnion> supinf t \<sqinter> b"
and "a \<squnion> ab_sups a b ts \<sqinter> b = a \<squnion> supinf (Nd ts) \<sqinter> b"
and "a \<squnion> ab_inf a b t \<sqinter> b = a \<squnion> infsup t \<sqinter> b"
and "a \<squnion> ab_infs a b ts \<sqinter> b = a \<squnion> infsup (Nd ts) \<sqinter> b"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup_ab_sups_ab_inf_ab_infs.induct)
  case (4 a b t ts)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, ccfv_threshold) ab_sups_ge_a inf.absorb_iff2 inf_left_commute inf_sup_distrib2 sup.left_idem sup_absorb1 sup_absorb2 sup_assoc sup_inf_assoc_iff)
next
  case (8 a b t ts)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit) ab_infs_le_b inf.absorb_iff2 inf_assoc inf_commute inf_right_idem sup.absorb1 sup_inf_distrib1)
qed auto

text \<open>A readable proof. Some steps still tricky.
Complication: sometimes \<open>a \<squnion> x \<sqinter> b\<close> is better and sometimes \<open>(a \<squnion> x) \<sqinter> b\<close>.\<close>
lemma eq_mod_ab_val:
shows "a \<squnion> ab_sup a b t \<sqinter> b = a \<squnion> supinf t \<sqinter> b"
and "a \<squnion> ab_sups a b ts \<sqinter> b = a \<squnion> supinf (Nd ts) \<sqinter> b"
and "a \<squnion> ab_inf a b t \<sqinter> b = a \<squnion> infsup t \<sqinter> b"
and "a \<squnion> ab_infs a b ts \<sqinter> b = a \<squnion> infsup (Nd ts) \<sqinter> b"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup_ab_sups_ab_inf_ab_infs.induct)
  case (8 a b t ts)
  let ?abt = "ab_sup a b t" let ?abts = "ab_infs a (b \<sqinter> ?abt) ts"
  let ?vt = "supinf t" let ?vts = "infsup (Nd ts)"
  show ?case
  proof (cases "b \<sqinter> ?abt \<le> a")
    case True
    hence b: "a \<squnion> ?vt \<sqinter> b = a" using "8.IH"(1) True by (metis sup_absorb1 inf_commute)
    have "a \<squnion> ab_infs a b (t#ts) \<sqinter> b = a \<squnion> b \<sqinter> ?abt \<sqinter> b" using True by (simp)
    also have "\<dots> = a \<squnion> ?abt \<sqinter> b" by (simp add: inf_commute)
    also have "\<dots> = a \<squnion> ?vt \<sqinter> b" by (simp add: "8.IH"(1))
    also have "\<dots> = a \<squnion> (?vt \<squnion> ?vt \<sqinter> ?vts) \<sqinter> b" by (simp)
    also have "\<dots> = a \<squnion> (?vt \<sqinter> b \<squnion> ?vt \<sqinter> ?vts \<sqinter> b)" by (metis inf_sup_distrib2)
    also have "\<dots> = a \<squnion> ?vt \<sqinter> b \<squnion> ?vt \<sqinter> ?vts \<sqinter> b" by (metis sup_assoc)
    also have "\<dots> = a \<squnion> ?vt \<sqinter> ?vts \<sqinter> b" by (metis b)
    also have "\<dots> = a \<squnion> infsup (Nd (t # ts)) \<sqinter> b" by (simp)
    finally show ?thesis .
  next
    case False
    from "8.IH"(2)[OF refl False] ab_infs_le_b
    have IH2': "a \<squnion> ?abts \<sqinter> b = a \<squnion> ?vts \<sqinter> ?abt \<sqinter> b"
      by (metis (no_types, lifting) inf_absorb1 inf_assoc inf_commute inf_idem)
    have "a \<squnion> ab_infs a b (t#ts) \<sqinter> b = a \<squnion> ?abts \<sqinter> b" using False by (simp)
    also have "\<dots> = a \<squnion> ?abt \<sqinter> ?vts \<sqinter> b" using IH2' by (metis inf_commute)
    also have "\<dots> = a \<squnion> ?vt \<sqinter> ?vts \<sqinter> b" using "8.IH"(1)
      by (metis (no_types, lifting) inf_assoc inf_commute sup_inf_distrib1)
    also have "\<dots> = a \<squnion> infsup (Nd (t # ts)) \<sqinter> b" by (simp)
    finally show ?thesis .
  qed
next
  case (4 a b t ts)
  let ?abt = "ab_inf a b t" let ?abts = "ab_sups (a  \<squnion> ?abt) b ts"
  let ?vt = "infsup t" let ?vts = "supinf (Nd ts)"
  show ?case
  proof (cases "b \<le> a  \<squnion> ?abt")
    case True
    have IH1': \<open>(a \<squnion> ?abt) \<sqinter> b = (a \<squnion> ?vt) \<sqinter> b\<close> by(metis sup_inf_assoc_iff "4.IH"(1))
    hence b: "(a \<squnion> ?vt) \<sqinter> b = b" using True inf_absorb2 by metis
    have "(a \<squnion> ab_sups a b (t#ts)) \<sqinter> b = (a \<squnion> (a \<squnion> ?abt)) \<sqinter> b" using True by (simp)
    also have "\<dots> = (a \<squnion> ?abt) \<sqinter> b" by (simp)
    also have "\<dots> = (a \<squnion> ?vt) \<sqinter> b" by (simp add: IH1')
    also have "\<dots> = (a \<squnion> ?vt \<squnion> ?vts) \<sqinter> (a \<squnion> ?vt) \<sqinter> b" by (simp add: inf.absorb2)
    also have "\<dots> = (a \<squnion> ?vt \<squnion> ?vts) \<sqinter> b" by (simp add: b inf_assoc)
    also have "\<dots> = (a \<squnion> supinf (Nd (t # ts))) \<sqinter> b" by (simp add: sup.assoc)
    finally show ?thesis
      using sup_inf_assoc_iff by blast
  next
    case False
    from "4.IH"(2)[OF refl False] ab_sups_ge_a
    have IH2': "(a \<squnion> ?abts) \<sqinter> b = (a \<squnion> ?abt \<squnion> ?vts) \<sqinter> b"
      by (smt (verit, best) le_sup_iff sup_absorb2 sup_inf_assoc_iff)
    have "(a \<squnion> ab_sups a b (t#ts)) \<sqinter> b = (a \<squnion> ?abts) \<sqinter> b" using False by (simp)
    also have "\<dots> = (a \<squnion> ?abt \<squnion> ?vts) \<sqinter> b" using IH2' by blast
    also have "\<dots> = a \<sqinter> b \<squnion> ?abt \<sqinter> b \<squnion> ?vts \<sqinter> b" by (simp add: inf_sup_distrib2)
    also have "\<dots> = (a \<squnion> ?abt \<sqinter> b) \<sqinter> b \<squnion> ?vts \<sqinter> b" by (metis inf_sup_distrib2 inf.right_idem)
    also have "\<dots> = (a \<squnion> ?vt \<sqinter> b) \<sqinter> b \<squnion> ?vts \<sqinter> b" using "4.IH"(1) by simp 
    also have "\<dots> = (a \<squnion> ?vt \<squnion> ?vts) \<sqinter> b" by (simp add: inf_sup_distrib2)
    also have "\<dots> = (a \<squnion> supinf (Nd (t # ts))) \<sqinter> b" by (simp add: sup_assoc)
    finally show ?thesis
      using sup_inf_assoc_iff by blast
  qed
qed (simp_all)

corollary ab_sup_bot_top: "ab_sup \<bottom> \<top> t = supinf t"
by (metis eq_mod_ab_val(1) inf_top_right sup_bot.left_neutral)

text \<open>Predicate @{const knuth} (and thus @{const fishburn}) does not hold:\<close>
lemma "let a = {False}; b = {False, True}; t = Nd [Lf {True}];
  ab = ab_sup a b t; v = supinf t in v = {True} \<and> ab = {True,False} \<and> b \<le> ab \<and> \<not> b \<le> v"
by eval

text \<open>Worse: @{const fishburn} (and @{const knuth}) only caters for a ``linear'' analysis where \<open>ab\<close> lies wrt \<open>a < b\<close>.
But \<open>ab\<close> may not satisfy either of the 3 alternatives in @{const fishburn}:\<close>
lemma "let a = {}; b = {True}; t = Nd [Lf {False}]; ab = ab_sup a b t; v = supinf t in
  v = {False} \<and> ab={False} \<and> \<not> ab\<le>a \<and> \<not> ab\<ge>b \<and> \<not> (a<ab \<and> ab < b)"
by eval


subsubsection "A stronger correctness property"

text \<open>The stronger correctness property @{const bounded}:\<close>

lemma (*bounded_val_ab:*)
shows "bounded a b (supinf t) (ab_sup a b t)"
and   "bounded a b (supinf (Nd ts)) (ab_sups a b ts)"
and   "bounded a b (infsup t) (ab_inf a b t)"
and   "bounded a b (infsup (Nd ts)) (ab_infs a b ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup_ab_sups_ab_inf_ab_infs.induct)
  case (4 a b t ts)
  thus ?case
    apply(simp add: Let_def inf.coboundedI1 sup.coboundedI1)
    by (smt (verit, best) ab_sups_ge_a inf_sup_distrib1 sup.absorb_iff2 sup_assoc sup_commute)
next
  case (8 t ts a b)
  thus ?case
    apply(simp add: Let_def inf.coboundedI1 sup.coboundedI1)
    by (smt (verit) ab_infs_le_b inf.absorb_iff2 inf_commute inf_left_commute sup_inf_distrib1)
qed auto

lemma bounded_val_ab:
shows "bounded a b (supinf t) (ab_sup a b t)"
and   "bounded a b (supinf (Nd ts)) (ab_sups a b ts)"
and   "bounded a b (infsup t) (ab_inf a b t)"
and   "bounded a b (infsup (Nd ts)) (ab_infs a b ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup_ab_sups_ab_inf_ab_infs.induct)
  case (4 a b t ts)
  let ?abt = "ab_inf a b t" let ?abts = "ab_sups (a \<squnion> ?abt) b ts"
  let ?vt = "infsup t" let ?vts = "sups (map infsup ts)"
  have "b \<sqinter> supinf (Nd (t # ts)) \<le> ab_sups a b (t # ts)"
  proof -
    have "b \<sqinter> supinf (Nd (t # ts)) = b \<sqinter> (?vt \<squnion> ?vts)" by(simp)
    also have "\<dots> = b \<sqinter> ?vt \<squnion> b \<sqinter> ?vts" by (fact inf_sup_distrib1)
    also have "\<dots> \<le> ?abt \<squnion> b \<sqinter> ?vts" using "4.IH"(1) by (metis order.refl sup.mono)
    also have "\<dots> \<le> ab_sups a b (t # ts)"
    proof cases
      assume "b \<le> a \<squnion> ?abt"
      have "?abt \<squnion> b \<sqinter> ?vts \<le> a \<squnion> ?abt \<squnion> b \<sqinter> ?vts" by (simp add: sup_assoc)
      also have "\<dots> = a \<squnion> ?abt" using \<open>b \<le> a \<squnion> ?abt\<close> by (meson le_infI1 sup.absorb1)
      also have "\<dots> = ab_sups a b (t # ts)" using \<open>b \<le> a \<squnion> ?abt\<close> by simp
      finally show ?thesis .
    next
      assume "\<not> b \<le> a \<squnion> ?abt"
      have "?abt \<squnion> b \<sqinter> ?vts \<le> ?abt \<squnion> ?abts"
        using "4.IH"(2)[OF refl \<open>\<not> b \<le> a \<squnion> ?abt\<close>] sup.mono by auto
      also have "\<dots> \<le> ?abts" by (meson ab_sups_ge_a le_sup_iff order_refl)
      also have "\<dots> = ab_sups a b (t # ts)" using \<open>\<not> b \<le> a \<squnion> ?abt\<close> by simp
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  moreover
  have "ab_sups a b (t # ts) \<le> a \<squnion> supinf (Nd (t # ts))"
  proof cases
    assume "b \<le> a \<squnion> ?abt"
    then have "ab_sups a b (t # ts) = a \<squnion> ?abt" by(simp add: Let_def)
    also have "\<dots> \<le> a \<squnion> ?vt" using "4.IH"(1) by simp
    also have "\<dots> \<le> a \<squnion> ?vt \<squnion> ?vts" by simp
    also have "\<dots> = a \<squnion> supinf (Nd (t # ts))" by (simp add: sup_assoc)
    finally show ?thesis .
  next
    assume "\<not> b \<le> a \<squnion> ?abt"
    then have "ab_sups a b (t # ts) = ?abts" by(simp add: Let_def)
    also have "\<dots> \<le> a \<squnion> ?abt \<squnion> ?vts" using "4.IH"(2)[OF refl \<open>\<not> b \<le> a \<squnion> ?abt\<close>] by simp
    also have "\<dots> \<le> a \<squnion> ?vt \<squnion> ?vts" using "4.IH"(1)
      by (metis sup.mono inf_sup_absorb le_inf_iff sup.cobounded2 sup.idem)
    also have "\<dots> = a \<squnion> supinf (Nd (t # ts))" by (simp add: sup_assoc)
    finally show ?thesis .
  qed
  ultimately show ?case ..
next
  case 8 thus ?case
    apply(simp add: Let_def)
    by (smt (verit) ab_infs_le_b inf.absorb_iff2 inf.cobounded2 inf.orderE inf_assoc inf_idem sup.coboundedI1 sup_inf_distrib1)
qed auto


subsubsection "Bird and Hughes"

(* Exercise \ref{exer:ABlat:BH} (Bird and Hughes) for lattices *)

fun ab_sup2 :: "('a::distrib_lattice) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_sups2 and ab_inf2 and ab_infs2 where
"ab_sup2 a b (Lf x) = a \<squnion> x \<sqinter> b" |
"ab_sup2 a b (Nd ts) = ab_sups2 a b ts" |

"ab_sups2 a b [] = a" |
"ab_sups2 a b (t#ts) = (let a' = ab_inf2 a b t in if a' = b then b else ab_sups2 a' b ts)" |

"ab_inf2 a b (Lf x) = (a \<squnion> x) \<sqinter> b" |
"ab_inf2 a b (Nd ts) = ab_infs2 a b ts" |

"ab_infs2 a b [] = b" |
"ab_infs2 a b (t#ts) = (let b' = ab_sup2 a b t in if a = b' then a else ab_infs2 a b' ts)"

lemma eq_mod_ab2_val:
shows "a\<le>b \<Longrightarrow> ab_sup2 a b t = a \<squnion> (supinf t \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_sups2 a b ts = a \<squnion> (supinf (Nd ts) \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_inf2 a b t = (a \<squnion> infsup t) \<sqinter> b"
and "a\<le>b \<Longrightarrow> ab_infs2 a b ts = (a \<squnion> infsup(Nd ts)) \<sqinter> b"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup2_ab_sups2_ab_inf2_ab_infs2.induct)
  case 4 thus ?case
    apply (simp add: Let_def)
    by (smt (verit, best) inf_commute inf_sup_distrib2 sup_assoc sup_inf_absorb sup_inf_assoc)
next
  case 8 thus ?case
    apply (simp add: Let_def)
    by (smt (verit, del_insts) inf_assoc inf_commute inf_sup_absorb sup_inf_assoc sup_inf_distrib1)
qed simp_all

corollary ab_sup2_bot_top: "ab_sup2 \<bottom> \<top> t = supinf t"
using eq_mod_ab2_val(1)[of \<bottom> \<top>] by simp

text \<open>Simpler proof with sets; not really surprising.\<close>
lemma ab_sup2_bounded_set:
shows "a\<le>(b:: _ set) \<Longrightarrow> ab_sup2 a b t = a \<squnion> (supinf t \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_sups2 a b ts = a \<squnion> (supinf (Nd ts) \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_inf2 a b t = (a \<squnion> infsup t) \<sqinter> b"
and "a\<le>b \<Longrightarrow> ab_infs2 a b ts = (a \<squnion> infsup(Nd ts)) \<sqinter> b"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup2_ab_sups2_ab_inf2_ab_infs2.induct)
qed (auto simp: Let_def)


subsubsection "Delayed Test"

(* Exercise: delayed test, version for distributive lattices; no proof (yet)! *)

fun ab_sup3 :: "('a::distrib_lattice) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_sups3 and ab_inf3 and ab_infs3 where
"ab_sup3 a b (Lf x) = x" |
"ab_sup3 a b (Nd ts) = ab_sups3 a b ts" |

"ab_sups3 a b [] = a" |
"ab_sups3 a b (t#ts) = (if a \<ge> b then a else ab_sups3 (a \<squnion> ab_inf3 a b t) b ts)" |

"ab_inf3 a b (Lf x) = x" |
"ab_inf3 a b (Nd ts) = ab_infs3 a b ts" |

"ab_infs3 a b [] = b" |
"ab_infs3 a b (t#ts) = (if a \<ge> b then b else ab_infs3 a (b \<sqinter> ab_sup3 a b t) ts)"

(* Unused. In case they are needed for the failed proof directly below. *)
lemma ab_sups3_ge_a: "ab_sups3 a b ts \<ge> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def)(use le_sup_iff in blast)

lemma ab_infs3_le_b: "ab_infs3 a b ts \<le> b"
apply(induction ts arbitrary: b)
by (auto simp: Let_def)(use le_inf_iff in blast)

(* Failed to prove it. Probably needs lemmas *)
lemma ab_sup3_ab_sup:
shows "a<b \<Longrightarrow> ab_sup3 a b t = ab_sup a b t"
and "a<b \<Longrightarrow> ab_sups3 a b ts = ab_sups a b ts"
and "a<b \<Longrightarrow> ab_inf3 a b t = ab_inf a b t"
and "a<b \<Longrightarrow> ab_infs3 a b ts = ab_infs a b ts"
quickcheck[expect=no_counterexample]
oops
(*
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup3_ab_sups3_ab_inf3_ab_infs3.induct)
  case (4 a b t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using 4 by (auto simp add: Let_def dest: leD)
  next
    case Cons
    then show ?thesis using 4 apply (auto simp add: Let_def )
  qed
next
  case (8 a b t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using 8 by (simp add: Let_def)
  next
    case Cons
    then show ?thesis using 8 by (auto simp add: Let_def min_le_iff_disj)
  qed
qed auto
*)


subsubsection "Bird and Hughes plus delayed test"

(* Exercise Bird and Hughes, delayed! - unused in book, a bit esoteric *)

fun ab_sup4 :: "('a::distrib_lattice) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_sups4 and ab_inf4 and ab_infs4 where
"ab_sup4 a b (Lf x) = a \<squnion> x \<sqinter> b" |
"ab_sup4 a b (Nd ts) = ab_sups4 a b ts" |

"ab_sups4 a b [] = a" |
"ab_sups4 a b (t#ts) = (if a = b then a else ab_sups4 (ab_inf4 a b t) b ts)" |

"ab_inf4 a b (Lf x) = (a \<squnion> x) \<sqinter> b" |
"ab_inf4 a b (Nd ts) = ab_infs4 a b ts" |

"ab_infs4 a b [] = b" |
"ab_infs4 a b (t#ts) = (if a = b then b else ab_infs4 a (ab_sup4 a b t) ts)"

(* TODO: no need for \<open>a\<le>b\<close> for linord *)
lemma ab_sup4_bounded:
shows "a\<le>b \<Longrightarrow> ab_sup4 a b t = a \<squnion> (supinf t \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_sups4 a b ts = a \<squnion> (supinf (Nd ts) \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_inf4 a b t = (a \<squnion> infsup t) \<sqinter> b"
and "a\<le>b \<Longrightarrow> ab_infs4 a b ts = (a \<squnion> infsup(Nd ts)) \<sqinter> b"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup4_ab_sups4_ab_inf4_ab_infs4.induct)
  case 3 thus ?case by (simp add: sup_absorb1)
next
  case 4 thus ?case
    apply (simp add: sup_absorb1)
    by (metis (no_types, lifting) inf_sup_distrib2 sup_assoc sup_inf_assoc)
next
  case 7 thus ?case by (simp add: inf.absorb2)
next
  case (8 a b t ts)
  then show ?case
  apply (simp add: inf.absorb2)
  by (simp add: inf_assoc inf_commute sup_absorb2 sup_inf_distrib1)
qed simp_all

lemma ab_sup4_bounded_set:
shows "a\<le>(b:: _ set) \<Longrightarrow> ab_sup4 a b t = a \<squnion> (supinf t \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_sups4 a b ts = a \<squnion> (supinf (Nd ts) \<sqinter> b)"
and "a\<le>b \<Longrightarrow> ab_inf4 a b t = (a \<squnion> infsup t) \<sqinter> b"
and "a\<le>b \<Longrightarrow> ab_infs4 a b ts = (a \<squnion> infsup(Nd ts)) \<sqinter> b"
by (induction a b t and a b ts and a b t and a b ts rule: ab_sup4_ab_sups4_ab_inf4_ab_infs4.induct)
   auto


subsection \<open>Fail-Soft\<close>

fun ab_sup' :: "'a::distrib_bounded_lattice \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_sups' ab_inf' ab_infs' where
"ab_sup' a b (Lf x) = x" |
"ab_sup' a b (Nd ts) = ab_sups' a b \<bottom> ts" |

"ab_sups' a b m [] = m" |
"ab_sups' a b m (t#ts) =
  (let m' = m \<squnion> (ab_inf' (m \<squnion> a) b t) in if m' \<ge> b then m' else ab_sups' a b m' ts)" |

"ab_inf' a b (Lf x) = x" |
"ab_inf' a b (Nd ts) = ab_infs' a b \<top> ts" |

"ab_infs' a b m [] = m" |
"ab_infs' a b m (t#ts) =
  (let m' = m \<sqinter> (ab_sup' a (m \<sqinter> b) t) in if m' \<le> a then m' else ab_infs' a b m' ts)"


lemma ab_sups'_ge_m: "ab_sups' a b m ts \<ge> m"
apply(induction ts arbitrary: a b m)
by (auto simp: Let_def)(use le_sup_iff in blast)

lemma ab_infs'_le_m: "ab_infs' a b m ts \<le> m"
apply(induction ts arbitrary: a b m)
by (auto simp: Let_def)(use le_inf_iff in blast)

text \<open>Fail-soft correctness:\<close>

lemma bounded_val_ab':
shows "bounded (a) b (supinf t) (ab_sup' a b t)"
and   "bounded (a \<squnion> m) b (supinf (Nd ts)) (ab_sups' a b m ts)"
and   "bounded a b (infsup t) (ab_inf' a b t)"
and   "bounded a (b \<sqinter> m) (infsup (Nd ts)) (ab_infs' a b m ts)"
proof(induction a b t and a b m ts and a b t and a b m ts rule: ab_sup'_ab_sups'_ab_inf'_ab_infs'.induct)
  case (4 a b m t ts)
  then show ?case
    apply(simp add: Let_def inf.coboundedI1 sup.coboundedI1)
    by (smt (verit) ab_sups'_ge_m inf_sup_distrib1 sup.absorb_iff1 sup_commute sup_left_commute)
next
  case (8 a b m t ts)
  then show ?case
    apply(simp add: Let_def inf.coboundedI1 sup.coboundedI1)
    by (smt (verit) ab_infs'_le_m inf.absorb_iff2 inf_assoc inf_left_commute sup_inf_distrib1)
qed auto

corollary "ab_sup' \<bottom> \<top> t = supinf t"
by (rule bounded_bot_top[OF bounded_val_ab'(1)])

lemma eq_mod_ab'_val:
shows "a \<squnion> ab_sup' a b t \<sqinter> b = a \<squnion> supinf t \<sqinter> b"
and "(m \<squnion> a) \<squnion> ab_sups' a b m ts \<sqinter> b = (m \<squnion> a) \<squnion> supinf (Nd ts) \<sqinter> b"
and "a \<squnion> ab_inf' a b t \<sqinter> b = a \<squnion> infsup t \<sqinter> b"
and "a \<squnion> ab_infs' a b m ts \<sqinter> (m \<sqinter> b) = a \<squnion> infsup (Nd ts) \<sqinter> (m \<sqinter> b)"
  apply (meson bounded_val_ab'(1) eq_mod_if_bounded)
  apply (metis bounded_val_ab'(2) eq_mod_if_bounded sup_commute)
  apply (meson bounded_val_ab'(3) eq_mod_if_bounded)
  by (metis bounded_val_ab'(4) eq_mod_if_bounded inf_commute)
(* direct proof also possible:
proof(induction a b t and a b m ts and a b t and a b m ts rule: ab_sup'_ab_sups'_ab_inf'_ab_infs'.induct)
  case (4 a b m t ts)
  then show ?case
    apply(simp add: Let_def)
    apply rule
    apply (smt (verit, ccfv_threshold) inf.absorb_iff2 inf_sup_absorb le_infE sup.idem sup_assoc sup_commute sup_inf_distrib1)
    by (smt (verit, ccfv_SIG) ab_sups'_ge_m inf_sup_distrib2 sup.cobounded1 sup.orderE sup_assoc sup_commute sup_inf_assoc_iff)
next
  case (8 a b m t ts)
  then show ?case
    apply( simp add: Let_def)
    apply rule
    apply (smt (verit, ccfv_SIG) inf.coboundedI1 inf_assoc inf_left_commute sup.orderE sup_inf_assoc_iff sup_inf_distrib1)
    by (smt (verit, ccfv_SIG) ab_infs'_le_m inf.cobounded1 inf.orderE inf_assoc inf_commute sup_inf_assoc_iff)
next
  case 3 thus ?case
    by (metis bounded_val_ab'(2) eq_mod_if_bounded sup.commute)
qed auto
*)

(* useful? *)
lemma ab_sups'_le_ab_sups: "ab_sups' a b c t \<sqinter> b \<le> ab_sups (a \<squnion> c) b t"
by (smt (verit, best) ab_sups_ge_a bounded_val_ab(2) eq_mod_ab'_val(2) inf_commute sup.absorb_iff2 sup_assoc sup_commute)

(* useful? *)
lemma ab_sup'_le_ab_sup: "ab_sup' a b t \<sqinter> b \<le> ab_sup a b t"
by (metis ab_sup'.elims ab_sup.simps(1) ab_sup.simps(2) ab_sups'_le_ab_sups inf.cobounded1 sup_bot_right)


subsubsection \<open>Towards \<open>bounded\<close> of Fail-Soft\<close>

theorem bounded_ab'_ab:
  shows "bounded (a) b (ab_sup' a b t)   (ab_sup a b t)"
    and "bounded a b (ab_sups' a b m ts) (ab_sups (sup m a) b ts)"
    and "bounded a b (ab_inf' a b t)   (ab_inf a b t)"
    and "bounded a b (ab_infs' a b m ts) (ab_infs a (inf m b) ts)"
oops


section \<open>De Morgan Algebras\<close>

text \<open>Now: also negation. But still not a boolean algebra but only a De Morgan algebra:\<close>

(* Modified copy of \<open>de_morgan_order\<close>; cannot be shared because of max vs sup *)
class de_morgan_algebra = distrib_bounded_lattice + uminus
opening lattice_syntax +
assumes de_Morgan_inf: "- (x \<sqinter> y) = - x \<squnion> - y"
assumes neg_neg[simp]: "- (- x) = x"
begin

lemma de_Morgan_sup: "- (x \<squnion> y) = - x \<sqinter> - y"
by (metis de_Morgan_inf neg_neg)

lemma neg_top[simp]: "- \<top> = \<bottom>"
by (metis bot_eq_sup_iff de_Morgan_inf inf_top.right_neutral neg_neg)

lemma neg_bot[simp]: "- \<bottom> = \<top>"
using neg_neg neg_top by blast

lemma uminus_eq_iff[simp]: "-a = -b \<longleftrightarrow> a = b"
by (metis neg_neg)

lemma uminus_le_reorder: "(- a \<le> b) = (- b \<le> a)"
by (metis de_Morgan_sup inf.absorb_iff2 le_iff_sup neg_neg)

lemma uminus_less_reorder: "(- a < b) = (- b < a)"
by (metis order.strict_iff_not neg_neg uminus_le_reorder)

lemma minus_le_minus[simp]: "- a \<le> - b \<longleftrightarrow> b \<le> a"
by (metis neg_neg uminus_le_reorder)

lemma minus_less_minus[simp]: "- a < - b \<longleftrightarrow> b < a"
by (metis neg_neg uminus_less_reorder)

lemma less_uminus_reorder: "a < - b \<longleftrightarrow> b < - a"
by (metis neg_neg uminus_less_reorder)

end

instantiation ereal :: de_morgan_algebra
begin

instance
proof (standard, goal_cases)
  case 1
  thus ?case by (simp add: min_def)
next
  case 2
  thus ?case by (simp)
qed

end

instantiation set :: (type)de_morgan_algebra
begin

instance
proof (standard, goal_cases)
  case 1
  thus ?case by (simp)
next
  case 2
  thus ?case by (simp)
qed

end

fun negsup :: "('a :: de_morgan_algebra)tree \<Rightarrow> 'a" where
"negsup (Lf x) = x" |
"negsup (Nd ts) = sups (map (\<lambda>t. - negsup t) ts)"

fun negate :: "bool \<Rightarrow> ('a::de_morgan_algebra) tree \<Rightarrow> 'a tree" where
"negate b (Lf x) = Lf (if b then -x else x)" |
"negate b (Nd ts) = Nd (map (negate (\<not>b)) ts)"

lemma negate_negate: "negate f (negate f t) = t"
by(induction t arbitrary: f)(auto cong: map_cong)

lemma uminus_infs:
  fixes f :: "'a \<Rightarrow> 'b::de_morgan_algebra"
shows "- infs (map f xs) = sups (map (\<lambda>x. - f x) xs)"
by(induction xs) (auto simp: de_Morgan_inf)

lemma supinf_negate: "supinf (negate b t) = - infsup (negate (\<not>b) (t::(_::de_morgan_algebra)tree))"
by(induction t) (auto simp: uminus_infs cong: map_cong)

lemma negsup_supinf_negate: "negsup t = supinf(negate False t)"
by(induction t) (auto simp: supinf_negate cong: map_cong)


subsection \<open>Fail-Hard\<close>

fun ab_negsup :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::de_morgan_algebra)tree \<Rightarrow> 'a" and ab_negsups where
"ab_negsup a b (Lf x) = x" |
"ab_negsup a b (Nd ts) = ab_negsups a b ts" |

"ab_negsups a b [] = a" |
"ab_negsups a b (t#ts) =
  (let a' = a \<squnion> - ab_negsup (-b) (-a) t
   in if a' \<ge> b then a' else ab_negsups a' b ts)"

text \<open>A direct \<open>bounded\<close> proof:\<close>

lemma ab_negsups_ge_a: "ab_negsups a b ts \<ge> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def)(use le_sup_iff in blast)

lemma bounded_val_ab_neg:
shows "bounded (a) b (negsup t) (ab_negsup (a) b t)"
and "bounded a b (negsup (Nd ts)) (ab_negsups (a) b ts)"
proof(induction a b t and a b ts rule: ab_negsup_ab_negsups.induct)
  case (4 a b t ts)
  then show ?case
    apply(simp add: Let_def inf.coboundedI1)
    by (smt (verit, ccfv_threshold) ab_negsups_ge_a de_Morgan_sup de_morgan_algebra_class.neg_neg inf.absorb_iff2 inf_sup_distrib1 le_iff_sup sup_commute sup_left_commute)
qed auto

text \<open>An indirect proof:\<close>

theorem ab_sup_ab_negsup:
shows "ab_sup a b t = ab_negsup a b (negate False t)"
and   "ab_sups a b ts = ab_negsups a b (map (negate True) ts)"
and   "ab_inf a b t = - ab_negsup (-b) (-a) (negate True t)"
and   "ab_infs a b ts = - ab_negsups (-b) (-a) (map (negate False) ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_sup_ab_sups_ab_inf_ab_infs.induct)
  case 8 then show ?case
    by(simp add: Let_def de_Morgan_sup de_Morgan_inf uminus_le_reorder)
qed (simp_all add: Let_def)

corollary ab_negsup_bot_top: "ab_negsup \<bottom> \<top> t = negsup t"
by (metis ab_sup_bot_top ab_sup_ab_negsup(1) negate_negate negsup_supinf_negate)

text \<open>Correctness statements derived from non-negative versions:\<close>

corollary eq_mod_ab_negsup_supinf_negate:
  "a \<squnion> ab_negsup a b t \<sqinter> b = a \<squnion> supinf (negate False t) \<sqinter> b"
by (metis eq_mod_ab_val(1) ab_sup_ab_negsup(1) negate_negate)

corollary bounded_negsup_ab_negsup:
  "bounded a b (negsup t) (ab_negsup a b t)"
by (metis negate_negate ab_sup_ab_negsup(1) bounded_val_ab(1) negsup_supinf_negate)


subsection \<open>Fail-Soft\<close>

fun ab_negsup' :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::de_morgan_algebra)tree \<Rightarrow> 'a" and ab_negsups' where
"ab_negsup' a b (Lf x) = x" |
"ab_negsup' a b (Nd ts) = (ab_negsups' a b \<bottom> ts)" |

"ab_negsups' a b m [] = m" |
"ab_negsups' a b m (t#ts) = (let m' = sup m (- ab_negsup' (-b) (- sup m a) t) in
      if m' \<ge> b then m' else ab_negsups' a b m' ts)"

text \<open>Relate un-negated to negated:\<close>

theorem ab_sup'_ab_negsup':
shows "ab_sup' a b t = ab_negsup' a b (negate False t)"
and   "ab_sups' a b m ts = ab_negsups' a b m (map (negate True) ts)"
and   "ab_inf' a b t = - ab_negsup' (-b) (-a) (negate True t)"
and   "ab_infs' a b m ts = - ab_negsups' (-b) (-a) (-m) (map (negate False) ts)"
proof(induction a b t and a b m ts and a b t and a b m ts rule: ab_sup'_ab_sups'_ab_inf'_ab_infs'.induct)
  case (4 a b m t ts)
  then show ?case
    by(simp add: Let_def de_Morgan_sup de_Morgan_inf uminus_le_reorder)
next
  case (8 a b m t ts)
  then show ?case
    by(simp add: Let_def de_Morgan_sup de_Morgan_inf uminus_le_reorder)
qed auto

lemma ab_negsups'_ge_a: "ab_negsups' a b m ts \<ge> m"
apply(induction ts arbitrary: a b m)
by (auto simp: Let_def)(use le_sup_iff in blast)

theorem bounded_val_ab'_neg:
shows "bounded a b (negsup t) (ab_negsup' a b t)"
  and "bounded (sup a m) b (negsup (Nd ts)) (ab_negsups' a b m ts)"
proof(induction a b t and a b m ts rule: ab_negsup'_ab_negsups'.induct)
 case (4 a b m t ts)
  then show ?case
    apply (auto simp add: Let_def inf.coboundedI1 sup.coboundedI1)
    apply (smt (verit, ccfv_threshold) de_Morgan_sup neg_neg inf.coboundedI1 le_iff_sup sup.cobounded1 sup_assoc sup_commute)
    apply (metis (no_types, lifting) ab_negsups'_ge_a de_Morgan_sup neg_neg inf.coboundedI1 inf_sup_distrib1 le_iff_sup le_sup_iff)
    by (smt (verit, ccfv_threshold) de_Morgan_inf de_morgan_algebra_class.neg_neg inf.orderE le_iff_sup sup.idem sup_commute sup_left_commute)
qed auto

(* Can also derive \<open>bounded_ab_negsup'_negsup(1)\<close> from the corresponding un-negated thm: *)
corollary "bounded a b (negsup t) (ab_negsup' a b t)"
by (metis negate_negate ab_sup'_ab_negsup'(1) bounded_val_ab'(1) negsup_supinf_negate)
(* But why not (it seems) \<open>bounded_ab_negsup'_negsup(2)\<close> ? *)

(* Just as unproved as \<open>bounded a b (ab_sup' t a b) (ab_sup a b t)\<close> *)
theorem bounded_ab_neg'_ab_neg:
shows "bounded a b (ab_negsup' a b t) (ab_negsup a b t)"
  and "bounded (sup a m) b (ab_negsups' a b m ts) (ab_negsup (a \<squnion> m) b (Nd ts))"
oops

end
