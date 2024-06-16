chapter \<open>Linear Orders\<close>

theory Alpha_Beta_Linear
imports
  "HOL-Library.Extended_Real" (* for quickcheck purposes *)
begin

section \<open>Classes\<close>

notation
  bot ("\<bottom>") and
  top ("\<top>")

class bounded_linorder = linorder + order_top + order_bot
begin

lemma bounded_linorder_collapse:
assumes "\<not> \<bottom> < \<top>" shows "(x::'a) = y"
proof -
  from assms have "\<top> \<le> \<bottom>" by(rule leI)
  have "x = \<top>" using order.trans[OF \<open>\<top> \<le> \<bottom>\<close> bot_least[of x]] top_unique by metis
  moreover
  have "y = \<top>" using order.trans[OF \<open>\<top> \<le> \<bottom>\<close> bot_least[of y]] top_unique by metis
  ultimately show ?thesis by blast
qed

end

class de_morgan_order = bounded_linorder + uminus +
assumes de_morgan_min: "- min x y = max (- x) (- y)"
assumes neg_neg[simp]: "- (- x) = x"
begin

lemma de_morgan_max: "- max x y = min (- x) (- y)"
by (metis de_morgan_min neg_neg)

lemma neg_top[simp]: "- \<top> = \<bottom>"
by (metis de_morgan_max max_top2 min_bot neg_neg)

lemma neg_bot[simp]: "- \<bottom> = \<top>"
using neg_neg neg_top by blast

lemma uminus_eq_iff[simp]: "-a = -b \<longleftrightarrow> a = b"
by (metis neg_neg)

lemma uminus_le_reorder: "(- a \<le> b) = (- b \<le> a)"
by (metis de_morgan_max max.absorb_iff1 min.absorb_iff1 neg_neg)

lemma uminus_less_reorder: "(- a < b) = (- b < a)"
by (metis order.strict_iff_not neg_neg uminus_le_reorder)

lemma minus_le_minus[simp]: "- a \<le> - b \<longleftrightarrow> b \<le> a"
by (metis neg_neg uminus_le_reorder)

lemma minus_less_minus[simp]: "- a < - b \<longleftrightarrow> b < a"
by (metis neg_neg uminus_less_reorder)

lemma less_uminus_reorder: "a < - b \<longleftrightarrow> b < - a"
by (metis neg_neg uminus_less_reorder)

end

(* For quickcheck: *)

instance bool :: bounded_linorder ..

instantiation ereal :: de_morgan_order
begin

instance
proof (standard, goal_cases)
  case 1
  thus ?case
    by (simp add: max_def)
next
  case 2
  thus ?case by (simp add: min_def)
qed

end


section \<open>Game Tree Evaluation\<close>

datatype 'a tree = Lf 'a | Nd "'a tree list"

datatype_compat tree

fun maxs :: "('a::bounded_linorder) list \<Rightarrow> 'a" where
"maxs [] = \<bottom>" |
"maxs (x#xs) = max x (maxs xs)"

fun mins :: "('a::bounded_linorder) list \<Rightarrow> 'a"where
"mins [] = \<top>" |
"mins (x#xs) = min x (mins xs)"

fun maxmin :: "('a::bounded_linorder) tree \<Rightarrow> 'a"
and minmax :: "('a::bounded_linorder) tree \<Rightarrow> 'a" where
"maxmin (Lf x) = x" |
"maxmin (Nd ts) = maxs (map minmax ts)" |
"minmax (Lf x) = x" |
"minmax (Nd ts) = mins (map maxmin ts)"

text \<open>Cannot use @{const Max} instead of \<open>maxs\<close> because @{term "Max {}"} is undefined.\<close>

text \<open>No need for bounds if lists are nonempty:\<close>

fun invar :: "'a tree \<Rightarrow> bool" where
"invar (Lf x) = True" |
"invar (Nd ts) = (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. invar t))"

fun maxs1 :: "('a::linorder) list \<Rightarrow> 'a" where
"maxs1 [x] = x" |
"maxs1 (x#xs) = max x (maxs1 xs)"

fun mins1 :: "('a::linorder) list \<Rightarrow> 'a"where
"mins1 [x] = x" |
"mins1 (x#xs) = min x (mins1 xs)"

fun maxmin1 :: "('a::bounded_linorder) tree \<Rightarrow> 'a"
and minmax1 :: "('a::bounded_linorder) tree \<Rightarrow> 'a" where
"maxmin1 (Lf x) = x" |
"maxmin1 (Nd ts) = maxs1 (map minmax1 ts)" |
"minmax1 (Lf x) = x" |
"minmax1 (Nd ts) = mins1 (map maxmin1 ts)"

lemma maxs1_maxs: "xs \<noteq> [] \<Longrightarrow> maxs1 xs = maxs xs"
by(induction xs rule: maxs1.induct) auto

lemma mins1_mins: "xs \<noteq> [] \<Longrightarrow> mins1 xs = mins xs"
by(induction xs rule: mins1.induct) auto

lemma maxmin1_maxmin:
shows "invar t \<Longrightarrow> maxmin1 t = maxmin t"
and   "invar t \<Longrightarrow> minmax1 t = minmax t"
proof(induction t rule: maxmin1_minmax1.induct)
  case 2 thus ?case by (simp add: maxs1_maxs cong: map_cong)
next
  case 4 thus ?case by (simp add: mins1_mins cong: map_cong)
qed auto


subsection \<open>Parameterized by the orderings\<close>

fun maxs_le :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"maxs_le bo le [] = bo" |
"maxs_le bo le (x#xs) = (let m = maxs_le bo le xs in if le x m then m else x)"

fun maxmin_le :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> 'a" where
"maxmin_le _  _ _ (Lf x) = x" |
"maxmin_le bo to le (Nd ts) = maxs_le bo le (map (maxmin_le to bo (\<lambda>x y. le y x)) ts)"

lemma maxs_le_maxs: "maxs_le \<bottom> (\<le>) xs = maxs xs"
by(induction xs) (auto simp: Let_def)

lemma maxs_le_mins: "maxs_le \<top> (\<ge>) xs = mins xs"
by(induction xs) (auto simp: Let_def)

lemma maxmin_le_maxmin:
  shows "maxmin_le \<bottom> \<top> (\<le>) t = maxmin  t"
  and   "maxmin_le \<top> \<bottom> (\<ge>) t = minmax t"
by(induction t and t rule: maxmin_minmax.induct)
  (auto simp add: Let_def max_def maxs_le_maxs maxs_le_mins cong: map_cong)


subsection \<open>Negamax: de Morgan orders\<close>

fun negmax :: "('a::de_morgan_order) tree \<Rightarrow> 'a" where
"negmax (Lf x) = x" |
"negmax (Nd ts) = maxs (map (\<lambda>t. - negmax t) ts)"

lemma de_morgan_mins:
fixes f :: "'a \<Rightarrow> 'b::de_morgan_order"
shows "- mins (map f xs) = maxs (map (\<lambda>x. - f x) xs)"
by(induction xs)(auto simp: de_morgan_min)

fun negate :: "bool \<Rightarrow> ('a::de_morgan_order) tree \<Rightarrow> ('a::de_morgan_order) tree" where
"negate b (Lf x) = Lf (if b then -x else x)" |
"negate b (Nd ts) = Nd (map (negate (\<not>b)) ts)"

lemma negate_negate: "negate f (negate f t) = t"
by(induction t arbitrary: f)(auto cong: map_cong)

lemma maxmin_negmax: "maxmin t = negmax (negate False t)"
and  minmax_negmax: "minmax t = - negmax (negate True t)"
by(induction t and t rule: maxmin_minmax.induct)
  (auto simp flip: de_morgan_mins cong: map_cong)

(* verbose only for presentation reasons (book) *)
lemma "maxmin t = negmax (negate False t)"
and  "minmax t = - negmax (negate True t)"
proof(induction t and t rule: maxmin_minmax.induct)
  case (2 ts)
  have "maxmin (Nd ts) = maxs (map minmax ts)"
    by simp
  also have "\<dots> = maxs (map (\<lambda>t. - negmax (negate True t)) ts)"
    using "2.IH" by (simp cong: map_cong)
  also have "\<dots> = maxs (map ((\<lambda>t. - negmax t) o (negate True)) ts)"
    by (metis comp_apply)
  also have "\<dots> = maxs (map (\<lambda>t. - negmax t) (map (negate True) ts))"
    by(simp)
  also have "\<dots> = negmax (Nd (map (negate True) ts))"
    by simp
  also have "\<dots> = negmax (negate False (Nd ts))"
    by simp
  finally show ?case .
next
  case (4 ts)
  have "minmax (Nd ts) = mins (map maxmin ts)"
    by simp
  also have "\<dots> = mins (map (\<lambda>t. negmax (negate False t)) ts)"
    using "4.IH" by (simp cong: map_cong)
  also have "\<dots> = - (- mins (map (\<lambda>t. negmax (negate False t)) ts))"
    by simp
  also have "\<dots> = - maxs (map (\<lambda>t. - negmax (negate False t)) ts)"
    by(simp only: de_morgan_mins)
  also have "\<dots> = - maxs (map ((\<lambda>t. - negmax t) o (negate False)) ts)"
    by (metis comp_apply)
  also have "\<dots> = - maxs (map (\<lambda>t. - negmax t) (map (negate False) ts))"
    by(simp)
  also have "\<dots> = - negmax (Nd (map (negate False) ts))"
    by simp
  also have "\<dots> = - negmax (negate True (Nd ts))"
    by simp
  finally show ?case .
qed (auto)

lemma shows negmax_maxmin: "negmax t = maxmin(negate False t)"
and "negmax t = - minmax(negate True t)"
  apply (simp add: maxmin_negmax negate_negate)
  by (simp add: minmax_negmax negate_negate)
(* verbose
proof(induction t and t rule: maxmin_minmax.induct)
  case (2 ts) (* verbose only for presentation reasons (book) *)
  have "negmax(Nd ts) = maxs (map (\<lambda>t. - negmax t) ts)" by simp
  also have "\<dots> = maxs (map (\<lambda>t. - (- minmax (negate True t))) ts)"
    using "2.IH" by (simp cong: map_cong)
  also have "\<dots> = maxs (map (\<lambda>t. minmax (negate True t)) ts)" by simp
  also have "\<dots> = maxs (map (minmax o negate True) ts)"
    by (metis comp_apply)
  also have "\<dots> = maxs (map minmax (map (negate True) ts))"
    by simp
  also have "\<dots> = maxmin (Nd (map (negate True) ts))"
    by (rule maxmin.simps(2)[symmetric])
  also have "\<dots> = maxmin (negate False (Nd ts))" by simp
  finally show ?case .
next
  case (4 ts) (* verbose only for presentation reasons (book) *)
  have "negmax(Nd ts) = maxs (map (\<lambda>t. - negmax t) ts)" by simp
  also have "\<dots> = maxs (map (\<lambda>t. - maxmin (negate False t)) ts)"
    using "4.IH" by (simp cong: map_cong)
  also have "\<dots> = - mins (map (\<lambda>t. maxmin (negate False t)) ts)" by(simp add: de_morgan_mins)
  also have "\<dots> = - mins (map (maxmin o negate False) ts)"
    by (metis comp_apply)
  also have "\<dots> = - mins (map maxmin (map (negate False) ts))"
    by simp
  also have "\<dots> = - minmax (Nd (map (negate False) ts))"
    by (simp)
  also have "\<dots> = - minmax (negate True (Nd ts))" by simp
  finally show ?case .
qed (auto simp add: de_morgan_mins cong: map_cong) (* could prove every case *)
*)

lemma maxs_append: "maxs (xs @ ys) = max (maxs xs) (maxs ys)"
by(induction xs) (auto simp: max.assoc)

lemma maxs_rev: "maxs (rev xs) = maxs xs"
by(induction xs) (auto simp: max.commute maxs_append)


section "Specifications"


subsection "The squash operator \<open>max a (min x b)\<close>"

abbreviation mm where "mm a x b == min (max a x) b"

lemma max_min_commute: "(a::_::linorder) \<le> b \<Longrightarrow> max a (min x b) = min b (max x a)"
by (metis max.absorb2 max.commute min.commute max_min_distrib1)

lemma max_min_commute2: "(a::_::linorder) \<le> b \<Longrightarrow> max a (min x b) = min (max a x) b"
by (metis max.absorb2 max.commute max_min_distrib1)

lemma max_min_neg: "a<b \<Longrightarrow> max (a::_::de_morgan_order) (min x b) = - max (-b) (min (-x) (-a))"
by(simp add: max_min_commute de_morgan_min de_morgan_max)


subsection \<open>Fail-Hard and Soft\<close>

text \<open>Specification of fail-hard; symmetric in \<open>x\<close> and \<open>y\<close>!\<close>
abbreviation
 "knuth (a::_::linorder) b x y ==
  ((y \<le> a \<longrightarrow> x \<le> a) \<and> (a < y \<and> y < b \<longrightarrow> y = x) \<and> (b \<le> y \<longrightarrow> b \<le> x))"

lemma knuth_bot_top: "knuth \<bottom> \<top> x y \<Longrightarrow> x = (y::_::bounded_linorder)"
by (metis bot.extremum_uniqueI linorder_le_less_linear top.extremum_uniqueI)

text \<open>The equational version of @{const knuth}. First, automatically:\<close>

text \<open>Needs \<open>a < b\<close>: take everything = \<open>\<infinity>\<close>, x = 0\<close>
lemma knuth_if_mm: "a < b \<Longrightarrow> mm a y b = mm a x b \<Longrightarrow> knuth a b x y"
by (smt (verit, del_insts) le_max_iff_disj min_def nle_le nless_le)

lemma mm_if_knuth: "knuth a b y x \<Longrightarrow> mm a y b = mm a x b"
by (metis leI max.orderE min.absorb_iff2 min_max_distrib1)

text \<open>Now readable:\<close>

lemma mm_iff_knuth: assumes "(a::_::linorder) < b"
shows "max a (min x b) = max a (min y b) \<longleftrightarrow> knuth a b y x" (is "?mm = ?h")
proof -
  have "max a (min x b) = max a (min y b) \<longleftrightarrow>
    (min x b \<le> a \<longleftrightarrow> min y b \<le> a) \<and> (a < min x b \<longrightarrow> min x b = min y b)"
    by (metis linorder_not_le max_def nle_le)
  also have "\<dots> \<longleftrightarrow> (x \<le> a \<longleftrightarrow> y \<le> a) \<and> (a < x \<longrightarrow> min x b = min y b)"
    using assms apply (simp add: linorder_not_le) by (metis leD min_le_iff_disj)
  also have "\<dots> \<longleftrightarrow> (x \<le> a \<longleftrightarrow> y \<le> a) \<and> (a < x \<longrightarrow> (b \<le> x \<longleftrightarrow> b \<le> y) \<and> (x < b \<longrightarrow> x=y))"
    by (metis leI min.strict_order_iff min_absorb2)
  also have "\<dots> \<longleftrightarrow> (x \<le> a \<longleftrightarrow> y \<le> a) \<and> (a < x \<longrightarrow> (b \<le> x \<longleftrightarrow> b \<le> y)) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"
    by blast
  also have "\<dots> \<longleftrightarrow> (x \<le> a \<longleftrightarrow> y \<le> a) \<and> (b \<le> x \<longleftrightarrow> b \<le> y) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"
    using assms dual_order.strict_trans2 linorder_not_less by blast
  also have "\<dots> \<longleftrightarrow> (x \<le> a \<longrightarrow> y \<le> a) \<and> (x \<ge> b \<longrightarrow> y \<ge> b) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"
    by (metis assms order.strict_trans linorder_le_less_linear nless_le)
  finally show ?thesis by blast
qed

corollary mm_iff_knuth': "a < b \<Longrightarrow> max a (min x b) = max a (min y b) \<longleftrightarrow> knuth a b x y"
using mm_iff_knuth by (metis mm_iff_knuth)

(*text \<open>Even in latex (relic)\<close>
text\<open>
\begin{lemma}
@{thm [mode=iffSpace,break,margin=70] mm_iff_knuth}
\end{lemma}

\begin{proofx} We assume @{prop "a < b"} and prove the equivalence:
\begin{quote}
@{prop "max a (min x b) = max a (min y b)"}\\
\<open>\<longleftrightarrow>\<close> \<open>(\<close>@{prop [mode=iff]"(min x b \<le> a \<longleftrightarrow> min y b \<le> a)"}\<open>) \<and>\<close>\\
\mbox{}\qquad\ \<open>(\<close>@{prop "(a < min x b \<longrightarrow> min x b = min y b)"}\<open>)\<close>
\hfill by def.\ of @{const max}\\
\<open>\<longleftrightarrow>\<close> \<open>(\<close>@{prop [mode=iff]"(x \<le> a \<longleftrightarrow> y \<le> a)"}\<open>) \<and>\<close>\\
\mbox{}\qquad\ \<open>(\<close>@{prop "(a < x \<longrightarrow> min x b = min y b)"}\<open>)\<close>
\hfill by @{prop "a < b"} and def.\ of @{const min}\\
\<open>\<longleftrightarrow>\<close> \<open>(\<close>@{prop [mode=iff]"(x \<le> a \<longleftrightarrow> y \<le> a)"}\<open>) \<and>\<close>\\
\mbox{}\qquad\ \<open>(\<close>@{prop [mode=iff]"(a < x \<longrightarrow> (b \<le> x \<longleftrightarrow> b \<le> y) \<and> (x < b \<longrightarrow> x=y))"}\<open>)\<close>
  \hfill by def.\ of @{const min}\\
\<open>\<longleftrightarrow>\<close> \<open>(\<close>@{prop [mode=iff]"(x \<le> a \<longleftrightarrow> y \<le> a)"}\<open>) \<and>\<close>\\
\mbox{}\qquad\ @{prop [mode=iff]"(a < x \<longrightarrow> (b \<le> x \<longleftrightarrow> b \<le> y)) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"}\\
\<open>\<longleftrightarrow>\<close> \<open>(\<close>@{prop [mode=iff]"(x \<le> a \<longleftrightarrow> y \<le> a)"}\<open>) \<and>\<close>\\
\mbox{}\qquad\ @{prop [mode=iff]"(b \<le> x \<longleftrightarrow> b \<le> y) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"}
 \hfill by @{prop "a < b"}\\
\<open>\<longleftrightarrow>\<close> \<open>(\<close>@{prop "(x \<le> a \<longrightarrow> y \<le> a)"}\<open>) \<and>\<close>\\
\mbox{}\qquad\ @{prop "(b \<le> x \<longrightarrow> b \<le> y) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"}
 \hfill by @{prop "a < b"}\\
\<open>\<longleftrightarrow>\<close> @{prop "(x \<le> a \<longrightarrow> y \<le> a) \<and> (b \<le> x \<longrightarrow> b \<le> y) \<and> (a < x \<and> x < b \<longrightarrow> x=y)"}
\end{quote}
where the final step follows from linearity and @{prop "a < b"}.
\end{proofx}
\<close>
*)

corollary knuth_comm: "a<b \<Longrightarrow> knuth a b x y \<longleftrightarrow> knuth a b y x"
using mm_iff_knuth[of a b x y] mm_iff_knuth[of a b y x]
by metis


text \<open>Specification of fail-soft: \<open>v\<close> is the actual value, \<open>ab\<close> the approximation.\<close>
abbreviation
 "fishburn (a::_::linorder) b v ab ==
  ((ab \<le> a \<longrightarrow> v \<le> ab) \<and> (a < ab \<and> ab < b \<longrightarrow> ab = v) \<and> (b \<le> ab \<longrightarrow> ab \<le> v))"

lemma fishburn_iff_min_max: "a < b \<Longrightarrow> fishburn a b v ab \<longleftrightarrow> min v b \<le> ab \<and> ab \<le> max v a"
by (metis (full_types) le_max_iff_disj linorder_not_le min_le_iff_disj nle_le)

lemma knuth_if_fishburn: "fishburn a b x y \<Longrightarrow> knuth a b x y"
using order_trans by blast

corollary fishburn_bot_top: "fishburn \<bottom> \<top> (x::_::bounded_linorder) y \<Longrightarrow> x = y"
by (metis bot.extremum bot.not_eq_extremum nle_le top.not_eq_extremum top_greatest)

lemma trans_fishburn: "fishburn a b x y \<Longrightarrow> fishburn a b y z \<Longrightarrow> fishburn a b x z"
using order.trans by blast

text \<open>An simple alternative formulation:\<close>

lemma fishburn2: "a < b \<Longrightarrow> fishburn a b f g = ((g > a \<longrightarrow> f \<ge> g) \<and> (g < b \<longrightarrow> f \<le> g))"
by auto

text \<open>Like \<open>fishburn2\<close> above, but exchanging \<open>f\<close> and \<open>g\<close>. Not clearly related to @{const knuth} and \<open>fishburn\<close>.\<close>

abbreviation "lb_ub a b f g \<equiv> ((f \<ge> a \<longrightarrow> g \<ge> a) \<and> (f \<le> b \<longrightarrow> g \<le> b))"

lemma "(a::nat) < b \<Longrightarrow> knuth a b f g \<Longrightarrow> lb_ub a b f g"
quickcheck[expect=counterexample]
oops

lemma "(a::nat) < b \<Longrightarrow> lb_ub a b f g \<Longrightarrow> knuth a b f g"
quickcheck[expect=counterexample]
oops

lemma "fishburn a b f g \<Longrightarrow> lb_ub a b f g"
by (metis order.trans nle_le)

lemma "(a::nat) < b \<Longrightarrow> lb_ub a b f g \<Longrightarrow> fishburn a b f g"
quickcheck[expect=counterexample]
oops

lemma "a<(b::int) \<Longrightarrow> fishburn a b f g \<Longrightarrow> fishburn a b g f"
quickcheck[expect=counterexample]
oops

lemma "a<(b::int) \<Longrightarrow> knuth a b f g \<Longrightarrow> fishburn a b f g"
quickcheck[expect=counterexample]
oops

lemma fishburn_trans: "fishburn a b f g \<Longrightarrow> fishburn a b g h \<Longrightarrow> fishburn a b f h"
by auto

text \<open>Exactness: if the real value is within the bounds, \<open>ab\<close> is exact.
More interesting would be the other way around.
The impact of the exactness lemmas below is unclear.\<close>

lemma fishburn_exact: "a \<le> v \<and> v \<le> b \<Longrightarrow> fishburn a b v ab \<Longrightarrow> ab = v"
by auto

text \<open>Let everyting = 0 and \<open>ab\<close> = 1:\<close>
lemma mm_not_exact: "a \<le> (v::bool) \<and> v \<le> b \<Longrightarrow> mm a v b = mm a ab b \<Longrightarrow> ab = v"
quickcheck[expect=counterexample]
oops
lemma knuth_not_exact: "a \<le> (v::ereal) \<and> v \<le> b \<Longrightarrow> knuth a b v ab \<Longrightarrow> ab = v"
quickcheck[expect=counterexample]
oops
lemma mm_not_exact: "a < b \<Longrightarrow> (a::ereal) \<le> v \<and> v \<le> b \<Longrightarrow> mm a v b = mm a ab b \<Longrightarrow> ab = v"
quickcheck[expect=counterexample]
oops


section \<open>Alpha-Beta for Linear Orders\<close>


subsection \<open>From the Left\<close>


subsubsection \<open>Hard\<close>

fun ab_max :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder)tree \<Rightarrow> 'a" and ab_maxs ab_min ab_mins where
"ab_max a b (Lf x) = x" |
"ab_max a b (Nd ts) = ab_maxs a b ts" |

"ab_maxs a b [] = a" |
"ab_maxs a b (t#ts) = (let a' = max a (ab_min a b t) in if a' \<ge> b then a' else ab_maxs a' b ts)" |

"ab_min a b (Lf x) = x" |
"ab_min a b (Nd ts) = ab_mins a b ts" |

"ab_mins a b [] = b" |
"ab_mins a b (t#ts) = (let b' = min b (ab_max a b t) in if b' \<le> a then b' else ab_mins a b' ts)"

lemma ab_maxs_ge_a: "ab_maxs a b ts \<ge> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def)(use max.bounded_iff in blast)

lemma ab_mins_le_b: "ab_mins a b ts \<le> b"
apply(induction ts arbitrary: b)
by (auto simp: Let_def)(use min.bounded_iff in blast)

text \<open>Automatic \<open>fishburn\<close> proof:\<close>

theorem (*fishburn_ab_max_auto: no_atp *)
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)   (ab_max a b t)"
    and "a < b \<Longrightarrow> fishburn a b (maxmin (Nd ts)) (ab_maxs a b ts)"
    and "a < b \<Longrightarrow> fishburn a b (minmax t)   (ab_min a b t)"
    and "a < b \<Longrightarrow> fishburn a b (minmax (Nd ts)) (ab_mins a b ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case (4 a b t ts)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, del_insts) ab_maxs_ge_a le_max_iff_disj linorder_not_le nle_le)
next
  case (8 a b t ts)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, del_insts) ab_mins_le_b linorder_not_le min.bounded_iff nle_le)
qed auto

text \<open>Detailed  \<open>fishburn\<close> proof:\<close>

theorem fishburn_val_ab:
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)   (ab_max a b t)"
    and "a < b \<Longrightarrow> fishburn a b (maxmin (Nd ts)) (ab_maxs a b ts)"
    and "a < b \<Longrightarrow> fishburn a b (minmax t)   (ab_min a b t)"
    and "a < b \<Longrightarrow> fishburn a b (minmax (Nd ts)) (ab_mins a b ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case (4 a b t ts)
  let ?abt = "ab_min a b t" let ?a' = "max a ?abt" let ?abts = "ab_maxs ?a' b ts"
  let ?mmt = "minmax t" let ?mmts = "maxmin (Nd ts)"
  let ?abtts = "ab_maxs a b (t # ts)" let ?mmtts = "maxmin (Nd (t # ts))"
  note IH1 = "4.IH"(1)[OF \<open>a<b\<close>]

  have 1: "?mmtts \<le> ?abtts" if ab: "?abtts \<le> a"
  proof (cases "b \<le> ?a'")
    case True(*impossible*)
    note \<open>a<b\<close>
    also note True
    also have "?a' = ?abtts" using True by simp
    also note \<open>\<dots> \<le> a\<close>
    finally have False by simp
    thus ?thesis ..
  next
    case False
    hence IH2: "fishburn ?a' b ?mmts ?abts" using 4(2)[OF refl] \<open>a<b\<close> linorder_not_le by blast
    from False ab have ab: "?abts \<le> a" by(simp)
    have "?a' \<le> ?abts" by(rule ab_maxs_ge_a)
    (*In fact: \<open>?abts = ?a' = a\<close>*)
    hence "?mmt \<le> ?abt" using IH1 ab by (metis order.trans linorder_not_le max.absorb4)
    have "?abts \<le> ?a'" using ab le_max_iff_disj by blast
    have "?a' \<le> a" using \<open>?a' \<le> ?abts\<close> ab by(rule order.trans)
    hence "?mmts \<le> ?abts" using IH2 \<open>?abts \<le> ?a'\<close> by blast
    with \<open>?mmt \<le> ?abt\<close> show ?thesis using False \<open>?a' \<le> ?abts\<close> by(auto)
  qed

  have 2: "?abtts \<le> ?mmtts" if ab: "b \<le> ?abtts"
  proof (cases "b \<le> ?a'")
    case True
    hence "b \<le> ?abt" using \<open>a<b\<close> by (metis linorder_not_le max_less_iff_conj)
    hence "?abt \<le> ?mmt" using IH1 by blast
    moreover
    then have "a \<le> ?mmt" using \<open>a<b\<close> \<open>b \<le> ?abt\<close> by (simp)
    ultimately show ?thesis using True by (simp add: max.coboundedI1)
  next
    case False
    hence "b \<le> ?abts" using ab by simp
    hence "?abts \<le> ?mmts" using "4.IH"(2)[OF refl] False by (meson linorder_not_le)
    then show ?thesis using False by (simp add: le_max_iff_disj)
  qed

  have 3: "?abtts = ?mmtts" if ab: "a < ?abtts" "?abtts < b"
  proof (cases "b \<le> ?a'")
    case True(*impossible*)
    also have "?a' = ?abtts" using True by simp
    also note ab(2)
    finally have False by simp
    thus ?thesis ..
  next
    case False
    hence IH2: "fishburn ?a' b ?mmts ?abts" using 4(2)[OF refl] \<open>a<b\<close> linorder_not_le by blast
    have "?abtts = ?abts" using False by(simp)
    have "?mmtts = max ?mmt ?mmts" by simp
    note IH11 = IH1[THEN conjunct1] note IH12 = IH1[THEN conjunct2,THEN conjunct1]
    note IH21 = IH2[THEN conjunct1] note IH22 = IH2[THEN conjunct2,THEN conjunct1]
    have arecb: "a < ?abts \<and> ?abts < b" using ab False by(auto)
    have "?abt \<le> a \<or> a < ?abt" by auto
    hence "?abts = max ?mmt ?mmts"
    proof
      assume "?abt \<le> a"
      hence "?a' = a" by simp
      hence "?abts = ?mmts" using IH22 arecb by presburger
      moreover
      have "?mmt \<le> ?mmts" using IH11 \<open>?abt \<le> a\<close> arecb \<open>?abts = ?mmts\<close> by auto
      ultimately show ?thesis by(simp add:Let_def)
    next
      assume "a < ?abt"
      have "?abt < b" by (meson False linorder_not_le max_less_iff_conj)
      hence "?abt = ?mmt" using IH12 \<open>a < ?abt\<close> by blast
      have "?a' < ?abts \<or> ?a' = ?abts" using ab_maxs_ge_a[of ?a' b ts] order_le_less by blast
      thus ?thesis
      proof
        assume "?a' < ?abts"
        thus ?thesis using \<open>?abt = ?mmt\<close> IH22 arecb by(simp)
      next
        assume "?a' = ?abts"
        then show ?thesis using \<open>?abt = ?mmt\<close> \<open>a < ?abt\<close> IH21 by(simp)
      qed
    qed
    thus ?thesis using \<open>?abtts = ?abts\<close> \<open>?mmtts = max ?mmt ?mmts\<close> by simp
  qed

  show ?case using 1 2 3 by blast
next
  case 8 thus ?case
    apply(simp add: Let_def)
    by (smt (verit, del_insts) ab_mins_le_b linorder_le_cases linorder_not_le min_le_iff_disj order_antisym)
qed auto

corollary ab_max_bot_top: "ab_max \<bottom> \<top> t = maxmin t"
by (metis bounded_linorder_collapse fishburn_val_ab(1) fishburn_bot_top)

text \<open>A detailed @{const knuth} proof, similar to @{thm fishburn_val_ab} proof:\<close>

theorem knuth_val_ab:
  shows "a < b \<Longrightarrow> knuth a b (maxmin t)   (ab_max a b t)"
    and "a < b \<Longrightarrow> knuth a b (maxmin (Nd ts)) (ab_maxs a b ts)"
    and "a < b \<Longrightarrow> knuth a b (minmax t)   (ab_min a b t)"
    and "a < b \<Longrightarrow> knuth a b (minmax (Nd ts)) (ab_mins a b ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case (4 a b t ts)
  let ?abt = "ab_min a b t" let ?a' = "max a ?abt" let ?abts = "ab_maxs ?a' b ts"
  let ?mmt = "minmax t" let ?mmts = "maxmin (Nd ts)"
  note IH1 = "4.IH"(1)[OF \<open>a<b\<close>]

  have 1: "maxmin (Nd (t # ts)) \<le> a" if ab: "ab_maxs a b (t # ts) \<le> a"
  proof (cases "b \<le> ?a'")
    case True(*impossible*)
    note \<open>a<b\<close>
    also note True
    also have "?a' = ab_maxs a b (t # ts)" using True by simp
    also note \<open>\<dots> \<le> a\<close>
    finally have False by simp
    thus ?thesis ..
  next
    case False
    hence IH2: "knuth ?a' b ?mmts ?abts"
      using 4(2)[OF refl] \<open>a<b\<close> linorder_not_le by blast
    from False ab have ab: "ab_maxs ?a' b ts \<le> a" by(simp)
    have "?a' \<le> ?abts" by(rule ab_maxs_ge_a)
    (*In fact: \<open>?abts = ?a' = a\<close>*)
    hence "?mmt \<le> a" using IH1 ab by (metis order.trans linorder_not_le max.absorb4)
    have "?abts \<le> ?a'" using ab le_max_iff_disj by blast
    from \<open>?a' \<le> ?abts\<close> ab have "?a' \<le> a" by(rule order.trans)
    hence "?mmts \<le> a" using IH2 \<open>?abts \<le> ?a'\<close> order.trans by blast
    with \<open>?mmt \<le> a\<close> show ?thesis by simp
  qed

  have 2: "b \<le> maxmin (Nd (t # ts))" if ab: "b \<le> ab_maxs a b (t # ts)"
  proof (cases "b \<le> ?a'")
    case True
    hence "b \<le> ?abt" using \<open>a<b\<close> by (metis linorder_not_le max_less_iff_conj)
    hence "b \<le> ?mmt" using IH1 by blast
    thus ?thesis by (simp add: le_max_iff_disj)
  next
    case False
    hence "b \<le> ?abts" using ab by simp
    hence "b \<le> ?mmts" using "4.IH"(2)[OF refl] False by (meson linorder_not_le)
    then show ?thesis by (simp add: le_max_iff_disj)
  qed

  have 3: "ab_maxs a b (t # ts) = maxmin (Nd (t # ts))"
   if ab: "a < ab_maxs a b (t # ts)" "ab_maxs a b (t # ts) < b"
  proof (cases "b \<le> ?a'")
    case True(*impossible*)
    also have "?a' = ab_maxs a b (t # ts)" using True by simp
    also note ab(2)
    finally have False by simp
    thus ?thesis ..
  next
    case False
    hence IH2: "knuth ?a' b ?mmts ?abts" using 4(2)[OF refl] \<open>a<b\<close> linorder_not_le by blast
    have "ab_maxs a b (t # ts) = ?abts" using False by(simp)
    note IH11 = IH1[THEN conjunct1] note IH12 = IH1[THEN conjunct2,THEN conjunct1]
    note IH21 = IH2[THEN conjunct1] note IH22 = IH2[THEN conjunct2,THEN conjunct1]
    have "?abt < b" by (meson False linorder_not_le max_less_iff_conj) (*used?*)
    have arecb: "a < ?abts \<and> ?abts < b" using ab False by(auto)
    have "?abt \<le> a \<or> a < ?abt" by auto
    thus ?thesis
    proof
      assume "?abt \<le> a"
      hence "?a' = a" by simp
      hence "?abts = ?mmts" using IH22 arecb by presburger
      moreover
      have "?mmt \<le> ?mmts" using IH11 \<open>?abt \<le> a\<close> arecb \<open>?abts = ?mmts\<close> by auto
      ultimately show ?thesis using \<open>ab_maxs a b (t # ts) = ?abts\<close> by(simp add:Let_def)
    next
      assume "a < ?abt"
      have "?abt = minmax t" using IH12 \<open>a < ?abt\<close> \<open>?abt < b\<close> by blast
      have "?a' < ?abts \<or> ?a' = ?abts" using ab_maxs_ge_a[of ?a' b ts] order_le_less by blast
      thus ?thesis
      proof
        assume "?a' < ?abts"
        then show ?thesis using \<open>?abt = ?mmt\<close> False IH22 arecb by(simp)
      next
        assume "?a' = ?abts"
        then show ?thesis using \<open>?abt = ?mmt\<close> False \<open>a < ?abt\<close> IH21 by(simp)
      qed
    qed
  qed

  show ?case using 1 2 3 by blast
next
  case 8 thus ?case
    apply(simp add: Let_def)
    by (smt (verit, del_insts) ab_mins_le_b linorder_le_cases linorder_not_le min_le_iff_disj order_antisym)
qed auto

text \<open>Towards exactness:\<close>

lemma ab_max_le_b: "\<lbrakk> a \<le> b; maxmin t \<le> b \<rbrakk> \<Longrightarrow> ab_max a b t \<le> b"
and  "\<lbrakk> a \<le> b; maxmin (Nd ts) \<le> b \<rbrakk> \<Longrightarrow> ab_maxs a b ts \<le> b"
and "\<lbrakk> a \<le> minmax t; a \<le> b \<rbrakk> \<Longrightarrow> a \<le> ab_min a b t"
and  "\<lbrakk> a \<le> minmax (Nd ts); a \<le> b \<rbrakk> \<Longrightarrow> a \<le> ab_mins a b ts"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case (4 a b t ts)
  show ?case
  proof (cases t)
    case Lf
    then show ?thesis using "4.IH"(2) "4.prems" by(simp add: Let_def)
  next
    case Nd
    then show ?thesis
      apply(simp add: Let_def leI ab_mins_le_b)
      using "4.IH"(2) "4.prems" ab_mins_le_b by auto
  qed
next
  case (8 a b t ts)
  show ?case
  proof (cases t)
    case Lf
    then show ?thesis using "8.IH"(2) "8.prems" by(simp add: Let_def)
  next
    case Nd
    then show ?thesis
      apply(simp add: Let_def leI ab_maxs_ge_a)
      using "8.IH"(2) "8.prems" ab_maxs_ge_a by auto
  qed
qed auto

lemma ab_max_exact:
assumes "v = maxmin t" "a \<le> v \<and> v \<le> b"
shows "ab_max a b t = v"
proof (cases t)
  case Lf with assms show ?thesis by simp
next
  case Nd
  then show ?thesis using assms
    by (smt (verit) ab_max.simps(2) ab_max_le_b ab_maxs_ge_a order.order_iff_strict order_le_less_trans fishburn_val_ab(1))
qed


subsubsection \<open>Hard, max/min flag\<close>

fun ab_minmax :: "bool \<Rightarrow> ('a::linorder) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_minmaxs where
"ab_minmax mx a b (Lf x) = x" |
"ab_minmax mx a b (Nd ts) = ab_minmaxs mx a b ts" |

"ab_minmaxs mx a b [] = a" |
"ab_minmaxs mx a b (t#ts) =
 (let abt = ab_minmax (\<not>mx) b a t;
      a' = (if mx then max else min) a abt
  in if (if mx then (\<ge>) else (\<le>)) a' b then a' else ab_minmaxs mx a' b ts)"

lemma ab_max_ab_minmax:
  shows "ab_max a b t = ab_minmax True a b t"
  and   "ab_maxs a b ts = ab_minmaxs True a b ts"
  and   "ab_min b a t = ab_minmax False a b t"
  and   "ab_mins b a ts = ab_minmaxs False a b ts"
proof(induction a b t and a b ts and b a t and b a ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
qed (auto simp add: Let_def)


subsubsection \<open>Hard, abstracted over \<open>\<le>\<close>\<close>

fun ab_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder)tree \<Rightarrow> 'a" and ab_les where
"ab_le le a b (Lf x) = x" |
"ab_le le a b (Nd ts) = ab_les le a b ts" |

"ab_les le a b [] = a" |
"ab_les le a b (t#ts) = (let abt = ab_le (\<lambda>x y. le y x) b a t;
  a' = if le a abt then abt else a in if le b a' then a' else ab_les le a' b ts)"

lemma ab_max_ab_le:
  shows "ab_max a b t = ab_le (\<le>) a b t"
  and   "ab_maxs a b ts = ab_les (\<le>) a b ts"
  and   "ab_min b a t = ab_le (\<ge>) a b t"
  and   "ab_mins b a ts = ab_les (\<ge>) a b ts"
proof(induction a b t and a b ts and b a t and b a ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
qed (auto simp add: Let_def)

text \<open>Delayed test:\<close>

fun ab_le3 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder)tree \<Rightarrow> 'a" and ab_les3 where
"ab_le3 le a b (Lf x) = x" |
"ab_le3 le a b (Nd ts) = ab_les3 le a b ts" |

"ab_les3 le a b [] = a" |
"ab_les3 le a b (t#ts) =
 (if le b a then a else
  let abt = ab_le3 (\<lambda>x y. le y x) b a t;
      a' = if le a abt then abt else a
  in ab_les3 le a' b ts)"

lemma ab_max_ab_le3:
  shows "a < b \<Longrightarrow> ab_max a b t = ab_le3 (\<le>) a b t"
  and   "a < b \<Longrightarrow> ab_maxs a b ts = ab_les3 (\<le>) a b ts"
  and   "a > b \<Longrightarrow> ab_min b a t = ab_le3 (\<ge>) a b t"
  and   "a > b \<Longrightarrow> ab_mins b a ts = ab_les3 (\<ge>) a b ts"
proof(induction a b t and a b ts and b a t and b a ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case (4 a b t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using 4 by (simp add: Let_def)
  next
    case Cons
    then show ?thesis using 4 by (auto simp add: Let_def le_max_iff_disj)
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

corollary ab_le3_bot_top: "ab_le3 (\<le>) \<bottom> \<top> t = maxmin t"
by (metis (mono_tags, lifting) ab_max_ab_le3(1) ab_max_bot_top bounded_linorder_collapse)


subsubsection \<open>Hard, \<open>max/min\<close> in \<open>Lf\<close>\<close>

text \<open>Idea due to Bird and Hughes\<close>

fun ab_max2 :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder)tree \<Rightarrow> 'a" and ab_maxs2 and ab_min2 and ab_mins2 where
"ab_max2 a b (Lf x) = max a (min x b)" |
"ab_max2 a b (Nd ts) = ab_maxs2 a b ts" |

"ab_maxs2 a b [] = a" |
"ab_maxs2 a b (t#ts) = (let a' = ab_min2 a b t in if a' = b then a' else ab_maxs2 a' b ts)" |

"ab_min2 a b (Lf x) = max a (min x b)" |
"ab_min2 a b (Nd ts) = ab_mins2 a b ts" |

"ab_mins2 a b [] = b" |
"ab_mins2 a b (t#ts) = (let b' = ab_max2 a b t in if a = b' then b' else ab_mins2 a b' ts)"

lemma ab_max2_max_min_maxmin:
shows "a \<le> b \<Longrightarrow> ab_max2 a b t = max a (min (maxmin t) b)" (* TODO: find equational proof! *)
and "a \<le> b \<Longrightarrow> ab_maxs2 a b ts = max a (min (maxmin (Nd ts)) b)"
and "a \<le> b \<Longrightarrow> ab_min2 a b t = max a (min (minmax t) b)"
and "a \<le> b \<Longrightarrow> ab_mins2 a b ts = max a (min (minmax (Nd ts)) b)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max2_ab_maxs2_ab_min2_ab_mins2.induct)
  case 4 thus ?case apply (simp add: Let_def)
    by (metis (no_types, lifting) max.assoc max_min_same(4) min_max_distrib1)
next
  case 8 thus ?case apply (simp add: Let_def)
    by (metis (no_types, opaque_lifting) max.left_idem max_min_distrib2 max_min_same(1) min.assoc min.commute)
qed auto

corollary ab_max2_bot_top: "ab_max2 \<bottom> \<top> t = maxmin t"
by(simp add: ab_max2_max_min_maxmin)

text \<open>Now for the \<open>ab\<close> version parameterized with \<open>le\<close>:\<close>

fun ab_le2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder)tree \<Rightarrow> 'a" and ab_les2 where
"ab_le2 le a b (Lf x) =
 (let xb = if le x b then x else b
  in if le a xb then xb else a)" |
"ab_le2 le a b (Nd ts) = ab_les2 le a b ts" |

"ab_les2 le a b [] = a" |
"ab_les2 le a b (t#ts) = (let a' = ab_le2 (\<lambda>x y. le y x) b a t in if a' = b then a' else ab_les2 le a' b ts)"

text \<open>Relate @{const ab_le2} back to @{const ab_max2} (using @{thm ab_max2_max_min_maxmin}!):\<close>

lemma ab_le2_ab_max2:
fixes a :: "_ :: bounded_linorder"
shows "a \<le> b \<Longrightarrow> ab_le2 (\<le>) a b t = ab_max2 a b t"
and   "a \<le> b \<Longrightarrow> ab_les2 (\<le>) a b ts = ab_maxs2 a b ts"
and   "a \<le> b \<Longrightarrow> ab_le2 (\<ge>) b a t = ab_min2 a b t"
and   "a \<le> b \<Longrightarrow> ab_les2 (\<ge>) b a ts = ab_mins2 a b ts"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max2_ab_maxs2_ab_min2_ab_mins2.induct)
  case (4 a b t ts) thus ?case
    apply (simp add: Let_def)
    by (metis ab_max2_max_min_maxmin(3) max.boundedI min.cobounded2)
next
  case 8 thus ?case
    apply (simp add: Let_def)
    by (metis ab_max2_max_min_maxmin(1) max.cobounded1)
qed auto

corollary ab_le2_bot_top: "ab_le2 (\<le>) \<bottom> \<top> t = maxmin t"
by (simp add: ab_le2_ab_max2(1) ab_max2_bot_top)


subsubsection \<open>Hard, Delayed Test\<close>

fun ab_max3 :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder)tree \<Rightarrow> 'a" and ab_maxs3 and ab_min3 and ab_mins3 where
"ab_max3 a b (Lf x) = x" |
"ab_max3 a b (Nd ts) = ab_maxs3 a b ts" |

"ab_maxs3 a b [] = a" |
"ab_maxs3 a b (t#ts) = (if a \<ge> b then a else ab_maxs3 (max a (ab_min3 a b t)) b ts)" |

"ab_min3 a b (Lf x) = x" |
"ab_min3 a b (Nd ts) = ab_mins3 a b ts" |

"ab_mins3 a b [] = b" |
"ab_mins3 a b (t#ts) = (if a \<ge> b then b else ab_mins3 a (min b (ab_max3 a b t)) ts)"

lemma ab_max3_ab_max:
shows "a<b \<Longrightarrow> ab_max3 a b t = ab_max a b t"
and "a<b \<Longrightarrow> ab_maxs3 a b ts = ab_maxs a b ts"
and "a<b \<Longrightarrow> ab_min3 a b t = ab_min a b t"
and "a<b \<Longrightarrow> ab_mins3 a b ts = ab_mins a b ts"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max3_ab_maxs3_ab_min3_ab_mins3.induct)
  case (4 a b t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using 4 by (simp add: Let_def)
  next
    case Cons
    then show ?thesis using 4 by (auto simp add: Let_def le_max_iff_disj)
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

corollary ab_max3_bot_top: "ab_max3 \<bottom> \<top> t = maxmin t"
by(metis fishburn_bot_top ab_max3_ab_max(1) fishburn_val_ab(1) bounded_linorder_collapse)


subsubsection \<open>Soft\<close>

text \<open>Fishburn\<close>

fun ab_max' :: "'a::bounded_linorder \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_maxs' ab_min' ab_mins' where
"ab_max' a b (Lf x) = x" |
"ab_max' a b (Nd ts) = ab_maxs' a b \<bottom> ts" |

"ab_maxs' a b m [] = m" |
"ab_maxs' a b m (t#ts) =
  (let m' = max m (ab_min' (max m a) b t) in if m' \<ge> b then m' else ab_maxs' a b m' ts)" |

"ab_min' a b (Lf x) = x" |
"ab_min' a b (Nd ts) = ab_mins' a b \<top> ts" |

"ab_mins' a b m [] = m" |
"ab_mins' a b m (t#ts) =
  (let m' = min m (ab_max' a (min m b) t) in if m' \<le> a then m' else ab_mins' a b m' ts)"

lemma ab_maxs'_ge_a: "ab_maxs' a b m ts \<ge> m"
apply(induction ts arbitrary: a b m)
by (auto simp: Let_def)(use max.bounded_iff in blast)


lemma ab_mins'_le_a: "ab_mins' a b m ts \<le> m"
apply(induction ts arbitrary: a b m)
by (auto simp: Let_def)(use min.bounded_iff in blast)

(* TODO: Exercise? *)
text\<open>Find \<open>a\<close>, \<open>b\<close> and \<open>t\<close> such that \<open>a < b\<close> and fail-soft is closer to the real value than fail-hard.\<close>
lemma "let a = - \<infinity>; b = ereal 0; t = Nd [Nd []]
 in a < b \<and> ab_max a b t = 0 \<and> ab_max' a b t = \<infinity> \<and> maxmin t = \<infinity>"
by eval

(* TODO? readable proofs of \<open>fishburn_val_ab'\<close>*)

theorem fishburn_val_ab':
shows "a < b \<Longrightarrow> fishburn a b (maxmin t) (ab_max' a b t)"
  and "max m a < b \<Longrightarrow> fishburn (max m a) b (maxmin (Nd ts)) (ab_maxs' a b m ts)"
  and "a < b \<Longrightarrow> fishburn a b (minmax t) (ab_min' a b t)"
  and "a < min m b \<Longrightarrow> fishburn a (min m b) (minmax (Nd ts)) (ab_mins' a b m ts)"
proof(induction a b t and a b m ts and a b t and a b m ts rule: ab_max'_ab_maxs'_ab_min'_ab_mins'.induct)
  case (4 a b m t ts)
  then show ?case
    apply (simp add: Let_def)
  by (smt (verit, best) ab_maxs'_ge_a max.absorb_iff2 max.coboundedI1 max.commute nle_le nless_le)
next
  case (8 a b m t ts)
  then show ?case
    apply (simp add: Let_def)
    by (smt (z3) ab_mins'_le_a linorder_not_le min.absorb_iff2 min.coboundedI1 min_def)
qed auto

theorem fishburn_ab'_ab:
  shows "a < b \<Longrightarrow> fishburn a b (ab_max' a b t)   (ab_max a b t)"
    and "max m a < b \<Longrightarrow> fishburn a b (ab_maxs' a b m ts) (ab_maxs (max m a) b ts)"
    and "a < b \<Longrightarrow> fishburn a b (ab_min' a b t)   (ab_min a b t)"
    and "a < min m b \<Longrightarrow> a < m \<Longrightarrow> fishburn a b (ab_mins' a b m ts) (ab_mins a (min m b) ts)"
proof(induction a b t and a b m ts and a b t and a b m ts rule: ab_max'_ab_maxs'_ab_min'_ab_mins'.induct)
  case 3 thus ?case apply simp
    by (metis linorder_not_le max.absorb4 max.order_iff)
next
  case (4 a b m t ts)
  thus ?case using [[simp_depth_limit=2]] apply (simp add: Let_def)
    by (smt (verit, ccfv_threshold) linorder_not_le max.absorb2 max_less_iff_conj nle_le)
next
  case 6 thus ?case
    apply simp using top.extremum_strict top.not_eq_extremum by blast
next
  case 7 thus ?case apply simp
    by (metis linorder_not_le min.absorb4 min.order_iff)
next
  case (8 a b m t ts)
  thus ?case using [[simp_depth_limit=2]] apply (simp add: Let_def)
    by (smt (verit) linorder_not_le min_def nle_le fishburn2)
qed auto

text \<open>Fail-soft can be more precise than fail-hard:\<close>
lemma "let a = ereal 0; b = 1; t = Nd [] in
  maxmin t = ab_max' a b t \<and> maxmin t \<noteq> ab_max a b t"
by eval

(* Towards dubious exactness: *)
lemma ab_max'_lb_ub:
shows "a \<le> b \<Longrightarrow> lb_ub a b (maxmin t) (ab_max' a b t)"
and "a \<le> b \<Longrightarrow> lb_ub a b (max i (maxmin (Nd ts))) (ab_maxs' a b i ts)"
and "a \<le> b \<Longrightarrow> lb_ub a b (minmax t) (ab_min' a b t)"
and "a \<le> b \<Longrightarrow> lb_ub a b (min i (minmax (Nd ts))) (ab_mins' a b i ts)"
proof(induction a b t and a b i ts and a b t and a b i ts rule: ab_max'_ab_maxs'_ab_min'_ab_mins'.induct)
  case (4 a b m t ts)
  then show ?case
    apply(simp_all add: Let_def)
    by (smt (verit) max.coboundedI1 max.coboundedI2 max_def)
next
  case (8 a b m t ts)
  then show ?case
    apply(simp_all add: Let_def)
    by (smt (verit, del_insts) min.coboundedI1 min.coboundedI2 min_def)
qed auto

lemma ab_max'_exact_less: "\<lbrakk> a<b; v = maxmin t; a \<le> v \<and> v \<le> b \<rbrakk> \<Longrightarrow> ab_max' a b t = v"
using fishburn_val_ab'(1) by force

lemma ab_max'_exact: "\<lbrakk> v = maxmin t; a \<le> v \<and> v \<le> b \<rbrakk> \<Longrightarrow> ab_max' a b t = v"
using ab_max'_exact_less ab_max'_lb_ub(1)
by (metis order.strict_trans2 nless_le)


subsubsection \<open>Searched trees\<close>

text \<open>Hard:\<close>

fun abt_max :: "('a::linorder) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" and abt_maxs abt_min abt_mins where
"abt_max a b (Lf x) = Lf x" |
"abt_max a b (Nd ts) = Nd (abt_maxs a b ts)" |

"abt_maxs a b [] = []" |
"abt_maxs a b (t#ts) = (let u = abt_min a b t; a' = max a (ab_min a b t) in
  u # (if a' \<ge> b then [] else abt_maxs a' b ts))" |

"abt_min a b (Lf x) = Lf x" |
"abt_min a b (Nd ts) = Nd (abt_mins a b ts)" |

"abt_mins a b [] = []" |
"abt_mins a b (t#ts) = (let u = abt_max a b t; b' = min b (ab_max a b t) in
  u # (if b' \<le> a then [] else abt_mins a b' ts))"

text \<open>Soft:\<close>

fun abt_max' :: "('a::bounded_linorder) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" and abt_maxs' abt_min' abt_mins' where
"abt_max' a b (Lf x) = Lf x" |
"abt_max' a b (Nd ts) = Nd (abt_maxs' a b \<bottom> ts)" |

"abt_maxs' a b m [] = []" |
"abt_maxs' a b m (t#ts) =
 (let u = abt_min' (max m a) b t; m' = max m (ab_min' (max m a) b t) in
  u # (if m' \<ge> b then [] else abt_maxs' a b m' ts))" |

"abt_min' a b (Lf x) = Lf x" |
"abt_min' a b (Nd ts) = Nd (abt_mins' a b \<top> ts)" |

"abt_mins' a b m [] = []" |
"abt_mins' a b m (t#ts) =
 (let u = abt_max' a (min m b) t; m' = min m (ab_max' a (min m b) t) in
  u # (if m' \<le> a then [] else abt_mins' a b m' ts))"

lemma abt_max'_abt_max:
shows "a < b \<Longrightarrow> abt_max' a b t = abt_max a b t"
and "max m a < b \<Longrightarrow> abt_maxs' a b m ts = abt_maxs (max m a) b ts"
and "a < b \<Longrightarrow> abt_min' a b t = abt_min a b t"
and "a < min m b \<Longrightarrow> abt_mins' a b m ts = abt_mins a (min m b) ts"
proof(induction a b t and a b m ts and a b t and a b m ts rule: abt_max'_abt_maxs'_abt_min'_abt_mins'.induct)
  case (4 a b m t ts)
  thus ?case unfolding abt_maxs'.simps(2) abt_maxs.simps(2) Let_def
    using fishburn_ab'_ab(3)
    by (smt (verit, best) le_max_iff_disj linorder_not_le max_def nless_le)
next
  case (8 a b m t ts)
  then show ?case unfolding abt_mins'.simps(2) abt_mins.simps(2) Let_def
    using fishburn_ab'_ab(1)
    by (smt (verit, del_insts) linorder_not_le min.absorb1 min.absorb3 min.commute min_le_iff_disj)
qed (auto)

text \<open>An annotated tree of \<open>ab\<close> calls with the \<open>a,b\<close> window.\<close>

datatype 'a tri = Ma 'a 'a "'a tr" | Mi 'a 'a "'a tr"
and 'a tr = No "'a tri list" | Le 'a

fun abtr_max :: "('a::linorder) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tri" and abtr_maxs abtr_min abtr_mins where
"abtr_max a b (Lf x) = Ma a b (Le x)" |
"abtr_max a b (Nd ts) = Ma a b (No (abtr_maxs a b ts))" |

"abtr_maxs a b [] = []" |
"abtr_maxs a b (t#ts) = (let u = abtr_min a b t; a' = max a (ab_min a b t) in
  u # (if a' \<ge> b then [] else abtr_maxs a' b ts))" |

"abtr_min a b (Lf x) = Mi a b (Le x)" |
"abtr_min a b (Nd ts) = Mi a b (No (abtr_mins a b ts))" |

"abtr_mins a b [] = []" |
"abtr_mins a b (t#ts) = (let u = abtr_max a b t; b' = min b (ab_max a b t) in
  u # (if b' \<le> a then [] else abtr_mins a b' ts))"

text \<open>For better readability get rid of \<open>ereal\<close>:\<close>
fun de :: "ereal \<Rightarrow> real" where
"de (ereal x) = x" |
"de PInfty = 100" |
"de MInfty = -100"

fun detri and detr where
"detri (Ma a b t) = Ma (de a) (de b) (detr t)" |
"detri (Mi a b t) = Mi (de a) (de b) (detr t)" |
"detr (No ts) = No (map detri ts)" |
"detr (Le x) = Le (de x)"

text \<open>Example in Knuth and Moore. Evaluation confirms that all subtrees \<open>u\<close> are pruned.\<close>
value "let
 t11 = Nd[Nd[Lf 3,Lf 1,Lf 4], Nd[Lf 1,t], Nd[Lf 2,Lf 6,Lf 5]];
 t12 = Nd[Nd[Lf 3,Lf 5,Lf 8], u]; t13 = Nd[Nd[Lf 8,Lf 4,Lf 6], u];
 t21 = Nd[Nd[Lf 3,Lf 2],Nd[Lf 9,Lf 5,Lf 0],Nd[Lf 2,u]];
 t31 = Nd[Nd[Lf 0,u],Nd[Lf 4,Lf 9,Lf 4],Nd[Lf 4,u]];
 t32 = Nd[Nd[Lf 2,u],Nd[Lf 7,Lf 8,Lf 1],Nd[Lf 6,Lf 4,Lf 0]];
  t = Nd[Nd[t11, t12, t13], Nd[t21,u], Nd[t31,t32,u]]
in (ab_max (-\<infinity>::ereal) \<infinity> t,abt_max (-\<infinity>::ereal) \<infinity> t,detri(abtr_max (-\<infinity>::ereal) \<infinity> t))"


subsubsection \<open>Soft, generalized, attempts\<close>

text \<open>Attempts to prove correct General version due to Junkang Li et al.\<close>

text \<open>This first version (not worth following!) stops the list iteration as soon as \<open>max m a \<ge> b\<close>
(I call this "delayed test", it complicates proofs a little.)
and the initial value is fixed \<open>a\<close> (not \<open>i0/1\<close>)\<close>

fun abil0' :: "('a::bounded_linorder)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abils0' abil1' abils1' where
"abil0' (Lf x) a b = x" |
"abil0' (Nd ts) a b = abils0' ts a b a" |

"abils0' [] a b m = m" |
"abils0' (t#ts) a b m =
  (if max m a \<ge> b then m else abils0' ts (max m a) b (max m (abil1' t b (max m a))))" |

"abil1' (Lf x) a b = x" |
"abil1' (Nd ts) a b = abils1' ts a b a" |

"abils1' [] a b m = m" |
"abils1' (t#ts) a b m =
  (if min m a \<le> b then m else  abils1' ts (min m a) b (min m (abil0' t b (min m a))))"

lemma abils0'_ge_i: "abils0' ts a b i \<ge> i"
apply(induction ts arbitrary: i a)
by (auto simp: Let_def)(use max.bounded_iff in blast)

lemma abils1'_le_i: "abils1' ts a b i \<le> i"
apply(induction ts arbitrary: i a)
by (auto simp: Let_def)(use min.bounded_iff in blast)

lemma fishburn_abil01':
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)           (abil0' t a b)"
    and "a < b \<Longrightarrow> i < b \<Longrightarrow> fishburn (max a i) b (maxmin (Nd ts)) (abils0' ts a b i)"
    and "a > b \<Longrightarrow> fishburn b a (minmax t)           (abil1' t a b)"
    and "a > b \<Longrightarrow> i > b \<Longrightarrow> fishburn b (min a i) (minmax (Nd ts)) (abils1' ts a b i)"
proof(induction t a b and ts a b i and t a b and ts a b i rule: abil0'_abils0'_abil1'_abils1'.induct)
  case (4 t ts a b m)
  thus ?case apply (simp add: Let_def)
    by (smt (verit) abils0'.elims abils0'_ge_i max.absorb_iff1 max.coboundedI2 max_def nless_le)
next
  case (8 t ts a b m)
  thus ?case apply (simp add: Let_def)
    by (smt (verit, best) abils1'.elims abils1'_le_i linorder_not_le min.absorb2 min_def min_le_iff_disj)
qed auto

text \<open>This second computes the value of \<open>t\<close> before deciding if it needs to look at \<open>ts\<close> as well.
This simplifies the proof (also in other versions, independently of initialization).
The initial value is not fixed but determined by \<open>i0/1\<close>. The "real" constraint on \<open>i0/1\<close>
is commented out and replaced by the simplified value \<open>a\<close>.\<close>

locale LeftSoft =
fixes i0 i1 :: "'a::bounded_linorder tree list \<Rightarrow> 'a \<Rightarrow> 'a"
assumes i0: "i0 ts a \<le> a \<comment>\<open>max a (maxmin (Nd ts))\<close>" and i1: "i1 ts a \<ge> a\<comment>\<open>min a (minmax (Nd ts))\<close>"
begin

fun abil0' :: "('a::bounded_linorder)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abils0' abil1' abils1' where
"abil0' (Lf x) a b = x" |
"abil0' (Nd ts) a b = abils0' ts a b (i0 ts a)" |

"abils0' [] a b m = m" |
"abils0' (t#ts) a b m =
  (let m' = max m (abil1' t b (max m a)) in if m' \<ge> b then m' else abils0' ts a b m')" |

"abil1' (Lf x) a b = x" |
"abil1' (Nd ts) a b = abils1' ts a b (i1 ts a)" |

"abils1' [] a b m = m" |
"abils1' (t#ts) a b m =
  (let m' = min m (abil0' t b (min m a)) in if m' \<le> b then m' else abils1' ts a b m')"

lemma abils0'_ge_i: "abils0' ts a b i \<ge> i"
apply(induction ts arbitrary: i)
by (auto simp: Let_def)(use max.bounded_iff in blast)

lemma abils1'_le_i: "abils1' ts a b i \<le> i"
apply(induction ts arbitrary: i)
by (auto simp: Let_def)(use min.bounded_iff in blast)

text \<open>Generalizations that don't seem to work:
a) \<open>max a i \<rightarrow> max (max a (maxmin (Nd ts))) i\<close>
b) \<open> ?\<close>\<close>

lemma fishburn_abil01':
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)           (abil0' t a b)"
    and "a < b \<Longrightarrow> i < b \<Longrightarrow> fishburn (max a i) b (maxmin (Nd ts)) (abils0' ts a b i)"
    and "a > b \<Longrightarrow> fishburn b a (minmax t)           (abil1' t a b)"
    and "a > b \<Longrightarrow> i > b \<Longrightarrow> fishburn b (min a i) (minmax (Nd ts)) (abils1' ts a b i)"
proof(induction t a b and ts a b i and t a b and ts a b i rule: abil0'_abils0'_abil1'_abils1'.induct)
  case (2 ts a b)
  thus ?case using i0[of ts a] by auto
next
  case (4 i t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (verit) abils0'_ge_i le_max_iff_disj linorder_not_le max.absorb1 nle_le)
next
  case (6 ts a b)
  thus ?case using i1[of a ts] by simp
next
  case (8 i t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (verit, best) abils1'_le_i linorder_not_le min_def min_less_iff_conj nle_le)
qed auto

text \<open>Note the \<open>a \<le> b\<close> instead of the \<open>a < b\<close> in theorem \<open>fishburn_abir01'\<close>:\<close>

lemma abil0'lb_ub:
shows "a \<le> b \<Longrightarrow> lb_ub a b (maxmin t) (abil0' t a b)"
and "a \<le> b \<Longrightarrow> lb_ub a b (max i (maxmin (Nd ts))) (abils0' ts a b i)"
and "a \<ge> b \<Longrightarrow> lb_ub b a (minmax t) (abil1' t a b)"
and "a \<ge> b \<Longrightarrow> lb_ub b a (min i (minmax (Nd ts))) (abils1' ts a b i)"
proof(induction t a b and ts a b i and t a b and ts a b i rule: abil0'_abils0'_abil1'_abils1'.induct)
  case (2 ts a b)
  then show ?case by simp (meson order.trans i0 le_max_iff_disj)
next
  case (4 t ts a b m)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, best) max.coboundedI1 max.coboundedI2 max_def)
next
  case (6 ts a b)
  then show ?case
    by simp (meson i1 min.coboundedI2 order_trans)
next
  case (8 t ts a b m)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, del_insts) min.coboundedI1 min.coboundedI2 min_def)
qed auto

lemma abil0'_exact_less: "\<lbrakk> a<b; v = maxmin t; a \<le> v \<and> v \<le> b \<rbrakk> \<Longrightarrow> abil0' t a b = v"
using fishburn_abil01'(1) by force

lemma abil0'_exact: "\<lbrakk> v = maxmin t; a \<le> v \<and> v \<le> b\<rbrakk> \<Longrightarrow> abil0' t a b = v"
by (metis abil0'_exact_less abil0'lb_ub(1) order.trans leD order_le_imp_less_or_eq)

end


subsubsection \<open>Transposition Table / Graph / Repeated AB\<close>

(* Marsland/Li, repeated evaluation of same position with different a/b. Transposition table!

"In alpha-beta search with cache for totally ordered values (for instance [Marsland, 1986]),
one can exploit the fact that with usual value initialisation, the value f(n,\<alpha>,\<beta>) satisfies
f(n,\<alpha>,\<beta>) < \<beta> \<Rightarrow> v(n) \<le> f(n,\<alpha>,\<beta>) and f(n,\<alpha>,\<beta>) > \<alpha> \<Rightarrow> v(n) \<ge> f(n,\<alpha>,\<beta>).
In particular, if \<alpha> < f(n,\<alpha>,\<beta>) < \<beta>, then f(n,\<alpha>,\<beta>) = v(n).
Hence by comparing f(n,\<alpha>,\<beta>) to \<alpha> and \<beta>, one can determine whether it is exact,
a lower, or an upper bound, and store it in the cache with an appropriate flag."

These lemmas show what can be done.
Lemma 1: The initial call is \<open>abf a b t > a\<close>. Thus \<open>abf a b t\<close> is a lower bound for \<open>maxmin t\<close>.
Thus the second call \<open>abf a' b' t\<close> can be made with \<open>max a' (abf a b t)\<close>.
Lemma 2: The initial call is \<open>abf t a b < b\<close>. Thus \<open>abf a b t\<close> is an upper bound for \<open>maxmin t\<close>.
Thus the second call \<open>abf a' b' t\<close> can be made with \<open>min b' (abf a b t)\<close>.

Works as long as \<open>abf\<close> satisfies fishburn.

TODO: ab function with cache.
*)

lemma ab_twice_lb:
 "\<lbrakk> \<forall>a b. fishburn a b (maxmin t) (ab a b t); b \<le> ab a b t; max a' (ab a b t) < b' \<rbrakk> \<Longrightarrow>
  fishburn a' b' (maxmin t) (ab (max a' (ab a b t)) b' t)"
by (smt (verit, del_insts) order.eq_iff order.strict_trans leI max_less_iff_conj)

lemma ab_twice_ub:
 "\<lbrakk> \<forall>a b. fishburn a b (maxmin t) (ab a b t); ab a b t \<le> a; min b' (ab a b t) > a' \<rbrakk> \<Longrightarrow>
  fishburn a' b' (maxmin t) (ab a' (min b' (ab a b t)) t)"
by (smt (verit, best) linorder_not_le min.absorb1 min.absorb2 min.strict_boundedE nless_le)

text \<open>But what does a narrower window achieve?
Less precise bounds but prefix of search space. For fail-hard and fail-soft.\<close>

fun prefix prefixs where
"prefix (Lf x) (Lf y) = (x=y)" |
"prefix (Nd ts) (Nd us) = prefixs ts us" |
"prefix _ _ = False" |

"prefixs [] us = True" |
"prefixs (t#ts) (u#us) = (prefix t u \<and> prefixs ts us)" |
"prefixs _ _ = False"

lemma fishburn_ab_max_windows:
shows "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> fishburn a b (ab_max a' b' t) (ab_max a b t)"
and   "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> fishburn a b (ab_maxs a' b' ts) (ab_maxs a b ts)"
and   "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> fishburn a b (ab_min a' b' t) (ab_min a b t)"
and   "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> fishburn a b (ab_mins a' b' ts) (ab_mins a b ts)"
proof (induction a b t and a b ts and a b t and a b ts
       arbitrary: a' b' and a' b' and a' b' and a' b'
       rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case 2 show ?case
    using "2.prems" apply simp
    using "2.IH" by presburger
next
  case (4 a b t ts) show ?case using "4.prems"
    apply (simp add: Let_def)
    using "4.IH"
    by (smt (verit, del_insts) ab_maxs_ge_a le_max_iff_disj linorder_not_le max_def nle_le)
next
  case 6 show ?case
    using "6.prems" apply simp
    using "6.IH" by presburger
next
  case (8 a b t ts) show ?case using "8.prems"
    apply (simp add: Let_def)
    using "8.IH"
    by (smt (verit, best) ab_mins_le_b order.strict_trans1 linorder_not_le min.absorb1 min.absorb2 nle_le)
qed auto

lemma abt_max_prefix_windows:
shows "\<lbrakk> a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> prefix (abt_max a b t) (abt_max a' b' t)"
and "\<lbrakk> a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> prefixs (abt_maxs a b ts) (abt_maxs a' b' ts)"
and "\<lbrakk> a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> prefix (abt_min a b t) (abt_min a' b' t)"
and "\<lbrakk> a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> prefixs (abt_mins a b ts) (abt_mins a' b' ts)"
proof (induction a b t and a b ts and a b t and a b ts
       arbitrary: a' b' and a' b' and a' b' and a' b'
       rule: abt_max_abt_maxs_abt_min_abt_mins.induct)
  case (4 a b t ts)
  then show ?case
    apply (simp add: Let_def)
    by (smt (verit, del_insts) fishburn_ab_max_windows(3) linorder_not_le max.coboundedI1 max.orderI max_def)
next
  case (8 a b t ts)
  then show ?case
    apply (simp add: Let_def)
    by (smt (verit, del_insts) fishburn_ab_max_windows(1) le_cases3 linorder_not_less min_def_raw knuth_if_fishburn)
qed auto

lemma fishburn_ab_max'_windows:
shows "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> fishburn a b (ab_max' a' b' t) (ab_max' a b t)"
and "\<lbrakk> max m a < b; a' \<le> a; b \<le> b'; m' \<le> m \<rbrakk> \<Longrightarrow> fishburn (max m a) b (ab_maxs' a' b' m' ts) (ab_maxs' a b m ts)"
and   "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> fishburn a b (ab_min' a' b' t) (ab_min' a b t)"
and "\<lbrakk> a < min m b; a' \<le> a; b \<le> b'; m \<le> m' \<rbrakk> \<Longrightarrow> fishburn a (min m b) (ab_mins' a' b' m' ts) (ab_mins' a b m ts)"
proof (induction a b t and a b m ts and a b t and a b m ts
       arbitrary: a' b' and a' b' m' and a' b' and a' b' m'
       rule: ab_max'_ab_maxs'_ab_min'_ab_mins'.induct)
  case (2 a b ts)
  show ?case
    using "2.prems" apply simp
    using "2.IH" by (metis max_bot nle_le)
next
  case (4 a b m t ts)
  show ?case
    using "4.prems" apply (simp add: Let_def)
    using "4.IH" ab_maxs'_ge_a
    by (smt (z3) le_max_iff_disj linorder_not_le max.cobounded2 max.commute max_def)
next
  case (6 a b ts)
  show ?case
    using "6.prems" apply simp
    using "6.IH" by (metis min_top nle_le)
next
  case (8 a b m t ts)
  show ?case
    using "8.prems" apply (simp add: Let_def)
    using "8.IH" ab_mins'_le_a
    by (smt (z3) leD linorder_linear min.absorb1 min.absorb2 min.bounded_iff not_le_imp_less)
qed auto

text \<open>Example of reduced search space:\<close>

lemma "let a = 0; b = (1::ereal); a' = 0; b' = 2; t = Nd [Lf 1, Lf 0]
  in abt_max' a b t = Nd [Lf 1] \<and> abt_max' a' b' t = t"
by eval

lemma abt_max'_prefix_windows:
shows "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> prefix (abt_max' a b t) (abt_max' a' b' t)"
and "\<lbrakk> max m a < b; a' \<le> a; b \<le> b'; m' \<le> m \<rbrakk> \<Longrightarrow> prefixs (abt_maxs' a b m ts) (abt_maxs' a' b' m' ts)"
and "\<lbrakk> a < b; a' \<le> a; b \<le> b' \<rbrakk> \<Longrightarrow> prefix (abt_min' a b t) (abt_min' a' b' t)"
and "\<lbrakk> a < min m b; a' \<le> a; b \<le> b'; m \<le> m' \<rbrakk> \<Longrightarrow> prefixs (abt_mins' a b m ts) (abt_mins' a' b' m' ts)"
proof (induction a b t and a b m ts and a b t and a b m ts
       arbitrary: a' b' and a' b' m' and a' b' and a' b' m'
       rule: abt_max'_abt_maxs'_abt_min'_abt_mins'.induct)
  case (4 a b m t ts)
  then show ?case apply (simp add: Let_def)
    using fishburn_ab_max'_windows(3)
    by (smt (verit, ccfv_threshold) add_mono linorder_le_cases max.absorb2 max.assoc max.order_iff order.strict_iff_not trans_le_add1)
next
  case (8 a b t ts)
  then show ?case apply (simp add: Let_def)
    using fishburn_ab_max'_windows(1)
    by (smt (verit, best)add_le_mono le_add1 linorder_not_less min.mono min_less_iff_conj order.trans nle_le)
qed auto


subsection \<open>From the Right\<close>

text \<open>The literature uniformly considers iteration from the left only.
Iteration from the right is technically simpler but needs to go through all successors,
which means generating all of them.
This is typically done anyway to reorder them based on heuristic evaluations.
This rules out an infinite list of successors, but it is unclear if there are any applications.\<close>

text \<open>Naming convention: 0 = max, 1 = min\<close>

subsubsection \<open>Hard\<close>

fun abr0 :: "('a::linorder)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abrs0 and abr1 and abrs1 where
"abr0 (Lf x) a b = x" |
"abr0 (Nd ts) a b = abrs0 ts a b" |

"abrs0 [] a b = a" |
"abrs0 (t#ts) a b = (let m = abrs0 ts a b in if m \<ge> b then m else max (abr1 t b m) m)" |

"abr1 (Lf x) a b = x" |
"abr1 (Nd ts) a b = abrs1 ts a b" |

"abrs1 [] a b = a" |
"abrs1 (t#ts) a b = (let m = abrs1 ts a b in if m \<le> b then m else min (abr0 t b m) m)"

lemma abrs0_ge_a: "abrs0 ts a b \<ge> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def)(use max.coboundedI2 in blast)

lemma abrs1_le_a: "abrs1 ts a b \<le> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def)(use min.coboundedI2 in blast)

theorem abr01_mm:
  shows "mm a (abr0 t a b) b = mm a (maxmin t) b"
    and "mm a (abrs0 ts a b) b = mm a (maxmin (Nd ts)) b"
    and "mm b (abr1 t a b) a = mm b (minmax t) a"
    and "mm b (abrs1 ts a b) a = mm b (minmax (Nd ts)) a"
proof(induction t a b and ts a b and t a b and ts a b rule: abr0_abrs0_abr1_abrs1.induct)
  case (4 t ts a b)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit) max.left_commute max_def_raw min.commute min.orderE min_max_distrib1)
next
  case (8 t ts a b)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit) max.left_idem max.orderE max_min_distrib2 max_min_same(4) min.assoc)
qed auto

text \<open>As a corollary:\<close>
corollary knuth_abr01_cor: "a < b \<Longrightarrow> knuth a b (maxmin t) (abr0 t a b)"
by (meson knuth_if_mm abr01_mm(1))

corollary maxmin_mm_abr0: "\<lbrakk> a \<le> maxmin t; maxmin t \<le> b \<rbrakk> \<Longrightarrow> maxmin t = mm a (abr0 t a b) b"
by (metis max_def min.absorb1 abr01_mm(1))
corollary maxmin_mm_abrs0: "\<lbrakk> a \<le> maxmin (Nd ts); maxmin (Nd ts) \<le> b \<rbrakk>
 \<Longrightarrow> maxmin (Nd ts) = mm a (abrs0 ts a b) b"
by (metis max_def min.absorb1 abr01_mm(2))

text \<open>The stronger @{const fishburn} spec:\<close>

text \<open>Needs \<open>a<b\<close>.\<close>
theorem fishburn_abr01:
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)   (abr0 t a b)"
    and "a < b \<Longrightarrow> fishburn a b (maxmin (Nd ts)) (abrs0 ts a b)"
    and "a > b \<Longrightarrow> fishburn b a (minmax t)   (abr1 t a b)"
    and "a > b \<Longrightarrow> fishburn b a (minmax (Nd ts)) (abrs1 ts a b)"
proof(induction t a b and ts a b and t a b and ts a b rule: abr0_abrs0_abr1_abrs1.induct)
  case (4 t ts a b)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, best) leI max.absorb_iff2 max.coboundedI1 max.orderE order.strict_iff_not)
next
  case (8 t ts a b)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, best) order.trans linorder_not_le min.absorb3 min.absorb_iff2 nle_le)
qed auto

text \<open>Above lemma does not work for \<open>a = b\<close> and \<open>a > b\<close>.
 Not fishburn: \<open>abr0 \<le> a\<close> but not \<open>maxmin \<le> abr0\<close>.
 Not knuth: \<open>abr0 \<le> a\<close> but not \<open>maxmin \<le> a\<close>\<close>
lemma "let a = 0::ereal; t = Nd [Lf 1, Lf 0] in abr0 t a a = 0 \<and> maxmin t = 1"
by eval
lemma "let a = 0::ereal; b = -1; t = Nd [Lf 1, Lf 0] in abr0 t a b = 0 \<and> maxmin t = 1"
by eval

text \<open>The following lemma does not follow from \<open>fishburn\<close> because of the weaker assumption \<open>a \<le> b\<close>
that is required for the later exactness lemma.\<close>

lemma abr0_le_b: "\<lbrakk> a \<le> b; maxmin t \<le> b \<rbrakk> \<Longrightarrow> abr0 t a b \<le> b"
and  "\<lbrakk> a \<le> b; maxmin (Nd ts) \<le> b \<rbrakk> \<Longrightarrow> abrs0 ts a b \<le> b"
and "\<lbrakk> b \<le> minmax t; b \<le> a \<rbrakk> \<Longrightarrow> b \<le> abr1 t a b"
and  "\<lbrakk> b \<le> minmax (Nd ts); b \<le> a \<rbrakk> \<Longrightarrow> b \<le> abrs1 ts a b"
proof(induction t a b and ts a b and t a b and ts a b rule: abr0_abrs0_abr1_abrs1.induct)
  case (4 t ts a b)
  show ?case
  proof (cases t)
    case Lf
    then show ?thesis using "4.IH"(1) "4.prems" by(simp add: Let_def)
  next
    case Nd
    then show ?thesis
      apply(simp add: Let_def leI abrs1_le_a)
      using "4.IH"(1) "4.prems" by auto
  qed
next
  case (8 t ts a b)
  show ?case
  proof (cases t)
    case Lf
    then show ?thesis using "8.IH"(1) "8.prems" by(simp add: Let_def)
  next
    case Nd
    then show ?thesis
      apply(simp add: Let_def leI abrs0_ge_a)
      using "8.IH"(1) "8.prems" by auto
  qed
qed auto

lemma abr0_exact_less:
assumes "a < b" "v = maxmin t" "a \<le> v \<and> v \<le> b"
shows "abr0 t a b = v"
using fishburn_exact[OF assms(3)] fishburn_abr01[OF assms(1)] assms(2) by metis

lemma abr0_exact:
assumes "v = maxmin t" "a \<le> v \<and> v \<le> b"
shows "abr0 t a b = v"
using  abr0_exact_less abr0_le_b abrs0_ge_a assms(1,2) abr0.elims
by (smt (verit, best) dual_order.trans leD maxmin.simps(1) order_le_imp_less_or_eq)

text \<open>Another proof:\<close>
lemma abr0_exact2:
assumes "v = maxmin t" "a \<le> v \<and> v \<le> b"
shows "abr0 t a b = v"
proof (cases t)
  case Lf with assms show ?thesis by simp
next
  case Nd
  then show ?thesis using assms
    by (smt (verit, del_insts) abr0.simps(2) abr0_le_b abrs0_ge_a order.order_iff_strict order_le_less_trans fishburn_abr01(1))
(*    by (smt (verit, ccfv_threshold) abr0.simps(2) abrs0_ge_a max_def min_def abr0_le_b abr01_mm(1))*)
qed


subsubsection \<open>Soft\<close>

text \<open>Starting at \<open>\<bottom>\<close> (after Fishburn)\<close>

fun abr0' :: "('a::bounded_linorder)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abrs0' and abr1' and abrs1' where
"abr0' (Lf x) a b = x" |
"abr0' (Nd ts) a b = abrs0' ts a b" |

"abrs0' [] a b = \<bottom>" |
"abrs0' (t#ts) a b = (let m = abrs0' ts a b in if m \<ge> b then m else max (abr1' t b (max m a)) m)" |

"abr1' (Lf x) a b = x" |
"abr1' (Nd ts) a b = abrs1' ts a b" |

"abrs1' [] a b = \<top>" |
"abrs1' (t#ts) a b = (let m = abrs1' ts a b in if m \<le> b then m else min (abr0' t b (min m a)) m)"

theorem fishburn_abr01':
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)   (abr0' t a b)"
    and "a < b \<Longrightarrow> fishburn a b (maxmin (Nd ts)) (abrs0' ts a b)"
    and "a > b \<Longrightarrow> fishburn b a (minmax t)   (abr1' t a b)"
    and "a > b \<Longrightarrow> fishburn b a (minmax (Nd ts)) (abrs1' ts a b)"
proof(induction t a b and ts a b and t a b and ts a b rule: abr0'_abrs0'_abr1'_abrs1'.induct)
  case (4 t ts a b)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, ccfv_SIG) le_max_iff_disj linorder_not_le max.absorb3 max.absorb_iff2)
next
  case (8 t ts a b)
  then show ?case
    apply(simp add: Let_def)
    by (smt (verit, best) linorder_not_le min.absorb_iff1 min.absorb_iff2 nle_le fishburn2)
qed auto

text \<open>Same as for \<open>abr0\<close>: Above lemma does not work for \<open>a = b\<close> and \<open>a > b\<close>.
 Not fishburn: \<open>abr0' \<le> a\<close> but not \<open>maxmin \<le> abr0'\<close>.
 Not knuth: \<open>abr0' \<le> a\<close> but not \<open>maxmin \<le> a\<close>\<close>
lemma "let a = 0::ereal; t = Nd [Lf 1, Lf 0] in abr0' t a a = 0 \<and> maxmin t = 1"
by eval
lemma "let a = 0::ereal; b = -1; t = Nd [Lf 1, Lf 0] in abr0' t a b = 0 \<and> maxmin t = 1"
by eval

text \<open>Fails for a=b=-1 and t = Nd []\<close>
theorem fishburn2_abr01_abr01':
  shows "a < b \<Longrightarrow> fishburn a b (abr0' t a b)   (abr0 t a b)"
    and "a < b \<Longrightarrow> fishburn a b (abrs0' ts a b) (abrs0 ts a b)"
    and "a > b \<Longrightarrow> fishburn b a (abr1' t a b)   (abr1 t a b)"
    and "a > b \<Longrightarrow> fishburn b a (abrs1' ts a b) (abrs1 ts a b)"
proof(induction t a b and ts a b and t a b and ts a b rule: abr0_abrs0_abr1_abrs1.induct)
  case (4 t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (verit) abrs0_ge_a max.absorb2 max.assoc max.commute nle_le order_le_imp_less_or_eq)
next
  case (8 t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (verit, ccfv_threshold) abrs1_le_a min.absorb_iff2 min.bounded_iff nle_le order.strict_iff_order)
qed auto

text \<open>Towards `exactness':\<close>

text \<open>No need for restricting \<open>a,b\<close>, but only corollaries:\<close>
corollary abr0'_mm: "mm a (abr0' t a b) b = mm a (maxmin t) b"
by (smt (verit) max.absorb1 max.cobounded2 max.strict_order_iff min.absorb2 min.absorb3 min.cobounded1 mm_if_knuth fishburn_abr01'(1))
corollary abrs0'_mm: "mm a (abrs0' ts a b) b = mm a (maxmin (Nd ts)) b"
by (metis abr0'.simps(2) abr0'_mm)
corollary abr1'_mm: "mm b (abr1' t a b) a = mm b (minmax t) a"
by (smt (verit, best) linorder_not_le max.absorb1 max_less_iff_conj min.absorb2 fishburn_abr01'(3))
corollary abrs1'_mm: "mm b (abrs1' ts a b) a = mm b (minmax (Nd ts)) a"
by (metis abr1'.simps(2) abr1'_mm)

corollary li1: "\<lbrakk> a \<le> maxmin t;  maxmin t \<le> b\<rbrakk> \<Longrightarrow> mm a (abr0' t a b) b = maxmin t"
  by (simp add: abr0'_mm)

text \<open>Note the \<open>a \<le> b\<close> instead of the \<open>a < b\<close> in @{thm fishburn_abr01'}:\<close>

lemma abr01'lb_ub:
shows "a \<le> b \<Longrightarrow> lb_ub a b (maxmin t)   (abr0' t a b)"
  and "a \<le> b \<Longrightarrow> lb_ub a b (maxmin (Nd ts)) (abrs0' ts a b)"
  and "a \<ge> b \<Longrightarrow> lb_ub b a (minmax t)   (abr1' t a b)"
  and "a \<ge> b \<Longrightarrow> lb_ub b a (minmax (Nd ts)) (abrs1' ts a b)"
apply(induction t a b and ts a b and t a b and ts a b rule: abr0'_abrs0'_abr1'_abrs1'.induct)
by(auto simp add: Let_def le_max_iff_disj  min_le_iff_disj)

lemma abr0'_exact_less: "\<lbrakk> a<b; v = maxmin t; a \<le> v \<and> v \<le> b \<rbrakk> \<Longrightarrow> abr0' t a b = v"
using fishburn_abr01'(1) by force

lemma abr0'_exact: "\<lbrakk> v = maxmin t; a \<le> v \<and> v \<le> b\<rbrakk> \<Longrightarrow> abr0' t a b = v"
by (metis abr0'_exact_less abr01'lb_ub(1) order.trans leD order_le_imp_less_or_eq)


subsubsection \<open>Also returning the searched tree\<close>

text \<open>Hard:\<close>

fun abtr0 :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a tree" and abtrs0 and abtr1 and abtrs1 where
"abtr0 (Lf x) a b = (x, Lf x)" |
"abtr0 (Nd ts) a b = (let (m,us) = abtrs0 ts a b in (m, Nd us))" |

"abtrs0 [] a b = (a,[])" |
"abtrs0 (t#ts) a b = (let (m,us) = abtrs0 ts a b in
  if m \<ge> b then (m,us) else let (n,u) = abtr1 t b m in (max n m,u#us))" |

"abtr1 (Lf x) a b = (x, Lf x)" |
"abtr1 (Nd ts) a b = (let (m,us) = abtrs1 ts a b in (m, Nd us))" |

"abtrs1 [] a b = (a,[])" |
"abtrs1 (t#ts) a b = (let (m,us) = abtrs1 ts a b in
  if m \<le> b then (m,us) else let (n,u) = abtr0 t b m in (min n m,u#us))"

text \<open>Soft:\<close>

fun abtr0' :: "('a::bounded_linorder) tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a tree" and abtrs0' and abtr1' and abtrs1' where
"abtr0' (Lf x) a b = (x, Lf x)" |
"abtr0' (Nd ts) a b = (let (m,us) = abtrs0' ts a b in (m, Nd us))" |

"abtrs0' [] a b = (\<bottom>,[])" |
"abtrs0' (t#ts) a b = (let (m,us) = abtrs0' ts a b in
  if m \<ge> b then (m,us) else let (n,u) = abtr1' t b (max m a) in (max n m,u#us))" |

"abtr1' (Lf x) a b = (x, Lf x)" |
"abtr1' (Nd ts) a b = (let (m,us) = abtrs1' ts a b in (m, Nd us))" |

"abtrs1' [] a b = (\<top>,[])" |
"abtrs1' (t#ts) a b = (let (m,us) = abtrs1' ts a b in
  if m \<le> b then (m,us) else let (n,u) = abtr0' t b (min m a) in (min n m,u#us))"

lemma fst_abtr01:
shows "fst(abtr0 t a b) = abr0 t a b"
and "fst(abtrs0 ts a b) = abrs0 ts a b"
and "fst(abtr1 t a b) = abr1 t a b"
and "fst(abtrs1 ts a b) = abrs1 ts a b"
by(induction t a b and ts a b and t a b and ts a b rule: abtr0_abtrs0_abtr1_abtrs1.induct)
  (auto simp: Let_def split: prod.split)

lemma fst_abtr01':
shows "fst(abtr0' t a b) = abr0' t a b"
and "fst(abtrs0' ts a b) = abrs0' ts a b"
and "fst(abtr1' t a b) = abr1' t a b"
and "fst(abtrs1' ts a b) = abrs1' ts a b"
by(induction t a b and ts a b and t a b and ts a b rule: abtr0'_abtrs0'_abtr1'_abtrs1'.induct)
  (auto simp: Let_def split: prod.split)

lemma snd_abtr01'_abtr01:
shows "a < b \<Longrightarrow> snd(abtr0' t a b) = snd(abtr0 t a b)"
and "a < b \<Longrightarrow> snd(abtrs0' ts a b) = snd(abtrs0 ts a b)"
and "a > b \<Longrightarrow> snd(abtr1' t a b) = snd(abtr1 t a b)"
and "a > b \<Longrightarrow> snd(abtrs1' ts a b) = snd(abtrs1 ts a b)"
proof(induction t a b and ts a b and t a b and ts a b rule: abtr0'_abtrs0'_abtr1'_abtrs1'.induct)
  case (4 t ts a b)
  then show ?case
    apply(simp add: Let_def split: prod.split)
    using fst_abtr01(2) fst_abtr01'(2) fishburn2_abr01_abr01'(2) abrs0_ge_a
    by (smt (verit, best) fst_conv le_max_iff_disj linorder_not_le max.absorb1 nle_le sndI)
next
  case (8 t ts a b)
  then show ?case
    apply(simp add: Let_def split: prod.split)
    using fst_abtr01(4) fst_abtr01'(4) fishburn2_abr01_abr01'(4) abrs1_le_a
    by (smt (verit, ccfv_threshold) fst_conv linorder_not_le min.absorb1 min.absorb_iff2 order.strict_trans2 snd_conv)
qed (auto simp add: split_beta)


subsubsection \<open>Generalized\<close>

text \<open>General version due to Junkang Li et al.:\<close>

locale SoftGeneral =
fixes i0 i1 :: "'a::bounded_linorder tree list \<Rightarrow> 'a \<Rightarrow> 'a"
assumes i0: "i0 ts a \<le> max a (maxmin(Nd ts))" and i1: "i1 ts a \<ge> min a (minmax (Nd ts))"
begin

fun abir0' :: "('a::bounded_linorder)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abirs0' and abir1' and abirs1' where
"abir0' (Lf x) a b = x" |
"abir0' (Nd ts) a b = abirs0' (i0 ts a) ts a b" |

"abirs0' i [] a b = i" |
"abirs0' i (t#ts) a b =
  (let m = abirs0' i ts a b in if m \<ge> b then m else max (abir1' t b (max m a)) m)" |

"abir1' (Lf x) a b = x" |
"abir1' (Nd ts) a b = abirs1' (i1 ts a) ts a b" |

"abirs1' i [] a b = i" |
"abirs1' i (t#ts) a b =
  (let m = abirs1' i ts a b in if m \<le> b then m else min (abir0' t b (min m a)) m)"

text \<open>Unused:\<close>
lemma abirs0'_ge_i: "abirs0' i ts a b \<ge> i"
apply(induction ts)
by (auto simp: Let_def) (metis max.coboundedI2)

lemma abirs1'_le_i: "abirs1' i ts a b \<le> i"
apply(induction ts)
by (auto simp: Let_def) (metis min.coboundedI2)

lemma fishburn_abir01':
  shows "a < b \<Longrightarrow> fishburn a b (maxmin t)           (abir0' t a b)"
    and "a < b \<Longrightarrow> fishburn a b (max i (maxmin (Nd ts))) (abirs0' i ts a b)"
    and "a > b \<Longrightarrow> fishburn b a (minmax t)           (abir1' t a b)"
    and "a > b \<Longrightarrow> fishburn b a (min i (minmax (Nd ts))) (abirs1' i ts a b)"
proof(induction t a b and i ts a b and t a b and i ts a b rule: abir0'_abirs0'_abir1'_abirs1'.induct)
  case (2 ts a b)
  thus ?case using i0[of ts a] apply simp
    by (smt (verit, best) leD le_max_iff_disj max_def)
next
  case (4 i t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (z3) linorder_not_le max.coboundedI2 max_def nle_le)
next
  case (6 ts a b)
  thus ?case
    using i1[of a ts] apply simp by (smt (verit, del_insts) leD min_le_iff_disj nle_le)
next
  case (8 i t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (verit, ccfv_SIG) linorder_not_le min.absorb2 min_le_iff_disj nle_le)
qed auto

text \<open>Note the \<open>a \<le> b\<close> instead of the \<open>a < b\<close> in @{thm fishburn_abir01'}:\<close>

lemma abir0'lb_ub:
shows "a \<le> b \<Longrightarrow> lb_ub a b (maxmin t) (abir0' t a b)"
and "a \<le> b \<Longrightarrow> lb_ub a b (max i (maxmin (Nd ts))) (abirs0' i ts a b)"
and "a \<ge> b \<Longrightarrow> lb_ub b a (minmax t) (abir1' t a b)"
and "a \<ge> b \<Longrightarrow> lb_ub b a (min i (minmax (Nd ts))) (abirs1' i ts a b)"
apply(induction t a b and i ts a b and t a b and i ts a b rule: abir0'_abirs0'_abir1'_abirs1'.induct)
apply(auto simp add: Let_def le_max_iff_disj  min_le_iff_disj)
  apply (metis i0 max.bounded_iff max.order_iff maxmin.simps(2))
  apply (metis i0 max.bounded_iff max.order_iff maxmin.simps(2))
  apply (metis i1 max.bounded_iff max.order_iff minmax.simps(2) min.bounded_iff)
  apply (metis i1 max.bounded_iff max.order_iff minmax.simps(2) min.bounded_iff)
done

lemma abir0'_exact_less: "\<lbrakk> a<b; v = maxmin t; a \<le> v \<and> v \<le> b \<rbrakk> \<Longrightarrow> abir0' t a b = v"
using fishburn_abir01'(1) by force

lemma abir0'_exact: "\<lbrakk> v = maxmin t; a \<le> v \<and> v \<le> b\<rbrakk> \<Longrightarrow> abir0' t a b = v"
by (metis abir0'_exact_less abir0'lb_ub(1) order.trans leD order_le_imp_less_or_eq)

end

text \<open>Now with explicit parameters \<open>i0\<close> and \<open>i1\<close> such that we can vary them:\<close>

fun abir0' :: "_ \<Rightarrow> _ \<Rightarrow> ('a::bounded_linorder)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abirs0' and abir1' and abirs1' where
"abir0' i0 i1 (Lf x) a b = x" |
"abir0' i0 i1 (Nd ts) a b = abirs0' i0 i1 (i0 ts a) ts a b" |

"abirs0' i0 i1 i [] a b = i" |
"abirs0' i0 i1 i (t#ts) a b =
  (let m = abirs0' i0 i1 i ts a b in if m \<ge> b then m else max (abir1' i0 i1 t b (max m a)) m)" |

"abir1' i0 i1 (Lf x) a b = x" |
"abir1' i0 i1 (Nd ts) a b = abirs1' i0 i1 (i1 ts a) ts a b" |

"abirs1' i0 i1 i [] a b = i" |
"abirs1' i0 i1 i (t#ts) a b =
  (let m = abirs1' i0 i1 i ts a b in if m \<le> b then m else min (abir0' i0 i1 t b (min m a)) m)"

text \<open>First, the same theorem as in the locale \<open>SoftGeneral\<close>:\<close>

definition "bnd i0 i1 \<equiv>
  \<forall>ts a. i0 ts a \<le> max a (maxmin(Nd ts)) \<and> i1 ts a \<ge> min a (minmax (Nd ts))"

declare [[unify_search_bound=400,unify_trace_bound=400]] (* Because of complex induction rules *)

lemma fishburn_abir01':
  shows "a < b \<Longrightarrow> bnd i0 i1 \<Longrightarrow> fishburn a b (maxmin t)           (abir0' i0 i1 t a b)"
    and "a < b \<Longrightarrow> bnd i0 i1 \<Longrightarrow> fishburn a b (max i (maxmin (Nd ts))) (abirs0' i0 i1 i ts a b)"
    and "a > b \<Longrightarrow> bnd i0 i1 \<Longrightarrow> fishburn b a (minmax t)           (abir1' i0 i1 t a b)"
    and "a > b \<Longrightarrow> bnd i0 i1 \<Longrightarrow> fishburn b a (min i (minmax (Nd ts))) (abirs1' i0 i1 i ts a b)"
proof(induction i0 i1 t a b and i0 i1 i ts a b and i0 i1 t a b and i0 i1 i ts a b
      rule: abir0'_abirs0'_abir1'_abirs1'.induct)
  case (2 ts a b)
  thus ?case unfolding bnd_def apply simp
    by (smt (verit, best) leD le_max_iff_disj max_def)
next
  case (4 i t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (z3) linorder_not_le max.coboundedI2 max_def nle_le)
next
  case (6 ts a b)
  thus ?case
    unfolding bnd_def apply simp
    by (smt (verit, ccfv_threshold) linorder_not_le min.absorb2 min_def min_le_iff_disj)
next
  case (8 i t ts a b)
  thus ?case apply (simp add: Let_def)
    by (smt (verit, ccfv_SIG) linorder_not_le min.absorb2 min_le_iff_disj nle_le)
qed (auto)

text \<open>Unused:\<close>
lemma abirs0'_ge_i: "abirs0' i0 i1 i ts a b \<ge> i"
apply(induction ts)
by (auto simp: Let_def) (metis max.coboundedI2)

lemma abirs0'_eq_i: "i \<ge> b \<Longrightarrow> abirs0' i0 i1 i ts a b = i"
by(induction ts) (auto simp: Let_def)

lemma abirs1'_le_i: "abirs1' i0 i1 i ts a b \<le> i"
apply(induction ts)
by (auto simp: Let_def) (metis min.coboundedI2)


text \<open>Monotonicity wrt the init functions, below/above \<open>a\<close>:\<close>

definition "bnd_mono i0 i1 i0' i1' =
 (\<forall>ts a. i0' ts a \<le> a \<and> i1' ts a \<ge> a \<and> i0 ts a \<le> i0' ts a \<and> i1 ts a \<ge> i1' ts a)"

lemma fishburn_abir0'_mono: 
shows "a < b \<Longrightarrow> bnd_mono i0 i1 i0' i1' \<Longrightarrow> fishburn a b (abir0' i0 i1 t a b) (abir0' i0' i1' t a b)"
  and "a < b \<Longrightarrow> bnd_mono i0 i1 i0' i1' \<Longrightarrow> i = i0 (ts0 @ ts) a \<Longrightarrow>
        fishburn a b (abirs0' i0 i1 i ts a b) (abirs0' i0' i1' (i0' (ts0 @ ts) a) ts a b)"
 and "a > b \<Longrightarrow> bnd_mono i0 i1 i0' i1' \<Longrightarrow> fishburn b a (abir1' i0 i1 t a b) (abir1' i0' i1' t a b)"
 and "a > b \<Longrightarrow> bnd_mono i0 i1 i0' i1' \<Longrightarrow> i = i1 (ts0@ts) a \<Longrightarrow>
        fishburn b a (abirs1' i0 i1 i ts a b) (abirs1' i0' i1' (i1' (ts0 @ ts) a) ts a b)"
proof(induction i0 i1 t a b and i0 i1 i ts a b and i0 i1 t a b and i0 i1 i ts a b
    arbitrary: i0' i1' and i0' i1' ts0 and i0' i1' and i0' i1' ts0
    rule: abir0'_abirs0'_abir1'_abirs1'.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (metis abir0'.simps(2) append_Nil)
next
  case 3
  then show ?case unfolding bnd_mono_def
    apply simp by (metis order.strict_trans1 leD)
next
  case (4 i0 i1 i t ts a b)
  show ?case
    using "4.prems" "4.IH"(2)[OF refl, of i0' i1'] "4.IH"(1)[OF \<open>a<b\<close>, of i0' i1' "ts0 @ [t]"]
    by (smt (z3) Cons_eq_appendI abirs0'.simps(2) append_eq_append_conv2 append_self_conv linorder_not_less max_def_raw nless_le order.strict_trans1)
next
  case 5
  then show ?case by simp
next
  case 6
  then show ?case by (metis abir1'.simps(2) append_Nil)
next
  case 7
  then show ?case unfolding bnd_mono_def
    apply simp by (metis leD order_le_less_trans)
next
  case (8 i0 i1 i t ts a b)
  then show ?case
    using "8.prems" "8.IH"(2)[OF refl, of i0' i1'] "8.IH"(1)[OF \<open>a>b\<close>, of i0' i1' "ts0 @ [t]"]
    by (smt (verit) Cons_eq_appendI abirs1'.simps(2) append_eq_append_conv2 linorder_le_less_linear min.absorb2 min.absorb3 min.order_iff min_less_iff_conj self_append_conv)
qed

text \<open>The \<open>i0\<close> bound of \<open>a\<close> cannot be increased to \<open>max a (maxmin(Nd ts)\<close>
(as the theorem \<open>fishburn_abir0'\<close> might suggest).
Problem: if \<open>b \<le> i0 a ts < i0' a ts\<close> then it can happen that
  \<open>b \<le> abirs0' i0 i1 t a b < abirs0' i0' i1' t a b\<close>, which violates \<open>fishburn\<close>.\<close>

value "let  a = - \<infinity>; b = 0::ereal; t = Nd [Lf (1::ereal)] in
 (abir0' (\<lambda>ts a. max a (maxmin(Nd ts))) i1' t a b,
  abir0' (\<lambda>ts a. max a (maxmin(Nd ts))-1) i1 t a b)"

lemma "let  a = - \<infinity>; b = 0::ereal; ts = [Lf (1::ereal)] in
  abirs0' (\<lambda>ts a. max a (maxmin(Nd ts))-1) (\<lambda>_ a. a+1) (max a (maxmin(Nd ts))-1) ts a b = 0"
unfolding Let_def
using [[simp_trace]] by (simp add:Let_def)



section \<open>Alpha-Beta for De Morgan Orders\<close>

subsection \<open>From the Left, Fail-Hard\<close>

text \<open>Like Knuth.\<close>

fun ab_negmax :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::de_morgan_order)tree \<Rightarrow> 'a" and ab_negmaxs where
"ab_negmax a b (Lf x) = x" |
"ab_negmax a b (Nd ts) = ab_negmaxs a b ts" |

"ab_negmaxs a b [] = a" |
"ab_negmaxs a b (t#ts) = (let a' = max a (- ab_negmax (-b) (-a) t) in if a' \<ge> b then a' else ab_negmaxs a' b ts)"

text \<open>Via \<open>foldl\<close>. Wasteful: \<open>foldl\<close> consumes whole list.\<close>

definition ab_negmaxf :: "('a::de_morgan_order) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" where
"ab_negmaxf b = (\<lambda>a t. if a \<ge> b then a else max a (- ab_negmax (-b) (-a) t))"

lemma foldl_ab_negmaxf_idemp:
  "b \<le> a \<Longrightarrow> foldl (ab_negmaxf b) a ts = a"
by(induction ts) (auto simp: ab_negmaxf_def)

lemma ab_negmaxs_foldl:
  "(a::'a::de_morgan_order) < b \<Longrightarrow> ab_negmaxs a b ts = foldl (ab_negmaxf b) a ts"
using foldl_ab_negmaxf_idemp[where 'a='a]
by(induction ts arbitrary: a) (auto simp: ab_negmaxf_def Let_def dest: not_le_imp_less)

text \<open>Also returning the searched tree.\<close>

(*TODO: mk ab_negmax, add ab_negmax', finish proofs*)fun abtl :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::de_morgan_order)tree \<Rightarrow> 'a * ('a::de_morgan_order)tree" and abtls where
"abtl a b (Lf x) = (x, Lf x)" |
"abtl a b (Nd ts) = (let (m,us) = abtls a b ts in (m, Nd us))" |

"abtls a b [] = (a,[])" |
"abtls a b (t#ts) = (let (a',u) = abtl (-b) (-a) t; a' = max a (-a') in
  if a' \<ge> b then (a',[u]) else let (n,us) = abtls a' b ts in (n,u#us))"

lemma fst_abtl:
shows "fst(abtl a b t) = ab_negmax a b t"
and "fst(abtls a b ts) = ab_negmaxs a b ts"
by(induction a b t and a b ts rule: abtl_abtls.induct)
  (auto simp: Let_def split: prod.split)

subsubsection "Correctness Proofs"

text \<open>First, a very direct proof.\<close>

lemma ab_negmaxs_ge_a: "ab_negmaxs a b ts \<ge> a"
apply(induction ts arbitrary: a)
by (auto simp: Let_def) (metis max.bounded_iff)

lemma fishburn_val_ab_neg:
shows "a < b \<Longrightarrow> fishburn a b (negmax t) (ab_negmax (a) b t)"
and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (ab_negmaxs (a) b ts)"
proof(induction a b t and a b ts rule: ab_negmax_ab_negmaxs.induct)
  case (4 a b t ts)
  then show ?case
    apply(simp add: Let_def less_uminus_reorder)
    by (smt (verit, ccfv_threshold) ab_negmaxs_ge_a le_max_iff_disj linorder_not_le minus_less_minus nle_le uminus_less_reorder)
qed auto

text "Now an indirect one by reduction to the min/max alpha-beta. Direct proof is simpler!"

text \<open>Relate ordinary and negmax ab:\<close>
theorem ab_max_negmax:
shows "ab_max a b t = ab_negmax a b (negate False t)"
and   "ab_maxs a b ts = ab_negmaxs a b (map (negate True) ts)"
and   "ab_min a b t = - ab_negmax (-b) (-a) (negate True t)"
and   "ab_mins a b ts = - ab_negmaxs (-b) (-a) (map (negate False) ts)"
proof(induction a b t and a b ts and a b t and a b ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  case 8
  then show ?case by(simp add: Let_def de_morgan_max de_morgan_min uminus_le_reorder)
qed (simp_all add: Let_def)

corollary fishburn_negmax_ab_negmax: "a < b \<Longrightarrow> fishburn a b (negmax t) (ab_negmax a b t)"
using fishburn_val_ab(1) ab_max_negmax(1) negmax_maxmin(1) negate_negate
by (metis (no_types, lifting))

(*
Currently unused and can be proved equationally from earlier lemmas.
Might come in useful if one tries to interconnect the ab-variants in a different order.
*)
lemma ab_negmax_ab_le:
  shows "ab_negmax a b t = ab_le (\<le>) a b (negate False t)"
  and   "ab_negmaxs a b ts = ab_les (\<le>) a b (map (negate True) ts)"
  and   "ab_negmax a b t = - ab_le (\<ge>) (-a) (-b) (negate True t)"
  and   "ab_negmaxs a b ts = - ab_les (\<ge>) (-a) (-b) (map (negate False) ts)"
by(induction a b t and a b ts and b a t and b a ts rule: ab_max_ab_maxs_ab_min_ab_mins.induct)
  (auto simp add: Let_def max_def ab_max_ab_le[symmetric] ab_max_negmax negate_negate o_def)

text \<open>Pointless? Weaker than fishburn and direct proof rather than corollary as via \<open>ab_max_negmax\<close>\<close>
text \<open>Weaker max-min property. Proof: Case False one eqn chain, but dualized IH:\<close>
theorem
shows ab_negmax_negmax2: "max a (min (ab_negmax a b t) b) = max a (min (negmax t) b)"
and ab_negmaxs_maxs_neg3: "a < b \<Longrightarrow> min (ab_negmaxs a b ts) b = max a (min (negmax (Nd ts)) b)"
proof(induction a b t and a b ts rule: ab_negmax_ab_negmaxs.induct)
  case 2
  thus ?case apply simp
    by (metis leI max_absorb1 max_def min.coboundedI2)
next
  case (4 a b t ts)
  let ?abt = "ab_negmax (- b) (- a) t" let ?a' = "max a (- ?abt)"
  let ?T = "negmax t" let ?S = "negmax (Nd ts)"
  show ?case
(* apply (simp add: Let_def) using 4
    by (smt (verit) ereal_minus_less_minus ereal_uminus_less_reorder linorder_neq_iff linorder_not_le max.absorb3 max.absorb4 max.absorb_iff2 min.absorb3 min.absorb4 min_less_iff_conj)
*)
  proof (cases "b \<le> ?a'")
    case True
    have "min b (max (-?abt) a) = min b (max (- ?T) a)" using "4.IH"(1) "4.prems"
      by (metis (no_types) neg_neg de_morgan_min)
    hence "b = min b (max (- ?T) a)" using True
      by (metis max.commute min.orderE)
    hence "b \<le> max (- ?T) a"
      by (metis min.cobounded2)
    hence b: "b \<le> - ?T"
      by (meson "4.prems" leD le_max_iff_disj)
    have "min (ab_negmaxs a b (t # ts)) b = min ?a' b"
      using True by simp
    also have "\<dots> = b"
      using True min.absorb2 by blast
    also have "\<dots> = max a (max (min (- ?T) b) (min ?S b))"
      using b "4.prems" by simp
    also have "\<dots> = max a (min (max (- ?T) ?S) b)"
      by (metis min_max_distrib1)
    also have "\<dots> = max a (min (negmax (Nd (t # ts))) b)"
      by simp
    finally show ?thesis .
  next
    case False
    hence 1: "- ?abt < b"
      by (metis le_max_iff_disj linorder_not_le)
    have IH1: "max a (min (- ?abt) b) = max a (min (- ?T) b)"
      using "4.IH"(1) \<open>a<b\<close> by (metis max_min_neg neg_neg)
    have "min (ab_negmaxs a b (t # ts)) b = min (ab_negmaxs (max a (- ?abt)) b ts) b"
      using False by(simp)
    also have "\<dots> = max (max a (- ?abt)) (min ?S b)"
      using "4.IH"(2) "4.prems" 1 False by(simp)
    also have "\<dots> = max (max a (min (-?abt) b)) (max a (min ?S b))"
      using 1 by (simp add: max.assoc max.left_commute)
    also have "\<dots> = max (max a (min (- ?T) b)) (max a (min ?S b))"
      using IH1 by presburger
    also have "\<dots> = max a (min (max (- ?T) ?S) b)"
      by (metis (no_types, lifting) max.assoc max.commute max.right_idem min_max_distrib1)
    also have "\<dots> =  max a (min (negmax (Nd (t # ts))) b)" by simp
    finally show ?thesis .
  qed
qed auto

corollary ab_negmax_negmax_cor2: "ab_negmax \<bottom> \<top> t = negmax t"
using ab_negmax_negmax2[of \<bottom> \<top> t] by (simp)


subsection \<open>From the Left, Fail-Soft\<close>

text \<open>After Fishburn\<close>

fun ab_negmax' :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::de_morgan_order)tree \<Rightarrow> 'a" and ab_negmaxs' where
"ab_negmax' a b (Lf x) = x" |
"ab_negmax' a b (Nd ts) = (ab_negmaxs' a b \<bottom> ts)" |

"ab_negmaxs' a b m [] = m" |
"ab_negmaxs' a b m (t#ts) = (let m' = max m (- ab_negmax' (-b) (- max m a) t) in
      if m' \<ge> b then m' else ab_negmaxs' a b m' ts)"

lemma ab_negmaxs'_ge_a: "ab_negmaxs' a b m ts \<ge> m"
apply(induction ts arbitrary: a b m)
by (auto simp: Let_def) (metis max.bounded_iff)

(* TODO? readble proofs *)

theorem fishburn_val_ab_neg':
shows "a < b \<Longrightarrow> fishburn a b (negmax t) (ab_negmax' a b t)"
  and "max a m < b \<Longrightarrow> fishburn (max a m) b (negmax (Nd ts)) (ab_negmaxs' a b m ts)"
proof(induction a b t and a b m ts rule: ab_negmax'_ab_negmaxs'.induct)
  case (4 a b m t ts)
  then show ?case
    apply (simp add: Let_def)
    by (smt (verit, del_insts) ab_negmaxs'_ge_a minus_le_minus uminus_le_reorder linorder_not_le max.absorb1 max.absorb4 max.coboundedI2 max.commute)
qed auto

(* Trickier than r version \<open>fishburn_abr_abr'\<close> below because of additional parameter m;
   does not look like one could simplify matters by porting r to l via mirror *)
theorem fishburn_ab'_ab_neg:
shows "a < b \<Longrightarrow> fishburn a b (ab_negmax' a b t) (ab_negmax a b t)"
  and "max m a < b \<Longrightarrow> fishburn a b (ab_negmaxs' a b m ts) (ab_negmaxs (max m a) b ts)"
proof(induction a b t and a b m ts rule: ab_negmax'_ab_negmaxs'.induct)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case
    by fastforce
next
  case 3
  then show ?case apply simp
    by (metis linorder_linear linorder_not_le max.commute max.orderE)
next
  case (4 a b m t ts)
  then show ?case
    apply (simp)
    by (smt (verit) minus_le_minus neg_neg leD linorder_le_less_linear linorder_linear max.absorb_iff1 max.assoc max.commute nle_le)
qed

text \<open>Another proof of \<open>fishburn_negmax_ab_negmax\<close>, just by transitivity:\<close>
corollary "a < b \<Longrightarrow> fishburn a b (negmax t) (ab_negmax a b t)"
by(rule trans_fishburn[OF fishburn_val_ab_neg'(1) fishburn_ab'_ab_neg(1)])

text \<open>Now fail-soft with traversed trees.\<close>

fun abtl' :: "'a \<Rightarrow> 'a \<Rightarrow> ('a::de_morgan_order)tree \<Rightarrow> 'a * ('a::de_morgan_order)tree" and abtls' where
"abtl' a b (Lf x) = (x, Lf x)" |
"abtl' a b (Nd ts) = (let (m,us) = abtls' a b \<bottom> ts in (m, Nd us))" |

"abtls' a b m [] = (m,[])" |
"abtls' a b m (t#ts) = (let (m',u) = abtl' (-b) (- max m a) t; m' = max m (- m') in
      if m' \<ge> b then (m',[u]) else let (n,us) = abtls' a b m' ts in (n,u#us))"

lemma fst_abtl':
shows "fst(abtl' a b t) = ab_negmax' a b t"
and "fst(abtls' a b m ts) = ab_negmaxs' a b m ts"
by(induction a b t and a b m ts rule: abtl'_abtls'.induct)
  (auto simp: Let_def split: prod.split)

text \<open>Fail-hard and fail-soft search the same part of the tree:\<close>

lemma snd_abtl'_abtl:
shows "a < b \<Longrightarrow> abtl' a b t = (ab_negmax' a b t, snd(abtl a b t))"
and "max m a < b \<Longrightarrow> abtls' a b m ts = (ab_negmaxs' a b m ts, snd(abtls (max m a) b ts))"
proof(induction a b t and a b m ts rule: abtl'_abtls'.induct)
  case (4 t ts a b)
  then show ?case
    apply(simp add: Let_def split: prod.split)
    by (smt (verit) fishburn_ab'_ab_neg(1) fst_abtl(1) fst_conv linorder_neq_iff max.absorb3 max.cobounded2 max.coboundedI2 max_def minus_less_minus snd_conv uminus_less_reorder)
qed (auto simp add: split_beta)


subsubsection "\<open>min\<close>/\<open>max\<close> in \<open>Lf\<close>"

fun ab_negmax2 :: " ('a::de_morgan_order) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_negmaxs2 where
"ab_negmax2 a b (Lf x) = max a (min x b)" |
"ab_negmax2 a b (Nd ts) = ab_negmaxs2 a b ts" |

"ab_negmaxs2 a b [] = a" |
"ab_negmaxs2 a b (t#ts) = (let a' = - ab_negmax2 (-b) (-a) t in if a' = b then a' else ab_negmaxs2 a' b ts)"

lemma ab_negmax2_max_min_negmax:
shows "a < b \<Longrightarrow> ab_negmax2 a b t = max a (min (negmax t) b)"
and "a < b \<Longrightarrow> ab_negmaxs2 a b ts = max a (min (negmax (Nd ts)) b)"
proof(induction a b t and a b ts rule: ab_negmax2_ab_negmaxs2.induct)
next
  case 4 thus ?case
    apply (simp add: Let_def)
    by (smt (z3) de_morgan_max le_max_iff_disj linorder_not_le max.commute max_def neg_neg uminus_less_reorder)
qed auto

corollary ab_negmax2_bot_top: "ab_negmax2 \<bottom> \<top> t = negmax t"
by (metis ab_negmax2_max_min_negmax(1) bounded_linorder_collapse max_bot min_top2)


subsubsection "Delayed test"

text \<open>Now a variant that delays the test to the next call of \<open>ab_negmaxs\<close>.
Like Bird and Hughes' version, except that \<open>ab_negmax3\<close> does not cut off the return value.\<close>

fun ab_negmax3 :: "('a::de_morgan_order) \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a" and ab_negmaxs3 where
"ab_negmax3 a b (Lf x) = x" |
"ab_negmax3 a b (Nd ts) = ab_negmaxs3 a b ts" |

"ab_negmaxs3 a b [] = a" |
"ab_negmaxs3 a b (t#ts) = (if a \<ge> b then a else ab_negmaxs3 (max a (- ab_negmax3 (-b) (-a) t)) b ts)"

lemma ab_negmax3_ab_negmax:
shows "a<b \<Longrightarrow> ab_negmax3 a b t = ab_negmax a b t"
and "a<b \<Longrightarrow> ab_negmaxs3 a b ts = ab_negmaxs a b ts"
proof(induction a b t and a b ts rule: ab_negmax3_ab_negmaxs3.induct)
  case (4 a b t ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using 4 by (simp add: Let_def)
  next
    case Cons
    then show ?thesis using 4 by (auto simp add: Let_def le_max_iff_disj)
  qed
qed auto

corollary ab_negmax3_bot_top: "ab_negmax3 \<bottom> \<top> t = negmax t"
by(metis fishburn_negmax_ab_negmax ab_negmax3_ab_negmax(1) bounded_linorder_collapse fishburn_bot_top)

lemma ab_negmaxs3_foldl:
  "ab_negmaxs3 a b ts = foldl (\<lambda>a t. if a \<ge> b then a else max a (- ab_negmax3 (-b) (-a) t)) a ts"
apply(induction ts arbitrary: a)
by (auto simp: Let_def) (metis ab_negmaxs3.elims)


subsection \<open>From the Right, Fail-Hard\<close>

fun abr :: "('a::de_morgan_order)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abrs where
"abr (Lf x) a b = x" |
"abr (Nd ts) a b = abrs ts a b" |

"abrs [] a b = a" |
"abrs (t#ts) a b = (let m = abrs ts a b in if m \<ge> b then m else max (- abr t (-b) (-m)) m)"

lemma Lf_eq_negateD: "Lf x = negate f t \<Longrightarrow> t = Lf(if f then -x else x)"
by(cases t) auto

lemma Nd_eq_negateD: "Nd ts' = negate f t \<Longrightarrow> \<exists>ts. t = Nd ts \<and> ts' = map (negate (\<not>f)) ts"
by(cases t) (auto simp: comp_def cong: map_cong)

lemma abr01_negate:
shows "abr0 (negate f t) a b = - abr1 (negate (\<not>f) t) (-a) (-b)"
and  "abrs0 (map (negate f) ts) a b = - abrs1 (map (negate (\<not>f)) ts) (-a) (-b)"
and "abr1 (negate f t) a b = - abr0 (negate (\<not>f) t) (-a) (-b)"
and  "abrs1 (map (negate f) ts) a b = - abrs0 (map (negate (\<not>f)) ts) (-a) (-b)"
proof(induction "negate f t" a b and "map (negate f) ts" a b and "negate f t" a b and "map (negate f) ts" a b arbitrary: f t and f ts and f t and f ts rule: abr0_abrs0_abr1_abrs1.induct)
  case (1 x a b)
  from Lf_eq_negateD[OF this] show ?case by simp
next
  case (2 ts a b)
  from Nd_eq_negateD[OF 2(2)] 2(1) show ?case by auto
next
  case (3 a b)
  then show ?case by simp
next
  case (4 t ts a b)
  from Cons_eq_map_D[OF 4(3)] 4(1) 4(2)[OF refl] show ?case
    by (auto simp: Let_def de_morgan_min) (metis neg_neg uminus_le_reorder)+
next
  case (5 x a b)
  from Lf_eq_negateD[OF this] show ?case by simp
next
  case (6 ts a b)
  from Nd_eq_negateD[OF 6(2)] 6(1) show ?case by auto
next
  case (7 a b)
  then show ?case by simp
next
  case (8 t ts a b)
  from Cons_eq_map_D[OF 8(3)] 8(1) 8(2)[OF refl] show ?case
    by (auto simp: Let_def de_morgan_max uminus_le_reorder)
qed

lemma abr_abr0:
 shows "abr t a b = abr0 (negate False t) a b"
 and "abrs ts a b = abrs0 (map (negate True) ts) a b"
proof (induction t a b and ts a b rule: abr_abrs.induct)
  case (1 x a b)
  then show ?case by simp
next
  case (2 ts a b)
  then show ?case by simp
next
  case (3 a b)
  then show ?case by simp
next
  case (4 t ts a b)
  then show ?case
    by (simp add: Let_def abr01_negate(3))
qed

subsubsection \<open>Relationship to \<open>foldr\<close>\<close>

fun foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
"foldr f v [] = v" |
"foldr f v (x#xs) = f x (foldr f v xs)"

definition "abrsf b = (\<lambda>t m. if m \<ge> b then m else max (- abr t (-b) (-m)) m)"

lemma abrs_foldr: "abrs ts a b = foldr (abrsf b) a ts"
by(induction ts arbitrary: a) (auto simp: abrsf_def Let_def)

text \<open>A direct (rather than mutually) recursive def of \<open>abr\<close>\<close>
lemma abr_Nd_foldr:
  "abr (Nd ts) a b = foldr (abrsf b) a ts"
by (simp add: abrs_foldr)

text \<open>Direct correctness proof of \<open>foldr\<close> version is no simpler than proof via \<open>abr/abrs\<close>:\<close>

lemma fishburn_abr_foldr: "a < b \<Longrightarrow> fishburn a b (negmax t) (abr t a b)"
proof(induction t arbitrary: a b)
  case (Lf)
  then show ?case by simp
next
  case (Nd ts)
  then show ?case
  proof(induction ts)
    case Nil
    then show ?case apply simp using linorder_not_less by blast
  next
    case (Cons t ts)
    then show ?case using Nd
      apply (simp add: abrsf_def abr_Nd_foldr)
      by (smt (verit) max.absorb3 max.bounded_iff max.commute minus_le_minus nle_le nless_le uminus_less_reorder)
  qed
qed


text \<open>The long proofs that follows are duplicated from the \<open>bounded_linorder\<close> section.\<close>

subsubsection \<open>\<open>fishburn\<close> Proofs\<close>

lemma abrs_ge_a: "abrs ts a b \<ge> a"
by (simp add: abr_abr0(2) abrs0_ge_a)

text \<open>Automatic correctness proof, also works for @{const knuth} instead of @{const fishburn}:\<close>

corollary fishburn_abr_negmax:
  shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (abr t a b)"
    and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (abrs ts a b)"
apply (metis abr_abr0(1) negmax_maxmin fishburn_abr01(1))
by (metis abr.simps(2) abr_abr0(1) negmax_maxmin fishburn_abr01(1))

corollary knuth_abr_negmax: "a < b \<Longrightarrow> knuth a b (negmax t) (abr t a b)"
by (meson order.trans fishburn_abr_negmax(1))

corollary abr_cor: "abr t \<bottom> \<top> = negmax t"
by (metis (mono_tags) bot.extremum_strict knuth_abr_negmax knuth_bot_top linorder_not_less)

text \<open>Detailed \<open>fishburn2\<close> proof (85 lines):\<close>

theorem fishburn2_abr:
  shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (abr t a b)"
    and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (abrs ts a b)"
unfolding fishburn2
proof(induction t a b and ts a b rule: abr_abrs.induct)
  case (4 t ts a b)
(*
thus ?case
apply(simp add: Let_def)
  by (smt (verit, ccfv_threshold) ereal_minus_less_minus ereal_uminus_less_reorder linorder_not_le max.absorb_iff2 max.order_iff nle_le order.strict_trans1)
*)
  let ?m = "abrs ts a b"
  let ?ab = "abrs (t # ts) a b"
  let ?nm1 = "negmax t"
  let ?nms = "negmax (Nd ts)"
  let ?nm1s = "negmax (Nd (t # ts))"
  let ?r = "abr t (- b) (- ?m)"

  have 1: "?nm1s \<le> ?ab" if asm: "?ab < b"
  proof -
    have "\<not> b \<le> ?m" using asm by(auto simp add: Let_def)
    hence "?ab = max (- ?r) ?m" by(simp add: Let_def)
    hence "- b < ?r" using uminus_less_reorder asm by auto
    have \<open>?nm1s = max (- ?nm1) ?nms\<close> by simp
    also have "\<dots> \<le> max (- ?r) ?m"
    proof -
      have "- ?nm1 \<le> - ?r"
        using "4.IH"(2)[OF refl, THEN conjunct1] \<open>- b < ?r\<close> \<open>\<not> b \<le> ?m\<close> by auto
      moreover have "?nms \<le> ?m"
        using "4.IH"(1)[OF \<open>a < b\<close>, THEN conjunct2] \<open>\<not> b \<le> ?m\<close> leI by blast
      ultimately show ?thesis by (metis max.mono)
    qed
    also note \<open>?ab = max (- ?r) ?m\<close>[symmetric]
    finally show ?thesis .
  qed

  have 2: "?ab \<le> ?nm1s" if "a < ?ab"
  proof cases
    assume "b \<le> ?m"
    have "?ab = ?m" using \<open>b \<le> ?m\<close> by(simp)
    also have "\<dots> \<le> ?nms" using "4.IH"(1)[OF \<open>a < b\<close>, THEN conjunct1]
      by (metis order.strict_trans2[OF \<open>a<b\<close> \<open>b \<le> ?m\<close>])
    also have "\<dots> \<le> max (-?nm1) ?nms"
      using max.cobounded2 by blast
    also have "\<dots> = ?nm1s" by simp
    finally show ?thesis .
  next
    assume "\<not> b \<le> ?m"
    hence IH2: "?r < - ?m \<longrightarrow> ?nm1 \<le> ?r"
        using "4.IH"(2)[OF refl,THEN conjunct2] minus_less_minus linorder_not_le by blast
    have "a < ?m \<or> \<not> a < ?m \<and> a < - ?r" using \<open>a < ?ab\<close> \<open>\<not> b \<le> ?m\<close>
      by(auto simp: Let_def less_max_iff_disj)
    then show ?thesis
    proof
      assume "a < ?m"
      hence IH1: "?m \<le> ?nms"
        using "4.IH"(1)[OF \<open>a<b\<close>, THEN conjunct1] by blast
      have 1: "- ?r \<le> ?nm1s"
      proof cases
        assume "?r < - ?m"
        thus ?thesis using IH2 by (simp add: le_max_iff_disj)
      next
        assume "\<not> ?r < - ?m"
        thus ?thesis using IH1
          apply simp
          by (smt (verit) le_max_iff_disj linorder_le_less_linear order.trans that uminus_le_reorder)
      qed
      have 2: "?m \<le> ?nm1s"
        using IH1 by(auto simp: le_max_iff_disj)
      show ?thesis
        using \<open>\<not> b \<le> ?m\<close> 1 2 by(simp add: Let_def not_le_imp_less)
    next
      assume a: "\<not> a < ?m \<and> a < - ?r"
      have 1 : "- ?r \<le> - ?nm1"
        using \<open>\<not> a < ?m \<and> a < - ?r\<close> IH2 less_uminus_reorder
        by (metis abrs_ge_a linorder_not_le minus_le_minus nle_le)
      have 2: "?m \<le> - ?nm1"
        using a "4.IH"(1)[OF \<open>a<b\<close>, THEN conjunct1] 1
        by (meson dual_order.strict_iff_not order.trans nle_le)
      have "?ab = max (- ?r) ?m"
        using a \<open>\<not> b \<le> ?m\<close> by(simp add: Let_def)
      also have "\<dots> \<le> max (- ?nm1) ?nms"
        using 1 2 by (simp add: max.coboundedI1)
      also have "\<dots> = ?nm1s"
        by simp
      finally show ?thesis .
    qed
  qed
  show ?case using 1 2 by blast
qed auto

text \<open>Detailed \<open>fishburn\<close> proof (100 lines):\<close>

theorem fishburn_abr:
  shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (abr t a b)"
    and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (abrs ts a b)"
proof(induction t a b and ts a b rule: abr_abrs.induct)
  case (4 t ts a b)
  let ?m = "abrs ts a b"
  let ?ab = "abrs (t # ts) a b"
  let ?r = "abr t (- b) (- ?m)"
  let ?nm1 = "negmax t"
  let ?nms = "negmax (Nd ts)"
  let ?nm1s = "negmax (Nd (t # ts))"
  have "?nm1s = max (- ?nm1) ?nms" by simp

  have 1: "?nm1s \<le> ?ab" if asm: "?ab \<le> a"
  proof -
    have "\<not> b \<le> ?m" by (rule ccontr) (use \<open>?ab \<le> a\<close> \<open>a < b\<close> in simp) (* more detail *)
    hence *: "?ab = max (- ?r) ?m" by(simp add: Let_def)
    hence "?m \<le> a" "- ?r \<le> a" using asm by auto
    have "- b < ?r" using \<open>- ?r \<le> a\<close> \<open>a < b\<close> uminus_less_reorder order_le_less_trans by blast
    note \<open>?nm1s = _\<close>
    also have "max (- ?nm1) ?nms \<le> max (- ?r) ?m"
    proof -
      have "- ?nm1 \<le> - ?r"
      proof cases (* uses totality of the ordering here (and in other places) *)
        assume "- ?m \<le> ?r"
        thus ?thesis using "4.IH"(2)[THEN conjunct2, THEN conjunct2] \<open>\<not> b \<le> ?m\<close> by auto
      next
        assume "\<not> - ?m \<le> ?r"
        thus ?thesis using  "4.IH"(2)[THEN conjunct2, THEN conjunct1] \<open>\<not> b \<le> ?m\<close> \<open>- b < ?r\<close> by (simp)
      qed
      moreover have "?nms \<le> ?m"
        using \<open>?m \<le> a\<close> "4.IH"(1)[OF "4.prems", THEN conjunct1] by (auto)
      ultimately show ?thesis by (metis max.mono)
    qed
    also note *[symmetric]
    finally show ?thesis .
  qed

  have 2: "?ab \<le> ?nm1s" if "b \<le> ?ab"
  proof cases
    assume "?m \<ge> b"
    show ?thesis using \<open>?m \<ge> b\<close>
      using "4.IH"(1)[OF \<open>a < b\<close>,THEN conjunct2,THEN conjunct2] max.coboundedI2 by auto
  next
    assume "\<not> ?m \<ge> b"
    hence "?ab = max (-?r) ?m" by(simp add: Let_def)
    hence "-?r \<ge> b" using \<open>b \<le> ?ab\<close> \<open>\<not> ?m \<ge> b\<close> by (metis le_max_iff_disj)
    hence "?ab = -?r"
      using \<open>?ab = _\<close> \<open>\<not> b \<le> ?m\<close> by(metis not_le_imp_less less_le_trans max.absorb3)
    also have "\<dots> \<le> - ?nm1" using  "4.IH"(2)[OF refl,THEN conjunct1] \<open>\<not> b \<le> ?m\<close> \<open>b \<le> -?r\<close>
      by (metis minus_le_minus uminus_le_reorder linorder_not_le)
    also have "\<dots> \<le> max (- ?nm1) ?nms" by auto
    also note  \<open>?nm1s = \<dots>\<close>[symmetric]
    finally show ?thesis .
  qed

  have 3: "?ab = ?nm1s" if asm: "a < ?ab" "?ab < b"
  proof -
    have "\<not> b \<le> ?m" by (rule ccontr) (use \<open>?ab < b\<close> in simp) (* more detail *)
    hence *: "?ab = max (- ?r) ?m" by(simp add: Let_def)
    hence "- ?r < b" using \<open>?ab < b\<close> by auto
    note *
    also have "max (- ?r) ?m = ?nm1s"
    proof -
      have "?r = ?nm1 \<and> ?nms \<le> - ?r" if \<open>\<not> - ?r \<le> ?m\<close>
      proof
        have " - b < ?r \<and> ?r < - ?m"
          using \<open>- ?r < b\<close> \<open>\<not> - ?r \<le> ?m\<close>
          by (metis minus_less_minus neg_neg linorder_not_le)
        thus "?r = ?nm1"
          using "4.IH"(2)[OF refl, THEN conjunct2,THEN conjunct1] \<open>\<not> b \<le> ?m\<close>
          using order.strict_trans by blast
        show "?nms \<le> - ?r"
        proof cases
          assume "?m \<le> a"
          thus ?thesis using "4.IH"(1)[OF \<open>a<b\<close>,THEN conjunct1] \<open>\<not> - ?r \<le> ?m\<close> by simp
        next
          assume "\<not> ?m \<le> a"
          thus ?thesis
            using "4.IH"(1)[OF \<open>a<b\<close>,THEN conjunct2, THEN conjunct1] \<open>\<not> - ?r \<le> ?m\<close> \<open>\<not> b \<le> ?m\<close> by auto
        qed
      qed
      moreover have "?m = ?nms \<and> - ?nm1 \<le> ?m" if "- ?r \<le> ?m"
      proof
        note \<open>a < ?ab\<close>
        also note *
        also have "max (- ?r) ?m = ?m" using \<open>- ?r \<le> ?m\<close> using max.absorb2 by blast
        finally have "a < ?m" .
        thus "?m = ?nms"
          using "4.IH"(1)[OF \<open>a < b\<close>,THEN conjunct2,THEN conjunct1] \<open>\<not> b \<le> ?m\<close> not_le by blast
        have "- ?nm1 \<le> - ?r"
          using  "4.IH"(2)[OF refl,THEN conjunct2,THEN conjunct2]  \<open>\<not> b \<le> ?m\<close>  \<open>- ?r \<le> ?m\<close>
          by (metis neg_neg not_le minus_le_minus)
        also note \<open>- ?r \<le> ?m\<close>
        finally show "- ?nm1 \<le> ?m" .
      qed
      ultimately show ?thesis using \<open>?nm1s = _\<close> by fastforce
    qed
    finally show ?thesis .
  qed
  show ?case using 1 2 3 by blast
qed auto


subsubsection \<open>Explicit equational @{const knuth} proofs via min/max\<close>

text \<open>Not mm, only min and max. Only min in abrs. \<open>a<b\<close> required: a=1, b=-1, t=[]\<close>

theorem shows abr_negmax3: "max a (min (abr t a b) b) = max a (min (negmax t) b)"
    and "a < b \<Longrightarrow> min (abrs ts a b) b = max a (min (negmax (Nd ts)) b)"
proof(induction t a b and ts a b rule: abr_abrs.induct)
  case (2 ts a b)
  then show ?case apply simp
    by (metis max_def min.strict_boundedE order_neq_le_trans)
next
  case (4 t ts a b)
  let ?abts = "abrs ts a b" let ?abt = "abr t (- b) (- ?abts)"
  show ?case
  proof (cases "b \<le> ?abts")
    case True
    thus ?thesis using "4.IH"(1)[OF "4.prems"] apply (simp add: Let_def)
      by (metis (no_types) max.left_commute max_min_same(2) min.commute min_max_distrib2)
  next
    case False
(* automatic:
    show ?thesis apply (simp add: Let_def) using 4
      by (smt (verit) Orderings.order_eq_iff antisym_conv3 ereal_uminus_eq_reorder max.absorb1 max.commute max.left_commute de_morgan_min min.absorb3 min.commute min.orderI)
*)
    have IH2: "min b (max (-?abt) ?abts) = min b (max (- negmax t) ?abts)"
      using "4.IH"(2) False by (metis (no_types) neg_neg de_morgan_max)
    have "min (abrs (t # ts) a b) b = min (max (- ?abt) ?abts) b"
      using False by (simp add: Let_def)
    also have "\<dots> = min b (max (- ?abt) ?abts)"
      by (metis min.commute)
    also have "\<dots> = min b (max (- negmax t) ?abts)"
      using IH2 by blast
    also have "\<dots> = max (min (- negmax t) b) (min ?abts b)"
      by (metis min.commute min_max_distrib2)
    also have "\<dots> = max (min (- negmax t) b) (max a (min (negmax (Nd ts)) b))"
      using "4.IH"(1)[OF "4.prems"] by presburger
    also have "\<dots> = max a (min (max (- negmax t) (negmax (Nd ts))) b)"
      by (metis max.left_commute min_max_distrib1)
    finally show ?thesis by simp
  qed
qed auto

text \<open>Not mm, only min and max. Also max in abrs:\<close>

theorem shows abr_negmax2: "max a (min (abr t a b) b) = max a (min (negmax t) b)"
    and "a < b \<Longrightarrow> max a (min (abrs ts a b) b) = max a (min (negmax (Nd ts)) b)"
proof(induction t a b and ts a b rule: abr_abrs.induct)
  case 2
  thus ?case apply simp
    by (metis max.orderE min.strict_boundedE not_le_imp_less)
  case (4 t ts a b)
  let ?abts = "abrs ts a b" let ?abt = "abr t (- b) (- ?abts)"
  show ?case
  proof (cases "b \<le> ?abts")
    case True
    thus ?thesis using "4.IH"(1)[OF "4.prems"] apply (simp add: Let_def)
      by (metis (no_types) max.left_commute max_min_same(2) min.commute min_max_distrib2)
  next
    case False
(* automatic:
    show ?thesis apply (simp add: Let_def) using 4
      by (smt (z3) False ereal_uminus_eq_reorder ereal_uminus_less_reorder max.left_commute de_morgan_min min.absorb_iff2 min.commute min.strict_order_iff min_max_distrib1 de_morgan_max nle_le)
*)
    hence "max a (min (abrs (t # ts) a b) b) = max a (min (max (- ?abt) ?abts) b)"
      by (simp add: Let_def linorder_not_le)
    also have "\<dots> = max a (-(max (min ?abt (- ?abts)) (-b)))"
      by (metis neg_neg de_morgan_max)
    also have "\<dots> = max a (-(max (-b) (min ?abt (- ?abts))))"
      by (metis max.commute)
    also have "\<dots> = max a (-(max (- b) (min (negmax t) (- ?abts))))"
      using "4.IH"(2)[OF refl] False by (simp add: linorder_not_le)
    also have "\<dots> = max a ((min b (max (- negmax t) ?abts)))"
      by (metis neg_neg de_morgan_min)
    also have "\<dots> = max (min (- negmax t) b) (max a (min ?abts b))"
      by (metis max.left_commute min.commute min_max_distrib2)
    also have "\<dots> = max (min (- negmax t) b) (max a (min (negmax (Nd ts)) b))"
      using "4.IH"(1)[OF "4.prems"] by presburger
    also have "\<dots> = max a (min (max (- negmax t) (negmax (Nd ts))) b)"
      by (metis max.left_commute min_max_distrib1)
    finally show ?thesis by simp
  qed
qed auto


subsubsection "Relating iteration from right and left"

text \<open>Enables porting \<open>abr\<close> lemmas to \<open>ab_negmax\<close> lemmas, eg correctness.\<close>

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror (Lf x) = Lf x" |
"mirror (Nd ts) = Nd (rev (map mirror ts))"

lemma abrs_append:
  "abrs (ts1 @ ts2) a b = (let m = abrs ts2 a b in if m \<ge> b then m else abrs ts1 m b)"
by(induction ts1 arbitrary: ts2) (auto simp add: Let_def)

lemma ab_negmax_abr_mirror:
shows "a<b \<Longrightarrow> ab_negmax a b t = abr (mirror t) a b"
  and "a<b \<Longrightarrow> ab_negmaxs a b ts = abrs (rev (map mirror ts)) a b"
proof(induction a b t and a b ts rule: ab_negmax_ab_negmaxs.induct)
  case 4
  then show ?case by (fastforce simp: Let_def abrs_append max.commute)
qed auto

lemma negmax_mirror:
fixes t :: "'a::de_morgan_order tree" and ts :: "'a::de_morgan_order tree list"
shows "negmax (mirror t) = negmax t \<and> negmax (Nd (rev (map mirror ts))) = negmax (Nd ts)"
by(rule compat_tree_tree_list.induct)(auto simp: max.commute maxs_rev maxs_append)

text \<open>Correctness of \<open>ab_negmax\<close> from correctness of \<open>abr\<close>:\<close>

theorem fishburn_ab_negmax_negmax_mirror:
shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (ab_negmax a b t)"
  and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (ab_negmaxs a b ts)"
apply (metis (no_types) ab_negmax_abr_mirror(1) negmax_mirror fishburn_abr_negmax(1))
by (metis (no_types) ab_negmax_abr_mirror(2) negmax_mirror fishburn_abr_negmax(2))


subsection \<open>From the Right, Fail-Soft \<close>

text \<open>Starting at \<open>\<bottom>\<close> (after Fishburn)\<close>

fun abr' :: "('a::de_morgan_order)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abrs' where
"abr' (Lf x) a b = x" |
"abr' (Nd ts) a b = abrs' ts a b" |

"abrs' [] a b = \<bottom>" |
"abrs' (t#ts) a b = (let m = abrs' ts a b in
  if m \<ge> b then m else max (- abr' t (-b) (- max m a)) m)"


lemma abr01'_negate:
shows "abr0' (negate f t) a b = - abr1' (negate (\<not>f) t) (-a) (-b)"
and  "abrs0' (map (negate f) ts) a b = - abrs1' (map (negate (\<not>f)) ts) (-a) (-b)"
and "abr1' (negate f t) a b = - abr0' (negate (\<not>f) t) (-a) (-b)"
and  "abrs1' (map (negate f) ts) a b = - abrs0' (map (negate (\<not>f)) ts) (-a) (-b)"
proof(induction "negate f t" a b and "map (negate f) ts" a b and "negate f t" a b and "map (negate f) ts" a b arbitrary: f t and f ts and f t and f ts rule: abr0'_abrs0'_abr1'_abrs1'.induct)
  case (1 x a b)
  from Lf_eq_negateD[OF this] show ?case by simp
next
  case (2 ts a b)
  from Nd_eq_negateD[OF 2(2)] 2(1) show ?case by auto
next
  case (3 a b)
  then show ?case by simp
next
  case (4 t ts a b)
  from Cons_eq_map_D[OF 4(3)] 4(1) 4(2)[OF refl] show ?case
    apply (clarsimp simp add: Let_def de_morgan_max de_morgan_min)
    by (metis neg_neg uminus_le_reorder)
next
  case (5 x a b)
  from Lf_eq_negateD[OF this] show ?case by simp
next
  case (6 ts a b)
  from Nd_eq_negateD[OF 6(2)] 6(1) show ?case by auto
next
  case (7 a b)
  then show ?case by simp
next
  case (8 t ts a b)
  from Cons_eq_map_D[OF 8(3)] 8(1) 8(2)[OF refl] show ?case
    by (auto simp: Let_def de_morgan_max de_morgan_min uminus_le_reorder)
qed

lemma abr_abr0':
 shows "abr' t a b = abr0' (negate False t) a b"
 and "abrs' ts a b = abrs0' (map (negate True) ts) a b"
proof (induction t a b and ts a b rule: abr'_abrs'.induct)
  case (1 x a b)
  then show ?case by simp
next
  case (2 ts a b)
  then show ?case by simp
next
  case (3 a b)
  then show ?case by simp
next
  case (4 t ts a b)
  then show ?case
    by (simp add: Let_def abr01'_negate(3))
qed

corollary fishburn_abr'_negmax_cor:
  shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (abr' t a b)"
    and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (abrs' ts a b)"
apply (metis abr_abr0'(1) negmax_maxmin fishburn_abr01'(1))
by (metis abr'.simps(2) abr_abr0'(1) negmax_maxmin fishburn_abr01'(1))

lemma abr'_exact: "\<lbrakk> v = negmax t; a \<le> v \<and> v \<le> b\<rbrakk> \<Longrightarrow> abr' t a b = v"
by (simp add: abr0'_exact abr_abr0'(1) negmax_maxmin)


text \<open>Now a lot of copy-paste-modify from \<open>bounded_linorder\<close>.\<close>

theorem (*fishburn_abr_abr': The point: can prove the r version below very simply;
 l version trickier: see \<open>fishburn_abl_abl'\<close> *) 
  shows "a < b \<Longrightarrow> fishburn a b (abr' t a b) (abr t a b)"
    and "a < b \<Longrightarrow> fishburn a b (abrs' ts a b) (abrs ts a b)"
proof(induction t a b  and ts a b rule: abr_abrs.induct)
  case (4 t ts a b)
  then show ?case apply (simp add: Let_def)
    by (smt (verit) order_eq_iff abrs_ge_a le_max_iff_disj less_uminus_reorder max_def minus_less_minus nless_le)
qed auto

theorem fishburn2_abr_abr':
  shows "a < b \<Longrightarrow> fishburn a b (abr' t a b) (abr t a b)"
    and "a < b \<Longrightarrow> fishburn a b (abrs' ts a b) (abrs ts a b)"
unfolding fishburn2
proof(induction t a b  and ts a b rule: abr_abrs.induct)
  case (4 t ts a b)
(* automatic:
  thus ?case apply (simp add: Let_def)
    by (smt (verit, ccfv_SIG) abrs_ge_a ereal_minus_less_minus ereal_uminus_less_reorder less_eq_ereal_def linorder_linear max.absorb_iff2 max.cobounded2 max.coboundedI1 max.strict_order_iff)
*)
  let ?m = "abrs ts a b"
  let ?ab = "abrs (t # ts) a b"
  let ?r = "abr t (- b) (- ?m)"
  let ?m' = "abrs' ts a b"
  let ?ab' = "abrs' (t # ts) a b"
  let ?r' = "abr' t (- b) (- max ?m' a)"
  note IH1 = "4.IH"(1)[OF \<open>a < b\<close>] note IH11 = IH1[THEN conjunct1] note IH12 = IH1[THEN conjunct2]

  have 1: "?ab \<le> ?ab'" if "a < ?ab"
  proof cases
    assume "b \<le> ?m"
    thus ?thesis using IH11 \<open>a<b\<close> by (auto simp: Let_def)
  next
    assume "\<not> b \<le> ?m"
    hence "?ab = max (- ?r) ?m" by (simp add: Let_def)
    hence "a < max (- ?r) ?m" using \<open>a < ?ab\<close> by presburger
    have IH22: "?r < - ?m \<longrightarrow> abr' t (- b) (- ?m) \<le> ?r"
      using \<open>\<not> b \<le> ?m\<close> "4.IH"(2) by auto
    have "\<not> b \<le> ?m'" using IH12 \<open>\<not> b \<le> ?m\<close> by auto
    hence "?ab' = max (- ?r') ?m'" by (simp add: Let_def)
    have "?m' \<le> ?m" using IH12 \<open>\<not> b \<le> ?m\<close> linorder_not_le by blast
    have "max ?m' a = ?m"
    proof cases
      assume "?m \<le> a"
      thus ?thesis using \<open>?m' \<le> ?m\<close> abrs_ge_a
        by (metis max.absorb1 max.commute)
    next
      assume "\<not> ?m \<le> a"
      thus ?thesis using IH11 \<open>?m' \<le> ?m\<close> by auto
    qed
    have "- ?r \<le> max (- ?r') ?m'"
    proof cases
      assume "?r < - ?m"
      thus ?thesis using IH22 \<open>max ?m' a = ?m\<close>
        by (simp add: max.coboundedI1) (* more detail *)
    next
      assume "\<not> ?r < - ?m"
      hence "?m = ?m'" using \<open>a < max (-?r) ?m\<close> \<open>max ?m' a = ?m\<close>
        by (metis linorder_not_le max.commute max.order_iff nle_le uminus_le_reorder)
      thus \<open>- ?r \<le> max (- ?r') ?m'\<close> using \<open>\<not> ?r < - ?m\<close>
        by (simp add: max.coboundedI2 uminus_le_reorder)
    qed
    moreover have "?m \<le> max (- ?r') (?m')"
    proof cases
      assume "a < ?m"
      hence "?m \<le> ?m'" using IH11 by simp
      then show ?thesis using le_max_iff_disj by blast
    next
      assume "\<not> a < ?m"
      hence "?m \<le> a" by simp
      also have "a < - ?r" using \<open>a < max (-?r) ?m\<close> \<open>\<not> a < ?m\<close> less_max_iff_disj by blast
      also note \<open>- ?r \<le> max (- ?r') ?m'\<close>
      finally show ?thesis using order.order_iff_strict by blast 
    qed
    ultimately show ?thesis using \<open>?ab = _\<close> \<open>?ab' = _\<close> by (metis max.bounded_iff)
  qed

  have 2: "?ab' \<le> ?ab" if "?ab < b"
  proof cases
    assume "b \<le> ?m"
    thus ?thesis
      using \<open>?ab < b\<close> by (simp add: Let_def)
  next
    assume "\<not> b \<le> ?m"
    hence "- ?r < b" using \<open>?ab < b\<close> by(auto simp: Let_def)
    with "4.IH"(2) \<open>\<not> b \<le> ?m\<close>
    have IH21: "?r \<le> abr' t (- b) (- ?m)"
      by (metis linorder_le_less_linear minus_less_minus uminus_less_reorder)
    have "\<not> b \<le> ?m'" "?m' \<le> ?m" using IH12 \<open>\<not> b \<le> ?m\<close> by auto
    have "?ab = max (- ?r) ?m" using \<open>\<not> b \<le> ?m\<close> by (simp add: Let_def)
    hence "?ab' = max (- ?r') ?m'" using \<open>\<not> b \<le> ?m'\<close> by (simp add: Let_def)
    have "- ?r' \<le> - ?r"
    proof cases
      assume "a < ?m"
      hence "?m' = ?m" using IH11 \<open>?m' \<le> ?m\<close> nle_le by blast
      hence "- ?r' = - abr' t (- b) (- ?m)" using \<open>a < ?m\<close> by simp
      also have "\<dots> \<le> - ?r" using IH21 minus_le_minus by blast
      finally show ?thesis .
    next
      assume "\<not> a < ?m"
      have "?m = a" using \<open>\<not> a < abrs ts a b\<close> abrs_ge_a by (metis order_le_imp_less_or_eq)
      hence "max ?m' a = a" using \<open>?m' \<le> ?m\<close> by simp
      with \<open>?m = a\<close> show ?thesis using IH21 by simp
    qed
    then have "- ?r' \<le> max (- ?r) ?m" using max.coboundedI1 by blast
    hence "max (- ?r') ?m' \<le> max (- ?r) ?m"
      using \<open>?m' \<le> ?m\<close> by (metis max.absorb2 max.bounded_iff max.cobounded2)
    thus ?thesis using \<open>?ab = _\<close> \<open>?ab' = _\<close> by metis
  qed

  show ?case using "1" "2" by blast

qed(auto simp add: bot_ereal_def)

theorem fishburn_abr'_negmax:
  shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (abr' t a b)"
    and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (abrs' ts a b)"
unfolding fishburn2
proof(induction t a b and ts a b rule: abr'_abrs'.induct)
  case (4 t ts a b)
(*
thus ?case
apply(simp add: Let_def)
  by (smt (verit, ccfv_threshold) ereal_minus_less_minus ereal_uminus_less_reorder linorder_not_le max.absorb_iff2 max.order_iff nle_le order.strict_trans1)
*)
  let ?m = "abrs' ts a b"
  let ?ab = "abrs' (t # ts) a b"
  let ?nm1 = "negmax t"
  let ?nms = "negmax (Nd ts)"
  let ?nm1s = "negmax (Nd (t # ts))"
  let ?r = "abr' t (- b) (- max ?m a)"

  have 1: "?nm1s \<le> ?ab" if asm: "?ab < b"
  proof -
    have "\<not> b \<le> ?m" using asm by(auto simp add: Let_def)
    hence "?ab = max (- ?r) ?m" by(simp add: Let_def)
    hence "- b < ?r" using uminus_less_reorder asm by auto
    have \<open>?nm1s = max (- ?nm1) ?nms\<close> by simp
    also have "\<dots> \<le> max (- ?r) ?m"
    proof -
      have "- ?nm1 \<le> - ?r"
        using "4.IH"(2)[OF refl, THEN conjunct1] \<open>a<b\<close> \<open>- b < ?r\<close> \<open>\<not> b \<le> ?m\<close> by auto
      moreover have "?nms \<le> ?m"
        using "4.IH"(1)[OF \<open>a < b\<close>, THEN conjunct2] \<open>\<not> b \<le> ?m\<close> leI by blast
      ultimately show ?thesis by (metis max.mono)
    qed
    also note \<open>?ab = max (- ?r) ?m\<close>[symmetric]
    finally show ?thesis .
  qed

  have 2: "?ab \<le> ?nm1s" if "a < ?ab"
  proof cases
    assume "b \<le> ?m"
    have "?ab = ?m" using \<open>b \<le> ?m\<close> by(simp)
    also have "\<dots> \<le> ?nms" using "4.IH"(1)[OF \<open>a < b\<close>, THEN conjunct1]
      by (metis order.strict_trans2[OF \<open>a<b\<close> \<open>b \<le> ?m\<close>])
    also have "\<dots> \<le> max (-?nm1) ?nms"
      using max.cobounded2 by blast
    also have "\<dots> = ?nm1s" by simp
    finally show ?thesis .
  next
    assume "\<not> b \<le> ?m"
    hence IH2: "?r < - ?m \<longrightarrow> ?nm1 \<le> ?r" (* more detail, esp why \<open>a < ?ab\<close>? *)
      using "4.IH"(2)[OF refl, THEN conjunct2] \<open>a<b\<close> \<open>a < ?ab\<close> by (auto simp: less_uminus_reorder)
    have "a < ?m \<or> \<not> a < ?m \<and> a < - ?r" using \<open>a < ?ab\<close> \<open>\<not> b \<le> ?m\<close>
      by(auto simp: Let_def less_max_iff_disj)
    then show ?thesis
    proof
      assume "a < ?m"
      hence IH1: "?m \<le> ?nms"
        using "4.IH"(1)[OF \<open>a<b\<close>, THEN conjunct1] by blast
      have 1: "- ?r \<le> ?nm1s"
      proof cases
        assume "?r < - ?m"
        thus ?thesis using IH2 by (simp add: le_max_iff_disj)
      next
        assume "\<not> ?r < - ?m"
        thus ?thesis using IH1
          by (simp add: less_uminus_reorder max.coboundedI2)
      qed
      have 2: "?m \<le> ?nm1s"
        using IH1 by(auto simp: le_max_iff_disj)
      show ?thesis
        using \<open>\<not> b \<le> ?m\<close> 1 2 by(simp add: Let_def not_le_imp_less)
    next
      assume a: "\<not> a < ?m \<and> a < - ?r"
      have 1 : "- ?r \<le> - ?nm1"
        using \<open>\<not> a < ?m \<and> a < - ?r\<close> IH2 by (auto simp: less_uminus_reorder)
      have 2: "?m \<le> - ?nm1"
        using a "4.IH"(1)[OF \<open>a<b\<close>, THEN conjunct1] 1
        by (meson dual_order.strict_iff_not order.trans nle_le)
      have "?ab = max (- ?r) ?m"
        using a \<open>\<not> b \<le> ?m\<close> by(simp add: Let_def)
      also have "\<dots> \<le> max (- ?nm1) ?nms"
        using 1 2 by (simp add: max.coboundedI1)
      also have "\<dots> = ?nm1s"
        by simp
      finally show ?thesis .
    qed
  qed
  show ?case using 1 2 by blast
qed (auto simp add: bot_ereal_def)

text \<open>Automatic proof:\<close>

theorem
  shows "a < b \<Longrightarrow> fishburn a b (negmax t)   (abr' t a b)"
    and "a < b \<Longrightarrow> fishburn a b (negmax (Nd ts)) (abrs' ts a b)"
unfolding fishburn2
proof(induction t a b and ts a b rule: abr'_abrs'.induct)
  case (4 t ts a b)
  then show ?case
    apply (simp add: Let_def)
    by (smt (verit, best) abrs_ge_a less_uminus_reorder uminus_less_reorder linorder_not_le max.absorb1 max.absorb_iff2 nle_le order.trans)
qed (auto simp add: bot_ereal_def)


subsubsection \<open>Also returning the searched tree\<close>

text \<open>Hard:\<close>

fun abtr :: "('a::de_morgan_order) tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a tree" and abtrs where
"abtr (Lf x) a b = (x, Lf x)" |
"abtr (Nd ts) a b = (let (m,us) = abtrs ts a b in (m, Nd us))" |

"abtrs [] a b = (a,[])" |
"abtrs (t#ts) a b = (let (m,us) = abtrs ts a b in
  if m \<ge> b then (m,us) else let (n,u) = abtr t (-b) (-m) in (max (-n) m,u#us))"

text \<open>Soft:\<close>

fun abtr' :: "('a::de_morgan_order) tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * 'a tree" and abtrs' where
"abtr' (Lf x) a b = (x, Lf x)" |
"abtr' (Nd ts) a b = (let (m,us) = abtrs' ts a b in (m, Nd us))" |

"abtrs' [] a b = (\<bottom>,[])" |
"abtrs' (t#ts) a b = (let (m,us) = abtrs' ts a b in
  if m \<ge> b then (m,us) else let (n,u) = abtr' t (-b) (- max m a) in (max (-n) m,u#us))"

lemma fst_abtr:
shows "fst(abtr t a b) = abr t a b"
and "fst(abtrs ts a b) = abrs ts a b"
by(induction t a b and ts a b rule: abtr_abtrs.induct)
  (auto simp: Let_def split: prod.split)

lemma fst_abtr':
shows "fst(abtr' t a b) = abr' t a b"
and "fst(abtrs' ts a b) = abrs' ts a b"
by(induction t a b and ts a b rule: abtr'_abtrs'.induct)
  (auto simp: Let_def split: prod.split)

lemma snd_abtr'_abtr:
shows "a < b \<Longrightarrow> snd(abtr' t a b) = snd(abtr t a b)"
and "a < b \<Longrightarrow> snd(abtrs' ts a b) = snd(abtrs ts a b)"
proof(induction t a b and ts a b rule: abtr'_abtrs'.induct)
  case (4 t ts a b)
  then show ?case
    apply(simp add: Let_def split: prod.split)
    using fst_abtr(2) fst_abtr'(2) fishburn2_abr_abr'(2) abrs_ge_a
    by (smt (verit, best) fst_conv le_max_iff_disj linorder_not_le max.absorb1 nle_le sndI)
qed (auto simp add: split_beta)


subsubsection \<open>Fail-Soft Generalized\<close>

fun abir' :: "_ \<Rightarrow> ('a::de_morgan_order)tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and abirs' where
"abir' i0 (Lf x) a b = x" |
"abir' i0 (Nd ts) a b = abirs' i0 (i0 (map (negate True) ts) a) ts a b" |

"abirs' i0 i [] a b = i" |
"abirs' i0 i (t#ts) a b =
  (let m = abirs' i0 i ts a b
   in if m \<ge> b then m else max (- abir' i0 t (- b) (- max m a)) m)"

abbreviation "neg_all \<equiv> negate True o negate False"

lemma neg_all_negate: "neg_all (negate f t) = negate (\<not>f) t"
apply(induction t arbitrary: f)
by auto (metis negate_negate)

lemma abir01'_negate:
shows "\<forall>ts a. i1 ts a = - i0 (map neg_all ts) (-a) \<Longrightarrow>
  abir0' i0 i1 (negate f t) a b = - abir1' i0 i1 (negate (\<not>f) t) (-a) (-b)"
and  "\<forall>ts a. i1 ts a = - i0 (map neg_all ts) (-a) \<Longrightarrow>
  abirs0' i0 i1 i (map (negate f) ts) a b = - abirs1' i0 i1 (-i) (map (negate (\<not>f)) ts) (-a) (-b)"
and "\<forall>ts a. i1 ts a = - i0 (map neg_all ts) (-a) \<Longrightarrow>
  abir1' i0 i1 (negate f t) a b = - abir0' i0 i1 (negate (\<not>f) t) (-a) (-b)"
and  "\<forall>ts a. i1 ts a = - i0 (map neg_all ts) (-a) \<Longrightarrow>
  abirs1' i0 i1 i (map (negate f) ts) a b = - abirs0' i0 i1 (-i) (map (negate (\<not>f)) ts) (-a) (-b)"
proof(induction i0 i1 "negate f t" a b and i0 i1 i "map (negate f) ts" a b and i0 i1 "negate f t" a b and i0 i1 i "map (negate f) ts" a b arbitrary: f t and f ts and f t and f ts rule: abir0'_abirs0'_abir1'_abirs1'.induct)
  case (1 x a b)
  from Lf_eq_negateD this show ?case by fastforce
next
  case (2 i0 i1 ts a b)
  from Nd_eq_negateD[OF 2(2)] 2(1,3) show ?case apply auto
    by (metis comp_apply neg_all_negate)
next
  case (3 a b)
  then show ?case by simp
next
  case (4 i0 i1 i t ts a b)
  from Cons_eq_map_D[OF 4(3)] 4(1,4) 4(2)[OF refl] show ?case
    apply (clarsimp simp: Let_def de_morgan_min de_morgan_max)
    by (metis neg_neg uminus_le_reorder)
next
  case (5 i0 i1 x a b)
  from Lf_eq_negateD this show ?case by fastforce
next
  case (6 i0 i1 ts a b)
  from Nd_eq_negateD[OF 6(2)] 6(1,3) show ?case apply auto
    by (metis (mono_tags) comp_apply neg_all_negate)
next
  case (7 i0 i1 i a b)
  then show ?case by simp
next
  case (8 i0 i1 i t ts a b)
  from Cons_eq_map_D[OF 8(3)] 8(1,4) 8(2)[OF refl] show ?case
    by (auto simp: Let_def de_morgan_max de_morgan_min uminus_le_reorder)
qed
(* Alternative:
lemma abir01'_negate:
shows "\<forall>f ts a. i1 (map (negate f) ts) a = - i0 (map (negate (\<not>f)) ts) (-a) \<Longrightarrow>
  abir0' i0 i1 (negate f t) a b = - abir1' i0 i1 (negate (\<not>f) t) (-a) (-b)"
and  "\<forall>f ts a. i1 (map (negate f) ts) a = - i0 (map (negate (\<not>f)) ts) (-a) \<Longrightarrow>
  abirs0' i0 i1 i (map (negate f) ts) a b = - abirs1' i0 i1 (-i) (map (negate (\<not>f)) ts) (-a) (-b)"
and "\<forall>f ts a. i1 (map (negate f) ts) a = - i0 (map (negate (\<not>f)) ts) (-a) \<Longrightarrow>
  abir1' i0 i1 (negate f t) a b = - abir0' i0 i1 (negate (\<not>f) t) (-a) (-b)"
and  "\<forall>f ts a. i1 (map (negate f) ts) a = - i0 (map (negate (\<not>f)) ts) (-a) \<Longrightarrow>
  abirs1' i0 i1 i (map (negate f) ts) a b = - abirs0' i0 i1 (-i) (map (negate (\<not>f)) ts) (-a) (-b)"
proof(induction i0 i1 "negate f t" a b and i0 i1 i "map (negate f) ts" a b and i0 i1 "negate f t" a b and i0 i1 i "map (negate f) ts" a b arbitrary: f t and f ts and f t and f ts rule: abir0'_abirs0'_abir1'_abirs1'.induct)
  case (1 x a b)
  from Lf_eq_negateD this show ?case by fastforce
next
  case (2 i0 i1 ts a b)
  from Nd_eq_negateD[OF 2(2)] 2(1,3) show ?case by auto
next
  case (3 a b)
  then show ?case by simp
next
  case (4 i0 i1 i t ts a b)
  from Cons_eq_map_D[OF 4(3)] 4(1,4) 4(2)[OF refl] show ?case
    apply (auto simp: Let_def de_morgan_min)
    apply (metis neg_neg uminus_le_reorder)
    apply (metis neg_neg uminus_le_reorder)
    by (simp add: de_morgan_max)
next
  case (5 i0 i1 x a b)
  from Lf_eq_negateD this show ?case by fastforce
next
  case (6 i0 i1 ts a b)
  from Nd_eq_negateD[OF 6(2)] 6(1,3) show ?case by fastforce
next
  case (7 i0 i1 i a b)
  then show ?case by simp
next
  case (8 i0 i1 i t ts a b)
  from Cons_eq_map_D[OF 8(3)] 8(1,4) 8(2)[OF refl] show ?case
    by (auto simp: Let_def de_morgan_max de_morgan_min uminus_le_reorder)
qed
*)

lemma abir'_abir0':
shows "abir' i0 t a b
  = abir0' i0 (\<lambda>ts a. - i0 (map neg_all ts) (-a)) (negate False t) a b"
and "abirs' i0 i ts a b
  = abirs0' i0 (\<lambda>ts a. - i0 (map neg_all ts) (-a)) i (map (negate True) ts) a b"
proof(induction i0 t a b and i0 i ts a b rule: abir'_abirs'.induct)
  case (1 i0 x a b)
  then show ?case by simp
next
  case (2 i0 ts a b)
  then show ?case by simp
next
  case (3 i0 i a b)
  then show ?case by simp
next
  case (4 i0 i t ts a b)
  then show ?case
    by (auto simp add: Let_def abir01'_negate(3) o_def)
qed


corollary fishburn_abir'_negmax_cor:
  shows "a < b \<Longrightarrow> bnd i0 (\<lambda>ts a. - i0 (map neg_all ts) (-a)) \<Longrightarrow> fishburn a b (negmax t)           (abir' i0 t a b)"
    and "a < b \<Longrightarrow> bnd i0 (\<lambda>ts a. - i0 (map neg_all ts) (-a)) \<Longrightarrow> fishburn a b (max i (negmax (Nd ts))) (abirs' i0 i ts a b)"
unfolding bnd_def
apply (metis (no_types, lifting) bnd_def abir'_abir0'(1) negmax_maxmin fishburn_abir01'(1))
by (smt (verit, ccfv_threshold) bnd_def abir'_abir0'(2) negate.simps(2) negmax_maxmin fishburn_abir01'(2))

end
