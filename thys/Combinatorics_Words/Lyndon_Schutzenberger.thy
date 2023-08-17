(*  Title:      CoW_Equations/Lyndon_Schutzenberger.thy
    Author:     Štěpán Holub, Charles University
    Author:     Štěpán Starosta, CTU in Prague

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Lyndon_Schutzenberger
  imports Submonoids Periodicity_Lemma

begin

chapter \<open>Lyndon-Schützenberger Equation\<close>

section \<open>The original result\<close>

text\<open>The Lyndon-Schützenberger equation is the following equation:
\[
x^ay^b = z^c,
\]
in this formalization denoted as @{term "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c"}.

We formalize here a complete solution of this equation.

The main result, proved by Lyndon and Schützenberger is that the equation has periodic solutions only in free groups if $2 \leq a,b,c$
In this formalization we consider the equation in words only. Then the original result can be formulated as saying that all words
$x$, $y$ and $z$ satisfying the equality ith $2 \leq a,b,c$ pairwise commute.

The result in free groups was first proved in @{cite LySch62}.
For words, there are several proofs to be found in the literature (for instance @{cite Lo83 and Dmsi2006}).
The presented proof is the authors' proof.

In addition, we give a full parametric solution of the equation for any $a$, $b$ and $c$.
\<close>

section "The original result"

text\<open>If $x^a$ or $y^b$ is sufficiently long, then the claim follows from the Periodicity Lemma.\<close>

lemma LS_per_lemma_case1:
  assumes eq: "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c" and "0 < a" and "0 < b" and "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| - 1 \<le> \<^bold>|x\<^sup>@a\<^bold>|"
  shows "x \<cdot> y = y \<cdot> x" and "x \<cdot> z = z \<cdot> x"
proof
  have "x\<^sup>@a \<le>p (z\<^sup>@c) \<cdot> x\<^sup>@a" "x \<^sup>@ a \<le>p x \<cdot> x \<^sup>@ a"
    unfolding eq[symmetric] shifts_rev by blast+
  hence "x\<^sup>@a \<le>p z \<cdot> x\<^sup>@a"
    using eq pref_prod_root triv_pref by metis
  from two_pers_1[OF this \<open>x \<^sup>@ a \<le>p x \<cdot> x \<^sup>@ a\<close> \<open>\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| - 1 \<le> \<^bold>|x \<^sup>@ a\<^bold>|\<close>, symmetric]
  show "x \<cdot> z = z \<cdot> x".
  hence "z\<^sup>@c\<cdot>x\<^sup>@a = x\<^sup>@a\<cdot>z\<^sup>@c"
    by (simp add: comm_add_exps)
  from this[folded eq, unfolded rassoc cancel, symmetric]
  have "x\<^sup>@a \<cdot> y\<^sup>@b = y\<^sup>@b \<cdot> x\<^sup>@a".
  from this[unfolded  comm_pow_roots[OF \<open>0 < a\<close> \<open>0 < b\<close>]]
  show "x \<cdot> y = y \<cdot> x".
qed

text \<open>A weaker version will be often more convenient\<close>
lemma LS_per_lemma_case:
  assumes eq: "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c" and "0 < a" and "0 < b" and "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|"
  shows "x \<cdot> y = y \<cdot> x" and "x \<cdot> z = z \<cdot> x"
  using LS_per_lemma_case1[OF assms(1-3)] assms(4) by force+

text\<open>The most challenging case is when $c = 3$.\<close>

lemma LS_core_case:
  assumes
    eq: "x\<^sup>@a \<cdot> y\<^sup>@b = z\<^sup>@c" and
    "2 \<le> a" and "2 \<le> b" and "2 \<le> c" and
    "c = 3" and
    "b*\<^bold>|y\<^bold>| \<le> a*\<^bold>|x\<^bold>|" and "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" and
    lenx: "a*\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|" and
    leny: "b*\<^bold>|y\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
  shows "x\<cdot>y = y\<cdot>x"
proof-
  have "0 < a" and "0 < b"
    using \<open>2 \<le> a\<close> \<open>2 \<le> b\<close> by auto

\<comment>\<open>We first show that a = 2\<close>
  have "a*\<^bold>|x\<^bold>|+b*\<^bold>|y\<^bold>| = 3*\<^bold>|z\<^bold>|"
    using \<open>c = 3\<close> eq lenmorph[of "x\<^sup>@a" "y\<^sup>@b"]
    by (simp add: pow_len)
  hence "3*\<^bold>|z\<^bold>| \<le> a*\<^bold>|x\<^bold>| + a*\<^bold>|x\<^bold>|"
    using \<open>b*\<^bold>|y\<^bold>| \<le> a*\<^bold>|x\<^bold>|\<close>  by simp
  hence "3*\<^bold>|z\<^bold>| < 2*\<^bold>|z\<^bold>| + 2*\<^bold>|x\<^bold>|"
    using lenx by linarith
  hence "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| < 3 * \<^bold>|x\<^bold>|" by simp
  from less_trans[OF lenx this, unfolded mult_less_cancel2]
  have "a = 2" using \<open>2 \<le> a\<close> by force

  hence "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|" using \<open>b*\<^bold>|y\<^bold>| \<le> a*\<^bold>|x\<^bold>|\<close> \<open>2 \<le> b\<close>
      pow_len[of x 2]  pow_len[of y b]
      mult_le_less_imp_less[of a b "\<^bold>|x\<^bold>|" "\<^bold>|y\<^bold>|"] not_le
    by auto
  have "x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z" using \<open>2 \<le> a\<close> eq \<open>c=3\<close> \<open>a=2\<close>
    by (simp add: numeral_2_eq_2 numeral_3_eq_3)

\<comment> \<open>Find words u, v, w\<close>
  have "\<^bold>|z\<^bold>| < \<^bold>|x\<cdot>x\<^bold>|"
    using \<open>\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| < 3 * \<^bold>|x\<^bold>|\<close> add.commute by auto
  from ruler_le[THEN prefD, OF triv_pref[of z "z\<cdot>z"] _ less_imp_le[OF this]]
  obtain w  where "z\<cdot>w = x\<cdot>x"
    using prefI[of "x\<cdot>x" "y\<^sup>@b" "z\<cdot>z\<cdot>z", unfolded rassoc, OF \<open>x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z\<close>] by fastforce

  have "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|"
    using \<open>a = 2\<close> lenx by auto
  from ruler_le[THEN prefD, OF _ _ less_imp_le[OF this], of "x\<cdot>x\<cdot>y\<^sup>@b", OF triv_pref, unfolded \<open>x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z\<close>, OF triv_pref]
  obtain u :: "'a list" where "x\<cdot>u=z"
    by blast
  have "u \<noteq> \<epsilon>"
    using \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close> \<open>x\<cdot>u = z\<close> by auto
  have "x = u\<cdot>w" using  \<open>z\<cdot>w = x\<cdot>x\<close> \<open>x\<cdot>u = z\<close> by auto

  have "\<^bold>|x\<cdot>x\<^bold>| < \<^bold>|z\<cdot>z\<^bold>|"  by (simp add: \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close> add_less_mono)
  from ruler_le[OF triv_pref[of "x\<cdot>x" "y\<^sup>@b", unfolded  rassoc \<open>x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z\<close>, unfolded lassoc] triv_pref, OF less_imp_le[OF this]]
  have "z\<cdot>w \<le>p z\<cdot>z"
    unfolding \<open>z\<cdot>w = x\<cdot>x\<close>.
  obtain v :: "'a list" where "w \<cdot> v = x"
    using lq_pref[of w x]
      pref_prod_pref'[OF pref_cancel[OF \<open>z\<cdot>w \<le>p z\<cdot>z\<close>, folded \<open>x \<cdot> u = z\<close>, unfolded \<open>x = u \<cdot> w\<close> rassoc], folded  \<open>x = u \<cdot> w\<close>] by blast
  have "u\<cdot>w\<cdot>v \<noteq> \<epsilon>"
    by (simp add: \<open>u \<noteq> \<epsilon>\<close>)

\<comment> \<open>Express x, y and z in terms of  u, v and w\<close>
  hence "z = w\<cdot>v\<cdot>u"
    using \<open>w \<cdot> v = x\<close> \<open>x \<cdot> u = z\<close> by auto
  from \<open>x \<cdot> x \<cdot> y\<^sup>@b = z \<cdot> z \<cdot> z\<close>[unfolded this lassoc, folded \<open>z \<cdot> w = x \<cdot> x\<close>, unfolded this rassoc]
  have "w\<cdot>v \<cdot> u\<cdot>w \<cdot> y\<^sup>@b = w\<cdot>v\<cdot>u\<cdot>w\<cdot>v\<cdot>u\<cdot>w\<cdot>v\<cdot>u".
  hence "y\<^sup>@b = v\<cdot>u\<cdot>w\<cdot>v\<cdot>u"
    using pref_cancel by auto

\<comment> \<open>Double period of uwv\<close>
  from period_fac[OF _ \<open>u\<cdot>w\<cdot>v \<noteq> \<epsilon>\<close>, of v u "\<^bold>|y\<^bold>|", unfolded rassoc, folded this]
  have "period (u\<cdot>w\<cdot>v) \<^bold>|y\<^bold>|"
    using pow_per[OF \<open>y \<noteq> \<epsilon>\<close> \<open>0 < b\<close>] by blast
  have "u\<cdot>w\<cdot>v = x \<cdot>v"
    by (simp add: \<open>x = u \<cdot> w\<close>)
  have "u\<cdot>w\<cdot>v = u\<cdot> x"
    by (simp add: \<open>w \<cdot> v = x\<close>)
  have "u\<cdot>w\<cdot>v <p u \<cdot> (u\<cdot>w\<cdot>v)"
    using \<open>u \<cdot> w \<cdot> v = u \<cdot> x\<close>[unfolded \<open>x = u \<cdot> w\<close>] \<open>u \<noteq> \<epsilon>\<close> triv_pref[of "u \<cdot> u \<cdot> w" v]
    by force
  have "period (u\<cdot>w\<cdot>v) \<^bold>|u\<^bold>|"
    using \<open>u\<cdot>w\<cdot>v <p u \<cdot> (u\<cdot>w\<cdot>v)\<close> by auto

\<comment> \<open>Common period d\<close>
  obtain d::nat where "d=gcd \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|"
    by simp
  have "\<^bold>|y\<^bold>| + \<^bold>|u\<^bold>| \<le> \<^bold>|u\<cdot>w\<cdot>v\<^bold>|" using \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> lenmorph \<open>u\<cdot>w\<cdot>v = u\<cdot> x\<close>
    by simp
  hence "period (u\<cdot>w\<cdot>v) d"
    using \<open>period (u \<cdot> w \<cdot> v) \<^bold>|u\<^bold>|\<close> \<open>period (u \<cdot> w \<cdot> v) \<^bold>|y\<^bold>|\<close> \<open>d = gcd \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close> two_periods
    by blast

\<comment> \<open>Divisibility\<close>
  have "v\<cdot>u\<cdot>z=y\<^sup>@b"
    by (simp add: \<open>y\<^sup>@b = v \<cdot> u \<cdot> w \<cdot> v \<cdot> u\<close> \<open>z = w \<cdot> v \<cdot> u\<close>)
  have "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
    using \<open>x = u \<cdot> w\<close> \<open>w \<cdot> v = x\<close> lenmorph[of u w] lenmorph[of w v] add.commute[of "\<^bold>|u\<^bold>|" "\<^bold>|w\<^bold>|"] add_left_cancel
    by simp
  hence "d dvd \<^bold>|v\<^bold>|" using gcd_nat.cobounded1[of "\<^bold>|v\<^bold>|" "\<^bold>|y\<^bold>|"] gcd.commute[of "\<^bold>|y\<^bold>|" "\<^bold>|u\<^bold>|"]
    by (simp add: \<open>d = gcd \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close>)
  have "d dvd \<^bold>|u\<^bold>|"
    by (simp add: \<open>d = gcd  \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close>)
  have "\<^bold>|z\<^bold>| + \<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| = b*\<^bold>|y\<^bold>|"
    using  lenarg[OF \<open>v\<cdot>u\<cdot>z=y\<^sup>@b\<close>, unfolded lenmorph pow_len] by auto
  from dvd_add_left_iff[OF \<open>d dvd \<^bold>|v\<^bold>|\<close>, of "\<^bold>|z\<^bold>|+\<^bold>|u\<^bold>|", unfolded this dvd_add_left_iff[OF \<open>d dvd \<^bold>|u\<^bold>|\<close>, of "\<^bold>|z\<^bold>|"]]
  have "d dvd \<^bold>|z\<^bold>|"
    using \<open>d = gcd  \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close> dvd_mult by blast
  from lenarg[OF \<open>z = w \<cdot> v \<cdot> u\<close>, unfolded lenmorph pow_len]
  have "d dvd \<^bold>|w\<^bold>|"
    using \<open>d dvd \<^bold>|z\<^bold>|\<close>  \<open>d dvd \<^bold>|u\<^bold>|\<close> \<open>d dvd \<^bold>|v\<^bold>|\<close>  by (simp add: dvd_add_left_iff)
  hence "d dvd \<^bold>|x\<^bold>|"
    using \<open>d dvd \<^bold>|v\<^bold>|\<close> \<open>w \<cdot> v = x\<close> by force

\<comment> \<open>x and y commute\<close>
  have "x \<le>p u\<cdot>w\<cdot>v"
    by (simp add: \<open>x = u \<cdot> w\<close>)
  have "period x d" using per_pref'[OF \<open>x\<noteq>\<epsilon>\<close>  \<open>period (u\<cdot>w\<cdot>v) d \<close> \<open>x \<le>p u \<cdot>w\<cdot>v\<close>].
  hence "x \<in> (take d x)*"
    using \<open>d dvd \<^bold>|x\<^bold>|\<close>
    using root_divisor by blast

  hence "period u d " using \<open>x = u \<cdot> w\<close> per_pref'
    using \<open>period x d\<close> \<open>u \<noteq> \<epsilon>\<close> by blast
  have " take d x = take d u" using \<open>u\<noteq>\<epsilon>\<close>  \<open>x = u \<cdot> w\<close> pref_share_take
    by (simp add: \<open>d = gcd  \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close>)
  from root_divisor[OF \<open>period u d\<close> \<open>d dvd \<^bold>|u\<^bold>|\<close>, folded this]
  have "u \<in> (take d x)*".


  hence "z \<in> (take d x)*"
    using \<open>x\<cdot>u=z\<close> \<open>x \<in> (take d x)*\<close> add_roots by blast
  from root_pref_cancel[OF _ root_pow_root[OF  \<open>x \<in> take d x*\<close>, of a],of "y\<^sup>@b", unfolded eq, OF root_pow_root[OF  this, of c]]
  have "y\<^sup>@b \<in> (take d x)*".
  from  comm_rootI[OF root_pow_root[OF  \<open>x \<in> take d x*\<close>, of a] this]
  show "x \<cdot> y = y \<cdot> x"
    unfolding comm_pow_roots[OF \<open>0 < a\<close> \<open>0 < b\<close>, of x y].
qed


text\<open>The main proof is by induction on the length of $z$. It also uses the reverse symmetry of the equation which is
exploited by two interpretations of the locale @{term LS}. Note also that the case $|x^a| < |y^b|$ is solved by
using induction on $|z| + |y^b|$ instead of just on $|z|$.
\<close>

lemma Lyndon_Schutzenberger':
  "\<lbrakk> x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c;  2 \<le> a;  2 \<le> b; 2 \<le> c \<rbrakk>
  \<Longrightarrow> x\<cdot>y = y\<cdot>x"
proof (induction "\<^bold>|z\<^bold>| + b* \<^bold>|y\<^bold>|" arbitrary: x y z a b c  rule: less_induct)
  case less

  have "0 < a" and "0 < b"
    using \<open>2 \<le> a\<close> \<open>2 \<le> b\<close> by auto

  have LSrev_eq: "rev y \<^sup>@ b \<cdot> rev x \<^sup>@ a = rev z \<^sup>@ c"
    using \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close>
    unfolding rev_append[symmetric] rev_pow[symmetric]
    by blast

  have leneq: "a * \<^bold>|x\<^bold>| + b*\<^bold>|y\<^bold>| = c * \<^bold>|z\<^bold>|"
    using lenarg[OF \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close>] unfolding pow_len lenmorph.

  show "x \<cdot> y = y \<cdot> x"
  proof
    assume "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>"
    show "x \<cdot> y = y \<cdot> x"
    proof (cases "\<^bold>|x \<^sup>@ a\<^bold>| < \<^bold>|y \<^sup>@ b\<^bold>|")

\<comment> \<open>WLOG assumption\<close>
      assume "\<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|y\<^sup>@b\<^bold>|"
      have "\<^bold>|rev z\<^bold>| + a* \<^bold>|rev x\<^bold>| < \<^bold>|z\<^bold>| + b* \<^bold>|y\<^bold>|" using \<open>\<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|y\<^sup>@b\<^bold>|\<close>
        by (simp add: pow_len)
      from "less.hyps"[OF this LSrev_eq \<open>2 \<le> b\<close> \<open>2 \<le> a\<close> \<open>2 \<le> c\<close>, symmetric]
      show "x \<cdot> y = y \<cdot> x"
        unfolding rev_append[symmetric] rev_is_rev_conv by simp
    next
      assume " \<not> \<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|y\<^sup>@b\<^bold>|" hence "\<^bold>|y\<^sup>@b\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|" by force
          \<comment> \<open>case solved by the Periodicity lemma\<close>
      note minus =  Suc_minus2[OF \<open>2 \<le> a\<close>] Suc_minus2[OF \<open>2 \<le> b\<close>]
      consider (with_Periodicity_lemma)
        "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x \<^sup>@ Suc(Suc (a-2))\<^bold>| \<or> \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| \<le> \<^bold>|y \<^sup>@ Suc(Suc (b-2))\<^bold>|" |
        (without_Periodicity_lemma)
        "\<^bold>|x\<^sup>@Suc(Suc (a-2))\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|" and "\<^bold>|y\<^sup>@Suc(Suc (b-2))\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
        unfolding minus
        using not_le_imp_less by blast
      thus "x \<cdot> y = y \<cdot> x"
      proof (cases)
        case with_Periodicity_lemma
        have "x = \<epsilon> \<or> rev y = \<epsilon> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
          by auto
        thus "x \<cdot> y = y \<cdot> x"
          using LS_per_lemma_case[OF \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> \<open>0 < a\<close> \<open>0 < b\<close>]
            LS_per_lemma_case[OF LSrev_eq \<open>0 < b\<close> \<open>0 < a\<close>] with_Periodicity_lemma[unfolded minus]
          unfolding length_rev rev_append[symmetric] rev_is_rev_conv rev_pow[symmetric]
          by linarith
      next
        case without_Periodicity_lemma
        assume lenx: "\<^bold>|x\<^sup>@Suc (Suc (a-2))\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|" and leny: "\<^bold>|y\<^sup>@Suc (Suc (b-2))\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
        have "Suc (Suc (a-2)) * \<^bold>|x\<^bold>| + Suc (Suc (b-2))*\<^bold>|y\<^bold>| < 4 * \<^bold>|z\<^bold>|"
          using  lenx leny unfolding pow_len by fastforce
        hence "c < 4" using leneq unfolding minus  by auto
        consider (c_is_3) "c = 3" | (c_is_2) "c = 2"
          using \<open>c < 4\<close> \<open>2 \<le> c\<close> by linarith
        then show "x \<cdot> y = y \<cdot> x"
        proof(cases)
          case c_is_3
          show "x \<cdot> y = y \<cdot> x"
            using
              LS_core_case[OF \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> \<open>2 \<le> a\<close> \<open>2 \<le> b\<close> \<open>2 \<le> c\<close> \<open>c = 3\<close> \<open>\<^bold>|y\<^sup>@b\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|\<close>[unfolded pow_len]
                _ _ lenx[unfolded pow_len minus] leny[unfolded pow_len minus]]
              \<open>x \<noteq> \<epsilon>\<close> \<open>y \<noteq> \<epsilon>\<close>
            by blast
        next
          assume "c = 2"
          hence eq2: "x\<^sup>@a \<cdot> y\<^sup>@b = z \<cdot> z"
            by (simp add: \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close>)
          from dual_order.trans  le_cases[of "\<^bold>|x\<^sup>@a\<^bold>|" "\<^bold>|z\<^bold>|" "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|", unfolded eq_len_iff[OF this]]
          have "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|"
            using \<open>\<^bold>|y\<^sup>@b\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|\<close> by blast
          define a' where "a' \<equiv> a - 1"
          have "Suc a' = a" and "1 \<le> a'"
            using \<open>2 \<le> a\<close> unfolding a'_def by auto
          from eq2[folded \<open>Suc a' = a\<close>, unfolded pow_Suc' rassoc]  pow_Suc'[of x a', unfolded this, symmetric]
          have eq3: "x \<^sup>@ a' \<cdot> x \<cdot> y \<^sup>@ b = z \<cdot> z" and aa':"x \<^sup>@ a' \<cdot> x = x \<^sup>@ a ".
          hence "\<^bold>|x\<^sup>@a'\<^bold>| < \<^bold>|z\<^bold>|"
            using \<open>Suc a' = a\<close> lenx unfolding  pow_len minus by fastforce
          hence "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|"
            using  mult_le_mono[of 1 a' "\<^bold>|z\<^bold>|" "\<^bold>|x\<^bold>|", OF \<open>1 \<le> a'\<close>, THEN leD] unfolding pow_len
            by linarith
          obtain u w where "x\<^sup>@a'\<cdot>u = z" and "w \<cdot> y\<^sup>@b = z"
            using eqdE[OF eq3[unfolded rassoc] less_imp_le[OF \<open>\<^bold>|x\<^sup>@a'\<^bold>| < \<^bold>|z\<^bold>|\<close>], of thesis]
              eqdE[OF eq2[symmetric]  \<open>\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|\<close>, of thesis] by fast

          have "x\<^sup>@a'\<cdot>x\<cdot>y\<^sup>@b = x\<^sup>@a'\<cdot>u\<cdot>w\<cdot>y\<^sup>@b"
            unfolding lassoc  \<open>x \<^sup>@ a' \<cdot> u = z\<close> \<open>w \<cdot> y\<^sup>@b = z\<close> aa' eq2 cancel..
          hence "u\<cdot>w=x"
            by auto
          hence "\<^bold>|w\<cdot>u\<^bold>| = \<^bold>|x\<^bold>|"
            using swap_len by blast

\<comment> \<open>Induction step: new equation with shorter z\<close>
          have "w\<^sup>@2\<cdot>y\<^sup>@b = (w\<cdot>u)\<^sup>@a"
            unfolding pow_two using \<open>w \<cdot> y \<^sup>@ b = z\<close> \<open>x \<^sup>@ a' \<cdot> u = z\<close> \<open>u\<cdot>w=x\<close> pow_slide[of w u a', unfolded \<open>Suc a' = a\<close>] by simp
          from "less.hyps"[OF _ this _ \<open>2 \<le> b\<close> \<open>2 \<le> a\<close>, unfolded \<open>\<^bold>|w\<cdot>u\<^bold>| = \<^bold>|x\<^bold>|\<close>]
          have "y\<cdot>w = w\<cdot>y"
            using  \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close>  by force

          have "y \<cdot> z = z \<cdot> y"
            unfolding \<open>w \<cdot> y\<^sup>@b = z\<close>[symmetric] lassoc \<open>y\<cdot>w = w\<cdot>y\<close>
            by (simp add: pow_comm)
          hence "z\<^sup>@c\<cdot>y\<^sup>@b = y\<^sup>@b\<cdot>z\<^sup>@c"
            by (simp add: comm_add_exps)
          from this[folded \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close>, unfolded lassoc]
          have "x\<^sup>@a\<cdot>y\<^sup>@b = y\<^sup>@b\<cdot>x\<^sup>@a"
            using cancel_right by blast
          from this[unfolded comm_pow_roots[OF \<open>0 < a\<close> \<open>0 < b\<close>]]
          show "x \<cdot> y = y \<cdot> x".
        qed
      qed
    qed
  qed
qed

theorem Lyndon_Schutzenberger:
  assumes "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c" and  "2 \<le> a"  and "2 \<le> b" and "2 \<le> c"
  shows  "x\<cdot>y = y\<cdot>x" and "x\<cdot>z = z\<cdot>x" and "y\<cdot>z = z\<cdot>y"
proof-
  show "x \<cdot> y = y \<cdot> x"
    using Lyndon_Schutzenberger'[OF assms].
  have "0 < c" and  "0 < b"
    using  \<open>2 \<le> c\<close> \<open>2 \<le> b\<close> by auto
  have "x \<cdot> x\<^sup>@a \<cdot> y\<^sup>@b = x\<^sup>@a \<cdot> y\<^sup>@b \<cdot> x" and "y \<cdot> x\<^sup>@a \<cdot> y\<^sup>@b = x\<^sup>@a \<cdot> y\<^sup>@b \<cdot> y"
    unfolding comm_add_exp[OF \<open>x \<cdot> y = y \<cdot> x\<close>[symmetric], of b]
    unfolding lassoc pow_comm comm_add_exp[OF \<open>x \<cdot> y = y \<cdot> x\<close>, symmetric, of a] by blast+
  thus "x\<cdot>z = z\<cdot>x" and "y\<cdot>z = z\<cdot>y"
    using comm_drop_exp[OF \<open>0 < c\<close>] unfolding lassoc \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> by metis+
qed
hide_fact Lyndon_Schutzenberger' LS_core_case

subsection "Some alternative formulations."

lemma Lyndon_Schutzenberger_conjug: assumes "u \<sim> v" and  "\<not> primitive (u \<cdot> v)" shows "u \<cdot> v = v \<cdot> u"
proof-
  obtain r s where "u = r \<cdot> s" and "v = s \<cdot> r"
    using \<open>u \<sim> v\<close> by blast
  have "u \<cdot> v \<sim> r\<^sup>@2 \<cdot> s\<^sup>@2"
    using conjugI'[of "r \<cdot> s \<cdot> s" r] unfolding \<open>u = r \<cdot> s\<close> \<open>v = s \<cdot> r\<close> pow_two rassoc.
  hence "\<not> primitive (r\<^sup>@2 \<cdot> s\<^sup>@2)"
    using \<open>\<not> primitive (u \<cdot> v)\<close> prim_conjug by auto
  from not_prim_primroot_expE[OF this, of "r \<cdot> s = s \<cdot> r"]
  have "r \<cdot> s = s \<cdot> r"
    using Lyndon_Schutzenberger(1)[of r 2 s 2, OF _ order.refl order.refl] by metis
  thus "u \<cdot> v = v \<cdot> u"
    using \<open>u = r \<cdot> s\<close> \<open>v = s \<cdot> r\<close> by presburger
qed

lemma Lyndon_Schutzenberger_prim: assumes "\<not> primitive x" and "\<not> primitive y" and "\<not> primitive (x \<cdot> y)"
  shows "x \<cdot> y = y \<cdot> x"
proof
  assume "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>"
  from not_prim_primroot_expE[OF \<open>\<not> primitive y\<close>]
  obtain m where "\<rho> y\<^sup>@m = y" and "2 \<le> m".
  from not_prim_primroot_expE[OF \<open>\<not> primitive x\<close>]
  obtain k where "\<rho> x\<^sup>@k = x" and "2 \<le> k".
  from not_prim_primroot_expE[OF \<open>\<not> primitive (x \<cdot> y)\<close>]
  obtain l where "\<rho>(x \<cdot> y)\<^sup>@l = x \<cdot> y" and "2 \<le> l".
  from Lyndon_Schutzenberger(1)[of "\<rho> x" k "\<rho> y" m "\<rho> (x \<cdot> y)" l,
       OF _  \<open>2 \<le> k\<close> \<open>2 \<le> m\<close> \<open>2 \<le> l\<close>]
  show "x \<cdot> y = y \<cdot> x"
    unfolding \<open>\<rho> y\<^sup>@m = y\<close> \<open>\<rho> x\<^sup>@k = x\<close> \<open>\<rho>(x \<cdot> y)\<^sup>@l = x \<cdot> y\<close>
    comp_primroot_conv'[of x y] by blast
qed

lemma Lyndon_Schutzenberger_rotate: assumes "x\<^sup>@c = r \<^sup>@ k \<cdot> u\<^sup>@b \<cdot> r \<^sup>@ k'"
  and "2 \<le> b" and "2 \<le> c" and "0 < k" and "0 < k'"
shows "u \<cdot> r = r \<cdot> u"
proof(rule comm_drop_exps)
  show "u\<^sup>@b \<cdot> r\<^sup>@(k' + k) = r\<^sup>@(k' + k) \<cdot> u\<^sup>@b"
  proof(rule Lyndon_Schutzenberger_prim)
    have "2 \<le> (k' + k)"
      using \<open>0 < k\<close> \<open>0 < k'\<close> by simp
    from pow_nemp_imprim[OF \<open>2 \<le> b\<close>] pow_nemp_imprim[OF this]
    show "\<not> primitive (u\<^sup>@b)" and "\<not> primitive (r \<^sup>@ (k' + k))"
      unfolding Suc_minus2[OF \<open>2 \<le> b\<close>].
    from pow_nemp_imprim[OF \<open>2 \<le> c\<close>]
    have "\<not> primitive (r \<^sup>@ k \<cdot> u\<^sup>@b \<cdot> r \<^sup>@ k')"
      unfolding assms(1)[symmetric].
    from this[unfolded conjug_prim_iff[OF conjugI'[of "r \<^sup>@ k" "u \<^sup>@ b \<cdot> r \<^sup>@ k'"]] rassoc]
    show "\<not> primitive (u \<^sup>@ b \<cdot> r \<^sup>@ (k' + k))"
      unfolding add_exps[symmetric] by force
  qed
qed (use assms in force)+

section \<open>Parametric solution of the equation @{term "x\<^sup>@j\<cdot>y\<^sup>@k = z\<^sup>@l"}\<close>

subsection \<open>Auxiliary lemmas\<close>

lemma xjy_imprim_len: assumes "x \<cdot> y \<noteq> y \<cdot> x" and eq: "x\<^sup>@j \<cdot> y = z\<^sup>@l" and "2 \<le> j" and "2 \<le> l"
  shows "\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|y\<^bold>| + 2*\<^bold>|x\<^bold>|" and "\<^bold>|z\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>|" and "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|" and "\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|"
proof-
  define j' where "j' \<equiv> j - 2"
  have "0 < j" "j = Suc(Suc j')"
    unfolding j'_def using \<open>2 \<le> j\<close> by force+
  from LS_per_lemma_case[of _ _ _ 1, unfolded pow_1, OF eq \<open>0 < j\<close>]
  show "\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|"
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by linarith
  from lenarg[OF eq, unfolded lenmorph, unfolded pow_len]
    add_less_mono1[OF this, of "\<^bold>|y\<^bold>|",  unfolded pow_len]
  show "\<^bold>|z\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>|"
    using mult_le_mono1[OF \<open>2 \<le> l\<close>, unfolded mult_2, of "\<^bold>|z\<^bold>|"] by linarith
  with \<open>\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|\<close>
  show "\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|y\<^bold>| + 2*\<^bold>|x\<^bold>|" and "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|"
    unfolding \<open>j = Suc (Suc j')\<close> pow_Suc lenmorph mult_2 by linarith+
qed

lemma case_j1k1: assumes
  eq: "x\<cdot>y = z\<^sup>@l" and
  non_comm: "x \<cdot> y \<noteq> y \<cdot> x" and
  l_min: "2 \<le> l"
  obtains r q m n where
    "x = (r\<cdot>q)\<^sup>@m\<cdot>r" and
    "y = q\<cdot> (r \<cdot> q)\<^sup>@n" and
    "z = r\<cdot>q" and
    "l = m + n + 1" and "r\<cdot>q \<noteq> q\<cdot>r" and "\<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| \<ge> 4"
proof-
  have "0 < l" "y \<noteq> \<epsilon>"
    using l_min non_comm by force+
  from split_pow[OF eq this]
  obtain r q m n where
   x: "x = (r \<cdot> q) \<^sup>@ m \<cdot> r" and
   y: "y = (q \<cdot> r)\<^sup>@ n \<cdot> q" and
   z: "z = r \<cdot> q" and
   l: "l = m + n + 1".
  from non_comm[unfolded x y]
  have "r \<cdot> q \<noteq> q \<cdot> r"
    unfolding shifts
    unfolding lassoc add_exps[symmetric] pow_Suc[symmetric] add.commute[of m]
    by force
  hence "r \<noteq> \<epsilon>" and "q \<noteq> \<epsilon>"
    by blast+
  have "2 \<le> \<^bold>|r \<cdot> q\<^bold>|"
    using nemp_pos_len[OF \<open>r \<noteq> \<epsilon>\<close>] nemp_pos_len[OF \<open>q \<noteq> \<epsilon>\<close>]
    unfolding lenmorph by linarith
  have "\<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| \<ge> 4"
    unfolding x y lenmorph[symmetric] shifts
    unfolding add_exps[symmetric] lassoc lenmorph[of "r \<cdot> q"]
    mult_Suc[symmetric] pow_len Suc_eq_plus1 l[symmetric]
    using mult_le_mono[OF \<open>2 \<le> l\<close> \<open>2 \<le> \<^bold>|r \<cdot> q\<^bold>|\<close>]
    by presburger
  from that[OF x y[unfolded shift_pow] z l \<open>r \<cdot> q \<noteq> q \<cdot> r\<close> this]
  show thesis.
qed




subsection \<open>@{term x} is longer\<close>

text\<open>We set up a locale representing the Lyndon-Schützenberger Equation
     with relaxed exponents and a length assumption breaking the symmetry.\<close>

locale LS_len_le = binary_code x y for x y +
  fixes j k l z
  assumes
    y_le_x: "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    and eq: "x\<^sup>@j \<cdot> y\<^sup>@k = z\<^sup>@l"
    and l_min: "2 \<le> l"
    and j_min: "1 \<le> j"
    and k_min: "1 \<le> k"
begin

lemma jk_small: obtains "j = 1" | "k = 1"
  using Lyndon_Schutzenberger(1)[OF eq _ _ l_min]
    le_neq_implies_less[OF j_min]
    le_neq_implies_less[OF k_min]
    non_comm
  unfolding One_less_Two_le_iff
  by blast

subsubsection \<open>case @{term "2 \<le> j"}\<close>

lemma case_j2k1: assumes "2 \<le> j" "k = 1"
  obtains r q t where
    "(r \<cdot> q) \<^sup>@ t \<cdot> r = x" and
    "q \<cdot> r \<cdot> r \<cdot> q  =  y" and
    "(r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q = z" and "2 \<le> t"
    "j = 2" and "l = 2" and "r\<cdot>q \<noteq> q\<cdot>r" and
    "primitive x" and "primitive y"
proof-
  note eq' = eq[unfolded \<open>k = 1\<close> pow_1]
  note xjy_imprim_len[OF non_comm eq[unfolded \<open>k = 1\<close> pow_1] \<open>2 \<le> j\<close> l_min]

  obtain j' where "j = Suc (Suc j')"
    using \<open>2 \<le> j\<close> using at_least2_Suc by metis
  hence "0 < j" by blast
  from lenarg[OF eq', unfolded lenmorph, unfolded pow_len]
    add_less_mono1[OF \<open>\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|\<close>, of "\<^bold>|y\<^bold>|", unfolded pow_len]
  have "l*\<^bold>|z\<^bold>| < 3*\<^bold>|z\<^bold>|"
    using \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close> y_le_x by linarith
  hence "l = 2"
    using l_min by simp
  from \<open>\<^bold>|x \<^sup>@ j\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|\<close> add_less_mono1[OF \<open>\<^bold>|z\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>|\<close>, of "\<^bold>|x\<^bold>|"] y_le_x
  have "j' * \<^bold>|x\<^bold>| < \<^bold>|x\<^bold>|"
    unfolding \<open>j = Suc (Suc j')\<close> pow_Suc lenmorph pow_len by linarith
  hence "j = 2"
    using  \<open>j = Suc (Suc j')\<close> by simp

  note eq[ unfolded \<open>k = 1\<close> pow_1 \<open>j = 2\<close> \<open>l = 2\<close> pow_two rassoc]
  from eqd[OF this less_imp_le[OF \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close>]]
  obtain p where "x \<cdot> p = z" and "p \<cdot> z = x \<cdot> y"
    by blast
  from eqd[OF \<open>p \<cdot> z = x \<cdot> y\<close>[folded \<open>x \<cdot> p = z\<close>, unfolded lassoc, symmetric]]
  obtain s where "x \<cdot> s = p \<cdot> x" and "s \<cdot> p = y"
    by auto
  have "p \<noteq> \<epsilon>"
    using \<open>x \<cdot> p = z\<close> \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close> by fastforce
  have "s \<noteq> \<epsilon>"
    using \<open>p \<noteq> \<epsilon>\<close> \<open>x \<cdot> s = p \<cdot> x\<close> by force
  from  conjug_eqE[OF \<open>x \<cdot> s = p \<cdot> x\<close>[symmetric] \<open>p \<noteq> \<epsilon>\<close>]
  obtain r q t where "r \<cdot> q = p" and "q \<cdot> r = s" and "(r \<cdot> q)\<^sup>@t\<cdot>r = x" and "q \<noteq> \<epsilon>".
  note \<open>s \<cdot> p = y\<close>[folded \<open>q \<cdot> r = s\<close> \<open>r \<cdot> q = p\<close>, unfolded rassoc]
  from y_le_x[folded this \<open>(r \<cdot> q)\<^sup>@t\<cdot>r = x\<close>, unfolded lenmorph pow_len] nemp_len[OF \<open>q \<noteq> \<epsilon>\<close>]
    add_le_mono1[OF mult_le_mono1[of t 1 "\<^bold>|r\<^bold>| + \<^bold>|q\<^bold>|", unfolded mult_1], of "\<^bold>|r\<^bold>|"]
  have "2 \<le> t"
    by linarith
        from \<open>p \<cdot> z = x \<cdot> y\<close>[folded \<open>q \<cdot> r \<cdot> r \<cdot> q = y\<close> \<open>(r \<cdot> q)\<^sup>@t\<cdot>r = x\<close>  \<open>r \<cdot> q = p\<close>, symmetric]
  have z: "(r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q = z"
    by comparison

\<comment> \<open>y is primitive due to the Lyndon-Schutzenberger\<close>

  from comm_drop_exp[OF \<open>0 < j\<close>, of y x j, unfolded eq']
  have "primitive y"
    using Lyndon_Schutzenberger_prim[OF pow_nemp_imprim[OF \<open>2 \<le>j\<close>], of y x, unfolded eq', OF _ pow_nemp_imprim[OF l_min]] non_comm by argo

  hence "q \<cdot> r \<noteq> r \<cdot> q"
    using \<open>p \<noteq> \<epsilon>\<close> \<open>q \<cdot> r = s\<close> \<open>r \<cdot> q = p\<close> \<open>s \<cdot> p = y\<close> comm_not_prim[OF \<open>s \<noteq> \<epsilon>\<close> \<open>p \<noteq> \<epsilon>\<close>] by argo

\<comment> \<open>primitivity of x using @{thm per_le_prim_iff}\<close>

  thm per_le_prim_iff[of x p]
  have "x \<le>p p \<cdot> x"
    unfolding \<open>(r \<cdot> q)\<^sup>@t\<cdot>r = x\<close>[symmetric] \<open>r \<cdot> q = p\<close>[symmetric]
    by comparison
  have "2*\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|"
    unfolding \<open>(r \<cdot> q)\<^sup>@t\<cdot>r = x\<close>[symmetric] \<open>r \<cdot> q = p\<close>[symmetric] lenmorph pow_len
    using mult_le_mono1[OF \<open>2 \<le> t\<close>, of "(\<^bold>|r\<^bold>| + \<^bold>|q\<^bold>|)"] by linarith
  have [symmetric]: "p \<cdot> x \<noteq> x \<cdot> p"
    unfolding \<open>(r \<cdot> q)\<^sup>@t\<cdot>r = x\<close>[symmetric] \<open>r \<cdot> q = p\<close>[symmetric] lassoc pow_comm[symmetric]
    unfolding rassoc cancel by fact
  with per_le_prim_iff[OF \<open>x \<le>p p \<cdot> x\<close> \<open>p \<noteq> \<epsilon>\<close> \<open> 2 * \<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>]
  have "primitive x"
    by blast

  from that[OF \<open>(r \<cdot> q)\<^sup>@t\<cdot>r = x\<close> \<open>q \<cdot> r \<cdot> r \<cdot> q = y\<close> z \<open>2 \<le> t\<close>
      \<open>j = 2\<close> \<open>l = 2\<close> \<open>q\<cdot>r \<noteq> r\<cdot>q\<close>[symmetric] \<open>primitive x\<close> \<open>primitive y\<close>]
  show thesis.
qed

subsubsection \<open>case @{term "j = 1"}\<close>

lemma case_j1k2_primitive: assumes "j = 1" "2 \<le> k"
  shows "primitive x"
  using Lyndon_Schutzenberger_prim[OF _ pow_nemp_imprim
      pow_nemp_imprim[OF l_min, of z, folded eq], OF _ \<open>2 \<le> k\<close>]
    comm_pow_roots[of j k x y] k_min non_comm
  unfolding \<open>j = 1\<close> pow_1
  by linarith

lemma case_j1k2_a: assumes "j = 1" "2 \<le> k" "z \<le>s y\<^sup>@k"
  obtains r q t where
    "x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
      (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q" and
    "y = r \<cdot> (q \<cdot> r) \<^sup>@ t" and
    "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)" and \<open>0 < t\<close> and "r\<cdot>q \<noteq> q\<cdot>r"
proof-
  have "z \<noteq> \<epsilon>"
    using assms(1) bin_fst_nemp eq by force
  have "0 < k" "0 < k -1"
    using \<open>2 \<le> k\<close> by linarith+
  have "0 < l" "0 < l - 1"
    using l_min by linarith+

  from LS_per_lemma_case[reversed, OF eq \<open>0 < k\<close>, unfolded \<open>j = 1\<close>]
  have perlem: "\<^bold>|y\<^sup>@k\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
    using non_comm
    by linarith

  obtain v where "y\<^sup>@k = v\<cdot>z"
    using \<open>z \<le>s y\<^sup>@k\<close> suffix_def by blast
  have "\<^bold>|v\<^bold>| < \<^bold>|y\<^bold>|"
    using perlem[unfolded lenarg[OF \<open>y\<^sup>@k = v\<cdot>z\<close>] lenmorph]
    by simp
  have "v <p y"
    using prefI[OF \<open>y\<^sup>@k = v\<cdot>z\<close>[symmetric]]
    unfolding pow_pos[OF \<open>0 < k\<close>]
    using pref_prod_less[OF _ \<open>\<^bold>|v\<^bold>| < \<^bold>|y\<^bold>|\<close>]
    by blast
  obtain u where "v\<cdot>u = y" "u \<noteq> \<epsilon>"
    using \<open>v <p y\<close> spref_exE by blast

  have "z = u\<cdot>y\<^sup>@(k-1)"
    using \<open>y\<^sup>@k = v\<cdot>z\<close>[unfolded pow_pos[OF \<open>0 < k\<close>],
        folded \<open>v \<cdot> u = y\<close>, unfolded rassoc cancel,
        unfolded \<open>v \<cdot> u = y\<close>, symmetric].

  note eq[unfolded pow_pos'[OF \<open>0 < l\<close>] \<open>y\<^sup>@k = v\<cdot>z\<close> lassoc cancel_right
      \<open>j = 1\<close> pow_1]

  obtain u' where "u'\<cdot>v = y"
  proof-
    have "v \<le>s z\<^sup>@(l-1)"
      using \<open>x \<cdot> v = z \<^sup>@ (l - 1)\<close> by blast
    moreover have "y \<le>s z\<^sup>@(l-1)"
      unfolding \<open>z = u\<cdot>y\<^sup>@(k-1)\<close> pow_pos'[OF \<open>0 < k - 1\<close>]
        pow_pos'[OF \<open>0 < l - 1\<close>] lassoc
      by blast
    ultimately have "v \<le>s y"
      using order_less_imp_le[OF \<open>\<^bold>|v\<^bold>| < \<^bold>|y\<^bold>|\<close>] suffix_length_suffix by blast
    thus thesis
      using sufD that by blast
  qed
  hence "u' \<noteq> \<epsilon>"
    using \<open>v <p y\<close> by force

  from conjugation[OF \<open>u'\<cdot>v = y\<close>[folded \<open>v\<cdot>u = y\<close>] \<open>u' \<noteq> \<epsilon>\<close>]
  obtain r q t where "r \<cdot> q = u'" "q \<cdot> r = u" "(r \<cdot> q) \<^sup>@ t \<cdot> r = v"
    by blast

  have y: "y = r \<cdot> (q \<cdot> r) \<^sup>@ Suc t"
    using \<open>u' \<cdot> v = y\<close>[symmetric, folded \<open>(r \<cdot> q) \<^sup>@ t \<cdot> r = v\<close> \<open>r \<cdot> q = u'\<close>]
    unfolding rassoc pow_slide[symmetric].
  have z: "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)"
    using \<open>q \<cdot> r = u\<close> \<open>z = u \<cdot> y \<^sup>@ (k - 1)\<close> y by blast

  let ?x = "((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
      (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q"
  have "?x \<cdot> v = z \<^sup>@ (l - 1)"
    unfolding z \<open>(r \<cdot> q) \<^sup>@ t \<cdot> r = v\<close>[symmetric] pow_pos'[OF \<open>0 < k - 1\<close>]
    pow_pos'[OF \<open>0 < l - 1\<close>] diff_diff_left nat_1_add_1
    by (simp only: shifts)
  from \<open>x \<cdot> v = z \<^sup>@ (l - 1)\<close>[folded this]
  have x: "x = ?x"
    by blast

  have "z\<cdot>y \<noteq> y\<cdot>z"
    using non_comm
    using comm_add_exp[of z y l, folded eq,
        unfolded rassoc pow_comm, unfolded lassoc cancel_right
        \<open>j = 1\<close> pow_1]
    by blast
  hence "r\<cdot>q \<noteq> q\<cdot>r"
    unfolding \<open>q \<cdot> r = u\<close> \<open>r \<cdot> q = u'\<close> \<open>u'\<cdot> v  = y\<close>[symmetric]
      \<open>z = u \<cdot> y \<^sup>@ (k - 1)\<close> pow_pos'[OF \<open>0 < k\<close>] rassoc
      \<open>y \<^sup>@ k = v \<cdot> z\<close>[unfolded \<open>u' \<cdot> v = y\<close>[symmetric]
        \<open>z = u \<cdot> y \<^sup>@ (k - 1)\<close>, symmetric] cancel_right..
  show thesis
    using that[OF x y z _ \<open>r\<cdot>q \<noteq> q\<cdot>r\<close>] by blast
qed

lemma case_j1k2_b: assumes "j = 1" "2 \<le> k" "y\<^sup>@k <s z"
  obtains q where
    "x = (q\<cdot>y\<^sup>@k)\<^sup>@(l-1)\<cdot>q" and
    "z = q\<cdot>y\<^sup>@k" and
    "q\<cdot>y \<noteq> y\<cdot>q"
proof-
  obtain q where "z = q\<cdot>y\<^sup>@k" "q \<noteq> \<epsilon>"
    using ssufD[OF \<open>y\<^sup>@k <s z\<close>]
    unfolding suffix_def
    by blast
  have "0 < l" using l_min by linarith
  have "x = (q\<cdot>y\<^sup>@k)\<^sup>@(l-1)\<cdot>q"
    using eq[unfolded pow_pos'[OF \<open>0 < l\<close>] \<open>j = 1\<close> pow_1,
        unfolded \<open>z = q\<cdot>y\<^sup>@k\<close> lassoc cancel_right].
  have "q\<cdot>y \<noteq> y\<cdot>q"
    using
      comm_trans[OF _ _ \<open>q \<noteq> \<epsilon>\<close>, of y x] conjug_pow[of y q y k, symmetric]
      conjug_pow[of "q \<cdot> y \<^sup>@ k" q  "q \<cdot> y \<^sup>@ k" "l-1"] non_comm
    unfolding append_same_eq[symmetric, of \<open>(q \<cdot> y \<^sup>@ k) \<^sup>@ (l - 1) \<cdot> q\<close> \<open>q \<cdot> (q \<cdot> y \<^sup>@ k) \<^sup>@ (l - 1)\<close> q]
    unfolding \<open>x = (q \<cdot> y \<^sup>@ k) \<^sup>@ (l - 1) \<cdot> q\<close> rassoc
    by argo
  show ?thesis
    using \<open>x = (q \<cdot> y \<^sup>@ k) \<^sup>@ (l - 1) \<cdot> q\<close> \<open>z = q \<cdot> y \<^sup>@ k\<close> \<open>q\<cdot>y \<noteq> y\<cdot>q\<close> that by blast
qed

subsection \<open>Putting things together\<close>

lemma solution_cases: obtains
  "j = 2" "k = 1" |
  "j = 1" "2 \<le> k" "z <s y\<^sup>@k" |
  "j = 1" "2 \<le> k" "y\<^sup>@k <s z" |
  "j = 1" "k = 1"
proof-
  have "0 < l" "0 < l-1"
    using l_min by linarith+
  have "0 < k"
    using k_min by linarith
  have "0 < j"
    using j_min by linarith
  have "z \<noteq> \<epsilon>"
    using eq nemp_pow_nemp[of z l] bin_fst_nemp[folded nonzero_pow_emp[OF \<open>0 < j\<close>, of x], THEN pref_nemp]
    by force
  have "z \<noteq> y\<^sup>@k"
  proof
    assume "z = y\<^sup>@k"
    with eq[unfolded pow_pos'[OF \<open>0 < l\<close>], folded this, unfolded cancel_right]
    have "x\<^sup>@j \<cdot> y\<^sup>@k = y\<^sup>@k \<cdot> x\<^sup>@j"
      using pow_comm by auto
    from comm_drop_exps[OF this \<open>0 < j\<close> \<open>0 < k\<close>]
    show False
      using non_comm by blast
  qed
  consider
    "2 \<le> j" "k = 1" |
    "j = 1" "2 \<le> k" |
    "j = 1" "k = 1"
    using jk_small j_min k_min le_neq_implies_less
    unfolding One_less_Two_le_iff[symmetric]
    by metis
  moreover consider "z <s y\<^sup>@k" | "y\<^sup>@k <s z"
    using suffix_order.less_le
      triv_suf[of "y\<^sup>@k" "x\<^sup>@j", unfolded eq, THEN suf_prod_root,
        THEN ruler_suf'] \<open>z \<noteq> y\<^sup>@k\<close>
    by blast
  moreover consider "j = 1" | "j = 2"
    using case_j2k1[of thesis] calculation(1) by blast
  ultimately show ?thesis
    using that
    by metis
qed

theorem parametric_solutionE: obtains
  \<comment>\<open>case @{term "x\<cdot>y"}\<close>
  r q m n where
  "x = (r\<cdot>q)\<^sup>@m\<cdot>r" and
  "y = q\<cdot>(r\<cdot>q)\<^sup>@n" and
  "z = r\<cdot>q" and
  "l = m + n + 1" and "r\<cdot>q \<noteq> q\<cdot>r"
|
  \<comment>\<open>case @{term "x\<cdot>y\<^sup>@k"} with @{term "2 \<le> k"} and @{term "z <s y\<^sup>@k"}\<close>
  r q t where
  "x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
      (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q" and
  "y = r \<cdot> (q \<cdot> r) \<^sup>@ t" and
  "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)" and
  "0 < t" and "r\<cdot>q \<noteq> q\<cdot>r"
|
  \<comment>\<open>case @{term "x\<cdot>y\<^sup>@k"} with @{term "2 \<le> k"} and @{term "y\<^sup>@k <s z"}\<close>
  q where
  "x = (q\<cdot>y\<^sup>@k)\<^sup>@(l-1)\<cdot>q" and
  "z = q\<cdot>y\<^sup>@k" and
  "q\<cdot>y \<noteq> y\<cdot>q"
|
  \<comment>\<open>case @{term "x\<^sup>@j\<cdot>y"} with @{term "2 \<le> j"}\<close>
  r q t where
  "x = (r \<cdot> q) \<^sup>@ t \<cdot> r" and
  "y  =  q \<cdot> r \<cdot> r \<cdot> q" and
  "z = (r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q" and
  "j = 2" and "l = 2" and "2 \<le> t" and "r\<cdot>q \<noteq> q\<cdot>r" and
  "primitive x" and "primitive y"
proof-
  show ?thesis
    using solution_cases
  proof(cases)
    case 1
    from case_j2k1[OF _ \<open>k = 1\<close>, of thesis] \<open>j = 2\<close>
    show ?thesis
      using that(4) by blast
  next
    case 2
    from case_j1k2_a[OF this(1-2) ssufD1[OF this(3)], of thesis]
    show thesis
      using that(2)
      by blast
  next
    case 3
    from case_j1k2_b[OF this, of thesis]
    show ?thesis
      using that(3) by blast
  next
    case 4
    from case_j1k1[OF eq[unfolded \<open>k = 1\<close> \<open>j = 1\<close> pow_1] non_comm l_min, of thesis]
    show thesis
      using that(1).
  qed
qed

end
text \<open>Using the solution from locale @{term LS_len_le},
the following theorem gives the full characterization of the equation in question:
$$ x^iy^j = z^\ell $$
\<close>

theorem LS_parametric_solution:
  assumes y_le_x: "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    and j_min: "1 \<le> j"  and k_min: "1 \<le> k" and l_min: "2 \<le> l"
  shows
    "x\<^sup>@j \<cdot> y\<^sup>@k = z\<^sup>@l
  \<longleftrightarrow>
    (\<exists>r m n t.
        x = r\<^sup>@m \<and> y = r\<^sup>@n \<and> z = r\<^sup>@t \<and> m*j+n*k=t*l) \<comment>\<open>Case A: {x,y} is not a code\<close>
  \<or> (j = 1 \<and> k = 1) \<and>
    (\<exists>r q m n.
        x = (r\<cdot>q)\<^sup>@m\<cdot>r \<and> y = q\<cdot>(r\<cdot>q)\<^sup>@n \<and> z = r\<cdot>q \<and> m + n + 1 = l \<and> r\<cdot>q \<noteq> q\<cdot>r) \<comment> \<open>Case B\<close>
  \<or> (j = 1 \<and> 2 \<le> k) \<and>
    (\<exists>r q.
        x = (q\<cdot>r\<^sup>@k)\<^sup>@(l-1)\<cdot>q \<and> y = r \<and> z = q\<cdot>r\<^sup>@k \<and> r\<cdot>q \<noteq> q\<cdot>r) \<comment> \<open>Case C\<close>
  \<or> (j = 1 \<and> 2 \<le> k) \<and>
    (\<exists>r q t. 0 < t \<and>
        x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2)\<cdot>(((q \<cdot> r) \<cdot>
               (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q
        \<and> y = r \<cdot> (q \<cdot> r) \<^sup>@ t
        \<and> z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)
        \<and> r\<cdot>q \<noteq> q\<cdot>r) \<comment> \<open>Case D\<close>
  \<or> (j = 2 \<and> k = 1 \<and> l = 2) \<and>
    (\<exists>r q t. 2 \<le> t \<and>
        x = (r \<cdot> q) \<^sup>@ t \<cdot> r \<and> y = q \<cdot> r \<cdot> r \<cdot> q
        \<and> z = (r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q  \<and> r\<cdot>q \<noteq> q\<cdot>r ) \<comment> \<open>Case E\<close>
  "
    (is "?eq =
   (?sol_per \<or> (?cond_j1k1 \<and> ?sol_j1k1) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_b) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_a) \<or>
   (?cond_j2k1l2 \<and> ?sol_j2k1l2))")
proof(rule iffI)
  assume eq: "x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l"
  show
    "(?sol_per \<or> (?cond_j1k1 \<and> ?sol_j1k1) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_b) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_a) \<or>
   (?cond_j2k1l2 \<and> ?sol_j2k1l2))"
  proof(cases)
    assume "x\<cdot>y = y\<cdot>x"
    from comm_primrootE[OF this]
    obtain r m n where "x = r \<^sup>@ m" "y = r \<^sup>@ n" "primitive r"
      using rootE by metis

    note eqs = eq[unfolded this, folded pow_mult add_exps, symmetric]
    obtain t where "z = r \<^sup>@ t"
      using l_min pow_comm_comm[OF eqs,
          THEN prim_comm_exp[OF \<open>primitive r\<close>]]
      by auto
    from eqs[unfolded this, folded pow_mult, symmetric]
    have "m * j + n * k = t * l"
      unfolding prim_nemp[OF \<open>primitive r\<close>, THEN eq_pow_exp].
    hence ?sol_per
      using \<open>x = r \<^sup>@ m\<close> \<open>y = r \<^sup>@ n\<close> \<open>z = r \<^sup>@ t\<close> by blast
    thus ?thesis
      by blast
  next
    assume "x\<cdot>y \<noteq> y\<cdot>x"
    interpret LS_len_le x y j k l z
      using \<open>x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l\<close> \<open>x\<cdot>y \<noteq> y\<cdot>x\<close> j_min k_min l_min y_le_x
      by(unfold_locales)

    show ?thesis
      using solution_cases
    proof(cases)
      case 1
      from case_j2k1[OF less_or_eq_imp_le[of 2 j] \<open>k = 1\<close>, OF disjI2, OF \<open>j = 2\<close>[symmetric], of "?sol_j2k1l2 \<and> l = 2"]
      have "?sol_j2k1l2" and "l = 2"
        by auto
      thus ?thesis
        using \<open>k = 1\<close> \<open>j = 2\<close> by blast
    next
      case 2
      have "?sol_j1k2_a"
        using case_j1k2_a[OF \<open>j = 1\<close> \<open>2 \<le> k\<close> ssufD1[OF \<open>z <s y \<^sup>@ k\<close>], of ?sol_j1k2_a]
        unfolding Suc_eq_plus1
        by blast
      thus ?thesis
        using \<open>j = 1\<close> \<open>2 \<le> k\<close> by blast
    next
      case 3
      with case_j1k2_b[OF this, of "?sol_j1k2_b"]
      have "?sol_j1k2_b" by auto
      thus ?thesis
        using \<open>j = 1\<close> \<open>2 \<le> k\<close> by blast
    next
      case 4
      with case_j1k1[OF eq[unfolded \<open>k = 1\<close> \<open>j = 1\<close> pow_1] non_comm l_min, of ?sol_j1k1]
      have"?sol_j1k1"
        unfolding Suc_eq_plus1 shift_pow
        by blast
      thus ?thesis
        using \<open>j = 1\<close> \<open>k = 1\<close> by blast
    qed
  qed
next
  have "l \<noteq> 0" "l - 1 \<noteq> 0"
    using l_min by auto
  have "k \<noteq> 0" using k_min by auto
  have "j \<noteq> 0" using j_min by auto
  assume   "(?sol_per \<or> (?cond_j1k1 \<and> ?sol_j1k1) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_b) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_a) \<or>
   (?cond_j2k1l2 \<and> ?sol_j2k1l2))"
  then show ?eq
  proof(elim disjE conjE exE)
    fix r m n t
    assume sol: "x = r \<^sup>@ m" "y = r \<^sup>@ n" "z = r \<^sup>@ t"
      and "m * j + n * k = t * l"
    show ?thesis
      unfolding sol
      unfolding pow_mult[symmetric] add_exps[symmetric]
      unfolding \<open>m * j + n * k = t * l\<close>..
  next
    fix r q m n
    assume "j = 1" "k = 1" and sol: "x = (r\<cdot>q)\<^sup>@m\<cdot>r"
      "y = q\<cdot>(r\<cdot>q)\<^sup>@n" "z = r\<cdot>q"
      and "m + n + 1 = l"
    hence "Suc (m+n) = l"
      by simp
    show ?thesis
      unfolding sol
      unfolding \<open>j = 1\<close> \<open>k = 1\<close> \<open>Suc (m + n) = l\<close>[symmetric] pow_1
      unfolding lassoc pow_Suc add_exps
      unfolding pow_comm[of _ m, symmetric] lassoc..
  next
    fix r q
    assume "j = 1" "2 \<le> k" and sol: "x = (q \<cdot> r \<^sup>@ k) \<^sup>@ (l - 1) \<cdot> q" "y = r" "z = q \<cdot> r \<^sup>@ k"
    have "0 < l"
      using \<open>2 \<le> l\<close> by force
    show ?thesis
      unfolding sol \<open>j = 1\<close> pow_1
      unfolding pow_pos'[OF \<open>0 < l\<close>] rassoc..
  next
    fix r q t
    assume "j = 1" "2 \<le> k" and sol:
      "x =
        ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
        (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q"
      "y = r \<cdot> (q \<cdot> r) \<^sup>@ t"
      "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)"
      "0 < t"
    obtain k' where  "Suc (Suc k') = k" using  Suc_minus2[OF \<open>2 \<le> k\<close>] by blast
    hence k1: "k - 1 = Suc k'" and k2: "k - 2 = k'" and k: "k = k'+ 2" by fastforce+
    obtain l' where "Suc (Suc l') = l" using  Suc_minus2[OF \<open>2 \<le> l\<close>] by blast
    hence l2: "l - 2 = l'" and l: "l  = l' + 2"  by fastforce+
    show "x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l"
      unfolding sol \<open>j = 1\<close> k1 k2 l2 unfolding k l by comparison
  next
    fix r q t
    assume "j = 2" "k = 1" "l = 2" and  sol:
      "x = (r \<cdot> q) \<^sup>@ t \<cdot> r"
      "y = q \<cdot> r \<cdot> r \<cdot> q" "z = (r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q"
      "2 \<le> t"
    show "x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l"
      unfolding \<open>j = 2\<close> \<open>k = 1\<close> \<open>l = 2\<close> sol pow_1 pow_two
      by comparison
  qed
qed

subsection \<open>Uniqueness of the imprimitivity witness\<close>

text\<open>In this section, we show that given a binary code @{term "{x,y}"} and
two imprimitive words @{term "x\<^sup>@j\<cdot>y\<^sup>@k"} and @{term "x\<^sup>@j'\<cdot>y\<^sup>@k'"} is possible
only if the two words are equals, that is, if @{term "j=j'"} and @{term "k=k'"}.\<close>

lemma LS_unique_same: assumes "x \<cdot> y \<noteq> y \<cdot> x"
  and "1 \<le> j" and "1 \<le> k" and "\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)"
  and "1 \<le> k'" and "\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k')"
shows "k = k'"
proof(rule ccontr)
  assume "k \<noteq> k'"

  define ka where "ka = (if k < k' then k else k')"
  define ka' where "ka' = (if k < k' then k' else k)"

  have "ka < ka'" and "ka \<noteq> ka'"
    unfolding ka_def ka'_def using \<open>k \<noteq> k'\<close> by auto
  then obtain dif where [symmetric]: "ka + dif = ka'" and "dif \<noteq> 0"
    using less_imp_add_positive by blast
  have "ka \<noteq> 0" and "ka' \<noteq> 0" and \<open>j \<noteq> 0\<close>
    unfolding ka_def ka'_def using \<open>1 \<le> k\<close> \<open>1 \<le> k'\<close> \<open>1 \<le> j\<close> by force+

  have "\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@ka)" "\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@ka')"
    unfolding ka_def ka'_def using assms(4) assms(6) by presburger+

  have "x\<^sup>@j\<cdot>y\<^sup>@ka' = x\<^sup>@j\<cdot>y\<^sup>@ka\<cdot>y\<^sup>@dif"
    unfolding add_exps[symmetric] \<open>ka' = ka + dif\<close>..

  consider "dif = 1" | "2 \<le> dif"
    using \<open>ka < ka'\<close> \<open>ka' = ka + dif\<close> by fastforce
  hence "x \<cdot> y = y \<cdot> x"
  proof(cases)
    assume "dif = 1"
    define u where "u = x\<^sup>@j\<cdot>y\<^sup>@(ka - 1)"
    have "\<not> primitive (u \<cdot> y)"
      unfolding u_def rassoc pow_Suc'[symmetric]  Suc_minus[OF \<open>ka \<noteq> 0\<close>] by fact
    have "\<not> primitive (u \<cdot> y \<cdot> y)"
      unfolding u_def rassoc using \<open>\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@ka')\<close>[unfolded \<open>x\<^sup>@j\<cdot>y\<^sup>@ka' = x\<^sup>@j\<cdot>y\<^sup>@ka\<cdot>y\<^sup>@dif\<close> \<open>dif = 1\<close> pow_1]
      unfolding pow_Suc'[of y "ka - 1", unfolded Suc_minus[OF \<open>ka \<noteq> 0\<close>]] rassoc.
    from imprim_ext_suf_comm[OF \<open>\<not> primitive (u \<cdot> y)\<close> \<open>\<not> primitive (u \<cdot> y \<cdot> y)\<close>]
    have "(x \<^sup>@ j \<cdot> y \<^sup>@ (ka - 1)) \<cdot> y = y \<cdot> x \<^sup>@ j \<cdot> y \<^sup>@ (ka - 1)"
      unfolding u_def.
    thus "x \<cdot> y = y \<cdot> x"
      using \<open>j \<noteq> 0\<close> by mismatch
  next
    assume "2 \<le> dif"
    hence "\<not> primitive (y\<^sup>@dif)"..
    from Lyndon_Schutzenberger_prim[OF \<open>\<not> primitive (x \<^sup>@ j \<cdot> y \<^sup>@ ka)\<close> this  \<open>\<not> primitive (x \<^sup>@ j \<cdot> y \<^sup>@ ka')\<close>[unfolded \<open>x \<^sup>@ j \<cdot> y \<^sup>@ ka' = x \<^sup>@ j \<cdot> y \<^sup>@ ka\<cdot> y\<^sup>@dif\<close> lassoc]]
    show "x \<cdot> y = y \<cdot> x"
      using \<open>dif \<noteq> 0\<close> \<open>j \<noteq> 0\<close> by mismatch
  qed
  thus False
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by blast
qed

lemma LS_unique_distinct_le: assumes "x \<cdot> y \<noteq> y \<cdot> x"
  and "2 \<le> j" and "\<not> primitive(x\<^sup>@j\<cdot>y)"
  and "2 \<le> k" and "\<not> primitive(x\<cdot>y\<^sup>@k)"
  and "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
shows False
proof-
  have "0 < k"
    using \<open>2 \<le> k\<close> by linarith
  obtain l z where [symmetric]:"z\<^sup>@l = x\<^sup>@j\<cdot>y" and "2 \<le> l"
    using  not_prim_primroot_expE[OF \<open>\<not> primitive(x\<^sup>@j\<cdot>y)\<close>].
  have "x\<^sup>@j\<cdot>y\<^sup>@1 = z\<^sup>@l"
    by (simp add: \<open>x \<^sup>@ j \<cdot> y = z \<^sup>@ l\<close>)
  interpret eq1: LS_len_le x y j 1 l z
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> \<open>x\<^sup>@j\<cdot>y\<^sup>@1 = z\<^sup>@l\<close> \<open>2 \<le> l\<close> \<open>2 \<le> j\<close>
    by(unfold_locales) linarith+

  from eq1.case_j2k1[OF \<open>2 \<le> j\<close> refl]
  obtain r q t where
    x[symmetric]: "(r \<cdot> q) \<^sup>@ t \<cdot> r = x" and
    y[symmetric]: "q \<cdot> r \<cdot> r \<cdot> q  =  y" and
    z[symmetric]: "(r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q = z" and
    "2 \<le> t" and "j = 2" and "l = 2" and "r\<cdot>q \<noteq> q\<cdot>r" and
    "primitive x" and "primitive y".

  have "q\<cdot>r \<noteq> \<epsilon>" "r\<cdot>q \<noteq> \<epsilon>"
    using eq1.bin_snd_nemp y by fastforce+

  obtain z' l' where "x\<cdot>y\<^sup>@k = z'\<^sup>@l'" "2 \<le> l'"
    using not_prim_primroot_expE[OF \<open>\<not> primitive (x \<cdot> y \<^sup>@ k)\<close>] by metis
  from \<open>x\<cdot>y\<^sup>@k = z'\<^sup>@l'\<close>[unfolded x y, unfolded rassoc, symmetric]
  have z': "z' \<^sup>@ l' = (r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> (q \<cdot> r \<cdot> r \<cdot> q) \<^sup>@ k".
  have "0 < l'" and "0 < l' - 1"
    using \<open>2 \<le> l'\<close> by auto
  have "r \<cdot> q \<cdot> r \<cdot> q \<le>p x"
   using pref_extD[of "r\<cdot>q\<cdot>r\<cdot>q" "(r \<cdot> q) \<^sup>@ (t - 2) \<cdot> r"]
    unfolding  x[folded pop_pow[OF \<open>2 \<le> t\<close>], unfolded pow_two] rassoc by blast

  have per1: "x \<cdot> q \<cdot> r \<le>p (r \<cdot> q) \<cdot> x \<cdot> q \<cdot> r"
    unfolding x by comparison
  have per2: "x \<cdot> q \<cdot> r \<le>p z' \<cdot> x \<cdot> q \<cdot> r"
    by (rule pref_prod_root[of _ _ l'],
    unfold \<open>x\<cdot>y\<^sup>@k = z'\<^sup>@l'\<close>[unfolded  y  pow_pos[OF \<open>0 < k\<close>], symmetric])
    comparison
  have "(r \<cdot> q) \<cdot> z' \<noteq> z' \<cdot> (r \<cdot> q)"
  proof
    assume "(r \<cdot> q) \<cdot> z' = z' \<cdot> (r \<cdot> q)"
    hence "(r \<cdot> q) \<cdot> z'\<^sup>@l' = z'\<^sup>@l' \<cdot> r \<cdot> q"
      by (simp add: comm_add_exp)
    from this[unfolded z']
    have "r \<cdot> q = q \<cdot> r"
      using \<open>0 < k\<close> by mismatch
    thus False
      using \<open>r \<cdot> q \<noteq> q \<cdot> r\<close> by presburger
  qed
  with two_pers[OF per1 per2]
  have "\<^bold>|x\<^bold>| \<le> \<^bold>|z'\<^bold>|"
    unfolding lenmorph by linarith

  from eqdE[OF \<open>x\<cdot>y\<^sup>@k = z'\<^sup>@l'\<close>[unfolded pow_pos[OF \<open>0 < l'\<close>]
       pow_pos'[OF \<open>0 < l'-1\<close>]] \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|z'\<^bold>|\<close> ]
  obtain w where "x \<cdot> w = z'" "w \<cdot> z' \<^sup>@ (l' - 1 - 1) \<cdot> z' = y \<^sup>@ k".
  from this(1) this(2)[unfolded lassoc]
  have  "x \<le>f y\<^sup>@k"
    by blast
  hence "r\<cdot>q\<cdot>r\<cdot>q \<le>f (q\<cdot>r\<cdot>r\<cdot>q)\<^sup>@k"
    unfolding y
    using pref_fac[OF \<open>r \<cdot> q \<cdot> r \<cdot> q \<le>p x\<close>] by blast

  have "\<^bold>|r \<cdot> q \<cdot> r \<cdot> q\<^bold>| = \<^bold>|q \<cdot> r \<cdot> r \<cdot> q\<^bold>|"
    by simp
  from xyxy_conj_yxxy[OF fac_pow_len_conjug[OF this \<open>r\<cdot>q\<cdot>r\<cdot>q \<le>f (q\<cdot>r\<cdot>r\<cdot>q)\<^sup>@k\<close>, symmetric]]
  have "r \<cdot> q = q \<cdot> r".
  thus False
    using \<open>r \<cdot> q \<noteq> q \<cdot> r\<close> by blast
qed

lemma LS_unique_distinct: assumes "x \<cdot> y \<noteq> y \<cdot> x"
  and "2 \<le> j" and "\<not> primitive(x\<^sup>@j\<cdot>y)"
  and "2 \<le> k" and "\<not> primitive(x\<cdot>y\<^sup>@k)"
shows False
  using LS_unique_distinct_le[OF assms] LS_unique_distinct_le[reversed, OF assms(1,4-5,2-3)] by fastforce

lemma LS_unique': assumes "x \<cdot> y \<noteq> y \<cdot> x"
  and "1 \<le> j" and "1 \<le> k"  and "\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)"
  and "1 \<le> j'" and "1 \<le> k'"  and "\<not> primitive(x\<^sup>@j'\<cdot>y\<^sup>@k')"
shows "k = k'"
proof-
  have "j = 1 \<or> k = 1"
    using Lyndon_Schutzenberger_prim[OF pow_non_prim pow_non_prim,
        OF _ _  \<open>\<not> primitive (x \<^sup>@ j \<cdot> y \<^sup>@ k)\<close>, THEN comm_drop_exps]
       \<open>1 \<le> j\<close> \<open>1 \<le> k\<close> \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by linarith
  have "j' = 1 \<or> k' = 1"
    using Lyndon_Schutzenberger_prim[OF pow_non_prim pow_non_prim,
        OF _ _  \<open>\<not> primitive (x \<^sup>@ j' \<cdot> y \<^sup>@ k')\<close>, THEN comm_drop_exps]
       \<open>1 \<le> j'\<close> \<open>1 \<le> k'\<close> \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by linarith
  show "k = k'"
  proof (cases "j = j'")
    assume "j = j'"
    from LS_unique_same[OF assms(1-4,6,7)[folded this]]
    show "k = k'".
  next
    assume "j \<noteq> j'"
    show "k = k'"
    proof(rule ccontr, cases "j = 1")
      assume "k \<noteq> k'" and  "j = 1"
      hence "2 \<le> j'" and "k' = 1" and "2 \<le> k"
        using \<open>j \<noteq> j'\<close> \<open>1 \<le> j'\<close> \<open>k \<noteq> k'\<close> \<open>1 \<le> k\<close>  \<open>j' = 1 \<or> k' = 1\<close> by auto
      from LS_unique_distinct[OF \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>  \<open>2 \<le> j'\<close> _ \<open>2 \<le> k\<close>]
      show False
        using \<open>\<not> primitive(x\<^sup>@j'\<cdot>y\<^sup>@k')\<close>[unfolded \<open>k'=1\<close> pow_1] \<open>\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)\<close>[unfolded \<open>j=1\<close> pow_1]
        by blast
    next
      assume "k \<noteq> k'" and  "j \<noteq> 1"
      hence "2 \<le> j" and "k = 1" and "2 \<le> k'" and "j' = 1"
        using \<open>1 \<le> j\<close> \<open>j = 1 \<or> k = 1\<close> \<open>1 \<le> k'\<close> \<open>j' = 1 \<or> k' = 1\<close> by auto
      from LS_unique_distinct[OF \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>2 \<le> j\<close> _ \<open>2 \<le> k'\<close>]
      show False
        using \<open>\<not> primitive(x\<^sup>@j'\<cdot>y\<^sup>@k')\<close>[unfolded \<open>j'=1\<close> pow_1] \<open>\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)\<close>[unfolded \<open>k=1\<close> pow_1]
        by blast
    qed
  qed
qed

lemma LS_unique: assumes "x \<cdot> y \<noteq> y \<cdot> x"
  and "1 \<le> j" and "1 \<le> k"  and "\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)"
  and "1 \<le> j'" and "1 \<le> k'"  and "\<not> primitive(x\<^sup>@j'\<cdot>y\<^sup>@k')"
shows "j = j'" and "k = k'"
  using  LS_unique'[OF \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>
      \<open>1 \<le> j\<close> \<open>1 \<le> k\<close>  \<open>\<not> primitive (x \<^sup>@ j \<cdot> y \<^sup>@ k)\<close>
      \<open>1 \<le> j'\<close> \<open>1 \<le> k'\<close> \<open>\<not> primitive (x \<^sup>@ j'\<cdot> y \<^sup>@ k')\<close>]
    LS_unique'[reversed, OF \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>
      \<open>1 \<le> k\<close> \<open>1 \<le> j\<close>   \<open>\<not> primitive (x \<^sup>@ j \<cdot> y \<^sup>@ k)\<close>
      \<open>1 \<le> k'\<close> \<open>1 \<le> j'\<close> \<open>\<not> primitive (x \<^sup>@ j'\<cdot> y \<^sup>@ k')\<close>]
  by blast+

section "The bound on the exponent in Lyndon-Schützenberger equation"

lemma (in LS_len_le) case_j1k2_exp_le:
  assumes "j = 1" "2 \<le> k"
  shows "k*\<^bold>|y\<^bold>|+ 4 \<le> \<^bold>|x\<^bold>|+2*\<^bold>|y\<^bold>|"
proof-
  have "x \<cdot> y \<^sup>@ k = z \<^sup>@ l" and "\<^bold>|y\<^bold>| \<noteq> 0" and "0 < l"
    using eq[unfolded \<open>j = 1\<close> cow_simps] nemp_len[OF bin_snd_nemp] l_min
    by linarith+

  consider "y \<^sup>@ k <s z" | "z \<le>s y\<^sup>@k"
    using ruler_eq'[reversed,
    OF \<open>x \<cdot> y\<^sup>@k = z\<^sup>@l\<close>[symmetric, unfolded pow_pos'[OF \<open>0 < l\<close>]]] by blast
  thus ?thesis
  proof(cases)
    assume "y\<^sup>@k <s z"
    from case_j1k2_b[OF assms this]
    obtain q where
      x: "x = (q \<cdot> y \<^sup>@ k) \<^sup>@ (l - 1) \<cdot> q" and
      "z = q \<cdot> y \<^sup>@ k" and
      "q \<cdot> y \<noteq> y \<cdot> q".
    have "1 \<le> \<^bold>|q\<^bold>|"
      using nemp_le_len[of q] \<open>q \<cdot> y \<noteq> y \<cdot> q\<close> by blast

    have "\<^bold>|y\<^bold>| \<ge> 1"
      using bin_snd_nemp nemp_le_len by blast

    have lle: "x \<le> (l-1)*x" for x
      using l_min
      by (simp add: quotient_smaller)

    have "\<^bold>|x\<^bold>| \<ge> k*\<^bold>|y\<^bold>| + 2"
      unfolding x lenmorph pow_len
      using le_trans[OF _ lle, of "k * \<^bold>|y\<^bold>| + 1" "\<^bold>|q\<^bold>| + k * \<^bold>|y\<^bold>|", THEN add_le_mono[OF \<open>1 \<le> \<^bold>|q\<^bold>|\<close>]]
      unfolding add.commute[of "\<^bold>|q\<^bold>|"]
      using \<open>1 \<le> \<^bold>|q\<^bold>|\<close> by auto
    thus ?thesis
      using \<open>\<^bold>|y\<^bold>| \<ge> 1\<close> by linarith
  next
    assume "z \<le>s y \<^sup>@ k "
    from  case_j1k2_a[OF assms this]
    obtain q r t where
      x: "x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot> (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q" and
      "y = r \<cdot> (q \<cdot> r) \<^sup>@ t" and
      "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 1)" and
      "0 < t" and "r \<cdot> q \<noteq> q \<cdot> r".

    have "q \<noteq> \<epsilon>" "r \<noteq> \<epsilon>"
      using \<open>r \<cdot> q \<noteq> q \<cdot> r\<close> by blast+
    hence "\<^bold>|q\<^bold>| \<ge> 1" "\<^bold>|r\<^bold>| \<ge> 1"
      using nemp_le_len by blast+
    hence "\<^bold>|q\<cdot>r\<^bold>| + \<^bold>|r\<^bold>| + \<^bold>|q\<^bold>| \<ge> 4"
      by simp

    have "\<^bold>|x\<^bold>| \<ge> \<^bold>|(((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q\<^bold>|"
      using x suf_len' by blast
    hence "\<^bold>|x\<^bold>| \<ge> \<^bold>|q\<cdot>r\<^bold>| + (k-2)*\<^bold>|y\<^bold>| + \<^bold>|r\<^bold>| + \<^bold>|q\<^bold>|"
      unfolding \<open>y = r \<cdot> (q \<cdot> r) \<^sup>@ t\<close>[symmetric]
      by (simp add: pow_len)
    hence "\<^bold>|x\<^bold>| \<ge> (k-2)*\<^bold>|y\<^bold>| + 4"
      using \<open>4 \<le> \<^bold>|q \<cdot> r\<^bold>| + \<^bold>|r\<^bold>| + \<^bold>|q\<^bold>|\<close> by linarith
    thus ?thesis
      unfolding add.commute[of "\<^bold>|x\<^bold>|"]
      unfolding nat_le_add_iff1[OF \<open>2 \<le> k\<close>].
  qed
qed

lemma (in LS_len_le) case_j2k1_exp_le:
  assumes "2 \<le> j" "k = 1"
  shows "j*\<^bold>|x\<^bold>| + 4 \<le> \<^bold>|y\<^bold>| + 2*\<^bold>|x\<^bold>|"
proof-
  from case_j2k1[OF assms]
  obtain r q t where
    "(r \<cdot> q) \<^sup>@ t \<cdot> r = x" and
    "q \<cdot> r \<cdot> r \<cdot> q = y" and
    "(r \<cdot> q) \<^sup>@ t \<cdot> r \<cdot> r \<cdot> q = z" and
    \<open>2 \<le> t\<close> and "j = 2" and "l = 2" and
    "r \<cdot> q \<noteq> q \<cdot> r" and
    "primitive x" and
    "primitive y".

  have "\<^bold>|r\<^bold>| \<ge> 1" "\<^bold>|q\<^bold>| \<ge> 1"
    using \<open>r \<cdot> q \<noteq> q \<cdot> r\<close> nemp_le_len by blast+
  hence "\<^bold>|y\<^bold>| \<ge> 4"
    unfolding \<open>q \<cdot> r \<cdot> r \<cdot> q = y\<close>[symmetric] lenmorph
    by linarith
  thus ?thesis
    by (simp add: \<open>j = 2\<close>)
qed

theorem LS_exp_le_one:
  assumes eq: "x \<cdot> y \<^sup>@ k = z \<^sup>@ l"
      and "2 \<le> l"
      and "x \<cdot> y \<noteq> y \<cdot> x"
      and "1 \<le> k"
      shows "k*\<^bold>|y\<^bold>| + 4 \<le> \<^bold>|x\<^bold>|+2*\<^bold>|y\<^bold>|"
proof-
  have "x \<noteq> \<epsilon>" "y \<noteq> \<epsilon>" "x \<noteq> y" "\<^bold>|y\<^bold>| \<noteq> 0" "z \<noteq> \<epsilon>"
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>x \<cdot> y \<^sup>@ k = z \<^sup>@ l\<close> by fastforce+
  have "l \<noteq> 0"  \<open>1 \<le> l-1\<close>
    using \<open>2 \<le> l\<close> by force+

  consider "k = 1" | "k \<ge> 2"
    using \<open>1 \<le> k\<close> by linarith
  then show ?thesis
  proof(cases)
    assume "k=1"
    have "4 \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>|"
      using case_j1k1[OF eq[unfolded \<open>k = 1\<close> pow_1] \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>2 \<le> l\<close>]
      by blast
    thus ?thesis
      unfolding \<open>k = 1\<close> by force
  next
    assume "k \<ge> 2"
  show ?thesis
  proof(rule le_cases)
    assume "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    then interpret LS_len_le x y 1 k l z
      using assms by (unfold_locales, auto)
    from case_j1k2_exp_le[OF refl \<open>k \<ge> 2\<close>]
    show ?thesis.
  next
    assume "\<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|"
    have "y \<cdot> x \<noteq> x \<cdot> y"
      using assms(3) by force
    define z' where "z' = rotate \<^bold>|x\<^bold>| z"
    hence "y\<^sup>@k \<cdot> x = z' \<^sup>@ l"
      using arg_cong[OF assms(1), of "\<lambda>t. rotate \<^bold>|x\<^bold>| t"]
      unfolding rotate_append rotate_pow_comm
      by blast
    interpret LS_len_le y x k 1 l z'
      using \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|\<close> \<open>y \<cdot> x \<noteq> x \<cdot> y\<close> \<open>y\<^sup>@k \<cdot> x = z' \<^sup>@ l\<close> \<open>2 \<le> l\<close> \<open>1 \<le> k\<close>
      by (unfold_locales, auto)
    from case_j2k1_exp_le[OF \<open>2 \<le> k\<close> refl]
    show ?thesis.
     qed
  qed
qed

lemma LS_exp_le_conv_rat:
  fixes x y k::"'a::linordered_field"
  assumes "y > 0"
  shows "k * y + 4 \<le> x + 2 * y \<longleftrightarrow> k \<le> (x - 4)/y+ 2"
  unfolding le_diff_eq[symmetric]
  unfolding diff_conv_add_uminus
  unfolding add.assoc add.commute[of "2*y"]
  unfolding add.assoc[symmetric]
  unfolding diff_le_eq[of _ "2*y" "x + - 4",symmetric] left_diff_distrib'[symmetric]
  unfolding pos_le_divide_eq[OF \<open>y > 0\<close>, symmetric]
  unfolding diff_le_eq..


end
