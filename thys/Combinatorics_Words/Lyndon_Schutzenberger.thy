(*  Title:      CoW_Equations/Lyndon_Schutzenberger.thy
    Author:     Štěpán Holub, Charles University
    Author:     Štěpán Starosta, CTU in Prague

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Lyndon_Schutzenberger
  imports Submonoids Periodicity_Lemma

begin

text\<open>If $x^a$ or $y^b$ is sufficiently long, then the claim follows from the Periodicity Lemma.\<close>

lemma LS_per_lemma_case:
  assumes eq: "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c" and "a \<noteq> 0" and "b \<noteq> 0" and "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|"
  shows "x\<cdot>y=y\<cdot>x"
proof (cases "x = \<epsilon>")
  assume "x = \<epsilon>"
  thus "x\<cdot>y=y\<cdot>x" by simp 
next 
  assume "x \<noteq> \<epsilon>"
  hence "z\<^sup>@c \<noteq> \<epsilon>" 
    using eq assms emp_pow[of c] by auto
  hence "x\<^sup>@a \<le>p (z\<^sup>@c)\<^sup>\<omega>"
    unfolding period_root_def using 
      pref_ext[OF triv_pref[of "x\<^sup>@a" "y\<^sup>@b", unfolded eq], of "x\<^sup>@a"] by blast 
  have "x \<^sup>@ a \<le>p x\<^sup>\<omega>"
    using \<open>x \<noteq> \<epsilon>\<close> \<open>a \<noteq> 0\<close> root_self[THEN per_drop_exp] by blast
  from two_pers_root[OF per_drop_exp[OF \<open>x\<^sup>@a \<le>p (z\<^sup>@c)\<^sup>\<omega>\<close>] this \<open>\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x \<^sup>@ a\<^bold>|\<close> ]
  have "z \<cdot> x = x \<cdot> z".
  hence "z\<^sup>@c\<cdot>x\<^sup>@a = x\<^sup>@a\<cdot>z\<^sup>@c"
    by (simp add: comm_add_exps)
  from this[folded eq, unfolded rassoc cancel, symmetric]
  have "x\<^sup>@a \<cdot> y\<^sup>@b = y\<^sup>@b \<cdot> x\<^sup>@a".
  from this[unfolded comm_pow_roots[OF \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>]]
  show "x \<cdot> y = y \<cdot> x".
qed

chapter \<open>Lyndon-Schützenberger Equation\<close>

section \<open>The original result\<close>

text\<open>The Lyndon-Schützenberger equation is the following equation on words:
\[
x^ay^b = z^c,
\]
in this formalization denoted as @{term "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c"}, with $2 \leq a,b,c$.
We formalize here a proof that the equation has periodic solutions only in free monoids, that is, that any three words 
$x$, $y$ and $z$ satisfying the equality pairwise commute.
The result was first proved in @{cite LySch62} in a more general setting of free groups.
There are several proofs to be found in the literature (for instance @{cite Lo83 and Dmsi2006}).
The presented proof is the author's proof.
\<close>

text\<open>We set up a locale representing the Lyndon-Schützenberger Equation.\<close>


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
  have "a \<noteq> 0" and "b \<noteq> 0"  
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
    using pow_per[OF \<open>y \<noteq> \<epsilon>\<close> \<open>b \<noteq> 0\<close>] by blast
  have "u\<cdot>w\<cdot>v = x \<cdot>v"
    by (simp add: \<open>x = u \<cdot> w\<close>) 
  have "u\<cdot>w\<cdot>v = u\<cdot> x"
    by (simp add: \<open>w \<cdot> v = x\<close>)
  have "u\<cdot>w\<cdot>v \<le>p u\<^sup>\<omega>"
    unfolding period_root_def
    using \<open>u \<cdot> w \<cdot> v = u \<cdot> x\<close>[unfolded \<open>x = u \<cdot> w\<close>] \<open>u \<noteq> \<epsilon>\<close> triv_pref[of "u \<cdot> u \<cdot> w" v]
    by force
  have "period (u\<cdot>w\<cdot>v) \<^bold>|u\<^bold>|"
    using \<open>u \<cdot> w \<cdot> v \<le>p u \<^sup>\<omega>\<close> by auto

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
    unfolding comm_pow_roots[OF \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>, of x y].
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

  have "a \<noteq> 0" and "b \<noteq> 0"
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
          using LS_per_lemma_case[OF \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>]
            LS_per_lemma_case[OF LSrev_eq \<open>b \<noteq> 0\<close> \<open>a \<noteq> 0\<close>] with_Periodicity_lemma[unfolded minus]
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
          obtain a' where "Suc a' = a" and "1 \<le> a'"
            using \<open>2 \<le> a\<close> minus by auto
          from eq2[folded \<open>Suc a' = a\<close>, unfolded pow_Suc2 rassoc]  pow_Suc2[of x a', unfolded this, symmetric]
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
          from this[unfolded comm_pow_roots[OF \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>]]
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
  have "c \<noteq> 0" and  "b \<noteq> 0" using  \<open>2 \<le> c\<close> \<open>2 \<le> b\<close> by auto
  have "x \<cdot> x\<^sup>@a \<cdot> y\<^sup>@b = x\<^sup>@a \<cdot> y\<^sup>@b \<cdot> x" and "y \<cdot> x\<^sup>@a \<cdot> y\<^sup>@b = x\<^sup>@a \<cdot> y\<^sup>@b \<cdot> y"
    unfolding comm_add_exp[OF \<open>x \<cdot> y = y \<cdot> x\<close>[symmetric], of b] comm_add_exp[OF \<open>x \<cdot> y = y \<cdot> x\<close>, symmetric, of a]
      lassoc power_commutes by blast+ 
  thus "x\<cdot>z = z\<cdot>x" and "y\<cdot>z = z\<cdot>y"
    using comm_drop_exp[OF \<open>c \<noteq> 0\<close>] unfolding lassoc \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> by metis+
qed
hide_fact Lyndon_Schutzenberger'

lemma Lyndon_Schutzenberger_conjug: assumes "u \<sim> v" and  "\<not> primitive (u \<cdot> v)" shows "u \<cdot> v = v \<cdot> u"
proof-
  obtain r s where "u = r \<cdot> s" and "v = s \<cdot> r"
    using \<open>u \<sim> v\<close> by blast
  have "u \<cdot> v \<sim> r\<^sup>@2 \<cdot> s\<^sup>@2"
    using conjugI'[of "r \<cdot> s \<cdot> s" r] unfolding \<open>u = r \<cdot> s\<close> \<open>v = s \<cdot> r\<close> pow_two rassoc.
  hence "\<not> primitive (r\<^sup>@2 \<cdot> s\<^sup>@2)"
    using \<open>\<not> primitive (u \<cdot> v)\<close> prim_conjug by auto
  from not_prim_pow[OF this, of "r \<cdot> s = s \<cdot> r"]
  have "r \<cdot> s = s \<cdot> r"
    using Lyndon_Schutzenberger(1)[of r 2 s 2, OF _ order.refl order.refl] by metis  
  thus "u \<cdot> v = v \<cdot> u"
    using \<open>u = r \<cdot> s\<close> \<open>v = s \<cdot> r\<close> by presburger
qed

lemma Lyndon_Schutzenberger_prim: assumes "\<not> primitive x" and "\<not> primitive y" and "\<not> primitive (x \<cdot> y)" 
  shows "x \<cdot> y = y \<cdot> x" 
proof
  assume "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" 
  from not_prim_primroot_expE'[OF \<open>\<not> primitive y\<close> \<open>y \<noteq> \<epsilon>\<close>]
  obtain m r where "r\<^sup>@m = y" and "2 \<le> m" and "\<rho> y = r" by metis
  from not_prim_primroot_expE'[OF \<open>\<not> primitive x\<close> \<open>x \<noteq> \<epsilon>\<close>]
  obtain k s where "s\<^sup>@k = x" and "2 \<le> k" and "\<rho> x = s" by metis
  from not_prim_primroot_expE'[OF \<open>\<not> primitive (x \<cdot> y)\<close> pref_nemp[OF \<open>x \<noteq> \<epsilon>\<close>]]
  obtain l z where "z\<^sup>@l = x \<cdot> y" and "2 \<le> l".
  from Lyndon_Schutzenberger(1)[OF this(1)[symmetric,
        folded \<open>r\<^sup>@m = y\<close> \<open>s\<^sup>@k = x\<close>, folded \<open>\<rho> x = s\<close> \<open>\<rho> y = r\<close>] \<open>2 \<le> k\<close> \<open>2 \<le> m\<close> \<open>2 \<le>l\<close>] 
  show "x \<cdot> y = y \<cdot> x" 
    unfolding comp_primroot_conv'[OF \<open>x \<noteq> \<epsilon>\<close> \<open>y \<noteq> \<epsilon>\<close>, symmetric]. 
qed

lemma Lyndon_Schutzenberger_rotate: assumes "x\<^sup>@k = r \<^sup>@ Suc q \<cdot> u\<^sup>@k \<cdot> r \<^sup>@ Suc q"
  and "1 < k" and "u \<noteq> \<epsilon>"
shows "u \<cdot> r = r \<cdot> u" and "u \<cdot> x = x \<cdot> u" and "x \<cdot> r = r \<cdot> x"
proof-
  have "2 \<le> k"
    using One_nat_def assms(2) by presburger
  have "2 \<le> Suc q + Suc q"
    by simp

  have "r \<^sup>@ Suc q \<le>p x \<cdot> r \<^sup>@ Suc q"
    by (metis assms(1) prefI pref_prod_root)
  have "u\<^sup>@k \<cdot> r \<^sup>@ (Suc q + Suc q) = ((r \<^sup>@ Suc q)\<inverse>\<^sup>>(x \<cdot>r\<^sup>@Suc q))\<^sup>@k"
    unfolding add_exps[of r "Suc q" "Suc q"] 
    using 
      per_drop_exp'[of 1 "r \<^sup>@ Suc q" x, THEN lq_conjug_pow, of k,
        unfolded assms(1)] \<open>r \<^sup>@ Suc q \<le>p x \<cdot> r \<^sup>@ Suc q\<close>
    by force

  from Lyndon_Schutzenberger(1)[OF \<open>u\<^sup>@k \<cdot> r \<^sup>@ (Suc q + Suc q) = ((r \<^sup>@ Suc q)\<inverse>\<^sup>>(x \<cdot>r\<^sup>@Suc q))\<^sup>@k\<close> \<open>2 \<le>k\<close> \<open>2 \<le> Suc q + Suc q\<close> \<open>2 \<le>k\<close>]
  show "u \<cdot> r = r \<cdot> u".

  have "x\<^sup>@k \<cdot> r = r \<cdot> x\<^sup>@k"
    unfolding assms(1) lassoc pow_comm[of r "Suc q", symmetric]
    unfolding rassoc power_commuting_commutes[OF \<open>u \<cdot> r = r \<cdot> u\<close>, of k, symmetric] 
      pow_comm[of r "Suc q", symmetric]
    by simp
  from comm_drop_exp[OF gr_implies_not0[OF assms(2)] this[symmetric]]
  show "x \<cdot> r = r \<cdot> x".
  show "u \<cdot> x = x \<cdot> u"
  proof(cases "r = \<epsilon>")
    case True
    with Lyndon_Schutzenberger(2)[OF \<open>u\<^sup>@k \<cdot> r \<^sup>@ (Suc q + Suc q) = ((r \<^sup>@ Suc q)\<inverse>\<^sup>>(x \<cdot>r\<^sup>@Suc q))\<^sup>@k\<close> \<open>2 \<le>k\<close> \<open>2 \<le> Suc q + Suc q\<close> \<open>2 \<le>k\<close>]
    show ?thesis
      by force
  next
    case False
    from comm_trans[OF \<open>u \<cdot> r = r \<cdot> u\<close> \<open>x \<cdot> r = r \<cdot> x\<close> this]
    show ?thesis.
  qed
qed

section \<open>Parametric solution of the equation @{term "x\<^sup>@j\<cdot>y\<^sup>@k = z\<^sup>@l"}\<close>

subsection \<open>Auxiliary lemmas\<close>

lemma xjy_imprim: assumes "x \<cdot> y \<noteq> y \<cdot> x" and eq: "x\<^sup>@j \<cdot> y = z\<^sup>@l" and "2 \<le> j" and "2 \<le> l"
  shows "\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|y\<^bold>| + 2*\<^bold>|x\<^bold>|" and "\<^bold>|z\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>|" and "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|" and "\<^bold>|x\<^sup>@j\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|"
proof-
  obtain j' where "j = Suc (Suc j')"
    using \<open>2 \<le> j\<close> using at_least2_Suc by metis
  have "j \<noteq> 0"
    using \<open>2 \<le> j\<close> by force+
  from LS_per_lemma_case[of _ _ _ 1, unfolded pow_one', OF eq this]
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

subsection \<open>@{term x} is longer\<close>

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

subsubsection \<open>case @{term "j = 2"}\<close>

lemma case_j2k1: assumes "2 \<le> j" "k = 1"
  obtains r q t where
    "(r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r = x" and
    "q \<cdot> r \<cdot> r \<cdot> q  =  y" and
    "(r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r \<cdot> r \<cdot> q = z" and
    "j = 2" and "l = 2" and "r\<cdot>q \<noteq> q\<cdot>r" and
    "primitive x" and "primitive y"
proof-
  note eq' = eq[unfolded \<open>k = 1\<close> pow_one']
  note xjy_imprim[OF non_comm eq[unfolded \<open>k = 1\<close> pow_one'] \<open>2 \<le> j\<close> l_min]

  obtain j' where "j = Suc (Suc j')"
    using \<open>2 \<le> j\<close> using at_least2_Suc by metis
  hence "j \<noteq> 0" by blast
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

  note eq[ unfolded \<open>k = 1\<close> pow_one' \<open>j = 2\<close> \<open>l = 2\<close> pow_two rassoc]
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
  obtain r q t' where "r \<cdot> q = p" and "q \<cdot> r = s" and "(r \<cdot> q)\<^sup>@t'\<cdot>r = x" and "q \<noteq> \<epsilon>".
  note \<open>s \<cdot> p = y\<close>[folded \<open>q \<cdot> r = s\<close> \<open>r \<cdot> q = p\<close>, unfolded rassoc]
  from y_le_x[folded this \<open>(r \<cdot> q)\<^sup>@t'\<cdot>r = x\<close>, unfolded lenmorph pow_len] nemp_len[OF \<open>q \<noteq> \<epsilon>\<close>]
    add_le_mono1[OF mult_le_mono1[of t' 1 "\<^bold>|r\<^bold>| + \<^bold>|q\<^bold>|", unfolded mult_1], of "\<^bold>|r\<^bold>|"]
  have "2 \<le> t'"
    by linarith
  then obtain t where "t' = Suc (Suc t)"
    using at_least2_Suc by blast
  from \<open>p \<cdot> z = x \<cdot> y\<close>[folded \<open>q \<cdot> r \<cdot> r \<cdot> q = y\<close> \<open>(r \<cdot> q)\<^sup>@t'\<cdot>r = x\<close>  \<open>r \<cdot> q = p\<close>, unfolded \<open>t' = Suc (Suc t)\<close> pow_Suc rassoc cancel, symmetric]
  have z: "(r \<cdot> q) \<^sup>@ Suc (Suc t) \<cdot> r \<cdot> r \<cdot> q = z"
    unfolding pow_Suc2[of _ "Suc t"] unfolding pow_Suc rassoc.

\<comment> \<open>y is primitive due to the Lyndon-Schutzenberger\<close>

  from comm_drop_exp[OF \<open>j \<noteq> 0\<close>, of y x j, unfolded eq']
  have "primitive y"
    using Lyndon_Schutzenberger_prim[OF pow_nemp_imprim[OF \<open>2 \<le>j\<close>], of y x, unfolded eq', OF _ pow_nemp_imprim[OF l_min]] non_comm by argo

  hence "q \<cdot> r \<noteq> r \<cdot> q"
    using \<open>p \<noteq> \<epsilon>\<close> \<open>q \<cdot> r = s\<close> \<open>r \<cdot> q = p\<close> \<open>s \<cdot> p = y\<close> comm_not_prim[OF \<open>s \<noteq> \<epsilon>\<close> \<open>p \<noteq> \<epsilon>\<close>] by argo

\<comment> \<open>primitivity of x using @{thm per_le_prim_iff}\<close>

  thm per_le_prim_iff[of x p]
  have "x \<le>p p \<cdot> x"
    unfolding \<open>(r \<cdot> q)\<^sup>@t'\<cdot>r = x\<close>[symmetric] \<open>r \<cdot> q = p\<close>[symmetric]
    by comparison
  have "2*\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|"
    unfolding \<open>(r \<cdot> q)\<^sup>@t'\<cdot>r = x\<close>[symmetric] \<open>r \<cdot> q = p\<close>[symmetric] lenmorph pow_len
    using mult_le_mono1[OF \<open>2 \<le> t'\<close>, of "(\<^bold>|r\<^bold>| + \<^bold>|q\<^bold>|)"] by linarith 
  have [symmetric]: "p \<cdot> x \<noteq> x \<cdot> p"
    unfolding \<open>(r \<cdot> q)\<^sup>@t'\<cdot>r = x\<close>[symmetric] \<open>r \<cdot> q = p\<close>[symmetric] lassoc pow_comm[symmetric]
    unfolding rassoc cancel by fact
  with per_le_prim_iff[OF \<open>x \<le>p p \<cdot> x\<close> \<open>p \<noteq> \<epsilon>\<close> \<open> 2 * \<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>] 
  have "primitive x" 
    by blast

  from that[OF \<open>(r \<cdot> q)\<^sup>@t'\<cdot>r = x\<close>[unfolded \<open>t' = Suc (Suc t)\<close>] \<open>q \<cdot> r \<cdot> r \<cdot> q = y\<close> z \<open>j = 2\<close> \<open>l = 2\<close> \<open>q\<cdot>r \<noteq> r\<cdot>q\<close>[symmetric]
      \<open>primitive x\<close> \<open>primitive y\<close>]
  show thesis.
qed 

subsubsection \<open>case @{term "j = 1"}\<close>

lemma case_j1k2_primitive: assumes "j = 1" "2 \<le> k"
  shows "primitive x"
  using Lyndon_Schutzenberger_prim[OF _ pow_nemp_imprim
      pow_nemp_imprim[OF l_min, of z, folded eq], OF _ \<open>2 \<le> k\<close>]
    comm_pow_roots[of j k x y] k_min non_comm
  unfolding \<open>j = 1\<close> pow_one'
  by linarith

lemma case_j1k2_a: assumes "j = 1" "2 \<le> k" "z \<le>s y\<^sup>@k"
  obtains r q t where
    "x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
      (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q" and
    "y = r \<cdot> (q \<cdot> r) \<^sup>@ Suc t" and
    "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)" and "r\<cdot>q \<noteq> q\<cdot>r"
proof-
  have "z \<noteq> \<epsilon>"
    using assms(1) bin_fst_nemp eq by force
  have "k \<noteq> 0" "k - 1 \<noteq> 0"
    using \<open>2 \<le> k\<close> by linarith+
  have "l \<noteq> 0" "l - 1 \<noteq> 0"
    using l_min by linarith+

  from LS_per_lemma_case[reversed, OF eq \<open>k \<noteq> 0\<close>, unfolded \<open>j = 1\<close>]
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
    unfolding pop_pow_one[OF \<open>k \<noteq> 0\<close>]
    using pref_prod_less[OF _ \<open>\<^bold>|v\<^bold>| < \<^bold>|y\<^bold>|\<close>]
    by blast
  obtain u where "v\<cdot>u = y" "u \<noteq> \<epsilon>"
    using \<open>v <p y\<close> unfolding strict_suffix_def suffix_def
    by blast

  have "z = u\<cdot>y\<^sup>@(k-1)"
    using \<open>y\<^sup>@k = v\<cdot>z\<close>[unfolded pop_pow_one[OF \<open>k \<noteq> 0\<close>],
        folded \<open>v \<cdot> u = y\<close>, unfolded rassoc cancel,
        unfolded \<open>v \<cdot> u = y\<close>, symmetric].

  note eq[unfolded pop_pow_one'[OF \<open>l \<noteq> 0\<close>] \<open>y\<^sup>@k = v\<cdot>z\<close> lassoc cancel_right
      \<open>j = 1\<close> pow_one']

  obtain u' where "u'\<cdot>v = y"
  proof-
    have "v \<le>s z\<^sup>@(l-1)"
      using \<open>x \<cdot> v = z \<^sup>@ (l - 1)\<close> by blast
    moreover have "y \<le>s z\<^sup>@(l-1)"
      unfolding \<open>z = u\<cdot>y\<^sup>@(k-1)\<close> pop_pow_one'[OF \<open>k - 1 \<noteq> 0\<close>]
        pop_pow_one'[OF \<open>l - 1 \<noteq> 0\<close>] lassoc
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

  from \<open>x \<cdot> v = z \<^sup>@ (l - 1)\<close>[folded z[symmetric] \<open>(r \<cdot> q) \<^sup>@ t \<cdot> r = v\<close>,
      unfolded pop_pow_one'[OF \<open>k - 1 \<noteq> 0\<close>] pop_pow_one'[OF \<open>l - 1 \<noteq> 0\<close>]]
  have x: "x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
      (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q"
    unfolding pop_pow_one[OF Suc_not_Zero] diff_Suc_1 shift_pow
    unfolding lassoc cancel_right
    unfolding rassoc pop_pow_one'[OF \<open>k - 1 \<noteq> 0\<close>]
    unfolding diff_Suc_eq_diff_pred[symmetric] Suc_1.

  (* ALT approach *)
  (* let ?x = "((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot> *)
      (* (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q" *)
  (* have "?x \<cdot> v = z \<^sup>@ (l - 1)" *)
    (* unfolding z \<open>(r \<cdot> q) \<^sup>@ t \<cdot> r = v\<close>[symmetric] pop_pow_one'[OF \<open>k - 1 \<noteq> 0\<close>] *)
    (* pop_pow_one'[OF \<open>l - 1 \<noteq> 0\<close>] diff_diff_left nat_1_add_1 *)
    (* by (simp only: shifts) *)
  (* from \<open>x \<cdot> v = z \<^sup>@ (l - 1)\<close>[folded this] *)
  (* have "x = ?x" *)
    (* by blast *)


  have "z\<cdot>y \<noteq> y\<cdot>z"
    using non_comm
    using power_commuting_commutes[of z y l, folded eq,
        unfolded rassoc pow_comm, unfolded lassoc cancel_right
        \<open>j = 1\<close> pow_one']
    by blast
  hence "r\<cdot>q \<noteq> q\<cdot>r"
    unfolding \<open>q \<cdot> r = u\<close> \<open>r \<cdot> q = u'\<close> \<open>u'\<cdot> v  = y\<close>[symmetric]
      \<open>z = u \<cdot> y \<^sup>@ (k - 1)\<close> pop_pow_one'[OF \<open>k \<noteq> 0\<close>] rassoc
      \<open>y \<^sup>@ k = v \<cdot> z\<close>[unfolded \<open>u' \<cdot> v = y\<close>[symmetric]
        \<open>z = u \<cdot> y \<^sup>@ (k - 1)\<close>, symmetric] cancel_right..

  show thesis
    using that[OF x y z \<open>r\<cdot>q \<noteq> q\<cdot>r\<close>].
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
  have "l \<noteq> 0" using l_min by linarith
  have "x = (q\<cdot>y\<^sup>@k)\<^sup>@(l-1)\<cdot>q"
    using eq[unfolded pop_pow_one'[OF \<open>l \<noteq> 0\<close>] \<open>j = 1\<close> pow_one',
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

lemma case_j1k1: assumes "j = 1" "k = 1"
  obtains r q m n where
    "x = (r\<cdot>q)\<^sup>@m\<cdot>r" and
    "y = q\<cdot>(r\<cdot>q)\<^sup>@n" and
    "z = r\<cdot>q" and
    "Suc (m+n)=l" and "r\<cdot>q \<noteq> q\<cdot>r"
proof-
  from eq[unfolded assms pow_one']
  have "x \<cdot> y = concat ([z] \<^sup>@ l)"
    by (simp add: concat_pow)
  hence "x <p concat ([z] \<^sup>@ l)"
    using bin_snd_nemp by blast

  from pref_mod_list[OF this]
  obtain m r where "m < \<^bold>|[z] \<^sup>@ l\<^bold>|" "r <p ([z] \<^sup>@ l) ! m"
    "concat (take m ([z] \<^sup>@ l)) \<cdot> r = x".

  have "m < l"
    using \<open>m < \<^bold>|[z] \<^sup>@ l\<^bold>|\<close>
    unfolding sing_pow_len.

  obtain n where "Suc (m + n) = l"
    using less_imp_Suc_add[OF \<open>m < l\<close>]
    by blast

  have "z\<^sup>@m\<cdot>r = x"
    using \<open>concat (take m ([z] \<^sup>@ l)) \<cdot> r = x\<close> 
    unfolding concat_take_sing[OF less_or_eq_imp_le, OF disjI1, OF \<open>m < l\<close>].

  have "r <p z"
    using \<open>m < \<^bold>|[z] \<^sup>@ l\<^bold>|\<close> \<open>r <p ([z] \<^sup>@ l) ! m\<close> sing_pow_len sing_pow_nth by metis
  then obtain q where "z = r\<cdot>q" "q \<noteq> \<epsilon>"
    by blast

  have "z \<^sup>@ m\<inverse>\<^sup>>z \<^sup>@ l = z\<^sup>@(l-m)"
    using lq_triv
      pop_pow[OF less_or_eq_imp_le[OF disjI1, OF \<open>m < \<^bold>|[z] \<^sup>@ l\<^bold>|\<close>], symmetric]
    unfolding sing_pow_len
    by auto
  hence "z \<^sup>@ m\<inverse>\<^sup>>z \<^sup>@ l = z\<cdot>z\<^sup>@n"
    unfolding pop_pow_one[OF zero_less_diff'[OF \<open>m < l\<close>]]
    using \<open>Suc (m + n) = l\<close> by force
  have "y = q\<cdot>(r\<cdot>q)\<^sup>@n"
    using lqI[OF \<open>x \<cdot> y = z \<^sup>@ l\<close>[folded \<open>z\<^sup>@m\<cdot>r = x\<close>, unfolded rassoc], symmetric]
    unfolding \<open>z \<^sup>@ m\<inverse>\<^sup>>z \<^sup>@ l = z\<cdot>z\<^sup>@n\<close>
    unfolding \<open>z = r\<cdot>q\<close> rassoc cancel.

  have "x\<cdot>z \<noteq> z\<cdot>x"
    using conjug_pow[of z x z l, folded \<open>x \<cdot> y = z \<^sup>@ l\<close>, 
        unfolded rassoc cancel, OF sym, symmetric]
      non_comm by blast
  hence "r\<cdot>q \<noteq> q\<cdot>r"
    unfolding \<open>z \<^sup>@ m \<cdot> r = x\<close>[symmetric] \<open>z = r \<cdot> q\<close>
    unfolding lassoc power_commutes[of "r\<cdot>q" m, symmetric]
    unfolding rassoc cancel.

  show ?thesis
    using that[OF \<open>z\<^sup>@m\<cdot>r = x\<close>[unfolded \<open>z = r\<cdot>q\<close>, symmetric]
        \<open>y = q\<cdot>(r\<cdot>q)\<^sup>@n\<close> \<open>z = r\<cdot>q\<close> \<open>Suc (m+n) = l\<close> \<open>r\<cdot>q \<noteq> q\<cdot>r\<close>].
qed

subsection \<open>Putting things together\<close>

lemma solution_cases: obtains 
  "j = 2" "k = 1" |
  "j = 1" "2 \<le> k" "z <s y\<^sup>@k" |
  "j = 1" "2 \<le> k" "y\<^sup>@k <s z" |
  "j = 1" "k = 1"
proof-
  have "l\<noteq>0" "l-1 \<noteq> 0"
    using l_min by linarith+
  have "k \<noteq> 0"
    using k_min by linarith
  have "j \<noteq> 0"
    using j_min by linarith
  have "z \<noteq> \<epsilon>"
    using eq nemp_pow_nemp[of z l] bin_fst_nemp[folded nonzero_pow_emp[OF \<open>j \<noteq> 0\<close>, of x], THEN pref_nemp]
    by force 
  have "z \<noteq> y\<^sup>@k"
  proof 
    assume "z = y\<^sup>@k"
    with eq[unfolded pop_pow_one'[OF \<open>l\<noteq>0\<close>], folded this, unfolded cancel_right]
    have "x\<^sup>@j \<cdot> y\<^sup>@k = y\<^sup>@k \<cdot> x\<^sup>@j"
      using pow_comm by auto
    with comm_drop_exps[of x "j-1" y "k - 1", unfolded Suc_minus[OF \<open>j \<noteq> 0\<close>] Suc_minus[OF \<open>k \<noteq> 0\<close>]] 
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
        THEN ruler_pref'[reversed]] \<open>z \<noteq> y\<^sup>@k\<close>
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
  "Suc (m+n) = l" and "r\<cdot>q \<noteq> q\<cdot>r"
|
  \<comment>\<open>case @{term "x\<cdot>y\<^sup>@k"} with @{term "2 \<le> k"} and @{term "z <s y\<^sup>@k"}\<close>
  r q t where
  "x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
      (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q" and
  "y = r \<cdot> (q \<cdot> r) \<^sup>@ Suc t" and
  "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)" and
  "r\<cdot>q \<noteq> q\<cdot>r"
|
  \<comment>\<open>case @{term "x\<cdot>y\<^sup>@k"} with @{term "2 \<le> k"} and @{term "y\<^sup>@k <s z"}\<close>
  q where 
  "x = (q\<cdot>y\<^sup>@k)\<^sup>@(l-1)\<cdot>q" and
  "z = q\<cdot>y\<^sup>@k" and 
  "q\<cdot>y \<noteq> y\<cdot>q"
|
  \<comment>\<open>case @{term "x\<^sup>@j\<cdot>y"} with @{term "2 \<le> j"}\<close>
  r q t where
  "x = (r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r" and
  "y  =  q \<cdot> r \<cdot> r \<cdot> q" and
  "z = (r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r \<cdot> r \<cdot> q" and
  "j = 2" and "l = 2" and "r\<cdot>q \<noteq> q\<cdot>r" and
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
    from case_j1k2_a[OF \<open>j = 1\<close> \<open>2 \<le> k\<close>, of thesis]
    show ?thesis
      using that(2) \<open>z <s y \<^sup>@ k\<close> unfolding strict_suffix_def
      by blast
  next
    case 3
    from case_j1k2_b[OF this, of thesis]
    show ?thesis
      using that(3) by blast
  next
    case 4
    from case_j1k1[OF this, of thesis]
    show ?thesis
      using that(1) by blast
  qed
qed

end (* end locale *)

text \<open>Using the solution from locale @{term LS_len_le},
the following theorem gives the full characterization of the equation in question:
$$ x^iy^j = z^\ell $$
\<close>

theorem LS_parametric_solution:
  assumes y_le_x: "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    and j_min: "1 \<le> j"  and k_min: "1 \<le> k" and l_min: "2 \<le> l"
  shows 
    "x\<^sup>@j \<cdot> y\<^sup>@k = z\<^sup>@l
  \<longleftrightarrow> ( 
    (\<exists>r m n t. 
        x = r\<^sup>@m \<and> y = r\<^sup>@n \<and> z = r\<^sup>@t \<and> m*j+n*k=t*l) \<comment>\<open>{x,y} is not a code\<close>
  \<or> ((j = 1 \<and> k = 1) \<and>
    (\<exists>r q m n. 
        x = (r\<cdot>q)\<^sup>@m\<cdot>r \<and> y = q\<cdot>(r\<cdot>q)\<^sup>@n \<and> z = r\<cdot>q \<and> Suc(m+n) = l \<and> r\<cdot>q \<noteq> q\<cdot>r))
  \<or> ((j = 1 \<and> 2 \<le> k) \<and> 
      (\<exists>r q t. 
        x = ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2)\<cdot>(((q \<cdot> r) \<cdot>
               (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q
      \<and> y = r \<cdot> (q \<cdot> r) \<^sup>@ Suc t
      \<and> z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)
      \<and> r\<cdot>q \<noteq> q\<cdot>r))
  \<or> ((j = 1 \<and> 2 \<le> k) \<and>
    (\<exists>r q. 
        x = (q\<cdot>r\<^sup>@k)\<^sup>@(l-1)\<cdot>q \<and> y = r \<and> z = q\<cdot>r\<^sup>@k \<and> r\<cdot>q \<noteq> q\<cdot>r))
  \<or> ((j = 2 \<and> k = 1 \<and> l = 2) \<and> 
    (\<exists>r q t. 
        x = (r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r \<and> y = q \<cdot> r \<cdot> r \<cdot> q 
      \<and> z = (r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r \<cdot> r \<cdot> q  \<and> r\<cdot>q \<noteq> q\<cdot>r ))
  )
  "
    (is "?eq =
   (?sol_per \<or> (?cond_j1k1 \<and> ?sol_j1k1) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_a) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_b) \<or>
   (?cond_j2k1l2 \<and> ?sol_j2k1l2))")
proof(rule iffI)
  assume eq: "x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l"
  show 
    "(?sol_per \<or> (?cond_j1k1 \<and> ?sol_j1k1) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_a) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_b) \<or>
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
        by blast+
      thus ?thesis
        using \<open>k = 1\<close> \<open>j = 2\<close> by blast
    next
      case 2
      have "?sol_j1k2_a"
        using case_j1k2_a[OF \<open>j = 1\<close> \<open>2 \<le> k\<close> ssufD1[OF \<open>z <s y \<^sup>@ k\<close>], of ?sol_j1k2_a] 
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
      with case_j1k1[OF this, of ?sol_j1k1]
      have"?sol_j1k1"
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
   (?cond_j1k2 \<and> ?sol_j1k2_a) \<or>
   (?cond_j1k2 \<and> ?sol_j1k2_b) \<or>
   (?cond_j2k1l2 \<and> ?sol_j2k1l2))"
  then show ?eq
  proof(elim disjE conjE exE)
    fix r m n t
    assume sol: "x = r \<^sup>@ m" "y = r \<^sup>@ n" "z = r \<^sup>@ t" 
      and "m * j + n * k = t * l"
    show ?thesis
      unfolding sol
      unfolding power_mult[symmetric] power_add[symmetric] 
      unfolding \<open>m * j + n * k = t * l\<close>..
  next
    fix r q m n
    assume "j = 1" "k = 1" and sol: "x = (r\<cdot>q)\<^sup>@m\<cdot>r"
      "y = q\<cdot>(r\<cdot>q)\<^sup>@n" "z = r\<cdot>q"
      and "Suc(m+n) = l"
    show ?thesis
      unfolding sol
      unfolding \<open>j = 1\<close> \<open>k = 1\<close> \<open>Suc(m+n) = l\<close>[symmetric] pow_one'
      unfolding lassoc pow_Suc add_exps
      unfolding power_commutes[of _ m, symmetric] lassoc..
  next
    fix r q t
    assume "j = 1" "2 \<le> k" and sol:
      "x =
        ((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)) \<^sup>@ (l - 2) \<cdot>
        (((q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 2)) \<cdot> r) \<cdot> q"
      "y = r \<cdot> (q \<cdot> r) \<^sup>@ Suc t"
      "z = (q \<cdot> r) \<cdot> (r \<cdot> (q \<cdot> r) \<^sup>@ Suc t) \<^sup>@ (k - 1)"
    obtain k' where  "Suc (Suc k') = k" using  Suc_minus2[OF \<open>2 \<le> k\<close>] by blast
    hence k1: "k - 1 = Suc k'" and k2: "k - 2 = k'" and k: "k = k'+ 2" by fastforce+ 
    obtain l' where "Suc (Suc l') = l" using  Suc_minus2[OF \<open>2 \<le> l\<close>] by blast 
    hence l2: "l - 2 = l'" and l: "l  = l' + 2"  by fastforce+
    show "x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l"
      unfolding sol \<open>j = 1\<close> k1 k2 l2 unfolding k l by comparison
  next
    fix r q
    assume "j = 1" "2 \<le> k" and sol: "x = (q \<cdot> r \<^sup>@ k) \<^sup>@ (l - 1) \<cdot> q" "y = r" "z = q \<cdot> r \<^sup>@ k"
    show ?thesis
      unfolding sol \<open>j = 1\<close> pow_one'
      unfolding pop_pow_one'[OF \<open>l \<noteq> 0\<close>] rassoc..
  next
    fix r q t
    assume "j = 2" "k = 1" "l = 2" and  sol:
      "x = (r \<cdot> q) \<^sup>@ Suc (Suc t) \<cdot> r"
      "y = q \<cdot> r \<cdot> r \<cdot> q" "z = (r \<cdot> q) \<^sup>@ Suc (Suc t) \<cdot> r \<cdot> r \<cdot> q"
    show "x \<^sup>@ j \<cdot> y \<^sup>@ k = z \<^sup>@ l"
      unfolding \<open>j = 2\<close> \<open>k = 1\<close> \<open>l = 2\<close> sol pow_one' pow_two
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
      unfolding u_def rassoc pow_Suc2[symmetric]  Suc_minus[OF \<open>ka \<noteq> 0\<close>] by fact
    have "\<not> primitive (u \<cdot> y \<cdot> y)"
      unfolding u_def rassoc using \<open>\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@ka')\<close>[unfolded \<open>x\<^sup>@j\<cdot>y\<^sup>@ka' = x\<^sup>@j\<cdot>y\<^sup>@ka\<cdot>y\<^sup>@dif\<close> \<open>dif = 1\<close> pow_one'] 
      unfolding pow_Suc2[of y "ka - 1", unfolded Suc_minus[OF \<open>ka \<noteq> 0\<close>]] rassoc.
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

  obtain l z where [symmetric]:"z\<^sup>@l = x\<^sup>@j\<cdot>y" and "2 \<le> l"
    using  not_prim_pow[OF \<open>\<not> primitive(x\<^sup>@j\<cdot>y)\<close>].
  have "x\<^sup>@j\<cdot>y\<^sup>@1 = z\<^sup>@l"
    by (simp add: \<open>x \<^sup>@ j \<cdot> y = z \<^sup>@ l\<close>)
  interpret eq1: LS_len_le x y j 1 l z
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> \<open>x\<^sup>@j\<cdot>y\<^sup>@1 = z\<^sup>@l\<close> \<open>2 \<le> l\<close> \<open>2 \<le> j\<close>
    by(unfold_locales, linarith+)

  from eq1.case_j2k1[OF \<open>2 \<le> j\<close>]
  obtain r q t where
    xrq: "(r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r = x" and
    yrq: "q \<cdot> r \<cdot> r \<cdot> q  =  y" and
    "(r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r \<cdot> r \<cdot> q = z" and
    "j = 2" and "l = 2" and "r\<cdot>q \<noteq> q\<cdot>r" and
    "primitive x" and "primitive y"
    by blast

  have "q\<cdot>r \<noteq> \<epsilon>" "r\<cdot>q \<noteq> \<epsilon>"
    using eq1.bin_snd_nemp yrq by fastforce+

  obtain z' l' where "x\<cdot>y\<^sup>@k = z'\<^sup>@l'" "2 \<le> l'"
    using not_prim_pow[OF \<open>\<not> primitive (x \<cdot> y \<^sup>@ k)\<close>] by metis
  have "l' \<noteq> 0" and "l' - 1 \<noteq> 0"
    using \<open>2 \<le> l'\<close> by auto

  have "k \<noteq> 0"
    using \<open>2 \<le> k\<close> by linarith

  let ?w = "(r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> (r \<cdot> q) \<cdot> r" 

  have "(r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> (r \<cdot> q) \<cdot> r \<le>p ((r \<cdot> q) \<cdot> (r \<cdot> q) \<^sup>@ (Suc (Suc t))) \<cdot> (r \<cdot> q) \<cdot> r"
    unfolding pow_comm[symmetric] rassoc pref_cancel_conv using triv_pref.
  hence per1: "?w \<le>p (r \<cdot> q) \<cdot> ?w"
    unfolding rassoc.

  have "((r \<cdot> q) \<^sup>@ (Suc (Suc t)) \<cdot> r) \<cdot> q \<cdot> r \<le>p z'\<^sup>@l'"
    unfolding \<open>x\<cdot>y\<^sup>@k = z'\<^sup>@l'\<close>[folded xrq yrq, unfolded rassoc, symmetric]
    unfolding rassoc pop_pow_one[OF \<open>k \<noteq> 0\<close>]
    by simp
  hence per2: "?w \<le>p z' \<cdot> ?w"
    using pref_prod_root by auto

  have "(r \<cdot> q) \<cdot> z' \<noteq> z' \<cdot> (r \<cdot> q)"
  proof
    have "k \<noteq> 0"
      using \<open>2 \<le> k\<close> by simp
    have "y\<^sup>@k = y\<^sup>@Suc (k - 1)"
      unfolding Suc_minus[OF \<open>k \<noteq> 0\<close>]..
    assume "(r \<cdot> q) \<cdot> z' = z' \<cdot> (r \<cdot> q)"
    hence "(r \<cdot> q) \<cdot> z'\<^sup>@l' = z'\<^sup>@l' \<cdot> r \<cdot> q"
      by (simp add: power_commuting_commutes)
    from this[folded \<open>x\<cdot>y\<^sup>@k = z'\<^sup>@l'\<close>[unfolded \<open>y\<^sup>@k = y\<^sup>@Suc (k - 1)\<close>] xrq yrq] 
    have "q \<cdot> r = r \<cdot> q"
      unfolding shifts by mismatch 
    thus False
      using \<open>r \<cdot> q \<noteq> q \<cdot> r\<close> by presburger
  qed
  with two_pers[OF _ per2, of "r\<cdot>q"] per1
  have "\<^bold>|?w\<^bold>| < \<^bold>|r \<cdot> q\<^bold>| + \<^bold>|z'\<^bold>|"
    unfolding rassoc using leI by blast
  hence "\<^bold>|x\<^bold>| \<le> \<^bold>|z'\<^bold>|"
    unfolding xrq[symmetric]
    by simp
  note eq2 = eqd[OF \<open>x\<cdot>y\<^sup>@k = z'\<^sup>@l'\<close>[unfolded pop_pow_one[OF \<open>l' \<noteq> 0\<close>]] this,
      folded xrq, unfolded pow_Suc pop_pow_one'[OF \<open>l' - 1 \<noteq> 0\<close>]]
  hence "z' \<le>s y\<^sup>@k" 
    unfolding lassoc by blast
  have  "r \<cdot> q \<cdot> r \<cdot> q \<le>p z'" 
    using eq2 by force
  hence "r\<cdot>q\<cdot>r\<cdot>q \<le>f (q\<cdot>r\<cdot>r\<cdot>q)\<^sup>@k"
    using \<open>z' \<le>s y\<^sup>@k\<close>[folded yrq]
    by blast

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
        OF _ _  \<open>\<not> primitive (x \<^sup>@ j \<cdot> y \<^sup>@ k)\<close>]
      comm_drop_exps[of x "j - 1" y "k - 1", unfolded Suc_minus'[OF \<open>1 \<le> j\<close>] Suc_minus'[OF \<open>1 \<le> k\<close>]]
      \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by blast

  have "j' = 1 \<or> k' = 1"
    using Lyndon_Schutzenberger_prim[OF pow_non_prim pow_non_prim,
        OF _ _  \<open>\<not> primitive (x \<^sup>@ j' \<cdot> y \<^sup>@ k')\<close>]
      comm_drop_exps[of x "j' - 1" y "k' - 1", unfolded Suc_minus'[OF \<open>1 \<le> j'\<close>] Suc_minus'[OF \<open>1 \<le> k'\<close>]]
      \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by blast

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
        using \<open>\<not> primitive(x\<^sup>@j'\<cdot>y\<^sup>@k')\<close>[unfolded \<open>k'=1\<close> pow_one'] \<open>\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)\<close>[unfolded \<open>j=1\<close> pow_one']
        by blast
    next
      assume "k \<noteq> k'" and  "j \<noteq> 1"
      hence "2 \<le> j" and "k = 1" and "2 \<le> k'" and "j' = 1"
        using \<open>1 \<le> j\<close> \<open>j = 1 \<or> k = 1\<close> \<open>1 \<le> k'\<close> \<open>j' = 1 \<or> k' = 1\<close> by auto 
      from LS_unique_distinct[OF \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>2 \<le> j\<close> _ \<open>2 \<le> k'\<close>] 
      show False
        using \<open>\<not> primitive(x\<^sup>@j'\<cdot>y\<^sup>@k')\<close>[unfolded \<open>j'=1\<close> pow_one'] \<open>\<not> primitive(x\<^sup>@j\<cdot>y\<^sup>@k)\<close>[unfolded \<open>k=1\<close> pow_one']
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

end