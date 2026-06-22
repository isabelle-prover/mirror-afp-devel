(*Session: Wooley_Elementary_Discrete_Inequality
  Title: Wooley's Discrete Inequality
  Author: Angeliki Koutsoukou-Argyraki 
  Affiliation: Royal Holloway, University of London
  Date: 1 October 2024.*)

section\<open>Wooley's Discrete Inequality\<close>

theory Wooley_Elementary_Discrete_Inequality 
  imports "HOL-Library.Quadratic_Discriminant" "HOL-Real_Asymp.Real_Asymp"

begin

text\<open>This is a formalisation of the proof of an inequality by Trevor D. Wooley attesting that when 
$\lambda > 0$, $$\min_{r \in \mathbb{N}}(r + \lambda/r) \leq \sqrt{4 \lambda +1}$$
with equality if and only if $\lambda = m(m-1)$ for some positive integer $m$.
The source is the note "An Elementary Discrete Inequality" available on Wooley's webpage 
\cite{Wooley_notes_inequality}:
\url{https://www.math.purdue.edu/~twooley/publ/20230410discineq.pdf}.\<close>


subsection\<open>General elementary technical lemmas\<close>

lemma obtains_nat_in_interval: 
  fixes x::real assumes "x\<ge>0"
  obtains c::nat where "c \<in> {x<.. x+1}" 
proof
  show "nat\<lfloor>x+1\<rfloor> \<in> {x<..x + 1}"
    using assms by force
qed

lemma obtains_nat_in_interval_greater_leq: 
  fixes x::real assumes "x\<ge>0"
  obtains c::nat where "c >x" and "c \<le> x+1" 
  by (meson assms greaterThanAtMost_iff obtains_nat_in_interval)

lemma obtains_nat_in_interval_half: 
  fixes x::real assumes "x\<ge>1/2"
  obtains c::nat where "c > x - (1/2)" and "c \<le> x+1/2" 
  using assms  obtains_nat_in_interval_greater_leq [of "x-1/2"]
  by (smt (verit) field_sum_of_halves)


subsection\<open>Trivial case, where we minimise over all positive real values of $r$\<close>

theorem elementary_ineq_Wooley_real:
  fixes l::real and g::"real \<Rightarrow> real" 
  assumes "l>0" and "\<forall> r \<in> R. g r = r+(l/r)"
    and "R={r::real. r>0}" 
  shows "(\<forall> r \<in> R. g r \<ge>  2* sqrt(l)) \<and> (\<forall> r \<in> R. g (sqrt(l)) \<le> g r)"
proof-
  have "\<forall> r \<in> R. 2 * sqrt(l)+ (sqrt(r) - (sqrt(l)/sqrt(r)))^2 = r+(l/r)"
    using  assms   by (simp add: power_divide power2_diff)
  moreover
  have "\<forall> r \<in> R. 2 * sqrt(l)+ (sqrt(r) - (sqrt(l)/sqrt(r)))^2 \<ge> 2 *(sqrt(l))"
    using assms by auto
  ultimately have "\<forall> r \<in> R. r+(l/r) \<ge> 2*sqrt(l)" by simp
  moreover
  have "g (sqrt(l)) = 2 *sqrt(l)" using assms by (simp add: real_div_sqrt)
  ultimately show  ?thesis using assms by auto
qed


subsection\<open>Main result: Inequality for the discrete version\<close>

theorem elementary_discrete_ineq_Wooley:
  fixes l::real and g::"nat \<Rightarrow> real"
  assumes "l>0" and "R = {r::nat. r>0}" and "\<forall> r \<in> R. g r = r+ (l/r)"
  shows "(INF r \<in> R. g r) \<le> sqrt(4*l+1)"

proof-

  text\<open>We will first show the inequality for a specific choice of $r_u \in R$. Then the assertion of 
the theorem will be simply shown by transitivity.\<close>

  define x::real where "x = sqrt(l+1/4)"
  with assms have "x>1/2"  
    by (smt (verit, best) real_sqrt_divide real_sqrt_four real_sqrt_less_iff real_sqrt_one)

  obtain r_u::nat where "r_u >x -1/2" and "r_u \<le> x+1/2" 
    using obtains_nat_in_interval_half \<open>x>1/2\<close> by (metis less_eq_real_def)
  have "r_u \<in> R" using assms \<open>1 / 2 < x\<close> \<open>x - 1 / 2 < real r_u\<close> by auto
  have ru_gt: "r_u > sqrt(l+1/4)-1/2" using \<open>r_u >x -1/2\<close> \<open>x =sqrt(l+1/4)\<close> by blast
  have ru_le: "r_u \<le> sqrt(l+1/4)+1/2" using \<open>r_u \<le> x +1/2\<close> \<open>x =sqrt(l+1/4)\<close> by blast

  text\<open>Proving the following auxiliary statement is the key part of the whole proof.\<close>

  have auxiliary: "\<bar>r_u - (l/r_u)\<bar> \<le> 1"
  proof-
    define \<delta>::real where "\<delta>  = r_u - sqrt(l+1/4)" 
    with assms ru_gt \<delta>_def ru_le 
    have \<delta>: "\<delta> > -1/2" "\<delta> \<le> 1/2"
      by auto

    have a: "\<bar>r_u - l/r_u\<bar> = \<bar> ((sqrt(l+1/4) + \<delta>)^2 -l)/(sqrt(l+1/4) + \<delta>)\<bar>" 
      using \<delta>_def
      by (smt (verit, ccfv_SIG) \<open>1 / 2 < x\<close> \<open>x - 1 / 2 < real r_u\<close> 
          add_divide_distrib nonzero_mult_div_cancel_right power2_eq_square)

    have b:"\<bar> ((sqrt(l+1/4) + \<delta>)^2 -l)/(sqrt(l+1/4) + \<delta>)\<bar> =  
\<bar>2* \<delta> +( ((1/4) - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))\<bar>" 
    proof-
      have "\<bar>((sqrt(l+1/4) + \<delta>)^2 -l)/(sqrt(l+1/4) + \<delta>) \<bar> = 
 \<bar>(1/4 + 2*(sqrt(l+1/4))* \<delta>+ \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta>) \<bar>"
        by (smt (verit, best) assms(1) divide_nonneg_nonneg power2_sum real_sqrt_pow2)
      also have "\<dots> =  \<bar> ( 2* \<delta>* (sqrt(l+1/4))+ 2* \<delta>\<^sup>2 + 1/4 -\<delta>\<^sup>2 )/(sqrt(l+1/4) + \<delta>)\<bar>"
        by (smt (verit) power2_sum)
      also have "\<dots> =  \<bar> ( 2* \<delta>* (sqrt(l+1/4)+ \<delta>) + 1/4 -\<delta>\<^sup>2 )/(sqrt(l+1/4) + \<delta>)\<bar>"
        by (smt (verit, ccfv_SIG) power2_diff power2_sum)
      also have "\<dots> =  \<bar> ( 2* \<delta>* (sqrt(l+1/4)+ \<delta>))/(sqrt(l+1/4) + \<delta>) 
+ ((1/4 -\<delta>\<^sup>2 )/(sqrt(l+1/4) + \<delta>)) \<bar> "
        by (metis add_diff_eq add_divide_distrib)
      also have  "\<dots> = \<bar> 2* \<delta> + ((1/4 -\<delta>\<^sup>2 )/(sqrt(l+1/4) + \<delta>)) \<bar>  "
        using \<open>\<delta> = real r_u - sqrt (l + 1 / 4)\<close> \<open>r_u \<in> R\<close> assms by force
      finally show ?thesis .
    qed

    show ?thesis
      text\<open>We distinguish the cases $\delta > 0$ and $\delta \leq 0$:\<close>
    proof (cases "\<delta> > 0")
      case True
      define t::real where "t = 1/2 - \<delta>"
      have c: "0 \<le> 2* \<delta> +(( 1/4 - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))"
      proof-
        have "\<delta>\<^sup>2 \<le> 1/4" using  \<delta>  \<open>\<delta> > 0\<close>
          by (metis less_eq_real_def plus_or_minus_sqrt real_sqrt_divide real_sqrt_four real_sqrt_le_iff real_sqrt_one real_sqrt_power) 
        then have "1/4 -\<delta>\<^sup>2 \<ge> 0" 
          by simp
        then show ?thesis using \<open>\<delta> > 0\<close> assms by simp
      qed

      have d: "2* \<delta> +( (1/4 - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> )) \<le> 1 -2*t + ((t-t\<^sup>2)/ (1-t))"
      proof-
        have "\<delta> = 1/2 - t" using  t_def by simp
        then have "2* \<delta> +( (1/4 - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> )) = 
                   2*(1/2 - t ) +( (1/4 - ( 1/2 - t)^2)/(sqrt(l+1/4) + 1/2 - t ))" 
          by simp
        also have  " \<dots> = 1 - 2*t + ( (1/4 - ( 1/4 -2*(1/2)* t+ t\<^sup>2))/(sqrt(l+1/4) + 1/2 - t ))"
          by (simp add: power2_diff power_divide)
        also have "\<dots> =  1 - 2*t + ((t- t\<^sup>2)/(sqrt(l+1/4) + 1/2 - t )) " by simp
        also have "\<dots> \<le> 1 -2*t + ((t-t\<^sup>2)/ (1-t))" 
        proof-
          have "sqrt(l+1/4) + 1/2 \<ge> 1"
            using \<open>1/2 < x\<close> x_def by linarith
          then have *: "sqrt(l+1/4) + 1/2 -t  \<ge> 1 -t" by simp
          have "1-t \<noteq> 0 "  using \<open>t = 1/2 - \<delta>\<close> \<open>\<delta> >0\<close> by linarith
          have "sqrt(l+1/4) + 1/2 -t \<noteq> 0" 
            using \<delta>_def \<open>t = 1/2 - \<delta>\<close>  \<open>\<delta> >0\<close> assms(1) by force
          then have "(1/(sqrt(l+1/4) + 1/2 - t ))\<le> (1/ (1-t))" 
            using * \<open>1-t \<noteq> 0 \<close> by (smt (verit) True \<open>\<delta> = 1/2 - t\<close> frac_le le_divide_eq_1_pos)
          have "t-t\<^sup>2 \<ge>0" using  \<open>\<delta> = 1/2 - t\<close> \<open>\<delta> >0\<close>
            by (smt (verit, best) \<open>\<delta> \<le> 1 / 2\<close> field_sum_of_halves le_add_same_cancel1 nat_1_add_1 
                power_decreasing_iff
                power_one_right real_sqrt_pow2_iff real_sqrt_zero zero_less_one_class.zero_le_one)
          then have "((t-t\<^sup>2) /(sqrt(l+1/4) + 1/2 - t ))\<le> ((t-t\<^sup>2)/ (1-t))" 
            by (smt (verit) "*" True \<open>t = 1/2 - \<delta>\<close> frac_le le_divide_eq_1_pos)
          then show ?thesis by force
        qed
        finally show ?thesis .
      qed

      have e: "1 -2*t + ((t-t\<^sup>2)/ (1-t)) \<le> 1"
      proof-
        have "1 -2*t + ((t-t\<^sup>2)/ (1-t)) =  1-2*t + ((1-t)*t /(1-t))" by algebra
        also have "\<dots> =  1- t"
          using c d by fastforce
        finally show ?thesis
          using \<delta> t_def by linarith 
      qed

      show ?thesis using a b c d e by linarith

    next
      case False
      define t::real where "t = 1/2 + \<delta>"
      then have "\<delta> = t-1/2"by simp
      have "\<delta> \<le> 0" using False by auto

      have "-( 2* \<delta> +( ((1/4) - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))) = 
- ( 2* (t-1/2) +( ((1/4) - (t-1/2)^2)/(sqrt(l+1/4) + t - 1/2 )))"
        using  \<open>\<delta> = t-1/2\<close>  by auto

      also have "\<dots> =-( 2*t- 1 +( (  t-t\<^sup>2)/(sqrt(l+1/4) + t - 1/2 )))" 
        by (simp add: power2_diff power_divide)

      finally have ***: "-( 2* \<delta> +( ((1/4) - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))) = 
-( 2*t- 1 +( (  t-t\<^sup>2)/(sqrt(l+1/4) + t - 1/2 )))" .

      have c:"-( 2* \<delta> +( ((1/4) - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))) \<le> 1 -2*t - ((t-t\<^sup>2)/ (sqrt(l+1/4)))"
      proof-
        have  c1: "sqrt(l+1/4) + t - 1/2 \<le> sqrt(l+1/4)"  
          using \<open>\<delta> = t - 1 / 2\<close> \<open>\<delta> \<le> 0\<close> by simp

        have "(sqrt(l+1/4) + t - 1/2) \<noteq> 0"  "sqrt(l+1/4) \<noteq> 0"
          using assms \<delta>_def \<open>\<delta> = t - 1/2\<close> \<open>r_u \<in> R\<close> by auto
        then
        have c2: "(t-t\<^sup>2)/(sqrt(l+1/4) + t - 1/2) \<ge>(t-t\<^sup>2)/ sqrt(l+1/4)"  
          using c1 assms 
          by (smt (verit, best) \<delta>_def ru_gt \<open>t = 1/2 + \<delta>\<close> 
              field_sum_of_halves frac_le le_add_same_cancel1 nat_1_add_1 of_nat_0_le_iff 
              power_decreasing_iff power_one_right zero_less_one_class.zero_le_one)

        have c3: "- (t-t\<^sup>2)/(sqrt(l+1/4) + t - 1/2) \<le> - (t-t\<^sup>2)/ sqrt(l+1/4)"  
          using c2  by linarith
        show ?thesis using *** c3 by linarith

      qed

      have d: "1 -2*t - ((t-t\<^sup>2)/ (sqrt(l+1/4))) \<le> 1"  
      proof-
        have *: "t >0" using \<open>\<delta> > -1/2\<close>  \<open>t = 1/2 + \<delta>\<close> by simp
        have **: "t \<le> 1" using  \<open>\<delta> \<le> 0\<close> \<open>t = 1/2 + \<delta>\<close> by simp
        show ?thesis using * **
          by (smt (verit) assms(1) divide_nonneg_nonneg mult_le_cancel_right2 power2_eq_square real_sqrt_ge_0_iff)
      qed

      have e: "-( 2* \<delta> +( ((1/4) - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))) \<ge> 1 -2*t - ((t-t\<^sup>2)/t)  "
      proof-
        have "-( 2* \<delta> +( ((1/4) - \<delta>\<^sup>2)/(sqrt(l+1/4) + \<delta> ))) 
= -( 2*t- 1 +((t-t\<^sup>2)/(sqrt(l+1/4) + t - 1/2)))"
          using *** by simp

        have "( (  t-t\<^sup>2)/(sqrt(l+1/4) + t - 1/2 )) \<le> (t-t\<^sup>2)/ t"
        proof-
          have \<dagger>: "(sqrt(l+1/4) + t - 1/2 ) \<ge>  t" using assms
            by (smt (verit, best) one_power2 power_divide real_sqrt_four real_sqrt_pow2 sqrt_le_D)
          moreover have "t >0" using \<open> \<delta> > -1/2\<close>  \<open>t = 1/2 + \<delta>\<close> by simp
          ultimately have "(sqrt(l+1/4) + t - 1/2 ) >0" 
            by auto
          show ?thesis using \<dagger> \<open>(sqrt(l+1/4) + t - 1/2 ) >0\<close> 
              \<open>0 < t\<close> 
            by (smt (verit, best) \<open>\<delta> \<le> 0\<close> \<open>t = 1/2 + \<delta>\<close> 
                frac_le le_add_same_cancel1 le_divide_eq_1_pos nat_1_add_1 power_decreasing_iff 
                power_one_right zero_less_one_class.zero_le_one)
        qed
        with *** show ?thesis by linarith

      qed
      have f: "1 -2*t - ((t-t\<^sup>2)/t) \<ge> -1/2" 
      proof-
        have "t >0" using \<open> \<delta> > -1/2\<close>  \<open>t = 1/2 + \<delta>\<close> by simp
        then have "1 -2*t - ((t-t\<^sup>2)/t) = 1-2*t -(1 -t)" 
          by (metis divide_diff_eq_iff less_irrefl one_eq_divide_iff power2_eq_square)
        also have "\<dots> = -t" by auto
        finally show ?thesis 
          using \<open>\<delta> \<le> 0\<close> \<open>t = 1/2 + \<delta>\<close>  by linarith
      qed
      show ?thesis using a b c d e f by linarith
    qed
  qed

  text\<open>The next step is to show that by the statement named "auxiliary" shown above, we can 
directly show the desired inequality for the specific $r_u \in R$:\<close>

  have "(r_u - l/r_u)^2 \<le>1" 
    using auxiliary abs_square_le_1 by blast
  then have "(r_u^2 - 2*r_u* (l/r_u) + l^2/r_u^2 \<le>1)" 
    using power2_diff power_divide assms
    by (smt (verit) mult_2 of_nat_add of_nat_eq_of_nat_power_cancel_iff)
  then have "r_u^2 - 2*l + l^2/r_u^2 \<le>1" using assms \<open>r_u \<in> R\<close> by force
  then have "r_u^2 + 2*l + l^2/r_u^2 \<le> ( 4*l+1)" by argo
  then have "r_u^2 + 2*r_u*(l/r_u) + l^2/r_u^2 \<le> ( 4*l+1)" using assms by simp
  then have "(r_u+ (l/r_u))^2 \<le> ( 4*l+1)"
    by (smt (verit, best) mult_2 of_nat_add of_nat_power_eq_of_nat_cancel_iff power2_sum 
        power_divide)
  then have "(r_u+ (l/r_u)) \<le> sqrt(4*l+1)" using real_le_rsqrt by blast
  moreover
  text\<open>The following shows that it is enough that we showed the inequality for the specific 
$r_u \in R$, as the statement of the theorem will then simply hold by transitivity.\<close>

  have "(INF r \<in> R. g r) \<le> g r_u " 
  proof-
    have "bdd_below (g ` R)" unfolding bdd_below_def 
      using  assms image_iff 
      by (metis add_increasing assms(1) divide_nonneg_nonneg image_iff less_eq_real_def
          of_nat_0_le_iff)
    show ?thesis
      by (simp add: \<open>bdd_below (g ` R)\<close> \<open>r_u \<in> R\<close> cINF_lower)
  qed
  ultimately show ?thesis using assms \<open>r_u \<in> R\<close> by force
qed

subsection\<open>Special case: Equality for the discrete version\<close>

text\<open>We will now show a special case of the main result where equality holds instead of inequality.\<close> 

text\<open>We will need to make use of the following technical lemma, which will be used so as to 
guarantee that there exists a $p \in R$ for which the INF of $g(r)$ equals to $g(p)$. To this end, 
we will show that here the infimum INF can be identified with the minimum Min by restricting to a 
finite set. As the operator Min in Isabelle is used for finite sets and $R$ is infinite, we
used INF in the original formulation, however here Min and INF can be identified.\<close>

text\<open>The following technical lemma is by Larry Paulson:\<close>

lemma restrict_to_min:
  fixes l::real and g::"nat \<Rightarrow> real"
  assumes "l>0" and R_def: "R={r::nat. r>0}" and g_def: "\<forall> r. g r = r + (l/r)"
  obtains F where "finite F" "F \<subseteq> R" "(INF r \<in> R. g r) = Min (g ` F)" "F \<noteq> {}"

proof -
  have ge0: "g r \<ge> 0" for r
    using \<open>l>0\<close> R_def g_def  by (auto simp: g_def) 
  then have bdd: "bdd_below (g ` R)"
    by (auto simp add: g_def R_def bdd_below_def)
  have "\<forall>\<^sub>F n in sequentially. g 1 < g n"
    by (simp add: g_def) real_asymp
  then obtain N where "N>0" and N: "\<And>r. r\<ge>N \<Longrightarrow> g 1 < g r"
    by (metis Suc_leD eventually_sequentially less_Suc_eq_0_disj) 
  define F where "F = R \<inter> {..N}"
  have F: "finite F" "F \<subseteq> R"
    by (auto simp add: F_def)
  have "F \<noteq> {}"
    using F_def R_def \<open>0 < N\<close> by blast
  have "(INF r \<in> R. g r) = (INF r \<in> F. g r)"
  proof (intro order.antisym cInf_mono bdd)
    show "bdd_below (g ` F)"
      by (meson ge0 bdd_belowI2)
  next
    fix b
    assume "b \<in> g ` R"
    then show "\<exists>a\<in>g ` F. a \<le> b"
      unfolding image_iff F_def R_def Bex_def
      by (metis N linorder_not_less IntI atMost_iff mem_Collect_eq nle_le zero_less_one)
  qed (use \<open>F\<subseteq>R\<close> \<open>0 < N\<close> in \<open>auto simp: R_def F_def\<close>)
  also have "\<dots> = Min (g ` F)"
    using \<open>F \<noteq> {}\<close> by (simp add: \<open>finite F\<close> cInf_eq_Min)
  finally have "(INF r \<in> R. g r) = Min (g ` F)" .
  with F show thesis
    using that \<open>F \<noteq> {}\<close> by blast
qed

text\<open>We will make use of the following calculation, which is convenient to formulate separately as
a lemma.\<close>

lemma elementary_discrete_ineq_Wooley_quadratic_eq_sol:
  fixes l::real and g::"nat \<Rightarrow> real" 
  assumes "l>0" and "\<forall> r. g r =r+ (l/r)" and "g r = sqrt(4*l+1)" 
  shows "(r = 1/2 + (1/2)* sqrt( 4*l +1)) \<or> (r = - 1/2 + (1/2)* sqrt(4*l +1))"
proof-
  have eq0: "r^2 - r*(sqrt( 4*l+1 )) + l = 0"  
  proof-
    have "r*( r + l/r) = r*(sqrt(4*l+1))" using assms by simp
    then have  "r^2 + r*(l/r) = r*(sqrt(4*l+1))"  
      by (simp add: distrib_left power2_eq_square)
    then show ?thesis
      by (smt (verit, ccfv_threshold) assms divide_eq_eq mult.commute real_sqrt_gt_1_iff)
  qed

  text\<open>Solving the above quadratic equation gives the following two roots:\<close>

  have roots:"(r = 1/2 + (1/2)*sqrt( 4*l +1))\<or>(r = - 1/2 + (1/2)*sqrt(4*l+1))"
  proof-
    define a::real where "a = 1"
    define b::real where "b = - sqrt(4*l+1)"
    define c::real where "c = l"
    have "a*r^2 + b* r + c =0" using eq0 by (simp add: mult.commute a_def b_def c_def)
    then have A: "(r = (-b + sqrt( discrim a  b c))/ 2*a) \<or> (r = (-b -sqrt( discrim a  b c))/ 2*a)"
      using discriminant_iff[of a r] a_def by simp
    have "discrim a b c = b^2 -4*a*c" 
      using discrim_def by simp
    then have B: "(r = (-b + sqrt(b^2 -4*a*c))/ 2*a) \<or> (r = (-b -sqrt(b^2 -4*a*c))/ 2*a)"
      using A by auto
    then have C: "(r = (-b + sqrt(b^2 -4*c))/ 2) \<or> (r = (-b -sqrt(b^2 -4*c))/ 2)"
      using a_def by simp
    have "b^2 -4*c = 1" using b_def c_def assms(1) by auto
    then have "(r = (-b + 1)/ 2) \<or> (r = (-b - 1)/ 2)"
      using C by auto
    then show ?thesis using b_def by auto
  qed
  show ?thesis using roots by simp
qed


text\<open>The special case with equality involves a double implication (iff), and we start by showing 
one direction.\<close>

theorem elementary_discrete_ineq_Wooley_special_case_1:
  fixes l::real and g::"nat \<Rightarrow> real" assumes "l>0" and "R={r::nat. r>0}" and "\<forall> r. g r = r + (l/r)"
    and "(INF r \<in> R. g r) = sqrt(4*l+1)"
  shows "\<exists> m::nat. l =m*(m-1)"

proof-
  have "\<exists> p \<in> R. (INF r \<in> R. g r) = g p"
  proof-
    obtain F where *:\<open>(INF r \<in> R. g r) = Min (g ` F)\<close> and \<open>finite F\<close> and \<open>F \<subseteq> R\<close> \<open>F \<noteq> {}\<close>
      using assms restrict_to_min by metis 
    then obtain p::nat where "  Min (g ` F)  = g p " "p \<in> R"
      by (smt (verit) Min_in finite_imageI image_iff image_is_empty subsetD)
    with * show ?thesis by metis
  qed
  with assms
  obtain r_u::nat where "g r_u = sqrt(4*l+1)" and "r_u \<in> R" 
    by metis
  then have ru: "(r_u + (l/r_u)) = sqrt( 4*l+1 )" 
    using assms by auto

  have "(r_u =  1/2 + (1/2)* sqrt( 4*l +1)) \<Longrightarrow> (l = r_u^2 - r_u)" 
  proof-
    assume "r_u =  1/2 + (1/2)* (sqrt( 4*l +1))"
    then have "2* r_u = 1 + sqrt( 4*l +1)" by simp
    then have "(2* real(r_u) -1)^2 = ( 4*l +1)" using assms by auto
    then have "(2*real(r_u))^2 -2*(2*real( r_u)) +1 = ( 4*l +1)" 
      by (simp add: power2_diff)
    then have "4*real(r_u)^2-4*(r_u) = 4*l" by fastforce
    then show "(l = r_u^2 - r_u )"  
      by (simp add: of_nat_diff power2_eq_square)
  qed
  moreover
  have "(r_u = - 1/2 + (1/2)* sqrt( 4*l +1))\<Longrightarrow> (l =r_u^2 + r_u)"
  proof-
    assume "r_u = - 1/2 + (1/2)* sqrt(4*l +1)"    
    then have "2 * r_u +1 =  sqrt(4*l+1)" by simp
    then have "(2*r_u +1)^2 = (4*l+1)" using assms by auto
    then have "4*(r_u)^2 +4*r_u +1 = 4*l+1" 
      by (simp add: power2_eq_square)
    then show " (l =r_u^2 + r_u )"
      by (simp add: of_nat_diff power2_eq_square)
  qed
  moreover
  have "(r_u =  1/2 + (1/2)* sqrt( 4*l +1)) \<or> (r_u = - 1/2 + (1/2)* sqrt(4*l +1))"
    using assms ru elementary_discrete_ineq_Wooley_quadratic_eq_sol
      assms by auto
  ultimately have "(l =r_u^2 + r_u) \<or> (l = r_u^2 - r_u)" 
    by blast
  then show ?thesis 
    by (metis add_implies_diff distrib_left mult.commute mult.right_neutral power2_eq_square right_diff_distrib')

  text\<open>(Interestingly, the above use of metis finished the proof in a simple step guaranteeing the 
existence of a witness with the desired property).\<close>

qed


text\<open>Now we show the other direction.\<close>

theorem elementary_discrete_ineq_Wooley_special_case_2:
  fixes l::real and g::"nat \<Rightarrow> real"
  assumes "l>0"  and  "R={r::nat. r>0}" and "\<forall> r. g r =r+ (l/r)" and "\<exists> m::nat. l =m*(m-1)"
  shows "(INF r \<in> R. g r) = sqrt(4*l+1)"

proof-    

  obtain r_u::nat where "(l =r_u^2 + r_u)" using assms 
    by (metis add.commute add_cancel_left_right mult_eq_if power2_eq_square)
  then have "sqrt( 4*l +1)= sqrt(4*r_u^2 +4* r_u +1)" by simp
  moreover have "4*r_u^2 +4* r_u +1 =(2*r_u +1)^2"
    by (simp add: Groups.mult_ac(2) distrib_left power2_eq_square)
  ultimately have 4: "sqrt( 4*l +1)= sqrt((2*r_u +1)^2)" by metis
  then have ru: "r_u  = -1/2 + 1/2*sqrt( 4*l +1)" by (simp add: add_divide_distrib)

  text\<open>To prove the conclusion of the theorem, we will follow a proof by contradiction.\<close>

  show ?thesis
  proof (rule ccontr)
    assume "Inf (g ` R) \<noteq> sqrt (4 * l + 1)"
    then have inf: "(INF r \<in> R. g r) < sqrt(4*l+1)"
      using assms less_eq_real_def elementary_discrete_ineq_Wooley by blast

    have "\<exists> p \<in> R. (INF r \<in> R. g r) = g p" 
    proof-
      obtain F where *:\<open>(INF r \<in> R. g r) = Min (g ` F)\<close> and \<open>finite F\<close> \<open>F \<subseteq> R\<close> \<open>F \<noteq> {}\<close>
        using assms restrict_to_min by metis 
      then obtain p::nat where "Min (g ` F)  = g p " "p \<in> R"
        by (meson Min_in finite_imageI imageE image_is_empty subsetD)
      with * show ?thesis by metis
    qed

    obtain p::nat where "p \<in> R" and "(INF r \<in> R. g r) = g p" using assms 
        \<open>\<exists> p \<in> R.  (INF r \<in> R. g r) = g p\<close> by blast
    then have "(p+ l/p < sqrt( 4*l+1))"
      using inf assms(3) by auto 

    have "p*(p+ l/p) < p*(sqrt( 4*l+1))" 
      using \<open>p \<in> R\<close> \<open>(p+ l/p < sqrt( 4*l+1))\<close> assms by simp
    then have  "p^2 - p*(sqrt( 4*l+1))+ l<0"  
      by (smt (verit) \<open>p \<in> R\<close> assms(2) distrib_left mem_Collect_eq nonzero_mult_div_cancel_left 
          of_nat_0_less_iff of_nat_mult power2_eq_square times_divide_eq_right)

    text\<open>We now need to find the possible values of this hypothetical $p \in R$, i.e. the roots of the 
above quadratic inequality. (These will be in-between the roots of the corresponding quadratic 
equation which were given in lemma @{thm elementary_discrete_ineq_Wooley_quadratic_eq_sol}). 
Here we show that the roots of the quadratic inequality lie in the following interval via a direct 
calculation:\<close>

    have p: "(p < (sqrt(4*l+1) + 1) / 2) \<and> (p >(sqrt(4*l+1) - 1) / 2)"
    proof-
      have "p^2 - p*(sqrt(4*l+1))+ l +1/4 < 1/4" 
        using \<open>p^2 - p*(sqrt(4*l+1))+ l<0\<close> by simp
      moreover
      have "- (2*(p* sqrt(4*l +1))/2) + (4* l +1)/4 = - p*(sqrt(4*l+1))+ l +1/4"
        by force
      ultimately have ***: "p^2 - (2*(p* sqrt(4*l +1))/2) + (4* l +1)/4  <1/4" 
        by linarith
      have ****: "(p -(sqrt(4*l +1))/2)^2 = p^2 -2 * p* (sqrt(4*l +1))/2+ ( (sqrt(4*l +1))/2)^2" 
        by (simp add: power2_diff)
      then have "p^2 -2 * p* (sqrt(4*l+1))/2+ ((sqrt(4*l +1))/2)^2 = p^2 -2 * p* (sqrt(4*l +1))/2+ (4*l +1)/4"
        by (smt (verit) assms(1) power_divide real_sqrt_four real_sqrt_pow2)
      then have "(p -(sqrt(4*l +1))/2)^2 <1/4" using *** **** by linarith
      then have "\<bar>(p -(sqrt(4*l +1))/2) \<bar> <1/2" 
        by (metis real_sqrt_abs real_sqrt_divide real_sqrt_four real_sqrt_less_mono real_sqrt_one)
      then have "((p -(sqrt(4*l +1))/2) ) <1/2"  "((p -(sqrt(4*l +1))/2) ) > -1/2" by linarith+
      then show ?thesis 
        by force
    qed

    text\<open>So $p$ lies in an interval of length strictly less than 1 between two positive integers, but 
this means that $p$ cannot be a positive integer, which yields the desired contradiction, thus 
completing the proof:\<close>

    obtain A::nat where A: "real A = - 1/2 + (1/2)* sqrt(4*l +1)"
      using ru by blast
    then show False
      using "4" p by fastforce
  qed
qed



text\<open>Finally, for convenience and completeness, we state the special case where equality holds 
formulated with the double implication and moreover including the values for which the INF (i.e.
minimum here as we have seen) is attained as previously calculated.\<close>

theorem elementary_discrete_ineq_Wooley_special_case_iff:
  fixes l::real and g::"nat \<Rightarrow> real" 
  assumes "l>0" and "R={r::nat. r>0}" and "\<forall> r. g r = r+ (l/r)"
  shows "((INF r \<in> R. g r) = sqrt(4*l+1)) \<longleftrightarrow> (\<exists> m::nat. l =m*(m-1))" 
    and 
    "g p =sqrt(4*l+1) \<longrightarrow> (p = 1/2 + (1/2)* sqrt( 4*l +1)) \<or> (p = -1/2 + (1/2)* sqrt(4*l +1))"
  using assms elementary_discrete_ineq_Wooley_special_case_1
    elementary_discrete_ineq_Wooley_special_case_2 
  apply blast
  using assms(1) assms(3) elementary_discrete_ineq_Wooley_quadratic_eq_sol restrict_to_min
  by auto

end
