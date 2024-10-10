section \<open>\<open>With_Type_Example\<close> -- Some contrieved simple examples\<close>

theory With_Type_Example
  imports With_Type "HOL-Computational_Algebra.Factorial_Ring" Mersenne_Primes.Lucas_Lehmer_Code
begin

unbundle lifting_syntax and no m_inv_syntax


subsection \<open>Semigroups (class with one parameter)\<close>


definition \<open>WITH_TYPE_CLASS_semigroup_add S plus \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. plus (plus a b) c = plus a (plus b c))\<close>
  for S :: \<open>'rep set\<close> and plus :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close>
definition \<open>WITH_TYPE_REL_semigroup_add r = (r ===> r ===> r)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

lemma with_type_wellformed_semigroup_add[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_semigroup_add S WITH_TYPE_REL_semigroup_add\<close>
  by (simp add: with_type_wellformed_def WITH_TYPE_CLASS_semigroup_add_def WITH_TYPE_REL_semigroup_add_def
      fun.Domainp_rel Domainp_pred_fun_eq bi_unique_alt_def)

lemma with_type_transfer_semigroup_add:
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_semigroup_add r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
proof -
  define f where \<open>f y = (SOME x. r x y)\<close> for y
  have rf: \<open>r x y \<longleftrightarrow> x = f y\<close> for x y
    unfolding f_def
    apply (rule someI2_ex)
    using assms
    by (auto intro!: simp: right_total_def bi_unique_def)
  have inj: \<open>inj f\<close>
    using \<open>bi_unique r\<close>
    by (auto intro!: injI simp: bi_unique_def rf)
  have aux1: \<open>\<forall>ya yb. x (f ya) (f yb) = f (y ya yb) \<Longrightarrow>
       \<forall>a. (\<exists>y. a = f y) \<longrightarrow> (\<forall>b. (\<exists>y. b = f y) \<longrightarrow> (\<forall>c. (\<exists>y. c = f y) \<longrightarrow> x (x a b) c = x a (x b c))) \<Longrightarrow> 
       y (y a b) c = y a (y b c)\<close> for x y a b c
    by (metis inj injD)
  show ?thesis
    unfolding WITH_TYPE_REL_semigroup_add_def rel_fun_def
    unfolding WITH_TYPE_CLASS_semigroup_add_def Domainp_iff rf
    by (auto intro!: simp: class.semigroup_add_def aux1)
qed

setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>semigroup_add\<close>,
  param_names = ["plus"],
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_semigroup_add\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_semigroup_add\<close>,
  with_type_wellformed = @{thm with_type_wellformed_semigroup_add},
  transfer = SOME @{thm with_type_transfer_semigroup_add},
  rep_rel_itself = NONE
}
\<close>

subsubsection \<open>Example\<close>

definition carrier :: \<open>int set\<close> where \<open>carrier = {0,1,2}\<close>
definition carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where \<open>carrier_plus i j = (i + j) mod 3\<close>

lemma carrier_nonempty[iff]: \<open>carrier \<noteq> {}\<close>
  by (simp add: carrier_def)

lemma carrier_semigroup[with_type_intros]: \<open>WITH_TYPE_CLASS_semigroup_add carrier carrier_plus\<close>
  by (auto simp: WITH_TYPE_CLASS_semigroup_add_def
        carrier_def carrier_plus_def)

text \<open>This proof uses both properties of the specific carrier (existence of two different elements)
  and of semigroups in general (associativity)\<close>
lemma example_semigroup:
  shows \<open>let 't::semigroup_add = carrier with carrier_plus in \<forall>x y.
    (plus_t x y = plus_t y x \<and> plus_t x (plus_t x x) = plus_t (plus_t x x) x)\<close>
proof (with_type_intro)
  show \<open>carrier \<noteq> {}\<close> by simp
  fix Rep :: \<open>'t \<Rightarrow> int\<close> and T and plus_t
  assume \<open>bij_betw Rep UNIV carrier\<close>
  then interpret type_definition Rep \<open>inv Rep\<close> carrier
    using type_definition_bij_betw_iff by blast
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    by (simp add: Rep_inject bi_unique_def r_def)
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume \<open>WITH_TYPE_REL_semigroup_add (\<lambda>x y. x = Rep y) carrier_plus plus_t\<close>
  then have transfer_carrier[transfer_rule]: \<open>(r ===> r ===> r) carrier_plus plus_t\<close>
    by (simp add: r_def WITH_TYPE_REL_semigroup_add_def)
  have [transfer_rule]: \<open>((r ===> r ===> r) ===> (\<longleftrightarrow>)) (WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
  proof (intro rel_funI)
    fix x y
    assume xy[transfer_rule]: \<open>(r ===> r ===> r) x y\<close>
    have aux1: \<open>\<forall>a. Domainp r a \<longrightarrow> (\<forall>b. Domainp r b \<longrightarrow> (\<forall>c. Domainp r c \<longrightarrow> x (x a b) c = x a (x b c))) \<Longrightarrow>
       r a b \<Longrightarrow> r ba bb \<Longrightarrow> r c bc \<Longrightarrow> x (x a ba) c = x a (x ba c)\<close> for a b ba bb c bc
      by blast
    have aux2: \<open>r a b \<Longrightarrow> r ba bb \<Longrightarrow> Domainp r (x a ba)\<close> for a b ba bb
      by (metis DomainPI rel_funD xy)
    show \<open>WITH_TYPE_CLASS_semigroup_add (Collect (Domainp r)) x \<longleftrightarrow> class.semigroup_add y\<close>
      unfolding class.semigroup_add_def
      apply transfer
      by (auto intro!: aux1 aux2 simp: WITH_TYPE_CLASS_semigroup_add_def)
  qed
  have dom_r: \<open>Collect (Domainp r) = carrier\<close>
    by (auto elim!: Rep_cases simp: Rep r_def Domainp_iff)
  interpret semigroup_add plus_t
    apply transfer
    using carrier_semigroup dom_r by auto

  have 1: \<open>plus_t x y = plus_t y x\<close> for x y
    apply transfer
    apply (simp add: carrier_plus_def)
    by presburger

  have 2: \<open>plus_t x (plus_t x x) = plus_t (plus_t x x) x\<close> for x
    by (simp add: add_assoc)

  from 1 2
  show \<open>\<forall>x y. plus_t x y = plus_t y x \<and> plus_t x (plus_t x x) = plus_t (plus_t x x) x\<close>
    by simp
qed

text \<open>Some hypothetical lemma where we use the existence of a commutative semigroup to 
  derive that 2147483647 is prime. (The lemma is true since 2147483647 is prime,
  but otherwise this is completely fictional.)\<close>
lemma artificial_lemma: \<open>(\<exists>p (x::_::semigroup_add) y. p x y = p y x) \<Longrightarrow> prime (2147483647 :: nat)\<close>
proof - \<comment> \<open>This proof can be ignored. We just didn't want to have a "sorry" in the theory file\<close>
  have "prime (2 ^ 31 - 1 :: nat)"
    by (subst lucas_lehmer_correct') eval
  also have \<open>\<dots> = 2147483647\<close>
    by eval
  finally show \<open>prime (2147483647 :: nat)\<close>
    by -
qed

lemma prime_2147483647: \<open>prime (2147483647 :: nat)\<close>
proof -
  from example_semigroup
  have \<open>let 't::semigroup_add = carrier with carrier_plus in
        prime (2147483647 :: nat)\<close>
  proof with_type_mp
    with_type_case
    show \<open>prime (2147483647 :: nat)\<close>
      apply (rule artificial_lemma)
      using with_type_mp.premise by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed


subsection \<open>Abelian groups (class with several parameters)\<close>

text \<open>Here we do exactly the same as for semigroups, except that now we use an abelian group.
  This shows the additional subtleties that arise when a class has more than one parameter.\<close>

notation rel_prod (infixr \<open>***\<close> 80)

definition \<open>WITH_TYPE_CLASS_ab_group_add S = (\<lambda>(plus,zero,minus,uminus). zero \<in> S
 \<and> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b \<in> S) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. minus a b \<in> S) \<and> (\<forall>a\<in>S. uminus a \<in> S)
 \<and> (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. plus (plus a b) c= plus a (plus b c)) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. plus a b = plus b a)
 \<and> (\<forall>a\<in>S. plus zero a = a) \<and> (\<forall>a\<in>S. plus (uminus a) a = zero) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. minus a b = plus a (uminus b)))\<close>
  for S :: \<open>'rep set\<close>
definition \<open>WITH_TYPE_REL_ab_group_add r = (r ===> r ===> r) *** r *** (r ===> r ===> r) *** (r ===> r)\<close>
  for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep \<Rightarrow> 'rep \<Rightarrow> 'rep\<close> and abs_ops :: \<open>'abs \<Rightarrow> 'abs \<Rightarrow> 'abs\<close>

lemma with_type_wellformed_ab_group_add[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_ab_group_add S WITH_TYPE_REL_ab_group_add\<close>
  by (simp add: with_type_wellformed_def WITH_TYPE_CLASS_ab_group_add_def WITH_TYPE_REL_ab_group_add_def
      fun.Domainp_rel Domainp_pred_fun_eq bi_unique_alt_def prod.Domainp_rel DomainPI)

lemma with_type_transfer_ab_group_add:
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(WITH_TYPE_REL_ab_group_add r ===> (\<longleftrightarrow>))
         (WITH_TYPE_CLASS_ab_group_add (Collect (Domainp r))) (\<lambda>(p,z,m,u). class.ab_group_add p z m u)\<close>
proof -
  define f where \<open>f y = (SOME x. r x y)\<close> for y
  have rf: \<open>r x y \<longleftrightarrow> x = f y\<close> for x y
    unfolding f_def
    apply (rule someI2_ex)
    using assms
    by (auto intro!: simp: right_total_def bi_unique_def)
  have inj: \<open>inj f\<close>
    using \<open>bi_unique r\<close>
    by (auto intro!: injI simp: bi_unique_def rf)
  show ?thesis
    unfolding WITH_TYPE_REL_ab_group_add_def rel_fun_def
    unfolding WITH_TYPE_CLASS_ab_group_add_def
    unfolding Domainp_iff rf
    using inj
    apply (simp add: class.ab_group_add_def class.comm_monoid_add_def
        class.ab_semigroup_add_def class.semigroup_add_def class.ab_semigroup_add_axioms_def
        class.comm_monoid_add_axioms_def class.ab_group_add_axioms_def inj_def)
    apply safe
    by metis+
qed


setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>ab_group_add\<close>,
  param_names = ["plus", "zero", "minus", "uminus"],
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_ab_group_add\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_ab_group_add\<close>,
  with_type_wellformed = @{thm with_type_wellformed_ab_group_add},
  transfer = SOME @{thm with_type_transfer_ab_group_add},
  rep_rel_itself = NONE
}
\<close>

subsubsection \<open>Example\<close>

definition carrier_group where \<open>carrier_group = (carrier_plus, 0::int, (\<lambda> i j. (i - j) mod 3), (\<lambda>i. (- i) mod 3))\<close>

lemma carrier_ab_group_add[with_type_intros]: \<open>WITH_TYPE_CLASS_ab_group_add carrier carrier_group\<close>
  by (auto simp: WITH_TYPE_CLASS_ab_group_add_def carrier_plus_def
        carrier_def carrier_group_def)

declare [[show_sorts=false]]
lemma example_ab_group:
  shows \<open>let 't::ab_group_add = carrier with carrier_group in \<forall>x y.
    (plus_t x y = plus_t y x \<and> plus_t x (plus_t x x) = plus_t (plus_t x x) x)\<close>
proof with_type_intro
  show \<open>carrier \<noteq> {}\<close> by simp
  fix Rep :: \<open>'t \<Rightarrow> int\<close> and t_ops
  assume wt: \<open>WITH_TYPE_REL_ab_group_add (\<lambda>x y. x = Rep y) carrier_group t_ops\<close>
  define plus zero minus uminus where \<open>plus = fst t_ops\<close>
    and \<open>zero = fst (snd t_ops)\<close>
    and \<open>minus = fst (snd (snd t_ops))\<close>
    and \<open>uminus = snd (snd (snd t_ops))\<close>

  assume \<open>bij_betw Rep UNIV carrier\<close>
  then interpret type_definition Rep \<open>inv Rep\<close> carrier
    by (simp add: type_definition_bij_betw_iff)

  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    by (simp add: Rep_inject bi_unique_def r_def)
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  from wt have transfer_carrier[transfer_rule]: \<open>((r ===> r ===> r) *** r *** (r ===> r ===> r) *** (r ===> r)) carrier_group t_ops\<close>
    by (simp add: r_def WITH_TYPE_REL_ab_group_add_def)
  have transfer_plus[transfer_rule]: \<open>(r ===> r ===> r) carrier_plus plus\<close>
    apply (subst asm_rl[of \<open>carrier_plus = fst (carrier_group)\<close>])
     apply (simp add: carrier_group_def)
    unfolding plus_def
    by transfer_prover
  have dom_r: \<open>Collect (Domainp r) = carrier\<close>
    by (auto elim!: Rep_cases simp: Rep r_def Domainp_iff)
  
  from with_type_transfer_ab_group_add[OF \<open>bi_unique r\<close> \<open>right_total r\<close>]
  have [transfer_rule]: \<open>((r ===> r ===> r) ===> r ===> (r ===> r ===> r) ===> (r ===> r) ===> (\<longleftrightarrow>))
                         (\<lambda>p z m u. WITH_TYPE_CLASS_ab_group_add carrier (p,z,m,u)) class.ab_group_add\<close>
    unfolding dom_r WITH_TYPE_REL_ab_group_add_def
    by (auto intro!: simp: rel_fun_def)

  interpret ab_group_add plus zero minus uminus
    unfolding zero_def plus_def minus_def uminus_def
    apply transfer
    using carrier_ab_group_add dom_r
    by (auto intro!: simp: Let_def case_prod_beta)

  have 1: \<open>plus x y = plus y x\<close> for x y
    \<comment> \<open>We could prove this simply with \<open>by (simp add: add_commute)\<close>, but we use the approach of
      going to the concrete type for demonstration.\<close>
    apply transfer
    apply (simp add: carrier_plus_def)
    by presburger

  have 2: \<open>plus x (plus x x) = plus (plus x x) x\<close> for x
    by (simp add: add_assoc)

  from 1 2
  show \<open>\<forall>x y. plus x y = plus y x \<and> plus x (plus x x) = plus (plus x x) x\<close>
    by (simp add: plus_def case_prod_beta)
qed

lemma artificial_lemma': \<open>(\<exists>p (x::_::group_add) y. p x y = p y x) \<Longrightarrow> prime (2305843009213693951 :: nat)\<close>
proof - \<comment> \<open>This proof can be ignored. We just didn't want to have a "sorry" in the theory file\<close>
  have "prime (2 ^ 61 - 1 :: nat)"
    by (subst lucas_lehmer_correct') eval
  also have \<open>\<dots> = 2305843009213693951\<close>
    by eval
  finally show \<open>prime (2305843009213693951 :: nat)\<close>
    by -
qed

lemma prime_2305843009213693951: \<open>prime (2305843009213693951 :: nat)\<close>
proof -
  from example_ab_group
  have \<open>let 't::ab_group_add = carrier with carrier_group in prime (2305843009213693951 :: nat)\<close>
  proof with_type_mp
    with_type_case
    show \<open>prime (2305843009213693951 :: nat)\<close>
      apply (rule artificial_lemma')
      using with_type_mp.premise by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed


end

