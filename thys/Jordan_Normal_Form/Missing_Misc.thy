(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Material missing in the distribution\<close>

text \<open>This theory provides some definitions and lemmas which we did not find in the 
  Isabelle distribution.\<close>

theory Missing_Misc
  imports
    "HOL-Library.FuncSet"
    "HOL-Combinatorics.Permutations"
begin

declare finite_image_iff [simp]

lemma inj_on_finite:
  \<open>finite (f ` A) \<longleftrightarrow> finite A\<close> if \<open>inj_on f A\<close>
  using that by (fact finite_image_iff)

text \<open>The following lemma is slightly generalized from Determinants.thy in HMA.\<close>

lemma finite_bounded_functions:
  assumes fS: "finite S"
  shows "finite T \<Longrightarrow> finite {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
proof (induct T rule: finite_induct)
  case empty
  have th: "{f. \<forall>i. f i = i} = {id}"
    by auto
  show ?case
    by (auto simp add: th)
next
  case (insert a T)
  let ?f = "\<lambda>(y,g) i. if i = a then y else g i"
  let ?S = "?f ` (S \<times> {f. (\<forall>i\<in>T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)})"
  have "?S = {f. (\<forall>i\<in> insert a T. f i \<in> S) \<and> (\<forall>i. i \<notin> insert a T \<longrightarrow> f i = i)}"
    apply (auto simp add: image_iff)
    apply (rule_tac x="x a" in bexI)
    apply (rule_tac x = "\<lambda>i. if i = a then i else x i" in exI)
    apply (insert insert, auto)
    done
  with finite_imageI[OF finite_cartesian_product[OF fS insert.hyps(3)], of ?f]
  show ?case
    by metis
qed

lemma finite_bounded_functions':
  assumes fS: "finite S"
  shows "finite T \<Longrightarrow> finite {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = j)}"
proof (induct T rule: finite_induct)
  case empty
  have th: "{f. \<forall>i. f i = j} = {(\<lambda> x. j)}"
    by auto
  show ?case
    by (auto simp add: th)
next
  case (insert a T)
  let ?f = "\<lambda>(y,g) i. if i = a then y else g i"
  let ?S = "?f ` (S \<times> {f. (\<forall>i\<in>T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = j)})"
  have "?S = {f. (\<forall>i\<in> insert a T. f i \<in> S) \<and> (\<forall>i. i \<notin> insert a T \<longrightarrow> f i = j)}"
    apply (auto simp add: image_iff)
    apply (rule_tac x="x a" in bexI)
    apply (rule_tac x = "\<lambda>i. if i = a then j else x i" in exI)
    apply (insert insert, auto)
    done
  with finite_imageI[OF finite_cartesian_product[OF fS insert.hyps(3)], of ?f]
  show ?case
    by metis
qed

lemma permutes_less [simp]:
  assumes p: "p permutes {0..<(n :: nat)}"
  shows
    "i < n \<Longrightarrow> p i < n"
    "i < n \<Longrightarrow> inv p i < n" 
    "p (inv p i) = i"
    "inv p (p i) = i"
  using assms
  by (simp_all add: permutes_inverses permutes_nat_less permutes_nat_inv_less)

lemma permutes_prod:
  assumes p: "p permutes S"
  shows "(\<Prod>s\<in>S. f (p s) s) = (\<Prod>s\<in>S. f s (inv p s))"
    (is "?l = ?r")
  using assms by (fact prod.permutes_inv)

lemma permutes_sum:
  assumes p: "p permutes S"
  shows "(\<Sum>s\<in>S. f (p s) s) = (\<Sum>s\<in>S. f s (inv p s))"
    (is "?l = ?r")
  using assms by (fact sum.permutes_inv)

context
  fixes A :: "'a set" 
    and B :: "'b set"
    and a_to_b :: "'a \<Rightarrow> 'b"
    and b_to_a :: "'b \<Rightarrow> 'a"
  assumes ab: "\<And> a. a \<in> A \<Longrightarrow> a_to_b a \<in> B"
    and ba: "\<And> b. b \<in> B \<Longrightarrow> b_to_a b \<in> A"
    and ab_ba: "\<And> a. a \<in> A \<Longrightarrow> b_to_a (a_to_b a) = a"
    and ba_ab: "\<And> b. b \<in> B \<Longrightarrow> a_to_b (b_to_a b) = b"
begin

qualified lemma permutes_memb: fixes p :: "'b \<Rightarrow> 'b"
  assumes p: "p permutes B"
  and a: "a \<in> A"
  defines "ip \<equiv> Hilbert_Choice.inv p"
  shows "a \<in> A" "a_to_b a \<in> B" "ip (a_to_b a) \<in> B" "p (a_to_b a) \<in> B" 
    "b_to_a (p (a_to_b a)) \<in> A" "b_to_a (ip (a_to_b a)) \<in> A"
proof -
  let ?b = "a_to_b a"
  from p have ip: "ip permutes B" unfolding ip_def by (rule permutes_inv)
  note in_ip = permutes_in_image[OF ip]
  note in_p = permutes_in_image[OF p]
  show a: "a \<in> A" by fact
  show b: "?b \<in> B" by (rule ab[OF a])
  show pb: "p ?b \<in> B" unfolding in_p by (rule b)
  show ipb: "ip ?b \<in> B" unfolding in_ip by (rule b)
  show "b_to_a (p ?b) \<in> A" by (rule ba[OF pb])
  show "b_to_a (ip ?b) \<in> A" by (rule ba[OF ipb])
qed

lemma permutes_bij_main: 
  "{p . p permutes A} \<supseteq> (\<lambda> p a. if a \<in> A then b_to_a (p (a_to_b a)) else a) ` {p . p permutes B}" 
  (is "?A \<supseteq> ?f ` ?B")
proof 
  note d = permutes_def
  let ?g = "\<lambda> q b. if b \<in> B then a_to_b (q (b_to_a b)) else b"
  let ?inv = "Hilbert_Choice.inv"
  fix p
  assume p: "p \<in> ?f ` ?B"
  then obtain q where q: "q permutes B" and p: "p = ?f q" by auto    
  let ?iq = "?inv q"
  from q have iq: "?iq permutes B" by (rule permutes_inv)
  note in_iq = permutes_in_image[OF iq]
  note in_q = permutes_in_image[OF q]
  have qiB: "\<And> b. b \<in> B \<Longrightarrow> q (?iq b) = b" using q by (rule permutes_inverses)
  have iqB: "\<And> b. b \<in> B \<Longrightarrow> ?iq (q b) = b" using q by (rule permutes_inverses)
  from q[unfolded d] 
  have q1: "\<And> b. b \<notin> B \<Longrightarrow> q b = b" 
   and q2: "\<And> b. \<exists>!b'. q b' = b" by auto
  note memb = permutes_memb[OF q]
  show "p \<in> ?A" unfolding p d
  proof (rule, intro conjI impI allI, force)
    fix a
    show "\<exists>!a'. ?f q a' = a"
    proof (cases "a \<in> A")
      case True
      note a = memb[OF True]
      let ?a = "b_to_a (?iq (a_to_b a))"
      show ?thesis
      proof 
        show "?f q ?a = a" using a by (simp add: ba_ab qiB ab_ba)
      next
        fix a'
        assume id: "?f q a' = a"
        show "a' = ?a"
        proof (cases "a' \<in> A")
          case False
          thus ?thesis using id a by auto
        next
          case True
          note a' = memb[OF this]
          from id True have "b_to_a (q (a_to_b a')) = a" by simp
          from arg_cong[OF this, of "a_to_b"] a' a
          have "q (a_to_b a') = a_to_b a" by (simp add: ba_ab)
          from arg_cong[OF this, of ?iq]
          have "a_to_b a' = ?iq (a_to_b a)" unfolding iqB[OF a'(2)] .
          from arg_cong[OF this, of b_to_a] show ?thesis unfolding ab_ba[OF True] .
        qed
      qed
    next
      case False note a = this
      show ?thesis
      proof
        show "?f q a = a" using a by simp
      next
        fix a'
        assume id: "?f q a' = a"
        show "a' = a"
        proof (cases "a' \<in> A")
          case False
          with id show ?thesis by simp
        next
          case True
          note a' = memb[OF True]
          with id False show ?thesis by auto
        qed
      qed
    qed
  qed
qed

end

lemma permutes_bij': assumes ab: "\<And> a. a \<in> A \<Longrightarrow> a_to_b a \<in> B"
    and ba: "\<And> b. b \<in> B \<Longrightarrow> b_to_a b \<in> A"
    and ab_ba: "\<And> a. a \<in> A \<Longrightarrow> b_to_a (a_to_b a) = a"
    and ba_ab: "\<And> b. b \<in> B \<Longrightarrow> a_to_b (b_to_a b) = b"
  shows "{p . p permutes A} = (\<lambda> p a. if a \<in> A then b_to_a (p (a_to_b a)) else a) ` {p . p permutes B}" 
  (is "?A = ?f ` ?B")
proof -
  note one_dir = ab ba ab_ba ba_ab
  note other_dir = ba ab ba_ab ab_ba
  let ?g = "(\<lambda> p b. if b \<in> B then a_to_b (p (b_to_a b)) else b)"
  define PA where "PA = ?A"
  define f where "f = ?f"
  define g where "g = ?g"
  {
    fix p
    assume "p \<in> PA"
    hence p: "p permutes A" unfolding PA_def by simp
    from p[unfolded permutes_def] have pnA: "\<And> a. a \<notin> A \<Longrightarrow> p a = a" by auto
    have "?f (?g p) = p"
    proof (rule ext)
      fix a
      show "?f (?g p) a = p a"
      proof (cases "a \<in> A")
        case False
        thus ?thesis by (simp add: pnA)
      next
        case True note a = this
        hence "p a \<in> A" unfolding permutes_in_image[OF p] .
        thus ?thesis using a by (simp add: ab_ba ba_ab ab)
      qed
    qed
    hence "f (g p) = p" unfolding f_def g_def .
  }
  hence "f ` g ` PA = PA" by force
  hence id: "?f ` ?g ` ?A = ?A" unfolding PA_def f_def g_def .
  have "?f ` ?B \<subseteq> ?A" by (rule permutes_bij_main[OF one_dir])
  moreover have "?g ` ?A \<subseteq> ?B" by (rule permutes_bij_main[OF ba ab ba_ab ab_ba])
  hence "?f ` ?g ` ?A \<subseteq> ?f ` ?B" by auto
  hence "?A \<subseteq> ?f ` ?B" unfolding id .
  ultimately show ?thesis by blast
qed    

lemma permutes_others:
  assumes p: "p permutes S" and x: "x \<notin> S" shows "p x = x"
  using p x by (rule permutes_not_in)

lemma inj_on_nat_permutes: assumes i: "inj_on f (S :: nat set)"
  and fS: "f \<in> S \<rightarrow> S"
  and fin: "finite S"
  and f: "\<And> i. i \<notin> S \<Longrightarrow> f i = i"
  shows "f permutes S"
  unfolding permutes_def
proof (intro conjI allI impI, rule f)
  fix y
  from endo_inj_surj[OF fin _ i] fS have fs: "f ` S = S" by auto
  show "\<exists>!x. f x = y"
  proof (cases "y \<in> S")
    case False
    thus ?thesis by (intro ex1I[of _ y], insert fS f, auto)
  next
    case True
    with fs obtain x where x: "x \<in> S" and fx: "f x = y" by force
    show ?thesis
    proof (rule ex1I, rule fx)
      fix x'
      assume fx': "f x' = y"
      with True f[of x'] have "x' \<in> S" by metis
      from inj_onD[OF i fx[folded fx'] x this]
      show "x' = x" by simp
    qed
  qed
qed

abbreviation (input) signof :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> 'a :: ring_1\<close>
  where \<open>signof p \<equiv> of_int (sign p)\<close>

lemma signof_id:
  "signof id = 1"
  "signof (\<lambda>x. x) = 1"
  by simp_all

lemma signof_inv: "finite S \<Longrightarrow> p permutes S \<Longrightarrow> signof (inv p) = signof p"
  by (simp add: permutes_imp_permutation sign_inverse)
  
lemma signof_pm_one: "signof p \<in> {1, - 1}"
  by (simp add: sign_def)
  
lemma signof_compose:
  assumes "p permutes {0..<(n :: nat)}"
  and "q permutes {0 ..<(m :: nat)}"
  shows "signof (p o q) = signof p * signof q"
proof -
  from assms have pp: "permutation p" "permutation q"
    by (auto simp: permutation_permutes)
  then show "signof (p o q) = signof p * signof q"
    by (simp add: sign_compose)
qed 

end
