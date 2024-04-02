theory Broadcast_Chain
  imports "Psi_Calculi.Chain"
begin

lemma pair_perm_fresh_contr:
  fixes a::'a and b::'a
  assumes
    at: "at TYPE('a)"
  and
    prems: "b \<sharp> pi" "(a, b) \<in> set pi"
  shows False
  using prems
  by(induct pi)
    (auto simp add: supp_list_cons fresh_list_nil supp_prod at_supp[OF at]
                    fresh_list_cons fresh_prod at_fresh[OF at])

lemma pair_perm_fresh_contr':
  fixes a::'a and b::'a
  assumes
    at: "at TYPE('a)"
  and
    prems: "a \<sharp> pi" "(a, b) \<in> set pi"
  shows False
  using prems
  by(induct pi)
    (auto simp add: supp_list_cons fresh_list_nil supp_prod at_supp[OF at]
                    fresh_list_cons fresh_prod at_fresh[OF at])

lemma list_set_supp:
  fixes l :: "('d::fs_name) list"
  shows "supp (set l) = (supp l :: name set)"
proof(induct l)
  case Nil then show ?case
    by (simp add: supp_list_nil supp_set_empty)
next
  case (Cons x xs) then show ?case
    using at_name_inst fs_name_inst pt_list_set_supp pt_name_inst by blast
qed

lemma name_set_supp:
  assumes "finite a"
  shows "supp a = (a::name set)"
  using assms
  by(rule at_fin_set_supp[OF at_name_inst])

lemma supp_idem:
  fixes l :: "('d::fs_name)"
  shows "supp((supp l)::name set) = (supp(l)::name set)"
proof -
  have f: "finite((supp l)::name set)"
    by finite_guess
  show ?thesis
    by(rule name_set_supp[OF f])
qed

lemma fresh_supp:
  fixes a :: name
    and X :: "('d::fs_name)"
  shows "a \<sharp> ((supp X)::name set) = a \<sharp> X"
  by(simp add: fresh_def supp_idem)

lemma fresh_chain_supp:
  fixes A :: "name list"
    and X :: "('d::fs_name)"
  shows "A \<sharp>* ((supp X)::name set) = A \<sharp>* X"
  unfolding fresh_star_def
  by(simp add: fresh_supp)

lemma fresh_chain_fin_union:
  fixes X::"('d::fs_name set)"
    and Y::"('d::fs_name set)"
    and A::"name list"
  assumes f1: "finite X"
    and f2: "finite Y"
  shows "A\<sharp>*(X\<union>Y) = (A\<sharp>*X \<and> A\<sharp>*Y)"
  unfolding fresh_star_def
  apply(subst fresh_fin_union[OF pt_name_inst, OF at_name_inst, OF fs_name_inst, OF f1, OF f2])
  by blast

lemma fresh_subset:
  fixes S :: "name set"
    and S' :: "name set"
    and a :: name
  assumes "a \<sharp> S"
    and "S' \<subseteq> S"
    and "finite S"

shows "a \<sharp> S'"
proof -
  have "finite S'" using \<open>S' \<subseteq> S\<close> \<open>finite S\<close>
    by(rule Finite_Set.finite_subset)
  with assms show ?thesis
    by(auto simp add: fresh_def supp_subset Chain.name_list_supp name_set_supp)
qed

lemma fresh_subset':
  fixes S :: "'d::fs_name set"
    and S' :: "'d::fs_name set"
    and a :: name
  assumes "a \<sharp> S"
    and "S' \<subseteq> S"
    and "finite S"

shows "a \<sharp> S'"
proof -
  have "finite S'" using \<open>S' \<subseteq> S\<close> \<open>finite S\<close>
    by(rule Finite_Set.finite_subset)
  have "supp S' \<subseteq> ((supp S)::name set)"
    apply(rule Chain.supp_subset)
    by fact+
  with assms show ?thesis
    unfolding fresh_def
    by auto
qed

lemma fresh_star_subset':
  fixes S :: "'d::fs_name set"
    and S' :: "'d::fs_name set"
    and A :: "name list"
  assumes "A \<sharp>* S"
    and "S' \<subseteq> S"
    and "finite S"

shows "A \<sharp>* S'"
  using assms
  unfolding fresh_star_def
  by(auto simp add: fresh_subset')

lemma fresh_star_subset:
  fixes S :: "name set"
    and S' :: "name set"
    and A :: "name list"
  assumes "A \<sharp>* S"
    and "S' \<subseteq> S"
    and "finite S"

shows "A \<sharp>* S'"
  using assms
  unfolding fresh_star_def
  by(auto simp add: fresh_subset)

lemma times_set_fresh:
  fixes a  :: name
    and S  :: "name list"
    and S' :: "name list"
  assumes "a \<sharp> set S"
    and "a \<sharp> set S'"
  shows "a \<sharp> set S \<times> set S'"
  using assms
proof(cases S)
  case Nil then show ?thesis by(simp add: fresh_set_empty)
next
  case (Cons s Svec) then show ?thesis
  proof(cases S')
    case Nil then show ?thesis by(simp add: fresh_set_empty)
  next
    case (Cons s' S') then show ?thesis
      using \<open>S = s # Svec\<close> assms
      apply(subst fresh_cart_prod[OF pt_name_inst, OF pt_name_inst, OF fs_name_inst, OF fs_name_inst, OF at_name_inst])
      by(simp+)
  qed
qed

lemma times_set_fresh_star:
  fixes A  :: "name list"
    and S  :: "name list"
    and S' :: "name list"
  assumes "A \<sharp>* set S"
    and "A \<sharp>* set S'"
  shows "A \<sharp>* (set S \<times> set S')"
  using assms
  unfolding fresh_star_def
proof(induct A)
  case Nil show ?case by simp
next
  case(Cons a A)
  have "a \<sharp> set S" and "a \<sharp> set S'" using Cons by simp+
  then have "a \<sharp> (set S \<times> set S')" by(rule times_set_fresh)
  have "\<forall> x\<in>set A. (x \<sharp> set S)" and "\<forall> x\<in>set A. (x \<sharp> set S')" using Cons
    by simp+
  then have "\<forall>x\<in>set A. x \<sharp> set S \<times> set S'" using Cons by simp
  then show ?case using \<open>a \<sharp> (set S \<times> set S')\<close>
    by simp
qed

lemma supp_list_set:
  fixes M::"'d::fs_name list"
  shows "(supp M) = ((supp(set M))::name set)"
proof(induct M)
  case Nil then show ?case by(simp add: supp_set_empty supp_list_nil)
next
  case (Cons m M)
  have lhs: "(supp (m # M)::name set) = supp m \<union> supp M" by(simp add: supp_list_cons)
  have rhs: "(supp (set (m # M))::name set) = supp m \<union> supp M"
  proof -
    have "supp (set (m # M)) = (supp (set [m] \<union> set M)::name set)"
      by simp
    moreover have "\<dots> = supp (set [m]) \<union> supp(set M)"
      apply(rule supp_fin_union[OF pt_name_inst, OF at_name_inst, OF fs_name_inst])
      by simp+
    moreover have "\<dots> = supp m \<union> supp M"
      using calculation(1) calculation(2) lhs list_set_supp by blast
    ultimately show ?thesis
      by simp
  qed
  show ?case
    unfolding lhs rhs
    by(rule refl)
qed

lemma fresh_list_set:
  fixes M::"'d::fs_name list"
    and A::"name list"
  shows "A \<sharp>* set M = A \<sharp>* M"
  unfolding fresh_star_def fresh_def supp_list_set
  by(rule refl)

lemma permSupp:
  fixes \<Psi>  :: "name prm"
    and \<Psi>' :: "'d::fs_name"

shows "(supp(\<Psi> \<bullet> \<Psi>')::name set) \<subseteq> ((supp \<Psi>) \<union> (supp \<Psi>'))"
proof -
  {
    fix x::name
    let ?P = "\<lambda>y. ([(x, y)] \<bullet> \<Psi>) \<bullet> ([(x, y)] \<bullet> \<Psi>') \<noteq> \<Psi> \<bullet> \<Psi>'"
    let ?Q = "\<lambda>y \<Psi>. ([(x, y)] \<bullet> \<Psi>) \<noteq> \<Psi>"
    assume "finite {y. ?Q y \<Psi>'}"
    moreover assume "finite {y. ?Q y \<Psi>}"
    and "infinite {b. [(x, b)] \<bullet> \<Psi> \<bullet> \<Psi>' \<noteq> \<Psi> \<bullet> \<Psi>'}"
    from \<open>infinite {b. [(x, b)] \<bullet> \<Psi> \<bullet> \<Psi>' \<noteq> \<Psi> \<bullet> \<Psi>'}\<close> have "infinite {y. ?P(y)}"
      by(subst cp1[symmetric, OF cp_pt_inst, OF pt_name_inst, OF at_name_inst])
    then have "infinite({y. ?P(y)} - {y. ?Q y \<Psi>})"
      using \<open>finite {y. ?Q y \<Psi>'}\<close> \<open>finite {y. ?Q y \<Psi>}\<close>
      by - (rule Diff_infinite_finite)
    ultimately have "infinite(({y. ?P(y)} - {y. ?Q y \<Psi>}) - {y. ?Q y \<Psi>'})"
      by(rule Diff_infinite_finite)
    then have "infinite({y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')})" by(simp add: set_diff_eq)
    moreover have "{y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')} = {}"
      by auto
    ultimately have "infinite {}"
      by - (drule Infinite_cong, auto)
    then have False by simp
  }
  from this show ?thesis
    by(force simp add: supp_def)
qed

end
