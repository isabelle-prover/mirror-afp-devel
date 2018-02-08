(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Gr\"obner Bases and Buchberger's Theorem\<close>

theory Groebner_Bases
imports Reduction
begin

text \<open>This theory provides the main results about Gr\"obner bases for multivariate polynomials.\<close>

context gd_powerprod
begin

definition crit_pair :: "('a \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b))"
  where "crit_pair p q = (monom_mult (1 / lc p) ((lcs (lp p) (lp q)) - (lp p)) (tail p),
                          monom_mult (1 / lc q) ((lcs (lp p) (lp q)) - (lp q)) (tail q))"

definition crit_pair_cbelow_on :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "crit_pair_cbelow_on d m F p q \<longleftrightarrow> cbelow_on (dgrad_p_set d m) (\<prec>p)
                                                     (monomial 1 (lcs (lp p) (lp q))) (\<lambda>a b. red F a b \<or> red F b a)
                                                     (fst (crit_pair p q)) (snd (crit_pair p q))"

definition spoly :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field)"
  where "spoly p q = (monom_mult (1 / lc p) ((lcs (lp p) (lp q)) - (lp p)) p) -
                      (monom_mult (1 / lc q) ((lcs (lp p) (lp q)) - (lp q)) q)"

definition (in ordered_powerprod) is_Groebner_basis::"('a \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool"
  where "is_Groebner_basis F \<equiv> relation.is_ChurchRosser (red F)"

subsection \<open>Critical Pairs and S-Polynomials\<close>

lemma crit_pair_same: "fst (crit_pair p p) = snd (crit_pair p p)"
  by (simp add: crit_pair_def)

lemma crit_pair_swap: "crit_pair p q = (snd (crit_pair q p), fst (crit_pair q p))"
  by (simp add: crit_pair_def lcs_comm)

lemma crit_pair_zero [simp]: "fst (crit_pair 0 q) = 0" and "snd (crit_pair p 0) = 0"
  by (simp_all add: crit_pair_def monom_mult_right0)

lemma dgrad_p_set_le_crit_pair_zero: "dgrad_p_set_le d {fst (crit_pair p 0)} {p}"
proof (simp add: crit_pair_def lp_def[of 0] monom_mult_right0 lcs_comm lcs_zero dgrad_p_set_le_def
      Keys_insert, rule dgrad_set_leI)
  fix s
  assume "s \<in> keys (monom_mult (1 / lc p) 0 (tail p))"
  from this keys_monom_mult_subset have "s \<in> plus 0 ` keys (tail p)" ..
  hence "s \<in> keys (tail p)" by simp
  hence "s \<in> keys p" by (simp add: keys_tail)
  moreover have "d s \<le> d s" ..
  ultimately show "\<exists>t\<in>keys p. d s \<le> d t" ..
qed

lemma dgrad_p_set_le_fst_crit_pair:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d {fst (crit_pair p q)} {p, q}"
proof (cases "q = 0")
  case True
  have "dgrad_p_set_le d {fst (crit_pair p q)} {p}" unfolding True
    by (fact dgrad_p_set_le_crit_pair_zero)
  also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
  finally show ?thesis .
next
  case False
  show ?thesis
  proof (cases "p = 0")
    case True
    have "dgrad_p_set_le d {fst (crit_pair p q)} {q}"
      by (simp add: True dgrad_p_set_le_def dgrad_set_le_def)
    also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof (simp add: dgrad_p_set_le_def Keys_insert crit_pair_def)
      define t where "t = lcs (lp p) (lp q) - lp p"
      let ?m = "monom_mult (1 / lc p) t (tail p)"
      from assms have "dgrad_set_le d (keys ?m) (insert t (keys (tail p)))"
        by (rule dgrad_set_le_monom_mult)
      also have "dgrad_set_le d ... (keys p \<union> keys q)"
      proof (rule dgrad_set_leI, simp)
        fix s
        assume "s = t \<or> s \<in> keys (tail p)"
        thus "\<exists>t\<in>keys p \<union> keys q. d s \<le> d t"
        proof
          assume "s = t"
          from assms have "d s \<le> ord_class.max (d (lp p)) (d (lp q))" unfolding \<open>s = t\<close> t_def
            by (rule dickson_grading_lcs_minus)
          hence "d s \<le> d (lp p) \<or> d s \<le> d (lp q)" by auto
          thus ?thesis
          proof
            from \<open>p \<noteq> 0\<close> have "lp p \<in> keys p" by (rule lp_in_keys)
            hence "lp p \<in> keys p \<union> keys q" by simp
            moreover assume "d s \<le> d (lp p)"
            ultimately show ?thesis ..
          next
            from \<open>q \<noteq> 0\<close> have "lp q \<in> keys q" by (rule lp_in_keys)
            hence "lp q \<in> keys p \<union> keys q" by simp
            moreover assume "d s \<le> d (lp q)"
            ultimately show ?thesis ..
          qed
        next
          assume "s \<in> keys (tail p)"
          hence "s \<in> keys p \<union> keys q" by (simp add: keys_tail)
          moreover have "d s \<le> d s" ..
          ultimately show ?thesis ..
        qed
      qed
      finally show "dgrad_set_le d (keys ?m) (keys p \<union> keys q)" .
    qed
  qed
qed

lemma dgrad_p_set_le_snd_crit_pair:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d {snd (crit_pair p q)} {p, q}"
  by (simp add: crit_pair_swap[of p] insert_commute[of p q], rule dgrad_p_set_le_fst_crit_pair, fact)

lemma dgrad_p_set_closed_fst_crit_pair:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "fst (crit_pair p q) \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_fst_crit_pair[OF assms(1)] have "{fst (crit_pair p q)} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(2, 3) show "{p, q} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_snd_crit_pair:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "snd (crit_pair p q) \<in> dgrad_p_set d m"
  by (simp add: crit_pair_swap[of p q], rule dgrad_p_set_closed_fst_crit_pair, fact+)

lemma fst_crit_pair_below_lcs: "fst (crit_pair p q) \<prec>p monomial 1 (lcs (lp p) (lp q))"
proof (cases "tail p = 0")
  case True
  thus ?thesis by (simp add: crit_pair_def ord_strict_p_monomial_iff monom_mult_right0)
next
  case False
  hence "p \<noteq> 0" by auto
  hence "lc p \<noteq> 0" by (rule lc_not_0)
  hence "1 / lc p \<noteq> 0" by simp
  from this False have "lp (monom_mult (1 / lc p) (lcs (lp p) (lp q) - lp p) (tail p)) =
                        lcs (lp p) (lp q) - lp p + lp (tail p)"
    by (rule lp_monom_mult)
  also from lp_tail[OF False] have "... \<prec> lcs (lp p) (lp q) - lp p + lp p"
    by (rule plus_monotone_strict_left)
  also from adds_lcs have "... = lcs (lp p) (lp q)" by (rule adds_minus)
  finally show ?thesis by (simp add: crit_pair_def ord_strict_p_monomial_iff)
qed

lemma snd_crit_pair_below_lcs: "snd (crit_pair p q) \<prec>p monomial 1 (lcs (lp p) (lp q))"
  by (simp add: crit_pair_swap[of p] lcs_comm[of "lp p"], fact fst_crit_pair_below_lcs)

lemma crit_pair_cbelow_same:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m"
  shows "crit_pair_cbelow_on d m F p p"
proof (simp add: crit_pair_cbelow_on_def crit_pair_same cbelow_on_def, intro disjI1 conjI)
  from assms(1) assms(2) assms(2) show "snd (crit_pair p p) \<in> dgrad_p_set d m"
    by (rule dgrad_p_set_closed_snd_crit_pair)
next
  from snd_crit_pair_below_lcs[of p p] show "snd (crit_pair p p) \<prec>p monomial 1 (lp p)" by simp
qed

lemma crit_pair_cbelow_sym: "crit_pair_cbelow_on d m F p q \<Longrightarrow> crit_pair_cbelow_on d m F q p"
proof (simp add: crit_pair_cbelow_on_def crit_pair_swap[of p q] lcs_comm, rule cbelow_on_symmetric)
  show "symp (\<lambda>a b. red F a b \<or> red F b a)" by (simp add: symp_def)
qed

lemma crit_pair_cs_imp_crit_pair_cbelow_on:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m"
    and "relation.cs (red F) (fst (crit_pair p q)) (snd (crit_pair p q))"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  from assms(1) have "relation_order (red F) (\<prec>p) (dgrad_p_set d m)" by (rule is_relation_order_red)
  moreover have "relation.dw_closed (red F) (dgrad_p_set d m)"
    by (rule relation.dw_closedI, rule dgrad_p_set_closed_red, rule assms(1), rule assms(2))
  moreover note assms(5)
  moreover from assms(1) assms(3) assms(4) have "fst (crit_pair p q) \<in> dgrad_p_set d m"
    by (rule dgrad_p_set_closed_fst_crit_pair)
  moreover from assms(1) assms(3) assms(4) have "snd (crit_pair p q) \<in> dgrad_p_set d m"
    by (rule dgrad_p_set_closed_snd_crit_pair)
  moreover note fst_crit_pair_below_lcs snd_crit_pair_below_lcs
  ultimately show ?thesis unfolding crit_pair_cbelow_on_def by (rule relation_order.cs_implies_cbelow_on)
qed

lemma crit_pair_cbelow_mono:
  assumes "crit_pair_cbelow_on d m F p q" and "F \<subseteq> G"
  shows "crit_pair_cbelow_on d m G p q"
  using assms(1) unfolding crit_pair_cbelow_on_def
proof (induct rule: cbelow_on_induct)
  case base
  show ?case by (simp add: cbelow_on_def, intro disjI1 conjI, fact+)
next
  case (step b c)
  from step(2) have "red G b c \<or> red G c b" using red_subset[OF _ assms(2)] by blast
  from step(5) step(3) this step(4) show ?case ..
qed

lemma lcs_red_single_fst_crit_pair:
  assumes "p \<noteq> 0"
  shows "red_single (monomial (-1) (lcs (lp p) (lp q))) (fst (crit_pair p q)) p (lcs (lp p) (lp q) - lp p)"
proof -
  let ?l = "lcs (lp p) (lp q)"
  from assms have "lc p \<noteq> 0" by (rule lc_not_0)
  have "lp p adds ?l" by (rule adds_lcs)
  hence eq1: "?l - lp p + lp p = ?l" by (rule adds_minus)
  with assms show ?thesis
  proof (simp add: crit_pair_def red_single_def)
    have eq2: "monomial (-1) ?l = monom_mult (- (1 / lc p)) (?l - lp p) (monomial (lc p) (lp p))"
      by (simp add: monom_mult_monomial eq1 \<open>lc p \<noteq> 0\<close>)
    show "monom_mult (1 / lc p) (?l - lp p) (tail p) = monomial (-1) ?l - monom_mult (- (1 / lc p)) (?l - lp p) p"
      by (simp add: eq2 monom_mult_dist_right_minus[symmetric] tail_alt_2 monom_mult_uminus_left)
  qed
qed

corollary lcs_red_single_snd_crit_pair:
  assumes "q \<noteq> 0"
  shows "red_single (monomial (-1) (lcs (lp p) (lp q))) (snd (crit_pair p q)) q (lcs (lp p) (lp q) - lp q)"
  by (simp add: crit_pair_swap[of p q] lcs_comm[of "lp p"], rule lcs_red_single_fst_crit_pair, fact)

lemma GB_imp_crit_pair_cbelow_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "is_Groebner_basis F"
  assumes "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
  shows "crit_pair_cbelow_on d m F p q"
  using assms(1, 2)
proof (rule crit_pair_cs_imp_crit_pair_cbelow_on)
  from assms(4, 2) show "p \<in> dgrad_p_set d m" ..
next
  from assms(5, 2) show "q \<in> dgrad_p_set d m" ..
next
  let ?cp = "crit_pair p q"
  let ?l = "monomial (-1) (lcs (lp p) (lp q))"
  from assms(4) lcs_red_single_fst_crit_pair[OF assms(6)] have "red F ?l (fst ?cp)"
    by (rule red_setI)
  hence 1: "(red F)\<^sup>*\<^sup>* ?l (fst ?cp)" ..
  from assms(5) lcs_red_single_snd_crit_pair[OF assms(7)] have "red F ?l (snd ?cp)"
    by (rule red_setI)
  hence 2: "(red F)\<^sup>*\<^sup>* ?l (snd ?cp)" ..
  from assms(3) have "relation.is_confluent_on (red F) UNIV"
    by (simp only: is_Groebner_basis_def relation.confluence_equiv_ChurchRosser[symmetric]
        relation.is_confluent_def)
  from this 1 2 show "relation.cs (red F) (fst ?cp) (snd ?cp)"
    by (simp add: relation.is_confluent_on_def)
qed

lemma spoly_alt:
  assumes "p \<noteq> 0" and "q \<noteq> 0"
  shows "spoly p q = fst (crit_pair p q) - snd (crit_pair p q)"
proof (rule poly_mapping_eqI, simp only: lookup_minus)
  fix t
  let ?l = "lcs (lp p) (lp q)"
  let ?cp = "crit_pair p q"
  let ?a = "\<lambda>x. monom_mult (1 / lc p) (?l - (lp p)) x"
  let ?b = "\<lambda>x. monom_mult (1 / lc q) (?l - (lp q)) x"
  have l_1: "(?l - lp p) + lp p = ?l" by (metis add.commute add_diff_cancel_left' adds_def adds_lcs)
  have l_2: "(?l - lp q) + lp q = ?l" by (metis add.commute add_diff_cancel_left' adds_def adds_lcs_2)
  show "lookup (spoly p q) t = lookup (fst ?cp) t - lookup (snd ?cp) t"
  proof (cases "t = ?l")
    case True
    have t_1: "t = (?l - lp p) + lp p" by (simp add: True l_1)
    from \<open>p \<noteq> 0\<close> have "lp p \<in> keys p" by (rule lp_in_keys)
    hence t_2: "t = (?l - lp q) + lp q" by (simp add: True l_2)
    from \<open>q \<noteq> 0\<close> have "lp q \<in> keys q" by (rule lp_in_keys)
    from \<open>lp p \<in> keys p\<close> have "lookup (?a p) t = 1" by (simp add: t_1 lookup_monom_mult lc_def)
    also from \<open>lp q \<in> keys q\<close> have "... = lookup (?b q) t" by (simp add: t_2 lookup_monom_mult lc_def)
    finally have "lookup (spoly p q) t = 0" by (simp add: spoly_def lookup_minus)
    moreover have "lookup (fst ?cp) t = 0"
      by (simp add: crit_pair_def t_1 lookup_monom_mult,
          simp only: not_in_keys_iff_lookup_eq_zero[symmetric] keys_tail, simp)
    moreover have "lookup (snd ?cp) t = 0"
      by (simp add: crit_pair_def t_2 lookup_monom_mult,
          simp only: not_in_keys_iff_lookup_eq_zero[symmetric] keys_tail, simp)
    ultimately show ?thesis by simp
  next
    case False
    have "lookup (?a (tail p)) t = lookup (?a p) t"
    proof (cases "?l - lp p adds t")
      case True
      then obtain s where t: "t = ?l - lp p + s" ..
      have "s \<noteq> lp p"
      proof
        assume "s = lp p"
        hence "t = ?l" by (simp add: t l_1)
        with \<open>t \<noteq> ?l\<close> show False ..
      qed
      thus ?thesis by (simp add: t lookup_monom_mult lookup_tail_2)
    next
      case False
      thus ?thesis by (simp add: monom_mult.rep_eq)
    qed
    moreover have "lookup (?b (tail q)) t = lookup (?b q) t"
    proof (cases "?l - lp q adds t")
      case True
      then obtain s where t: "t = ?l - lp q + s" ..
      have "s \<noteq> lp q"
      proof
        assume "s = lp q"
        hence "t = ?l" by (simp add: t l_2)
        with \<open>t \<noteq> ?l\<close> show False ..
      qed
      thus ?thesis by (simp add: t lookup_monom_mult lookup_tail_2)
    next
      case False
      thus ?thesis by (simp add: monom_mult.rep_eq)
    qed
    ultimately show ?thesis by (simp add: spoly_def crit_pair_def lookup_minus)
  qed
qed

lemma spoly_same: "spoly p p = 0"
  by (simp add: spoly_def)

lemma spoly_swap: "spoly p q = - spoly q p"
  by (simp add: spoly_def lcs_comm)

lemma spoly_red_zero_imp_crit_pair_cbelow_on:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m" and "p \<noteq> 0" and "q \<noteq> 0" and "(red F)\<^sup>*\<^sup>* (spoly p q) 0"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  from assms(7) have "relation.cs (red F) (fst (crit_pair p q)) (snd (crit_pair p q))"
    unfolding spoly_alt[OF assms(5) assms(6)] by (rule red_diff_rtrancl_cs)
  with assms(1) assms(2) assms(3) assms(4) show ?thesis by (rule crit_pair_cs_imp_crit_pair_cbelow_on)
qed

lemma dgrad_p_set_le_spoly_zero: "dgrad_p_set_le d {spoly p 0} {p}"
proof (simp add: spoly_def lp_def[of 0] monom_mult_right0 lcs_comm lcs_zero dgrad_p_set_le_def
      Keys_insert, rule dgrad_set_leI)
  fix s
  assume "s \<in> keys (monom_mult (1 / lc p) 0 p)"
  from this keys_monom_mult_subset have "s \<in> plus 0 ` keys p" ..
  hence "s \<in> keys p" by simp
  moreover have "d s \<le> d s" ..
  ultimately show "\<exists>t\<in>keys p. d s \<le> d t" ..
qed

lemma dgrad_p_set_le_spoly:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d {spoly p q} {p, q}"
proof (cases "p = 0")
  case True
  have "dgrad_p_set_le d {spoly p q} {spoly q 0}" unfolding True spoly_swap[of 0 q]
    by (fact dgrad_p_set_le_uminus)
  also have "dgrad_p_set_le d ... {q}" by (fact dgrad_p_set_le_spoly_zero)
  also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
  finally show ?thesis .
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    have "dgrad_p_set_le d {spoly p q} {p}" unfolding True by (fact dgrad_p_set_le_spoly_zero)
    also have "dgrad_p_set_le d ... {p, q}" by (rule dgrad_p_set_le_subset, simp)
    finally show ?thesis .
  next
    case False
    have "dgrad_p_set_le d {spoly p q} {fst (crit_pair p q), snd (crit_pair p q)}"
      unfolding spoly_alt[OF \<open>p \<noteq> 0\<close> False] by (rule dgrad_p_set_le_minus)
    also have "dgrad_p_set_le d ... {p, q}"
    proof (rule dgrad_p_set_leI_insert)
      from assms show "dgrad_p_set_le d {fst (crit_pair p q)} {p, q}"
        by (rule dgrad_p_set_le_fst_crit_pair)
    next
      from assms show "dgrad_p_set_le d {snd (crit_pair p q)} {p, q}"
        by (rule dgrad_p_set_le_snd_crit_pair)
    qed
    finally show ?thesis .
  qed
qed

lemma dgrad_p_set_closed_spoly:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "spoly p q \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_spoly[OF assms(1)] have "{spoly p q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(2, 3) show "{p, q} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

subsection \<open>Buchberger's Theorem\<close>

text \<open>Before proving the main theorem of Gr\"obner bases theory for S-polynomials, as is usually done
  in textbooks, we first prove it for critical pairs: a set @{term F} yields a confluent reduction
  relation if the critical pairs of all @{term "p \<in> F"} and @{term "q \<in> F"} can be connected below
  the least common sum of the leading power-products of @{term p} and @{term q}.
  The reason why we proceed in this way is that it becomes much easier to prove the correctness of
  Buchberger's second criterion for avoiding useless pairs.\<close>

lemma crit_pair_cbelow_imp_confluent_dgrad_p_set:
  assumes dg: "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  assumes main: "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m F p q"
  shows "relation.is_confluent_on (red F) (dgrad_p_set d m)"
proof -
  let ?A = "dgrad_p_set d m"
  let ?R = "red F"
  let ?RS = "\<lambda>a b. red F a b \<or> red F b a"
  let ?ord = "(\<prec>p)"
  from dg have ro: "Confluence.relation_order ?R ?ord ?A"
    by (rule is_relation_order_red)
  have dw: "relation.dw_closed ?R ?A"
    by (rule relation.dw_closedI, rule dgrad_p_set_closed_red, rule dg, rule assms(2))
  show ?thesis
  proof (rule relation_order.loc_connectivity_implies_confluence, fact ro)
    show "is_loc_connective_on ?A ?ord ?R" unfolding is_loc_connective_on_def
    proof (intro ballI allI impI)
      fix a b1 b2 :: "'a \<Rightarrow>\<^sub>0 'b"
      assume "a \<in> ?A"
      assume "?R a b1 \<and> ?R a b2"
      hence "?R a b1" and "?R a b2" by simp_all
      hence "b1 \<in> ?A" and "b2 \<in> ?A" and "?ord b1 a" and "?ord b2 a"
        using red_ord dgrad_p_set_closed_red[OF dg assms(2) \<open>a \<in> ?A\<close>] by blast+
      from this(1) this(2) have "b1 - b2 \<in> ?A" by (rule dgrad_p_set_closed_minus)
      from \<open>red F a b1\<close> obtain f1 and t1 where "f1 \<in> F" and r1: "red_single a b1 f1 t1" by (rule red_setE)
      from \<open>red F a b2\<close> obtain f2 and t2 where "f2 \<in> F" and r2: "red_single a b2 f2 t2" by (rule red_setE)
      from r1 r2 have "f1 \<noteq> 0" and "f2 \<noteq> 0" by (simp_all add: red_single_def)
      hence lc1: "lc f1 \<noteq> 0" and lc2: "lc f2 \<noteq> 0" using lc_not_0 by auto
      show "cbelow_on ?A ?ord a (\<lambda>a b. ?R a b \<or> ?R b a) b1 b2"
      proof (cases "t1 + lp f1 = t2 + lp f2")
        case False
        from confluent_distinct[OF r1 r2 False \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>] obtain s where
          s1: "(red F)\<^sup>*\<^sup>* b1 s" and s2: "(red F)\<^sup>*\<^sup>* b2 s" .
        have "relation.cs ?R b1 b2" unfolding relation.cs_def by (intro exI conjI, fact s1, fact s2)
        from ro dw this \<open>b1 \<in> ?A\<close> \<open>b2 \<in> ?A\<close> \<open>?ord b1 a\<close> \<open>?ord b2 a\<close> show ?thesis
          by (rule relation_order.cs_implies_cbelow_on)
      next
        case True
        define t where "t \<equiv> t2 + lp f2"
        define l where "l \<equiv> lcs (lp f1) (lp f2)"
        define a' where "a' = except a {t}"
        define ma where "ma = monomial (lookup a t) t"
        have t_alt: "t = t1 + lp f1" by (simp only: True t_def)
        have "a = ma + a'" unfolding ma_def a'_def by (fact plus_except)

        from adds_lcs[of "lp f1" "lp f2"] have "(lp f1) adds l" unfolding l_def .
        from adds_lcs_2[of "lp f2" "lp f1"] have "(lp f2) adds l" unfolding l_def .
        have "lp f1 adds (t1 + lp f1)" by (simp add: t_def)
        hence "lp f1 adds t" by (simp add: t_def True)
        have "lp f2 adds t" by (simp add: t_def)
        from lcs_adds[OF \<open>lp f1 adds t\<close> \<open>lp f2 adds t\<close>] have "l adds t" unfolding l_def .
        from True have "t - (lp f1) = t1" unfolding t_def by (metis add_implies_diff)
        with \<open>l adds t\<close> \<open>lp f1 adds l\<close> have tf1: "(t - l) + (l - (lp f1)) = t1"
          by (metis minus_plus_minus_cancel)
        have "t - (lp f2) = t2" by (simp add: t_def)
        with \<open>l adds t\<close> \<open>lp f2 adds l\<close> have tf2: "(t - l) + (l - (lp f2)) = t2"
          by (metis minus_plus_minus_cancel)
        let ?ca = "lookup a t"
        let ?v = "t - l"
        from \<open>l adds t\<close> have "?v + l = t" by (simp add: adds_minus)
        from tf1 have "?v adds t1" using addsI by blast
        with dg have "d ?v \<le> d t1" by (rule dickson_grading_adds_imp_le)
        also from dg \<open>a \<in> ?A\<close> r1 have "... \<le> m" by (rule dgrad_p_set_red_single_pp)
        finally have "d ?v \<le> m" .
        from r2 have "?ca \<noteq> 0" by (simp add: red_single_def t_def)
        hence "-?ca \<noteq> 0" by simp

        (* b1 *)
        from r1 have "b1 = a - monom_mult (?ca / lc f1) t1 f1"
          by (simp add: red_single_def t_def True)
        also have "... = monom_mult (- ?ca) ?v (fst (crit_pair f1 f2)) + a'"
        proof (simp add: a'_def crit_pair_def l_def[symmetric] monom_mult_assoc tf1, rule poly_mapping_eqI,
              simp add: lookup_add lookup_minus)
          fix s
          show "lookup a s - lookup (monom_mult (?ca / lc f1) t1 f1) s =
                lookup (monom_mult (- (?ca / lc f1)) t1 (tail f1)) s + lookup (except a {t}) s"
          proof (cases "s = t")
            case True
            show ?thesis
              by (simp add: True lookup_except,
                  simp add: t_alt lookup_monom_mult lookup_tail_2 lc_def[symmetric] lc1)
          next
            case False
            hence "s \<notin> {t}" by simp
            moreover
            {
              assume "t1 adds s"
              hence "t1 + (s - t1) = s" by (metis add.commute adds_minus)
              hence "s - t1 \<noteq> lp f1" using False t_alt by auto
              hence "lookup f1 (s - t1) = lookup (tail f1) (s - t1)" by (simp add: lookup_tail_2)
            }
            ultimately show ?thesis using False by (simp add: lookup_except monom_mult.rep_eq)
          qed
        qed
        finally have b1: "b1 = monom_mult (- ?ca) ?v (fst (crit_pair f1 f2)) + a'" .

        (* b2 *)
        from r2 have "b2 = a - monom_mult (?ca / lc f2) t2 f2"
          by (simp add: red_single_def t_def True)
        also have "... = monom_mult (- ?ca) ?v (snd (crit_pair f1 f2)) + a'"
        proof (simp add: a'_def crit_pair_def l_def[symmetric] monom_mult_assoc tf2, rule poly_mapping_eqI,
              simp add: lookup_add lookup_minus)
          fix s
          show "lookup a s - lookup (monom_mult (?ca / lc f2) t2 f2) s =
                lookup (monom_mult (- (?ca / lc f2)) t2 (tail f2)) s + lookup (except a {t}) s"
          proof (cases "s = t")
            case True
            show ?thesis
              by (simp add: True lookup_except,
                  simp add: t_def lookup_monom_mult lookup_tail_2 lc_def[symmetric] lc2)
          next
            case False
            hence "s \<notin> {t}" by simp
            moreover
            {
              assume "t2 adds s"
              hence "t2 + (s - t2) = s" by (metis add.commute adds_minus)
              hence "s - t2 \<noteq> lp f2" using False t_def by auto
              hence "lookup f2 (s - t2) = lookup (tail f2) (s - t2)" by (simp add: lookup_tail_2)
            }
            ultimately show ?thesis using False by (simp add: lookup_except monom_mult.rep_eq)
          qed
        qed
        finally have b2: "b2 = monom_mult (- ?ca) ?v (snd (crit_pair f1 f2)) + a'" .

        from \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close> \<open>f1 \<noteq> 0\<close> \<open>f2 \<noteq> 0\<close> have "crit_pair_cbelow_on d m F f1 f2" by (rule main)
        hence "cbelow_on ?A ?ord (monomial 1 l) ?RS (fst (crit_pair f1 f2)) (snd (crit_pair f1 f2))"
          by (simp only: crit_pair_cbelow_on_def l_def)
        with dg assms (2) \<open>d ?v \<le> m\<close> \<open>-?ca \<noteq> 0\<close>
        have "cbelow_on ?A ?ord (monom_mult (-?ca) ?v (monomial 1 l)) ?RS
              (monom_mult (-?ca) ?v (fst (crit_pair f1 f2))) (monom_mult (-?ca) ?v (snd (crit_pair f1 f2)))"
          by (rule cbelow_on_monom_mult)
        hence "cbelow_on ?A ?ord (monomial (-?ca) t) ?RS
              (monom_mult (-?ca) ?v (fst (crit_pair f1 f2))) (monom_mult (-?ca) ?v (snd (crit_pair f1 f2)))"
          by (simp add: monom_mult_monomial \<open>?v + l = t\<close>)
        with \<open>?ca \<noteq> 0\<close> have "cbelow_on ?A ?ord (monomial ?ca (0 + t)) ?RS
              (monom_mult (-?ca) ?v (fst (crit_pair f1 f2))) (monom_mult (-?ca) ?v (snd (crit_pair f1 f2)))"
          by (rule cbelow_on_monom_mult_monomial)
        hence "cbelow_on ?A ?ord ma ?RS
              (monom_mult (-?ca) ?v (fst (crit_pair f1 f2))) (monom_mult (-?ca) ?v (snd (crit_pair f1 f2)))"
          by (simp add: ma_def)
        with dg assms(2) _ _
        show "cbelow_on ?A ?ord a ?RS b1 b2" unfolding \<open>a = ma + a'\<close> b1 b2
        proof (rule cbelow_on_plus)
          show "a' \<in> ?A"
            by (rule, simp add: a'_def keys_except, erule conjE, intro dgrad_p_setD,
                rule \<open>a \<in> dgrad_p_set d m\<close>)
        next
          show "keys a' \<inter> keys ma = {}" by (simp add: ma_def a'_def keys_except)
        qed
      qed
    qed
  qed fact
qed

corollary crit_pair_cbelow_imp_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  assumes "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m F p q"
  shows "is_Groebner_basis F"
  unfolding is_Groebner_basis_def
proof (rule relation.confluence_implies_ChurchRosser,
      simp only: relation.is_confluent_def relation.is_confluent_on_def, intro ballI allI impI)
  fix a b1 b2
  assume a: "(red F)\<^sup>*\<^sup>* a b1 \<and> (red F)\<^sup>*\<^sup>* a b2"
  from assms(2) obtain n where "m \<le> n" and "a \<in> dgrad_p_set d n" and "F \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  {
    fix p q
    assume "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
    hence "crit_pair_cbelow_on d m F p q" by (rule assms(3))
    from this dgrad_p_set_subset[OF \<open>m \<le> n\<close>] have "crit_pair_cbelow_on d n F p q"
      unfolding crit_pair_cbelow_on_def by (rule cbelow_on_mono)
  }
  with assms(1) \<open>F \<subseteq> dgrad_p_set d n\<close> have "relation.is_confluent_on (red F) (dgrad_p_set d n)"
    by (rule crit_pair_cbelow_imp_confluent_dgrad_p_set)
  from this \<open>a \<in> dgrad_p_set d n\<close> have "\<forall>b1 b2. (red F)\<^sup>*\<^sup>* a b1 \<and> (red F)\<^sup>*\<^sup>* a b2 \<longrightarrow> relation.cs (red F) b1 b2"
    unfolding relation.is_confluent_on_def ..
  with a show "relation.cs (red F) b1 b2" by blast
qed

corollary Buchberger_criterion_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  assumes "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> (red F)\<^sup>*\<^sup>* (spoly p q) 0"
  shows "is_Groebner_basis F"
  using assms(1) assms(2)
proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
  fix p q
  assume "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
  from this(1) this(2) have "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m" using assms(2) by auto
  from assms(1) assms(2) this \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show "crit_pair_cbelow_on d m F p q"
  proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
    from \<open>p \<in> F\<close> \<open>q \<in> F\<close> show "(red F)\<^sup>*\<^sup>* (spoly p q) 0" by (rule assms(3))
  qed
qed

lemmas Buchberger_criterion_finite = Buchberger_criterion_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

lemma (in ordered_powerprod) GB_imp_zero_reducibility:
  assumes "is_Groebner_basis G" and "f \<in> (pideal G)"
  shows "(red G)\<^sup>*\<^sup>* f 0"
proof -
  from in_pideal_srtc[OF \<open>f \<in> (pideal G)\<close>] \<open>is_Groebner_basis G\<close> have "relation.cs (red G) f 0"
    unfolding is_Groebner_basis_def relation.is_ChurchRosser_def by simp
  then obtain s where rfs: "(red G)\<^sup>*\<^sup>* f s" and r0s: "(red G)\<^sup>*\<^sup>* 0 s" unfolding relation.cs_def by auto
  from rtrancl_0[OF r0s] and rfs show ?thesis by simp
qed

lemma (in ordered_powerprod) GB_imp_reducibility:
  assumes "is_Groebner_basis G" and "f \<noteq> 0" and "f \<in> pideal G"
  shows "is_red G f"
  using assms by (meson GB_imp_zero_reducibility is_red_def relation.rtrancl_is_final)

lemma is_Groebner_basis_empty: "is_Groebner_basis {}"
  by (rule Buchberger_criterion_finite, rule, simp)

lemma is_Groebner_basis_singleton: "is_Groebner_basis {f}"
  by (rule Buchberger_criterion_finite, simp, simp add: spoly_same)

subsection \<open>Buchberger's Criteria for Avoiding Useless Pairs\<close>

lemma product_criterion:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> F" and "q \<in> F"
    and "p \<noteq> 0" and "q \<noteq> 0" and "gcs (lp p) (lp q) = 0"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  let ?l = "lcs (lp p) (lp q)"
  define s where "s = monom_mult (- 1 / (lc p * lc q)) 0 (tail p * tail q)"
  from assms(7) have "?l = lp p + lp q"
    by (metis add_cancel_left_left gcs_plus_lcs)
  hence "?l - lp p = lp q" and "?l - lp q = lp p" by simp_all

  from \<open>q \<noteq> 0\<close> have "(red {q})\<^sup>*\<^sup>* (monom_mult (1 / lc p) (lp q) (tail p))
                      (monom_mult (- (1 / lc p) / lc q) 0 (tail p * tail q))"
    by (rule red_monom_mult_lp)
  hence "(red {q})\<^sup>*\<^sup>* (fst (crit_pair p q)) s" by (simp add: crit_pair_def \<open>?l - lp p = lp q\<close> s_def)
  moreover from \<open>q \<in> F\<close> have "{q} \<subseteq> F" by simp
  ultimately have 1: "(red F)\<^sup>*\<^sup>* (fst (crit_pair p q)) s" by (rule red_rtrancl_subset)

  from \<open>p \<noteq> 0\<close> have "(red {p})\<^sup>*\<^sup>* (monom_mult (1 / lc q) (lp p) (tail q))
                      (monom_mult (- (1 / lc q) / lc p) 0 (tail q * tail p))"
    by (rule red_monom_mult_lp)
  hence "(red {p})\<^sup>*\<^sup>* (snd (crit_pair p q)) s"
    by (simp add: crit_pair_def \<open>?l - lp q = lp p\<close> s_def ac_simps)
  moreover from \<open>p \<in> F\<close> have "{p} \<subseteq> F" by simp
  ultimately have 2: "(red F)\<^sup>*\<^sup>* (snd (crit_pair p q)) s" by (rule red_rtrancl_subset)

  note assms(1) assms(2)
  moreover from \<open>p \<in> F\<close> \<open>F \<subseteq> dgrad_p_set d m\<close> have "p \<in> dgrad_p_set d m" ..
  moreover from \<open>q \<in> F\<close> \<open>F \<subseteq> dgrad_p_set d m\<close> have "q \<in> dgrad_p_set d m" ..
  moreover from 1 2 have "relation.cs (red F) (fst (crit_pair p q)) (snd (crit_pair p q))"
    unfolding relation.cs_def by blast
  ultimately show ?thesis by (rule crit_pair_cs_imp_crit_pair_cbelow_on)
qed

lemma chain_criterion:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> F" and "q \<in> F"
    and "p \<noteq> 0" and "q \<noteq> 0" and "lp r adds lcs (lp p) (lp q)"
    and pr: "crit_pair_cbelow_on d m F p r" and rq: "crit_pair_cbelow_on d m F r q"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  let ?A = "dgrad_p_set d m"
  let ?RS = "\<lambda>a b. red F a b \<or> red F b a"
  let ?lpr = "lcs (lp p) (lp r)"
  let ?lrq = "lcs (lp r) (lp q)"
  let ?lpq = "lcs (lp p) (lp q)"

  from \<open>p \<in> F\<close> \<open>F \<subseteq> dgrad_p_set d m\<close> have "p \<in> dgrad_p_set d m" ..
  from this \<open>p \<noteq> 0\<close> have "d (lp p) \<le> m" by (rule dgrad_p_setD_lp)
  from \<open>q \<in> F\<close> \<open>F \<subseteq> dgrad_p_set d m\<close> have "q \<in> dgrad_p_set d m" ..
  from this \<open>q \<noteq> 0\<close> have "d (lp q) \<le> m" by (rule dgrad_p_setD_lp)
  from assms(1) have "d ?lpq \<le> ord_class.max (d (lp p)) (d (lp q))" by (rule dickson_grading_lcs)
  also from \<open>d (lp p) \<le> m\<close> \<open>d (lp q) \<le> m\<close> have "... \<le> m" by simp
  finally have "d ?lpq \<le> m" .

  from adds_lcs \<open>lp r adds ?lpq\<close> have "?lpr adds ?lpq" by (rule lcs_adds)
  then obtain up where "?lpq = ?lpr + up" ..
  hence up1: "?lpq - lp p = up + (?lpr - lp p)" and up2: "up + (?lpr - lp r) = ?lpq - lp r"
    by (metis add.commute adds_lcs minus_plus, metis add.commute adds_lcs_2 minus_plus)
  have fst_pq: "fst (crit_pair p q) = monom_mult 1 up (fst (crit_pair p r))"
    by (simp add: crit_pair_def monom_mult_assoc up1)
  from assms(1) assms(2) _ _ pr have "cbelow_on ?A (\<prec>p) (monom_mult 1 up (monomial 1 ?lpr)) ?RS
                                    (fst (crit_pair p q)) (monom_mult 1 up (snd (crit_pair p r)))"
    unfolding fst_pq crit_pair_cbelow_on_def
  proof (rule cbelow_on_monom_mult)
    from \<open>d ?lpq \<le> m\<close> show "d up \<le> m" by (simp add: \<open>?lpq = ?lpr + up\<close> dickson_gradingD1[OF assms(1)])
  qed simp
  hence 1: "cbelow_on ?A (\<prec>p) (monomial 1 ?lpq) ?RS (fst (crit_pair p q)) (monom_mult 1 up (snd (crit_pair p r)))"
    by (simp add: monom_mult_monomial \<open>?lpq = ?lpr + up\<close> add.commute)

  from \<open>lp r adds ?lpq\<close> adds_lcs_2 have "?lrq adds ?lpq" by (rule lcs_adds)
  then obtain uq where "?lpq = ?lrq + uq" ..
  hence uq1: "?lpq - lp q = uq + (?lrq - lp q)" and uq2: "uq + (?lrq - lp r) = ?lpq - lp r"
    by (metis add.commute adds_lcs_2 minus_plus, metis add.commute adds_lcs minus_plus)
  have eq: "monom_mult 1 uq (fst (crit_pair r q)) = monom_mult 1 up (snd (crit_pair p r))"
    by (simp add: crit_pair_def monom_mult_assoc up2 uq2)
  have snd_pq: "snd (crit_pair p q) = monom_mult 1 uq (snd (crit_pair r q))"
    by (simp add: crit_pair_def monom_mult_assoc uq1)
  from assms(1) assms(2) _ _ rq have "cbelow_on ?A (\<prec>p) (monom_mult 1 uq (monomial 1 ?lrq)) ?RS
                                    (monom_mult 1 uq (fst (crit_pair r q))) (snd (crit_pair p q))"
    unfolding snd_pq crit_pair_cbelow_on_def
  proof (rule cbelow_on_monom_mult)
    from \<open>d ?lpq \<le> m\<close> show "d uq \<le> m" by (simp add: \<open>?lpq = ?lrq + uq\<close> dickson_gradingD1[OF assms(1)])
  qed simp
  hence "cbelow_on ?A (\<prec>p) (monomial 1 ?lpq) ?RS (monom_mult 1 uq (fst (crit_pair r q))) (snd (crit_pair p q))"
    by (simp add: monom_mult_monomial \<open>?lpq = ?lrq + uq\<close> add.commute)
  hence "cbelow_on ?A (\<prec>p) (monomial 1 ?lpq) ?RS (monom_mult 1 up (snd (crit_pair p r))) (snd (crit_pair p q))"
    by (simp only: eq)
  
  with 1 show ?thesis unfolding crit_pair_cbelow_on_def by (rule cbelow_on_transitive)
qed

subsection \<open>Weak and Strong Gr\"obner Bases\<close>

lemma ord_p_wf_on:
  assumes "dickson_grading (+) d"
  shows "wfP_on (dgrad_p_set d m) (\<prec>p)"
proof (rule wfP_onI_min)
  fix x::"'a \<Rightarrow>\<^sub>0 'b" and Q
  assume "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
  with assms obtain z where "z \<in> Q" and *: "\<And>y. y \<prec>p z \<Longrightarrow> y \<notin> Q"
    by (rule ord_p_minimum_dgrad_p_set, blast)
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_p_set d m. y \<prec>p z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>dgrad_p_set d m. y \<prec>p z \<longrightarrow> y \<notin> Q" by (intro ballI impI *)
  qed
qed

(* TODO: Collect all "_dgrad_p_set"-facts in a locale? *)
lemma is_red_implies_0_red_dgrad_p_set:
  assumes "dickson_grading (+) d" and "B \<subseteq> dgrad_p_set d m"
  assumes "pideal B \<subseteq> pideal A" and major: "\<And>q. q \<in> pideal A \<Longrightarrow> q \<in> dgrad_p_set d m \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> is_red B q"
    and in_ideal: "p \<in> pideal A" and "p \<in> dgrad_p_set d m"
  shows "(red B)\<^sup>*\<^sup>* p 0"
proof -
  from ord_p_wf_on[OF assms(1)] assms(6) in_ideal show ?thesis
  proof (induction p rule: wfP_on_induct)
    case (step p)
    show ?case
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      from major[OF step(3) step(1) False] obtain q where redpq: "red B p q" unfolding is_red_alt ..
      with assms(1) assms(2) step(1) have "q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red)
      moreover from redpq have "q \<prec>p p" by (rule red_ord)
      moreover from \<open>pideal B \<subseteq> pideal A\<close> \<open>p \<in> pideal A\<close> \<open>red B p q\<close> have "q \<in> pideal A"
        by (rule pideal_closed_red)
      ultimately have "(red B)\<^sup>*\<^sup>* q 0" by (rule step(2))
      show ?thesis by (rule converse_rtranclp_into_rtranclp, rule redpq, fact)
    qed
  qed
qed

lemma is_red_implies_0_red_dgrad_p_set':
  assumes "dickson_grading (+) d" and "B \<subseteq> dgrad_p_set d m"
  assumes "pideal B \<subseteq> pideal A" and major: "\<And>q. q \<in> pideal A \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> is_red B q"
    and in_ideal: "p \<in> pideal A"
  shows "(red B)\<^sup>*\<^sup>* p 0"
proof -
  from assms(2) obtain n where "m \<le> n" and "p \<in> dgrad_p_set d n" and B: "B \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  from ord_p_wf_on[OF assms(1)] this(2) in_ideal show ?thesis
  proof (induction p rule: wfP_on_induct)
    case (step p)
    show ?case
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      from major[OF \<open>p \<in> (pideal A)\<close> False] obtain q where redpq: "red B p q" unfolding is_red_alt ..
      with assms(1) B \<open>p \<in> dgrad_p_set d n\<close> have "q \<in> dgrad_p_set d n" by (rule dgrad_p_set_closed_red)
      moreover from redpq have "q \<prec>p p" by (rule red_ord)
      moreover from \<open>pideal B \<subseteq> pideal A\<close> \<open>p \<in> pideal A\<close> \<open>red B p q\<close> have "q \<in> pideal A"
        by (rule pideal_closed_red)
      ultimately have "(red B)\<^sup>*\<^sup>* q 0" by (rule step(2))
      show ?thesis by (rule converse_rtranclp_into_rtranclp, rule redpq, fact)
    qed
  qed
qed

lemma GB_implies_unique_nf_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G"
  shows "\<exists>! h. (red G)\<^sup>*\<^sup>* f h \<and> \<not> is_red G h"
proof -
  from assms(1) assms(2) have "wfP (red G)\<inverse>\<inverse>" by (rule red_wf_dgrad_p_set)
  then obtain h where ftoh: "(red G)\<^sup>*\<^sup>* f h" and irredh: "relation.is_final (red G) h"
    by (rule relation.wf_imp_nf_ex)
  show ?thesis
  proof
    from ftoh and irredh show "(red G)\<^sup>*\<^sup>* f h \<and> \<not> is_red G h" by (simp add: is_red_def)
  next
    fix h'
    assume "(red G)\<^sup>*\<^sup>* f h' \<and> \<not> is_red G h'"
    hence ftoh': "(red G)\<^sup>*\<^sup>* f h'" and irredh': "relation.is_final (red G) h'" by (simp_all add: is_red_def)
    show "h' = h"
    proof (rule relation.ChurchRosser_unique_final)
      from isGB show "relation.is_ChurchRosser (red G)" by (simp only: is_Groebner_basis_def)
    qed fact+
  qed
qed

lemma translation_property':
  assumes "p \<noteq> 0" and red_p_0: "(red F)\<^sup>*\<^sup>* p 0"
  shows "is_red F (p + q) \<or> is_red F q"
proof (rule disjCI)
  assume not_red: "\<not> is_red F q"
  from red_p_0 \<open>p \<noteq> 0\<close> obtain f where "f \<in> F" and "f \<noteq> 0" and lp_adds: "lp f adds lp p"
    by (rule zero_reducibility_implies_lp_divisibility)
  show "is_red F (p + q)"
  proof (cases "q = 0")
    case True
    with is_red_indI1[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> \<open>p \<noteq> 0\<close> lp_adds] show ?thesis by simp
  next
    case False
    from not_red is_red_addsI[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> _ lp_adds, of q] have "\<not> lp p \<in> (keys q)" by blast
    hence "lookup q (lp p) = 0" by simp
    with lp_in_keys[OF \<open>p \<noteq> 0\<close>] have "lp p \<in> (keys (p + q))" unfolding in_keys_iff by (simp add: lookup_add)
    from is_red_addsI[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> this lp_adds] show ?thesis .
  qed
qed
  
lemma translation_property:
  assumes "p \<noteq> q" and red_0: "(red F)\<^sup>*\<^sup>* (p - q) 0"
  shows "is_red F p \<or> is_red F q"
proof -
  from \<open>p \<noteq> q\<close> have "p - q \<noteq> 0" by simp
  from translation_property'[OF this red_0, of q] show ?thesis by simp
qed

lemma weak_GB_is_strong_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes "\<And>f. f \<in> pideal G \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> (red G)\<^sup>*\<^sup>* f 0"
  shows "is_Groebner_basis G"
  using assms(1, 2)
proof (rule Buchberger_criterion_dgrad_p_set)
  fix p q
  assume "p \<in> G" and "q \<in> G"
  show "(red G)\<^sup>*\<^sup>* (spoly p q) 0"
  proof (rule assms(3))
    show "spoly p q \<in> pideal G" unfolding spoly_def
      by (rule pideal_closed_minus, (rule pideal_closed_monom_mult, rule generator_in_pideal, fact)+)
  next
    note assms(1)
    moreover from \<open>p \<in> G\<close> assms(2) have "p \<in> dgrad_p_set d m" ..
    moreover from \<open>q \<in> G\<close> assms(2) have "q \<in> dgrad_p_set d m" ..
    ultimately show "spoly p q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_spoly)
  qed
qed

lemma weak_GB_is_strong_GB:
  assumes "\<And>f. f \<in> (pideal G) \<Longrightarrow> (red G)\<^sup>*\<^sup>* f 0"
  shows "is_Groebner_basis G"
  unfolding is_Groebner_basis_def
proof (rule relation.confluence_implies_ChurchRosser,
      simp add: relation.is_confluent_def relation.is_confluent_on_def, intro allI impI, erule conjE)
  fix f p q
  assume "(red G)\<^sup>*\<^sup>* f p" and "(red G)\<^sup>*\<^sup>* f q"
  hence "relation.srtc (red G) p q"
    by (meson relation.rtc_implies_srtc relation.srtc_symmetric relation.srtc_transitive)
  hence "p - q \<in> pideal G" by (rule srtc_in_pideal)
  hence "(red G)\<^sup>*\<^sup>* (p - q) 0" by (rule assms)
  thus "relation.cs (red G) p q" by (rule red_diff_rtrancl_cs)
qed

corollary GB_alt_1_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pideal G. f \<in> dgrad_p_set d m \<longrightarrow> (red G)\<^sup>*\<^sup>* f 0)"
  using weak_GB_is_strong_GB_dgrad_p_set[OF assms] GB_imp_zero_reducibility by blast

corollary GB_alt_1: "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pideal G. (red G)\<^sup>*\<^sup>* f 0)"
  using weak_GB_is_strong_GB GB_imp_zero_reducibility by blast

lemma isGB_I_is_red:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes "\<And>f. f \<in> pideal G \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> is_red G f"
  shows "is_Groebner_basis G"
  unfolding GB_alt_1_dgrad_p_set[OF assms(1, 2)]
proof (intro ballI impI)
  fix f
  assume "f \<in> pideal G" and "f \<in> dgrad_p_set d m"
  with assms(1, 2) subset_refl assms(3) show "(red G)\<^sup>*\<^sup>* f 0"
    by (rule is_red_implies_0_red_dgrad_p_set)
qed

lemma GB_alt_2_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pideal G. f \<noteq> 0 \<longrightarrow> is_red G f)"
proof
  assume "is_Groebner_basis G"
  show "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
  proof (intro ballI, intro impI)
    fix f
    assume "f \<in> (pideal G)" and "f \<noteq> 0"
    show "is_red G f" by (rule GB_imp_reducibility, fact+)
  qed
next
  assume a2: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
  show "is_Groebner_basis G" unfolding GB_alt_1
  proof
    fix f
    assume "f \<in> pideal G"
    from assms show "(red G)\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red_dgrad_p_set')
      fix q
      assume "q \<in> pideal G" and "q \<noteq> 0"
      thus "is_red G q" by (rule a2[rule_format])
    qed (fact subset_refl, fact)
  qed
qed
  
lemma GB_adds_lp:
  assumes "is_Groebner_basis G" and "f \<in> pideal G" and "f \<noteq> 0"
  obtains g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f"
proof -
  from assms(1) assms(2) have "(red G)\<^sup>*\<^sup>* f 0" by (rule GB_imp_zero_reducibility)
  show ?thesis by (rule zero_reducibility_implies_lp_divisibility, fact+)
qed

lemma isGB_I_adds_lp:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes "\<And>f. f \<in> pideal G \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp f)"
  shows "is_Groebner_basis G"
  using assms(1, 2)
proof (rule isGB_I_is_red)
  fix f
  assume "f \<in> pideal G" and "f \<in> dgrad_p_set d m" and "f \<noteq> 0"
  hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp f)" by (rule assms(3))
  then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by blast
  thus "is_red G f" using \<open>f \<noteq> 0\<close> is_red_indI1 by blast
qed

lemma GB_alt_3_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp f))"
    (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof (intro ballI impI)
    fix f
    assume "f \<in> pideal G" and "f \<noteq> 0"
    with \<open>?L\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by (rule GB_adds_lp)
    thus "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f" by blast
  qed
next
  assume ?R
  show ?L unfolding GB_alt_2_dgrad_p_set[OF assms]
  proof (intro ballI impI)
    fix f
    assume "f \<in> pideal G" and "f \<noteq> 0"
    with \<open>?R\<close> have "(\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp f)" by blast
    then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by blast
    thus "is_red G f" using \<open>f \<noteq> 0\<close> is_red_indI1 by blast
  qed
qed
  
lemma GB_insert:
  assumes "is_Groebner_basis G" and "f \<in> pideal G"
  shows "is_Groebner_basis (insert f G)"
  using assms by (metis GB_alt_1 GB_imp_zero_reducibility pideal_insert red_rtrancl_subset subset_insertI)

lemma GB_subset:
  assumes "is_Groebner_basis G" and "G \<subseteq> G'" and "pideal G' = pideal G"
  shows "is_Groebner_basis G'"
  using assms(1) unfolding GB_alt_1 using assms(2) assms(3) red_rtrancl_subset by blast

lemma (in ordered_powerprod) GB_remove_0_stable_GB:
  assumes "is_Groebner_basis G"
  shows "is_Groebner_basis (G - {0})"
  using assms by (simp only: is_Groebner_basis_def red_minus_singleton_zero)

lemmas is_red_implies_0_red_finite = is_red_implies_0_red_dgrad_p_set'[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_implies_unique_nf_finite = GB_implies_unique_nf_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_alt_2_finite = GB_alt_2_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_alt_3_finite = GB_alt_3_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

subsection \<open>Replacing Elements in Gr\"obner Bases\<close>

lemma replace_in_dgrad_p_set:
  assumes "G \<subseteq> dgrad_p_set d m"
  obtains n where "q \<in> dgrad_p_set d n" and "G \<subseteq> dgrad_p_set d n"
    and "insert q (G - {p}) \<subseteq> dgrad_p_set d n"
proof -
  from assms obtain n where "m \<le> n" and 1: "q \<in> dgrad_p_set d n" and 2: "G \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  from this(2, 3) have "insert q (G - {p}) \<subseteq> dgrad_p_set d n" by auto
  with 1 2 show ?thesis ..
qed

lemma GB_replace_lp_adds_stable_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and q: "q \<in> (pideal G)" and "lp q adds lp p"
  shows "is_Groebner_basis (insert q (G - {p}))" (is "is_Groebner_basis ?G'")
proof -
  from assms(2) obtain n where 1: "G \<subseteq> dgrad_p_set d n" and 2: "?G' \<subseteq> dgrad_p_set d n"
    by (rule replace_in_dgrad_p_set)
  from isGB show ?thesis unfolding GB_alt_3_dgrad_p_set[OF assms(1) 1] GB_alt_3_dgrad_p_set[OF assms(1) 2]
  proof (intro ballI impI)
    fix f
    assume f1: "f \<in> (pideal ?G')" and "f \<noteq> 0"
      and a1: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
    from f1 replace_pideal[OF q, of p] have "f \<in> pideal G" ..
    from a1[rule_format, OF this \<open>f \<noteq> 0\<close>] obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp f" by auto
    show "\<exists>g\<in>?G'. g \<noteq> 0 \<and> lp g adds lp f"
    proof (cases "g = p")
      case True
      show ?thesis
      proof
        from \<open>lp q adds lp p\<close> have "lp q adds lp g" unfolding True .
        also have "... adds lp f" by fact
        finally have "lp q adds lp f" .
        with \<open>q \<noteq> 0\<close> show "q \<noteq> 0 \<and> lp q adds lp f" ..
      next
        show "q \<in> ?G'" by simp
      qed
    next
      case False
      show ?thesis
      proof
        show "g \<noteq> 0 \<and> lp g adds lp f" by (rule, fact+)
      next
        from \<open>g \<in> G\<close> False show "g \<in> ?G'" by blast
      qed
    qed
  qed
qed
  
lemma GB_replace_lp_adds_stable_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "q \<noteq> 0" and "q \<in> pideal G" and "lp q adds lp p"
  shows "pideal (insert q (G - {p})) = pideal G" (is "pideal ?G' = pideal G")
proof (rule, rule replace_pideal, fact, rule)
  fix f
  assume "f \<in> pideal G"
  note assms(1)
  moreover from assms(2) obtain n where "?G' \<subseteq> dgrad_p_set d n" by (rule replace_in_dgrad_p_set)
  moreover have "is_Groebner_basis ?G'" by (rule GB_replace_lp_adds_stable_GB_dgrad_p_set, fact+)
  ultimately have "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf_dgrad_p_set)
  then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
  have "\<not> is_red G h"
  proof
    assume "is_red G h"
    have "is_red ?G' h" by (rule replace_lp_adds_stable_is_red, fact+)
    with irredh show False ..
  qed
  have "f - h \<in> pideal ?G'" by (rule red_rtranclp_diff_in_pideal, rule ftoh)
  have "f - h \<in> pideal G" by (rule, fact, rule replace_pideal, fact)
  from pideal_closed_minus[OF this \<open>f \<in> pideal G\<close>] have "-h \<in> pideal G" by simp
  from pideal_closed_uminus[OF this] have "h \<in> pideal G" by simp
  with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_imp_reducibility by auto
  with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
  thus "f \<in> pideal ?G'" by (simp add: red_rtranclp_0_in_pideal)
qed
  
lemma GB_replace_red_stable_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and q: "red (G - {p}) p q"
  shows "is_Groebner_basis (insert q (G - {p}))" (is "is_Groebner_basis ?G'")
proof -
  from assms(2) obtain n where 1: "G \<subseteq> dgrad_p_set d n" and 2: "?G' \<subseteq> dgrad_p_set d n"
    by (rule replace_in_dgrad_p_set)
  from isGB show ?thesis unfolding GB_alt_2_dgrad_p_set[OF assms(1) 1] GB_alt_2_dgrad_p_set[OF assms(1) 2]
  proof (intro ballI impI)
    fix f
    assume f1: "f \<in> (pideal ?G')" and "f \<noteq> 0"
      and a1: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> is_red G f"
    have "q \<in> pideal G"
    proof (rule pideal_closed_red, rule pideal_mono)
      from generator_subset_pideal \<open>p \<in> G\<close> show "p \<in> pideal G" ..
    next
      show "G - {p} \<subseteq> G" by (rule Diff_subset)
    qed (rule q)
    from f1 replace_pideal[OF this, of p] have "f \<in> pideal G" ..
    have "is_red G f" by (rule a1[rule_format], fact+)
    show "is_red ?G' f" by (rule replace_red_stable_is_red, fact+)
  qed
qed

lemma GB_replace_red_stable_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "red (G - {p}) p q"
  shows "pideal (insert q (G - {p})) = pideal G" (is "pideal ?G' = _")
proof -
  from \<open>p \<in> G\<close> generator_subset_pideal have "p \<in> pideal G" ..
  have "q \<in> pideal G"
    by (rule pideal_closed_red, rule pideal_mono, rule Diff_subset, rule \<open>p \<in> pideal G\<close>, rule ptoq)
  show ?thesis
  proof (rule, rule replace_pideal, fact, rule)
    fix f
    assume "f \<in> pideal G"
    note assms(1)
    moreover from assms(2) obtain n where "?G' \<subseteq> dgrad_p_set d n" by (rule replace_in_dgrad_p_set)
    moreover have "is_Groebner_basis ?G'" by (rule GB_replace_red_stable_GB_dgrad_p_set, fact+)
    ultimately have "\<exists>! h. (red ?G')\<^sup>*\<^sup>* f h \<and> \<not> is_red ?G' h" by (rule GB_implies_unique_nf_dgrad_p_set)
    then obtain h where ftoh: "(red ?G')\<^sup>*\<^sup>* f h" and irredh: "\<not> is_red ?G' h" by auto
    have "\<not> is_red G h"
    proof
      assume "is_red G h"
      have "is_red ?G' h" by (rule replace_red_stable_is_red, fact+)
      with irredh show False ..
    qed
    have "f - h \<in> pideal ?G'" by (rule red_rtranclp_diff_in_pideal, rule ftoh)
    have "f - h \<in> pideal G" by (rule, fact, rule replace_pideal, fact)
    from pideal_closed_minus[OF this \<open>f \<in> pideal G\<close>] have "-h \<in> pideal G" by simp
    from pideal_closed_uminus[OF this] have "h \<in> pideal G" by simp
    with isGB \<open>\<not> is_red G h\<close> have "h = 0" using GB_imp_reducibility by auto
    with ftoh have "(red ?G')\<^sup>*\<^sup>* f 0" by simp
    thus "f \<in> pideal ?G'" by (simp add: red_rtranclp_0_in_pideal)
  qed
qed
  
lemma GB_replace_red_rtranclp_stable_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (G - {p}))\<^sup>*\<^sup>* p q"
  shows "is_Groebner_basis (insert q (G - {p}))"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from isGB \<open>p \<in> G\<close> show ?case by (simp add: insert_absorb)
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    from assms(1) assms(2) isGB \<open>p \<in> G\<close> show ?thesis
    proof (rule GB_replace_red_stable_GB_dgrad_p_set)
      from \<open>red (G - {p}) y z\<close> show "red (G - {p}) p z" unfolding True .
    qed
  next
    case False
    show ?thesis
      proof (cases "y \<in> G")
        case True
        with \<open>y \<noteq> p\<close> have "y \<in> G - {p}" (is "_ \<in> ?G'") by blast
        hence "insert y (G - {p}) = ?G'" by auto
        with step(3) have "is_Groebner_basis ?G'" by simp
        from \<open>y \<in> ?G'\<close> generator_subset_pideal have "y \<in> pideal ?G'" ..
        have "z \<in> pideal ?G'" by (rule pideal_closed_red, rule subset_refl, fact+)
        show "is_Groebner_basis (insert z ?G')" by (rule GB_insert, fact+)
      next
        case False
        from assms(2) obtain n where "insert y (G - {p}) \<subseteq> dgrad_p_set d n"
            by (rule replace_in_dgrad_p_set)
        from assms(1) this step(3) have "is_Groebner_basis (insert z (insert y (G - {p}) - {y}))"
        proof (rule GB_replace_red_stable_GB_dgrad_p_set)
          from \<open>red (G - {p}) y z\<close> False show "red ((insert y (G - {p})) - {y}) y z" by simp
        qed simp
        moreover from False have "... = (insert z (G - {p}))" by simp
        ultimately show ?thesis by simp
      qed
  qed
qed

lemma GB_replace_red_rtranclp_stable_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  assumes isGB: "is_Groebner_basis G" and "p \<in> G" and ptoq: "(red (G - {p}))\<^sup>*\<^sup>* p q"
  shows "pideal (insert q (G - {p})) = pideal G"
  using ptoq
proof (induct q rule: rtranclp_induct)
  case base
  from \<open>p \<in> G\<close> show ?case by (simp add: insert_absorb)
next
  case (step y z)
  show ?case
  proof (cases "y = p")
    case True
    from assms(1) assms(2) isGB \<open>p \<in> G\<close> step(2) show ?thesis unfolding True
      by (rule GB_replace_red_stable_pideal_dgrad_p_set)
  next
    case False
    have gb: "is_Groebner_basis (insert y (G - {p}))"
      by (rule GB_replace_red_rtranclp_stable_GB_dgrad_p_set, fact+)
    show ?thesis
    proof (cases "y \<in> G")
      case True
      with \<open>y \<noteq> p\<close> have "y \<in> G - {p}" (is "_ \<in> ?G'") by blast
      hence eq: "insert y ?G' = ?G'" by auto
      from \<open>y \<in> ?G'\<close> generator_subset_pideal have "y \<in> pideal ?G'" ..
      have "z \<in> pideal ?G'" by (rule pideal_closed_red, rule subset_refl, fact+)
      hence "pideal (insert z ?G') = pideal ?G'" by (rule pideal_insert)
      also from step(3) have "... = pideal G" by (simp only: eq)
      finally show ?thesis .
    next
      case False
      from assms(2) obtain n where 1: "insert y (G - {p}) \<subseteq> dgrad_p_set d n"
        by (rule replace_in_dgrad_p_set)
      from False have "pideal (insert z (G - {p})) = pideal (insert z (insert y (G - {p}) - {y}))"
        by auto
      also from assms(1) 1 gb have "... = pideal (insert y (G - {p}))"
      proof (rule GB_replace_red_stable_pideal_dgrad_p_set)
        from step(2) False show "red ((insert y (G - {p})) - {y}) y z" by simp
      qed simp
      also have "... = pideal G" by fact
      finally show ?thesis .
    qed
  qed
qed

lemmas GB_replace_lp_adds_stable_GB_finite =
  GB_replace_lp_adds_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_lp_adds_stable_pideal_finite =
  GB_replace_lp_adds_stable_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_stable_GB_finite =
  GB_replace_red_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_stable_pideal_finite =
  GB_replace_red_stable_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_rtranclp_stable_GB_finite =
  GB_replace_red_rtranclp_stable_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_replace_red_rtranclp_stable_pideal_finite =
  GB_replace_red_rtranclp_stable_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

subsection \<open>An Inconstructive Proof of the Existence of Finite Gr\"obner Bases\<close>

lemma ex_finite_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  obtains G where "G \<subseteq> dgrad_p_set d m" and "finite G" and "is_Groebner_basis G" and "pideal G = pideal F"
proof -
  define S where "S = {lp f | f. f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0}"
  have "S \<subseteq> dgrad_set d m"
  proof
    fix s
    assume "s \<in> S"
    then obtain f where "f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0" and "s = lp f"
      unfolding S_def by blast
    from this(1) have "f \<in> dgrad_p_set d m" and "f \<noteq> 0" by simp_all
    from this(2) have "s \<in> keys f" unfolding \<open>s = lp f\<close> by (rule lp_in_keys)
    with \<open>f \<in> dgrad_p_set d m\<close> have "d s \<le> m" by (rule dgrad_p_setD)
    thus "s \<in> dgrad_set d m" by (simp add: dgrad_set_def)
  qed
  with assms(1) obtain T where "finite T" and "T \<subseteq> S" and *: "\<And>s. s \<in> S \<Longrightarrow> (\<exists>t\<in>T. t adds s)"
    by (rule ex_finite_adds, blast)
  define crit where "crit = (\<lambda>t f. f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0 \<and> t = lp f)"
  have ex_crit: "t \<in> T \<Longrightarrow> (\<exists>f. crit t f)" for t
  proof -
    assume "t \<in> T"
    from this \<open>T \<subseteq> S\<close> have "t \<in> S" ..
    then obtain f where "f \<in> pideal F \<and> f \<in> dgrad_p_set d m \<and> f \<noteq> 0" and "t = lp f"
      unfolding S_def by blast
    thus "\<exists>f. crit t f" unfolding crit_def by blast
  qed
  define G where "G = (\<lambda>t. SOME g. crit t g) ` T"
  have G: "g \<in> G \<Longrightarrow> g \<in> pideal F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" for g
  proof -
    assume "g \<in> G"
    then obtain t where "t \<in> T" and g: "g = (SOME h. crit t h)" unfolding G_def ..
    have "crit t g" unfolding g by (rule someI_ex, rule ex_crit, fact)
    thus "g \<in> pideal F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" by (simp add: crit_def)
  qed
  have **: "t \<in> T \<Longrightarrow> (\<exists>g\<in>G. lp g = t)" for t
  proof -
    assume "t \<in> T"
    define g where "g = (SOME h. crit t h)"
    from \<open>t \<in> T\<close> have "g \<in> G" unfolding g_def G_def by blast
    thus "\<exists>g\<in>G. lp g = t"
    proof
      have "crit t g" unfolding g_def by (rule someI_ex, rule ex_crit, fact)
      thus "lp g = t" by (simp add: crit_def)
    qed
  qed
  have adds: "f \<in> pideal F \<Longrightarrow> f \<in> dgrad_p_set d m \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)" for f
  proof -
    assume "f \<in> pideal F" and "f \<in> dgrad_p_set d m" and "f \<noteq> 0"
    hence "lp f \<in> S" unfolding S_def by blast
    hence "\<exists>t\<in>T. t adds (lp f)" by (rule *)
    then obtain t where "t \<in> T" and "t adds (lp f)" ..
    from this(1) have "\<exists>g\<in>G. lp g = t" by (rule **)
    then obtain g where "g \<in> G" and "lp g = t" ..
    show "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f"
    proof (intro bexI conjI)
      from G[OF \<open>g \<in> G\<close>] show "g \<noteq> 0" by (elim conjE)
    next
      from \<open>t adds lp f\<close> show "lp g adds lp f" by (simp only: \<open>lp g = t\<close>)
    qed fact
  qed
  have sub1: "pideal G \<subseteq> pideal F"
  proof (rule pideal_subset_pidealI, rule)
    fix g
    assume "g \<in> G"
    from G[OF this] show "g \<in> pideal F" ..
  qed
  have sub2: "G \<subseteq> dgrad_p_set d m"
  proof
    fix g
    assume "g \<in> G"
    from G[OF this] show "g \<in> dgrad_p_set d m" by (elim conjE)
  qed
  show ?thesis
  proof
    from \<open>finite T\<close> show "finite G" unfolding G_def ..
  next
    from assms(1) sub2 adds show "is_Groebner_basis G"
    proof (rule isGB_I_adds_lp)
      fix f
      assume "f \<in> pideal G"
      from this sub1 show "f \<in> pideal F" ..
    qed
  next
    show "pideal G = pideal F"
    proof
      show "pideal F \<subseteq> pideal G"
      proof (rule pideal_subset_pidealI, rule)
        fix f
        assume "f \<in> F"
        hence "f \<in> pideal F" by (rule generator_in_pideal)
        from \<open>f \<in> F\<close> assms(2) have "f \<in> dgrad_p_set d m" ..
        with assms(1) sub2 sub1 _ \<open>f \<in> pideal F\<close> have "(red G)\<^sup>*\<^sup>* f 0"
        proof (rule is_red_implies_0_red_dgrad_p_set)
          fix q
          assume "q \<in> pideal F" and "q \<in> dgrad_p_set d m" and "q \<noteq> 0"
          hence "(\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp q)" by (rule adds)
          then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp q" by blast
          thus "is_red G q" using \<open>q \<noteq> 0\<close> is_red_indI1 by blast
        qed
        thus "f \<in> pideal G" by (rule red_rtranclp_0_in_pideal)
      qed
    qed fact
  next
    show "G \<subseteq> dgrad_p_set d m"
    proof
      fix g
      assume "g \<in> G"
      hence "g \<in> pideal F \<and> g \<in> dgrad_p_set d m \<and> g \<noteq> 0" by (rule G)
      thus "g \<in> dgrad_p_set d m" by (elim conjE)
    qed
  qed
qed

text \<open>The preceding lemma justifies the following definition.\<close>

definition some_GB :: "('a \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) set"
  where "some_GB F = (SOME G. finite G \<and> is_Groebner_basis G \<and> pideal G = pideal F)"

lemma some_GB_props_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "finite (some_GB F) \<and> is_Groebner_basis (some_GB F) \<and> pideal (some_GB F) = pideal F"
proof -
  from assms obtain G where "finite G" and "is_Groebner_basis G" and "pideal G = pideal F"
    by (rule ex_finite_GB_dgrad_p_set)
  hence "finite G \<and> is_Groebner_basis G \<and> pideal G = pideal F" by simp
  thus "finite (some_GB F) \<and> is_Groebner_basis (some_GB F) \<and> pideal (some_GB F) = pideal F"
    unfolding some_GB_def by (rule someI)
qed

lemma finite_some_GB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "finite (some_GB F)"
  using some_GB_props_dgrad_p_set[OF assms] ..

lemma some_GB_isGB_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis (some_GB F)"
  using some_GB_props_dgrad_p_set[OF assms] by (elim conjE)

lemma some_GB_pideal_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "pideal (some_GB F) = pideal F"
  using some_GB_props_dgrad_p_set[OF assms] by (elim conjE)

lemmas finite_some_GB_finite = finite_some_GB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas some_GB_isGB_finite = some_GB_isGB_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas some_GB_pideal_finite = some_GB_pideal_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

text \<open>Theory \<open>Buchberger_Algorithm\<close> implements an algorithm for effectively computing Gr\"obner bases.\<close>

subsection \<open>Relation @{term red_supset}\<close>

text \<open>The following relation is needed for proving the termination of Buchberger's algorithm (i.e.
  function @{term gbaux}).\<close>

definition red_supset::"('a, 'b::field) poly_mapping set \<Rightarrow> ('a, 'b) poly_mapping set \<Rightarrow> bool" (infixl "\<sqsupset>p" 50)
  where "red_supset A B \<equiv> (\<exists>p. is_red A p \<and> \<not> is_red B p) \<and> (\<forall>p. is_red B p \<longrightarrow> is_red A p)"

lemma red_supsetE:
  assumes "A \<sqsupset>p B"
  obtains p where "is_red A p" and "\<not> is_red B p"
proof -
  from assms have "\<exists>p. is_red A p \<and> \<not> is_red B p" by (simp add: red_supset_def)
  from this obtain p where "is_red A p" and " \<not> is_red B p" by auto
  thus ?thesis ..
qed

lemma red_supsetD:
  assumes a1: "A \<sqsupset>p B" and a2: "is_red B p"
  shows "is_red A p"
proof -
  from assms have "\<forall>p. is_red B p \<longrightarrow> is_red A p" by (simp add: red_supset_def)
  hence "is_red B p \<longrightarrow> is_red A p" ..
  from a2 this show ?thesis by simp
qed

lemma red_supsetI [intro]:
  assumes "\<And>q. is_red B q \<Longrightarrow> is_red A q" and "is_red A p" and "\<not> is_red B p"
  shows "A \<sqsupset>p B"
  unfolding red_supset_def using assms by auto

lemma red_supset_insertI:
  assumes "x \<noteq> 0" and "\<not> is_red A x"
  shows "(insert x A) \<sqsupset>p A"
proof
  fix q
  assume "is_red A q"
  thus "is_red (insert x A) q" unfolding is_red_alt
  proof
    fix a
    assume "red A q a"
    from red_unionI2[OF this, of "{x}"] have "red (insert x A) q a" by simp
    show "\<exists>qa. red (insert x A) q qa"
    proof
      show "red (insert x A) q a" by fact
    qed
  qed
next
  show "is_red (insert x A) x" unfolding is_red_alt
  proof
    from red_unionI1[OF red_self[OF \<open>x \<noteq> 0\<close>], of A] show "red (insert x A) x 0" by simp
  qed
next
  show "\<not> is_red A x" by fact
qed

lemma red_supset_transitive:
  assumes "A \<sqsupset>p B" and "B \<sqsupset>p C"
  shows "A \<sqsupset>p C"
proof -
  from assms(2) obtain p where "is_red B p" and "\<not> is_red C p" by (rule red_supsetE)
  show ?thesis
  proof
    fix q
    assume "is_red C q"
    with assms(2) have "is_red B q" by (rule red_supsetD)
    with assms(1) show "is_red A q" by (rule red_supsetD)
  next
    from assms(1) \<open>is_red B p\<close> show "is_red A p" by (rule red_supsetD)
  qed fact
qed

lemma red_supset_wf_on:
  assumes "dickson_grading (+) d"
  shows "wfP_on (Pow (dgrad_p_set d m)) (\<sqsupset>p)"
proof (rule wfP_on_chain, rule, erule exE)
  let ?A = "dgrad_p_set d m"
  fix f::"nat \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) set)"
  assume "\<forall>i. f i \<in> Pow ?A \<and> f (Suc i) \<sqsupset>p f i"
  hence a1_subset: "f i \<subseteq> ?A" and a1: "f (Suc i) \<sqsupset>p f i" for i by simp_all

  have a1_trans: "i < j \<Longrightarrow> f j \<sqsupset>p f i" for i j
  proof -
    assume "i < j"
    thus "f j \<sqsupset>p f i"
    proof (induct j)
      case 0
      thus ?case by simp
    next
      case (Suc j)
      from Suc(2) have "i = j \<or> i < j" by auto
      thus ?case
      proof
        assume "i = j"
        show ?thesis unfolding \<open>i = j\<close> by (fact a1)
      next
        assume "i < j"
        from a1 have "f (Suc j) \<sqsupset>p f j" .
        also from \<open>i < j\<close> have "... \<sqsupset>p f i" by (rule Suc(1))
        finally(red_supset_transitive) show ?thesis .
      qed
    qed
  qed

  have a2: "\<exists>p \<in> f (Suc i). \<exists>q. is_red {p} q \<and> \<not> is_red (f i) q" for i
  proof -
    from a1 have "f (Suc i) \<sqsupset>p f i" .
    then obtain q where red: "is_red (f (Suc i)) q" and irred: "\<not> is_red (f i) q"
      by (rule red_supsetE)
    from red obtain p where "p \<in> f (Suc i)" and "is_red {p} q" by (rule is_red_singletonI)
    show "\<exists>p\<in>f (Suc i). \<exists>q. is_red {p} q \<and> \<not> is_red (f i) q"
    proof
      show "\<exists>q. is_red {p} q \<and> \<not> is_red (f i) q"
      proof (intro exI, intro conjI)
        show "is_red {p} q" by fact
      qed (fact)
    next
      show "p \<in> f (Suc i)" by fact
    qed
  qed

  let ?P = "\<lambda>i p. p \<in> (f (Suc i)) \<and> (\<exists>q. is_red {p} q \<and> \<not> is_red (f i) q)"
  define g where "g \<equiv> \<lambda>i::nat. (SOME p. ?P i p)"
  have a3: "?P i (g i)" for i
  proof -
    from a2[of i] obtain gi where "gi \<in> f (Suc i)" and "\<exists>q. is_red {gi} q \<and> \<not> is_red (f i) q" ..
    show ?thesis unfolding g_def by (rule someI[of _ gi], intro conjI, fact+)
  qed

  have a4: "i < j \<Longrightarrow> \<not> lp (g i) adds (lp (g j))" for i j
  proof
    assume "i < j" and adds: "lp (g i) adds lp (g j)"
    from a3 have "\<exists>q. is_red {g j} q \<and> \<not> is_red (f j) q" ..
    then obtain q where redj: "is_red {g j} q" and "\<not> is_red (f j) q" by auto
    have *: "\<not> is_red (f (Suc i)) q"
    proof -
      from \<open>i < j\<close> have "i + 1 < j \<or> i + 1 = j" by auto
      thus ?thesis
      proof
        assume "i + 1 < j"
        from red_supsetD[OF a1_trans[rule_format, OF this], of q] \<open>\<not> is_red (f j) q\<close>
          show ?thesis by auto
      next
        assume "i + 1 = j"
        thus ?thesis using \<open>\<not> is_red (f j) q\<close> by simp
      qed
    qed
    from a3 have "g i \<in> f (i + 1)" and redi: "\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q" by simp_all
    have "\<not> is_red {g i} q"
    proof
      assume "is_red {g i} q"
      from is_red_singletonD[OF this \<open>g i \<in> f (i + 1)\<close>] * show False by simp
    qed
    have "g i \<noteq> 0"
    proof -
      from redi obtain q0 where "is_red {g i} q0" by auto
      from is_red_singleton_not_0[OF this] show ?thesis .
    qed
    from \<open>\<not> is_red {g i} q\<close> is_red_singleton_trans[OF redj adds \<open>g i \<noteq> 0\<close>] show False by simp
  qed

  have a5: "d ((lp \<circ> g) i) \<le> m" for i
  proof simp
    from a3 have "g i \<in> f (Suc i)" and "\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q" by simp_all
    from this(2) obtain q where "is_red {g i} q" by auto
    hence "g i \<noteq> 0" by (rule is_red_singleton_not_0)
    from a1_subset \<open>g i \<in> f (Suc i)\<close> have "g i \<in> ?A" ..
    from this \<open>g i \<noteq> 0\<close> show "d (lp (g i)) \<le> m" by (rule dgrad_p_setD_lp)
  qed

  from dickson_gradingE2[OF assms a5, of id] obtain i j where "i < j" and "lp (g i) adds lp (g j)"
    by auto
  from this a4[OF \<open>i < j\<close>] show False by simp
qed

end (* gd_powerprod *)

lemma in_lex_prod_alt:
  "(x, y) \<in> r <*lex*> s \<longleftrightarrow> (((fst x), (fst y)) \<in> r \<or> (fst x = fst y \<and> ((snd x), (snd y)) \<in> s))"
  by (metis in_lex_prod prod.collapse prod.inject surj_pair)

subsection \<open>Context @{locale od_powerprod}\<close>

context od_powerprod
begin

lemmas red_wf = red_wf_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas Buchberger_criterion = Buchberger_criterion_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]

end (* od_powerprod *)

end (* theory *)
