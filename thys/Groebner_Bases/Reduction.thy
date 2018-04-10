(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Polynomial Reduction\<close>

theory Reduction
imports Polynomials.MPoly_Type_Class Confluence
begin

text \<open>This theory formalizes the concept of @{emph \<open>reduction\<close>} of polynomials by polynomials.\<close>

context ordered_powerprod
begin

definition red_single::"('a \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where "red_single p q f t \<longleftrightarrow> (f \<noteq> 0 \<and> lookup p (t + lp f) \<noteq> 0 \<and>
                                q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f)"

definition red::"('a \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "red F p q \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t. red_single p q f t)"

definition is_red::"('a \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "is_red F a \<longleftrightarrow> \<not> relation.is_final (red F) a"

subsection \<open>Basic Properties of Reduction\<close>

lemma red_setI:
  assumes "f \<in> F" and a: "red_single p q f t"
  shows "red F p q"
  unfolding red_def
proof
  from \<open>f \<in> F\<close> show "f \<in> F" .
next
  from a show "\<exists>t. red_single p q f t" ..
qed

lemma red_setE:
  assumes a: "red F p q"
  obtains f::"'a \<Rightarrow>\<^sub>0 'b::field" and t where "f \<in> F" and "red_single p q f t"
proof -
  from a obtain f where "f \<in> F" and t: "\<exists>t. red_single p q f t" unfolding red_def by auto
  from t obtain t where "red_single p q f t" ..
  from \<open>f \<in> F\<close> this show "?thesis" ..
qed

lemma red_empty: "\<not> red {} p q"
  by (rule, elim red_setE, simp)

lemma red_singleton_zero: "\<not> red {0} p q"
  by (rule, elim red_setE, simp add: red_single_def)

lemma red_union: "red (F \<union> G) p q = (red F p q \<or> red G p q)"
proof
  assume "red (F \<union> G) p q"
  from red_setE[OF this] obtain f t where "f \<in> F \<union> G" and r: "red_single p q f t" .
  from \<open>f \<in> F \<union> G\<close> have "f \<in> F \<or> f \<in> G" by simp
  thus "red F p q \<or> red G p q"
  proof
    assume "f \<in> F" 
    show ?thesis by (intro disjI1, rule red_setI[OF \<open>f \<in> F\<close> r])
  next
    assume "f \<in> G" 
    show ?thesis by (intro disjI2, rule red_setI[OF \<open>f \<in> G\<close> r])
  qed
next
  assume "red F p q \<or> red G p q"
  thus "red (F \<union> G) p q"
  proof
    assume "red F p q"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single p q f t" .
    show ?thesis by (intro red_setI[of f _ _ _ t], rule UnI1, rule \<open>f \<in> F\<close>, fact)
  next
    assume "red G p q"
    from red_setE[OF this] obtain f t where "f \<in> G" and "red_single p q f t" .
    show ?thesis by (intro red_setI[of f _ _ _ t], rule UnI2, rule \<open>f \<in> G\<close>, fact)
  qed
qed

lemma red_unionI1:
  assumes "red F p q"
  shows "red (F \<union> G) p q"
  unfolding red_union by (rule disjI1, fact)

lemma red_unionI2:
  assumes "red G p q"
  shows "red (F \<union> G) p q"
  unfolding red_union by (rule disjI2, fact)

lemma red_subset:
  fixes p q::"('a, 'b::field) poly_mapping" and F G::"('a, 'b) poly_mapping set"
  assumes "red G p q" and "G \<subseteq> F"
  shows "red F p q"
proof -
  from \<open>G \<subseteq> F\<close> obtain H where "F = G \<union> H" by auto
  show ?thesis unfolding \<open>F = G \<union> H\<close> by (rule red_unionI1, fact)
qed

lemma red_union_singleton_zero: "red (F \<union> {0}) = red F"
  by (intro ext, simp only: red_union red_singleton_zero, simp)

lemma red_minus_singleton_zero: "red (F - {0}) = red F"
  by (metis Un_Diff_cancel2 red_union_singleton_zero)

lemma red_rtrancl_subset:
  assumes major: "(red G)\<^sup>*\<^sup>* p q" and "G \<subseteq> F"
  shows "(red F)\<^sup>*\<^sup>* p q"
  using major
proof (induct rule: rtranclp_induct)
  show "(red F)\<^sup>*\<^sup>* p p" ..
next
  fix r q
  assume "red G r q" and "(red F)\<^sup>*\<^sup>* p r"
  show "(red F)\<^sup>*\<^sup>* p q"
  proof
    show "(red F)\<^sup>*\<^sup>* p r" by fact
  next
    from red_subset[OF \<open>red G r q\<close> \<open>G \<subseteq> F\<close>] show "red F r q" .
  qed
qed

lemma red_singleton: "red {f} p q \<longleftrightarrow> (\<exists>t. red_single p q f t)"
  unfolding red_def
proof
  assume "\<exists>f\<in>{f}. \<exists>t. red_single p q f t"
  from this obtain f0 where "f0 \<in> {f}" and a: "\<exists>t. red_single p q f0 t" ..
  from \<open>f0 \<in> {f}\<close> have "f0 = f" by simp
  from this a show "\<exists>t. red_single p q f t" by simp
next
  assume a: "\<exists>t. red_single p q f t"
  show "\<exists>f\<in>{f}. \<exists>t. red_single p q f t"
  proof (rule, simp)
    from a show "\<exists>t. red_single p q f t" .
  qed
qed

lemma red_single_lookup:
  assumes "red_single p q f t"
  shows "lookup q (t + lp f) = 0"
  using assms unfolding red_single_def
proof
  assume "f \<noteq> 0" and "lookup p (t + lp f) \<noteq> 0 \<and> q = p - monom_mult (lookup p (t + lp f) / lc f) t f"
  hence "lookup p (t + lp f) \<noteq> 0" and q_def: "q = p - monom_mult (lookup p (t + lp f) / lc f) t f"
    by auto
  from lookup_minus[of p "monom_mult (lookup p (t + lp f) / lc f) t f" "t + lp f"]
       lookup_monom_mult_plus[of "lookup p (t + lp f) / lc f" t f "lp f"]
       lc_not_0[OF \<open>f \<noteq> 0\<close>]
    show ?thesis unfolding q_def lc_def by simp
qed

lemma red_single_higher:
  assumes "red_single p q f t"
  shows "higher q (t + lp f) = higher p (t + lp f)"
  using assms unfolding higher_eq_iff red_single_def
proof (intro allI, intro impI)
  fix s
  assume a: "t + lp f \<prec> s"
    and "f \<noteq> 0 \<and> lookup p (t + lp f) \<noteq> 0 \<and> q = p - monom_mult (lookup p (t + lp f) / lc f) t f"
  hence "f \<noteq> 0"
    and "lookup p (t + lp f) \<noteq> 0"
    and q_def: "q = p - monom_mult (lookup p (t + lp f) / lc f) t f"
    by simp_all
  from \<open>lookup p (t + lp f) \<noteq> 0\<close> lc_not_0[OF \<open>f \<noteq> 0\<close>] have c_not_0: "lookup p (t + lp f) / lc f \<noteq> 0"
    by (simp add: field_simps)
  from q_def lookup_minus[of p "monom_mult (lookup p (t + lp f) / lc f) t f"]
    have q_lookup: "\<And>s. lookup q s = lookup p s - lookup (monom_mult (lookup p (t + lp f) / lc f) t f) s"
    by simp
  from a lp_monom_mult[OF c_not_0 \<open>f \<noteq> 0\<close>, of t]
    have "\<not> s \<preceq> lp (monom_mult (lookup p (t + lp f) / lc f) t f)" by simp
  with lp_max[of "monom_mult (lookup p (t + lp f) / lc f) t f" s]
  have "lookup (monom_mult (lookup p (t + lp f) / lc f) t f) s = 0"
      apply (auto)
      by (metis lookup_not_eq_zero_eq_in_keys)
  thus "lookup q s = lookup p s" using q_lookup[of s] by simp
qed

lemma red_single_ord:
  assumes "red_single p q f t"
  shows "q \<prec>p p"
  unfolding ord_strict_higher
proof (intro exI, intro conjI)
  from red_single_lookup[OF assms] show "lookup q (t + lp f) = 0" .
next
  from assms show "lookup p (t + lp f) \<noteq> 0" unfolding red_single_def by simp
next
  from red_single_higher[OF assms] show "higher q (t + lp f) = higher p (t + lp f)" .
qed

lemma red_single_nonzero1:
  assumes "red_single p q f t"
  shows "p \<noteq> 0"
proof
  assume "p = 0"
  from this red_single_ord[OF assms] ord_p_0_min[of q] show False by simp
qed

lemma red_single_nonzero2:
  assumes "red_single p q f t"
  shows "f \<noteq> 0"
proof
  assume "f = 0"
  from assms monom_mult_right0 have "f \<noteq> 0" unfolding red_single_def by simp
  from this \<open>f = 0\<close> show False by simp
qed

lemma red_single_self:
  assumes "p \<noteq> 0"
  shows "red_single p 0 p 0"
proof -
  from lc_not_0[OF assms] have lc: "lc p \<noteq> 0" .
  show ?thesis unfolding red_single_def
  proof (intro conjI)
    show "p \<noteq> 0" by fact
  next
    from lc show "lookup p (0 + lp p) \<noteq> 0" unfolding lc_def by simp
  next
    from lc have "(lookup p (0 + lp p)) / lc p = 1" unfolding lc_def by simp
    from this monom_mult_left1[of p] show "0 = p - monom_mult (lookup p (0 + lp p) / lc p) 0 p"
      by simp
  qed
qed

lemma red_single_trans:
  assumes "red_single p p0 f t" and "lp g adds lp f" and "g \<noteq> 0"
  obtains p1 where "red_single p p1 g (t + (lp f - lp g))"
proof -
  let ?s = "t + (lp f - lp g)"
  let ?p = "p - monom_mult (lookup p (?s + lp g) / lc g) ?s g"
  have "red_single p ?p g ?s" unfolding red_single_def
  proof (intro conjI)
    from add_minus_2[of "lp g" "lp f"]
    have eq: "t + (lp f - lp g) + lp g = t + lp f"
      apply (auto simp: algebra_simps)
      by (metis add.commute adds_minus assms(2))
    from \<open>red_single p p0 f t\<close> have "lookup p (t + lp f) \<noteq> 0" unfolding red_single_def by simp
    thus "lookup p (t + (lp f - lp g) + lp g) \<noteq> 0" by (simp add: eq)
  qed (fact, simp)
  thus ?thesis ..
qed

lemma red_nonzero:
  assumes "red F p q"
  shows "p \<noteq> 0"
proof -
  from red_setE[OF assms] obtain f t where "red_single p q f t" .
  show ?thesis by (rule red_single_nonzero1, fact)
qed

lemma red_self:
  assumes "p \<noteq> 0"
  shows "red {p} p 0"
unfolding red_singleton
proof
  from red_single_self[OF assms] show "red_single p 0 p 0" .
qed

lemma red_ord:
  assumes "red F p q"
  shows "q \<prec>p p"
proof -
  from red_setE[OF assms] obtain f and t where "red_single p q f t" .
  from red_single_ord[OF this] show "q \<prec>p p" .
qed

lemma red_indI1:
  assumes "f \<in> F" and "f \<noteq> 0" and "p \<noteq> 0" and adds: "lp f adds lp p"
  shows "red F p (p - monom_mult (lc p / lc f) (lp p - lp f) f)"
proof (intro red_setI[OF \<open>f \<in> F\<close>])
  have c: "lookup p (lp p - lp f + lp f) = lc p" unfolding lc_def
    by (metis adds adds_minus)
  show "red_single p (p - monom_mult (lc p / lc f) (lp p - lp f) f) f (lp p - lp f)"
    unfolding red_single_def
  proof (intro conjI, fact)
    from c lc_not_0[OF \<open>p \<noteq> 0\<close>] show "lookup p (lp p - lp f + lp f) \<noteq> 0" by simp
  next
    from c show "p - monom_mult (lc p / lc f) (lp p - lp f) f =
                  p - monom_mult (lookup p (lp p - lp f + lp f) / lc f) (lp p - lp f) f"
      by simp
  qed
qed

lemma red_indI2:
  assumes "p \<noteq> 0" and r: "red F (tail p) q"
  shows "red F p (q + monomial (lc p) (lp p))"
proof -
  from red_setE[OF r] obtain f t where "f \<in> F" and rs: "red_single (tail p) q f t" by auto
  from rs have "f \<noteq> 0" and ct: "lookup (tail p) (t + lp f) \<noteq> 0"
    and q: "q = tail p - monom_mult (lookup (tail p) (t + lp f) / lc f) t f"
    unfolding red_single_def by simp_all
  from ct lookup_tail[of p "t + lp f"] have "t + lp f \<prec> lp p" by (auto split: if_splits)
  hence c: "lookup (tail p) (t + lp f) = lookup p (t + lp f)" using lookup_tail[of p] by simp
  show ?thesis
  proof (intro red_setI[OF \<open>f \<in> F\<close>])
    show "red_single p (q + Poly_Mapping.single (lp p) (lc p)) f t" unfolding red_single_def
    proof (intro conjI, fact)
      from ct c show "lookup p (t + lp f) \<noteq> 0" by simp
    next
      from q have "q + monomial (lc p) (lp p) =
                  (monomial (lc p) (lp p) + tail p) - monom_mult (lookup (tail p) (t + lp f) / lc f) t f"
        by simp
      also have "\<dots> = p - monom_mult (lookup (tail p) (t + lp f) / lc f) t f"
        using leading_monomial_tail[of p] by auto
      finally show "q + monomial (lc p) (lp p) = p - monom_mult (lookup p (t + lp f) / lc f) t f"
        by (simp only: c)
    qed
  qed
qed

lemma red_indE:
  assumes "red F p q"
  shows "(\<exists>f\<in>F. f \<noteq> 0 \<and> lp f adds lp p \<and>
            (q = p - monom_mult (lc p / lc f) (lp p - lp f) f)) \<or>
            red F (tail p) (q - monomial (lc p) (lp p))"
proof -
  from red_nonzero[OF assms] have "p \<noteq> 0" .
  from red_setE[OF assms] obtain f t where "f \<in> F" and rs: "red_single p q f t" by auto
  from rs have "f \<noteq> 0"
    and cn0: "lookup p (t + lp f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f"
    unfolding red_single_def by simp_all
  show ?thesis
  proof (cases "lp p = t + lp f")
    case True
    hence "lp f adds lp p" by simp
    from True have eq1: "lp p - lp f = t" by simp
    from True have eq2: "lc p = lookup p (t + lp f)" unfolding lc_def by simp
    show ?thesis
    proof (intro disjI1, rule bexI[of _ f], intro conjI, fact+)
      from q eq1 eq2 show "q = p - monom_mult (lc p / lc f) (lp p - lp f) f" by simp
    qed (fact)
  next
    case False
    from this lookup_tail_2[of p "t + lp f"]
      have ct: "lookup (tail p) (t + lp f) = lookup p (t + lp f)" by simp
    show ?thesis
    proof (intro disjI2, intro red_setI[of f], fact)
      show "red_single (tail p) (q - monomial (lc p) (lp p)) f t" unfolding red_single_def
      proof (intro conjI, fact)
        from cn0 ct show "lookup (tail p) (t + lp f) \<noteq> 0" by simp
      next
        from leading_monomial_tail[of p]
          have "p - monomial (lc p) (lp p) = (monomial (lc p) (lp p) + tail p) - monomial (lc p) (lp p)"
          by simp
        also have "\<dots> = tail p" by simp
        finally have eq: "p - monomial (lc p) (lp p) = tail p" .
        from q have "q - monomial (lc p) (lp p) =
                    (p - monomial (lc p) (lp p)) - monom_mult ((lookup p (t + lp f)) / lc f) t f" by simp
        also from eq have "\<dots> = tail p - monom_mult ((lookup p (t + lp f)) / lc f) t f" by simp
        finally show "q - monomial (lc p) (lp p) = tail p - monom_mult (lookup (tail p) (t + lp f) / lc f) t f"
          using ct by simp
      qed
    qed
  qed
qed

lemma is_redI:
  assumes "red F a b"
  shows "is_red F a"
unfolding is_red_def relation.is_final_def by (simp, intro exI[of _ b], fact)

lemma is_redE:
  assumes "is_red F a"
  obtains b where "red F a b"
using assms unfolding is_red_def relation.is_final_def
proof simp
  assume r: "\<And>b. red F a b \<Longrightarrow> thesis" and b: "\<exists>x. red F a x"
  from b obtain b where "red F a b" ..
  show thesis by (rule r[of b], fact)
qed

lemma is_red_alt:
  shows "is_red F a \<longleftrightarrow> (\<exists>b. red F a b)"
proof
  assume "is_red F a"
  from is_redE[OF this] obtain b where "red F a b" .
  show "\<exists>b. red F a b" by (intro exI[of _ b], fact)
next
  assume "\<exists>b. red F a b"
  from this obtain b where "red F a b" ..
  show "is_red F a" by (rule is_redI, fact)
qed

lemma is_red_singletonI:
  fixes F::"('a, 'b::field) poly_mapping set" and q::"('a, 'b) poly_mapping"
  assumes "is_red F q"
  obtains p where "p \<in> F" and "is_red {p} q"
proof -
  from assms obtain q0 where "red F q q0" unfolding is_red_alt ..
  from this red_def[of F q q0] obtain p where "p \<in> F" and t: "\<exists>t. red_single q q0 p t" by auto
  have "is_red {p} q" unfolding is_red_alt
  proof
    from red_singleton[of p q q0] t show "red {p} q q0" by simp
  qed
  from \<open>p \<in> F\<close> this show ?thesis ..
qed

lemma is_red_singletonD:
  fixes F::"('a, 'b::field) poly_mapping set" and p q::"('a, 'b) poly_mapping"
  assumes "is_red {p} q" and "p \<in> F"
  shows "is_red F q"
proof -
  from assms(1) obtain q0 where "red {p} q q0" unfolding is_red_alt ..
  from red_singleton[of p q q0] this have "\<exists>t. red_single q q0 p t" ..
  from this obtain t where "red_single q q0 p t" ..
  show ?thesis unfolding is_red_alt
    by (intro exI[of _ q0], intro red_setI[OF assms(2), of q q0 t], fact)
qed

lemma is_red_singleton_trans:
  assumes "is_red {f} p" and "lp g adds lp f" and "g \<noteq> 0"
  shows "is_red {g} p"
proof -
  from \<open>is_red {f} p\<close> obtain q where "red {f} p q" unfolding is_red_alt ..
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  from red_single_trans[OF this \<open>lp g adds lp f\<close> \<open>g \<noteq> 0\<close>] obtain q0 where
    "red_single p q0 g (t + (lp f - lp g))" .
  show ?thesis
  proof (rule is_redI[of "{g}" p q0])
    show "red {g} p q0" unfolding red_def
      by (intro bexI[of _ g], intro exI[of _ "t + (lp f - lp g)"], fact, simp)
  qed
qed

lemma is_red_singleton_not_0:
  assumes "is_red {f} p"
  shows "f \<noteq> 0"
using assms unfolding is_red_alt
proof
  fix q
  assume "red {f} p q"
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  thus ?thesis unfolding red_single_def ..
qed

lemma irred_0:
  shows "\<not> is_red F 0"
proof (rule, rule is_redE)
  fix b
  assume "red F 0 b"
  from ord_p_0_min[of b] red_ord[OF this] show False by simp
qed

lemma is_red_indI1:
  assumes "f \<in> F" and "f \<noteq> 0" and "p \<noteq> 0" and "lp f adds lp p"
  shows "is_red F p"
by (intro is_redI, rule red_indI1[OF assms])

lemma is_red_indI2:
  assumes "p \<noteq> 0" and "is_red F (tail p)"
  shows "is_red F p"
proof -
  from is_redE[OF \<open>is_red F (tail p)\<close>] obtain q where "red F (tail p) q" .
  show ?thesis by (intro is_redI, rule red_indI2[OF \<open>p \<noteq> 0\<close>], fact)
qed

lemma is_red_indE:
  assumes "is_red F p"
  shows "(\<exists>f\<in>F. f \<noteq> 0 \<and> lp f adds lp p) \<or> is_red F (tail p)"
proof -
  from is_redE[OF assms] obtain q where "red F p q" .
  from red_indE[OF this] show ?thesis
  proof
    assume "\<exists>f\<in>F. f \<noteq> 0 \<and> lp f adds lp p \<and> q = p - monom_mult (lc p / lc f) (lp p - lp f) f"
    from this obtain f where "f \<in> F" and "f \<noteq> 0" and "lp f adds lp p" by auto
    show ?thesis by (intro disjI1, rule bexI[of _ f], intro conjI, fact+)
  next
    assume "red F (tail p) (q - monomial (lc p) (lp p))"
    show ?thesis by (intro disjI2, intro is_redI, fact)
  qed
qed

lemma rtrancl_0:
  assumes "(red F)\<^sup>*\<^sup>* 0 x"
  shows "x = 0"
proof -
  from irred_0[of F] have "relation.is_final (red F) 0" unfolding is_red_def by simp
  from relation.rtrancl_is_final[OF \<open>(red F)\<^sup>*\<^sup>* 0 x\<close> this] show ?thesis by simp
qed

lemma red_rtrancl_ord:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "q \<preceq>p p"
  using assms
proof induct
  case base
  show ?case ..
next
  case (step y z)
  from step(2) have "z \<prec>p y" by (rule red_ord)
  hence "z \<preceq>p y" by simp
  also note step(3)
  finally show ?case .
qed

subsection \<open>Reducibility and Addition \& Multiplication\<close>

lemma red_single_monom_mult:
  assumes a: "red_single p q f t" and "c \<noteq> 0"
  shows "red_single (monom_mult c s p) (monom_mult c s q) f (s + t)"
proof -
  from a have "f \<noteq> 0"
    and "lookup p (t + lp f) \<noteq> 0"
    and q_def: "q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f"
    unfolding red_single_def by auto
  have assoc: "(s + t) + lp f = s + (t + lp f)" by (simp add: ac_simps)
  have g2: "lookup (monom_mult c s p) ((s + t) + lp f) \<noteq> 0"
  proof
    assume "lookup (monom_mult c s p) ((s + t) + lp f) = 0"
    hence "c * lookup p (t + lp f) = 0" using assoc by (simp add: lookup_monom_mult_plus)
    thus False using \<open>c \<noteq> 0\<close> \<open>lookup p (t + lp f) \<noteq> 0\<close> by simp
  qed
  have g3: "monom_mult c s q =
    (monom_mult c s p) - monom_mult ((lookup (monom_mult c s p) ((s + t) + lp f)) / lc f) (s + t) f"
  proof -
    from q_def monom_mult_dist_right_minus[of c s p]
      have "monom_mult c s q =
            monom_mult c s p - monom_mult c s (monom_mult (lookup p (t + lp f) / lc f) t f)" by simp
    also from monom_mult_assoc[of c s "lookup p (t + lp f) / lc f" t f] assoc
      have "monom_mult c s (monom_mult (lookup p (t + lp f) / lc f) t f) =
            monom_mult ((lookup (monom_mult c s p) ((s + t) + lp f)) / lc f) (s + t) f"
        by (simp add: lookup_monom_mult_plus)
    finally show ?thesis .
  qed
  from \<open>f \<noteq> 0\<close> g2 g3 show ?thesis unfolding red_single_def by auto
qed

lemma red_single_plus_1:
  assumes "red_single p q f t" and "t + lp f \<notin> keys (p + r)"
  shows "red_single (q + r) (p + r) f t"
proof -
  from assms have "f \<noteq> 0" and "lookup p (t + lp f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f"
    by (simp_all add: red_single_def)
  from assms(1) have cq_0: "lookup q (t + lp f) = 0" by (rule red_single_lookup)
  from assms(2) have "lookup (p + r) (t + lp f) = 0" by simp
  with neg_eq_iff_add_eq_0[of "lookup p (t + lp f)" "lookup r (t + lp f)"]
    have cr: "lookup r (t + lp f) = - (lookup p (t + lp f))" by (simp add: lookup_add)
  hence cr_not_0: "lookup r (t + lp f) \<noteq> 0" using \<open>lookup p (t + lp f) \<noteq> 0\<close> by simp
  from \<open>f \<noteq> 0\<close> show ?thesis unfolding red_single_def
  proof (intro conjI)
    from cr_not_0 show "lookup (q + r) (t + lp f) \<noteq> 0" by (simp add: lookup_add cq_0)
  next
    from lc_not_0[OF \<open>f \<noteq> 0\<close>]
      have "monom_mult ((lookup (q + r) (t + lp f)) / lc f) t f =
                  monom_mult ((lookup r (t + lp f)) / lc f) t f"
        by (simp add: field_simps lookup_add cq_0)
    thus "p + r = q + r - monom_mult (lookup (q + r) (t + lp f) / lc f) t f"
      by (simp add: cr q monom_mult_uminus_left)
  qed
qed

lemma red_single_plus_2:
  assumes "red_single p q f t" and "t + lp f \<notin> keys (q + r)"
  shows "red_single (p + r) (q + r) f t"
proof -
  from assms have "f \<noteq> 0" and cp: "lookup p (t + lp f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f"
    by (simp_all add: red_single_def)
  from assms(1) have cq_0: "lookup q (t + lp f) = 0" by (rule red_single_lookup)
  with assms(2) have cr_0: "lookup r (t + lp f) = 0" by (simp add: lookup_add)
  from \<open>f \<noteq> 0\<close> show ?thesis unfolding red_single_def
  proof (intro conjI)
    from cp show "lookup (p + r) (t + lp f) \<noteq> 0" by (simp add: lookup_add cr_0)
  next
    show "q + r = p + r - monom_mult (lookup (p + r) (t + lp f) / lc f) t f"
      by (simp add: cr_0 q lookup_add)
  qed
qed

lemma red_single_plus_3:
  assumes "red_single p q f t" and "t + lp f \<in> keys (p + r)" and "t + lp f \<in> keys (q + r)"
  shows "\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t"
proof -
  from assms have "f \<noteq> 0" and "lookup p (t + lp f) \<noteq> 0"
    and q: "q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f"
    by (simp_all add: red_single_def)
  from assms(2) have cpr: "lookup (p + r) (t + lp f) \<noteq> 0" by simp
  from assms(3) have cqr: "lookup (q + r) (t + lp f) \<noteq> 0" by simp
  from assms(1) have cq_0: "lookup q (t + lp f) = 0" by (rule red_single_lookup)
  let ?s = "(p + r) - monom_mult ((lookup (p + r) (t + lp f)) / lc f) t f"
  from \<open>f \<noteq> 0\<close> cpr have "red_single (p + r) ?s f t" by (simp add: red_single_def)
  moreover from \<open>f \<noteq> 0\<close> have "red_single (q + r) ?s f t" unfolding red_single_def
  proof (intro conjI)
    from cqr show "lookup (q + r) (t + lp f) \<noteq> 0" .
  next
    from lc_not_0[OF \<open>f \<noteq> 0\<close>]
      monom_mult_dist_left[of "(lookup p (t + lp f)) / lc f" "(lookup r (t + lp f)) / lc f" t f]
      have "monom_mult ((lookup (p + r) (t + lp f)) / lc f) t f =
                (monom_mult ((lookup p (t + lp f)) / lc f) t f) +
                  (monom_mult ((lookup r (t + lp f)) / lc f) t f)"
        by (simp add: field_simps lookup_add)
    moreover from lc_not_0[OF \<open>f \<noteq> 0\<close>]
      monom_mult_dist_left[of "(lookup q (t + lp f)) / lc f" "(lookup r (t + lp f)) / lc f" t f]
      have "monom_mult ((lookup (q + r) (t + lp f)) / lc f) t f =
                monom_mult ((lookup r (t + lp f)) / lc f) t f"
        by (simp add: field_simps lookup_add cq_0)
    ultimately show "p + r - monom_mult (lookup (p + r) (t + lp f) / lc f) t f =
                     q + r - monom_mult (lookup (q + r) (t + lp f) / lc f) t f" by (simp add: q)
  qed
  ultimately show ?thesis by auto
qed

lemma red_single_plus:
  assumes "red_single p q f t"
  shows "red_single (p + r) (q + r) f t \<or>
          red_single (q + r) (p + r) f t \<or>
          (\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t)" (is "?A \<or> ?B \<or> ?C")
proof (cases "t + lp f \<in> keys (p + r)")
  case True
  show ?thesis
  proof (cases "t + lp f \<in> keys (q + r)")
    case True
    with assms \<open>t + lp f \<in> keys (p + r)\<close> have ?C by (rule red_single_plus_3)
    thus ?thesis by simp
  next
    case False
    with assms have ?A by (rule red_single_plus_2)
    thus ?thesis ..
  qed
next
  case False
  with assms have ?B by (rule red_single_plus_1)
  thus ?thesis by simp
qed

lemma red_single_diff:
  assumes "red_single (p - q) r f t"
  shows "red_single p (r + q) f t \<or> red_single q (p - r) f t \<or>
          (\<exists>p' q'. red_single p p' f t \<and> red_single q q' f t \<and> r = p' - q')" (is "?A \<or> ?B \<or> ?C")
proof -
  let ?s = "t + lp f"
  from assms have "f \<noteq> 0"
    and "lookup (p - q) ?s \<noteq> 0"
    and r: "r = p - q - monom_mult ((lookup (p - q) ?s) / lc f) t f"
    unfolding red_single_def by auto
  from this(2) have diff: "lookup p ?s \<noteq> lookup q ?s" by (simp add: lookup_minus)
  show ?thesis
  proof (cases "lookup p ?s = 0")
    case True
    with diff have "?s \<in> keys q" by simp
    moreover have "lookup (p - q) ?s = - lookup q ?s" by (simp add: lookup_minus True)
    ultimately have ?B using \<open>f \<noteq> 0\<close> by (simp add: red_single_def r monom_mult_uminus_left)
    thus ?thesis by simp
  next
    case False
    hence "?s \<in> keys p" by simp
    show ?thesis
    proof (cases "lookup q ?s = 0")
      case True
      hence "lookup (p - q) ?s = lookup p ?s" by (simp add: lookup_minus)
      hence ?A using \<open>f \<noteq> 0\<close> \<open>?s \<in> keys p\<close> by (simp add: red_single_def r monom_mult_uminus_left)
      thus ?thesis ..
    next
      case False
      hence "?s \<in> keys q" by simp
      let ?p = "p - monom_mult ((lookup p ?s) / lc f) t f"
      let ?q = "q - monom_mult ((lookup q ?s) / lc f) t f"
      have ?C
      proof (intro exI conjI)
        from \<open>f \<noteq> 0\<close> \<open>?s \<in> keys p\<close> show "red_single p ?p f t" by (simp add: red_single_def)
      next
        from \<open>f \<noteq> 0\<close> \<open>?s \<in> keys q\<close> show "red_single q ?q f t" by (simp add: red_single_def)
      next
        from \<open>f \<noteq> 0\<close> have "lc f \<noteq> 0" by (rule lc_not_0)
        hence eq: "(lookup p (t + lp f) - lookup q (t + lp f)) / lc f =
                   lookup p (t + lp f) / lc f - lookup q (t + lp f) / lc f" by (simp add: field_simps)
        show "r = ?p - ?q" by (simp add: r lookup_minus eq monom_mult_dist_left_minus)
      qed
      thus ?thesis by simp
    qed
  qed
qed

lemma red_monom_mult:
  assumes a: "red F p q" and "c \<noteq> 0"
  shows "red F (monom_mult c s p) (monom_mult c s q)"
proof -
  from red_setE[OF a] obtain f and t where "f \<in> F" and rs: "red_single p q f t" by auto
  from red_single_monom_mult[OF rs \<open>c \<noteq> 0\<close>, of s] show ?thesis by (intro red_setI[OF \<open>f \<in> F\<close>])
qed

lemma red_plus_keys_disjoint:
  assumes "red F p q" and "keys p \<inter> keys r = {}"
  shows "red F (p + r) (q + r)"
proof -
  from assms(1) obtain f t where "f \<in> F" and *: "red_single p q f t" by (rule red_setE)
  from this(2) have "red_single (p + r) (q + r) f t"
  proof (rule red_single_plus_2)
    from * have "lookup q (t + lp f) = 0"
      by (simp add: red_single_def lookup_minus lookup_monom_mult lc_def[symmetric] lc_not_0)
    hence "t + lp f \<notin> keys q" by simp
    moreover have "t + lp f \<notin> keys r"
    proof
      assume "t + lp f \<in> keys r"
      moreover from * have "t + lp f \<in> keys p" by (simp add: red_single_def)
      ultimately have "t + lp f \<in> keys p \<inter> keys r" by simp
      with assms(2) show False by simp
    qed
    ultimately have "t + lp f \<notin> keys q \<union> keys r" by simp
    thus "t + lp f \<notin> keys (q + r)" using keys_add_subset[of q r] by blast
  qed
  with \<open>f \<in> F\<close> show ?thesis by (rule red_setI)
qed

lemma red_plus:
  assumes a: "red F p q"
  obtains s where "(red F)\<^sup>*\<^sup>* (p + r) s" and "(red F)\<^sup>*\<^sup>* (q + r) s"
proof -
  from red_setE[OF a] obtain f and t where "f \<in> F" and rs: "red_single p q f t" by auto
  from red_single_plus[OF rs, of r] show ?thesis
  proof
    assume c1: "red_single (p + r) (q + r) f t"
    show ?thesis
    proof
      from c1 show "(red F)\<^sup>*\<^sup>* (p + r) (q + r)" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
    next
      show "(red F)\<^sup>*\<^sup>* (q + r) (q + r)" ..
    qed
  next
    assume "red_single (q + r) (p + r) f t \<or> (\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t)"
    thus ?thesis
    proof
      assume c2: "red_single (q + r) (p + r) f t"
      show ?thesis
      proof
        show "(red F)\<^sup>*\<^sup>* (p + r) (p + r)" ..
      next
        from c2 show "(red F)\<^sup>*\<^sup>* (q + r) (p + r)" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
      qed
    next
      assume "\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t"
      then obtain s where s1: "red_single (p + r) s f t" and s2: "red_single (q + r) s f t" by auto
      show ?thesis
      proof
        from s1 show "(red F)\<^sup>*\<^sup>* (p + r) s" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
      next
        from s2 show "(red F)\<^sup>*\<^sup>* (q + r) s" by (intro r_into_rtranclp, intro red_setI[OF \<open>f \<in> F\<close>])
      qed
    qed
  qed
qed

corollary red_plus_cs:
  assumes "red F p q"
  shows "relation.cs (red F) (p + r) (q + r)"
  unfolding relation.cs_def
proof -
  from assms obtain s where "(red F)\<^sup>*\<^sup>* (p + r) s" and "(red F)\<^sup>*\<^sup>* (q + r) s" by (rule red_plus)
  show "\<exists>s. (red F)\<^sup>*\<^sup>* (p + r) s \<and> (red F)\<^sup>*\<^sup>* (q + r) s" by (intro exI, intro conjI, fact, fact)
qed

lemma red_uminus:
  assumes "red F p q"
  shows "red F (-p) (-q)"
  using red_monom_mult[OF assms, of "-1" 0] by simp

lemma red_diff:
  assumes "red F (p - q) r"
  obtains p' q' where "(red F)\<^sup>*\<^sup>* p p'" and "(red F)\<^sup>*\<^sup>* q q'" and "r = p' - q'"
proof -
  from assms obtain f t where "f \<in> F" and "red_single (p - q) r f t" by (rule red_setE)
  from red_single_diff[OF this(2)] show ?thesis
  proof (elim disjE)
    assume "red_single p (r + q) f t"
    with \<open>f \<in> F\<close> have *: "red F p (r + q)" by (rule red_setI)
    show ?thesis
    proof
      from * show "(red F)\<^sup>*\<^sup>* p (r + q)" ..
    next
      show "(red F)\<^sup>*\<^sup>* q q" ..
    qed simp
  next
    assume "red_single q (p - r) f t"
    with \<open>f \<in> F\<close> have *: "red F q (p - r)" by (rule red_setI)
    show ?thesis
    proof
      show "(red F)\<^sup>*\<^sup>* p p" ..
    next
      from * show "(red F)\<^sup>*\<^sup>* q (p - r)" ..
    qed simp
  next
    assume "\<exists>p' q'. red_single p p' f t \<and> red_single q q' f t \<and> r = p' - q'"
    then obtain p' q' where 1: "red_single p p' f t" and 2: "red_single q q' f t" and "r = p' - q'"
      by blast
    from \<open>f \<in> F\<close> 2 have "red F q q'" by (rule red_setI)
    from \<open>f \<in> F\<close> 1 have "red F p p'" by (rule red_setI)
    hence "(red F)\<^sup>*\<^sup>* p p'" ..
    moreover from \<open>red F q q'\<close> have "(red F)\<^sup>*\<^sup>* q q'" ..
    moreover note \<open>r = p' - q'\<close>
    ultimately show ?thesis ..
  qed
qed

lemma red_diff_rtrancl':
  assumes "(red F)\<^sup>*\<^sup>* (p - q) r"
  obtains p' q' where "(red F)\<^sup>*\<^sup>* p p'" and "(red F)\<^sup>*\<^sup>* q q'" and "r = p' - q'"
  using assms
proof (induct arbitrary: thesis rule: rtranclp_induct)
  case base
  show ?case by (rule base, fact rtrancl_refl[to_pred], fact rtrancl_refl[to_pred], fact refl)
next
  case (step y z)
  obtain p1 q1 where p1: "(red F)\<^sup>*\<^sup>* p p1" and q1: "(red F)\<^sup>*\<^sup>* q q1" and y: "y = p1 - q1" by (rule step(3))
  from step(2) obtain p' q' where p': "(red F)\<^sup>*\<^sup>* p1 p'" and q': "(red F)\<^sup>*\<^sup>* q1 q'" and z: "z = p' - q'"
    unfolding y by (rule red_diff)
  show ?case
  proof (rule step(4))
    from p1 p' show "(red F)\<^sup>*\<^sup>* p p'" by simp
  next
    from q1 q' show "(red F)\<^sup>*\<^sup>* q q'" by simp
  qed fact
qed

lemma red_diff_rtrancl:
  assumes "(red F)\<^sup>*\<^sup>* (p - q) 0"
  obtains s where "(red F)\<^sup>*\<^sup>* p s" and "(red F)\<^sup>*\<^sup>* q s"
proof -
  from assms obtain p' q' where p': "(red F)\<^sup>*\<^sup>* p p'" and q': "(red F)\<^sup>*\<^sup>* q q'" and "0 = p' - q'"
    by (rule red_diff_rtrancl')
  from this(3) have "q' = p'" by simp
  from p' q' show ?thesis unfolding \<open>q' = p'\<close> ..
qed

corollary red_diff_rtrancl_cs:
  assumes "(red F)\<^sup>*\<^sup>* (p - q) 0"
  shows "relation.cs (red F) p q"
  unfolding relation.cs_def
proof -
  from assms obtain s where "(red F)\<^sup>*\<^sup>* p s" and "(red F)\<^sup>*\<^sup>* q s" by (rule red_diff_rtrancl)
  show "\<exists>s. (red F)\<^sup>*\<^sup>* p s \<and> (red F)\<^sup>*\<^sup>* q s" by (intro exI, intro conjI, fact, fact)
qed

subsection \<open>Confluence of Reducibility\<close>

lemma confluent_distinct_aux:
  assumes r1: "red_single p q1 f1 t1" and r2: "red_single p q2 f2 t2"
    and "t1 + lp f1 \<prec> t2 + lp f2" and "f1 \<in> F" and "f2 \<in> F"
  obtains s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof -
  from r1 have "f1 \<noteq> 0" and c1: "lookup p (t1 + lp f1) \<noteq> 0"
    and q1_def: "q1 = p - monom_mult (lookup p (t1 + lp f1) / lc f1) t1 f1"
    unfolding red_single_def by auto
  from r2 have "f2 \<noteq> 0" and c2: "lookup p (t2 + lp f2) \<noteq> 0"
    and q2_def: "q2 = p - monom_mult (lookup p (t2 + lp f2) / lc f2) t2 f2"
    unfolding red_single_def by auto
  from \<open>t1 + lp f1 \<prec> t2 + lp f2\<close>
  have "lookup (monom_mult (lookup p (t1 + lp f1) / lc f1) t1 f1) (t2 + lp f2) = 0"
    by (metis lookup_mult_0)
  from lookup_minus[of p _ "t2 + lp f2"] this have c: "lookup q1 (t2 + lp f2) = lookup p (t2 + lp f2)"
    unfolding q1_def by simp
  define q3 where "q3 \<equiv> q1 - monom_mult ((lookup q1 (t2 + lp f2)) / lc f2) t2 f2"
  have "red_single q1 q3 f2 t2" unfolding red_single_def
  proof (rule, fact, rule)
    from c c2 show "lookup q1 (t2 + lp f2) \<noteq> 0" by simp
  next
    show "q3 = q1 - monom_mult (lookup q1 (t2 + lp f2) / lc f2) t2 f2" unfolding q3_def ..
  qed
  hence "red F q1 q3" by (intro red_setI[OF \<open>f2 \<in> F\<close>])
  hence q1q3: "(red F)\<^sup>*\<^sup>* q1 q3" by (intro r_into_rtranclp)
  from r1 have "red F p q1" by (intro red_setI[OF \<open>f1 \<in> F\<close>])
  from red_plus[OF this, of "- monom_mult ((lookup p (t2 + lp f2)) / lc f2) t2 f2"] obtain s
    where r3: "(red F)\<^sup>*\<^sup>* (p - monom_mult (lookup p (t2 + lp f2) / lc f2) t2 f2) s"
    and r4: "(red F)\<^sup>*\<^sup>* (q1 - monom_mult (lookup p (t2 + lp f2) / lc f2) t2 f2) s" by auto
  from r3 have q2s: "(red F)\<^sup>*\<^sup>* q2 s" unfolding q2_def by simp
  from r4 c have q3s: "(red F)\<^sup>*\<^sup>* q3 s" unfolding q3_def by simp
  show ?thesis
  proof
    from rtranclp_trans[OF q1q3 q3s] show "(red F)\<^sup>*\<^sup>* q1 s" .
  next
    from q2s show "(red F)\<^sup>*\<^sup>* q2 s" .
  qed
qed

lemma confluent_distinct:
  assumes r1: "red_single p q1 f1 t1" and r2: "red_single p q2 f2 t2"
    and ne: "t1 + lp f1 \<noteq> t2 + lp f2" and "f1 \<in> F" and "f2 \<in> F"
  obtains s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof -
  from ne have "t1 + lp f1 \<prec> t2 + lp f2 \<or> t2 + lp f2 \<prec> t1 + lp f1" by auto
  thus ?thesis
  proof
    assume a1: "t1 + lp f1 \<prec> t2 + lp f2"
    from confluent_distinct_aux[OF r1 r2 a1 \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>] obtain s where
      "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s" .
    thus ?thesis ..
  next
    assume a2: "t2 + lp f2 \<prec> t1 + lp f1"
    from confluent_distinct_aux[OF r2 r1 a2 \<open>f2 \<in> F\<close> \<open>f1 \<in> F\<close>] obtain s where
      "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s" .
    thus ?thesis ..
  qed
qed

corollary confluent_same:
  assumes r1: "red_single p q1 f t1" and r2: "red_single p q2 f t2" and "f \<in> F"
  obtains s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof (cases "t1 = t2")
  case True
  with r1 r2 have "q1 = q2" by (simp add: red_single_def)
  show ?thesis
  proof
    show "(red F)\<^sup>*\<^sup>* q1 q2" unfolding \<open>q1 = q2\<close> ..
  next
    show "(red F)\<^sup>*\<^sup>* q2 q2" ..
  qed
next
  case False
  hence "t1 + lp f \<noteq> t2 + lp f" by simp
  from r1 r2 this \<open>f \<in> F\<close> \<open>f \<in> F\<close> obtain s where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
    by (rule confluent_distinct)
  thus ?thesis ..
qed

subsection \<open>Reducibility and Ideal Membership\<close>

lemma srtc_in_pideal:
  assumes "relation.srtc (red F) p q"
  shows "p - q \<in> pideal F"
  using assms unfolding relation.srtc_def
proof (induct rule: rtranclp.induct)
  fix p
  from ideal.module_0[of F] show "p - p \<in> pideal F" by simp
next
  fix p r q
  assume pr_in: "p - r \<in> pideal F" and red: "red F r q \<or> red F q r"
  from red obtain f c t where "f \<in> F" and "q = r - monom_mult c t f"
  proof
    assume "red F r q"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single r q f t" .
    hence "q = r - monom_mult (lookup r (t + lp f) / lc f) t f" unfolding red_single_def by simp
    show thesis by (rule, fact, fact)
  next
    assume "red F q r"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single q r f t" .
    hence "r = q - monom_mult (lookup q (t + lp f) / lc f) t f" unfolding red_single_def by simp
    hence "q = r + monom_mult (lookup q (t + lp f) / lc f) t f" by simp
    hence "q = r - monom_mult (-(lookup q (t + lp f) / lc f)) t f"
      using monom_mult_uminus_left[of _ t f] by simp
    show thesis by (rule, fact, fact)
  qed
  hence eq: "p - q = (p - r) + monom_mult c t f" by simp
  show "p - q \<in> pideal F" unfolding eq
    by (rule ideal.module_closed_plus, fact, rule monom_mult_in_pideal, fact)
qed

lemma in_pideal_srtc:
  assumes "p \<in> pideal F"
  shows "relation.srtc (red F) p 0"
  using assms
proof (induct p rule: pideal_induct)
  show "relation.srtc (red F) 0 0" unfolding relation.srtc_def ..
next
  fix a f c t
  assume a_in: "a \<in> pideal F" and IH: "relation.srtc (red F) a 0" and "f \<in> F"
  show "relation.srtc (red F) (a + monom_mult c t f) 0"
  proof (cases "c = 0")
    assume "c = 0"
    hence "a + monom_mult c t f = a" using monom_mult_left0[of t f] by simp
    thus ?thesis using IH by simp
  next
    assume "c \<noteq> 0"
    show ?thesis
    proof (cases "f = 0")
      assume "f = 0"
      hence "a + monom_mult c t f = a" using monom_mult_right0[of c t] by simp
      thus ?thesis using IH by simp
    next
      assume "f \<noteq> 0"
      from lc_not_0[OF this] have "lc f \<noteq> 0" .
      have "red F (monom_mult c t f) 0"
      proof (intro red_setI[OF \<open>f \<in> F\<close>])
        from lookup_monom_mult_plus[of c t f "lp f"]
          have eq: "lookup (monom_mult c t f) (t + lp f) = c * lc f" unfolding lc_def .
        show "red_single (monom_mult c t f) 0 f t" unfolding red_single_def eq
        proof (intro conjI, fact)
          from \<open>c \<noteq> 0\<close> \<open>lc f \<noteq> 0\<close> show "c * lc f \<noteq> 0" by simp
        next
          from \<open>lc f \<noteq> 0\<close> show "0 = monom_mult c t f - monom_mult (c * lc f / lc f) t f" by simp
        qed
      qed
      from red_plus[OF this, of a] obtain s where
        s1: "(red F)\<^sup>*\<^sup>* (monom_mult c t f + a) s" and s2: "(red F)\<^sup>*\<^sup>* (0 + a) s" .
      have "relation.cs (red F) (a + monom_mult c t f) a" unfolding relation.cs_def
      proof (intro exI[of _ s], intro conjI)
        from s1 show "(red F)\<^sup>*\<^sup>* (a + monom_mult c t f) s" by (simp only: add.commute)
      next
        from s2 show "(red F)\<^sup>*\<^sup>* a s" by simp
      qed
      from relation.srtc_transitive[OF relation.cs_implies_srtc[OF this] IH] show ?thesis .
    qed
  qed
qed

lemma red_rtranclp_diff_in_pideal:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "p - q \<in> pideal F"
proof -
  from assms have "relation.srtc (red F) p q"
    by (simp add: r_into_rtranclp relation.rtc_implies_srtc)
  thus ?thesis by (rule srtc_in_pideal)
qed

corollary red_diff_in_pideal:
  assumes "red F p q"
  shows "p - q \<in> pideal F"
  by (rule red_rtranclp_diff_in_pideal, rule r_into_rtranclp, fact)
  
corollary red_rtranclp_0_in_pideal:
  assumes "(red F)\<^sup>*\<^sup>* p 0"
  shows "p \<in> pideal F"
  using assms red_rtranclp_diff_in_pideal by fastforce

lemma pideal_closed_red:
  assumes "pideal B \<subseteq> pideal A" and "p \<in> pideal A" and "red B p q"
  shows "q \<in> pideal A"
proof -
  have "q - p \<in> pideal A"
  proof
    have "p - q \<in> pideal B" by (rule red_diff_in_pideal, fact)
    hence "- (p - q) \<in> pideal B" by (rule ideal.module_closed_uminus)
    thus "q - p \<in> pideal B" by simp
  qed fact
  from ideal.module_closed_plus[OF this \<open>p \<in> pideal A\<close>] show ?thesis by simp
qed

subsection \<open>More Properties of @{const red}, @{const red_single} and @{const is_red}\<close>

lemma red_rtrancl_mult:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q)"
proof (cases "c = 0")
  case True
  have "(red F)\<^sup>*\<^sup>* 0 0" by simp
  thus ?thesis by (simp only: True monom_mult_left0[of t])
next
  case False
  from assms show ?thesis
  proof (induct rule: rtranclp_induct)
    show "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t p)" by simp
  next
    fix q0 q
    assume "(red F)\<^sup>*\<^sup>* p q0" and "red F q0 q" and "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q0)"
    show "(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q)"
    proof (rule rtranclp.intros(2)[OF \<open>(red F)\<^sup>*\<^sup>* (monom_mult c t p) (monom_mult c t q0)\<close>])
      from red_monom_mult[OF \<open>red F q0 q\<close> False, of t] show "red F (monom_mult c t q0) (monom_mult c t q)" .
    qed
  qed
qed

corollary red_rtrancl_uminus:
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* (-p) (-q)"
  using red_rtrancl_mult[OF assms, of "-1" 0] by simp

lemma red_rtrancl_diff_induct [consumes 1, case_names base step]:
  assumes a: "(red F)\<^sup>*\<^sup>* (p - q) r"
    and cases: "P p p" "!!y z. [| (red F)\<^sup>*\<^sup>* (p - q) z; red F z y; P p (q + z)|] ==> P p (q + y)"
  shows "P p (q + r)"
  using a
proof (induct rule: rtranclp_induct)
  from cases(1) show "P p (q + (p - q))" by simp
next
  fix y z
  assume "(red F)\<^sup>*\<^sup>* (p - q) z" "red F z y" "P p (q + z)"
  thus "P p (q + y)" using cases(2) by simp
qed

lemma red_rtrancl_diff_0_induct [consumes 1, case_names base step]:
  assumes a: "(red F)\<^sup>*\<^sup>* (p - q) 0"
    and base: "P p p" and ind: "\<And>y z. [| (red F)\<^sup>*\<^sup>* (p - q) y; red F y z; P p (y + q)|] ==> P p (z + q)"
  shows "P p q"
proof -
  from ind red_rtrancl_diff_induct[of F p q 0 P, OF a base] have "P p (0 + q)"
    by (simp add: ac_simps)
  thus ?thesis by simp
qed

lemma is_red_union: "is_red (A \<union> B) p \<longleftrightarrow> (is_red A p \<or> is_red B p)"
  unfolding is_red_alt red_union by auto

lemma red_single_0_lp:
  fixes f h t
  assumes "red_single f 0 h t"
  shows "lp f = lp h + t"
proof -
  from red_single_nonzero1[OF assms] have "f \<noteq> 0" .
  {
    assume "h \<noteq> 0" and neq: "lookup f (t + lp h) \<noteq> 0" and
      eq: "f = monom_mult (lookup f (t + lp h) / lc h) t h"
    from lc_not_0[OF \<open>h \<noteq> 0\<close>] have "lc h \<noteq> 0" .
    with neq have "(lookup f (t + lp h) / lc h) \<noteq> 0" by simp
    from eq lp_monom_mult[OF this \<open>h \<noteq> 0\<close>, of t] have "lp f = t + lp h" by simp
    hence "lp f = lp h + t" by (simp add: ac_simps)
  }
  with assms show ?thesis unfolding red_single_def by auto
qed

lemma red_single_lp_distinct_lp:
  fixes f g h t
  assumes rs: "red_single f g h t" and "g \<noteq> 0" and "lp g \<noteq> lp f"
  shows "lp f = lp h + t"
proof -
  from red_single_nonzero1[OF rs] have "f \<noteq> 0" .
  from red_single_ord[OF rs] have "g \<preceq>p f" by simp
  from ord_p_lp[OF this] \<open>lp g \<noteq> lp f\<close> have "lp g \<prec> lp f" by simp
  {
    assume "h \<noteq> 0" and neq: "lookup f (t + lp h) \<noteq> 0" and
      eq: "f = g + monom_mult (lookup f (t + lp h) / lc h) t h" (is "f = g + ?R")
    from lc_not_0[OF \<open>h \<noteq> 0\<close>] have "lc h \<noteq> 0" .
    with neq have "(lookup f (t + lp h) / lc h) \<noteq> 0" (is "?c \<noteq> 0") by simp
    from eq lp_monom_mult[OF this \<open>h \<noteq> 0\<close>, of t] have lpR: "lp ?R = t + lp h" by simp
    from monom_mult_0_iff[of ?c t h] \<open>?c \<noteq> 0\<close> \<open>h \<noteq> 0\<close> have "?R \<noteq> 0" by auto
    from lp_plus_lessE[of g] eq \<open>lp g \<prec> lp f\<close> have "lp g \<prec> lp ?R" by auto
    from lp_plus_eqI[OF this] eq lpR have "lp f = lp h + t" by (simp add: ac_simps)
  }
  with assms show ?thesis unfolding red_single_def by auto
qed

lemma zero_reducibility_implies_lp_divisibility':
  assumes "(red F)\<^sup>*\<^sup>* f 0" and "f \<noteq> 0"
  shows "\<exists>h\<in>F. h \<noteq> 0 \<and> (lp h adds lp f)"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step f g)
  show ?case
  proof (cases "g = 0")
    case True
    with step.hyps have "red F f 0" by simp
    from red_setE[OF this] obtain h t where "h \<in> F" and rs: "red_single f 0 h t" by auto
    show ?thesis
    proof
      from red_single_0_lp[OF rs] have "lp h adds lp f" by simp
      also from rs have "h \<noteq> 0" by (simp add: red_single_def) 
      ultimately show "h \<noteq> 0 \<and> lp h adds lp f" by simp
    qed (rule \<open>h \<in> F\<close>)
  next
    case False
    show ?thesis
    proof (cases "lp g = lp f")
      case True
      with False step.hyps show ?thesis by simp
    next
      case False
      from red_setE[OF \<open>red F f g\<close>] obtain h t where "h \<in> F" and rs: "red_single f g h t" by auto
      show ?thesis
      proof
        from red_single_lp_distinct_lp[OF rs \<open>g \<noteq> 0\<close> False] have "lp h adds lp f" by simp
        also from rs have "h \<noteq> 0" by (simp add: red_single_def) 
        ultimately show "h \<noteq> 0 \<and> lp h adds lp f" by simp
      qed (rule \<open>h \<in> F\<close>)
    qed
  qed
qed
  
lemma zero_reducibility_implies_lp_divisibility:
  assumes "(red F)\<^sup>*\<^sup>* f 0" and "f \<noteq> 0"
  obtains h where "h \<in> F" and "h \<noteq> 0" and "lp h adds lp f"
  using zero_reducibility_implies_lp_divisibility'[OF assms] by auto

lemma is_red_addsI:
  assumes "f \<in> F" and "f \<noteq> 0" and "t \<in> (keys p)" and "lp f adds t"
  shows "is_red F p"
  using assms
proof (induction p rule: poly_mapping_tail_induct)
  case 0
  from \<open>t \<in> (keys 0)\<close> keys_eq_empty_iff[of 0] show ?case by auto
next
  case (tail p)
  from "tail.IH"[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> _ \<open>lp f adds t\<close>] have imp: "t \<in> (keys (tail p)) \<Longrightarrow> is_red F (tail p)" .
  show ?case
  proof (cases "t = lp p")
    case True
    show ?thesis
    proof (rule is_red_indI1[OF \<open>f \<in> F\<close> \<open>f \<noteq> 0\<close> \<open>p \<noteq> 0\<close>])
      from \<open>lp f adds t\<close> True show "lp f adds lp p" by simp
    qed
  next
    case False
    with \<open>t \<in> (keys p)\<close> \<open>p \<noteq> 0\<close> have "t \<in> (keys (tail p))"
      by (simp add: lookup_tail_2 in_keys_iff del: lookup_not_eq_zero_eq_in_keys) 
    from is_red_indI2[OF \<open>p \<noteq> 0\<close> imp[OF this]] show ?thesis .
  qed
qed

lemma is_red_addsE':
  assumes "is_red F p"
  shows "\<exists>f\<in>F. \<exists>t\<in>(keys p). f \<noteq> 0 \<and> lp f adds t"
  using assms
proof (induction p rule: poly_mapping_tail_induct)
  case 0
  with irred_0[of F] show ?case by simp
next
  case (tail p)
  from is_red_indE[OF \<open>is_red F p\<close>] show ?case
  proof
    assume "\<exists>f\<in>F. f \<noteq> 0 \<and> lp f adds lp p"
    then obtain f where "f \<in> F" and "f \<noteq> 0" and "lp f adds lp p" by auto
    show ?case
    proof
      show "\<exists>t\<in>keys p. f \<noteq> 0 \<and> lp f adds t"
      proof (intro bexI, intro conjI)
        from \<open>p \<noteq> 0\<close> show "lp p \<in> (keys p)" by (metis in_keys_iff lc_def lc_not_0)
      qed (rule \<open>f \<noteq> 0\<close>, rule \<open>lp f adds lp p\<close>)
    qed (rule \<open>f \<in> F\<close>)
  next
    assume "is_red F (tail p)"
    from "tail.IH"[OF this] obtain f t
      where "f \<in> F" and "f \<noteq> 0" and t_in_keys_tail: "t \<in> (keys (tail p))" and "lp f adds t" by auto
    from "tail.hyps" t_in_keys_tail have t_in_keys: "t \<in> (keys p)" by (metis lookup_tail in_keys_iff)
    show ?case
    proof
      show "\<exists>t\<in>keys p. f \<noteq> 0 \<and> lp f adds t"
        by (intro bexI, intro conjI, rule \<open>f \<noteq> 0\<close>, rule \<open>lp f adds t\<close>, rule t_in_keys)
    qed (rule \<open>f \<in> F\<close>)
  qed
qed

lemma is_red_addsE:
  assumes "is_red F p"
  obtains f t where "f \<in> F" and "t \<in> (keys p)" and "f \<noteq> 0" and "lp f adds t"
  using is_red_addsE'[OF assms] by auto

lemma is_red_adds_iff:
  shows "(is_red F p) \<longleftrightarrow> (\<exists>f\<in>F. \<exists>t\<in>(keys p). f \<noteq> 0 \<and> lp f adds t)"
  using is_red_addsE' is_red_addsI by auto
    
lemma is_red_subset:
  assumes red: "is_red A p" and sub: "A \<subseteq> B"
  shows "is_red B p"
proof -
  from red obtain f t where "f \<in> A" and "t \<in> keys p" and "f \<noteq> 0" and "lp f adds t" by (rule is_red_addsE)
  show ?thesis by (rule is_red_addsI, rule, fact+)
qed

lemma not_is_red_empty: "\<not> is_red {} f"
  by (simp add: is_red_adds_iff)

lemma red_single_mult_const:
  assumes "red_single p q f t" and "c \<noteq> 0"
  shows "red_single p q (monom_mult c 0 f) t"
proof -
  let ?s = "t + lp f"
  let ?f = "monom_mult c 0 f"
  from assms(1) have "f \<noteq> 0" and "lookup p ?s \<noteq> 0"
    and "q = p - monom_mult ((lookup p ?s) / lc f) t f" by (simp_all add: red_single_def)
  from this(1) assms(2) have lp: "lp ?f = lp f" and lc: "lc ?f = c * lc f"
    by (simp add: lp_monom_mult, simp add: lc_monom_mult)
  show ?thesis unfolding red_single_def
  proof (intro conjI)
    from \<open>f \<noteq> 0\<close> assms(2) show "?f \<noteq> 0" by (simp add: monom_mult_0_iff)
  next
    from \<open>lookup p ?s \<noteq> 0\<close> show "lookup p (t + lp ?f) \<noteq> 0" by (simp add: lp)
  next
    show "q = p - monom_mult (lookup p (t + lp ?f) / lc ?f) t ?f"
      by (simp add: lp monom_mult_assoc lc assms(2), fact)
  qed
qed

lemma red_rtrancl_plus_higher:
  assumes "(red F)\<^sup>*\<^sup>* p q" and "\<And>s t. s \<in> keys p \<Longrightarrow> t \<in> keys r \<Longrightarrow> s \<prec> t"
  shows "(red F)\<^sup>*\<^sup>* (p + r) (q + r)"
  using assms(1)
proof induct
  case base
  show ?case ..
next
  case (step y z)
  from step(1) have "y \<preceq>p p" by (rule red_rtrancl_ord)
  hence "lp y \<preceq> lp p" by (rule ord_p_lp)
  from step(2) have "red F (y + r) (z + r)"
  proof (rule red_plus_keys_disjoint)
    show "keys y \<inter> keys r = {}"
    proof (rule ccontr)
      assume "keys y \<inter> keys r \<noteq> {}"
      then obtain t where "t \<in> keys y" and "t \<in> keys r" by auto
      from this(1) have "t \<preceq> lp y" and "y \<noteq> 0" using lp_max by auto
      with \<open>y \<preceq>p p\<close> have "p \<noteq> 0" using ord_p_0_min[of y] by auto
      hence "lp p \<in> keys p" by (rule lp_in_keys)
      from this \<open>t \<in> keys r\<close> have "lp p \<prec> t" by (rule assms(2))
      with \<open>lp y \<preceq> lp p\<close> have "lp y \<prec> t" by simp
      with \<open>t \<preceq> lp y\<close>  show False by simp
    qed
  qed
  with step(3) show ?case ..
qed

lemma red_monom_mult_leading_monomial: "(red {f})\<^sup>*\<^sup>* (monom_mult (lc f) (lp f) p) (- p * tail f)"
proof (cases "f = 0")
  case True
  show ?thesis by (simp add: True lc_def monom_mult_left0)
next
  case False
  show ?thesis
  proof (induct p rule: poly_mapping_tail_induct)
    case 0
    show ?case by (simp add: monom_mult_right0)
  next
    case (tail p)
    from False have "lc f \<noteq> 0" by (rule lc_not_0)
    from tail(1) have "lc p \<noteq> 0" by (rule lc_not_0)
    let ?t = "monom_mult (lc f) (lp f) (tail p)"
    let ?m = "monom_mult (lc f) (lp f) (monomial (lc p) (lp p))"
    have m: "?m = monom_mult (lc p) (lp p) (monomial (lc f) (lp f))"
      by (simp add: monom_mult_monomial ac_simps)
    from \<open>lc f \<noteq> 0\<close> have kt: "keys ?t = plus (lp f) ` keys (tail p)" by (rule keys_monom_mult)
    thm keys_monom_mult[OF \<open>lc f \<noteq> 0\<close>] keys_single
    have km: "keys ?m = {lp f + lp p}" by (simp add: keys_monom_mult[OF \<open>lc f \<noteq> 0\<close>] \<open>lc p \<noteq> 0\<close>)
    from tail(2) have "(red {f})\<^sup>*\<^sup>* (?t + ?m) (- tail p * tail f + ?m)"
    proof (rule red_rtrancl_plus_higher)
      fix s t
      assume "s \<in> keys ?t" and "t \<in> keys ?m"
      from this(1) obtain u where "u \<in> keys (tail p)" and s: "s = lp f + u" unfolding kt ..
      from this(1) have "tail p \<noteq> 0" and "u \<preceq> lp (tail p)" using lp_max by auto
      moreover from \<open>tail p \<noteq> 0\<close> have "lp (tail p) \<prec> lp p" by (rule lp_tail)
      ultimately have "u \<prec> lp p" by simp
      moreover from \<open>t \<in> keys ?m\<close> have "t = lp f + lp p" by (simp only: km, simp)
      ultimately show "s \<prec> t" by (simp add: s plus_monotone_strict_left)
    qed
    hence *: "(red {f})\<^sup>*\<^sup>* (monom_mult (lc f) (lp f) p) (?m - tail p * tail f)"
      by (simp add: leading_monomial_tail[symmetric, of p] add.commute[of "tail p"] monom_mult_dist_right[symmetric])
    have "red {f} ?m (- (monomial (lc p) (lp p)) * tail f)" unfolding red_singleton
    proof
      have lp: "lp p + lp f = lp f + lp p" by (simp only: add.commute)
      thm times_monomial_left
      show "red_single ?m (- (monomial (lc p) (lp p)) * tail f) f (lp p)"
      proof (simp add: red_single_def \<open>f \<noteq> 0\<close> km lp lookup_monom_mult \<open>lc f \<noteq> 0\<close> \<open>lc p \<noteq> 0\<close>,
              simp add: m monom_mult_dist_right_minus[symmetric] times_monomial_left)
        have "monom_mult (lc p) (lp p) (monomial (lc f) (lp f) - f) =
              - monom_mult (lc p) (lp p) (f - monomial (lc f) (lp f))"
          by (metis minus_diff_eq monom_mult_uminus_right)
        also have "... = - monom_mult (lc p) (lp p) (tail f)" by (simp only: tail_alt_2)
        finally show "- monom_mult (lc p) (lp p) (tail f) =
                      monom_mult (lc p) (lp p) (monomial (lc f) (lp f) - f)" by simp
      qed
    qed
    hence "red {f} (?m + (- tail p * tail f)) (- (monomial (lc p) (lp p)) * tail f + (- tail p * tail f))"
    proof (rule red_plus_keys_disjoint)
      show "keys ?m \<inter> keys (- tail p * tail f) = {}"
      proof (cases "tail p = 0")
        case True
        show ?thesis by (simp add: True)
      next
        case False
        from tail(2) have "- tail p * tail f \<preceq>p ?t" by (rule red_rtrancl_ord)
        hence "lp (- tail p * tail f) \<preceq> lp ?t" by (rule ord_p_lp)
        also from \<open>lc f \<noteq> 0\<close> False have "... = lp f + lp (tail p)" by (rule lp_monom_mult)
        also from lp_tail[OF False] have "... \<prec> lp f + lp p" by (rule plus_monotone_strict_left)
        finally have "lp f + lp p \<notin> keys (- tail p * tail f)" using lp_gr_keys by blast
        thus ?thesis by (simp add: km)
      qed
    qed
    hence "red {f} (?m - tail p * tail f) (- (monomial (lc p) (lp p)) * tail f - tail p * tail f)"
      by simp
    also have "... = - p * tail f" using leading_monomial_tail[symmetric, of p]
      by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus distrib_right
            minus_add_distrib mult_minus_left)
    finally have "red {f} (?m - tail p * tail f) (- p * tail f)" .
    with * show ?case ..
  qed
qed

corollary red_monom_mult_lp:
  assumes "f \<noteq> 0"
  shows "(red {f})\<^sup>*\<^sup>* (monom_mult c (lp f) p) (monom_mult (- c / lc f) 0 (p * tail f))"
proof -
  from assms have "lc f \<noteq> 0" by (rule lc_not_0)
  hence 1: "monom_mult c (lp f) p = monom_mult (lc f) (lp f) (monom_mult (c / lc f) 0 p)"
    by (simp add: monom_mult_assoc)
  have 2: "monom_mult (- c / lc f) 0 (p * tail f) = - (monom_mult (c / lc f) 0 p) * tail f"
    by (simp add: monom_mult_uminus_left, simp add: times_monomial_left[symmetric])
  show ?thesis unfolding 1 2 by (fact red_monom_mult_leading_monomial)
qed

lemma is_red_monomial_iff: "is_red F (monomial c t) \<longleftrightarrow> (c \<noteq> 0 \<and> (\<exists>f\<in>F. f \<noteq> 0 \<and> lp f adds t))"
  by (simp add: is_red_adds_iff)

lemma is_red_monomialI:
  assumes "c \<noteq> 0" and "f \<in> F" and "f \<noteq> 0" and "lp f adds t"
  shows "is_red F (monomial c t)"
  unfolding is_red_monomial_iff using assms by blast

lemma is_red_monomialD:
  assumes "is_red F (monomial c t)"
  shows "c \<noteq> 0"
  using assms unfolding is_red_monomial_iff ..

lemma is_red_monomialE:
  assumes "is_red F (monomial c t)"
  obtains f where "f \<in> F" and "f \<noteq> 0" and "lp f adds t"
  using assms unfolding is_red_monomial_iff by blast

lemma replace_lp_adds_stable_is_red:
  assumes red: "is_red F f" and "q \<noteq> 0" and "lp q adds lp p"
  shows "is_red (insert q (F - {p})) f"
proof -
  from red obtain g t where "g \<in> F" and "g \<noteq> 0" and "t \<in> keys f" and "lp g adds t" by (rule is_red_addsE)
  show ?thesis
  proof (cases "g = p")
    case True
    show ?thesis
    proof (rule is_red_addsI)
      show "q \<in> insert q (F - {p})" by simp
    next
      have "lp q adds lp p" by fact
      also have "... adds t" using \<open>lp g adds t\<close> unfolding True .
      finally show "lp q adds t" .
    qed (fact+)
  next
    case False
    with \<open>g \<in> F\<close> have "g \<in> insert q (F - {p})" by blast
    from this \<open>g \<noteq> 0\<close> \<open>t \<in> keys f\<close> \<open>lp g adds t\<close> show ?thesis by (rule is_red_addsI)
  qed
qed
  
lemma conversion_property:
  assumes "is_red {p} f" and "red {r} p q"
  shows "is_red {q} f \<or> is_red {r} f"
proof -
  from \<open>is_red {p} f\<close> obtain t where "t \<in> keys f" and "lp p adds t" and "p \<noteq> 0" by (rule is_red_addsE, simp)
  from red_indE[OF \<open>red {r} p q\<close>]
    have "(r \<noteq> 0 \<and> lp r adds lp p \<and> q = p - monom_mult (lc p / lc r) (lp p - lp r) r) \<or>
          red {r} (tail p) (q - monomial (lc p) (lp p))" by simp
  thus ?thesis
  proof
    assume "r \<noteq> 0 \<and> lp r adds lp p \<and> q = p - monom_mult (lc p / lc r) (lp p - lp r) r"
    hence "r \<noteq> 0" and "lp r adds lp p" by simp_all
    show ?thesis by (intro disjI2, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  next
    assume "red {r} (tail p) (q - monomial (lc p) (lp p))" (is "red _ ?p' ?q'")
    with red_ord have "?q' \<prec>p ?p'" .
    hence "?p' \<noteq> 0"
      and assm: "(?q' = 0 \<or> ((lp ?q') \<prec> (lp ?p') \<or> (lp ?q') = (lp ?p')))"
      unfolding ord_strict_p_rec[of ?q' ?p'] by (auto simp add: Let_def lc_def)
    have "lp ?p' \<prec> lp p" by (rule lp_tail, fact)
    let ?m = "monomial (lc p) (lp p)"
    from monomial_0D[of "lp p" "lc p"] lc_not_0[OF \<open>p \<noteq> 0\<close>] have "?m \<noteq> 0" by blast
    have "lp ?m = lp p" by (rule lp_monomial, rule lc_not_0, fact)
    have "q \<noteq> 0 \<and> lp q = lp p"
    proof (cases "?q' = 0")
      case True
      hence "q = ?m" by simp
      with \<open>?m \<noteq> 0\<close> \<open>lp ?m = lp p\<close> show ?thesis by simp
    next
      case False
      from assm show ?thesis
      proof
        assume "(lp ?q') \<prec> (lp ?p') \<or> (lp ?q') = (lp ?p')"
        hence "lp ?q' \<preceq> lp ?p'" by auto
        also have "... \<prec> lp p" by fact
        finally have "lp ?q' \<prec> lp p" .
        hence "lp ?q' \<prec> lp ?m" unfolding \<open>lp ?m = lp p\<close> .
        from lp_plus_eqI[OF this] \<open>lp ?m = lp p\<close> have "lp q = lp p" by simp
        show ?thesis
        proof (intro conjI, rule ccontr)
          assume "\<not> q \<noteq> 0"
          hence "q = 0" by simp
          hence "?q' = -?m" by simp
          hence "lp ?q' = lp (-?m)" by simp
          also have "... = lp ?m" using lp_uminus .
          finally have "lp ?q' = lp ?m" .
          with \<open>lp ?q' \<prec> lp ?m\<close> show False by simp
        qed (fact)
      next
        assume "?q' = 0"
        with False show ?thesis ..
      qed
    qed
    hence "q \<noteq> 0" and "lp q adds lp p" by simp_all
    show ?thesis by (intro disjI1, rule is_red_singleton_trans, rule \<open>is_red {p} f\<close>, fact+)
  qed
qed
  
lemma replace_red_stable_is_red:
  assumes a1: "is_red F f" and a2: "red (F - {p}) p q"
  shows "is_red (insert q (F - {p})) f" (is "is_red ?F' f")
proof -
  from a1 obtain g where "g \<in> F" and "is_red {g} f" by (rule is_red_singletonI)
  show ?thesis
  proof (cases "g = p")
    case True
    from a2 obtain h where "h \<in> F - {p}" and "red {h} p q" unfolding red_def by auto
    from \<open>is_red {g} f\<close> have "is_red {p} f" unfolding True .
    have "is_red {q} f \<or> is_red {h} f" by (rule conversion_property, fact+)
    thus ?thesis
    proof
      assume "is_red {q} f"
      show ?thesis
      proof (rule is_red_singletonD)
        show "q \<in> ?F'" by auto
      qed fact
    next
      assume "is_red {h} f"
      show ?thesis
      proof (rule is_red_singletonD)
        from \<open>h \<in> F - {p}\<close> show "h \<in> ?F'" by simp
      qed fact
    qed
  next
    case False
    show ?thesis
    proof (rule is_red_singletonD)
      from \<open>g \<in> F\<close> False show "g \<in> ?F'" by blast
    qed fact
  qed
qed

end (* ordered_powerprod *)

subsection \<open>Well-foundedness and Termination\<close>

context gd_powerprod
begin

lemma dgrad_set_le_red_single:
  assumes "dickson_grading (+) d" and "red_single p q f t"
  shows "dgrad_set_le d {t} (keys p)"
proof (rule dgrad_set_leI, simp)
  have "t adds t + lp f" by simp
  with assms(1) have "d t \<le> d (t + lp f)" by (rule dickson_grading_adds_imp_le)
  moreover from assms(2) have "t + lp f \<in> keys p" by (simp add: red_single_def)
  ultimately show "\<exists>s\<in>keys p. d t \<le> d s" ..
qed

lemma dgrad_p_set_le_red_single:
  assumes "dickson_grading (+) d" and "red_single p q f t"
  shows "dgrad_p_set_le d {q} {f, p}"
proof -
  let ?f = "monom_mult ((lookup p (t + lp f)) / lc f) t f"
  from assms(2) have "t + lp f \<in> keys p" and q: "q = p - ?f" by (simp_all add: red_single_def)
  have "dgrad_p_set_le d {q} {p, ?f}" unfolding q by (fact dgrad_p_set_le_minus)
  also have "dgrad_p_set_le d ... {f, p}"
  proof (rule dgrad_p_set_leI_insert)
    from assms(1) have "dgrad_set_le d (keys ?f) (insert t (keys f))"
      by (rule dgrad_set_le_monom_mult)
    also have "dgrad_set_le d ... (keys f \<union> keys p)"
    proof (rule dgrad_set_leI, simp)
      fix s
      assume "s = t \<or> s \<in> keys f"
      thus "\<exists>u\<in>keys f \<union> keys p. d s \<le> d u"
      proof
        assume "s = t"
        from assms have "dgrad_set_le d {s} (keys p)" unfolding \<open>s = t\<close>
          by (rule dgrad_set_le_red_single)
        moreover have "s \<in> {s}" ..
        ultimately obtain u where "u \<in> keys p" and "d s \<le> d u" by (rule dgrad_set_leE)
        from this(1) have "u \<in> keys f \<union> keys p" by simp
        with \<open>d s \<le> d u\<close> show ?thesis ..
      next
        assume "s \<in> keys f"
        hence "s \<in> keys f \<union> keys p" by simp
        moreover have "d s \<le> d s" ..
        ultimately show ?thesis ..
      qed
    qed
    finally show "dgrad_p_set_le d {?f} {f, p}" by (simp add: dgrad_p_set_le_def Keys_insert)
  next
    show "dgrad_p_set_le d {p} {f, p}" by (rule dgrad_p_set_le_subset, simp)
  qed
  finally show ?thesis .
qed

lemma dgrad_p_set_le_red:
  assumes "dickson_grading (+) d" and "red F p q"
  shows "dgrad_p_set_le d {q} (insert p F)"
proof -
  from assms(2) obtain f t where "f \<in> F" and "red_single p q f t" by (rule red_setE)
  from assms(1) this(2) have "dgrad_p_set_le d {q} {f, p}" by (rule dgrad_p_set_le_red_single)
  also have "dgrad_p_set_le d ... (insert p F)" by (rule dgrad_p_set_le_subset, auto intro: \<open>f \<in> F\<close>)
  finally show ?thesis .
qed

corollary dgrad_p_set_le_red_rtrancl:
  assumes "dickson_grading (+) d" and "(red F)\<^sup>*\<^sup>* p q"
  shows "dgrad_p_set_le d {q} (insert p F)"
  using assms(2)
proof (induct)
  case base
  show ?case by (rule dgrad_p_set_le_subset, simp)
next
  case (step y z)
  from assms(1) step(2) have "dgrad_p_set_le d {z} (insert y F)" by (rule dgrad_p_set_le_red)
  also have "dgrad_p_set_le d ... (insert p F)"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d F (insert p F)" by (rule dgrad_p_set_le_subset, blast)
  qed fact
  finally show ?case .
qed

lemma dgrad_p_set_red_single_pp:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "red_single p q f t"
  shows "d t \<le> m"
proof -
  from assms(1) assms(3) have "dgrad_set_le d {t} (keys p)" by (rule dgrad_set_le_red_single)
  moreover have "t \<in> {t}" ..
  ultimately obtain s where "s \<in> keys p" and "d t \<le> d s" by (rule dgrad_set_leE)
  from assms(2) this(1) have "d s \<le> m" by (rule dgrad_p_setD)
  with \<open>d t \<le> d s\<close> show ?thesis by (rule le_trans)
qed

lemma dgrad_p_set_closed_red_single:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "f \<in> dgrad_p_set d m"
    and "red_single p q f t"
  shows "q \<in> dgrad_p_set d m"
proof -
  from dgrad_p_set_le_red_single[OF assms(1, 4)] have "{q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(2, 3) show "{f, p} \<subseteq> dgrad_p_set d m" by simp
  qed
  thus ?thesis by simp
qed

lemma dgrad_p_set_closed_red:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m" and "red F p q"
  shows "q \<in> dgrad_p_set d m"
proof -
  from assms(4) obtain f t where "f \<in> F" and *: "red_single p q f t" by (rule red_setE)
  from assms(2) this(1) have "f \<in> dgrad_p_set d m" ..
  from assms(1) assms(3) this * show ?thesis by (rule dgrad_p_set_closed_red_single)
qed

lemma dgrad_p_set_closed_red_rtrancl:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m" and "(red F)\<^sup>*\<^sup>* p q"
  shows "q \<in> dgrad_p_set d m"
  using assms(4)
proof (induct)
  case base
  from assms(3) show ?case .
next
  case (step r q)
  from assms(1) assms(2) step(3) step(2) show "q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red)
qed

lemma is_relation_order_red:
  assumes "dickson_grading (+) d"
  shows "Confluence.relation_order (red F) (\<prec>p) (dgrad_p_set d m)"
proof
  show "wfP_on (dgrad_p_set d m) (\<prec>p)"
  proof (rule wfP_onI_min)
    fix x::"'a \<Rightarrow>\<^sub>0 'c" and Q
    assume "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
    with assms obtain q where "q \<in> Q" and *: "\<And>y. y \<prec>p q \<Longrightarrow> y \<notin> Q"
      by (rule ord_p_minimum_dgrad_p_set, auto)
    from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_p_set d m. y \<prec>p z \<longrightarrow> y \<notin> Q"
    proof
      from * show "\<forall>y\<in>dgrad_p_set d m. y \<prec>p q \<longrightarrow> y \<notin> Q" by auto
    qed
  qed
next
  show "red F \<le> (\<prec>p)\<inverse>\<inverse>" by (simp add: predicate2I red_ord)
qed (fact ord_strict_p_transitive)

lemma red_wf_dgrad_p_set_aux:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "wfP_on (dgrad_p_set d m) (red F)\<inverse>\<inverse>"
proof (rule wfP_onI_min)
  fix x::"'a \<Rightarrow>\<^sub>0 'b" and Q
  assume "x \<in> Q" and "Q \<subseteq> dgrad_p_set d m"
  with assms(1) obtain q where "q \<in> Q" and *: "\<And>y. y \<prec>p q \<Longrightarrow> y \<notin> Q"
    by (rule ord_p_minimum_dgrad_p_set, auto)
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>dgrad_p_set d m. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>dgrad_p_set d m. (red F)\<inverse>\<inverse> y q \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI, simp)
      fix y
      assume "red F q y"
      hence "y \<prec>p q" by (rule red_ord)
      thus "y \<notin> Q" by (rule *)
    qed
  qed
qed

lemma red_wf_dgrad_p_set:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m"
  shows "wfP (red F)\<inverse>\<inverse>"
proof (rule wfI_min[to_pred])
  fix x::"'a \<Rightarrow>\<^sub>0 'b" and Q
  assume "x \<in> Q"
  from assms(2) obtain n where "m \<le> n" and "x \<in> dgrad_p_set d n" and "F \<subseteq> dgrad_p_set d n"
    by (rule dgrad_p_set_insert)
  let ?Q = "Q \<inter> dgrad_p_set d n"
  from assms(1) \<open>F \<subseteq> dgrad_p_set d n\<close> have "wfP_on (dgrad_p_set d n) (red F)\<inverse>\<inverse>"
    by (rule red_wf_dgrad_p_set_aux)
  moreover from \<open>x \<in> Q\<close> \<open>x \<in> dgrad_p_set d n\<close> have "x \<in> ?Q" ..
  moreover have "?Q \<subseteq> dgrad_p_set d n" by simp
  ultimately obtain z where "z \<in> ?Q" and *: "\<And>y. (red F)\<inverse>\<inverse> y z \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and "z \<in> dgrad_p_set d n" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(red F)\<inverse>\<inverse> y z"
      hence "red F z y" by simp
      with assms(1) \<open>F \<subseteq> dgrad_p_set d n\<close> \<open>z \<in> dgrad_p_set d n\<close> have "y \<in> dgrad_p_set d n"
        by (rule dgrad_p_set_closed_red)
      moreover from \<open>(red F)\<inverse>\<inverse> y z\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by blast
    qed
  qed
qed

lemmas red_wf_finite = red_wf_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

lemma cbelow_on_monom_mult:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "d t \<le> m" and "c \<noteq> 0"
    and "cbelow_on (dgrad_p_set d m) (\<prec>p) z (\<lambda>a b. red F a b \<or> red F b a) p q"
  shows "cbelow_on (dgrad_p_set d m) (\<prec>p) (monom_mult c t z) (\<lambda>a b. red F a b \<or> red F b a)
          (monom_mult c t p) (monom_mult c t q)"
  using assms(5)
proof (induct rule: cbelow_on_induct)
  case base
  show ?case unfolding cbelow_on_def
  proof (rule disjI1, intro conjI, fact refl)
    from assms(5) have "p \<in> dgrad_p_set d m" by (rule cbelow_on_first_in)
    with assms(1) assms(3) show "monom_mult c t p \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_monom_mult)
  next
    from assms(5) have "p \<prec>p z" by (rule cbelow_on_first_below)
    from this assms(4) show "monom_mult c t p \<prec>p monom_mult c t z" by (rule ord_strict_p_monom_mult)
  qed
next
  case (step q' q)
  let ?R = "\<lambda>a b. red F a b \<or> red F b a"
  from step(5) show ?case
  proof
    from assms(1) assms(3) step(3) show "monom_mult c t q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_monom_mult)
  next
    from step(2) red_monom_mult[OF _ assms(4)] show "?R (monom_mult c t q') (monom_mult c t q)" by auto
  next
    from step(4) assms(4) show "monom_mult c t q \<prec>p monom_mult c t z" by (rule ord_strict_p_monom_mult)
  qed
qed

lemma cbelow_on_monom_mult_monomial:
  assumes "c \<noteq> 0"
    and "cbelow_on (dgrad_p_set d m) (\<prec>p) (monomial c' t) (\<lambda>a b. red F a b \<or> red F b a) p q"
  shows "cbelow_on (dgrad_p_set d m) (\<prec>p) (monomial c (s + t)) (\<lambda>a b. red F a b \<or> red F b a) p q"
proof -
  have *: "f \<prec>p monomial c' t \<Longrightarrow> f \<prec>p monomial c (s + t)" for f
  proof (simp add: ord_strict_p_monomial_iff assms(1), elim conjE disjE, erule disjI1, rule disjI2)
    assume "lp f \<prec> t"
    also have "... \<preceq> s + t" using local.zero_min plus_monotone by fastforce
    finally show "lp f \<prec> s + t" .
  qed
  from assms(2) show ?thesis
  proof (induct rule: cbelow_on_induct)
    case base
    show ?case unfolding cbelow_on_def
    proof (rule disjI1, intro conjI, fact refl)
      from assms(2) show "p \<in> dgrad_p_set d m" by (rule cbelow_on_first_in)
    next
      from assms(2) have "p \<prec>p monomial c' t" by (rule cbelow_on_first_below)
      thus "p \<prec>p monomial c (s + t)" by (rule *)
    qed
  next
    case (step q' q)
    let ?R = "\<lambda>a b. red F a b \<or> red F b a"
    from step(5) step(3) step(2) show ?case
    proof
      from step(4) show "q \<prec>p monomial c (s + t)" by (rule *)
    qed
  qed
qed

lemma cbelow_on_plus:
  assumes "dickson_grading (+) d" and "F \<subseteq> dgrad_p_set d m" and "r \<in> dgrad_p_set d m"
    and "keys r \<inter> keys z = {}"
    and "cbelow_on (dgrad_p_set d m) (\<prec>p) z (\<lambda>a b. red F a b \<or> red F b a) p q"
  shows "cbelow_on (dgrad_p_set d m) (\<prec>p) (z + r) (\<lambda>a b. red F a b \<or> red F b a) (p + r) (q + r)"
  using assms(5)
proof (induct rule: cbelow_on_induct)
  case base
  show ?case unfolding cbelow_on_def
  proof (rule disjI1, intro conjI, fact refl)
    from assms(5) have "p \<in> dgrad_p_set d m" by (rule cbelow_on_first_in)
    from this assms(3) show "p + r \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_plus)
  next
    from assms(5) have "p \<prec>p z" by (rule cbelow_on_first_below)
    from this assms(4) show "p + r \<prec>p z + r" by (rule ord_strict_p_plus)
  qed
next
  case (step q' q)
  let ?RS = "\<lambda>a b. red F a b \<or> red F b a"
  let ?A = "dgrad_p_set d m"
  let ?R = "red F"
  let ?ord = "(\<prec>p)"
  from assms(1) have ro: "relation_order ?R ?ord ?A"
    by (rule is_relation_order_red)
  have dw: "relation.dw_closed ?R ?A"
    by (rule relation.dw_closedI, rule dgrad_p_set_closed_red, rule assms(1), rule assms(2))
  from step(2) have "relation.cs (red F) (q' + r) (q + r)"
  proof
    assume "red F q q'"
    hence "relation.cs (red F) (q + r) (q' + r)" by (rule red_plus_cs)
    thus ?thesis by (rule relation.cs_sym)
  next
    assume "red F q' q"
    thus ?thesis by (rule red_plus_cs)
  qed
  with ro dw have "cbelow_on ?A ?ord (z + r) ?RS (q' + r) (q + r)"
  proof (rule relation_order.cs_implies_cbelow_on)
    from step(1) have "q' \<in> ?A" by (rule cbelow_on_second_in)
    from this assms(3) show "q' + r \<in> ?A" by (rule dgrad_p_set_closed_plus)
  next
    from step(3) assms(3) show "q + r \<in> ?A" by (rule dgrad_p_set_closed_plus)
  next
    from step(1) have "q' \<prec>p z" by (rule cbelow_on_second_below)
    from this assms(4) show "q' + r \<prec>p z + r" by (rule ord_strict_p_plus)
  next
    from step(4) assms(4) show "q + r \<prec>p z + r" by (rule ord_strict_p_plus)
  qed
  with step(5) show ?case by (rule cbelow_on_transitive)
qed

end (* gd_powerprod *)

subsection \<open>Algorithms\<close>

subsubsection \<open>Function @{term rd}\<close>

context ordered_powerprod
begin

function rd_mult :: "('a \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('b \<times> 'a) option" where
  "rd_mult p f =
    (if p = 0 then
      None
    else
      (if lp f adds lp p then
        Some (lc p / lc f, lp p - lp f)
      else
        rd_mult (tail p) f
      )
    )"
  by auto
termination proof -
  let ?R = "{(x, y::'a \<Rightarrow>\<^sub>0 'b). keys x \<subset> keys y} <*lex*> {}"
  show ?thesis
  proof
    show "wf ?R"
    proof
      from keys_subset_wf show "wf {(x, y). keys x \<subset> keys y}" by (simp only: wfP_def)
    qed simp
  next
    fix p f::"'a \<Rightarrow>\<^sub>0 'b"
    assume "p \<noteq> 0"
    hence "lp p \<in> keys p" by (rule lp_in_keys)
    hence "keys (tail p) \<subset> keys p" unfolding keys_tail by auto
    thus "((tail p, f), p, f) \<in> ?R" by simp
  qed
qed

definition rd::"('a \<Rightarrow>\<^sub>0 'b::field) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> bool)"
  where "rd p f =
          (if f = 0 then
            (p, False)
          else
            (case rd_mult p f of Some (c, t) \<Rightarrow> (p - monom_mult c t f, True) | None \<Rightarrow> (p, False)))"

lemma compute_rd_mult[code]:
  "rd_mult p f =
    (if p = 0 then
      None
    else
      (if (lp f) adds (lp p) then
        Some (lc p / lc f, lp p - lp f)
      else
        rd_mult (tail p) f
      )
    )"
  by simp

lemma rd_mult_left0: "rd_mult 0 f = None"
  by simp

lemma rd_mult_adds:
  assumes "p \<noteq> 0" and "lp f adds lp p"
  shows "rd_mult p f = Some (lc p / lc f, lp p - lp f)"
  using assms by simp

lemma rd_mult_nadds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "\<not> lp f adds lp p"
  shows "rd_mult p f = rd_mult (tail p) f"
  using assms by simp

lemma rd_left0: "rd 0 f = (0, False)"
  by (simp add: rd_def rd_mult_left0 del: rd_mult.simps)

lemma rd_right0: "rd p 0 = (p, False)"
  by (simp add: rd_def del: rd_mult.simps)

lemma rd_adds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "lp f adds lp p"
  shows "rd p f = (p - monom_mult (lc p / lc f) (lp p - lp f) f, True)"
  by (simp add: rd_def rd_mult_adds[OF assms(1, 3)] assms(2) del: rd_mult.simps)

lemma case_distrib:
  "f (case x of None \<Rightarrow> h | Some (a, b) \<Rightarrow> g a b) = (case x of None \<Rightarrow> f h | Some (a, b) \<Rightarrow> f (g a b))"
  by (simp add: option.case_eq_if split_beta)

lemma fst_rd:
  "fst (rd p f) = (if f = 0 then p else (case rd_mult p f of Some (c, t) \<Rightarrow> p - monom_mult c t f | None \<Rightarrow> p))"
  by (simp add: rd_def case_distrib[of fst] del: rd_mult.simps cong: option.case_cong)

lemma fst_rd_nadds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "\<not> lp f adds lp p"
  shows "fst (rd p f) = (monomial (lc p) (lp p)) + fst (rd (tail p) f)"
  by (simp add: fst_rd rd_mult_nadds[OF assms] assms(2) case_distrib[of "(+) (monomial (lc p) (lp p))"]
      leading_monomial_tail[symmetric] add_diff_eq del: rd_mult.simps cong: option.case_cong)

lemma fst_rd_red_set:
  assumes "is_red {f} p"
  shows "red {f} p (fst (rd p f))"
  using assms
proof (induct p rule: poly_mapping_tail_induct)
  case 0
  from this irred_0[of "{f}"] show "red {f} 0 (fst (rd 0 f))" by simp
next
  case (tail p)
  show "red {f} p (fst (rd p f))"
  proof (cases "\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f adds lp p")
    assume "\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f adds lp p"
    hence "f \<noteq> 0" and "lp f adds lp p" by auto
    have "red {f} p (p - monom_mult (lc p / lc f) (lp p - lp f) f)"
      by (intro red_indI1, simp, fact+)
    with \<open>f \<noteq> 0\<close> show ?thesis using rd_mult_adds[OF \<open>p \<noteq> 0\<close> \<open>lp f adds lp p\<close>] by (simp add: rd_def)
  next
    assume "\<not> (\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f adds lp p)"
    from this is_red_indE[OF tail(3)] have r: "is_red {f} (tail p)"
      and dis: "f = 0 \<or> \<not> (lp f adds lp p)"
      by auto
    from is_red_singleton_not_0[OF r] have "f \<noteq> 0" .
    from dis this have "\<not> (lp f adds lp p)" by simp
    from fst_rd_nadds[OF \<open>p \<noteq> 0\<close> \<open>f \<noteq> 0\<close> this] red_indI2[OF \<open>p \<noteq> 0\<close> tail(2)[OF r]]
      show ?thesis by (simp only: rd_def ac_simps)
  qed
qed

lemma fst_rd_irred_set:
  assumes "\<not> is_red {f} p"
  shows "fst (rd p f) = p"
  using assms
proof (induct p rule: poly_mapping_tail_induct, simp add: rd_left0)
  fix p
  assume "p \<noteq> 0" and IH: "\<not> is_red {f} (tail p) \<Longrightarrow> fst (rd (tail p) f) = tail p"
    and irred: "\<not> is_red {f} p"
  have "f \<in> {f}" by simp
  from irred is_red_indI1[OF this _ \<open>p \<noteq> 0\<close>] have dis: "f = 0 \<or> \<not> (lp f adds lp p)" by auto
  show "fst (rd p f) = p"
  proof (cases "f = 0")
    case True
    thus ?thesis by (simp add: rd_def)
  next
    case False
    hence nadds: "\<not> (lp f adds lp p)" using dis by simp
    from irred is_red_indI2[OF \<open>p \<noteq> 0\<close>, of "{f}"] have "\<not> is_red {f} (tail p)" by auto
    from IH[OF this] fst_rd_nadds[OF \<open>p \<noteq> 0\<close> False nadds] leading_monomial_tail[of p]
      show ?thesis by simp
  qed
qed

lemma fst_rd_red:
  assumes "red_single p q f t"
  shows "\<exists>t. red_single p (fst (rd p f)) f t"
proof -
  have "is_red {f} p" by (intro is_redI, intro red_setI[of f], simp, fact)
  from red_setE[OF fst_rd_red_set[OF this]] obtain t where "red_single p (fst (rd p f)) f t" by force
  show ?thesis by (intro exI, fact)
qed

lemma fst_rd_irred:
  assumes "\<And>q t. \<not> red_single p q f t"
  shows "fst (rd p f) = p"
proof (rule fst_rd_irred_set, rule)
  assume "is_red {f} p"
  from is_redE[OF this] obtain q where "red {f} p q" .
  from red_setE[OF this] obtain t where "red_single p q f t" by force
  from this assms[of q t] show False by simp
qed

lemma fst_rd_id_set: "(fst (rd p f) = p) \<longleftrightarrow> (\<not> is_red {f} p)"
proof
  assume "fst (rd p f) = p"
  show "\<not> is_red {f} p"
  proof
    assume "is_red {f} p"
    from fst_rd_red_set[OF this] \<open>fst (rd p f) = p\<close> have "red {f} p p" by simp
    from red_ord[OF this] show False by simp
  qed
next
  assume a: "\<not> is_red {f} p"
  show "fst (rd p f) = p"
  proof (intro fst_rd_irred_set notI)
    assume "is_red {f} p"
    with \<open>\<not> is_red {f} p\<close> show False ..
  qed
qed

lemma fst_rd_id: "(fst (rd p f) = p) \<longleftrightarrow> (\<forall>q t. \<not> red_single p q f t)"
proof
  assume "fst (rd p f) = p"
  show "\<forall>q t. \<not> red_single p q f t"
  proof (intro allI)
    fix q t
    show "\<not> red_single p q f t"
    proof
      assume "red_single p q f t"
      from fst_rd_red[OF this] obtain s where "red_single p (fst (rd p f)) f s" ..
      hence "red_single p p f s" using \<open>fst (rd p f) = p\<close> by simp
      from red_single_ord[OF this] show False by simp
    qed
  qed
next
  assume a: "\<forall>q t. \<not> red_single p q f t"
  show "fst (rd p f) = p"
  proof (intro fst_rd_irred, intro notI)
    fix q t
    assume "red_single p q f t"
    from this a show False by simp
  qed
qed

lemma fst_rd_less_eq: "fst (rd p f) \<preceq>p p"
proof (cases "is_red {f} p")
  case True
  then obtain q where "red {f} p q" by (rule is_redE)
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  from fst_rd_red[OF this] obtain s where "red_single p (fst (rd p f)) f s" ..
  from red_single_ord[OF this] show ?thesis by simp
next
  case False
  hence "fst (rd p f) = p" using fst_rd_id_set[of p f] by simp
  thus ?thesis by simp
qed

lemma fst_rd_lessI:
  assumes "red_single p q f t"
  shows "fst (rd p f) \<prec>p p"
proof -
  from fst_rd_red[OF assms] obtain s where "red_single p (fst (rd p f)) f s" ..
  from red_single_ord[OF this] show ?thesis .
qed

lemma fst_rd_lessE:
  assumes "fst (rd p f) \<prec>p p"
  obtains t where "red_single p (fst (rd p f)) f t"
proof -
  from assms have "fst (rd p f) \<noteq> p" by simp
  hence "\<exists>q t. red_single p q f t" using fst_rd_id[of p f] by simp
  from this obtain q s where "red_single p q f s" by auto
  from fst_rd_red[OF this] obtain t where "red_single p (fst (rd p f)) f t" ..
  thus ?thesis ..
qed

lemma snd_rd_iff_neq: "snd (rd p f) \<longleftrightarrow> (fst (rd p f) \<noteq> p)"
proof (simp add: rd_def del: rd_mult.simps split: option.split, intro allI impI)
  fix c t
  assume "f \<noteq> 0"
  assume "rd_mult p f = Some (c, t)"
  hence "c \<noteq> 0"
  proof (induct p rule: poly_mapping_tail_induct)
    case 0
    thus ?case by simp
  next
    case (tail p)
    from tail(3) show ?case
    proof (simp add: compute_rd_mult[of p] del: rd_mult.simps split: if_splits)
      assume "lc p / lc f = c \<and> lp p - lp f = t"
      hence c: "c = lc p / lc f" by simp
      assume "p \<noteq> 0"
      hence "lc p \<noteq> 0" by (rule lc_not_0)
      moreover from \<open>f \<noteq> 0\<close> have "lc f \<noteq> 0" by (rule lc_not_0)
      ultimately show ?thesis by (simp add: c)
    next
      assume "rd_mult (tail p) f = Some (c, t)"
      thus ?thesis by (rule tail(2))
    qed
  qed
  with \<open>f \<noteq> 0\<close> show "monom_mult c t f \<noteq> 0" by (simp add: monom_mult_0_iff)
qed

corollary snd_rd_iff_is_red: "snd (rd p f) \<longleftrightarrow> (is_red {f} p)"
  by (simp add: snd_rd_iff_neq fst_rd_id_set)

subsubsection \<open>Functions @{term rd_list} and @{term trd}\<close>

primrec rd_list::"('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<times> bool" where
  rd_list_base: "rd_list Nil p = (p, False)"|
  rd_list_rec: "rd_list (f # fs) p = (let q = rd p f in (if snd q then q else rd_list fs p))"

lemma fst_rd_list_red:
  assumes "is_red (set fs) p"
  shows "red (set fs) p (fst (rd_list fs p))"
  using assms
proof (induct fs)
  case Nil
  from Nil have "is_red {} p" by simp
  then obtain q where "red {} p q" by (rule is_redE)
  from red_setE[OF this] obtain f t where "f \<in> {}" and "red_single p q f t" .
  from \<open>f \<in> {}\<close> show "red (set []) p (fst (rd_list [] p))" ..
next
  case (Cons f fs)
  show "red (set (f # fs)) p (fst (rd_list (f # fs) p))" unfolding rd_list_rec
  proof (cases "snd (rd p f)")
    case True
    hence "is_red {f} p" by (simp only: snd_rd_iff_is_red)
    have "red ({f} \<union> (set fs)) p (fst (rd p f))" by (rule red_unionI1, rule fst_rd_red_set, fact)
    with True show "red (set (f # fs)) p (fst (let q = rd p f in if snd q then q else rd_list fs p))"
      by simp
  next
    case False
    hence irred: "\<not> is_red {f} p" by (simp add: snd_rd_iff_is_red)
    from Cons(2) have "is_red ({f} \<union> (set fs)) p" by simp
    hence "is_red {f} p \<or> is_red (set fs) p" by (simp only: is_red_union)
    with irred have "is_red (set fs) p" by simp
    hence "red (set fs) p (fst (rd_list fs p))" by (rule Cons(1))
    hence "red (set (f # fs)) p (fst (rd_list fs p))" by (meson red_subset set_subset_Cons)
    thus "red (set (f # fs)) p (fst (let q = rd p f in if snd q then q else rd_list fs p))"
      by (simp add: Let_def False)
  qed
qed

lemma rd_list_fixpointI:
  assumes "\<not> is_red (set fs) p"
  shows "fst (rd_list fs p) = p"
  using assms
proof (induct fs, simp)
  fix f fs
  assume IH: "(\<not> is_red (set fs) p) \<Longrightarrow> fst (rd_list fs p) = p"
    and irred: "\<not> is_red (set (f # fs)) p"
  from irred have "\<not> is_red ({f} \<union> (set fs)) p" by simp
  hence "\<not> ((is_red {f} p) \<or> (is_red (set fs) p))" using is_red_union[of "{f}" "set fs" p] by simp
  hence irred1: "\<not> is_red {f} p" and irred2: "\<not> is_red (set fs) p" by simp_all
  from irred1 have eq: "\<not> snd (rd p f)" by (simp add: snd_rd_iff_is_red)
  from IH[OF irred2] eq show "fst (rd_list (f # fs) p) = p" by simp
qed

lemma rd_list_fixpointD:
  assumes "fst (rd_list fs p) = p"
  shows "\<not> is_red (set fs) p"
proof
  assume "is_red (set fs) p"
  from red_ord[OF fst_rd_list_red[OF this]] assms show False by simp
qed

corollary fst_rd_list_id: "(fst (rd_list fs p) = p) \<longleftrightarrow> (\<not> is_red (set fs) p)"
  using rd_list_fixpointI rd_list_fixpointD by auto

lemma fst_rd_list_le: "fst (rd_list fs p) \<preceq>p p"
proof (cases "is_red (set fs) p")
  case True
  from red_ord[OF fst_rd_list_red[OF this]] show ?thesis by simp
next
  case False
  from rd_list_fixpointI[OF this] show ?thesis by simp
qed

lemma fst_rd_list_in_pideal_ind:
  assumes "set fs \<subseteq> bs"
  shows "p - fst (rd_list fs p) \<in> pideal bs"
  using assms
proof (induct fs)
  from ideal.module_0 show "p - fst (rd_list [] p) \<in> pideal bs" by simp
next
  fix a fs
  assume IH: "set fs \<subseteq> bs \<Longrightarrow> p - fst (rd_list fs p) \<in> pideal bs" and a: "set (a # fs) \<subseteq> bs"
  from a have "a \<in> bs" by simp
  from a have "set fs \<subseteq> bs" by simp
  show "p - fst (rd_list (a # fs) p) \<in> pideal bs" unfolding rd_list_rec Let_def
  proof (simp add: if_splits, rule, intro impI)
    assume "snd (rd p a)"
    hence "fst (rd p a) \<noteq> p" by (simp add: fst_rd_id_set snd_rd_iff_is_red)
    hence "fst (rd p a) \<prec>p p" using fst_rd_less_eq[of p a] by simp
    from fst_rd_lessE[OF this] obtain t where "red_single p (fst (rd p a)) a t" .
    hence eq: "p - fst (rd p a) = monom_mult (lookup p (t + lp a) / lc a) t a"
      unfolding red_single_def by simp
    show "p - fst (rd p a) \<in> pideal bs" unfolding eq by (rule monom_mult_in_pideal, rule \<open>a \<in> bs\<close>)
  next
    show "\<not> snd (rd p a) \<longrightarrow> p - fst (rd_list fs p) \<in> pideal bs"
    proof
      assume "\<not> snd (rd p a)"
      from IH[OF \<open>set fs \<subseteq> bs\<close>] show "p - fst (rd_list fs p) \<in> pideal bs" .
    qed
  qed
qed

lemma fst_rd_list_in_pideal: "p - fst (rd_list fs p) \<in> pideal (set fs)"
  by (rule fst_rd_list_in_pideal_ind, simp)

lemma snd_rd_list_iff_neq: "snd (rd_list fs p) \<longleftrightarrow> (fst (rd_list fs p) \<noteq> p)"
proof (induct fs)
  case Nil
  show ?case by simp
next
  case (Cons f fs)
  show ?case by (simp add: Let_def Cons snd_rd_iff_neq)
qed

corollary snd_rd_list_iff_is_red: "snd (rd_list fs p) \<longleftrightarrow> (is_red (set fs) p)"
  by (simp add: snd_rd_list_iff_neq fst_rd_list_id)

end (* ordered_powerprod *)

context gd_powerprod
begin

definition trd_term :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::field) list \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<times> (('a \<Rightarrow>\<^sub>0 'b) list \<times> ('a \<Rightarrow>\<^sub>0 'b))) set"
  where "trd_term d = {(x, y). dgrad_p_set_le d (set (snd x # fst x)) (set (snd y # fst y)) \<and> snd x \<prec>p snd y}"

lemma trd_term_wf:
  assumes "dickson_grading (+) d"
  shows "wf (trd_term d)"
proof (rule wfI_min)
  fix x :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<times> ('a \<Rightarrow>\<^sub>0 'b)" and Q
  assume "x \<in> Q"
  let ?A = "set (snd x # fst x)"
  have "finite ?A" ..
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. set (snd q # fst q) \<subseteq> ?B}"
  note assms
  moreover have "snd x \<in> snd ` ?Q" by (rule, fact refl, simp only: mem_Collect_eq A \<open>x \<in> Q\<close>)
  moreover have "snd ` ?Q \<subseteq> ?B" by auto
  ultimately obtain z0 where "z0 \<in> snd ` ?Q"
    and *: "\<And>y. y \<prec>p z0 \<Longrightarrow> y \<notin> snd ` ?Q" by (rule ord_p_minimum_dgrad_p_set, blast)
  from this(1) obtain z where "z \<in> {q \<in> Q. set (snd q # fst q) \<subseteq> ?B}" and z0: "z0 = snd z" ..
  from this(1) have "z \<in> Q" and a: "set (snd z # fst z) \<subseteq> ?B" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> trd_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> trd_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> trd_term d"
      hence b: "dgrad_p_set_le d (set (snd y # fst y)) (set (snd z # fst z))" and "snd y \<prec>p z0"
        by (simp_all add: trd_term_def z0)
      from \<open>snd y \<prec>p z0\<close> have "snd y \<notin> snd ` ?Q" by (rule *)
      hence "y \<notin> Q \<or> \<not> set (snd y # fst y) \<subseteq> ?B" by auto
      moreover from b a have "set (snd y # fst y) \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

function trd :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "trd fs p = (let q = rd_list fs p in (if snd q then trd fs (fst q) else fst q))"
  by (pat_completeness, auto)
termination proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "trd_term d"
  show ?thesis
  proof (rule, rule trd_term_wf, fact)
    fix p fs and q::"('a \<Rightarrow>\<^sub>0 'b) \<times> bool"
    assume q: "q = rd_list fs p" and "snd q"
    from this(2) have "is_red (set fs) p" by (simp add: q snd_rd_list_iff_is_red)
    hence red: "red (set fs) p (fst q)" unfolding q by (rule fst_rd_list_red)
    show "((fs, fst q), (fs, p)) \<in> ?R"
    proof (simp add: trd_term_def, rule)
      from dg red have "dgrad_p_set_le d {fst q} (insert p (set fs))"
        by (rule dgrad_p_set_le_red)
      show "dgrad_p_set_le d (insert (fst q) (set fs)) (insert p (set fs))"
      proof (rule dgrad_p_set_leI_insert)
        show "dgrad_p_set_le d (set fs) (insert p (set fs))" by (rule dgrad_p_set_le_subset, blast)
      qed fact
    next
      from red show "fst q \<prec>p p" by (rule red_ord)
    qed
  qed
qed

lemma trd_induct:
  assumes base: "\<And>fs p. fst (rd_list fs p) = p \<Longrightarrow> P fs p p"
    and ind: "\<And>fs p. fst (rd_list fs p) \<noteq> p \<Longrightarrow> P fs (fst (rd_list fs p)) (trd fs (fst (rd_list fs p))) \<Longrightarrow>
              P fs p (trd fs (fst (rd_list fs p)))"
  shows "P fs p (trd fs p)"
proof (induct p rule: trd.induct)
  fix fs and p::"'a \<Rightarrow>\<^sub>0 'b"
  let ?x = "rd_list fs p"
  assume "\<And>x. x = ?x \<Longrightarrow> snd x \<Longrightarrow> P fs (fst x) (trd fs (fst x))"
  from this[of ?x] have imp: "snd ?x \<Longrightarrow> P fs (fst ?x) (trd fs (fst ?x))" by simp
  show "P fs p (trd fs p)"
  proof (cases "snd ?x")
    case True
    hence eq: "trd fs p = trd fs (fst ?x)" by (simp del: trd.simps add: trd.simps[of fs p])
    from True have "fst (rd_list fs p) \<noteq> p" by (simp add: snd_rd_list_iff_neq)
    from ind[OF this imp[OF True]] eq show ?thesis by simp
  next
    case False
    hence "fst (rd_list fs p) = p" by (simp add: snd_rd_list_iff_neq)
    with base[OF this] False show ?thesis by simp
  qed
qed

lemma trd_red_rtrancl: "(red (set fs))\<^sup>*\<^sup>* p (trd fs p)"
proof (induct rule: trd_induct)
  fix fs and p::"'a \<Rightarrow>\<^sub>0 'b"
  assume "fst (rd_list fs p) = p"
  show "(red (set fs))\<^sup>*\<^sup>* p p" ..
next
  fix fs and p::"'a \<Rightarrow>\<^sub>0 'b"
  let ?x = "rd_list fs p"
  assume "fst ?x \<noteq> p" and "(red (set fs))\<^sup>*\<^sup>* (fst ?x) (trd fs (fst ?x))"
  show "(red (set fs))\<^sup>*\<^sup>* p (trd fs (fst ?x))"
  proof (rule converse_rtranclp_into_rtranclp)
    from \<open>fst ?x \<noteq> p\<close> rd_list_fixpointI[of fs p] have "is_red (set fs) p" by auto
    thus "red (set fs) p (fst ?x)" by (rule fst_rd_list_red)
  qed fact
qed

lemma trd_irred: "\<not> is_red (set fs) (trd fs p)"
proof (induct rule: trd_induct)
  fix fs and p::"'a \<Rightarrow>\<^sub>0 'b"
  assume "fst (rd_list fs p) = p"
  thus "\<not> is_red (set fs) p" by (rule rd_list_fixpointD)
qed assumption

lemma trd_in_pideal: "(p - (trd fs p)) \<in> pideal (set fs)"
proof (induct p rule: trd_induct)
  fix fs and p::"'a \<Rightarrow>\<^sub>0 'b"
  from ideal.module_0 show "p - p \<in> pideal (set fs)" by simp
next
  fix fs and p::"'a \<Rightarrow>\<^sub>0 'b"
  assume IH: "(fst (rd_list fs p) - trd fs (fst (rd_list fs p))) \<in> pideal (set fs)"
  from ideal.module_closed_plus[OF IH fst_rd_list_in_pideal[of p fs]]
    show "p - trd fs (fst (rd_list fs p)) \<in> pideal (set fs)" by simp
qed

lemma pideal_closed_trd:
  assumes "p \<in> pideal B" and "set fs \<subseteq> pideal B"
  shows "(trd fs p) \<in> pideal B"
proof -
  from assms(2) have "pideal (set fs) \<subseteq> pideal B" by (rule ideal.module_subset_moduleI)
  with trd_in_pideal have "p - trd fs p \<in> pideal B" ..
  with assms(1) have "p - (p - trd fs p) \<in> pideal B" by (rule ideal.module_closed_minus)
  thus ?thesis by simp
qed

end (* gd_powerprod *)

end (* theory *)
