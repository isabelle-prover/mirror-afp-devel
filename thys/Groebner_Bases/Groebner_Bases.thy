(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Gr\"obner Bases\<close>

theory Groebner_Bases
imports "../Polynomials/MPoly_Type_Class" Confluence General
begin

text \<open>This theory provides the main results about Gr\"obner bases of multivariate polynomials.
  Function @{term gb} implements Buchberger's algorithm; the key property of @{term gb} is
  summarized in theorem @{text in_pideal_gb}.\<close>

subsection \<open>Polynomial Reduction\<close>

context ordered_powerprod
begin

definition red_single::"('a, 'b::field) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> 'a \<Rightarrow> bool"
  where "red_single p q f t \<equiv> (f \<noteq> 0 \<and> lookup p (t + lp f) \<noteq> 0 \<and>
                                q = p - monom_mult ((lookup p (t + lp f)) / lc f) t f)"

definition red::"('a, 'b::field) poly_mapping set \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool"
  where "red F p q \<equiv> (\<exists>f\<in>F. \<exists>t. red_single p q f t)"

definition is_red::"('a, 'b::field) poly_mapping set \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool"
  where "is_red F a \<equiv> \<not> relation.is_final (red F) a"

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
       lookup_monom_mult[of "lookup p (t + lp f) / lc f" t f "lp f"]
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
  from a lp_mult[OF c_not_0 \<open>f \<noteq> 0\<close>, of t]
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

subsubsection \<open>Reducibility and Addition \& Multiplication\<close>

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
    hence "c * lookup p (t + lp f) = 0" using assoc lookup_monom_mult[of c s p "t + lp f"] by simp
    thus False using \<open>c \<noteq> 0\<close> \<open>lookup p (t + lp f) \<noteq> 0\<close> by simp
  qed
  have g3: "monom_mult c s q =
    (monom_mult c s p) - monom_mult ((lookup (monom_mult c s p) ((s + t) + lp f)) / lc f) (s + t) f"
  proof -
    from q_def monom_mult_dist_right_minus[of c s p]
      have "monom_mult c s q =
            monom_mult c s p - monom_mult c s (monom_mult (lookup p (t + lp f) / lc f) t f)" by simp
    also from monom_mult_assoc[of c s "lookup p (t + lp f) / lc f" t f] assoc
      lookup_monom_mult[of c s p "t + lp f"]
      have "monom_mult c s (monom_mult (lookup p (t + lp f) / lc f) t f) =
            monom_mult ((lookup (monom_mult c s p) ((s + t) + lp f)) / lc f) (s + t) f" by simp
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
  using red_monom_mult[OF assms, of "-1" 0] by (simp add: uminus_monom_mult)

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

subsubsection \<open>Confluence of Reducibility\<close>

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

subsubsection \<open>Reducibility and Ideal Membership\<close>

lemma srtc_in_pideal:
  assumes "relation.srtc (red F) p q"
  shows "p - q \<in> pideal F"
  using assms unfolding relation.srtc_def
proof (induct rule: rtranclp.induct)
  fix p
  from zero_in_pideal[of F] show "p - p \<in> pideal F" by simp
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
    by (rule pideal_closed_plus, fact, rule monom_mult_in_pideal, fact)
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
        from lookup_monom_mult[of c t f "lp f"]
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
    hence "- (p - q) \<in> pideal B" by (rule pideal_closed_uminus)
    thus "q - p \<in> pideal B" by simp
  qed fact
  from pideal_closed_plus[OF this \<open>p \<in> pideal A\<close>] show ?thesis by simp
qed

subsubsection \<open>More Properties of @{const red}, @{const red_single} and @{const is_red}\<close>

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
  using red_rtrancl_mult[OF assms, of "-1" 0] by (simp add: uminus_monom_mult)

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
    from eq lp_mult[OF this \<open>h \<noteq> 0\<close>, of t] have "lp f = t + lp h" by simp
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
    from eq lp_mult[OF this \<open>h \<noteq> 0\<close>, of t] have lpR: "lp ?R = t + lp h" by simp
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
    by (simp add: lp_mult, simp add: lc_mult)
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
    from \<open>lc f \<noteq> 0\<close> have kt: "keys ?t = (+) (lp f) ` keys (tail p)" by (rule keys_monom_mult)
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
        also from \<open>lc f \<noteq> 0\<close> False have "... = lp f + lp (tail p)" by (rule lp_mult)
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

end (* ordered_powerprod *)

subsection \<open>Well-foundedness and Termination\<close>

context gd_powerprod
begin

lemma dgrad_p_red_single_pp:
  assumes "dickson_grading (+) d" and "red_single p q f t"
  shows "d t \<le> dgrad_p d p"
proof -
  {
    have "t adds t + lp f" by simp
    with assms(1) have "d t \<le> d (t + lp f)" by (rule dickson_grading_adds_imp_le)
  }
  also {
    from assms(2) have "t + lp f \<in> keys p" by (simp add: red_single_def)
    hence "d (t + lp f) \<le> dgrad_p d p" by (rule dgrad_p_geI)
  }
  finally show ?thesis .
qed

lemma dgrad_p_red_single:
  assumes "dickson_grading (+) d" and "red_single p q f t"
  shows "dgrad_p d q \<le> ord_class.max (dgrad_p d f) (dgrad_p d p)" (is "_ \<le> ?m")
proof -
  let ?f = "monom_mult ((lookup p (t + lp f)) / lc f) t f"
  from assms(2) have "t + lp f \<in> keys p" and q: "q = p - ?f" by (simp_all add: red_single_def)
  from assms have "d t \<le> dgrad_p d p" by (rule dgrad_p_red_single_pp)
  moreover from assms(1) have "dgrad_p d ?f \<le> ord_class.max (d t) (dgrad_p d f)"
    by (rule dgrad_p_monom_mult)
  ultimately have "dgrad_p d ?f \<le> ?m" by simp
  with dgrad_p_minus[of d p ?f] show ?thesis unfolding q by auto
qed

lemma dgrad_p_redE:
  assumes "dickson_grading (+) d" and "red F p q"
  obtains r where "r \<in> insert p F" and "dgrad_p d q \<le> dgrad_p d r"
proof -
  from assms(2) obtain f t where "f \<in> F" and *: "red_single p q f t" by (rule red_setE)
  from assms(1) this(2) have *: "dgrad_p d q \<le> ord_class.max (dgrad_p d f) (dgrad_p d p)"
    by (rule dgrad_p_red_single)
  show ?thesis
  proof (cases "dgrad_p d f \<le> dgrad_p d p")
    case True
    with * have "dgrad_p d q \<le> dgrad_p d p" by simp
    show ?thesis
    proof
      show "p \<in> insert p F" by simp
    qed fact
  next
    case False
    with * have "dgrad_p d q \<le> dgrad_p d f" by simp
    show ?thesis
    proof
      from \<open>f \<in> F\<close> show "f \<in> insert p F" by simp
    qed fact
  qed
qed

lemma dgrad_p_redE_rtrancl:
  assumes "dickson_grading (+) d" and "(red F)\<^sup>*\<^sup>* p q"
  obtains r where "r \<in> insert p F" and "dgrad_p d q \<le> dgrad_p d r"
proof -
  assume rl: "\<And>r. r \<in> insert p F \<Longrightarrow> dgrad_p d q \<le> dgrad_p d r \<Longrightarrow> thesis"
  from assms(2) rl show thesis
  proof (induct arbitrary: thesis)
    case base
    show ?case
    proof (rule base)
      show "p \<in> insert p F" by simp
    qed rule
  next
    case (step q' q)
    obtain r' where "r' \<in> insert p F" and 1: "dgrad_p d q' \<le> dgrad_p d r'" by (rule step(3))
    from assms(1) step(2) obtain r where "r \<in> insert q' F" and 2: "dgrad_p d q \<le> dgrad_p d r"
      by (rule dgrad_p_redE)
    from this(1) have "r = q' \<or> r \<in> F" by simp
    thus ?case
    proof
      assume "r = q'"
      show ?thesis
      proof (rule step(4))
        from 2 1 show "dgrad_p d q \<le> dgrad_p d r'" unfolding \<open>r = q'\<close> by (rule le_trans)
      qed fact
    next
      assume "r \<in> F"
      show ?thesis
      proof (rule step(4))
        from \<open>r \<in> F\<close> show "r \<in> insert p F" by simp
      qed fact
    qed
  qed
qed

lemma dgrad_p_set_red_single_pp:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "red_single p q f t"
  shows "d t \<le> m"
proof -
  from assms(1) assms(3) have "d t \<le> dgrad_p d p" by (rule dgrad_p_red_single_pp)
  also from assms(2) have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis .
qed

lemma dgrad_p_set_closed_red_single:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "f \<in> dgrad_p_set d m"
    and "red_single p q f t"
  shows "q \<in> dgrad_p_set d m"
proof -
  from assms(1) assms(4) have "dgrad_p d q \<le> ord_class.max (dgrad_p d f) (dgrad_p d p)"
    by (rule dgrad_p_red_single)
  also from assms(2) assms(3) have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis by (simp add: dgrad_p_set_alt)
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
  let ?m = "ord_class.max (dgrad_p d x) m"
  let ?Q = "Q \<inter> dgrad_p_set d ?m"
  have "m \<le> ?m" and "dgrad_p d x \<le> ?m" by simp_all
  from this(2) have "x \<in> dgrad_p_set d ?m" by (simp add: dgrad_p_set_alt)
  from assms(2) dgrad_p_set_subset[OF \<open>m \<le> ?m\<close>] have "F \<subseteq> dgrad_p_set d ?m" by (rule subset_trans)
  with assms(1) have "wfP_on (dgrad_p_set d ?m) (red F)\<inverse>\<inverse>" by (rule red_wf_dgrad_p_set_aux)
  moreover from \<open>x \<in> Q\<close> \<open>x \<in> dgrad_p_set d ?m\<close> have "x \<in> ?Q" ..
  moreover have "?Q \<subseteq> dgrad_p_set d ?m" by simp
  ultimately obtain z where "z \<in> ?Q" and *: "\<And>y. (red F)\<inverse>\<inverse> y z \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and "z \<in> dgrad_p_set d ?m" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (red F)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(red F)\<inverse>\<inverse> y z"
      hence "red F z y" by simp
      with assms(1) \<open>F \<subseteq> dgrad_p_set d ?m\<close> \<open>z \<in> dgrad_p_set d ?m\<close> have "y \<in> dgrad_p_set d ?m"
        by (rule dgrad_p_set_closed_red)
      moreover from \<open>(red F)\<inverse>\<inverse> y z\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by blast
    qed
  qed
qed

lemmas red_wf_finite = red_wf_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

definition dgrad_p_set_le :: "('a \<Rightarrow> nat) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b::zero) set) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b::zero) set) \<Rightarrow> bool"
  where "dgrad_p_set_le d F G \<longleftrightarrow> (\<forall>f \<in> F. \<exists>g \<in> G. dgrad_p d f \<le> dgrad_p d g)"

text \<open>@{const dgrad_p_set_le} will be needed to prove termination of @{term trd} and @{term gb_aux}.\<close>

lemma dgrad_p_set_leI:
  assumes "\<And>f. f \<in> F \<Longrightarrow> \<exists>g\<in>G. dgrad_p d f \<le> dgrad_p d g"
  shows "dgrad_p_set_le d F G"
  using assms by (auto simp: dgrad_p_set_le_def)

lemma dgrad_p_set_leE:
  assumes "dgrad_p_set_le d F G" and "f \<in> F"
  obtains g where "g \<in> G" and "dgrad_p d f \<le> dgrad_p d g"
  using assms by (auto simp: dgrad_p_set_le_def)

lemma dgrad_p_set_le_trans [trans]:
  assumes "dgrad_p_set_le d F G" and "dgrad_p_set_le d G H"
  shows "dgrad_p_set_le d F H"
proof (rule dgrad_p_set_leI)
  fix f
  assume "f \<in> F"
  with assms(1) obtain g where "g \<in> G" and 1: "dgrad_p d f \<le> dgrad_p d g" by (rule dgrad_p_set_leE)
  from assms(2) this(1) obtain h where "h \<in> H" and 2: "dgrad_p d g \<le> dgrad_p d h" by (rule dgrad_p_set_leE)
  from this(1) show "\<exists>h\<in>H. dgrad_p d f \<le> dgrad_p d h"
  proof
    from 1 2 show "dgrad_p d f \<le> dgrad_p d h" by (rule le_trans)
  qed
qed

lemma dgrad_p_set_le_subset:
  assumes "F \<subseteq> G"
  shows "dgrad_p_set_le d F G"
proof (rule dgrad_p_set_leI)
  fix f
  assume "f \<in> F"
  with assms have "f \<in> G" ..
  thus "\<exists>g\<in>G. dgrad_p d f \<le> dgrad_p d g"
  proof
    show "dgrad_p d f \<le> dgrad_p d f" by (rule le_refl)
  qed
qed

lemma dgrad_p_set_leI_insert:
  assumes "dgrad_p_set_le d F G" and "f' \<in> G" and "dgrad_p d f \<le> dgrad_p d f'"
  shows "dgrad_p_set_le d (insert f F) G"
  using assms by (auto simp: dgrad_p_set_le_def)

lemma dgrad_p_set_le_dgrad_p_set:
  assumes "dgrad_p_set_le d F G" and "G \<subseteq> dgrad_p_set d m"
  shows "F \<subseteq> dgrad_p_set d m"
proof
  fix f
  assume "f \<in> F"
  with assms(1) obtain g where "g \<in> G" and *: "dgrad_p d f \<le> dgrad_p d g" by (rule dgrad_p_set_leE)
  from assms(2) this(1) have "g \<in> dgrad_p_set d m" ..
  hence "dgrad_p d g \<le> m" by (simp add: dgrad_p_set_alt)
  with * have "dgrad_p d f \<le> m" by (rule le_trans)
  thus "f \<in> dgrad_p_set d m" by (simp add: dgrad_p_set_alt)
qed

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

subsection \<open>Gr\"obner Bases and Buchberger's Theorem\<close>

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

definition (in ordered_powerprod) is_Groebner_basis::"('a, 'b::field) poly_mapping set \<Rightarrow> bool"
  where "is_Groebner_basis F \<equiv> relation.is_ChurchRosser (red F)"

lemma crit_pair_same: "fst (crit_pair p p) = snd (crit_pair p p)"
  by (simp add: crit_pair_def)

lemma crit_pair_swap: "crit_pair p q = (snd (crit_pair q p), fst (crit_pair q p))"
  by (simp add: crit_pair_def lcs_comm)

lemma crit_pair_zero [simp]: "fst (crit_pair 0 q) = 0" and "snd (crit_pair p 0) = 0"
  by (simp_all add: crit_pair_def monom_mult_right0)

lemma dgrad_p_crit_pair_zero: "dgrad_p d (fst (crit_pair p 0)) \<le> dgrad_p d p"
proof (simp add: crit_pair_def lp_def[of 0] monom_mult_right0 lcs_comm lcs_zero, rule dgrad_p_leI)
  fix t
  assume "t \<in> keys (monom_mult (1 / lc p) 0 (tail p))"
  with keys_monom_mult_subset have "t \<in> ((+) 0) ` keys (tail p)" ..
  then obtain u where "u \<in> keys (tail p)" and "t = 0 + u" ..
  hence "t \<in> keys p" by (simp add: keys_tail)
  thus "d t \<le> dgrad_p d p" by (rule dgrad_p_geI)
qed

lemma dgrad_p_fst_crit_pair:
  assumes "dickson_grading (+) d"
  shows "dgrad_p d (fst (crit_pair p q)) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)" (is "_ \<le> ?m")
proof (cases "q = 0")
  case True
  from dgrad_p_crit_pair_zero[of d p] show ?thesis by (simp add: True)
next
  case False
  hence 1: "d (lp q) \<le> dgrad_p d q" by (rule dgrad_p_geI_lp)
  show ?thesis
  proof (cases "p = 0")
    case True
    from dgrad_p_crit_pair_zero[of d q] show ?thesis by (simp add: True)
  next
    case False
    hence 2: "d (lp p) \<le> dgrad_p d p" by (rule dgrad_p_geI_lp)
    show ?thesis
    proof -
      let ?s = "lcs (lp p) (lp q) - lp p"
      let ?t = "lcs (lp p) (lp q) - lp q"
      from assms(1) have "d ?s \<le> ord_class.max (d (lp p)) (d (lp q))"
        by (rule dickson_grading_lcs_minus)
      with 1 2 have "d ?s \<le> ?m" by simp
      from assms(1) have "d ?t \<le> ord_class.max (d (lp q)) (d (lp p))"
        by (simp only: lcs_comm[of "lp p"], rule dickson_grading_lcs_minus)
      with 1 2 have "d ?t \<le> ?m" by simp
      let ?a = "monom_mult (1 / lc p) ?s (tail p)"
      from assms have "dgrad_p d ?a \<le> ord_class.max (d ?s) (dgrad_p d (tail p))"
        by (rule dgrad_p_monom_mult)
      also from dgrad_p_tail[of d p] have "... \<le> ord_class.max (d ?s) (dgrad_p d p)" by auto
      also from \<open>d ?s \<le> ?m\<close> have "... \<le> ?m" by simp
      finally show "dgrad_p d (fst (crit_pair p q)) \<le> ?m" by (simp add: crit_pair_def)
    qed
  qed
qed

lemma dgrad_p_snd_crit_pair:
  assumes "dickson_grading (+) d"
  shows "dgrad_p d (snd (crit_pair p q)) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
  by (simp add: crit_pair_swap[of p] linorder_class.max.commute[of "dgrad_p d p"],
      rule dgrad_p_fst_crit_pair, fact)

lemma dgrad_p_set_closed_fst_crit_pair:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "fst (crit_pair p q) \<in> dgrad_p_set d m"
proof -
  from assms(1) have "dgrad_p d (fst (crit_pair p q)) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
    by (rule dgrad_p_fst_crit_pair)
  also from assms(2) assms(3) have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis by (simp add: dgrad_p_set_alt)
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
    by (rule lp_mult)
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

lemma dgrad_p_spoly_zero: "dgrad_p d (spoly p 0) \<le> dgrad_p d p"
proof (simp add: spoly_def lp_def[of 0] monom_mult_right0 lcs_comm lcs_zero, rule dgrad_p_leI)
  fix t
  assume "t \<in> keys (monom_mult (1 / lc p) 0 p)"
  with keys_monom_mult_subset have "t \<in> ((+) 0) ` keys p" ..
  then obtain u where "u \<in> keys p" and "t = 0 + u" ..
  hence "t \<in> keys p" by simp
  thus "d t \<le> dgrad_p d p" by (rule dgrad_p_geI)
qed

lemma dgrad_p_spoly:
  assumes "dickson_grading (+) d"
  shows "dgrad_p d (spoly p q) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: spoly_swap[of 0], intro dgrad_p_spoly_zero)
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    thus ?thesis by (simp, intro dgrad_p_spoly_zero)
  next
    case False
    show ?thesis unfolding spoly_alt[OF \<open>p \<noteq> 0\<close> False] using dgrad_p_fst_crit_pair[OF assms, of p q]
      dgrad_p_snd_crit_pair[OF assms, of p q] dgrad_p_minus[of d] le_trans by fastforce
  qed
qed

lemma dgrad_p_set_closed_spoly:
  assumes "dickson_grading (+) d" and "p \<in> dgrad_p_set d m" and "q \<in> dgrad_p_set d m"
  shows "spoly p q \<in> dgrad_p_set d m"
proof -
  from assms(1) have "dgrad_p d (spoly p q) \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
    by (rule dgrad_p_spoly)
  also from assms have "... \<le> m" by (simp add: dgrad_p_set_alt)
  finally show ?thesis by (simp add: dgrad_p_set_alt)
qed

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
  have "a \<in> dgrad_p_set d (dgrad_p d a)" by (fact dgrad_p_set_dgrad_p)
  let ?m = "ord_class.max m (dgrad_p d a)"
  have "m \<le> ?m" and "dgrad_p d a \<le> ?m" by simp_all
  with dgrad_p_set_subset assms(2) \<open>a \<in> dgrad_p_set d (dgrad_p d a)\<close>
    have "F \<subseteq> dgrad_p_set d ?m" and "a \<in> dgrad_p_set d ?m" by blast+
  {
    fix p q
    assume "p \<in> F" and "q \<in> F" and "p \<noteq> 0" and "q \<noteq> 0"
    hence "crit_pair_cbelow_on d m F p q" by (rule assms(3))
    from this dgrad_p_set_subset[OF \<open>m \<le> ?m\<close>] have "crit_pair_cbelow_on d ?m F p q"
      unfolding crit_pair_cbelow_on_def by (rule cbelow_on_mono)
  }
  with assms(1) \<open>F \<subseteq> dgrad_p_set d ?m\<close> have "relation.is_confluent_on (red F) (dgrad_p_set d ?m)"
    by (rule crit_pair_cbelow_imp_confluent_dgrad_p_set)
  from this \<open>a \<in> dgrad_p_set d ?m\<close> have "\<forall>b1 b2. (red F)\<^sup>*\<^sup>* a b1 \<and> (red F)\<^sup>*\<^sup>* a b2 \<longrightarrow> relation.cs (red F) b1 b2"
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

subsubsection \<open>Buchberger's Criteria for Avoiding Useless Pairs\<close>

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

subsubsection \<open>Weak and Strong Gr\"obner Bases\<close>

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
  assumes "pideal B \<subseteq> pideal A" and major: "\<And>q. q \<in> (pideal A) \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> is_red B q"
    and in_ideal: "p \<in> (pideal A)"
  shows "(red B)\<^sup>*\<^sup>* p 0"
proof -
  define n where "n = ord_class.max m (dgrad_p d p)"
  have "m \<le> n" and "dgrad_p d p \<le> n" by (simp_all add: n_def)
  from assms(2) dgrad_p_set_subset[OF \<open>m \<le> n\<close>] have B: "B \<subseteq> dgrad_p_set d n" by (rule subset_trans)
  from \<open>dgrad_p d p \<le> n\<close> have "p \<in> dgrad_p_set d n" by (simp add: dgrad_p_set_alt)
  from ord_p_wf_on[OF assms(1)] this in_ideal show ?thesis
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
  
lemma GB_alt_1: "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> (pideal G). (red G)\<^sup>*\<^sup>* f 0)"
  using weak_GB_is_strong_GB GB_imp_zero_reducibility by blast

lemma GB_alt_2_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> (pideal G). f \<noteq> 0 \<longrightarrow> is_red G f)"
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
    proof (rule is_red_implies_0_red_dgrad_p_set)
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

lemma GB_alt_3_dgrad_p_set:
  assumes "dickson_grading (+) d" and "G \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis G \<longleftrightarrow> (\<forall>f \<in> (pideal G). f \<noteq> 0 \<longrightarrow> (\<exists>g \<in> G. g \<noteq> 0 \<and> lp g adds lp f))"
  unfolding GB_alt_1
proof
  assume a1: "\<forall>f\<in>pideal G. (red G)\<^sup>*\<^sup>* f 0"
  show "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
  proof (intro ballI, intro impI)
    fix f
    assume "f \<in> (pideal G)" and "f \<noteq> 0"
    with a1 have "(red G)\<^sup>*\<^sup>* f 0" by simp
    from zero_reducibility_implies_lp_divisibility'[OF this \<open>f \<noteq> 0\<close>] show "\<exists>h\<in>G. h \<noteq> 0 \<and> lp h adds lp f" .
  qed
next
  assume a2: "\<forall>f\<in>pideal G. f \<noteq> 0 \<longrightarrow> (\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp f)"
  show "\<forall>f\<in>pideal G. (red G)\<^sup>*\<^sup>* f 0"
  proof (intro ballI)
    fix f
    assume "f \<in> (pideal G)"
    from assms show "(red G)\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red_dgrad_p_set)
      fix q
      assume "q \<in> (pideal G)" and "q \<noteq> 0"
      with a2 have "\<exists>g\<in>G. g \<noteq> 0 \<and> lp g adds lp q" by simp
      then obtain g where "g \<in> G" and "g \<noteq> 0" and "lp g adds lp q" by auto
      thus "is_red G q" using \<open>q \<noteq> 0\<close> is_red_indI1 by blast
    qed (fact subset_refl, fact)
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

lemmas is_red_implies_0_red_finite = is_red_implies_0_red_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_implies_unique_nf_finite = GB_implies_unique_nf_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_alt_2_finite = GB_alt_2_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]
lemmas GB_alt_3_finite = GB_alt_3_dgrad_p_set[OF dickson_grading_dgrad_dummy dgrad_p_set_exhaust_expl]

end (* gd_powerprod *)

subsubsection \<open>Context @{locale od_powerprod}\<close>

context od_powerprod
begin

lemmas red_wf = red_wf_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]
lemmas Buchberger_criterion = Buchberger_criterion_dgrad_p_set[OF dickson_grading_zero subset_dgrad_p_set_zero]

end (* od_powerprod *)

subsection \<open>Algorithms\<close>

type_synonym ('a, 'b) apT = "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list"
type_synonym ('a, 'b) critT = "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"

subsubsection \<open>Function @{term rd}\<close>

context ordered_powerprod
begin

function rd_mult::"('a, 'b::field) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('b * 'a)" where
  "rd_mult p f =
    (if p = 0 \<or> f = 0 then
      (0, 0)
    else
      (if lp f adds lp p then
        (lc p / lc f, lp p - lp f)
      else
        rd_mult (tail p) f
      )
    )"
  by auto
termination proof -
  let ?R = "{(x, y::('a, 'b) poly_mapping). keys x \<subset> keys y} <*lex*> {}"
  show ?thesis
  proof
    show "wf ?R"
    proof
      from keys_subset_wf show "wf {(x, y). keys x \<subset> keys y}" by (simp only: wfP_def)
    qed simp
  next
    fix p f::"('a, 'b) poly_mapping"
    assume "\<not> (p = 0 \<or> f = 0)"
    hence "p \<noteq> 0" by simp
    hence "lp p \<in> keys p" by (rule lp_in_keys)
    hence "keys (tail p) \<subset> keys p" unfolding keys_tail by auto
    thus "((tail p, f), p, f) \<in> ?R" by simp
  qed
qed

definition rd::"('a, 'b::field) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping"
where "rd p f \<equiv> (let m = rd_mult p f in p - monom_mult (fst m) (snd m) f)"

lemma compute_rd_mult[code]:
  "rd_mult p f =
    (if p = 0 \<or> f = 0 then
      (0, 0)
    else
      (if (lp f) adds (lp p) then
        (lc p / lc f, lp p - lp f)
      else
        rd_mult (tail p) f
      )
    )"
  by simp

lemma rd_mult_left0:
  shows "rd_mult 0 f = (0, 0)"
by simp

lemma rd_mult_right0:
  shows "rd_mult p 0 = (0, 0)"
by simp

lemma rd_mult_adds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "lp f adds lp p"
  shows "rd_mult p f = (lc p / lc f, lp p - lp f)"
using assms by simp

lemma rd_mult_nadds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "\<not> lp f adds lp p"
  shows "rd_mult p f = rd_mult (tail p) f"
using assms by simp

lemma rd_left0:
  shows "rd 0 f = 0"
unfolding rd_def by (simp add: rd_mult_left0 Let_def del: rd_mult.simps, rule monom_mult_left0)

lemma rd_right0:
  shows "rd p 0 = p"
unfolding rd_def by (simp add: rd_mult_right0 Let_def del: rd_mult.simps, rule monom_mult_left0)

lemma rd_adds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "lp f adds lp p"
  shows "rd p f = p - monom_mult (lc p / lc f) (lp p - lp f) f"
unfolding rd_def by (simp add: rd_mult_adds[OF assms] Let_def del: rd_mult.simps)

lemma rd_nadds:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "\<not> lp f adds lp p"
  shows "rd p f = (monomial (lc p) (lp p)) + (rd (tail p) f)"
  by (simp add: rd_def rd_mult_nadds[OF assms] Let_def del: rd_mult.simps, rule leading_monomial_tail)

lemma rd_red_set:
  assumes "is_red {f} p"
  shows "red {f} p (rd p f)"
using assms
proof (induct p rule: poly_mapping_tail_induct)
  case 0
  from this irred_0[of "{f}"] show "red {f} 0 (rd 0 f)" by simp
next
  case (tail p)
  assume "p \<noteq> 0" and IH: "is_red {f} (tail p) \<Longrightarrow> red {f} (tail p) (rd (tail p) f)"
    and red: "is_red {f} p"
  show "red {f} p (rd p f)"
  proof (cases "\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f adds lp p")
    assume "\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f adds lp p"
    hence "f \<noteq> 0" and "lp f adds lp p" by auto
    have "red {f} p (p - monom_mult (lc p / lc f) (lp p - lp f) f)"
      by (intro red_indI1, simp, fact+)
    thus ?thesis using rd_mult_adds[OF \<open>p \<noteq> 0\<close> \<open>f \<noteq> 0\<close> \<open>lp f adds lp p\<close>] unfolding rd_def by simp
  next
    assume "\<not> (\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f adds lp p)"
    from this is_red_indE[OF red] have r: "is_red {f} (tail p)"
      and dis: "f = 0 \<or> \<not> (lp f adds lp p)"
      by auto
    from is_red_singleton_not_0[OF r] have "f \<noteq> 0" .
    from dis this have "\<not> (lp f adds lp p)" by simp
    from rd_nadds[OF \<open>p \<noteq> 0\<close> \<open>f \<noteq> 0\<close> this] red_indI2[OF \<open>p \<noteq> 0\<close> IH[OF r]]
      show ?thesis by (simp only: rd_def ac_simps)
  qed
qed

lemma rd_irred_set:
  assumes "\<not> is_red {f} p"
  shows "rd p f = p"
using assms
proof (induct p rule: poly_mapping_tail_induct, simp only: rd_left0)
  fix p
  assume "p \<noteq> 0" and IH: "\<not> is_red {f} (tail p) \<Longrightarrow> rd (tail p) f = tail p"
    and irred: "\<not> is_red {f} p"
  have "f \<in> {f}" by simp
  from irred is_red_indI1[OF this _ \<open>p \<noteq> 0\<close>] have dis: "f = 0 \<or> \<not> (lp f adds lp p)" by auto
  show "rd p f = p"
  proof (cases "f = 0")
    case True
    thus ?thesis by (simp only: rd_right0)
  next
    case False
    hence nadds: "\<not> (lp f adds lp p)" using dis by simp
    from irred is_red_indI2[OF \<open>p \<noteq> 0\<close>, of "{f}"] have "\<not> is_red {f} (tail p)" by auto
    from IH[OF this] rd_nadds[OF \<open>p \<noteq> 0\<close> False nadds] leading_monomial_tail[of p]
      show ?thesis by simp
  qed
qed

lemma rd_red:
  assumes "red_single p q f t"
  shows "\<exists>t. red_single p (rd p f) f t"
proof -
  have "is_red {f} p" by (intro is_redI, intro red_setI[of f], simp, fact)
  from red_setE[OF rd_red_set[OF this]] obtain t where "red_single p (rd p f) f t" by force
  show ?thesis by (intro exI, fact)
qed

lemma rd_irred:
  assumes "\<And>q t. \<not> red_single p q f t"
  shows "rd p f = p"
proof (rule rd_irred_set, rule)
  assume "is_red {f} p"
  from is_redE[OF this] obtain q where "red {f} p q" .
  from red_setE[OF this] obtain t where "red_single p q f t" by force
  from this assms[of q t] show False by simp
qed

lemma rd_id_set:
  shows "(rd p f = p) = (\<forall>q. \<not> red {f} p q)"
proof
  assume "rd p f = p"
  show "\<forall>q. \<not> red {f} p q"
  proof (intro allI)
    fix q
    show "\<not> red {f} p q"
    proof
      assume "red {f} p q"
      have "is_red {f} p" by (intro is_redI, fact)
      from rd_red_set[OF this] \<open>rd p f = p\<close> have "red {f} p p" by simp
      from red_ord[OF this] show False by simp
    qed
  qed
next
  assume a: "\<forall>q. \<not> red {f} p q"
  show "rd p f = p"
  proof (intro rd_irred_set, intro notI)
    assume "is_red {f} p"
    from is_redE[OF this] obtain q where "red {f} p q" .
    from this a show False by simp
  qed
qed

lemma rd_id:
  shows "(rd p f = p) = (\<forall>q t. \<not> red_single p q f t)"
proof
  assume "rd p f = p"
  show "\<forall>q t. \<not> red_single p q f t"
  proof (intro allI)
    fix q t
    show "\<not> red_single p q f t"
    proof
      assume "red_single p q f t"
      from rd_red[OF this] obtain s where "red_single p (rd p f) f s" ..
      hence "red_single p p f s" using \<open>rd p f = p\<close> by simp
      from red_single_ord[OF this] show False by simp
    qed
  qed
next
  assume a: "\<forall>q t. \<not> red_single p q f t"
  show "rd p f = p"
  proof (intro rd_irred, intro notI)
    fix q t
    assume "red_single p q f t"
    from this a show False by simp
  qed
qed

lemma rd_less_eq:
  shows "(rd p f) \<preceq>p p"
proof (cases "\<forall>q. \<not> red {f} p q")
  case True
  hence "rd p f = p" using rd_id_set[of p f] by simp
  thus ?thesis by simp
next
  case False
  hence "\<exists>q. red {f} p q" by simp
  from this obtain q where "red {f} p q" by auto
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  from rd_red[OF this] obtain s where "red_single p (rd p f) f s" ..
  from red_single_ord[OF this] show ?thesis by simp
qed

lemma rd_lessI:
  assumes "red_single p q f t"
  shows "(rd p f) \<prec>p p"
proof -
  from rd_red[OF assms] obtain s where "red_single p (rd p f) f s" ..
  from red_single_ord[OF this] show ?thesis .
qed

lemma rd_lessE:
  assumes "(rd p f) \<prec>p p"
  obtains t where "red_single p (rd p f) f t"
proof -
  from assms have "(rd p f) \<noteq> p" by simp
  hence "\<exists>q t. red_single p q f t" using rd_id[of p f] by simp
  from this obtain q s where "red_single p q f s" by auto
  from rd_red[OF this] obtain t where "red_single p (rd p f) f t" ..
  thus ?thesis ..
qed

subsubsection \<open>Functions @{term rd_list} and @{term trd}\<close>

primrec rd_list::"('a, 'b::field) poly_mapping list \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping" where
  rd_list_base: "rd_list Nil p = p"|
  rd_list_rec: "rd_list (f # fs) p = (let q = rd p f in (if q = p then rd_list fs p else q))"

lemma rd_list_red:
  assumes "is_red (set fs) p"
  shows "red (set fs) p (rd_list fs p)"
proof -
  from assms obtain q where "red (set fs) p q" unfolding is_red_alt ..
  thus ?thesis
  proof (induct fs)
    case Nil
    from Nil have "red {} p q" by simp
    from red_setE[OF this] obtain f t where "f \<in> {}" and "red_single p q f t" .
    from \<open>f \<in> {}\<close> show "red (set []) p (rd_list [] p)" ..
  next
    case Cons
    fix f fs
    assume IH: "red (set fs) p q \<Longrightarrow> red (set fs) p (rd_list fs p)" and r: "red (set (f # fs)) p q"
    from r have "red (insert f (set fs)) p q" by simp
    from red_setE[OF this] obtain g t where
      g: "g \<in> (insert f (set fs))" and red_g: "red_single p q g t" .
    from g have g_cases: "g = f \<or> g \<in> set fs" by simp
    show "red (set (f # fs)) p (rd_list (f # fs) p)" unfolding rd_list_rec
    proof (cases "rd p f = p")
      case True
      hence irred: "\<forall>q t. \<not> red_single p q f t" using rd_id[of p f] by simp
      from g_cases have "g \<in> set fs"
      proof (rule, simp_all)
        assume "g = f"
        from this irred[rule_format, of q t] red_g show "f \<in> set fs" by simp
      qed
      from red_unionI2[OF IH[OF red_setI[OF this red_g]], of "{f}"] True
        show "red (set (f # fs)) p (let q = rd p f in if q = p then rd_list fs p else q)" by simp
    next
      case False
      from this rd_id[of p f] have "\<exists>q t. red_single p q f t" by simp
      from this obtain q0 t0 where "red_single p q0 f t0" by auto
      have "red ({f} \<union> (set fs)) p (rd p f)"
        by (rule red_unionI1, simp only: red_singleton, rule rd_red[OF \<open>red_single p q0 f t0\<close>])
      with False show "red (set (f # fs)) p (let q = rd p f in if q = p then rd_list fs p else q)"
        by simp
    qed
  qed
qed

lemma rd_list_fixpointI:
  assumes "\<not> is_red (set fs) p"
  shows "(rd_list fs p) = p"
proof -
  from assms have "\<And>q. \<not> red (set fs) p q" unfolding is_red_alt by simp
  thus ?thesis
  proof (induct fs, simp)
    fix f fs
    assume IH: "(\<And>q. \<not> red (set fs) p q) \<Longrightarrow> rd_list fs p = p"
      and irred: "\<And>q. \<not> red (set (f # fs)) p q"
    from irred have "\<And>q. \<not> red ({f} \<union> (set fs)) p q" by simp
    hence "\<And>q. \<not> ((red {f} p q) \<or> (red (set fs) p q))" using red_union[of "{f}" "set fs" p] by simp
    hence irred1: "\<And>q. \<not> red {f} p q" and irred2: "\<And>q. \<not> red (set fs) p q" by simp_all
    from irred1 have eq: "(rd p f) = p" unfolding rd_id_set ..
    from IH[OF irred2] eq show "rd_list (f # fs) p = p" unfolding rd_list_rec by simp
  qed
qed

lemma rd_list_fixpointD:
  assumes "(rd_list fs p) = p"
  shows "\<not> is_red (set fs) p"
proof
  assume "is_red (set fs) p"
  from red_ord[OF rd_list_red[OF this]] assms show False by simp
qed

lemma rd_list_le:
  shows "(rd_list fs p) \<preceq>p p"
proof (cases "is_red (set fs) p")
  case True
  from red_ord[OF rd_list_red[OF this]] show ?thesis by simp
next
  case False
  from rd_list_fixpointI[OF this] show ?thesis by simp
qed

lemma rd_list_in_pideal_ind:
  assumes "set fs \<subseteq> bs"
  shows "p - (rd_list fs p) \<in> pideal bs"
using assms
proof (induct fs)
  from zero_in_pideal show "p - rd_list [] p \<in> pideal bs" by simp
next
  fix a fs
  assume IH: "set fs \<subseteq> bs \<Longrightarrow> p - rd_list fs p \<in> pideal bs" and a: "set (a # fs) \<subseteq> bs"
  from a have "a \<in> bs" by simp
  from a have "set fs \<subseteq> bs" by simp
  show "p - rd_list (a # fs) p \<in> pideal bs" unfolding rd_list_rec Let_def
  proof (simp add: if_splits, rule, intro impI)
    assume "rd p a = p"
    from IH[OF \<open>set fs \<subseteq> bs\<close>] show "p - rd_list fs p \<in> pideal bs" .
  next
    show "rd p a \<noteq> p \<longrightarrow> p - rd p a \<in> pideal bs"
    proof
      assume "rd p a \<noteq> p"
      hence "rd p a \<prec>p p" using rd_less_eq[of p a] by simp
      from rd_lessE[OF this] obtain t where "red_single p (rd p a) a t" .
      hence eq: "p - rd p a = monom_mult (lookup p (t + lp a) / lc a) t a"
        unfolding red_single_def by simp
      show "p - rd p a \<in> pideal bs" unfolding eq by (rule monom_mult_in_pideal, rule \<open>a \<in> bs\<close>)
    qed
  qed
qed

lemma rd_list_in_pideal:
  shows "p - (rd_list fs p) \<in> pideal (set fs)"
  by (rule rd_list_in_pideal_ind, simp)

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

function trd::"('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "trd fs p = (let q = rd_list fs p in (if q = p then p else trd fs q))"
by (pat_completeness, auto)
termination proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "trd_term d"
  show ?thesis
  proof (rule, rule trd_term_wf, fact)
    fix p fs and q::"('a, 'b) poly_mapping"
    assume q: "q = rd_list fs p" and neq: "q \<noteq> p"
    have red: "red (set fs) p q" unfolding q
      by (rule rd_list_red, rule ccontr, drule rd_list_fixpointI, simp only: q[symmetric] neq)
    show "((fs, q), (fs, p)) \<in> ?R"
    proof (simp add: trd_term_def, rule)
      from dg red obtain r where "r \<in> insert p (set fs)" and "dgrad_p d q \<le> dgrad_p d r"
        by (rule dgrad_p_redE)
      show "dgrad_p_set_le d (insert q (set fs)) (insert p (set fs))"
        by (rule dgrad_p_set_leI_insert, rule dgrad_p_set_le_subset, rule subset_insertI, fact+)
    next
      from red show "q \<prec>p p" by (rule red_ord)
    qed
  qed
qed

lemma trd_induct:
  assumes base: "\<And>fs p. rd_list fs p = p \<Longrightarrow> P fs p p"
    and ind: "\<And>fs p. rd_list fs p \<noteq> p \<Longrightarrow> P fs (rd_list fs p) (trd fs (rd_list fs p)) \<Longrightarrow>
              P fs p (trd fs (rd_list fs p))"
  shows "P fs p (trd fs p)"
proof (induct p rule: trd.induct)
  fix fs and p::"('a, 'b) poly_mapping"
  let ?x = "rd_list fs p"
  assume "\<And>x. x = rd_list fs p \<Longrightarrow> x \<noteq> p \<Longrightarrow> P fs x (trd fs x)"
  from this[of ?x] have imp: "?x \<noteq> p \<Longrightarrow> P fs ?x (trd fs ?x)" by simp
  show "P fs p (trd fs p)"
  proof (cases "?x = p")
    case True
    from base[OF True] True show ?thesis by simp
  next
    case False
    hence eq: "trd fs p = trd fs ?x" by (simp del: trd.simps add: trd.simps[of fs p])
    from ind[OF False imp[OF False]] eq show ?thesis by simp
  qed
qed

lemma trd_red_rtrancl: "(red (set fs))\<^sup>*\<^sup>* p (trd fs p)"
proof (induct rule: trd_induct)
  fix fs and p::"('a, 'b) poly_mapping"
  assume "rd_list fs p = p"
  show "(red (set fs))\<^sup>*\<^sup>* p p" ..
next
  fix fs and p::"('a, 'b) poly_mapping"
  let ?x = "rd_list fs p"
  assume "?x \<noteq> p" and "(red (set fs))\<^sup>*\<^sup>* ?x (trd fs ?x)"
  show "(red (set fs))\<^sup>*\<^sup>* p (trd fs ?x)"
  proof (rule converse_rtranclp_into_rtranclp)
    from \<open>?x \<noteq> p\<close> rd_list_fixpointI[of fs p] have "is_red (set fs) p" by auto
    from rd_list_red[OF this] show "red (set fs) p ?x" .
  next
    show "(red (set fs))\<^sup>*\<^sup>* ?x (trd fs ?x)" by fact
  qed
qed

lemma trd_irred: "\<not> is_red (set fs) (trd fs p)"
proof (induct rule: trd_induct)
  fix fs and p::"('a, 'b) poly_mapping"
  assume "rd_list fs p = p"
  from rd_list_fixpointD[OF this] show "\<not> is_red (set fs) p" .
next
  fix fs and p::"('a, 'b) poly_mapping"
  let ?x = "rd_list fs p"
  assume "\<not> is_red (set fs) (trd fs ?x)"
  show "\<not> is_red (set fs) (trd fs ?x)" by fact
qed

lemma trd_in_pideal: "(p - (trd fs p)) \<in> pideal (set fs)"
proof (induct p rule: trd_induct)
  fix fs and p::"('a, 'b) poly_mapping"
  from zero_in_pideal show "p - p \<in> pideal (set fs)" by simp
next
  fix fs and p::"('a, 'b) poly_mapping"
  assume IH: "(rd_list fs p - trd fs (rd_list fs p)) \<in> pideal (set fs)"
  from pideal_closed_plus[OF IH rd_list_in_pideal[of p fs]]
    show "p - trd fs (rd_list fs p) \<in> pideal (set fs)" by simp
qed

lemma pideal_closed_trd:
  assumes "p \<in> pideal (set fs)"
  shows "(trd fs p) \<in> pideal (set fs)"
using assms
proof (induct rule: trd_induct)
  fix fs and p::"('a, 'b) poly_mapping"
  assume "p \<in> pideal (set fs)"
  thus "p \<in> pideal (set fs)" .
next
  fix fs and p::"('a, 'b) poly_mapping"
  assume IH: "rd_list fs p \<in> pideal (set fs) \<Longrightarrow> trd fs (rd_list fs p) \<in> pideal (set fs)"
    and p_in: "p \<in> pideal (set fs)"
  show "trd fs (rd_list fs p) \<in> pideal (set fs)"
  proof (rule IH)
    from pideal_closed_minus[OF p_in rd_list_in_pideal[of p fs]]
      show "rd_list fs p \<in> pideal (set fs)" by simp
  qed
qed

subsubsection \<open>Relation @{term red_supset}\<close>

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

subsubsection \<open>The @{emph \<open>add_pairs\<close>} Parameter\<close>

definition add_pairs_set :: "('a, 'b::zero) apT \<Rightarrow> bool"
  where "add_pairs_set apf \<longleftrightarrow> (\<forall>bs rs h. set (apf rs bs h) = set rs \<union> Pair h ` set bs)"

lemma add_pairs_setI:
  assumes "\<And>bs rs h. set (apf rs bs h) = set rs \<union> Pair h ` set bs"
  shows "add_pairs_set apf"
  using assms by (auto simp add: add_pairs_set_def)

lemma add_pairs_setD:
  assumes "add_pairs_set apf"
  shows "set (apf rs bs h) = set rs \<union> Pair h ` set bs"
  using assms by (auto simp add: add_pairs_set_def)

lemma add_pairs_setD2:
  assumes "add_pairs_set apf" and "(a, b) \<in> set (apf ps bs h)"
  shows "(a, b) \<in> set ps \<or> (a = h \<and> b \<in> set bs)"
proof -
  from assms(2) have "(a, b) \<in> set ps \<union> Pair h ` set bs" by (simp only: add_pairs_setD[OF assms(1)])
  thus "(a, b) \<in> set ps \<or> (a = h \<and> b \<in> set bs)" by auto
qed

lemma add_pairs_setD3:
  assumes "add_pairs_set apf" and "set ps \<subseteq> (set bs) \<times> (set bs)"
  shows "set (apf ps bs h) \<subseteq> set (h # bs) \<times> set (h # bs)"
proof
  fix x y
  assume "(x, y) \<in> set (apf ps bs h)"
  with assms(1) have "(x, y) \<in> set ps \<or> (x = h \<and> y \<in> set bs)" by (rule add_pairs_setD2)
  thus "(x, y) \<in> set (h # bs) \<times> set (h # bs)"
  proof
    assume "(x, y) \<in> set ps"
    from this assms(2) have "(x, y) \<in> (set bs) \<times> (set bs)" ..
    thus ?thesis by simp
  next
    assume "x = h \<and> y \<in> set bs"
    thus ?thesis by simp
  qed
qed

lemma add_pairs_set_inI1:
  assumes "add_pairs_set apf" and "p \<in> set ps"
  shows "p \<in> set (apf ps bs h)"
  using assms by (simp add: add_pairs_setD)

lemma add_pairs_set_inI2:
  assumes "add_pairs_set apf" and "p \<in> set bs"
  shows "(h, p) \<in> set (apf ps bs h)"
  using assms by (simp add: add_pairs_setD)

lemma fst_add_pairs_subset:
  assumes "add_pairs_set apf"
  shows "fst ` set (apf rs bs h) \<subseteq> insert h (fst ` set rs)"
proof -
  from assms have "set (apf rs bs h) = set rs \<union> Pair h ` set bs" by (rule add_pairs_setD)
  hence "fst ` set (apf rs bs h) = fst ` (set rs \<union> Pair h ` set bs)" by simp
  thus ?thesis by auto
qed

lemma snd_add_pairs_subset:
  assumes "add_pairs_set apf"
  shows "snd ` set (apf rs bs h) \<subseteq> (snd ` set rs) \<union> set bs"
proof -
  from assms have "set (apf rs bs h) = set rs \<union> Pair h ` set bs" by (rule add_pairs_setD)
  hence "snd ` set (apf rs bs h) = snd ` (set rs \<union> Pair h ` set bs)" by simp
  thus ?thesis by auto
qed

definition add_pairs_naive :: "('a, 'b) apT"
  where "add_pairs_naive ps bs h \<equiv> ps @ (map (Pair h) bs)"

lemma add_pairs_set_add_pairs_naive: "add_pairs_set add_pairs_naive"
  by (simp add: add_pairs_set_def add_pairs_naive_def)

primrec add_pairs_sorted :: "('a, 'b::zero) apT" where
  "add_pairs_sorted ps [] _ = ps"|
  "add_pairs_sorted ps (b # bs) h =
    add_pairs_sorted (insort_wrt (\<lambda>_ y. lcs (lp h) (lp b) \<preceq> lcs (lp (fst y)) (lp (snd y))) (h, b) ps) bs h"

lemma add_pairs_set_add_pairs_sorted: "add_pairs_set add_pairs_sorted"
  unfolding add_pairs_set_def
proof (intro allI)
  fix bs ps and h::"'a \<Rightarrow>\<^sub>0 'b"
  show "set (add_pairs_sorted ps bs h) = set ps \<union> Pair h ` set bs"
    by (induct bs arbitrary: ps, simp_all)
qed

(* Could be defined tail-recursively, but is usually only called on "small" arguments anyway. *)
primrec pairs :: "('a, 'b) apT \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list" where
  "pairs _ [] = []"|
  "pairs apf (x # xs) = apf (pairs apf xs) xs x"

lemma pairsD1:
  assumes "add_pairs_set apf" and "(p, q) \<in> set (pairs apf bs)"
  shows "p \<in> set bs"
  using assms(2)
proof (induct bs)
  assume "(p, q) \<in> set (pairs apf [])"
  thus "p \<in> set []" by simp
next
  fix x xs
  assume IH: "(p, q) \<in> set (pairs apf xs) \<Longrightarrow> p \<in> set xs"
    and a: "(p, q) \<in> set (pairs apf (x # xs))"
  from a have "(p, q) \<in> set (apf (pairs apf xs) xs x)" by simp
  with assms(1) have "(p, q) \<in> set (pairs apf xs) \<or> (p = x \<and> q \<in> set xs)"
    by (rule add_pairs_setD2)
  thus "p \<in> set (x # xs)"
  proof
    assume "(p, q) \<in> set (pairs apf xs)"
    hence "p \<in> set xs" by (rule IH)
    thus ?thesis by simp
  next
    assume "p = x \<and> q \<in> set xs"
    thus ?thesis by simp
  qed
qed

lemma pairsD2:
  assumes "add_pairs_set apf" and "(p, q) \<in> set (pairs apf bs)"
  shows "q \<in> set bs"
  using assms(2)
proof (induct bs)
  assume "(p, q) \<in> set (pairs apf [])"
  thus "q \<in> set []" by simp
next
  fix x xs
  assume IH: "(p, q) \<in> set (pairs apf xs) \<Longrightarrow> q \<in> set xs"
    and a: "(p, q) \<in> set (pairs apf (x # xs))"
  from a have "(p, q) \<in> set (apf (pairs apf xs) xs x)" by simp
  with assms(1) have "(p, q) \<in> set (pairs apf xs) \<or> (p = x \<and> q \<in> set xs)"
    by (rule add_pairs_setD2)
  thus "q \<in> set (x # xs)"
  proof
    assume "(p, q) \<in> set (pairs apf xs)"
    hence "q \<in> set xs" by (rule IH)
    thus ?thesis by simp
  next
    assume "p = x \<and> q \<in> set xs"
    thus ?thesis by simp
  qed
qed

corollary pairs_subset:
  assumes "add_pairs_set apf"
  shows "set (pairs apf bs) \<subseteq> set bs \<times> set bs"
  by (rule, rule, rule, erule pairsD1[OF assms], erule pairsD2[OF assms])

lemma in_pairsI:
  assumes "add_pairs_set apf" and "p \<noteq> q" and "p \<in> set bs" and "q \<in> set bs"
  shows "(p, q) \<in> set (pairs apf bs) \<or> (q, p) \<in> set (pairs apf bs)"
  using assms(3, 4)
proof (induct bs)
  case Nil
  thus ?case by simp
next
  case (Cons b bs)
  from Cons(3) have d: "q = b \<or> q \<in> set bs" by simp
  from Cons(2) have "p = b \<or> p \<in> set bs" by simp
  thus ?case
  proof
    assume "p = b"
    with assms(2) have "q \<noteq> b" by simp
    with d have "q \<in> set bs" by simp
    with assms(1) have "(p, q) \<in> set (pairs apf (b # bs))" unfolding \<open>p = b\<close> pairs.simps
      by (rule add_pairs_set_inI2)
    thus ?thesis ..
  next
    assume "p \<in> set bs"
    from d show ?thesis
    proof
      assume "q = b"
      from assms(1) \<open>p \<in> set bs\<close> have "(q, p) \<in> set (pairs apf (b # bs))"
        unfolding \<open>q = b\<close> pairs.simps by (rule add_pairs_set_inI2)
      thus ?thesis ..
    next
      assume "q \<in> set bs"
      with \<open>p \<in> set bs\<close> have "(p, q) \<in> set (pairs apf bs) \<or> (q, p) \<in> set (pairs apf bs)"
        by (rule Cons(1))
      thus ?thesis
      proof
        assume "(p, q) \<in> set (pairs apf bs)"
        with assms(1) have "(p, q) \<in> set (pairs apf (b # bs))"
          unfolding pairs.simps by (rule add_pairs_set_inI1)
        thus ?thesis ..
      next
        assume "(q, p) \<in> set (pairs apf bs)"
        with assms(1) have "(q, p) \<in> set (pairs apf (b # bs))"
          unfolding pairs.simps by (rule add_pairs_set_inI1)
        thus ?thesis ..
      qed
    qed
  qed
qed

subsubsection \<open>@{term processed}\<close>

definition processed::"(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> bool"
  where "processed p bs ps \<longleftrightarrow> fst p \<in> set bs \<and> snd p \<in> set bs \<and> p \<notin> set ps \<and> (snd p, fst p) \<notin> set ps"

lemma processed_alt:
  "processed (a, b) bs ps \<longleftrightarrow> ((a \<in> set bs) \<and> (b \<in> set bs) \<and> (a, b) \<notin> set ps \<and> (b, a) \<notin> set ps)"
  unfolding processed_def by auto

lemma processedI:
  assumes "f \<in> set bs" and "g \<in> set bs" and "(f, g) \<notin> set ps" and "(g, f) \<notin> set ps"
  shows "processed (f, g) bs ps"
  unfolding processed_alt using assms by simp

lemma processedD1:
  assumes "processed (f, g) bs ps"
  shows "f \<in> set bs"
  using assms by (simp add: processed_alt)

lemma processedD2:
  assumes "processed (f, g) bs ps"
  shows "g \<in> set bs"
  using assms by (simp add: processed_alt)

lemma processedD3:
  assumes "processed (f, g) bs ps"
  shows "(f, g) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processedD4:
  assumes "processed (f, g) bs ps"
  shows "(g, f) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processed_Nil: "processed (f, g) bs [] \<longleftrightarrow> (f \<in> set bs \<and> g \<in> set bs)"
  by (simp add: processed_alt)

lemma processed_Cons:
  assumes "processed (f, g) bs ps"
    and a1: "f = p \<Longrightarrow> g = q \<Longrightarrow> thesis"
    and a2: "f = q \<Longrightarrow> g = p \<Longrightarrow> thesis"
    and a3: "processed (f, g) bs ((p, q) # ps) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "f \<in> set bs" and "g \<in> set bs" and "(f, g) \<notin> set ps" and "(g, f) \<notin> set ps"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(f, g) = (p, q)")
    case True
    hence "f = p" and "g = q" by simp_all
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(f, g) \<notin> set ps\<close> have *: "(f, g) \<notin> set ((p, q) # ps)" by auto
    show ?thesis
    proof (cases "(g, f) = (p, q)")
      case True
      hence "f = q" and "g = p" by simp_all
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(g, f) \<notin> set ps\<close> have "(g, f) \<notin> set ((p, q) # ps)" by auto
      with \<open>f \<in> set bs\<close> \<open>g \<in> set bs\<close> * have "processed (f, g) bs ((p, q) # ps)" by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

lemma processed_pairs:
  assumes "add_pairs_set apf" and "f \<noteq> g" and "f \<in> set bs" and "g \<in> set bs"
  shows "\<not> processed (f, g) bs (pairs apf bs)"
proof
  assume "processed (f, g) bs (pairs apf bs)"
  hence "(f, g) \<notin> set (pairs apf bs)" and "(g, f) \<notin> set (pairs apf bs)"
    by (rule processedD3, rule processedD4)
  moreover from assms have "(f, g) \<in> set (pairs apf bs) \<or> (g, f) \<in> set (pairs apf bs)"
    by (rule in_pairsI)
  ultimately show False by simp
qed

lemma processed_add_pairs:
  assumes "add_pairs_set apf" and "processed (f, g) (h # bs) (apf ps bs h)"
  shows "processed (f, g) bs ps \<or> (f = h \<and> g = h)"
proof -
  from assms(2) have d1: "f = h \<or> f \<in> set bs" and d2: "g = h \<or> g \<in> set bs"
    and a: "(f, g) \<notin> set (apf ps bs h)" and b: "(g, f) \<notin> set (apf ps bs h)" by (simp_all add: processed_def)
  from d1 show ?thesis
  proof
    assume "f = h"
    from d2 show ?thesis
    proof
      assume "g = h"
      with \<open>f = h\<close> show ?thesis by simp
    next
      assume "g \<in> set bs"
      with assms(1) have "(f, g) \<in> set (apf ps bs h)" unfolding \<open>f = h\<close> by (rule add_pairs_set_inI2)
      with a show ?thesis ..
    qed
  next
    assume "f \<in> set bs"
    from d2 show ?thesis
    proof
      assume "g = h"
      from assms(1) \<open>f \<in> set bs\<close> have "(g, f) \<in> set (apf ps bs h)" unfolding \<open>g = h\<close> by (rule add_pairs_set_inI2)
      with b show ?thesis ..
    next
      assume "g \<in> set bs"
      from \<open>f \<in> set bs\<close> this have "processed (f, g) bs ps"
      proof (rule processedI)
        show "(f, g) \<notin> set ps"
        proof
          assume "(f, g) \<in> set ps"
          with assms(1) have "(f, g) \<in> set (apf ps bs h)" by (rule add_pairs_set_inI1)
          with a show False ..
        qed
      next
        show "(g, f) \<notin> set ps"
        proof
          assume "(g, f) \<in> set ps"
          with assms(1) have "(g, f) \<in> set (apf ps bs h)" by (rule add_pairs_set_inI1)
          with b show False ..
        qed
      qed
      thus ?thesis ..
    qed
  qed
qed

subsubsection \<open>The @{emph \<open>crit\<close>} Parameter\<close>

definition crit_conn :: "('a, 'b::field) critT \<Rightarrow> bool"
  where "crit_conn cf \<longleftrightarrow> (\<forall>d m bs ps p q. dickson_grading (+) d \<longrightarrow> set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
                                set ps \<subseteq> set bs \<times> set bs \<longrightarrow>
                                (\<forall>p' q'. processed (p', q') bs ps \<longrightarrow> p' \<noteq> 0 \<longrightarrow> q' \<noteq> 0 \<longrightarrow>
                                    (p' \<noteq> p \<or> q' \<noteq> q) \<longrightarrow> (p' \<noteq> q \<or> q' \<noteq> p) \<longrightarrow>
                                    crit_pair_cbelow_on d m (set bs) p' q') \<longrightarrow>
                                p \<in> set bs \<longrightarrow> q \<in> set bs \<longrightarrow> p \<noteq> 0 \<longrightarrow> q \<noteq> 0 \<longrightarrow> cf ps bs p q \<longrightarrow>
                                crit_pair_cbelow_on d m (set bs) p q)"

lemma crit_connI:
  assumes "\<And>d m bs ps p q.
        dickson_grading (+) d \<Longrightarrow> set bs \<subseteq> dgrad_p_set d m \<Longrightarrow> set ps \<subseteq> set bs \<times> set bs \<Longrightarrow>
        (\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
                  (p' \<noteq> p \<or> q' \<noteq> q) \<Longrightarrow> (p' \<noteq> q \<or> q' \<noteq> p) \<Longrightarrow>
                  crit_pair_cbelow_on d m (set bs) p' q') \<Longrightarrow>
        p \<in> set bs \<Longrightarrow> q \<in> set bs \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> cf ps bs p q \<Longrightarrow>
        crit_pair_cbelow_on d m (set bs) p q"
  shows "crit_conn cf"
  using assms unfolding crit_conn_def by (metis (no_types, lifting))

lemma crit_connD:
  assumes "crit_conn cf" and 1: "dickson_grading (+) d"
    and 2: "set bs \<subseteq> dgrad_p_set d m" and 3: "set ps \<subseteq> set bs \<times> set bs"
    and 4: "\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
                  (p' \<noteq> p \<or> q' \<noteq> q) \<Longrightarrow> (p' \<noteq> q \<or> q' \<noteq> p) \<Longrightarrow>
                  crit_pair_cbelow_on d m (set bs) p' q'"
    and 5: "p \<in> set bs" and 6: "q \<in> set bs" and 7: "p \<noteq> 0" and 8: "q \<noteq> 0" and 9: "cf ps bs p q"
  shows "crit_pair_cbelow_on d m (set bs) p q"
  using assms unfolding crit_conn_def by blast

definition product_crit :: "('a, 'b::zero) critT"
  where "product_crit ps bs p q \<longleftrightarrow> (gcs (lp p) (lp q) = 0)"

lemma crit_conn_product_crit: "crit_conn product_crit"
proof (rule crit_connI)
  fix d m bs ps p and q::"'a \<Rightarrow>\<^sub>0 'b"
  assume "product_crit ps bs p q"
  hence *: "gcs (lp p) (lp q) = 0" by (simp only: product_crit_def)
  assume "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m"
    and "p \<in> set bs" and "q \<in> set bs" and "p \<noteq> 0" and "q \<noteq> 0"
  from this * show "crit_pair_cbelow_on d m (set bs) p q" by (rule product_criterion)
qed

definition chain_crit :: "('a, 'b::zero) critT"
  where "chain_crit ps bs p q \<longleftrightarrow> (\<exists>r \<in> set bs. r \<noteq> 0 \<and> r \<noteq> p \<and> r \<noteq> q \<and> lp r adds lcs (lp p) (lp q) \<and>
                                    (p, r) \<notin> set ps \<and> (r, p) \<notin> set ps \<and> (q, r) \<notin> set ps \<and> (r, q) \<notin> set ps)"

lemma chain_critE:
  assumes "chain_crit ps bs p q" and "p \<in> set bs" and "q \<in> set bs"
  obtains r where "r \<in> set bs" and "r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q" and "lp r adds lcs (lp p) (lp q)"
    and "processed (p, r) bs ps" and "processed (r, q) bs ps"
proof -
  from assms(1) obtain r where "r \<in> set bs" and "r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and "lp r adds lcs (lp p) (lp q)" and "(p, r) \<notin> set ps" and "(r, p) \<notin> set ps"
    and "(q, r) \<notin> set ps" and "(r, q) \<notin> set ps" unfolding chain_crit_def by blast
  from this(1, 2, 3, 4, 5) show ?thesis
  proof
    from assms(2) \<open>r \<in> set bs\<close> \<open>(p, r) \<notin> set ps\<close> \<open>(r, p) \<notin> set ps\<close> show "processed (p, r) bs ps"
      by (rule processedI)
  next
    from \<open>r \<in> set bs\<close> assms(3) \<open>(r, q) \<notin> set ps\<close> \<open>(q, r) \<notin> set ps\<close> show "processed (r, q) bs ps"
      by (rule processedI)
  qed
qed

lemma crit_conn_chain_crit: "crit_conn chain_crit"
proof (rule crit_connI)
  fix d m bs ps p and q::"'a \<Rightarrow>\<^sub>0 'b"
  assume "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m"
    and *: "\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
           p' \<noteq> p \<or> q' \<noteq> q \<Longrightarrow>  p' \<noteq> q \<or> q' \<noteq> p \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p' q'"
    and "p \<noteq> 0" and "q \<noteq> 0"
  assume "chain_crit ps bs p q" and "p \<in> set bs" and "q \<in> set bs"
  then obtain r where "r \<in> set bs" and "r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q" and "lp r adds lcs (lp p) (lp q)"
    and "processed (p, r) bs ps" and "processed (r, q) bs ps" by (rule chain_critE)
  from \<open>dickson_grading (+) d\<close> \<open>set bs \<subseteq> dgrad_p_set d m\<close> \<open>p \<in> set bs\<close> \<open>q \<in> set bs\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>
    \<open>lp r adds lcs (lp p) (lp q)\<close> show "crit_pair_cbelow_on d m (set bs) p q"
  proof (rule chain_criterion)
    from \<open>processed (p, r) bs ps\<close> \<open>p \<noteq> 0\<close> \<open>r \<noteq> 0\<close> show "crit_pair_cbelow_on d m (set bs) p r"
    proof (rule *)
      from \<open>r \<noteq> q\<close> show "p \<noteq> p \<or> r \<noteq> q" by simp
    next
      from \<open>r \<noteq> p\<close> show "p \<noteq> q \<or> r \<noteq> p" by simp
    qed
  next
    from \<open>processed (r, q) bs ps\<close> \<open>r \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show "crit_pair_cbelow_on d m (set bs) r q"
    proof (rule *)
      from \<open>r \<noteq> p\<close> show "r \<noteq> p \<or> q \<noteq> q" by simp
    next
      from \<open>r \<noteq> q\<close> show "r \<noteq> q \<or> q \<noteq> p" by simp
    qed
  qed
qed

definition comb_crit :: "('a, 'b::zero) critT \<Rightarrow> ('a, 'b) critT \<Rightarrow> ('a, 'b) critT"
  where "comb_crit c1 c2 ps bs p q \<longleftrightarrow> (c1 ps bs p q \<or> c2 ps bs p q)"

lemma crit_conn_comb_crit:
  assumes "crit_conn c1" and "crit_conn c2"
  shows "crit_conn (comb_crit c1 c2)"
proof (rule crit_connI)
  fix d m bs ps p and q::"'a \<Rightarrow>\<^sub>0 'b"
  assume 1: "dickson_grading (+) d" and 2: "set bs \<subseteq> dgrad_p_set d m" and 3: "set ps \<subseteq> set bs \<times> set bs"
    and 4: "\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
           p' \<noteq> p \<or> q' \<noteq> q \<Longrightarrow>  p' \<noteq> q \<or> q' \<noteq> p \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p' q'"
    and 5: "p \<in> set bs" and 6: "q \<in> set bs" and 7: "p \<noteq> 0" and 8: "q \<noteq> 0"
  assume "comb_crit c1 c2 ps bs p q"
  hence "c1 ps bs p q \<or> c2 ps bs p q" by (simp only: comb_crit_def)
  thus "crit_pair_cbelow_on d m (set bs) p q"
  proof
    assume "c1 ps bs p q"
    with assms(1) 1 2 3 4 5 6 7 8 show ?thesis by (rule crit_connD)
  next
    assume "c2 ps bs p q"
    with assms(2) 1 2 3 4 5 6 7 8 show ?thesis by (rule crit_connD)
  qed
qed

definition pc_crit :: "('a, 'b::zero) critT"
  where "pc_crit = comb_crit product_crit chain_crit"

corollary crit_conn_pc_crit: "crit_conn pc_crit"
  by (simp only: pc_crit_def, rule crit_conn_comb_crit, fact crit_conn_product_crit, fact crit_conn_chain_crit)

subsubsection \<open>Function @{term gb}\<close>

definition trdsp::"('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "trdsp bs p q \<equiv> trd bs (spoly p q)"

lemma trdsp_in_pideal:
  assumes "p \<in> set bs" and "q \<in> set bs"
  shows "trdsp bs p q \<in> pideal (set bs)"
  unfolding trdsp_def spoly_def
  apply (rule pideal_closed_trd)
  apply (rule pideal_closed_minus)
  subgoal by (rule monom_mult_in_pideal, fact)
  subgoal by (rule monom_mult_in_pideal, fact)
  done

lemma trdsp_eq_zero_imp_cbelow_on:
  assumes "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m" and "p \<noteq> 0" and "q \<noteq> 0" and "trdsp bs p q = 0" and "set bs \<subseteq> F"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  from assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) have "crit_pair_cbelow_on d m (set bs) p q"
  proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
    from assms(7) trd_red_rtrancl[of bs "spoly p q"] show "(red (set bs))\<^sup>*\<^sup>* (spoly p q) 0"
      by (simp add: trdsp_def)
  qed
  from this assms(8) show ?thesis by (rule crit_pair_cbelow_mono)
qed

lemma dgrad_p_trdspE:
  assumes "dickson_grading (+) d"
  obtains r where "r \<in> insert p (insert q (set bs))" and "dgrad_p d (trdsp bs p q) \<le> dgrad_p d r"
proof -
  let ?h = "trdsp bs p q"
  have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) ?h" unfolding trdsp_def by (rule trd_red_rtrancl)
  with assms obtain r0 where "r0 \<in> insert (spoly p q) (set bs)" and r0: "dgrad_p d ?h \<le> dgrad_p d r0"
    by (rule dgrad_p_redE_rtrancl)
  from this(1) have "r0 = spoly p q \<or> r0 \<in> set bs" by simp
  thus ?thesis
  proof
    assume "r0 = spoly p q"
    from assms have "dgrad_p d r0 \<le> ord_class.max (dgrad_p d p) (dgrad_p d q)"
      unfolding \<open>r0 = spoly p q\<close> by (rule dgrad_p_spoly)
    hence "dgrad_p d r0 \<le> dgrad_p d p \<or> dgrad_p d r0 \<le> dgrad_p d q" by auto
    thus ?thesis
    proof
      assume *: "dgrad_p d r0 \<le> dgrad_p d p"
      show ?thesis
      proof
        from r0 * show "dgrad_p d ?h \<le> dgrad_p d p" by (rule le_trans)
      qed simp
    next
      assume *: "dgrad_p d r0 \<le> dgrad_p d q"
      show ?thesis
      proof
        from r0 * show "dgrad_p d ?h \<le> dgrad_p d q" by (rule le_trans)
      qed simp
    qed
  next
    assume "r0 \<in> set bs"
    hence "r0 \<in> insert p (insert q (set bs))" by simp
    from this r0 show ?thesis ..
  qed
qed

corollary dgrad_p_set_closed_trdsp:
  assumes "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m"
  shows "trdsp bs p q \<in> dgrad_p_set d m"
proof -
  from assms(1) obtain r where "r \<in> insert p (insert q (set bs))"
    and le: "dgrad_p d (trdsp bs p q) \<le> dgrad_p d r" by (rule dgrad_p_trdspE)
  from this(1) have "r = p \<or> r = q \<or> r \<in> set bs" by simp
  from this assms(2) assms(3) assms(4) have "r \<in> dgrad_p_set d m" by blast
  hence "dgrad_p d r \<le> m" by (simp add: dgrad_p_set_alt)
  with le have "dgrad_p d (trdsp bs p q) \<le> m" by (rule le_trans)
  thus ?thesis by (simp add: dgrad_p_set_alt)
qed

text \<open>Proving termination of Buchberger's algorithm is a bit involved; we need a couple more
  definitions and lemmas. Actually, the fact that we want to prove termination in context
  @{locale gd_powerprod} rather than @{locale od_powerprod} complicates matters even more
  (in particular the definition of the well-founded termination relation).\<close>

definition pair_to_set :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) set"
  where "pair_to_set x = set (fst x) \<union> fst ` set (snd x) \<union> snd ` set (snd x)"

definition gbaux_term1 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::field) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list)) set"
  where "gbaux_term1 d = {(a, b::('a \<Rightarrow>\<^sub>0 'b) list). (set a) \<sqsupset>p (set b)} <*lex*> (measure length)"

definition gbaux_term2 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::field) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list)) set"
  where "gbaux_term2 d = {(a, b). dgrad_p_set_le d (pair_to_set a) (pair_to_set b)}"

definition gbaux_term where "gbaux_term d = gbaux_term1 d \<inter> gbaux_term2 d"

text \<open>@{const gbaux_term} is need for proving termination of function @{term gbaux}.\<close>

lemma in_lex_prod_alt:
  "(x, y) \<in> r <*lex*> s \<longleftrightarrow> (((fst x), (fst y)) \<in> r \<or> (fst x = fst y \<and> ((snd x), (snd y)) \<in> s))"
  by (metis in_lex_prod prod.collapse prod.inject surj_pair)

lemma gbaux_term1_wf_on:
  assumes "dickson_grading (+) d"
  shows "wfP_on {x. pair_to_set x \<subseteq> dgrad_p_set d m} (\<lambda>x y. (x, y) \<in> gbaux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_p_set d m"
  let ?A = "{x::(('a \<Rightarrow>\<^sub>0 'b) list) \<times> ((('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list). pair_to_set x \<subseteq> ?B}"
  have A_sub_Pow: "set ` fst ` ?A \<subseteq> Pow ?B" by (auto simp add: pair_to_set_def)
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  have Q_sub_A: "set ` fst ` Q \<subseteq> set ` fst ` ?A" by (rule image_mono, rule image_mono, fact)
  from assms have "wfP_on (Pow ?B) (\<sqsupset>p)" by (rule red_supset_wf_on)
  moreover have "set (fst x) \<in> set ` fst ` Q" by (rule, rule refl, rule, rule refl, fact)
  moreover from Q_sub_A A_sub_Pow have "set ` fst ` Q \<subseteq> Pow ?B" by (rule subset_trans)
  ultimately obtain z0 where "z0 \<in> set ` fst ` Q"
    and *: "\<And>y. y \<sqsupset>p z0 \<Longrightarrow> y \<notin> set ` fst ` Q" by (rule wfP_onE_min, blast)
  from this(1) obtain z1 where "z1 \<in> Q" and z0: "z0 = set (fst z1)" by auto

  let ?Q = "{q \<in> Q. set (fst q) = z0}"
  have "snd z1 \<in> snd ` ?Q" by (rule, rule refl, simp add: \<open>z1 \<in> Q\<close> z0)
  with wf_measure obtain z2 where "z2 \<in> snd ` ?Q" and **: "\<And>y. (y, z2) \<in> measure length \<Longrightarrow> y \<notin> snd ` ?Q"
    by (rule wfE_min, blast)
  from this(1) obtain z where "z \<in> ?Q" and z2: "z2 = snd z" ..
  from this(1) have "z \<in> Q" and eq: "set (fst z) = z0" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>?A. (y, z) \<in> gbaux_term1 d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>?A. (y, z) \<in> gbaux_term1 d \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI)
      fix y
      assume "y \<in> ?A"
      assume "(y, z) \<in> gbaux_term1 d"
      hence "set (fst y) \<sqsupset>p z0 \<or> (fst y = fst z \<and> (snd y, z2) \<in> measure length)"
        by (simp add: gbaux_term1_def eq[symmetric] z2 in_lex_prod_alt)
      thus "y \<notin> Q"
      proof
        assume "set (fst y) \<sqsupset>p z0"
        hence "set (fst y) \<notin> set ` fst ` Q" by (rule *)
        thus ?thesis by auto
      next
        assume "fst y = fst z \<and> (snd y, z2) \<in> measure length"
        hence "fst y = fst z" and "(snd y, z2) \<in> measure length" by simp_all
        from this(2) have "snd y \<notin> snd ` ?Q" by (rule **)
        hence "y \<notin> ?Q" by auto
        thus ?thesis by (simp add: \<open>fst y = fst z\<close> eq)
      qed
    qed
  qed
qed

lemma gbaux_term_wf:
  assumes "dickson_grading (+) d"
  shows "wf (gbaux_term d)"
proof (rule wfI_min)
  fix x::"(('a \<Rightarrow>\<^sub>0 'b) list) \<times> ((('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list)" and Q
  assume "x \<in> Q"
  let ?A = "pair_to_set x"
  have "finite ?A" by (simp add: pair_to_set_def)
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. pair_to_set q \<subseteq> ?B}"
  from assms have "wfP_on {x. pair_to_set x \<subseteq> ?B} (\<lambda>x y. (x, y) \<in> gbaux_term1 d)"
    by (rule gbaux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. pair_to_set x \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> gbaux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "pair_to_set z \<subseteq> ?B" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> gbaux_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> gbaux_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> gbaux_term d"
      hence "(y, z) \<in> gbaux_term1 d" and "(y, z) \<in> gbaux_term2 d" by (simp_all add: gbaux_term_def)
      from this(2) have "dgrad_p_set_le d (pair_to_set y) (pair_to_set z)" by (simp add: gbaux_term2_def)
      from this \<open>pair_to_set z \<subseteq> ?B\<close> have "pair_to_set y \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      moreover from \<open>(y, z) \<in> gbaux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

lemma dgrad_p_set_le_pair_to_set_trdsp:
  assumes "dickson_grading (+) d" and "add_pairs_set apf"
  shows "dgrad_p_set_le d (pair_to_set ((trdsp bs p q) # bs, apf rs bs (trdsp bs p q))) (pair_to_set (bs, (p, q) # rs))"
proof -
  let ?h = "trdsp bs p q"
  from assms(1) obtain r where r: "r \<in> insert p (insert q (set bs))" and "dgrad_p d ?h \<le> dgrad_p d r"
    unfolding assms(2) by (rule dgrad_p_trdspE)
  from fst_add_pairs_subset[OF assms(2), of rs bs "trdsp bs p q"] snd_add_pairs_subset[OF assms(2), of rs bs]
  have "pair_to_set (?h # bs, apf rs bs ?h) \<subseteq> insert ?h (pair_to_set (bs, rs))"
    by (simp only: pair_to_set_def, auto)
  hence "dgrad_p_set_le d (pair_to_set (?h # bs, apf rs bs ?h)) (insert ?h (pair_to_set (bs, rs)))"
    by (rule dgrad_p_set_le_subset)
  also have "dgrad_p_set_le d ... (insert p (insert q (pair_to_set (bs, rs))))"
  proof (rule dgrad_p_set_leI_insert, rule dgrad_p_set_le_subset)
    from r show "r \<in> insert p (insert q (pair_to_set (bs, rs)))" by (auto simp add: pair_to_set_def)
  next
    show "dgrad_p d ?h \<le> dgrad_p d r" by fact
  qed blast
  also have "... = pair_to_set (bs, (p, q) # rs)"
    by (auto simp add: pair_to_set_def)
  finally show ?thesis .
qed

text \<open>Functions @{term gb} and @{term gbaux} implement Buchberger's algorithm for computing
  Gr\"obner bases, incorporating Buchberger's two criteria for avoiding useless S-polynomials.\<close>

function (domintros) gbaux::"('a, 'b) apT \<Rightarrow> ('a, 'b) critT \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow>
    (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list" where
  gbaux_base: "gbaux _ _ bs [] = bs"|
  gbaux_rec: "gbaux apf cf bs ((p, q) # rs) =
    (if cf rs bs p q then
      gbaux apf cf bs rs
    else
      (let h = trdsp bs p q in
        (if h = 0 then
          gbaux apf cf bs rs
        else
          gbaux apf cf (h # bs) (apf rs bs h)
        )
      )
    )"
  by pat_completeness auto

text \<open>Note that we could parameterize @{const gbaux} over a binary (order) relation @{term R} instead
  of the ``add-pairs function'' @{term apf}. Then, @{term R} could be used to determine the order of
  the pairs in @{term rs}, and @{const gbaux} would terminate unconditionally. However, @{term apf} is
  more powerful, since it has a ``global'' view of the list of pairs and therefore has the potential
  of arranging the elements in a more clever way than by just comparing pairs of elements to each
  other, as @{term R} would do.\<close>

lemma gbaux_domI:
  assumes "add_pairs_set apf"
  shows "gbaux_dom (apf, cf, args)"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gbaux_term d"
  from dg have "wf ?R" by (rule gbaux_term_wf)
  thus ?thesis
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> gbaux_term d \<Longrightarrow> gbaux_dom (apf, cf, y)"
    obtain bs rs0 where x: "x = (bs, rs0)" by force
    show "gbaux_dom (apf, cf, x)" unfolding x
    proof (cases rs0)
      case Nil
      show "gbaux_dom (apf, cf, bs, rs0)" unfolding Nil by (rule gbaux.domintros)
    next
      case (Cons pq rs)
      obtain p q where "pq = (p, q)" by force
      from IH' have IH: "\<And>bs' rs'. ((bs', rs'), (bs, (p, q) # rs)) \<in> gbaux_term d \<Longrightarrow> gbaux_dom (apf, cf, bs', rs')"
        unfolding Cons x \<open>pq = (p, q)\<close> by blast
      have *: "gbaux_dom (apf, cf, bs, rs)"
      proof (rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def)
        show "dgrad_p_set_le d (pair_to_set (bs, rs)) (pair_to_set (bs, (p, q) # rs))"
          by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
      qed
      show "gbaux_dom (apf, cf, bs, rs0)" unfolding Cons \<open>pq = (p, q)\<close>
      proof (rule gbaux.domintros)
        assume "trdsp bs p q \<noteq> 0"
        let ?h = "trdsp bs p q"
        show "gbaux_dom (apf, cf, ?h # bs, apf rs bs ?h)"
        proof (rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def, rule)
          show "insert ?h (set bs) \<sqsupset>p set bs"
          proof (rule red_supset_insertI[OF \<open>?h \<noteq> 0\<close>, of "set bs"])
            from trd_irred[of bs "(spoly p q)"] show "\<not> is_red (set bs) ?h" by (simp add: trdsp_def)
          qed
        next
          from dg assms show "dgrad_p_set_le d (pair_to_set (?h # bs, apf rs bs ?h)) (pair_to_set (bs, (p, q) # rs))"
            by (rule dgrad_p_set_le_pair_to_set_trdsp)
        qed
      qed (rule *, rule*)
    qed
  qed
qed

lemma gbaux_simp_1 [simp, code]: "gbaux apf cf bs [] = bs"
  by (rule gbaux.psimps(1), rule gbaux.domintros)

lemma gbaux_simp_2:
  assumes "add_pairs_set apf"
  shows "gbaux apf cf bs ((p, q) # rs) =
      (if cf rs bs p q then
        gbaux apf cf bs rs
      else
        (let h = trdsp bs p q in if h = 0 then gbaux apf cf bs rs else gbaux apf cf (h # bs) (apf rs bs h))
      )"
  by (rule gbaux.psimps(2), rule gbaux_domI, fact)

lemma gbaux_simp_2_1:
  assumes "add_pairs_set apf" and "cf rs bs p q"
  shows "gbaux apf cf bs ((p, q) # rs) = gbaux apf cf bs rs"
  using assms(2) by (simp add: gbaux_simp_2[OF assms(1)])

lemma gbaux_simp_2_2:
  assumes "add_pairs_set apf" and "trdsp bs p q = 0"
  shows "gbaux apf cf bs ((p, q) # rs) = gbaux apf cf bs rs"
  using assms(2) by (simp add: gbaux_simp_2[OF assms(1)])

lemma gbaux_simp_2_3:
  assumes "add_pairs_set apf" and "\<not> cf rs bs p q" and "trdsp bs p q \<noteq> 0"
  shows "gbaux apf cf bs ((p, q) # rs) = gbaux apf cf ((trdsp bs p q) # bs) (apf rs bs (trdsp bs p q))"
  using assms(2) assms(3) by (simp add: gbaux_simp_2[OF assms(1)] Let_def)

text \<open>In order to prove the following lemma we again have to employ well-founded induction, since
  @{thm gbaux.pinduct} does not treat the first arguments of @{const gbaux} (i.\,e. @{term apf} and
  @{term cf}) in the proper way.\<close>
lemma gbaux_induct [consumes 1, case_names base ind1 ind2]:
  assumes "add_pairs_set apf"
  assumes base: "\<And>bs. P bs [] bs"
    and ind1: "\<And>bs ps p q. cf ps bs p q \<or> trdsp bs p q = 0 \<Longrightarrow> P bs ps (gbaux apf cf bs ps) \<Longrightarrow>
                P bs ((p, q) # ps) (gbaux apf cf bs ps)"
    and ind2: "\<And>bs ps p q h. \<not> cf ps bs p q \<Longrightarrow> h = trdsp bs p q \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
                P (h # bs) (apf ps bs h) (gbaux apf cf (h # bs) (apf ps bs h)) \<Longrightarrow>
                P bs ((p, q) # ps) (gbaux apf cf (h # bs) (apf ps bs h))"
  shows "P bs ps (gbaux apf cf bs ps)"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gbaux_term d"
  from dg have "wf ?R" by (rule gbaux_term_wf)
  hence "P (fst (bs, ps)) (snd (bs, ps)) (gbaux apf cf (fst (bs, ps)) (snd (bs, ps)))"
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> gbaux_term d \<Longrightarrow> P (fst y) (snd y) (gbaux apf cf (fst y) (snd y))"
    obtain bs rs0 where x: "x = (bs, rs0)" by force
    show "P (fst x) (snd x) (gbaux apf cf (fst x) (snd x))"
    proof (simp add: x, cases rs0)
      case Nil
      from base show "P bs rs0 (gbaux apf cf bs rs0)" by (simp add: Nil)
    next
      case (Cons pq rs)
      obtain p q where "pq = (p, q)" by force
      from IH' have IH: "\<And>bs' rs'. ((bs', rs'), (bs, (p, q) # rs)) \<in> gbaux_term d \<Longrightarrow> P bs' rs' (gbaux apf cf bs' rs')"
        unfolding Cons x \<open>pq = (p, q)\<close> by auto
      show "P bs rs0 (gbaux apf cf bs rs0)" unfolding Cons \<open>pq = (p, q)\<close>
      proof (cases "cf rs bs p q")
        case True
        show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))"
          unfolding gbaux_simp_2_1[of _ cf, OF assms(1) True]
        proof (rule ind1, rule disjI1, fact, rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def)
          show "dgrad_p_set_le d (pair_to_set (bs, rs)) (pair_to_set (bs, (p, q) # rs))"
            by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
        qed
      next
        case False
        show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))"
        proof (cases "trdsp bs p q = 0")
          case True
          show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))" unfolding gbaux_simp_2_2[OF assms(1) True]
          proof (rule ind1, rule disjI2, fact, rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def)
            show "dgrad_p_set_le d (pair_to_set (bs, rs)) (pair_to_set (bs, (p, q) # rs))"
              by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
          qed
        next
          case False
          let ?h = "trdsp bs p q"
          show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))"
            unfolding gbaux_simp_2_3[of _ cf, OF assms(1) \<open>\<not> cf rs bs p q\<close> False]
          proof (rule ind2, fact, fact refl, fact, rule IH,
                  simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def, rule)
          show "insert ?h (set bs) \<sqsupset>p set bs"
            proof (rule red_supset_insertI[OF \<open>?h \<noteq> 0\<close>, of "set bs"])
              from trd_irred[of bs "(spoly p q)"] show "\<not> is_red (set bs) ?h" by (simp add: trdsp_def)
            qed
          next
            from dg assms(1) show "dgrad_p_set_le d (pair_to_set (?h # bs, apf rs bs ?h)) (pair_to_set (bs, (p, q) # rs))"
              by (rule dgrad_p_set_le_pair_to_set_trdsp)
          qed
        qed
      qed
    qed
  qed
  thus ?thesis by simp
qed

lemma gbaux_sublist:
  assumes "add_pairs_set apf"
  obtains cs::"('a \<Rightarrow>\<^sub>0 'b::field) list" where "gbaux apf cf bs ps = cs @ bs"
  using assms
proof (induct rule: gbaux_induct)
  case (base bs)
  show ?case by (rule base[of "[]"], simp)
next
  case (ind1 bs ps p q)
  show ?case by (rule ind1(2), fact)
next
  case (ind2 bs ps p q h)
  show ?case
  proof (rule ind2(4), rule ind2(5))
    fix cs
    assume "gbaux apf cf (h # bs) (apf ps bs h) = cs @ h # bs"
    thus "gbaux apf cf (h # bs) (apf ps bs h) = (cs @ [h]) @ bs" by simp
  qed
qed

lemma gbaux_subset:
  assumes "add_pairs_set apf"
  shows "set bs \<subseteq> set (gbaux apf cf bs ps)"
proof -
  from assms obtain cs where "gbaux apf cf bs ps = cs @ bs" by (rule gbaux_sublist)
  thus ?thesis by simp
qed

lemma gbaux_dgrad_p_set_le:
  assumes "dickson_grading (+) d" and "add_pairs_set apf"
  shows "dgrad_p_set_le d (set (gbaux apf cf bs ps)) (pair_to_set (bs, ps))"
  using assms(2)
proof (induct rule: gbaux_induct)
  case (base bs)
  thus ?case by (simp add: pair_to_set_def, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (ind1 bs ps p q)
  have "pair_to_set (bs, ps) \<subseteq> pair_to_set (bs, (p, q) # ps)" by (auto simp add: pair_to_set_def)
  hence "dgrad_p_set_le d (pair_to_set (bs, ps)) (pair_to_set (bs, (p, q) # ps))"
    by (rule dgrad_p_set_le_subset)
  with ind1(2) show ?case by (rule dgrad_p_set_le_trans)
next
  case (ind2 bs ps p q h)
  from assms have "dgrad_p_set_le d (pair_to_set (h # bs, apf ps bs h)) (pair_to_set (bs, (p, q) # ps))"
    unfolding ind2(2) by (rule dgrad_p_set_le_pair_to_set_trdsp)
  with ind2(4) show ?case by (rule dgrad_p_set_le_trans)
qed

corollary gbaux_dgrad_p_set:
  assumes "dickson_grading (+) d" and "add_pairs_set apf" and "set bs \<subseteq> dgrad_p_set d m"
    and "fst ` (set ps) \<subseteq> dgrad_p_set d m" and "snd ` (set ps) \<subseteq> dgrad_p_set d m"
  shows "set (gbaux apf cf bs ps) \<subseteq> dgrad_p_set d m"
proof
  fix f::"'a \<Rightarrow>\<^sub>0 'b"
  from assms(1) assms(2) have "dgrad_p_set_le d (set (gbaux apf cf bs ps)) (pair_to_set (bs, ps))"
    by (rule gbaux_dgrad_p_set_le)
  moreover assume "f \<in> set (gbaux apf cf bs ps)"
  ultimately obtain g where "g \<in> pair_to_set (bs, ps)" and le: "dgrad_p d f \<le> dgrad_p d g"
    by (rule dgrad_p_set_leE)
  from this(1) have "g \<in> set bs \<or> g \<in> fst ` (set ps) \<or> g \<in> snd ` (set ps)"
    by (simp add: pair_to_set_def)
  hence "g \<in> dgrad_p_set d m"
  proof (elim disjE)
    assume "g \<in> set bs"
    from this assms(3) show ?thesis ..
  next
    assume "g \<in> fst ` (set ps)"
    from this assms(4) show ?thesis ..
  next
    assume "g \<in> snd ` (set ps)"
    from this assms(5) show ?thesis ..
  qed
  hence "dgrad_p d g \<le> m" by (simp add: dgrad_p_set_alt)
  with le have "dgrad_p d f \<le> m" by (rule le_trans)
  thus "f \<in> dgrad_p_set d m" by (simp add: dgrad_p_set_alt)
qed

lemma gbaux_connectible:
  assumes "add_pairs_set apf" and "crit_conn cf" and "dickson_grading (+) d"
    and "set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> (set bs) \<times> (set bs)"
    and "\<And>p q. processed (p, q) bs ps \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p q"
  assumes "f \<in> set (gbaux apf cf bs ps)" and "g \<in> set (gbaux apf cf bs ps)"
    and "f \<noteq> 0" and "g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (set (gbaux apf cf bs ps)) f g"
  using assms(1, 4, 5, 6, 7, 8)
proof (induct rule: gbaux_induct)
  case (base bs)
  from base(4, 5) have "processed (f, g) bs []" by (simp only: processed_Nil)
  from this \<open>f \<noteq> 0\<close> \<open>g \<noteq> 0\<close> show ?case by (rule base(3))
next
  case (ind1 bs ps p q)

  from ind1(4) have "(p, q) \<in> (set bs) \<times> (set bs)" by simp
  hence "p \<in> set bs" and "q \<in> set bs" by simp_all
  from \<open>p \<in> set bs\<close> ind1(3) have p_in: "p \<in> dgrad_p_set d m" ..
  from \<open>q \<in> set bs\<close> ind1(3) have q_in: "q \<in> dgrad_p_set d m" ..
  from ind1(4) have ps_sub: "set ps \<subseteq> (set bs) \<times> (set bs)" by simp

  have cpq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p q"
  proof -
    assume "p \<noteq> 0" and "q \<noteq> 0"
    from ind1(1) show "crit_pair_cbelow_on d m (set bs) p q"
    proof
      assume "cf ps bs p q"
      with assms(2, 3) ind1(3) ps_sub _ \<open>p \<in> set bs\<close> \<open>q \<in> set bs\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show ?thesis
      proof (rule crit_connD)
        fix p' q'
        assume "processed (p', q') bs ps" and "p' \<noteq> 0" and "q' \<noteq> 0"
          and d1: "p' \<noteq> p \<or> q' \<noteq> q" and d2: "p' \<noteq> q \<or> q' \<noteq> p"
        from this(1) show "crit_pair_cbelow_on d m (set bs) p' q'"
        proof (rule processed_Cons)
          assume "p' = p" and "q' = q"
          with d1 show ?thesis by simp
        next
          assume "p' = q" and "q' = p"
          with d2 show ?thesis by simp
        next
          assume "processed (p', q') bs ((p, q) # ps)"
          from this \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis by (rule ind1(5))
        qed
      qed
    next
      assume "trdsp bs p q = 0"
      from assms(3) ind1(3) p_in q_in \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> this subset_refl show ?thesis
        by (rule trdsp_eq_zero_imp_cbelow_on)
    qed
  qed

  note ind1(3) ps_sub
  moreover {
    fix p' q'
    assume "processed (p', q') bs ps" and "p' \<noteq> 0" and "q' \<noteq> 0"
    from this(1) have "crit_pair_cbelow_on d m (set bs) p' q'"
    proof (rule processed_Cons)
      assume "p' = p" and "q' = q"
      from \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis unfolding \<open>p' = p\<close> \<open>q' = q\<close> by (rule cpq)
    next
      assume "p' = q" and "q' = p"
      from \<open>q' \<noteq> 0\<close> \<open>p' \<noteq> 0\<close> have "crit_pair_cbelow_on d m (set bs) q' p'"
        unfolding \<open>p' = q\<close> \<open>q' = p\<close> by (rule cpq)
      thus ?thesis by (rule crit_pair_cbelow_sym)
    next
      assume "processed (p', q') bs ((p, q) # ps)"
      from this \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis by (rule ind1(5))
    qed
  }
  ultimately show "crit_pair_cbelow_on d m (set (gbaux apf cf bs ps)) f g"
    using ind1(6, 7) by (rule ind1(2))
next
  case (ind2 bs ps p q h)

  from ind2(6) have "(p, q) \<in> (set bs) \<times> (set bs)" by simp
  hence "p \<in> set bs" and "q \<in> set bs" by simp_all
  from \<open>p \<in> set bs\<close> ind2(5) have p_in: "p \<in> dgrad_p_set d m" ..
  from \<open>q \<in> set bs\<close> ind2(5) have q_in: "q \<in> dgrad_p_set d m" ..
  from assms(3) ind2(5) p_in q_in have h_in: "h \<in> dgrad_p_set d m"
    unfolding ind2(2) by (rule dgrad_p_set_closed_trdsp)
  with ind2(5) have hbs_sub: "set (h # bs) \<subseteq> dgrad_p_set d m" by simp
  have "set bs \<subseteq> set (h # bs)" by auto

  from ind2(6) have ps_sub': "set ps \<subseteq> (set bs) \<times> (set bs)" by simp
  with assms(1) have apf_sub: "set (apf ps bs h) \<subseteq> set (h # bs) \<times> set (h # bs)" by (rule add_pairs_setD3)

  have cpq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (set (h # bs)) p q"
  proof -
    assume "p \<noteq> 0" and "q \<noteq> 0"
    have "{h} \<subseteq> set (h # bs)" by simp
    have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) h" unfolding ind2(2) trdsp_def by (rule trd_red_rtrancl)
    from this \<open>set bs \<subseteq> set (h # bs)\<close> have r1: "(red (set (h # bs)))\<^sup>*\<^sup>* (spoly p q) h"
      by (rule red_rtrancl_subset)
    from red_self[OF \<open>h \<noteq> 0\<close>] have "(red {h})\<^sup>*\<^sup>* h 0" ..
    from this \<open>{h} \<subseteq> set (h # bs)\<close> have "(red (set (h # bs)))\<^sup>*\<^sup>* h 0" by (rule red_rtrancl_subset)
    with r1 have "(red (set (h # bs)))\<^sup>*\<^sup>* (spoly p q) 0" by (rule rtranclp_trans)
    show "crit_pair_cbelow_on d m (set (h # bs)) p q"
      by (rule spoly_red_zero_imp_crit_pair_cbelow_on, fact+)
  qed

  from hbs_sub apf_sub _ ind2(8, 9) show ?case
  proof (rule ind2(4))
    fix p' q'
    assume "processed (p', q') (h # bs) (apf ps bs h)" and "p' \<noteq> 0" and "q' \<noteq> 0"
    from processed_add_pairs[OF assms(1) this(1)]
    show "crit_pair_cbelow_on d m (set (h # bs)) p' q'"
    proof
      assume "processed (p', q') bs ps"
      thus ?thesis
      proof (rule processed_Cons)
        assume "p' = p" and "q' = q"
        from \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis unfolding \<open>p' = p\<close> \<open>q' = q\<close> by (rule cpq)
      next
        assume "p' = q" and "q' = p"
        from \<open>q' \<noteq> 0\<close> \<open>p' \<noteq> 0\<close> have "crit_pair_cbelow_on d m (set (h # bs)) q' p'"
          unfolding \<open>p' = q\<close> \<open>q' = p\<close> by (rule cpq)
        thus ?thesis by (rule crit_pair_cbelow_sym)
      next
        assume "processed (p', q') bs ((p, q) # ps)"
        from this \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> have "crit_pair_cbelow_on d m (set bs) p' q'" by (rule ind2(7))
        from this \<open>set bs \<subseteq> set (h # bs)\<close> show ?thesis by (rule crit_pair_cbelow_mono)
      qed
    next
      assume "p' = h \<and> q' = h"
      hence "p' = h" and "q' = h" by simp_all
      from assms(3) h_in show ?thesis unfolding \<open>p' = h\<close> \<open>q' = h\<close> by (rule crit_pair_cbelow_same)
    qed
  qed
qed

lemma gbaux_pideal:
  assumes "add_pairs_set apf" and "set ps \<subseteq> (set bs) \<times> (set bs)"
  shows "pideal (set (gbaux apf cf bs ps)) = pideal (set bs)"
  using assms
proof (induction rule: gbaux_induct)
  case (base bs)
  show ?case ..
next
  case (ind1 bs ps p q)
  from ind1(3) have "set ps \<subseteq> (set bs) \<times> (set bs)" by simp
  thus ?case by (rule ind1(2))
next
  case (ind2 bs ps p q h)
  from ind2(5) have "p \<in> set bs" and "q \<in> set bs" by simp_all
  have "pideal (set (gbaux apf cf (h # bs) (apf ps bs h))) = pideal (set (h # bs))"
  proof (rule ind2(4))
    from assms(1) show "set (apf ps bs h) \<subseteq> set (h # bs) \<times> set (h # bs)"
    proof (rule add_pairs_setD3)
      from ind2(5) show "set ps \<subseteq> (set bs) \<times> (set bs)" by simp
    qed
  qed
  also have "... = pideal (set bs)"
    by (simp add: ind2(2), rule pideal_insert, rule trdsp_in_pideal, fact+)
  finally show "pideal (set (gbaux apf cf (h # bs) (apf ps bs h))) = pideal (set bs)" .
qed

definition gb_param :: "('a, 'b) apT \<Rightarrow> ('a, 'b) critT \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list"
  where "gb_param apf cf bs \<equiv> gbaux apf cf bs (pairs apf bs)"

definition gb :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list"
  where "gb \<equiv> gb_param add_pairs_sorted pc_crit"

theorem gb_param_dgrad_p_set_le:
  assumes "dickson_grading (+) d" and "add_pairs_set apf"
  shows "dgrad_p_set_le d (set (gb_param apf cf bs)) (set bs)"
proof -
  from assms have "dgrad_p_set_le d (set (gbaux apf cf bs (pairs apf bs))) (pair_to_set (bs, pairs apf bs))"
    by (rule gbaux_dgrad_p_set_le)
  also from assms(2) have "... = set bs" by (auto simp add: pair_to_set_def dest: pairsD1 pairsD2)
  finally show ?thesis unfolding gb_param_def .
qed

corollary gb_param_dgrad_p_set:
  assumes "dickson_grading (+) d" and "add_pairs_set apf" and "set bs \<subseteq> dgrad_p_set d m"
  shows "set (gb_param apf cf bs) \<subseteq> dgrad_p_set d m"
  by (rule dgrad_p_set_le_dgrad_p_set, rule gb_param_dgrad_p_set_le, fact+)

theorem gb_param_isGB:
  assumes "add_pairs_set apf" and "crit_conn cf"
  shows "is_Groebner_basis (set (gb_param apf cf bs))"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  obtain m where "set bs \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust, rule finite_set)
  with dg assms(1) have "set (gb_param apf cf bs) \<subseteq> dgrad_p_set d m" by (rule gb_param_dgrad_p_set)
  with dg show ?thesis
  proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
    fix p q
    assume p_in: "p \<in> set (gb_param apf cf bs)" and q_in: "q \<in> set (gb_param apf cf bs)"
    assume "p \<noteq> 0" and "q \<noteq> 0"
    with assms dg \<open>set bs \<subseteq> dgrad_p_set d m\<close> _ _ _ _
    show "crit_pair_cbelow_on d m (set (gb_param apf cf bs)) p q" unfolding gb_param_def
    proof (rule gbaux_connectible)
      from assms(1) show "set (pairs apf bs) \<subseteq> set bs \<times> set bs" by (rule pairs_subset)
    next
      fix p' q'
      assume proc: "processed (p', q') bs (pairs apf bs)"
      hence "p' \<in> set bs" and "q' \<in> set bs" by (rule processedD1, rule processedD2)
      show "crit_pair_cbelow_on d m (set bs) p' q'"
      proof (cases "p' = q'")
        case True
        from dg show ?thesis unfolding True
        proof (rule crit_pair_cbelow_same)
          from \<open>q' \<in> set bs\<close> \<open>set bs \<subseteq> dgrad_p_set d m\<close> show "q' \<in> dgrad_p_set d m" ..
        qed
      next
        case False
        from assms(1) this \<open>p' \<in> set bs\<close> \<open>q' \<in> set bs\<close> have "\<not> processed (p', q') bs (pairs apf bs)"
          by (rule processed_pairs)
        from this proc show ?thesis ..
      qed
    next
      from p_in show "p \<in> set (gbaux apf cf bs (pairs apf bs))" by (simp only: gb_param_def)
    next
      from q_in show "q \<in> set (gbaux apf cf bs (pairs apf bs))" by (simp only: gb_param_def)
    qed
  qed
qed

theorem gb_param_pideal:
  assumes "add_pairs_set apf"
  shows "pideal (set (gb_param apf cf bs)) = pideal (set bs)"
  unfolding gb_param_def using assms
proof (rule gbaux_pideal)
  from assms show "set (pairs apf bs) \<subseteq> set bs \<times> set bs" by (auto dest: pairsD1 pairsD2)
qed

lemmas gb_isGB = gb_param_isGB[OF add_pairs_set_add_pairs_sorted crit_conn_pc_crit, simplified gb_def[symmetric]]
lemmas gb_pideal = gb_param_pideal[OF add_pairs_set_add_pairs_sorted, of pc_crit, simplified gb_def[symmetric]]

text \<open>The following theorem yields a criterion for deciding whether a given polynomial belongs to
  the ideal generated by a given list of polynomials. Note again that @{term "pideal (set bs)"}
  coincides with the ideal (in @{typ "('a, 'b) poly_mapping"}) generated by @{term "set bs"}!\<close>

theorem in_pideal_gb: "p \<in> pideal (set bs) \<longleftrightarrow> (trd (gb bs) p) = 0"
proof
  assume "p \<in> pideal (set bs)"
  hence p_in: "p \<in> pideal (set (gb bs))" using gb_pideal[of bs] by simp
  from gb_isGB[of bs] have cr: "relation.is_ChurchRosser (red (set (gb bs)))"
    unfolding is_Groebner_basis_def .
  hence a: "\<forall>a b. relation.srtc (red (set (gb bs))) a b \<longrightarrow> relation.cs (red (set (gb bs))) a b"
    unfolding relation.is_ChurchRosser_def .
  from a[rule_format, OF in_pideal_srtc[OF p_in]] obtain s
    where r1: "(red (set (gb bs)))\<^sup>*\<^sup>* p s" and r2: "(red (set (gb bs)))\<^sup>*\<^sup>* 0 s"
      unfolding relation.cs_def by auto
  from r1 rtrancl_0[OF r2] have r0: "(red (set (gb bs)))\<^sup>*\<^sup>* p 0" by simp
  from irred_0[of "set (gb bs)"] have fin_0: "relation.is_final (red (set (gb bs))) 0"
    unfolding is_red_def by simp
  from trd_irred[of "gb bs" p] have fin_trd: "relation.is_final (red (set (gb bs))) (trd (gb bs) p)"
    unfolding is_red_def by simp
  from relation.ChurchRosser_unique_final[OF cr trd_red_rtrancl[of "gb bs" p] r0 fin_trd fin_0]
    show "trd (gb bs) p = 0" .
next
  assume "trd (gb bs) p = 0"
  from this trd_in_pideal[of p "gb bs"] have "p \<in> pideal (set (gb bs))" by simp
  thus "p \<in> pideal (set bs)" using gb_pideal[of bs] by simp
qed

end (* gd_powerprod *)

end (* theory *)
