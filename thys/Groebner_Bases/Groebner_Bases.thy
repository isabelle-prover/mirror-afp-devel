(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Gr\"obner Bases\<close>

theory Groebner_Bases
imports Abstract_Poly Confluence
begin

text \<open>This theory provides the main results about Gr\"obner bases of multivariate polynomials.
  Function @{term gb} implements Buchberger's algorithm; the key property of @{term gb} is
  summarized in theorem @{text in_pideal_gb}.\<close>

subsection \<open>Reducibility\<close>

context ordered_powerprod
begin

definition red_single::"('a, 'b::field) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> 'a \<Rightarrow> bool" where
  "red_single p q f t \<equiv> (f \<noteq> 0 \<and> coeff p (t * lp f) \<noteq> 0 \<and>
                          q = p - monom_mult ((coeff p (t * lp f)) / lc f) t f)"
definition red::"('a, 'b::field) mpoly set \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> bool" where
  "red F p q \<equiv> (\<exists>f\<in>F. \<exists>t. red_single p q f t)"
definition is_red::"('a, 'b::field) mpoly set \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> bool" where
  "is_red F a \<equiv> \<not> relation.is_final (red F) a"

lemma red_setI:
  fixes t and p q f::"('a, 'b::field) mpoly" and F::"('a, 'b) mpoly set"
  assumes "f \<in> F" and a: "red_single p q f t"
  shows "red F p q"
unfolding red_def
proof
  from \<open>f \<in> F\<close> show "f \<in> F" .
next
  from a show "\<exists>t. red_single p q f t" ..
qed

lemma red_setE:
  fixes p q::"('a, 'b::field) mpoly" and F::"('a, 'b) mpoly set"
  assumes a: "red F p q"
  obtains f::"('a, 'b) mpoly" and t where "f \<in> F" and "red_single p q f t"
proof -
  from a obtain f where "f \<in> F" and t: "\<exists>t. red_single p q f t" unfolding red_def by auto
  from t obtain t where "red_single p q f t" ..
  from \<open>f \<in> F\<close> this show "?thesis" ..
qed

lemma red_union:
  fixes p q::"('a, 'b::field) mpoly" and F G::"('a, 'b) mpoly set"
  shows "red (F \<union> G) p q = (red F p q \<or> red G p q)"
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
  fixes p q::"('a, 'b::field) mpoly" and F G::"('a, 'b) mpoly set"
  assumes "red F p q"
  shows "red (F \<union> G) p q"
unfolding red_union by (rule disjI1, fact)

lemma red_unionI2:
  fixes p q::"('a, 'b::field) mpoly" and F G::"('a, 'b) mpoly set"
  assumes "red G p q"
  shows "red (F \<union> G) p q"
unfolding red_union by (rule disjI2, fact)

lemma red_subset:
  fixes p q::"('a, 'b::field) mpoly" and F G::"('a, 'b) mpoly set"
  assumes "red G p q" and "G \<subseteq> F"
  shows "red F p q"
proof -
  from \<open>G \<subseteq> F\<close> obtain H where "F = G \<union> H" by auto
  show ?thesis unfolding \<open>F = G \<union> H\<close> by (rule red_unionI1, fact)
qed

lemma red_rtrancl_subset:
  fixes p q::"('a, 'b::field) mpoly" and F G::"('a, 'b) mpoly set"
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

lemma red_singleton:
  fixes p q f::"('a, 'b::field) mpoly"
  shows "red {f} p q \<longleftrightarrow> (\<exists>t. red_single p q f t)"
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

lemma red_single_coeff:
  fixes p q f::"('a, 'b::field) mpoly" and t
  assumes "red_single p q f t"
  shows "coeff q (t * lp f) = 0"
using assms unfolding red_single_def
proof
  assume "f \<noteq> 0" and "coeff p (t * lp f) \<noteq> 0 \<and> q = p - monom_mult (coeff p (t * lp f) / lc f) t f"
  hence "coeff p (t * lp f) \<noteq> 0" and q_def: "q = p - monom_mult (coeff p (t * lp f) / lc f) t f"
    by auto
  from coeff_minus[of p "monom_mult (coeff p (t * lp f) / lc f) t f" "t * lp f"]
       monom_mult_coeff[of "coeff p (t * lp f) / lc f" t f "lp f"]
       lc_not_0[OF \<open>f \<noteq> 0\<close>]
    show ?thesis unfolding q_def lc_def by simp
qed

lemma red_single_higher:
  fixes p q f::"('a, 'b::field) mpoly" and t
  assumes "red_single p q f t"
  shows "higher q (t * lp f) = higher p (t * lp f)"
using assms unfolding higher_equal red_single_def
proof (intro allI, intro impI)
  fix s
  assume a: "t * lp f \<prec> s"
    and "f \<noteq> 0 \<and> coeff p (t * lp f) \<noteq> 0 \<and> q = p - monom_mult (coeff p (t * lp f) / lc f) t f"
  hence "f \<noteq> 0"
    and "coeff p (t * lp f) \<noteq> 0"
    and q_def: "q = p - monom_mult (coeff p (t * lp f) / lc f) t f"
    by simp_all
  from \<open>coeff p (t * lp f) \<noteq> 0\<close> lc_not_0[OF \<open>f \<noteq> 0\<close>] have c_not_0: "coeff p (t * lp f) / lc f \<noteq> 0"
    by (simp add: field_simps)
  from q_def coeff_minus[of p "monom_mult (coeff p (t * lp f) / lc f) t f"]
    have q_coeff: "\<And>s. coeff q s = coeff p s - coeff (monom_mult (coeff p (t * lp f) / lc f) t f) s"
    by simp
  from a lp_mult[OF c_not_0 \<open>f \<noteq> 0\<close>, of t]
    have "\<not> s \<preceq> lp (monom_mult (coeff p (t * lp f) / lc f) t f)" by simp
  with lp_max[of "monom_mult (coeff p (t * lp f) / lc f) t f" s]
    have "coeff (monom_mult (coeff p (t * lp f) / lc f) t f) s = 0" by auto
  thus "coeff q s = coeff p s" using q_coeff[of s] by simp
qed

lemma red_single_ord:
  fixes p q f::"('a, 'b::field) mpoly" and t
  assumes "red_single p q f t"
  shows "q \<prec>p p"
unfolding ord_strict_higher
proof (intro exI, intro conjI)
  from red_single_coeff[OF assms] show "coeff q (t * lp f) = 0" .
next
  from assms show "coeff p (t * lp f) \<noteq> 0" unfolding red_single_def by simp
next
  from red_single_higher[OF assms] show "higher q (t * lp f) = higher p (t * lp f)" .
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
  shows "red_single p 0 p 1"
proof -
  from lc_not_0[OF assms] have lc: "lc p \<noteq> 0" .
  show ?thesis unfolding red_single_def
  proof (intro conjI)
    show "p \<noteq> 0" by fact
  next
    from lc show "coeff p (1 * lp p) \<noteq> 0" unfolding lc_def by simp
  next
    from lc have "(coeff p (1 * lp p)) / lc p = 1" unfolding lc_def by simp
    from this monom_mult_left1[of p] show "0 = p - monom_mult (coeff p (1 * lp p) / lc p) 1 p"
      by simp
  qed
qed

lemma red_single_trans:
  assumes "red_single p p0 f t" and "lp g dvd lp f" and "g \<noteq> 0"
  obtains p1 where "red_single p p1 g (t * (lp f divide lp g))"
proof -
  let ?s = "t * (lp f divide lp g)"
  let ?p = "p - monom_mult (coeff p (?s * lp g) / lc g) ?s g"
  have "red_single p ?p g ?s" unfolding red_single_def
  proof (intro conjI)
    from times_divide_2[of "lp g" "lp f"] divide_times[OF \<open>lp g dvd lp f\<close>, of "lp g"]
      mult.assoc[of t "lp f divide lp g" "lp g"] mult.commute[of "lp f"]
      have eq: "t * (lp f divide lp g) * lp g = t * lp f" by simp
    from \<open>red_single p p0 f t\<close> have "coeff p (t * lp f) \<noteq> 0" unfolding red_single_def by simp
    thus "coeff p (t * (lp f divide lp g) * lp g) \<noteq> 0" by (simp add: eq)
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
  from red_single_self[OF assms] show "red_single p 0 p 1" .
qed

lemma red_ord:
  fixes p q::"('a, 'b::field) mpoly" and F::"('a, 'b) mpoly set"
  assumes "red F p q"
  shows "q \<prec>p p"
proof -
  from red_setE[OF assms] obtain f and t where "red_single p q f t" .
  from red_single_ord[OF this] show "q \<prec>p p" .
qed

lemma red_indI1:
  assumes "f \<in> F" and "f \<noteq> 0" and "p \<noteq> 0" and dvd: "lp f dvd lp p"
  shows "red F p (p - monom_mult (lc p / lc f) (lp p divide lp f) f)"
proof (intro red_setI[OF \<open>f \<in> F\<close>])
  from divide_times[OF dvd, of "lp f"] times_divide[of "lp p" "lp f"]
    have c: "coeff p (lp p divide lp f * lp f) = lc p" unfolding lc_def by simp
  show "red_single p (p - monom_mult (lc p / lc f) (lp p divide lp f) f) f (lp p divide lp f)"
    unfolding red_single_def
  proof (intro conjI, fact)
    from c lc_not_0[OF \<open>p \<noteq> 0\<close>] show "coeff p (lp p divide lp f * lp f) \<noteq> 0" by simp
  next
    from c show "p - monom_mult (lc p / lc f) (lp p divide lp f) f =
                  p - monom_mult (coeff p (lp p divide lp f * lp f) / lc f) (lp p divide lp f) f"
      by simp
  qed
qed

lemma red_indI2:
  assumes "p \<noteq> 0" and r: "red F (tail p) q"
  shows "red F p (q + monom (lc p) (lp p))"
proof -
  from red_setE[OF r] obtain f t where "f \<in> F" and rs: "red_single (tail p) q f t" by auto
  from rs have "f \<noteq> 0" and ct: "coeff (tail p) (t * lp f) \<noteq> 0"
    and q: "q = tail p - monom_mult (coeff (tail p) (t * lp f) / lc f) t f"
    unfolding red_single_def by simp_all
  from ct coeff_tail[OF \<open>p \<noteq> 0\<close>, of "t * lp f"] have "t * lp f \<prec> lp p" by (auto split: if_splits)
  hence c: "coeff (tail p) (t * lp f) = coeff p (t * lp f)" using coeff_tail[OF \<open>p \<noteq> 0\<close>] by simp
  show ?thesis
  proof (intro red_setI[OF \<open>f \<in> F\<close>])
    show "red_single p (q + monom (lc p) (lp p)) f t" unfolding red_single_def
    proof (intro conjI, fact)
      from ct c show "coeff p (t * lp f) \<noteq> 0" by simp
    next
      from q have "q + monom (lc p) (lp p) =
                  (monom (lc p) (lp p) + tail p) - monom_mult (coeff (tail p) (t * lp f) / lc f) t f"
        by simp
      also have "\<dots> = p - monom_mult (coeff (tail p) (t * lp f) / lc f) t f"
        using leading_monomial_tail[OF \<open>p \<noteq> 0\<close>] by simp
      finally show "q + monom (lc p) (lp p) = p - monom_mult (coeff p (t * lp f) / lc f) t f"
        by (simp only: c)
    qed
  qed
qed

lemma red_indE:
  assumes "red F p q"
  shows "(\<exists>f\<in>F. f \<noteq> 0 \<and> lp f dvd lp p \<and>
            (q = p - monom_mult (lc p / lc f) (lp p divide lp f) f)) \<or>
            red F (tail p) (q - monom (lc p) (lp p))"
proof -
  from red_nonzero[OF assms] have "p \<noteq> 0" .
  from red_setE[OF assms] obtain f t where "f \<in> F" and rs: "red_single p q f t" by auto
  from rs have "f \<noteq> 0"
    and cn0: "coeff p (t * lp f) \<noteq> 0"
    and q: "q = p - monom_mult ((coeff p (t * lp f)) / lc f) t f"
    unfolding red_single_def by simp_all
  show ?thesis
  proof (cases "lp p = t * lp f")
    case True
    hence "lp f dvd lp p" by simp
    from True have eq1: "lp p divide lp f = t" using times_divide by simp
    from True have eq2: "lc p = coeff p (t * lp f)" unfolding lc_def by simp
    show ?thesis
    proof (intro disjI1, rule bexI[of _ f], intro conjI, fact+)
      from q eq1 eq2 show "q = p - monom_mult (lc p / lc f) (lp p divide lp f) f" by simp
    qed (fact)
  next
    case False
    from this coeff_tail_2[OF \<open>p \<noteq> 0\<close>, of "t * lp f"]
      have ct: "coeff (tail p) (t * lp f) = coeff p (t * lp f)" by simp
    show ?thesis
    proof (intro disjI2, intro red_setI[of f], fact)
      show "red_single (tail p) (q - monom (lc p) (lp p)) f t" unfolding red_single_def
      proof (intro conjI, fact)
        from cn0 ct show "coeff (tail p) (t * lp f) \<noteq> 0" by simp
      next
        from leading_monomial_tail[OF \<open>p \<noteq> 0\<close>]
          have "p - monom (lc p) (lp p) = (monom (lc p) (lp p) + tail p) - monom (lc p) (lp p)"
          by simp
        also have "\<dots> = tail p" by simp
        finally have eq: "p - monom (lc p) (lp p) = tail p" .
        from q have "q - monom (lc p) (lp p) =
                    (p - monom (lc p) (lp p)) - monom_mult ((coeff p (t * lp f)) / lc f) t f" by simp
        also from eq have "\<dots> = tail p - monom_mult ((coeff p (t * lp f)) / lc f) t f" by simp
        finally show "q - monom (lc p) (lp p) = tail p - monom_mult (coeff (tail p) (t * lp f) / lc f) t f"
          using ct by simp
      qed
    qed
  qed
qed

text \<open>In @{term "red F p q"}, @{term p} is greater than @{term q}, so the converse of
  @{term "red F"} is well-founded.\<close>

lemma red_wf:
  fixes F::"('a, 'b::field) mpoly set"
  shows "wfP (red F)\<inverse>\<inverse>"
proof (intro wfP_subset[OF ord_p_wf], rule)
  fix p q::"('a, 'b) mpoly"
  assume "(red F)\<inverse>\<inverse> q p"
  hence "red F p q" by (rule conversepD)
  from red_ord[OF this] show "q \<prec>p p" .
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
  fixes F::"('a, 'b::field) mpoly set" and q::"('a, 'b) mpoly"
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
  fixes F::"('a, 'b::field) mpoly set" and p q::"('a, 'b) mpoly"
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
  assumes "is_red {f} p" and "lp g dvd lp f" and "g \<noteq> 0"
  shows "is_red {g} p"
proof -
  from \<open>is_red {f} p\<close> obtain q where "red {f} p q" unfolding is_red_alt ..
  from this red_singleton[of f p q] obtain t where "red_single p q f t" by auto
  from red_single_trans[OF this \<open>lp g dvd lp f\<close> \<open>g \<noteq> 0\<close>] obtain q0 where
    "red_single p q0 g (t * (lp f divide lp g))" .
  show ?thesis
  proof (rule is_redI[of "{g}" p q0])
    show "red {g} p q0" unfolding red_def
      by (intro bexI[of _ g], intro exI[of _ "t * (lp f divide lp g)"], fact, simp)
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
  assumes "f \<in> F" and "f \<noteq> 0" and "p \<noteq> 0" and "lp f dvd lp p"
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
  shows "(\<exists>f\<in>F. f \<noteq> 0 \<and> lp f dvd lp p) \<or> is_red F (tail p)"
proof -
  from is_redE[OF assms] obtain q where "red F p q" .
  from red_indE[OF this] show ?thesis
  proof
    assume "\<exists>f\<in>F. f \<noteq> 0 \<and> lp f dvd lp p \<and> q = p - monom_mult (lc p / lc f) (lp p divide lp f) f"
    from this obtain f where "f \<in> F" and "f \<noteq> 0" and "lp f dvd lp p" by auto
    show ?thesis by (intro disjI1, rule bexI[of _ f], intro conjI, fact+)
  next
    assume "red F (tail p) (q - monom (lc p) (lp p))"
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

subsubsection \<open>Reducibility and Addition \& Multiplication\<close>

lemma red_single_mult:
  fixes p q f::"('a, 'b::field) mpoly" and s t and c::'b
  assumes a: "red_single p q f t" and "c \<noteq> 0"
  shows "red_single (monom_mult c s p) (monom_mult c s q) f (s * t)"
proof -
  from a have "f \<noteq> 0"
    and "coeff p (t * lp f) \<noteq> 0"
    and q_def: "q = p - monom_mult ((coeff p (t * lp f)) / lc f) t f"
    unfolding red_single_def by auto
  have assoc: "(s * t) * lp f = s * (t * lp f)" by (simp add: ac_simps)
  have g2: "coeff (monom_mult c s p) ((s * t) * lp f) \<noteq> 0"
  proof
    assume "coeff (monom_mult c s p) ((s * t) * lp f) = 0"
    hence "c * coeff p (t * lp f) = 0" using assoc monom_mult_coeff[of c s p "t * lp f"] by simp
    thus False using \<open>c \<noteq> 0\<close> \<open>coeff p (t * lp f) \<noteq> 0\<close> by simp
  qed
  have g3: "monom_mult c s q =
    (monom_mult c s p) - monom_mult ((coeff (monom_mult c s p) ((s * t) * lp f)) / lc f) (s * t) f"
  proof -
    from q_def monom_mult_dist_right_minus[of c s p]
      have "monom_mult c s q =
            monom_mult c s p - monom_mult c s (monom_mult (coeff p (t * lp f) / lc f) t f)" by simp
    also from monom_mult_assoc[of c s "coeff p (t * lp f) / lc f" t f] assoc
      monom_mult_coeff[of c s p "t * lp f"]
      have "monom_mult c s (monom_mult (coeff p (t * lp f) / lc f) t f) =
            monom_mult ((coeff (monom_mult c s p) ((s * t) * lp f)) / lc f) (s * t) f" by simp
    finally show ?thesis .
  qed
  from \<open>f \<noteq> 0\<close> g2 g3 show ?thesis unfolding red_single_def by auto
qed

lemma red_single_plus:
  fixes p q r f::"('a, 'b::field) mpoly" and t
  assumes "red_single p q f t"
  shows "red_single (p + r) (q + r) f t \<or>
          red_single (q + r) (p + r) f t \<or>
          (\<exists>s. red_single (p + r) s f t \<and> red_single (q + r) s f t)"
proof -
  from assms have "f \<noteq> 0"
    and "coeff p (t * lp f) \<noteq> 0"
    and q_def: "q = p - monom_mult ((coeff p (t * lp f)) / lc f) t f"
    unfolding red_single_def by auto
  hence q_r: "q + r = (p + r) - monom_mult ((coeff p (t * lp f)) / lc f) t f" by simp
  from red_single_coeff[OF assms] have cq_0: "coeff q (t * lp f) = 0" .
  from
      coeff_plus[of p r "t * lp f"]
      lc_not_0[OF \<open>f \<noteq> 0\<close>]
      monom_mult_dist_left[of "(coeff p (t * lp f)) / lc f" "(coeff r (t * lp f)) / lc f" t f]
    have eq1: "monom_mult ((coeff (p + r) (t * lp f)) / lc f) t f =
              (monom_mult ((coeff p (t * lp f)) / lc f) t f) +
                (monom_mult ((coeff r (t * lp f)) / lc f) t f)"
    by (simp add: field_simps)
  from coeff_plus[of q r "t * lp f"] lc_not_0[OF \<open>f \<noteq> 0\<close>] cq_0
      monom_mult_dist_left[of "(coeff q (t * lp f)) / lc f" "(coeff r (t * lp f)) / lc f" t f]
    have eq2: "monom_mult ((coeff (q + r) (t * lp f)) / lc f) t f =
                monom_mult ((coeff r (t * lp f)) / lc f) t f"
    by (simp add: field_simps)
  show ?thesis
  proof (cases "coeff (p + r) (t * lp f) = 0")
    assume "coeff (p + r) (t * lp f) = 0"
    with neg_eq_iff_add_eq_0[of "coeff p (t * lp f)" "coeff r (t * lp f)"]
          coeff_plus[of p r "t * lp f"]
      have cr: "coeff r (t * lp f) = - (coeff p (t * lp f))" by simp
    hence cr_not_0: "coeff r (t * lp f) \<noteq> 0" using \<open>coeff p (t * lp f) \<noteq> 0\<close> by simp
    have "red_single (q + r) (p + r) f t" unfolding red_single_def
    proof
      from \<open>f \<noteq> 0\<close> show "f \<noteq> 0" .
    next
      show "coeff (q + r) (t * lp f) \<noteq> 0 \<and>
            p + r = q + r - monom_mult (coeff (q + r) (t * lp f) / lc f) t f"
      proof
        from coeff_plus[of q r "t * lp f"] cr_not_0 cq_0
          show "coeff (q + r) (t * lp f) \<noteq> 0" by simp
      next
        from eq2 cr monom_mult_uminus_left[of "(coeff p (t * lp f) / lc f)" t f]
          show "p + r = q + r - monom_mult (coeff (q + r) (t * lp f) / lc f) t f"
            unfolding q_def by simp
      qed
    qed
    thus ?thesis by simp
  next
    assume cpr: "coeff (p + r) (t * lp f) \<noteq> 0"
    show ?thesis
    proof (cases "coeff (q + r) (t * lp f) = 0")
      case True
      hence cr_0: "coeff r (t * lp f) = 0" using coeff_plus[of q r "t * lp f"] cq_0 by simp
      have "red_single (p + r) (q + r) f t" unfolding red_single_def
      proof
        from \<open>f \<noteq> 0\<close> show "f \<noteq> 0" .
      next
        show "coeff (p + r) (t * lp f) \<noteq> 0 \<and>
              q + r = p + r - monom_mult (coeff (p + r) (t * lp f) / lc f) t f"
        proof
          from cr_0 \<open>coeff p (t * lp f) \<noteq> 0\<close> coeff_plus[of p r]
            show "coeff (p + r) (t * lp f) \<noteq> 0" by simp
        next
          from q_r eq1 cr_0 monom_mult_left0[of t f]
            show "q + r = p + r - monom_mult (coeff (p + r) (t * lp f) / lc f) t f"
              by (simp add: field_simps)
        qed
      qed
      thus ?thesis by simp
    next
      case False
      let ?s = "(p + r) - monom_mult ((coeff (p + r) (t * lp f)) / lc f) t f"
      have r1: "red_single (p + r) ?s f t" using \<open>f \<noteq> 0\<close> cpr unfolding red_single_def by simp
      have r2: "red_single (q + r) ?s f t" unfolding red_single_def
      proof
        from \<open>f \<noteq> 0\<close> show "f \<noteq> 0" .
      next
        show "coeff (q + r) (t * lp f) \<noteq> 0 \<and>
                p + r - monom_mult (coeff (p + r) (t * lp f) / lc f) t f =
                q + r - monom_mult (coeff (q + r) (t * lp f) / lc f) t f"
        proof
          from False show "coeff (q + r) (t * lp f) \<noteq> 0" .
        next
          from eq1 eq2 q_def
            show "p + r - monom_mult (coeff (p + r) (t * lp f) / lc f) t f =
                  q + r - monom_mult (coeff (q + r) (t * lp f) / lc f) t f" by simp
        qed
      qed
      from r1 r2 show ?thesis by auto
    qed
  qed
qed

lemma red_mult:
  fixes c::"'b::field" and s and p q::"('a, 'b) mpoly" and F::"('a, 'b) mpoly set"
  assumes a: "red F p q" and "c \<noteq> 0"
  shows "red F (monom_mult c s p) (monom_mult c s q)"
proof -
  from red_setE[OF a] obtain f and t where "f \<in> F" and rs: "red_single p q f t" by auto
  from red_single_mult[OF rs \<open>c \<noteq> 0\<close>, of s] show ?thesis by (intro red_setI[OF \<open>f \<in> F\<close>])
qed

lemma red_plus:
  fixes p q r::"('a, 'b::field) mpoly" and F::"('a, 'b) mpoly set"
  assumes a: "red F p q"
  obtains s::"('a, 'b) mpoly" where "(red F)\<^sup>*\<^sup>* (p + r) s" and "(red F)\<^sup>*\<^sup>* (q + r) s"
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

lemma red_uminus:
  fixes p q::"('a, 'b::field) mpoly" and F::"('a, 'b) mpoly set"
  assumes "red F p q"
  shows "red F (-p) (-q)"
proof -
  from red_mult[OF assms, of "-1" 1] show ?thesis by (simp add: uminus_monom_mult)
qed

lemma red_plus_cs:
  assumes "red F p q"
  shows "relation.cs (red F) (p + r) (q + r)"
unfolding relation.cs_def
proof -
  from red_plus[OF assms, of r] obtain s where "(red F)\<^sup>*\<^sup>* (p + r) s" and "(red F)\<^sup>*\<^sup>* (q + r) s" .
  show "\<exists>s. (red F)\<^sup>*\<^sup>* (p + r) s \<and> (red F)\<^sup>*\<^sup>* (q + r) s" by (intro exI, intro conjI, fact, fact)
qed

subsubsection \<open>Confluence of Reducibility\<close>

lemma confluent_distinct_aux:
  fixes p q1 q2 f1 f2::"('a, 'b::field) mpoly" and t1 t2 and F::"('a, 'b) mpoly set"
  assumes r1: "red_single p q1 f1 t1" and r2: "red_single p q2 f2 t2"
    and "t1 * lp f1 \<prec> t2 * lp f2" and "f1 \<in> F" and "f2 \<in> F"
  obtains s::"('a, 'b) mpoly" where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof -
  from r1 have "f1 \<noteq> 0" and c1: "coeff p (t1 * lp f1) \<noteq> 0"
    and q1_def: "q1 = p - monom_mult (coeff p (t1 * lp f1) / lc f1) t1 f1"
    unfolding red_single_def by auto
  from r2 have "f2 \<noteq> 0" and c2: "coeff p (t2 * lp f2) \<noteq> 0"
    and q2_def: "q2 = p - monom_mult (coeff p (t2 * lp f2) / lc f2) t2 f2"
    unfolding red_single_def by auto
  from coeff_mult_0[OF \<open>t1 * lp f1 \<prec> t2 * lp f2\<close>]
    have "coeff (monom_mult (coeff p (t1 * lp f1) / lc f1) t1 f1) (t2 * lp f2) = 0" by simp
  from coeff_minus[of p _ "t2 * lp f2"] this have c: "coeff q1 (t2 * lp f2) = coeff p (t2 * lp f2)"
    unfolding q1_def by simp
  def q3 \<equiv> "q1 - monom_mult ((coeff q1 (t2 * lp f2)) / lc f2) t2 f2"
  have "red_single q1 q3 f2 t2" unfolding red_single_def
  proof (rule, fact, rule)
    from c c2 show "coeff q1 (t2 * lp f2) \<noteq> 0" by simp
  next
    show "q3 = q1 - monom_mult (coeff q1 (t2 * lp f2) / lc f2) t2 f2" unfolding q3_def ..
  qed
  hence "red F q1 q3" by (intro red_setI[OF \<open>f2 \<in> F\<close>])
  hence q1q3: "(red F)\<^sup>*\<^sup>* q1 q3" by (intro r_into_rtranclp)
  from r1 have "red F p q1" by (intro red_setI[OF \<open>f1 \<in> F\<close>])
  from red_plus[OF this, of "- monom_mult ((coeff p (t2 * lp f2)) / lc f2) t2 f2"] obtain s
    where r3: "(red F)\<^sup>*\<^sup>* (p - monom_mult (coeff p (t2 * lp f2) / lc f2) t2 f2) s"
    and r4: "(red F)\<^sup>*\<^sup>* (q1 - monom_mult (coeff p (t2 * lp f2) / lc f2) t2 f2) s" by auto
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
  fixes p q1 q2 f1 f2::"('a, 'b::field) mpoly" and t1 t2 and F::"('a, 'b) mpoly set"
  assumes r1: "red_single p q1 f1 t1" and r2: "red_single p q2 f2 t2"
    and ne: "t1 * lp f1 \<noteq> t2 * lp f2" and "f1 \<in> F" and "f2 \<in> F"
  obtains s::"('a, 'b) mpoly" where "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s"
proof -
  from ne have "t1 * lp f1 \<prec> t2 * lp f2 \<or> t2 * lp f2 \<prec> t1 * lp f1" by auto
  thus ?thesis
  proof
    assume a1: "t1 * lp f1 \<prec> t2 * lp f2"
    from confluent_distinct_aux[OF r1 r2 a1 \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>] obtain s where
      "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s" .
    thus ?thesis ..
  next
    assume a2: "t2 * lp f2 \<prec> t1 * lp f1"
    from confluent_distinct_aux[OF r2 r1 a2 \<open>f2 \<in> F\<close> \<open>f1 \<in> F\<close>] obtain s where
      "(red F)\<^sup>*\<^sup>* q1 s" and "(red F)\<^sup>*\<^sup>* q2 s" .
    thus ?thesis ..
  qed
qed

subsubsection \<open>Reducibility and Ideal Membership\<close>

lemma srtc_in_pideal:
  assumes "relation.srtc (red F) p q"
  shows "p - q \<in> pideal F"
using assms unfolding relation.srtc_def
proof (induct rule: rtranclp.induct)
  fix p
  from pideal_0[of F] show "p - p \<in> pideal F" by simp
next
  fix p r q
  assume pr_in: "p - r \<in> pideal F" and red: "red F r q \<or> red F q r"
  from red obtain f c t where "f \<in> F" and "q = r - monom_mult c t f"
  proof
    assume "red F r q"
    thm red_setE[show_types]
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single r q f t" .
    hence "q = r - monom_mult (coeff r (t * lp f) / lc f) t f" unfolding red_single_def by simp
    show thesis by (rule, fact, fact)
  next
    assume "red F q r"
    from red_setE[OF this] obtain f t where "f \<in> F" and "red_single q r f t" .
    hence "r = q - monom_mult (coeff q (t * lp f) / lc f) t f" unfolding red_single_def by simp
    hence "q = r + monom_mult (coeff q (t * lp f) / lc f) t f" by simp
    hence "q = r - monom_mult (-(coeff q (t * lp f) / lc f)) t f"
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
proof (induct p)
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
        from monom_mult_coeff[of c t f "lp f"]
          have eq: "coeff (monom_mult c t f) (t * lp f) = c * lc f" unfolding lc_def .
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
        from s1 show "(red F)\<^sup>*\<^sup>* (a + monom_mult c t f) s" by (simp only: plus_mpoly_comm)
      next
        from s2 show "(red F)\<^sup>*\<^sup>* a s" by simp
      qed
      from relation.srtc_transitive[OF relation.cs_implies_srtc[OF this] IH] show ?thesis .
    qed
  qed
qed

lemma is_relation_order:
  fixes F::"('a, 'b::field) mpoly set"
  shows "Confluence.relation_order (red F) (op \<preceq>p) (op \<prec>p)"
proof
  show "red F \<le> op \<prec>p\<inverse>\<inverse>"
  proof
    fix x y
    assume "red F x y"
    show "(op \<prec>p)\<inverse>\<inverse> x y"
    proof
      from red_ord[OF \<open>red F x y\<close>] show "y \<prec>p x" .
    qed
  qed
next
  from ord_p_wf show "wfP op \<prec>p" .
qed

subsection \<open>Gr\"obner Bases and Buchberger's Theorem\<close>

definition is_Groebner_basis::"('a, 'b::field) mpoly set \<Rightarrow> bool"
  where "is_Groebner_basis F \<equiv> relation.is_ChurchRosser (red F)"

definition spoly::"('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b::field) mpoly" where
  "spoly p q \<equiv> (monom_mult (1 / lc p) ((lcm (lp p) (lp q)) divide (lp p)) p) -
                (monom_mult (1 / lc q) ((lcm (lp p) (lp q)) divide (lp q)) q)"

lemma spoly_same:
  shows "spoly p p = 0"
unfolding spoly_def by simp

lemma spoly_exchange:
  shows "spoly p q = - spoly q p"
unfolding spoly_def by (simp add: lcm_comm)

lemma red_rtrancl_mult:
  fixes p q::"('a, 'b::field) mpoly" and c::'b and t
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
      from red_mult[OF \<open>red F q0 q\<close> False, of t] show "red F (monom_mult c t q0) (monom_mult c t q)" .
    qed
  qed
qed

lemma red_rtrancl_uminus:
  fixes p q::"('a, 'b::field) mpoly"
  assumes "(red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* (-p) (-q)"
proof -
  from red_rtrancl_mult[OF assms, of "-1" 1] show ?thesis by (simp add: uminus_monom_mult)
qed

lemma red_rtrancl_diff_induct:
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

lemma red_rtrancl_diff_0_induct:
  assumes a: "(red F)\<^sup>*\<^sup>* (p - q) 0"
    and base: "P p p" and ind: "\<And>y z. [| (red F)\<^sup>*\<^sup>* (p - q) y; red F y z; P p (y + q)|] ==> P p (z + q)"
  shows "P p q"
proof -
  from ind red_rtrancl_diff_induct[of F p q 0 P, OF a base] have "P p (0 + q)"
    by (simp add: plus_mpoly_comm)
  thus ?thesis by simp
qed

text \<open>The following is the key result in the theory of Gr\"obner bases. Its proof is modelled after
  the one given in @{cite Buchberger1998a}.\<close>

theorem Buchberger_criterion:
  assumes "\<And>p q. p \<in> F \<Longrightarrow> q \<in> F \<Longrightarrow> (red F)\<^sup>*\<^sup>* (spoly p q) 0"
  shows "is_Groebner_basis F"
proof -
  have "relation_order.is_loc_connective (red F) (op \<prec>p)"
    unfolding relation_order.is_loc_connective_def[OF is_relation_order]
  proof (intro allI, intro impI)
    fix a b1 b2
    assume "red F a b1 \<and> red F a b2"
    hence "red F a b1" and "red F a b2" by auto
    from red_setE[OF \<open>red F a b1\<close>] obtain f1 and t1 where "f1 \<in> F" and r1: "red_single a b1 f1 t1" .
    from red_setE[OF \<open>red F a b2\<close>] obtain f2 and t2 where "f2 \<in> F" and r2: "red_single a b2 f2 t2" .
    from red_single_ord[OF r1] have "b1 \<prec>p a" .
    from red_single_ord[OF r2] have "b2 \<prec>p a" .
    from r1 r2 have "f1 \<noteq> 0" and "f2 \<noteq> 0" unfolding red_single_def by simp_all
    hence lc1: "lc f1 \<noteq> 0" and lc2: "lc f2 \<noteq> 0" using lc_not_0 by auto
    show "cbelow (op \<prec>p) a (\<lambda>a b. red F a b \<or> red F b a) b1 b2"
    proof (cases "t1 * lp f1 = t2 * lp f2")
      case False
      from confluent_distinct[OF r1 r2 False \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>] obtain s where
        s1: "(red F)\<^sup>*\<^sup>* b1 s" and s2: "(red F)\<^sup>*\<^sup>* b2 s" .
      have "relation.cs (red F) b1 b2" unfolding relation.cs_def
      proof (intro exI, intro conjI)
        from s1 show "(red F)\<^sup>*\<^sup>* b1 s" .
      next
        from s2 show "(red F)\<^sup>*\<^sup>* b2 s" .
      qed
      from relation_order.cs_implies_cbelow[OF is_relation_order this \<open>b1 \<prec>p a\<close> \<open>b2 \<prec>p a\<close>]
        show ?thesis .
    next
      case True
      def t \<equiv> "t2 * lp f2"
      def l \<equiv> "lcm (lp f1) (lp f2)"
      from dvd_lcm[of "lp f1" "lp f2"] have "(lp f1) dvd l" unfolding l_def .
      from dvd_lcm_2[of "lp f2" "lp f1"] have "(lp f2) dvd l" unfolding l_def .
      have "lp f1 dvd (t1 * lp f1)" unfolding t_def by simp
      hence "lp f1 dvd t" using True unfolding t_def by simp
      have "lp f2 dvd t" unfolding t_def by simp
      from lcm_min[OF \<open>lp f1 dvd t\<close> \<open>lp f2 dvd t\<close>] have "l dvd t" unfolding l_def .
      from times_divide_2[of "lp f1" t1] mult.commute[of "lp f1" t1] True
        have "t divide (lp f1) = t1" unfolding t_def by simp
      from divide_times_divide_cancel[OF \<open>l dvd t\<close> \<open>lp f1 dvd l\<close>] this
        have tf1: "(t divide l) * (l divide (lp f1)) = t1" by simp
      from times_divide_2[of "lp f2" t2] mult.commute[of "lp f2" t2]
        have "t divide (lp f2) = t2" unfolding t_def by simp
      from divide_times_divide_cancel[OF \<open>l dvd t\<close> \<open>lp f2 dvd l\<close>] this
        have tf2: "(t divide l) * (l divide (lp f2)) = t2" by simp
      let ?ca = "coeff a t"
      let ?v = "t divide l"
      have "b2 - b1 = monom_mult (?ca / lc f1) t1 f1 - monom_mult (?ca / lc f2) t2 f2"
        using True r1 r2 unfolding red_single_def t_def by simp
      also have "\<dots> = monom_mult ?ca ?v (spoly f1 f2)"
        using monom_mult_dist_right_minus[of ?ca ?v] monom_mult_assoc[of ?ca ?v] tf1 tf2 lc1 lc2
        unfolding l_def spoly_def by simp
      finally have "b2 - b1 = monom_mult ?ca ?v (spoly f1 f2)" .
      from this red_rtrancl_mult[OF assms[OF \<open>f1 \<in> F\<close> \<open>f2 \<in> F\<close>], of ?ca ?v]
        have "(red F)\<^sup>*\<^sup>* (b2 - b1) 0" by (simp add: monom_mult_right0)
      from red_rtrancl_uminus[OF this] have "(red F)\<^sup>*\<^sup>* (b1 - b2) 0" by simp
      thus ?thesis
      proof (rule red_rtrancl_diff_0_induct)
        show "cbelow op \<prec>p a (\<lambda>a b. red F a b \<or> red F b a) b1 b1" unfolding cbelow_def
          by (intro disjI1, intro conjI, simp, fact)
      next
        fix y z
        assume "(red F)\<^sup>*\<^sup>* (b1 - b2) y" and "red F y z"
          and "cbelow op \<prec>p a (\<lambda>a b. red F a b \<or> red F b a) b1 (y + b2)"
        show "cbelow op \<prec>p a (\<lambda>a b. red F a b \<or> red F b a) b1 (z + b2)"
        proof (rule cbelow_transitive)
          show "cbelow op \<prec>p a (\<lambda>a b. red F a b \<or> red F b a) b1 (y + b2)" by fact
        next
          from True red_single_coeff[OF r1]
            have c1: "coeff b1 t = 0" unfolding t_def by simp
          from red_single_coeff[OF r2]
            have c2: "coeff b2 t = 0" unfolding t_def by simp
          from red_single_higher[OF r1] True
            have h1: "higher b1 t = higher a t" unfolding t_def by simp
          from red_single_higher[OF r2]
            have h2: "higher b2 t = higher a t" unfolding t_def by simp
          from h1 h2 have h: "higher b1 t = higher b2 t" by simp
          from cbelow_second_below[OF \<open>cbelow op \<prec>p a (\<lambda>a b. red F a b \<or> red F b a) b1 (y + b2)\<close>]
            have "y + b2 \<prec>p a" .
          show "cbelow op \<prec>p a (\<lambda>a b. red F a b \<or> red F b a) (y + b2) (z + b2)"
          proof (rule relation_order.cs_implies_cbelow[OF is_relation_order red_plus_cs[OF \<open>red F y z\<close>]])
            from \<open>(red F)\<^sup>*\<^sup>* (b1 - b2) y\<close> \<open>red F y z\<close> have "(red F)\<^sup>*\<^sup>* (b1 - b2) z" by simp
            hence "coeff z t = 0 \<and> higher z t = 0"
            proof (induct rule: rtranclp_induct)
              from coeff_minus[of b1 b2 t] higher_minus[of b1 b2 t] c1 c2 h
                show "coeff (b1 - b2) t = 0 \<and> higher (b1 - b2) t = 0" by simp
            next
              fix y0 z0
              assume "red F y0 z0" and "coeff y0 t = 0 \<and> higher y0 t = 0"
              hence cy0: "coeff y0 t = 0" and hy0: "higher y0 t = 0" by auto
              from red_ord[OF \<open>red F y0 z0\<close>] have "z0 \<preceq>p y0" by simp
              from higher_coeff_equal_0[OF cy0 hy0 this] show "coeff z0 t = 0 \<and> higher z0 t = 0" .
            qed
            hence cz: "coeff z t = 0" and hz: "higher z t = 0" by auto
            show "z + b2 \<prec>p a" unfolding ord_strict_higher
            proof
              show "coeff (z + b2) t = 0 \<and> coeff a t \<noteq> 0 \<and> higher (z + b2) t = higher a t"
              proof (intro conjI)
                from coeff_plus[of z b2 t] cz c2 show "coeff (z + b2) t = 0" by simp
              next
                from r2 show "coeff a t \<noteq> 0" unfolding red_single_def t_def by simp
              next
                from higher_plus[of z b2 t] hz h2 show "higher (z + b2) t = higher a t" by simp
              qed
            qed
          qed (fact)
        qed
      qed
    qed
  qed
  thus ?thesis using relation_order.loc_connectivity_equiv_ChurchRosser[OF is_relation_order, of F]
    unfolding is_Groebner_basis_def by simp
qed

end (* ordered_powerprod *)

subsection \<open>Algorithms\<close>

subsubsection \<open>Functions @{term up} and @{term pairs}\<close>

definition up::"(('a, 'b) mpoly * ('a, 'b) mpoly) list \<Rightarrow> ('a, 'b) mpoly list \<Rightarrow> ('a, 'b) mpoly \<Rightarrow>
                (('a, 'b) mpoly * ('a, 'b) mpoly) list"
  where "up ps bs h \<equiv> ps @ (map (\<lambda>b. (b, h)) bs)"

lemma in_upI1:
  assumes "p \<in> set ps"
  shows "p \<in> set (up ps bs h)"
using assms unfolding up_def by simp

lemma in_upI2:
  assumes "p \<in> set bs"
  shows "(p, h) \<in> set (up ps bs h)"
using assms unfolding up_def by simp

lemma in_upE:
  assumes "(a, b) \<in> set (up ps bs h)"
  obtains "(a, b) \<in> set ps"|"b = h \<and> a \<in> set bs"
using assms unfolding up_def
proof -
  assume a1: "(a, b) \<in> set ps \<Longrightarrow> thesis" and a2: "b = h \<and> a \<in> set bs \<Longrightarrow> thesis"
    and pair_in: "(a, b) \<in> set (ps @ map (\<lambda>b. (b, h)) bs)"
  from pair_in have "(a, b) \<in> set ps \<or> (a, b) \<in> set (map (\<lambda>b. (b, h)) bs)" by simp
  thus thesis
  proof
    assume "(a, b) \<in> set ps"
    show ?thesis by (rule a1, fact)
  next
    assume "(a, b) \<in> set (map (\<lambda>b. (b, h)) bs)"
    from this obtain a0 where "a0 \<in> set bs" and "(a, b) = (a0, h)" by auto
    hence "a = a0" and "b = h" by simp_all
    show ?thesis by (rule a2, intro conjI, fact, simp only: \<open>a = a0\<close>, fact)
  qed
qed

fun pairs::"('a, 'b) mpoly list \<Rightarrow> (('a, 'b) mpoly * ('a, 'b) mpoly) list" where
  "pairs [] = []"|
  "pairs (x # xs) = (map (Pair x) xs) @ (pairs xs)"

lemma in_pairsI:
  assumes "p \<noteq> q" and "p \<in> set bs" and "q \<in> set bs"
  obtains "(p, q) \<in> set (pairs bs)"|"(q, p) \<in> set (pairs bs)"
using assms
proof (induct rule: pairs.induct)
  assume "p \<in> set []"
  thus thesis by simp
next
  fix x xs
  assume IH: "((p, q) \<in> set (pairs xs) \<Longrightarrow> thesis) \<Longrightarrow> ((q, p) \<in> set (pairs xs) \<Longrightarrow> thesis) \<Longrightarrow>
              p \<noteq> q \<Longrightarrow> p \<in> set xs \<Longrightarrow> q \<in> set xs \<Longrightarrow> thesis"
    and pq: "(p, q) \<in> set (pairs (x # xs)) \<Longrightarrow> thesis"
    and qp: "(q, p) \<in> set (pairs (x # xs)) \<Longrightarrow> thesis"
    and "p \<noteq> q" and p_in: "p \<in> set (x # xs)" and q_in: "q \<in> set (x # xs)"
  from p_in have p_cases: "p = x \<or> p \<in> set xs" by simp
  from q_in have q_cases: "q = x \<or> q \<in> set xs" by simp
  from p_cases show thesis
  proof
    assume "p = x"
    from this q_cases \<open>p \<noteq> q\<close> have "q \<in> set xs" by simp
    show ?thesis
    proof (rule pq, simp only: \<open>p = x\<close>)
      from \<open>q \<in> set xs\<close> have "(x, q) \<in> set (map (Pair x) xs)" by simp
      thus "(x, q) \<in> set (pairs (x # xs))" by simp
    qed
  next
    assume "p \<in> set xs"
    from q_cases show ?thesis
    proof
      assume "q = x"
      show ?thesis
      proof (rule qp, simp only: \<open>q = x\<close>)
        from \<open>p \<in> set xs\<close> have "(x, p) \<in> set (map (Pair x) xs)" by simp
        thus "(x, p) \<in> set (pairs (x # xs))" by simp
      qed
    next
      assume "q \<in> set xs"
      show ?thesis
      proof (rule IH)
        assume a: "(p, q) \<in> set (pairs xs)"
        show thesis
        proof (rule pq)
          from a show "(p, q) \<in> set (pairs (x # xs))" by simp
        qed
      next
        assume a: "(q, p) \<in> set (pairs xs)"
        show thesis
        proof (rule qp)
          from a show "(q, p) \<in> set (pairs (x # xs))" by simp
        qed
      qed (fact+)
    qed
  qed
qed

lemma in_pairsD1:
  assumes "(p, q) \<in> set (pairs bs)"
  shows "p \<in> set bs"
using assms
proof (induct rule: pairs.induct)
  assume "(p, q) \<in> set (pairs [])"
  thus "p \<in> set []" by simp
next
  fix x xs
  assume IH: "(p, q) \<in> set (pairs xs) \<Longrightarrow> p \<in> set xs"
    and a: "(p, q) \<in> set (pairs (x # xs))"
  from a have "(p, q) \<in> set (map (Pair x) xs) \<or> (p, q) \<in> set (pairs xs)" by simp
  thus "p \<in> set (x # xs)"
  proof
    assume "(p, q) \<in> set (map (Pair x) xs)"
    hence "p = x" by auto
    thus ?thesis by simp
  next
    assume "(p, q) \<in> set (pairs xs)"
    from IH[OF this] show ?thesis by simp
  qed
qed

lemma in_pairsD2:
  assumes "(p, q) \<in> set (pairs bs)"
  shows "q \<in> set bs"
using assms
proof (induct rule: pairs.induct)
  assume "(p, q) \<in> set (pairs [])"
  thus "q \<in> set []" by simp
next
  fix x xs
  assume IH: "(p, q) \<in> set (pairs xs) \<Longrightarrow> q \<in> set xs"
    and a: "(p, q) \<in> set (pairs (x # xs))"
  from a have "(p, q) \<in> set (map (Pair x) xs) \<or> (p, q) \<in> set (pairs xs)" by simp
  thus "q \<in> set (x # xs)"
  proof
    assume "(p, q) \<in> set (map (Pair x) xs)"
    hence "q \<in> set xs" by auto
    thus ?thesis by simp
  next
    assume "(p, q) \<in> set (pairs xs)"
    from IH[OF this] show ?thesis by simp
  qed
qed

subsubsection \<open>Function @{term rd}\<close>

context ordered_powerprod
begin

function rd_mult::"('a, 'b::field) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('b * 'a)" where
  "rd_mult p f =
    (if p = 0 \<or> f = 0 then
      (0, 1)
    else
      (if lp f dvd lp p then
        (lc p / lc f, lp p divide lp f)
      else
        rd_mult (tail p) f
      )
    )"
by auto
termination proof -
  let ?R = "{(x, y). x \<prec>p y} <*lex*> {}"
  show ?thesis
  proof
    show "wf ?R"
    proof
      from ord_p_wf show "wf {(x, y). x \<prec>p y}" unfolding wfP_def .
    qed (simp)
  next
    fix p f::"('a, 'b) mpoly"
    assume "\<not> (p = 0 \<or> f = 0)"
    hence "p \<noteq> 0" by simp
    from tail_ord_p[OF this] show "((tail p, f), p, f) \<in> ?R" by simp
  qed
qed

definition rd::"('a, 'b::field) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly"
where "rd p f \<equiv> (let m = rd_mult p f in p - monom_mult (fst m) (snd m) f)"

lemma compute_rd_mult[code]:
  "rd_mult p f =
    (if p = 0 \<or> f = 0 then
      (0, 1)
    else
      (if dummy_dvd (lp f) (lp p) then
        (lc p / lc f, lp p divide lp f)
      else
        rd_mult (tail p) f
      )
    )"
unfolding dummy_dvd_iff by simp

lemma rd_mult_left0:
  shows "rd_mult 0 f = (0, 1)"
by simp

lemma rd_mult_right0:
  shows "rd_mult p 0 = (0, 1)"
by simp

lemma rd_mult_dvd:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "lp f dvd lp p"
  shows "rd_mult p f = (lc p / lc f, lp p divide lp f)"
using assms by simp

lemma rd_mult_ndvd:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "\<not> lp f dvd lp p"
  shows "rd_mult p f = rd_mult (tail p) f"
using assms by simp

lemma rd_left0:
  shows "rd 0 f = 0"
unfolding rd_def by (simp add: rd_mult_left0 Let_def del: rd_mult.simps, rule monom_mult_left0)

lemma rd_right0:
  shows "rd p 0 = p"
unfolding rd_def by (simp add: rd_mult_right0 Let_def del: rd_mult.simps, rule monom_mult_left0)

lemma rd_dvd:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "lp f dvd lp p"
  shows "rd p f = p - monom_mult (lc p / lc f) (lp p divide lp f) f"
unfolding rd_def by (simp add: rd_mult_dvd[OF assms] Let_def del: rd_mult.simps)

lemma rd_ndvd:
  assumes "p \<noteq> 0" and "f \<noteq> 0" and "\<not> lp f dvd lp p"
  shows "rd p f = (monom (lc p) (lp p)) + (rd (tail p) f)"
unfolding rd_def
by (simp add: rd_mult_ndvd[OF assms] Let_def del: rd_mult.simps, rule leading_monomial_tail, fact)

lemma rd_red_set:
  assumes "is_red {f} p"
  shows "red {f} p (rd p f)"
using assms
proof (induct p rule: mpoly_induct)
  assume "is_red {f} 0"
  from this irred_0[of "{f}"] show "red {f} 0 (rd 0 f)" by simp
next
  fix p
  assume "p \<noteq> 0" and IH: "is_red {f} (tail p) \<Longrightarrow> red {f} (tail p) (rd (tail p) f)"
    and red: "is_red {f} p"
  show "red {f} p (rd p f)"
  proof (cases "\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f dvd lp p")
    assume "\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f dvd lp p"
    hence "f \<noteq> 0" and "lp f dvd lp p" by auto
    have "red {f} p (p - monom_mult (lc p / lc f) (lp p divide lp f) f)"
      by (intro red_indI1, simp, fact+)
    thus ?thesis using rd_mult_dvd[OF \<open>p \<noteq> 0\<close> \<open>f \<noteq> 0\<close> \<open>lp f dvd lp p\<close>] unfolding rd_def by simp
  next
    assume "\<not> (\<exists>f\<in>{f}. f \<noteq> 0 \<and> lp f dvd lp p)"
    from this is_red_indE[OF red] have r: "is_red {f} (tail p)"
      and dis: "f = 0 \<or> \<not> (lp f dvd lp p)"
      by auto
    from is_red_singleton_not_0[OF r] have "f \<noteq> 0" .
    from dis this have "\<not> (lp f dvd lp p)" by simp
    from rd_ndvd[OF \<open>p \<noteq> 0\<close> \<open>f \<noteq> 0\<close> this] red_indI2[OF \<open>p \<noteq> 0\<close> IH[OF r]]
      show ?thesis by (simp only: rd_def ac_simps)
  qed
qed

lemma rd_irred_set:
  assumes "\<not> is_red {f} p"
  shows "rd p f = p"
using assms
proof (induct p rule: mpoly_induct, simp only: rd_left0)
  fix p
  assume "p \<noteq> 0" and IH: "\<not> is_red {f} (tail p) \<Longrightarrow> rd (tail p) f = tail p"
    and irred: "\<not> is_red {f} p"
  have "f \<in> {f}" by simp
  from irred is_red_indI1[OF this _ \<open>p \<noteq> 0\<close>] have dis: "f = 0 \<or> \<not> (lp f dvd lp p)" by auto
  show "rd p f = p"
  proof (cases "f = 0")
    case True
    thus ?thesis by (simp only: rd_right0)
  next
    case False
    hence ndvd: "\<not> (lp f dvd lp p)" using dis by simp
    from irred is_red_indI2[OF \<open>p \<noteq> 0\<close>, of "{f}"] have "\<not> is_red {f} (tail p)" by auto
    from IH[OF this] rd_ndvd[OF \<open>p \<noteq> 0\<close> False ndvd] leading_monomial_tail[OF \<open>p \<noteq> 0\<close>]
      show ?thesis by simp
  qed
qed

lemma rd_red:
  assumes "red_single p q f t"
  shows "\<exists>t. red_single p (rd p f) f t"
proof -
  have "is_red {f} p" by (intro is_redI, intro red_setI[of f], simp, fact)
  from red_setE[OF rd_red_set[OF this]] obtain t where "red_single p (rd p f) f t" by auto
  show ?thesis by (intro exI, fact)
qed

lemma rd_irred:
  assumes "\<And>q t. \<not> red_single p q f t"
  shows "rd p f = p"
proof (rule rd_irred_set, rule)
  assume "is_red {f} p"
  from is_redE[OF this] obtain q where "red {f} p q" .
  from red_setE[OF this] obtain t where "red_single p q f t" by auto
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

primrec rd_list::"('a, 'b::field) mpoly list \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" where
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

lemma rd_list_less_eq:
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
  from pideal_0 show "p - rd_list [] p \<in> pideal bs" by simp
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
      hence eq: "p - rd p a = monom_mult (coeff p (t * lp a) / lc a) t a"
        unfolding red_single_def by simp
      show "p - rd p a \<in> pideal bs" unfolding eq by (rule monom_mult_in_pideal, rule \<open>a \<in> bs\<close>)
    qed
  qed
qed

lemma rd_list_in_pideal:
  shows "p - (rd_list fs p) \<in> pideal (set fs)"
by (rule rd_list_in_pideal_ind, simp)

function trd::"('a, 'b::field) mpoly list \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly" where
  "trd fs p = (let q = rd_list fs p in (if q = p then p else trd fs q))"
by (pat_completeness, auto)
termination proof -
  let ?R = "(measure length) <*lex*> {(x, y). x \<prec>p y}"
  show ?thesis proof
    show "wf ?R"
    proof (rule, rule)
      from ord_p_wf show "wf {(x, y). x \<prec>p y}" unfolding wfP_def .
    qed
  next
    fix p fs and q::"('a, 'b) mpoly"
    assume q: "q = rd_list fs p" and neq: "q \<noteq> p"
    show "((fs, q), (fs, p)) \<in> ?R" unfolding in_lex_prod
    proof (rule disjI2, simp)
      from rd_list_less_eq[of fs p] q neq show "q \<prec>p p" by simp
    qed
  qed
qed

lemma trd_induct:
  assumes base: "\<And>fs p. rd_list fs p = p \<Longrightarrow> P fs p p"
    and ind: "\<And>fs p. rd_list fs p \<noteq> p \<Longrightarrow> P fs (rd_list fs p) (trd fs (rd_list fs p)) \<Longrightarrow>
              P fs p (trd fs (rd_list fs p))"
  shows "P fs p (trd fs p)"
proof (induct p rule: trd.induct)
  fix fs and p::"('a, 'b) mpoly"
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

lemma trd_red_rtrancl:
  shows "(red (set fs))\<^sup>*\<^sup>* p (trd fs p)"
proof (induct rule: trd_induct)
  fix fs and p::"('a, 'b) mpoly"
  assume "rd_list fs p = p"
  show "(red (set fs))\<^sup>*\<^sup>* p p" ..
next
  fix fs and p::"('a, 'b) mpoly"
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

lemma trd_irred:
  shows "\<not> is_red (set fs) (trd fs p)"
proof (induct rule: trd_induct)
  fix fs and p::"('a, 'b) mpoly"
  assume "rd_list fs p = p"
  from rd_list_fixpointD[OF this] show "\<not> is_red (set fs) p" .
next
  fix fs and p::"('a, 'b) mpoly"
  let ?x = "rd_list fs p"
  assume "\<not> is_red (set fs) (trd fs ?x)"
  show "\<not> is_red (set fs) (trd fs ?x)" by fact
qed

lemma trd_in_pideal:
  shows "(p - (trd fs p)) \<in> pideal (set fs)"
proof (induct p rule: trd_induct)
  fix fs and p::"('a, 'b) mpoly"
  from pideal_0 show "p - p \<in> pideal (set fs)" by simp
next
  fix fs and p::"('a, 'b) mpoly"
  assume IH: "(rd_list fs p - trd fs (rd_list fs p)) \<in> pideal (set fs)"
  from pideal_closed_plus[OF IH rd_list_in_pideal[of p fs]]
    show "p - trd fs (rd_list fs p) \<in> pideal (set fs)" by simp
qed

lemma pideal_closed_trd:
  assumes "p \<in> pideal (set fs)"
  shows "(trd fs p) \<in> pideal (set fs)"
using assms
proof (induct rule: trd_induct)
  fix fs and p::"('a, 'b) mpoly"
  assume "p \<in> pideal (set fs)"
  thus "p \<in> pideal (set fs)" .
next
  fix fs and p::"('a, 'b) mpoly"
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

definition red_supset::"('a, 'b::field) mpoly set \<Rightarrow> ('a, 'b) mpoly set \<Rightarrow> bool" (infixl "\<sqsupset>p" 50) where
  "red_supset as bs \<equiv> (\<exists>p. is_red as p \<and> \<not> is_red bs p) \<and> (\<forall>p. is_red bs p \<longrightarrow> is_red as p)"

lemma red_supsetD1:
  assumes "as \<sqsupset>p bs"
  obtains p where "is_red as p" and "\<not> is_red bs p"
proof -
  from assms have "\<exists>p. is_red as p \<and> \<not> is_red bs p" unfolding red_supset_def by simp
  from this obtain p where "is_red as p" and " \<not> is_red bs p" by auto
  thus ?thesis ..
qed

lemma red_supsetD2:
  assumes a1: "as \<sqsupset>p bs" and a2: "is_red bs p"
  shows "is_red as p"
proof -
  from assms have "\<forall>p. is_red bs p \<longrightarrow> is_red as p" unfolding red_supset_def by simp
  hence "is_red bs p \<longrightarrow> is_red as p" ..
  from a2 this show ?thesis by simp
qed

lemma red_supsetI[intro]:
  assumes "\<And>q. is_red bs q \<Longrightarrow> is_red as q" and "is_red as p" and "\<not> is_red bs p"
  shows "as \<sqsupset>p bs"
unfolding red_supset_def
proof (intro conjI, intro exI)
  from assms show "is_red as p \<and> \<not> is_red bs p" by simp
next
  show "\<forall>p. is_red bs p \<longrightarrow> is_red as p"
  proof (intro allI, intro impI)
    fix q
    assume "is_red bs q"
    from assms this show "is_red as q" by simp
  qed
qed

lemma red_supset_insertI:
  assumes "x \<noteq> 0" and "\<not> is_red as x"
  shows "(insert x as) \<sqsupset>p as"
proof
  fix q
  assume "is_red as q"
  thus "is_red (insert x as) q" unfolding is_red_alt
  proof
    fix a
    assume "red as q a"
    from red_unionI2[OF this, of "{x}"] have "red (insert x as) q a" by simp
    show "\<exists>qa. red (insert x as) q qa"
    proof
      show "red (insert x as) q a" by fact
    qed
  qed
next
  show "is_red (insert x as) x" unfolding is_red_alt
  proof
    from red_unionI1[OF red_self[OF \<open>x \<noteq> 0\<close>], of as] show "red (insert x as) x 0" by simp
  qed
next
  show "\<not> is_red as x" by fact
qed

lemma red_supset_transitive:
  assumes "A \<sqsupset>p B" and "B \<sqsupset>p C"
  shows "A \<sqsupset>p C"
proof -
  from red_supsetD1[OF assms(2)] obtain p where "is_red B p" and "\<not> is_red C p" .
  show ?thesis
  proof
    fix q
    assume "is_red C q"
    from red_supsetD2[OF assms(2) this] have "is_red B q" .
    from red_supsetD2[OF assms(1) this] show "is_red A q" .
  next
    from red_supsetD2[OF assms(1) \<open>is_red B p\<close>] show "is_red A p" .
  next
    show "\<not> is_red C p" by fact
  qed
qed

lemma red_supset_wf:
  shows "wfP (op \<sqsupset>p)"
proof (rule wfP_chain)
  show "\<not>(\<exists>f::(nat \<Rightarrow> (('a, 'b) mpoly set)). \<forall>i. f (Suc i) \<sqsupset>p f i)"
  proof (intro notI, erule exE)
    fix f::"nat \<Rightarrow> (('a, 'b) mpoly set)"
    assume a1: "\<forall>i. f (Suc i) \<sqsupset>p f i"
    have a1_trans: "\<And>i j. i < j \<longrightarrow> f j \<sqsupset>p f i"
    proof -
      fix i j::nat
      show "i < j \<longrightarrow> f j \<sqsupset>p f i"
      proof (induct j)
        show "i < 0 \<longrightarrow> f 0 \<sqsupset>p f i" by (intro impI, simp)
      next
        fix j::nat
        assume IH: "i < j \<longrightarrow> f j \<sqsupset>p f i"
        from a1 have supj: "f (Suc j) \<sqsupset>p f j" by simp
        show "i < Suc j \<longrightarrow> f (Suc j) \<sqsupset>p f i"
        proof
          assume "i < Suc j"
          hence "i < j \<or> i = j" by auto
          thus "f (Suc j) \<sqsupset>p f i"
          proof
            assume "i < j"
            from this IH have "f j \<sqsupset>p f i" by simp
            from red_supset_transitive[OF \<open>f (Suc j) \<sqsupset>p f j\<close> this] show ?thesis .
          next
            assume "i = j"
            thus ?thesis using supj by simp
          qed
        qed
      qed
    qed
    have a2: "\<And>i. \<exists>p \<in> f (Suc i). \<exists>q. is_red {p} q \<and> \<not> is_red (f i) q"
    proof -
      fix i::nat
      from a1 have "f (Suc i) \<sqsupset>p f i" ..
      from red_supsetD1[OF this] obtain q where
        red: "is_red (f (Suc i)) q" and irred: "\<not> is_red (f i) q" .
      from is_red_singletonI[OF red] obtain p where "p \<in> f (Suc i)" and "is_red {p} q" .
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
    def g \<equiv> "\<lambda>i::nat. (SOME p::('a, 'b) mpoly. p \<in> (f (Suc i)) \<and> (\<exists>q. is_red {p} q \<and> \<not> is_red (f i) q))"
    have a3: "\<And>i j. i < j \<Longrightarrow> \<not> lp (g i) dvd (lp (g j))"
    proof
      fix i j::nat
      assume "i < j" and dvd: "lp (g i) dvd lp (g j)"
      from a2[of j] obtain gj where "gj \<in> f (Suc j)" and "\<exists>q. is_red {gj} q \<and> \<not> is_red (f j) q" ..
      have "g j \<in> f (Suc j) \<and> (\<exists>q. is_red {g j} q \<and> \<not> is_red (f j) q)"
        unfolding g_def by (rule someI[of _ gj], intro conjI, fact+)
      hence "\<exists>q. is_red {g j} q \<and> \<not> is_red (f j) q" ..
      from this obtain q where redj: "is_red {g j} q" and "\<not> is_red (f j) q" by auto
      have a4: "\<not> is_red (f (Suc i)) q"
      proof -
        from \<open>i < j\<close> have "i + 1 < j \<or> i + 1 = j" by auto
        thus ?thesis
        proof
          assume "i + 1 < j"
          from red_supsetD2[OF a1_trans[rule_format, OF this], of q] \<open>\<not> is_red (f j) q\<close>
            show ?thesis by auto
        next
          assume "i + 1 = j"
          thus ?thesis using \<open>\<not> is_red (f j) q\<close> by simp
        qed
      qed
      from a2[of i] obtain gi where "gi \<in> f (Suc i)" and "\<exists>q. is_red {gi} q \<and> \<not> is_red (f i) q" ..
      have "g i \<in> f (Suc i) \<and> (\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q)"
        unfolding g_def by (rule someI[of _ gi], intro conjI, fact+)
      hence "g i \<in> f (i + 1)" and redi: "\<exists>q. is_red {g i} q \<and> \<not> is_red (f i) q" by simp_all
      have "\<not> is_red {g i} q"
      proof
        assume "is_red {g i} q"
        from is_red_singletonD[OF this \<open>g i \<in> f (i + 1)\<close>] a4 show False by simp
      qed
      have "g i \<noteq> 0"
      proof -
        from redi obtain q0 where "is_red {g i} q0" by auto
        from is_red_singleton_not_0[OF this] show ?thesis .
      qed
      from \<open>\<not> is_red {g i} q\<close> is_red_singleton_trans[OF redj dvd \<open>g i \<noteq> 0\<close>] show False by simp
    qed
    from dickson[of "lp o g"] obtain i j where "i < j" and "lp (g i) dvd lp (g j)" by auto
    from this a3[OF \<open>i < j\<close>] show False by simp
  qed
qed

subsubsection \<open>Function @{term gb}\<close>

definition trdsp::"('a, 'b::field) mpoly list \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly \<Rightarrow> ('a, 'b) mpoly"
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

text \<open>Functions @{term gb} and @{term gbaux} implement Buchberger's original algorithm for computing
  Gr\"obner bases. The efficiency of @{term gbaux} could be improved by incorporating Buchberger's
  criteria for avoiding useless S-polynomials.\<close>

function gbaux::"('a, 'b::field) mpoly list \<Rightarrow> (('a, 'b) mpoly * ('a, 'b) mpoly) list \<Rightarrow>
                  ('a, 'b) mpoly list" where
  gbaux_base: "gbaux B [] = B"|
  gbaux_rec: "gbaux B ((p, q) # r) =
    (let h = trdsp B p q in
      (if h = 0 then
        gbaux B r
      else
        gbaux (h # B) (up r B h)
      )
    )"
by pat_completeness auto
termination proof -
  let ?R = "{(a, b::('a, 'b) mpoly list). (set a) \<sqsupset>p (set b)} <*lex*> (measure length)"
  show ?thesis
  proof
    show "wf ?R"
    proof
      show "wf {(a, b::('a, 'b) mpoly list). (set a) \<sqsupset>p (set b)}"
      proof (rule wfI_min)
        fix x and Q::"('a, 'b) mpoly list set"
        assume "x \<in> Q"
        hence "set x \<in> set`Q" by simp
        from red_supset_wf have "wf {(p, q). p \<sqsupset>p q}" unfolding wfP_def .
        from wfE_min[OF this \<open>set x \<in> set`Q\<close>] obtain z where
          "z \<in> set`Q" and z_min: "\<And>y. (y, z) \<in> {(p, q). p \<sqsupset>p q} \<Longrightarrow> y \<notin> set`Q" by auto
        from \<open>z \<in> set`Q\<close> obtain z0 where "z0 \<in> Q" and z_def: "z = set z0" by auto
        show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> {(a, b). set a \<sqsupset>p set b} \<longrightarrow> y \<notin> Q"
        proof (intro bexI, intro allI)
          fix y
          show "(y, z0) \<in> {(a, b). set a \<sqsupset>p set b} \<longrightarrow> y \<notin> Q"
          proof
            assume "(y, z0) \<in> {(a, b). set a \<sqsupset>p set b}"
            hence "set y \<sqsupset>p z" using z_def by simp
            hence "(set y, z) \<in> {(p, q). p \<sqsupset>p q}" by simp
            from z_min[OF this] show "y \<notin> Q" by auto
          qed
        next
          show "z0 \<in> Q" by fact
        qed
      qed
    next
      show "wf (measure length)" ..
    qed
  next
    fix B p q r and h::"('a, 'b) mpoly"
    assume "h = trdsp B p q" and "h = 0"
    show "((B, r), (B, (p, q) # r)) \<in> ?R"
      unfolding in_lex_prod by (intro disjI2, intro conjI, simp_all)
  next
    fix B p q r and h::"('a, 'b) mpoly"
    assume h_def: "h = trdsp B p q" and "h \<noteq> 0"
    show "((h # B, (up r B h)), (B, (p, q) # r)) \<in> ?R" unfolding in_lex_prod
    proof (intro disjI1, simp)
      show "insert h (set B) \<sqsupset>p set B"
      proof (rule red_supset_insertI[OF \<open>h \<noteq> 0\<close>, of "set B"])
        from trd_irred[of B "(spoly p q)"] h_def show "\<not> is_red (set B) h"
          unfolding trdsp_def by simp
      qed
    qed
  qed
qed

definition gb::"('a, 'b::field) mpoly list \<Rightarrow> ('a, 'b) mpoly list" where "gb B \<equiv> gbaux B (pairs B)"

lemma gbaux_induct:
  assumes base: "\<And>bs. P bs [] bs"
    and ind1: "\<And>bs ps p q. trdsp bs p q = 0 \<Longrightarrow> P bs ps (gbaux bs ps) \<Longrightarrow>
                P bs ((p, q)#ps) (gbaux bs ps)"
    and ind2: "\<And>bs ps p q h. h = trdsp bs p q \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
                P (h#bs) (up ps bs h) (gbaux (h#bs) (up ps bs h)) \<Longrightarrow>
                P bs ((p, q)#ps) (gbaux (h#bs) (up ps bs h))"
  shows "P bs ps (gbaux bs ps)"
proof (induct bs ps rule: gbaux.induct)
  fix bs
  from base[of bs] show "P bs [] (gbaux bs [])" by simp
next
  fix bs ps p and q::"('a, 'b) mpoly"
  let ?h = "trdsp bs p q"
  assume IH1: "\<And>x. x = trdsp bs p q \<Longrightarrow> x = 0 \<Longrightarrow> P bs ps (gbaux bs ps)"
    and IH2: "\<And>x. x = trdsp bs p q \<Longrightarrow> x \<noteq> 0 \<Longrightarrow>
              P (x # bs) (up ps bs x) (gbaux (x # bs) (up ps bs x))"
  show "P bs ((p, q) # ps) (gbaux bs ((p, q) # ps))"
  proof (cases "?h = 0")
    case True
    from IH1[OF _ True] have "P bs ps (gbaux bs ps)" by simp
    from True ind1[OF True this] show ?thesis by simp
  next
    case False
    from IH2[OF _ False] have a: "P (?h#bs) (up ps bs ?h) (gbaux (?h#bs) (up ps bs ?h))" by simp
    from False gbaux_rec[of bs p q ps]
      have eq: "gbaux bs ((p, q) # ps) = gbaux (?h # bs) (up ps bs ?h)"
      by (simp del: gbaux.simps add: Let_def)
    from ind2[OF _ False a, of p q] eq show ?thesis by simp
  qed
qed

lemma gbaux_sublist:
  obtains cs::"('a, 'b::field) mpoly list" where "gbaux bs ps = cs @ bs"
proof (induct rule: gbaux_induct)
  fix bs::"('a, 'b) mpoly list"
  assume a1: "\<And>cs. bs = cs @ bs \<Longrightarrow> thesis"
  show thesis by (rule a1[of "[]"], simp)
next
  fix bs ps p and q::"('a, 'b) mpoly"
  assume "trdsp bs p q = 0"
    and a2: "(\<And>cs. gbaux bs ps = cs @ bs \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    and "\<And>cs. gbaux bs ps = cs @ bs \<Longrightarrow> thesis"
  show thesis by (rule a2, fact)
next
  fix bs ps p q and h::"('a, 'b) mpoly"
  assume h_def: "h = trdsp bs p q" and "h \<noteq> 0"
    and a3: "(\<And>cs. gbaux (h # bs) (up ps bs h) = cs @ h # bs \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    and a4: "\<And>cs. gbaux (h # bs) (up ps bs h) = cs @ bs \<Longrightarrow> thesis"
  show thesis
  proof (rule a3, rule a4)
    fix cs
    assume "gbaux (h # bs) (up ps bs h) = cs @ h # bs"
    thus "gbaux (h # bs) (up ps bs h) = (cs @ [h]) @ bs" by simp
  qed
qed

lemma gbaux_subset:
  shows "set bs \<subseteq> set (gbaux bs ps)"
proof -
  from gbaux_sublist[of bs ps] obtain cs where eq: "gbaux bs ps = cs @ bs" .
  from eq show ?thesis by simp
qed

definition nproc::"(('a, 'b) mpoly * ('a, 'b) mpoly) \<Rightarrow> ('a, 'b) mpoly list \<Rightarrow>
                    (('a, 'b) mpoly * ('a, 'b) mpoly) list \<Rightarrow> bool" where
  "nproc p as ps \<equiv> (p \<in> set ps) \<or> ((snd p, fst p) \<in> set ps) \<or> (fst p \<notin> set as) \<or> (snd p \<notin> set as)"

lemma nproc_alt:
  shows "nproc (a, b) as ps \<longleftrightarrow> ((a, b) \<in> set ps) \<or> ((b, a) \<in> set ps) \<or> (a \<notin> set as) \<or> (b \<notin> set as)"
unfolding nproc_def by auto

lemma nproc_nil:
  assumes major: "nproc (f, g) bs []"
    and a1: "f \<notin> set bs \<Longrightarrow> thesis"
    and a2: "g \<notin> set bs \<Longrightarrow> thesis"
  shows thesis
using major unfolding nproc_alt
proof
  assume "(f, g) \<in> set []"
  thus ?thesis by simp
next
  assume "(g, f) \<in> set [] \<or> f \<notin> set bs \<or> g \<notin> set bs"
  thus ?thesis
  proof
    assume "(g, f) \<in> set []"
    thus ?thesis by simp
  next
    assume "f \<notin> set bs \<or> g \<notin> set bs"
    thus ?thesis
    proof
      assume "f \<notin> set bs"
      from a1[OF this] show ?thesis .
    next
      assume "g \<notin> set bs"
      from a2[OF this] show ?thesis .
    qed
  qed
qed

lemma nproc_cons:
  assumes major: "nproc (f, g) bs ((p, q) # ps)"
    and a1: "f = p \<Longrightarrow> g = q \<Longrightarrow> thesis"
    and a2: "f = q \<Longrightarrow> g = p \<Longrightarrow> thesis"
    and a3: "nproc (f, g) bs ps \<Longrightarrow> thesis"
  shows thesis
using major unfolding nproc_alt
proof
  assume "(f, g) \<in> set ((p, q) # ps)"
  hence "(f, g) = (p, q) \<or> (f, g) \<in> set ps" by simp
  thus ?thesis
  proof
    assume "(f, g) = (p, q)"
    hence "f = p" and "g = q" by simp_all
    show ?thesis by (rule a1, fact, fact)
  next
    assume "(f, g) \<in> set ps"
    show ?thesis by (rule a3, simp only: nproc_alt, rule disjI1, fact)
  qed
next
  assume "(g, f) \<in> set ((p, q) # ps) \<or> f \<notin> set bs \<or> g \<notin> set bs"
  thus ?thesis
  proof
    assume "(g, f) \<in> set ((p, q) # ps)"
    hence "(g, f) = (p, q) \<or> (g, f) \<in> set ps" by simp
    thus ?thesis
    proof
      assume "(g, f) = (p, q)"
      hence "f = q" and "g = p" by simp_all
      show ?thesis by (rule a2, fact, fact)
    next
      assume "(g, f) \<in> set ps"
      show ?thesis by (rule a3, simp only: nproc_alt, rule disjI2, rule disjI1, fact)
    qed
  next
    assume "f \<notin> set bs \<or> g \<notin> set bs"
    show ?thesis by (rule a3, simp only: nproc_alt, rule disjI2, rule disjI2, fact)
  qed
qed

lemma nproc_pairs:
  assumes "f \<noteq> g" and "f \<in> set bs" and "g \<in> set bs"
  shows "nproc (f, g) bs (pairs bs)"
proof (rule in_pairsI[OF assms])
  assume "(f, g) \<in> set (pairs bs)"
  show ?thesis unfolding nproc_alt by (rule disjI1, fact)
next
  assume "(g, f) \<in> set (pairs bs)"
  show ?thesis unfolding nproc_alt by (rule disjI2, rule disjI1, fact)
qed

lemma nproc_up:
  assumes "f \<notin> set bs \<or> g \<notin> set bs"
  shows "nproc (f, g) (h # bs) (up ps bs h) \<or> (f = h \<and> g = h)"
proof (rule disjCI)
  assume "\<not> (f = h \<and> g = h)"
  hence dis: "f \<noteq> h \<or> g \<noteq> h" by simp
  show "nproc (f, g) (h # bs) (up ps bs h)"
  proof (cases "f = h")
    assume "f = h"
    hence "g \<noteq> h" using dis by simp
    show ?thesis
    proof (cases "g \<in> set bs")
      case True
      show ?thesis unfolding nproc_alt \<open>f = h\<close> by (rule disjI2, rule disjI1, rule in_upI2, fact)
    next
      case False
      show ?thesis unfolding nproc_alt
      proof ((rule disjI2)+, rule)
        assume "g \<in> set (h # bs)"
        hence "g = h \<or> g \<in> set bs" by simp
        from this \<open>g \<noteq> h\<close> False show False by simp
      qed
    qed
  next
    assume "f \<noteq> h"
    show ?thesis
    proof (cases "g = h")
      assume "g = h"
      show ?thesis
      proof (cases "f \<in> set bs")
        case True
        show ?thesis unfolding nproc_alt \<open>g = h\<close> by (rule disjI1, rule in_upI2, fact)
      next
        case False
        show ?thesis unfolding nproc_alt
        proof (rule disjI2, rule disjI2, rule disjI1, rule)
          assume "f \<in> set (h # bs)"
          hence "f = h \<or> f \<in> set bs" by simp
          from this \<open>f \<noteq> h\<close> False show False by simp
        qed
      qed
    next
      assume "g \<noteq> h"
      from assms show ?thesis
      proof
        assume "f \<notin> set bs"
        show ?thesis unfolding nproc_alt
        proof (rule disjI2, rule disjI2, rule disjI1, rule)
          assume "f \<in> set (h # bs)"
          hence "f = h \<or> f \<in> set bs" by simp
          from this \<open>f \<noteq> h\<close> \<open>f \<notin> set bs\<close> show False by simp
        qed
      next
        assume "g \<notin> set bs"
        show ?thesis unfolding nproc_alt
        proof ((rule disjI2)+, rule)
          assume "g \<in> set (h # bs)"
          hence "g = h \<or> g \<in> set bs" by simp
          from this \<open>g \<noteq> h\<close> \<open>g \<notin> set bs\<close> show False by simp
        qed
      qed
    qed
  qed
qed

lemma gbaux_connectible:
  assumes "f \<in> set (gbaux bs ps)" and "g \<in> set (gbaux bs ps)" and "nproc (f, g) bs ps"
  shows "(red (set (gbaux bs ps)))\<^sup>*\<^sup>* (spoly f g) 0"
using assms
proof (induct rule: gbaux_induct)
  fix bs
  assume "f \<in> set bs" and "g \<in> set bs" and nproc: "nproc (f, g) bs []"
  show "(red (set bs))\<^sup>*\<^sup>* (spoly f g) 0"
  proof (rule nproc_nil[OF nproc])
    assume "f \<notin> set bs"
    thus ?thesis using \<open>f \<in> set bs\<close> by simp
  next
    assume "g \<notin> set bs"
    thus ?thesis using \<open>g \<in> set bs\<close> by simp
  qed

next
  fix bs ps p and q::"('a, 'b) mpoly"
  assume h0: "trdsp bs p q = 0"
    and IH: "f \<in> set (gbaux bs ps) \<Longrightarrow> g \<in> set (gbaux bs ps) \<Longrightarrow> nproc (f, g) bs ps \<Longrightarrow>
              (red (set (gbaux bs ps)))\<^sup>*\<^sup>* (spoly f g) 0"
    and f_in: "f \<in> set (gbaux bs ps)"
    and g_in: "g \<in> set (gbaux bs ps)"
    and nproc: "nproc (f, g) bs ((p, q) # ps)"
  
  from h0 trd_red_rtrancl[of bs "spoly p q"] have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) 0"
    unfolding trdsp_def by simp
  from red_rtrancl_subset[OF this gbaux_subset, of ps]
    have pq: "(red (set (gbaux bs ps)))\<^sup>*\<^sup>* (spoly p q) 0" .
  from red_rtrancl_uminus[OF this] spoly_exchange[of q p]
    have qp: "(red (set (gbaux bs ps)))\<^sup>*\<^sup>* (spoly q p) 0" by simp
  
  show "(red (set (gbaux bs ps)))\<^sup>*\<^sup>* (spoly f g) 0"
  proof (rule nproc_cons[OF nproc])
    assume "f = p" and "g = q"
    thus ?thesis using pq by simp
  next
    assume "f = q" and "g = p"
    thus ?thesis using qp by simp
  next
    assume "nproc (f, g) bs ps"
    from IH[OF f_in g_in this] show ?thesis .
  qed

next
  fix bs ps p q and h::"('a, 'b) mpoly"
  assume h_def: "h = trdsp bs p q" and "h \<noteq> 0"
    and IH: "f \<in> set (gbaux (h # bs) (up ps bs h)) \<Longrightarrow>
              g \<in> set (gbaux (h # bs) (up ps bs h)) \<Longrightarrow> nproc (f, g) (h # bs) (up ps bs h) \<Longrightarrow>
             (red (set (gbaux (h # bs) (up ps bs h))))\<^sup>*\<^sup>* (spoly f g) 0"
    and f_in: "f \<in> set (gbaux (h # bs) (up ps bs h))"
    and g_in: "g \<in> set (gbaux (h # bs) (up ps bs h))"
    and nproc: "nproc (f, g) bs ((p, q) # ps)"

  have "set bs \<subseteq> set (h # bs)" by auto
  have "{h} \<subseteq> set (h # bs)" by simp
  from trd_red_rtrancl[of bs "spoly p q"] have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) h"
    unfolding h_def trdsp_def .
  from red_rtrancl_subset[OF this \<open>set bs \<subseteq> set (h # bs)\<close>]
    have r1: "(red (set (h # bs)))\<^sup>*\<^sup>* (spoly p q) h" .
  from red_self[OF \<open>h \<noteq> 0\<close>] have "(red {h})\<^sup>*\<^sup>* h 0" ..
  from red_rtrancl_subset[OF this \<open>{h} \<subseteq> set (h # bs)\<close>] have r2: "(red (set (h # bs)))\<^sup>*\<^sup>* h 0" .
  from red_rtrancl_subset[OF rtranclp_trans[OF r1 r2] gbaux_subset, of "up ps bs h"]
    have pq: "(red (set (gbaux (h # bs) (up ps bs h))))\<^sup>*\<^sup>* (spoly p q) 0" .
  from red_rtrancl_uminus[OF this] spoly_exchange[of q p]
    have qp: "(red (set (gbaux (h # bs) (up ps bs h))))\<^sup>*\<^sup>* (spoly q p) 0" by simp

  show "(red (set (gbaux (h # bs) (up ps bs h))))\<^sup>*\<^sup>* (spoly f g) 0"
  proof (rule nproc_cons[OF nproc])
    assume "f = p" and "g = q"
    thus ?thesis using pq by simp
  next
    assume "f = q" and "g = p"
    thus ?thesis using qp by simp
  next
    assume "nproc (f, g) bs ps"
    thus ?thesis unfolding nproc_alt
    proof
      assume "(f, g) \<in> set ps"
      show ?thesis
      proof (rule IH[OF f_in g_in])
        show "nproc (f, g) (h # bs) (up ps bs h)"
          unfolding nproc_alt by (rule disjI1, rule in_upI1, fact)
      qed
    next
      assume "(g, f) \<in> set ps \<or> f \<notin> set bs \<or> g \<notin> set bs"
      thus ?thesis
      proof
        assume "(g, f) \<in> set ps"
        show ?thesis
        proof (rule IH[OF f_in g_in])
          show "nproc (f, g) (h # bs) (up ps bs h)"
            unfolding nproc_alt by (rule disjI2, rule disjI1, rule in_upI1, fact)
        qed
      next
        assume "f \<notin> set bs \<or> g \<notin> set bs"
        from nproc_up[OF this] show ?thesis
        proof
          assume "f = h \<and> g = h"
          hence "spoly f g = 0" unfolding spoly_def by simp
          thus ?thesis by simp
        next
          assume "nproc (f, g) (h # bs) (up ps bs h)"
          from IH[OF f_in g_in this] show ?thesis .
        qed
      qed
    qed
  qed
qed

lemma gbaux_pideal:
  assumes "\<And>a b. (a, b) \<in> set ps \<Longrightarrow> (a \<in> set bs \<and> b \<in> set bs)"
  shows "pideal (set (gbaux bs ps)) = pideal (set bs)"
using assms
proof (induction rule: gbaux_induct)
  fix bs::"('a, 'b) mpoly list"
  show "pideal (set bs) = pideal (set bs)" ..
next
  fix bs ps p and q::"('a, 'b) mpoly"
  assume IH: "(\<And>a b. (a, b) \<in> set ps \<Longrightarrow> a \<in> set bs \<and> b \<in> set bs) \<Longrightarrow>
                pideal (set (gbaux bs ps)) = pideal (set bs)"
    and ps_sub: "\<And>a b. (a, b) \<in> set ((p, q) # ps) \<Longrightarrow> a \<in> set bs \<and> b \<in> set bs"
  show "pideal (set (gbaux bs ps)) = pideal (set bs)"
  proof (rule IH)
    fix a b
    assume pair_in: "(a, b) \<in> set ps"
    show "a \<in> set bs \<and> b \<in> set bs"
    proof (rule ps_sub)
      from pair_in show "(a, b) \<in> set ((p, q) # ps)" by simp
    qed
  qed
next
  fix bs ps p q and h::"('a, 'b) mpoly"
  assume h_def: "h = trdsp bs p q"
    and IH: "(\<And>a b. (a, b) \<in> set (up ps bs h) \<Longrightarrow> a \<in> set (h # bs) \<and> b \<in> set (h # bs)) \<Longrightarrow>
            pideal (set (gbaux (h # bs) (up ps bs h))) = pideal (set (h # bs))"
    and ps_sub: "\<And>a b. (a, b) \<in> set ((p, q) # ps) \<Longrightarrow> a \<in> set bs \<and> b \<in> set bs"
  have "(p, q) \<in> set ((p, q) # ps)" by simp
  from ps_sub[OF this] have "p \<in> set bs" and "q \<in> set bs" by simp_all
  have eq: "pideal (insert h (set bs)) = pideal (set bs)"
    unfolding h_def by (rule pideal_insert, rule trdsp_in_pideal, fact+)
  have "pideal (set (gbaux (h # bs) (up ps bs h))) = pideal (set (h # bs))"
  proof (rule IH)
    fix a b
    assume "(a, b) \<in> set (up ps bs h)"
    thus "a \<in> set (h # bs) \<and> b \<in> set (h # bs)"
    proof (rule in_upE)
      assume "(a, b) \<in> set ps"
      hence "(a, b) \<in> set ((p, q) # ps)" by simp
      from ps_sub[OF this] have "a \<in> set bs" and "b \<in> set bs" by simp_all
      show ?thesis
      proof
        from \<open>a \<in> set bs\<close> show "a \<in> set (h # bs)" by simp
      next
        from \<open>b \<in> set bs\<close> show "b \<in> set (h # bs)" by simp
      qed
    next
      assume "b = h \<and> a \<in> set bs"
      hence "b = h" and "a \<in> set bs" by simp_all
      show ?thesis
      proof
        from \<open>a \<in> set bs\<close> show "a \<in> set (h # bs)" by simp
      next
        from \<open>b = h\<close> show "b \<in> set (h # bs)" by simp
      qed
    qed
  qed
  from this eq show "pideal (set (gbaux (h # bs) (up ps bs h))) = pideal (set bs)" by simp
qed

theorem gb_isGB:
  shows "is_Groebner_basis (set (gb bs))"
proof (rule Buchberger_criterion)
  fix p q
  assume p_in: "p \<in> set (gb bs)" and q_in: "q \<in> set (gb bs)"
  from p_in have p_in_2: "p \<in> set (gbaux bs (pairs bs))" unfolding gb_def .
  from q_in have q_in_2: "q \<in> set (gbaux bs (pairs bs))" unfolding gb_def .
  show "(red (set (gb bs)))\<^sup>*\<^sup>* (spoly p q) 0"
  proof (cases "p = q")
    assume "p = q"
    from this spoly_same[of q] show ?thesis by simp
  next
    assume "p \<noteq> q"
    show ?thesis unfolding gb_def
    proof (rule gbaux_connectible[OF p_in_2 q_in_2], cases "p \<in> set bs \<and> q \<in> set bs")
      case True
      hence "p \<in> set bs" and "q \<in> set bs" by simp_all
      from nproc_pairs[OF \<open>p \<noteq> q\<close> this] show "nproc (p, q) bs (pairs bs)" .
    next
      case False
      hence "p \<notin> set bs \<or> q \<notin> set bs" by simp
      show "nproc (p, q) bs (pairs bs)" unfolding nproc_alt by (rule disjI2, rule disjI2, fact)
    qed
  qed
qed

theorem gb_pideal:
  shows "pideal (set (gb bs)) = pideal (set bs)"
unfolding gb_def
proof (rule gbaux_pideal)
  fix a b
  assume pair_in: "(a, b) \<in> set (pairs bs)"
  show "a \<in> set bs \<and> b \<in> set bs" by (rule, rule in_pairsD1[OF pair_in], rule in_pairsD2[OF pair_in])
qed

text \<open>The following theorem yields a criterion for deciding whether a given polynomial belongs to
  the ideal generated by a given list of polynomials. Note again that @{term "pideal (set bs)"}
  coincides with the ideal (in @{typ "('a, 'b) mpoly"}) generated by @{term "set bs"}!\<close>

theorem in_pideal_gb:
  shows "p \<in> pideal (set bs) \<longleftrightarrow> (trd (gb bs) p) = 0"
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

end (* ordered_powerprod *)

end (* theory *)
