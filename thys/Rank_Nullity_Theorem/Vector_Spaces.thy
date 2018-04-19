(* Title:   Modules.thy
   Author:  Amine Chaieb, University of Cambridge
   Author:  Jose Divasón <jose.divasonm at unirioja.es>
   Author:  Jesús Aransay <jesus-maria.aransay at unirioja.es>
   Author:  Johannes Hölzl, VU Amsterdam
*)

section \<open>Vector Spaces\<close>

theory Vector_Spaces
  imports Modules
begin

lemma ordLeq3_finite_infinite:
  assumes A: "finite A" and B: "infinite B" shows "ordLeq3 (card_of A) (card_of B)"
proof -
  have \<open>ordLeq3 (card_of A) (card_of B) \<or> ordLeq3 (card_of B) (card_of A)\<close>
    by (intro ordLeq_total card_of_Well_order)
  moreover have "\<not> ordLeq3 (card_of B) (card_of A)"
    using B A card_of_ordLeq_finite[of B A] by auto
  ultimately show ?thesis by auto
qed

locale vector_space = module scale for scale :: "'a::field \<Rightarrow> 'b \<Rightarrow> 'b :: ab_group_add" (infixr "*s" 75)
begin

lemma dependent_def: "dependent P \<longleftrightarrow> (\<exists>a \<in> P. a \<in> span (P - {a}))"
  unfolding dependent_explicit
proof safe
  fix a assume aP: "a \<in> P" and "a \<in> span (P - {a})"
  then obtain a S u
    where aP: "a \<in> P" and fS: "finite S" and SP: "S \<subseteq> P" "a \<notin> S" and ua: "(\<Sum>v\<in>S. u v *s v) = a"
    unfolding span_explicit by blast
  let ?S = "insert a S"
  let ?u = "\<lambda>y. if y = a then - 1 else u y"
  from fS SP have "(\<Sum>v\<in>?S. ?u v *s v) = 0"
    by (simp add: if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases field_simps Diff_eq[symmetric] ua)
  moreover have "finite ?S" "?S \<subseteq> P" "a \<in> ?S" "?u a \<noteq> 0"
    using fS SP aP by auto
  ultimately show "\<exists>t u. finite t \<and> t \<subseteq> P \<and> (\<Sum>v\<in>t. u v *s v) = 0 \<and> (\<exists>v\<in>t. u v \<noteq> 0)" by fast
next
  fix S u v
  assume fS: "finite S" and SP: "S \<subseteq> P" and vS: "v \<in> S"
   and uv: "u v \<noteq> 0" and u: "(\<Sum>v\<in>S. u v *s v) = 0"
  let ?a = v
  let ?S = "S - {v}"
  let ?u = "\<lambda>i. (- u i) / u v"
  have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P"
    using fS SP vS by auto
  have "(\<Sum>v\<in>?S. ?u v *s v) = (\<Sum>v\<in>S. (- (inverse (u ?a))) *s (u v *s v)) - ?u v *s v"
    using fS vS uv by (simp add: sum_diff1 field_simps)
  also have "\<dots> = ?a"
    unfolding scale_sum_right[symmetric] u using uv by simp
  finally have "(\<Sum>v\<in>?S. ?u v *s v) = ?a" .
  with th0 show "\<exists>a \<in> P. a \<in> span (P - {a})"
    unfolding span_explicit by (auto intro!: bexI[where x="?a"] exI[where x="?S"] exI[where x="?u"])
qed

lemma in_span_insert:
  assumes a: "a \<in> span (insert b S)"
    and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof -
  from span_breakdown[of b "insert b S" a, OF insertI1 a]
  obtain k where k: "a - k *s b \<in> span (S - {b})" by auto
  have "k \<noteq> 0"
  proof
    assume "k = 0"
    with k span_mono[of "S - {b}" S] have "a \<in> span S" by auto
    with na show False by blast  
  qed
  then have eq: "b = (1/k) *s a - (1/k) *s (a - k *s b)"
    by (simp add: algebra_simps)

  from k have "(1/k) *s (a - k *s b) \<in> span (S - {b})"
    by (rule span_scale)
  also have "... \<subseteq> span (insert a S)"
    by (rule span_mono) auto
  finally show ?thesis
    using k by (subst eq) (blast intro: span_diff span_scale span_base)
qed

lemma dependent_insertD: assumes a: "a \<notin> span S" and S: "dependent (insert a S)" shows "dependent S"
proof -
  have "a \<notin> S" using a by (auto dest: span_base)
  obtain b where b: "b = a \<or> b \<in> S" "b \<in> span (insert a S - {b})"
    using S unfolding dependent_def by blast
  have "b \<noteq> a" "b \<in> S"
    using b \<open>a \<notin> S\<close> a by auto
  with b have *: "b \<in> span (insert a (S - {b}))"
    by (auto simp: insert_Diff_if)
  show "dependent S"
  proof cases
    assume "b \<in> span (S - {b})" with \<open>b \<in> S\<close> show ?thesis
      by (auto simp add: dependent_def)
  next
    assume "b \<notin> span (S - {b})"
    with * have "a \<in> span (insert b (S - {b}))" by (rule in_span_insert)
    with a show ?thesis
      using \<open>b \<in> S\<close> by (auto simp: insert_absorb)
  qed
qed

lemma independent_insertI: "a \<notin> span S \<Longrightarrow> independent S \<Longrightarrow> independent (insert a S)"
  by (auto dest: dependent_insertD)

lemma independent_insert:
  "independent (insert a S) \<longleftrightarrow> (if a \<in> S then independent S else independent S \<and> a \<notin> span S)"
proof -
  have "a \<notin> S \<Longrightarrow> a \<in> span S \<Longrightarrow> dependent (insert a S)"
    by (auto simp: dependent_def)
  then show ?thesis
    by (auto intro: dependent_mono simp: independent_insertI)
qed

lemma maximal_independent_subset_extend:
  assumes "S \<subseteq> V" "independent S"
  shows "\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
proof -
  let ?C = "{B. S \<subseteq> B \<and> independent B \<and> B \<subseteq> V}"
  have "\<exists>M\<in>?C. \<forall>X\<in>?C. M \<subseteq> X \<longrightarrow> X = M"
  proof (rule subset_Zorn)
    fix C :: "'b set set" assume "subset.chain ?C C"
    then have C: "\<And>c. c \<in> C \<Longrightarrow> c \<subseteq> V" "\<And>c. c \<in> C \<Longrightarrow> S \<subseteq> c" "\<And>c. c \<in> C \<Longrightarrow> independent c"
      "\<And>c d. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> c \<subseteq> d \<or> d \<subseteq> c"
      unfolding subset.chain_def by blast+

    show "\<exists>U\<in>?C. \<forall>X\<in>C. X \<subseteq> U"
    proof cases
      assume "C = {}" with assms show ?thesis
        by (auto intro!: exI[of _ S])
    next
      assume "C \<noteq> {}"
      with C(2) have "S \<subseteq> \<Union>C"
        by auto
      moreover have "independent (\<Union>C)"
        by (intro independent_Union_directed C)
      moreover have "\<Union>C \<subseteq> V"
        using C by auto
      ultimately show ?thesis
        by auto
    qed
  qed
  then obtain B where B: "independent B" "B \<subseteq> V" "S \<subseteq> B"
    and max: "\<And>S. independent S \<Longrightarrow> S \<subseteq> V \<Longrightarrow> B \<subseteq> S \<Longrightarrow> S = B"
    by auto
  moreover
  { assume "\<not> V \<subseteq> span B"
    then obtain v where "v \<in> V" "v \<notin> span B"
      by auto
    with B have "independent (insert v B)" by (auto intro: dependent_insertD)
    from max[OF this] \<open>v \<in> V\<close> \<open>B \<subseteq> V\<close>
    have "v \<in> B"
      by auto
    with \<open>v \<notin> span B\<close> have False
      by (auto intro: span_base) }
  ultimately show ?thesis
    by (auto intro!: exI[of _ B])
qed

lemma maximal_independent_subset: "\<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}"] empty_subsetI independent_empty)

text \<open>Extends a basis from B to a basis of the entire space.\<close>
definition extend_basis :: "'b set \<Rightarrow> 'b set"
  where "extend_basis B = (SOME B'. B \<subseteq> B' \<and> independent B' \<and> span B' = UNIV)"

lemma
  assumes B: "independent B"
  shows extend_basis_superset: "B \<subseteq> extend_basis B"
    and independent_extend_basis: "independent (extend_basis B)"
    and span_extend_basis[simp]: "span (extend_basis B) = UNIV"
proof -
  define p where "p B' \<equiv> B \<subseteq> B' \<and> independent B' \<and> span B' = UNIV" for B'
  obtain B' where "p B'"
    using maximal_independent_subset_extend[OF subset_UNIV B] by (auto simp: p_def)
  then have "p (extend_basis B)"
    unfolding extend_basis_def p_def[symmetric] by (rule someI)
  then show "B \<subseteq> extend_basis B" "independent (extend_basis B)" "span (extend_basis B) = UNIV"
    by (auto simp: p_def)
qed

lemma in_span_delete:
  assumes a: "a \<in> span S"
    and na: "a \<notin> span (S - {b})"
  shows "b \<in> span (insert a (S - {b}))"
  apply (rule in_span_insert)
  apply (rule set_rev_mp)
  apply (rule a)
  apply (rule span_mono)
  apply blast
  apply (rule na)
  done

lemma span_redundant: "x \<in> span S \<Longrightarrow> span (insert x S) = span S"
  unfolding span_def by (rule hull_redundant)

lemma span_trans: "x \<in> span S \<Longrightarrow> y \<in> span (insert x S) \<Longrightarrow> y \<in> span S"
  by (simp only: span_redundant)

lemma span_insert_0[simp]: "span (insert 0 S) = span S"
  by (metis span_zero span_redundant)

lemma exchange_lemma:
  assumes f: "finite t"
  and i: "independent s"
  and sp: "s \<subseteq> span t"
  shows "\<exists>t'. card t' = card t \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  using f i sp
proof (induct "card (t - s)" arbitrary: s t rule: less_induct)
  case less
  note ft = `finite t` and s = `independent s` and sp = `s \<subseteq> span t`
  let ?P = "\<lambda>t'. card t' = card t \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  let ?ths = "\<exists>t'. ?P t'"

  {
    assume st: "t \<subseteq> s"
    from spanning_subset_independent[OF st s sp] st ft span_mono[OF st]
    have ?ths by (auto intro: span_base)
  }
  moreover
  {
    assume st:"\<not> t \<subseteq> s"
    from st obtain b where b: "b \<in> t" "b \<notin> s"
      by blast
    from b have "t - {b} - s \<subset> t - s"
      by blast
    then have cardlt: "card (t - {b} - s) < card (t - s)"
      using ft by (auto intro: psubset_card_mono)
    from b ft have ct0: "card t \<noteq> 0"
      by auto
    have ?ths
    proof cases
      assume stb: "s \<subseteq> span (t - {b})"
      from ft have ftb: "finite (t - {b})"
        by auto
      from less(1)[OF cardlt ftb s stb]
      obtain u where u: "card u = card (t - {b})" "s \<subseteq> u" "u \<subseteq> s \<union> (t - {b})" "s \<subseteq> span u"
        and fu: "finite u" by blast
      let ?w = "insert b u"
      have th0: "s \<subseteq> insert b u"
        using u by blast
      from u(3) b have "u \<subseteq> s \<union> t"
        by blast
      then have th1: "insert b u \<subseteq> s \<union> t"
        using u b by blast
      have bu: "b \<notin> u"
        using b u by blast
      from u(1) ft b have "card u = (card t - 1)"
        by auto
      then have th2: "card (insert b u) = card t"
        using card_insert_disjoint[OF fu bu] ct0 by auto
      from u(4) have "s \<subseteq> span u" .
      also have "\<dots> \<subseteq> span (insert b u)"
        by (rule span_mono) blast
      finally have th3: "s \<subseteq> span (insert b u)" .
      from th0 th1 th2 th3 fu have th: "?P ?w"
        by blast
      from th show ?thesis by blast
    next
      assume stb: "\<not> s \<subseteq> span (t - {b})"
      from stb obtain a where a: "a \<in> s" "a \<notin> span (t - {b})"
        by blast
      have ab: "a \<noteq> b"
        using a b by blast
      have at: "a \<notin> t"
        using a ab span_base[of a "t- {b}"] by auto
      have mlt: "card ((insert a (t - {b})) - s) < card (t - s)"
        using cardlt ft a b by auto
      have ft': "finite (insert a (t - {b}))"
        using ft by auto
      {
        fix x
        assume xs: "x \<in> s"
        have t: "t \<subseteq> insert b (insert a (t - {b}))"
          using b by auto
        have bs: "b \<in> span (insert a (t - {b}))"
          apply (rule in_span_delete)
          using a sp unfolding subset_eq
          apply auto
          done
        from xs sp have "x \<in> span t"
          by blast
        with span_mono[OF t] have x: "x \<in> span (insert b (insert a (t - {b})))" ..
        from span_trans[OF bs x] have "x \<in> span (insert a (t - {b}))" .
      }
      then have sp': "s \<subseteq> span (insert a (t - {b}))"
        by blast
      from less(1)[OF mlt ft' s sp'] obtain u where u:
        "card u = card (insert a (t - {b}))"
        "finite u" "s \<subseteq> u" "u \<subseteq> s \<union> insert a (t - {b})"
        "s \<subseteq> span u" by blast
      from u a b ft at ct0 have "?P u"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?ths by blast
qed

lemma independent_span_bound:
  assumes f: "finite t"
    and i: "independent s"
    and sp: "s \<subseteq> span t"
  shows "finite s \<and> card s \<le> card t"
  by (metis exchange_lemma[OF f i sp] finite_subset card_mono)

(*The following lemmas don't appear in the library, but they are useful in my development.*)
lemma independent_explicit:
  "independent A \<longleftrightarrow> (\<forall>S \<subseteq> A. finite S \<longrightarrow> (\<forall>u. (\<Sum>v\<in>S. u v *s v) = 0 \<longrightarrow> (\<forall>v\<in>S. u v = 0)))"
  unfolding dependent_explicit [of A] by (simp add: disj_not2)

lemma independent_if_scalars_zero:
  assumes fin_A: "finite A"
  and sum: "\<And>f x. (\<Sum>x\<in>A. f x *s x) = 0 \<Longrightarrow> x \<in> A \<Longrightarrow> f x = 0"
  shows "independent A"
proof (unfold independent_explicit, clarify)
  fix S v and u :: "'b \<Rightarrow> 'a"
  assume S: "S \<subseteq> A" and v: "v \<in> S"
  let ?g = "\<lambda>x. if x \<in> S then u x else 0"
  have "(\<Sum>v\<in>A. ?g v *s v) = (\<Sum>v\<in>S. u v *s v)"
    using S fin_A by (auto intro!: sum.mono_neutral_cong_right)
  also assume "(\<Sum>v\<in>S. u v *s v) = 0"
  finally have "?g v = 0" using v S sum by force
  thus "u v = 0"  unfolding if_P[OF v] .
qed

lemma bij_if_span_eq_span_bases:
  assumes B: "independent B" and C: "independent C"
    and eq: "span B = span C"
  shows "\<exists>f. bij_betw f B C"
proof cases
  assume "finite B \<or> finite C"
  then have "finite B \<and> finite C \<and> card C = card B"
    using independent_span_bound[of B C] independent_span_bound[of C B] assms
      span_superset[of B] span_superset[of C]
    by auto
  then show ?thesis
    by (auto intro!: finite_same_card_bij)
next
  assume "\<not> (finite B \<or> finite C)"
  then have "infinite B" "infinite C" by auto
  { fix B C assume  B: "independent B" and C: "independent C" and "infinite B" "infinite C" and eq: "span B = span C"
    let ?R = "representation B" and ?R' = "representation C" let ?U = "\<lambda>c. {v. ?R c v \<noteq> 0}"
    have in_span_C [simp, intro]: \<open>b \<in> B \<Longrightarrow> b \<in> span C\<close> for b unfolding eq[symmetric] by (rule span_base) 
    have in_span_B [simp, intro]: \<open>c \<in> C \<Longrightarrow> c \<in> span B\<close> for c unfolding eq by (rule span_base) 
    have \<open>B \<subseteq> (\<Union>c\<in>C. ?U c)\<close>
    proof
      fix b assume \<open>b \<in> B\<close>
      have \<open>b \<in> span C\<close>
        using \<open>b \<in> B\<close> unfolding eq[symmetric] by (rule span_base)
      have \<open>(\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. (?R' b v * ?R v w) *s w) =
          (\<Sum>v | ?R' b v \<noteq> 0. ?R' b v *s (\<Sum>w | ?R v w \<noteq> 0. ?R v w *s w))\<close>
        by (simp add: scale_sum_right)
      also have \<open>\<dots> = (\<Sum>v | ?R' b v \<noteq> 0. ?R' b v *s v)\<close>
        by (auto simp: sum_nonzero_representation_eq B eq span_base representation_ne_zero)
      also have \<open>\<dots> = b\<close>
        by (rule sum_nonzero_representation_eq[OF C \<open>b \<in> span C\<close>])
      finally have "?R b b = ?R (\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. (?R' b v * ?R v w) *s w) b"
        by simp
      also have \<open>\<dots> = (\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. ?R' b v * ?R v w * ?R w b)\<close>
        using B \<open>b \<in> B\<close>
        apply (subst representation_sum[OF B])
         apply (fastforce intro: span_sum span_scale span_base representation_ne_zero)
        apply (rule sum.cong[OF refl])
        apply (subst representation_sum[OF B])
         apply (simp add: span_sum span_scale span_base representation_ne_zero)
        apply (simp add: representation_scale[OF B] span_base representation_ne_zero)
        done
      finally have "(\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. ?R' b v * ?R v w * ?R w b) \<noteq> 0"
        using representation_basis[OF B \<open>b \<in> B\<close>] by auto
      then obtain v w where bv: "?R' b v \<noteq> 0" and vw: "?R v w \<noteq> 0" and "?R' b v * ?R v w * ?R w b \<noteq> 0"
        by (blast elim: sum.not_neutral_contains_not_neutral)
      with representation_basis[OF B, of w] vw[THEN representation_ne_zero]
      have \<open>?R' b v \<noteq> 0\<close> \<open>?R v b \<noteq> 0\<close> by (auto split: if_splits)
      then show \<open>b \<in> (\<Union>c\<in>C. ?U c)\<close>
        by (auto dest: representation_ne_zero)
    qed
    then have B_eq: \<open>B = (\<Union>c\<in>C. ?U c)\<close>
      by (auto intro: span_base representation_ne_zero eq)
    have "ordLeq3 (card_of B) (card_of C)"
    proof (subst B_eq, rule card_of_UNION_ordLeq_infinite[OF \<open>infinite C\<close>])
      show "ordLeq3 (card_of C) (card_of C)"
        by (intro ordLeq_refl card_of_Card_order)
      show "\<forall>c\<in>C. ordLeq3 (card_of {v. representation B c v \<noteq> 0}) (card_of C)"
        by (intro ballI ordLeq3_finite_infinite \<open>infinite C\<close> finite_representation)
    qed }
  from this[of B C] this[of C B] B C eq \<open>infinite C\<close> \<open>infinite B\<close>
  show ?thesis by (auto simp add: ordIso_iff_ordLeq card_of_ordIso)
qed

definition dim :: "'b set \<Rightarrow> nat"
  where "dim V = card (SOME b. independent b \<and> span b = span V)"

lemma dim_eq_card:
  assumes BV: "span B = span V" and B: "independent B"
  shows "dim V = card B"
proof -
  define p where "p b \<equiv> independent b \<and> span b = span V" for b
  have "p (SOME B. p B)"
    using assms by (intro someI[of p B]) (auto simp: p_def)
  then have "\<exists>f. bij_betw f B (SOME B. p B)"
    by (subst (asm) p_def, intro bij_if_span_eq_span_bases[OF B]) (simp_all add: BV)
  then have "card B = card (SOME B. p B)"
    by (auto intro: bij_betw_same_card)
  then show ?thesis
    by (simp add: dim_def p_def)
qed

lemma basis_card_eq_dim: "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = dim V"
  using dim_eq_card[of B V] span_mono[of B V] span_minimal[OF _ subspace_span, of V B] by auto

lemma basis_exists: "\<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> card B = dim V"
  by (meson basis_card_eq_dim empty_subsetI independent_empty maximal_independent_subset_extend)

lemma dim_eq_card_independent: "independent B \<Longrightarrow> dim B = card B"
  by (rule dim_eq_card[OF refl])

lemma dim_span: "dim (span S) = dim S"
  by (simp add: dim_def span_span)

lemma dim_span_eq_card_independent: "independent B \<Longrightarrow> dim (span B) = card B"
  by (simp add: dim_span dim_eq_card)

lemma dim_le_card: assumes "V \<subseteq> span W" "finite W" shows "dim V \<le> card W"
proof -
  obtain A where "independent A" "A \<subseteq> V" "V \<subseteq> span A"
    using maximal_independent_subset[of V] by auto
  with assms independent_span_bound[of W A] basis_card_eq_dim[of A V]
  show ?thesis by auto
qed

lemma span_eq_dim: "span S = span T \<Longrightarrow> dim S = dim T"
  by (metis dim_span)

end

lemma module_iff_vector_space: "module s \<longleftrightarrow> vector_space s"
  unfolding module_def vector_space_def ..


locale linear = vs1: vector_space s1 + vs2: vector_space s2 + module_hom s1 s2 f
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
  and f :: "'b \<Rightarrow> 'c"

lemma module_hom_iff_linear: "module_hom s1 s2 f \<longleftrightarrow> linear s1 s2 f"
  unfolding module_hom_def linear_def module_iff_vector_space by auto

lemma linear_iff: "linear s1 s2 f \<longleftrightarrow>
  (vector_space s1 \<and> vector_space s2 \<and> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (s1 c x) = s2 c (f x)))"
  unfolding linear_def module_hom_iff vector_space_def by auto

locale vector_space_pair = vs1: vector_space s1 + vs2: vector_space s2
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
begin

sublocale module_pair s1 s2 by unfold_locales

sublocale p: vector_space scale by unfold_locales

lemma linear_eq_on:
  assumes l: "module_hom s1 s2 f" "module_hom s1 s2 g"
  assumes x: "x \<in> vs1.span B" and eq: "\<And>b. b \<in> B \<Longrightarrow> f b = g b"
  shows "f x = g x"
proof -
  interpret d: module_hom s1 s2 "\<lambda>x. f x - g x"
    using l by (intro module_hom_sub) (auto simp: module_hom_iff_linear)
  have "f x - g x = 0"
    by (rule d.eq_0_on_span[OF _ x]) (auto simp: eq)
  then show ?thesis by auto
qed

definition construct :: "'b set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c)"
  where "construct B g v = (\<Sum>b | vs1.representation (vs1.extend_basis B) v b \<noteq> 0.
      vs1.representation (vs1.extend_basis B) v b *b (if b \<in> B then g b else 0))"

lemma construct_cong: "(\<And>b. b \<in> B \<Longrightarrow> f b = g b) \<Longrightarrow> construct B f = construct B g"
  unfolding construct_def by (rule ext, auto intro!: sum.cong)

lemma module_hom_construct:
  assumes B[simp]: "vs1.independent B"
  shows "module_hom s1 s2 (construct B f)"
  unfolding module_hom_iff_linear linear_iff
proof safe
  have eB[simp]: "vs1.independent (vs1.extend_basis B)"
    using vs1.independent_extend_basis[OF B] .
  let ?R = "vs1.representation (vs1.extend_basis B)"
  fix c x y
  have "construct B f (x + y) =
    (\<Sum>b\<in>{b. ?R x b \<noteq> 0} \<union> {b. ?R y b \<noteq> 0}. ?R (x + y) b *b (if b \<in> B then f b else 0))"
    by (auto intro!: sum.mono_neutral_cong_left simp: vs1.finite_representation vs1.representation_add construct_def)
  also have "\<dots> = construct B f x + construct B f y"
    by (auto simp: construct_def vs1.representation_add vs2.scale_left_distrib sum.distrib
      intro!: arg_cong2[where f="(+)"] sum.mono_neutral_cong_right vs1.finite_representation)
  finally show "construct B f (x + y) = construct B f x + construct B f y" .
  
  show "construct B f (c *a x) = c *b construct B f x"
    by (auto simp del: vs2.scale_scale intro!: sum.mono_neutral_cong_left vs1.finite_representation
      simp add: construct_def vs2.scale_scale[symmetric] vs1.representation_scale vs2.scale_sum_right)
qed intro_locales

lemma construct_basis:
  assumes B[simp]: "vs1.independent B" and b: "b \<in> B"
  shows "construct B f b = f b"
proof -
  have *: "vs1.representation (vs1.extend_basis B) b = (\<lambda>v. if v = b then 1 else 0)"
    using vs1.extend_basis_superset[OF B] b
    by (intro vs1.representation_basis vs1.independent_extend_basis) auto
  then have "{v. vs1.representation (vs1.extend_basis B) b v \<noteq> 0} = {b}"
    by auto
  then show ?thesis
    unfolding construct_def by (simp add: * b)
qed

lemma construct_outside:
  assumes B: "vs1.independent B" and v: "v \<in> vs1.span (vs1.extend_basis B - B)"
  shows "construct B f v = 0"
  unfolding construct_def
proof (clarsimp intro!: sum.neutral)
  fix b assume "b \<in> B"
  then have "vs1.representation (vs1.extend_basis B - B) v b = 0"
    using vs1.representation_ne_zero[of "vs1.extend_basis B - B" v b] by auto
  moreover have "vs1.representation (vs1.extend_basis B) v = vs1.representation (vs1.extend_basis B - B) v"
    using vs1.representation_extend[OF vs1.independent_extend_basis[OF B] v] by auto
  ultimately show "vs1.representation (vs1.extend_basis B) v b *b f b = 0"
    by simp
qed

lemma construct_add:
  assumes B[simp]: "vs1.independent B"
  shows "construct B (\<lambda>x. f x + g x) v = construct B f v + construct B g v"
proof (rule linear_eq_on)
  show "v \<in> vs1.span (vs1.extend_basis B)" by simp
  show "b \<in> vs1.extend_basis B \<Longrightarrow> construct B (\<lambda>x. f x + g x) b = construct B f b + construct B g b" for b
    using construct_outside[OF B vs1.span_base, of b] by (cases "b \<in> B") (auto simp: construct_basis)
qed (intro module_hom_construct module_hom_add B)+

lemma construct_scale:
  assumes B[simp]: "vs1.independent B"
  shows "construct B (\<lambda>x. c *b f x) v = c *b construct B f v"
proof (rule linear_eq_on)
  show "v \<in> vs1.span (vs1.extend_basis B)" by simp
  show "b \<in> vs1.extend_basis B \<Longrightarrow> construct B (\<lambda>x. c *b f x) b = c *b construct B f b" for b
    using construct_outside[OF B vs1.span_base, of b] by (cases "b \<in> B") (auto simp: construct_basis)
qed (intro module_hom_construct module_hom_scale B)+

lemma construct_in_span:
  assumes B[simp]: "vs1.independent B"
  shows "construct B f v \<in> vs2.span (f ` B)"
proof -
  interpret c: module_hom s1 s2 "construct B f" by (rule module_hom_construct) fact
  let ?R = "vs1.representation B"
  have "v \<in> vs1.span ((vs1.extend_basis B - B) \<union> B)"
    by (auto simp: Un_absorb2 vs1.extend_basis_superset)
  then obtain x y where "v = x + y" "x \<in> vs1.span (vs1.extend_basis B - B)" "y \<in> vs1.span B"
    unfolding vs1.span_Un by auto
  moreover have "construct B f (\<Sum>b | ?R y b \<noteq> 0. ?R y b *a b) \<in> vs2.span (f ` B)"
    by (auto simp add: c.sum c.scale construct_basis vs1.representation_ne_zero
      intro!: vs2.span_sum vs2.span_scale intro: vs2.span_base )
  ultimately show "construct B f v \<in> vs2.span (f ` B)"
    by (auto simp add: c.add construct_outside vs1.sum_nonzero_representation_eq)
qed

lemma (in linear) exists_left_inverse_on:
  assumes V: "vs1.subspace V" and f: "inj_on f V"
  shows "\<exists>g\<in>UNIV \<rightarrow> V. module_hom s2 s1 g \<and> (\<forall>v\<in>V. g (f v) = v)"
proof -
  obtain B where V_eq: "V = vs1.span B" and B: "vs1.independent B"
    using vs1.maximal_independent_subset[of V] vs1.span_minimal[OF _ \<open>vs1.subspace V\<close>] by auto
  have f: "inj_on f (vs1.span B)"
    using f unfolding V_eq .
  show ?thesis
  proof (intro bexI ballI conjI)
    interpret p: vector_space_pair s2 s1 by unfold_locales
    have fB: "vs2.independent (f ` B)"
      using independent_injective_image[OF B f] .
    let ?g = "p.construct (f ` B) (the_inv_into B f)"
    show "module_hom ( *b) ( *a) ?g"
      by (rule p.module_hom_construct[OF fB])
    have "?g b \<in> vs1.span (the_inv_into B f ` f ` B)" for b
      by (intro p.construct_in_span fB)
    moreover have "the_inv_into B f ` f ` B = B"
      by (auto simp: image_comp comp_def the_inv_into_f_f inj_on_subset[OF f vs1.span_superset]
          cong: image_cong)
    ultimately show "?g \<in> UNIV \<rightarrow> V"
      by (auto simp: V_eq)
    have "(?g \<circ> f) v = id v" if "v \<in> vs1.span B" for v
    proof (rule vector_space_pair.linear_eq_on[where x=v])
      show "vector_space_pair ( *a) ( *a)" by unfold_locales
      show "module_hom ( *a) ( *a) (?g \<circ> f)"
        apply (rule module_hom_compose[of _ "( *b)"])
        subgoal by unfold_locales
        apply fact
        done
      show "module_hom ( *a) ( *a) id" by (rule module_hom_id) unfold_locales
      show "v \<in> vs1.span B" by fact
      show "b \<in> B \<Longrightarrow> (p.construct (f ` B) (the_inv_into B f) \<circ> f) b = id b" for b
        by (simp add: p.construct_basis fB the_inv_into_f_f inj_on_subset[OF f vs1.span_superset])
    qed
    then show "v \<in> V \<Longrightarrow> ?g (f v) = v" for v by (auto simp: comp_def id_def V_eq)
  qed
qed

lemma (in linear) exists_right_inverse_on:
  assumes "vs1.subspace V" 
  shows "\<exists>g\<in>UNIV \<rightarrow> V. module_hom s2 s1 g \<and> (\<forall>v\<in>f ` V. f (g v) = v)"
proof -
  obtain B where V_eq: "V = vs1.span B" and B: "vs1.independent B"
    using vs1.maximal_independent_subset[of V] vs1.span_minimal[OF _ \<open>vs1.subspace V\<close>] by auto
  obtain C where C: "vs2.independent C" and fB_C: "f ` B \<subseteq> vs2.span C" "C \<subseteq> f ` B"
    using vs2.maximal_independent_subset[of "f ` B"] by auto
  then have "\<forall>v\<in>C. \<exists>b\<in>B. v = f b" by auto
  then obtain g where g: "\<And>v. v \<in> C \<Longrightarrow> g v \<in> B" "\<And>v. v \<in> C \<Longrightarrow> f (g v) = v" by metis
  show ?thesis
  proof (intro bexI ballI conjI)
    interpret p: vector_space_pair s2 s1 by unfold_locales
    let ?g = "p.construct C g"
    show "module_hom ( *b) ( *a) ?g"
      by (rule p.module_hom_construct[OF C])
    have "?g v \<in> vs1.span (g ` C)" for v
      by (rule p.construct_in_span[OF C])
    also have "\<dots> \<subseteq> V" unfolding V_eq using g by (intro vs1.span_mono) auto
    finally show "?g \<in> UNIV \<rightarrow> V" by auto
    have "(f \<circ> ?g) v = id v" if v: "v \<in> f ` V" for v
    proof (rule vector_space_pair.linear_eq_on[where x=v])
      show "vector_space_pair ( *b) ( *b)" by unfold_locales
      show "module_hom ( *b) ( *b) (f \<circ> ?g)"
        apply (rule module_hom_compose[of _ "( *a)"])
        apply fact
        subgoal by unfold_locales
        done
      show "module_hom ( *b) ( *b) id" by (rule module_hom_id) unfold_locales
      have "vs2.span (f ` B) = vs2.span C"
        using fB_C vs2.span_mono[of C "f ` B"] vs2.span_minimal[of "f`B" "vs2.span C"] by (auto simp: vs2.subspace_span)
      then show "v \<in> vs2.span C"
        using v span_image[of B] by (simp add: V_eq)
      show "(f \<circ> p.construct C g) b = id b" if b: "b \<in> C" for b
        by (auto simp: p.construct_basis g C b)
    qed
    then show "v \<in> f ` V \<Longrightarrow> f (?g v) = v" for v by (auto simp: comp_def id_def)
  qed
qed

end

locale finite_dimensional_vector_space = vector_space +
  fixes Basis :: "'b set"
  assumes finite_Basis: "finite Basis"
  and independent_Basis: "independent Basis"
  and span_Basis: "span Basis = UNIV"
begin

definition "dimension = card Basis"

lemma finiteI_independent: "independent B \<Longrightarrow> finite B"
  using independent_span_bound[OF finite_Basis, of B] by (auto simp: span_Basis)

lemma dim_mono: assumes "V \<subseteq> span W" shows "dim V \<le> dim W"
proof -
  obtain B where "independent B" "B \<subseteq> W" "W \<subseteq> span B"
    using maximal_independent_subset[of W] by auto
  with dim_le_card[of V B] assms independent_span_bound[of Basis B] basis_card_eq_dim[of B W]
    span_mono[of B W] span_minimal[OF _ subspace_span, of W B]
  show ?thesis
    by (auto simp: finite_Basis span_Basis)
qed

lemma dim_subset: "S \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using dim_mono[of S T] by (auto intro: span_base)

lemma dim_UNIV: "dim UNIV = card Basis"
  using dim_eq_card[of Basis UNIV] by (simp add: independent_Basis span_Basis span_UNIV)

lemma independent_card_le_dim: assumes "B \<subseteq> V" and "independent B" shows "card B \<le> dim V"
  by (subst dim_eq_card[symmetric, OF refl \<open>independent B\<close>]) (rule dim_subset[OF \<open>B \<subseteq> V\<close>])

lemma dim_unique: "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim)

lemma card_ge_dim_independent:
  assumes BV: "B \<subseteq> V"
    and iB: "independent B"
    and dVB: "dim V \<le> card B"
  shows "V \<subseteq> span B"
proof
  fix a
  assume aV: "a \<in> V"
  {
    assume aB: "a \<notin> span B"
    then have iaB: "independent (insert a B)"
      using iB aV BV by (simp add: independent_insert)
    from aV BV have th0: "insert a B \<subseteq> V"
      by blast
    from aB have "a \<notin>B"
      by (auto simp add: span_base)
    with independent_card_le_dim[OF th0 iaB] dVB finiteI_independent[OF iB]
    have False by auto
  }
  then show "a \<in> span B" by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "B \<subseteq> V"
    and VB: "V \<subseteq> span B"
    and fB: "finite B"
    and dVB: "dim V \<ge> card B"
  shows "independent B"
proof -
  {
    fix a
    assume a: "a \<in> B" "a \<in> span (B - {a})"
    from a fB have c0: "card B \<noteq> 0"
      by auto
    from a fB have cb: "card (B - {a}) = card B - 1"
      by auto
    {
      fix x
      assume x: "x \<in> V"
      from a have eq: "insert a (B - {a}) = B"
        by blast
      from x VB have x': "x \<in> span B"
        by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B - {a})" .
    }
    then have th1: "V \<subseteq> span (B - {a})"
      by blast
    have th2: "finite (B - {a})"
      using fB by auto
    from dim_le_card[OF th1 th2]
    have c: "dim V \<le> card (B - {a})" .
    from c c0 dVB cb have False by simp
  }
  then show ?thesis
    unfolding dependent_def by blast
qed

lemma card_eq_dim: "B \<subseteq> V \<Longrightarrow> card B = dim V \<Longrightarrow> finite B \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis order_eq_iff card_le_dim_spanning card_ge_dim_independent)

end

locale finite_dimensional_vector_space_pair =
  vs1: finite_dimensional_vector_space s1 B1 + vs2: finite_dimensional_vector_space s2 B2
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and B1 :: "'b set"
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
  and B2 :: "'c set"
begin

sublocale vector_space_pair s1 s2 by unfold_locales

lemma linear_surjective_imp_injective:
  assumes lf: "linear s1 s2 f" and sf: "surj f" and eq: "vs2.dim UNIV = vs1.dim UNIV"
    shows "inj f"
proof -
  interpret linear s1 s2 f by fact
  have *: "card (f ` B1) \<le> vs2.dim UNIV"
    using vs1.finite_Basis vs1.dim_eq_card[of B1 UNIV] sf
    by (auto simp: vs1.span_Basis vs1.span_UNIV vs1.independent_Basis eq intro!: card_image_le)

  have indep_fB: "vs2.independent (f ` B1)"
    using vs1.finite_Basis vs1.dim_eq_card[of B1 UNIV] sf *
    by (intro vs2.card_le_dim_spanning[of "f ` B1" UNIV]) (auto simp: span_image vs1.span_Basis )
  have "vs2.dim UNIV \<le> card (f ` B1)"
    unfolding eq sf[symmetric] vs2.dim_span_eq_card_independent[symmetric, OF indep_fB]
      vs2.dim_span
    by (intro vs2.dim_mono) (auto simp: span_image vs1.span_Basis)
  with * have "card (f ` B1) = vs2.dim UNIV" by auto
  also have "... = card B1"
    unfolding eq vs1.dim_UNIV ..
  finally have "inj_on f B1"
    by (subst inj_on_iff_eq_card[OF vs1.finite_Basis])
  then show "inj f"
    using inj_on_span_iff_independent_image[OF indep_fB] vs1.span_Basis by auto
qed

lemma linear_injective_imp_surjective:
  assumes lf: "linear s1 s2 f" and sf: "inj f" and eq: "vs2.dim UNIV = vs1.dim UNIV"
    shows "surj f"
proof -
  interpret linear s1 s2 f by fact
  have *: False if b: "b \<notin> vs2.span (f ` B1)" for b
  proof -
    have *: "vs2.independent (f ` B1)"
      using vs1.independent_Basis by (intro independent_injective_image inj_on_subset[OF sf]) auto
    have **: "vs2.independent (insert b (f ` B1))"
      using b * by (rule vs2.independent_insertI)

    have "b \<notin> f ` B1" using vs2.span_base[of b "f ` B1"] b by auto
    then have "Suc (card B1) = card (insert b (f ` B1))"
      using sf[THEN inj_on_subset, of B1] by (subst card_insert) (auto intro: vs1.finite_Basis simp: card_image)
    also have "\<dots> = vs2.dim (insert b (f ` B1))"
      using vs2.dim_eq_card_independent[OF **] by simp
    also have "vs2.dim (insert b (f ` B1)) \<le> vs2.dim B2"
      by (rule vs2.dim_mono) (auto simp: vs2.span_Basis)
    also have "\<dots> = card B1"
      using vs1.dim_span[of B1] vs2.dim_span[of B2] unfolding vs1.span_Basis vs2.span_Basis eq 
        vs1.dim_eq_card_independent[OF vs1.independent_Basis] by simp
    finally show False by simp
  qed
  have "f ` UNIV = f ` vs1.span B1" unfolding vs1.span_Basis ..
  also have "\<dots> = vs2.span (f ` B1)" unfolding span_image ..
  also have "\<dots> = UNIV" using * by blast
  finally show ?thesis .
qed

lemma linear_injective_isomorphism:
  assumes lf: "linear s1 s2 f"
    and fi: "inj f"
    and dims: "vs2.dim UNIV = vs1.dim UNIV"
  shows "\<exists>f'. linear s2 s1 f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
proof -
  interpret linear s1 s2 f by fact
  show ?thesis
    unfolding isomorphism_expand[symmetric]
    using exists_right_inverse_on[OF vs1.subspace_UNIV]
      exists_left_inverse_on[OF vs1.subspace_UNIV fi]
    apply (auto simp: module_hom_iff_linear)
    subgoal for f' f''
      apply (rule exI[where x=f''])
      using linear_injective_imp_surjective[OF lf fi dims]
      apply auto
      by (metis comp_apply eq_id_iff surj_def)
    done
qed

lemma linear_surjective_isomorphism:
  assumes lf: "linear s1 s2 f"
    and sf: "surj f"
    and dims: "vs2.dim UNIV = vs1.dim UNIV"
  shows "\<exists>f'. linear s2 s1 f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
proof -
  interpret linear s1 s2 f by fact
  show ?thesis
    unfolding isomorphism_expand[symmetric]
    using exists_right_inverse_on[OF vs1.subspace_UNIV]
      exists_left_inverse_on[OF vs1.subspace_UNIV]
    using linear_surjective_imp_injective[OF lf sf dims] sf
    apply (auto simp: module_hom_iff_linear)
    subgoal for f' f''
      apply (rule exI[where x=f''])
      apply auto
      by (metis isomorphism_expand)
    done
qed

end

lemma linear_compose: "linear s1 s2 f \<Longrightarrow> linear s2 s3 g \<Longrightarrow> linear s1 s3 (g o f)"
  unfolding module_hom_iff_linear[symmetric]
  by (rule module_hom_compose)

context finite_dimensional_vector_space begin

sublocale pairself: finite_dimensional_vector_space_pair scale Basis scale Basis ..

lemmas linear_surjective_isomorphism = pairself.linear_surjective_isomorphism[OF _ _ refl]
lemmas linear_injective_isomorphism = pairself.linear_injective_isomorphism[OF _ _ refl]

end

lemma linear_eq_on_span:
  assumes lf: "linear scale scaleC f"
    and lg: "linear scale scaleC g"
    and fg: "\<And>x. x \<in> B \<Longrightarrow> f x = g x"
    and x: "x \<in> module.span scale B"
  shows "f x = g x"
  by (meson Vector_Spaces.linear.axioms(3) fg lf lg module_hom_eq_on_span x)

lemma (in vector_space) linear_id: "linear scale scale id"
  by unfold_locales auto



end