(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section {* Gram-Schmidt Orthogonalization *}

text {*
  This theory provides the Gram-Schmidt orthogonalization algorithm,
  that takes the conjugate operation into account. It works over fields
  like the rational, real, or complex numbers. 
*}

theory Gram_Schmidt
imports 
  VS_Connect 
  Missing_VectorSpace
  Conjugate
begin

subsection {* Conjugates of Vectors *}

definition vec_conjugate::"'a :: conjugatable_field vec \<Rightarrow> 'a vec" ("conjugate\<^sub>v")
  where "conjugate\<^sub>v v = vec (dim\<^sub>v v) (\<lambda>i. conjugate (v $ i))"

lemma vec_conjugate_index[simp]:
  shows "i < dim\<^sub>v v \<Longrightarrow> conjugate\<^sub>v v $ i = conjugate (v $ i)"
    and "dim\<^sub>v (conjugate\<^sub>v v) = dim\<^sub>v v"
  unfolding vec_conjugate_def by auto

lemma vec_conjugate_closed[simp]: "v : carrier\<^sub>v n \<Longrightarrow> conjugate\<^sub>v v : carrier\<^sub>v n"
  unfolding vec_conjugate_def by auto

lemma vec_conjugate_dist_add:
  assumes dim: "v : carrier\<^sub>v n" "w : carrier\<^sub>v n"
  shows "conjugate\<^sub>v (v \<oplus>\<^sub>v w) = conjugate\<^sub>v v \<oplus>\<^sub>v conjugate\<^sub>v w"
  by (rule, insert dim, auto simp: conjugate_dist_add)

lemma vec_conjugate_uminus: "\<ominus>\<^sub>v (conjugate\<^sub>v v) = conjugate\<^sub>v (\<ominus>\<^sub>v v)"
  by (rule, auto simp:conjugate_neg)

lemma vec_conjugate_zero[simp]: "conjugate\<^sub>v (\<zero>\<^sub>v n) = \<zero>\<^sub>v n" by auto

lemma vec_conjugate_id[simp]: "conjugate\<^sub>v (conjugate\<^sub>v v) = v"
  unfolding vec_conjugate_def by auto

lemma vec_conjugate_cancel_iff[simp]: "conjugate\<^sub>v v = conjugate\<^sub>v w \<longleftrightarrow> v = w"
  (is "?v = ?w \<longleftrightarrow> _")
proof(rule iffI)
  assume cvw: "?v = ?w" show "v = w"
  proof(rule)
    have "dim\<^sub>v ?v = dim\<^sub>v ?w" using cvw by auto
    thus dim: "dim\<^sub>v v = dim\<^sub>v w" by simp
    fix i assume i: "i < dim\<^sub>v w"
    hence "conjugate\<^sub>v v $ i = conjugate\<^sub>v w $ i" using cvw by auto
    hence "conjugate (v$i) = conjugate (w $ i)" using i dim by auto
    thus "v $ i = w $ i" by auto
  qed
qed auto

lemma vec_conjugate_zero_iff[simp]: "conjugate\<^sub>v v = \<zero>\<^sub>v n \<longleftrightarrow> v = \<zero>\<^sub>v n"
  using vec_conjugate_cancel_iff[of _ "\<zero>\<^sub>v n"] by auto

lemma vec_conjugate_dist_smult: "conjugate\<^sub>v (k \<odot>\<^sub>v v) = conjugate k \<odot>\<^sub>v conjugate\<^sub>v v"
  unfolding vec_conjugate_def
  apply(rule) using conjugate_dist_mul by auto

lemma vec_conjugate_dist_sprod:
  assumes v[simp]: "v : carrier\<^sub>v n" and w[simp]: "w : carrier\<^sub>v n"
  shows "conjugate (v \<bullet> w) = conjugate\<^sub>v v \<bullet> conjugate\<^sub>v w"
  unfolding scalar_prod_def
  apply (subst setsum_conjugate[OF finite_atLeastLessThan])
  unfolding vec_conjugate_index
proof (rule setsum.cong[OF refl])
  fix i assume "i : {0..<dim\<^sub>v w}"
  hence [simp]:"i < dim\<^sub>v v" "i < dim\<^sub>v w"
    unfolding vec_elemsD[OF v] vec_elemsD[OF w]
    using atLeastLessThan_iff by auto
  show "conjugate (v $ i * w $ i) = conjugate\<^sub>v v $ i * conjugate\<^sub>v w $ i"
    using conjugate_dist_mul vec_conjugate_index by auto
qed

abbreviation cscalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: conjugatable_field" (infix "\<bullet>c" 70)
  where "op \<bullet>c == \<lambda>v w. v \<bullet> conjugate\<^sub>v w"

lemma vec_conjugate_conjugate_sprod[simp]:
  assumes v[simp]: "v : carrier\<^sub>v n" and w[simp]: "w : carrier\<^sub>v n"
  shows "conjugate (conjugate\<^sub>v v \<bullet> w) = v \<bullet>c w"
  apply (subst vec_conjugate_dist_sprod[of _ n]) by auto

lemma vec_conjugate_sprod_comm:
  assumes "v : carrier\<^sub>v n" and "w : carrier\<^sub>v n"
  shows "v \<bullet>c w = (conjugate\<^sub>v w \<bullet> v)"
  unfolding scalar_prod_def using assms by(subst setsum_ivl_cong, auto)

lemma vec_conjugate_square_zero:
  fixes v :: "'a :: conjugatable_ordered_field vec"
  assumes v[simp]: "v : carrier\<^sub>v n"
  shows "v \<bullet>c v = 0 \<longleftrightarrow> v = \<zero>\<^sub>v n"
proof
  have dim: "dim\<^sub>v v = dim\<^sub>v (\<zero>\<^sub>v n)" by auto
  let ?f = "\<lambda>i. v$i * conjugate (v$i)"
  let ?I = "{0..<dim\<^sub>v v}"
  have f: "?f : ?I \<rightarrow> { y. y \<ge> 0 }" using conjugate_square_positive by auto
  assume vv0: "v \<bullet>c v = 0"
  hence fI0: "?f ` ?I \<subseteq> {0}"
    unfolding scalar_prod_def
    using positive_sum[OF _ f] by auto
  { fix i assume i: "i < dim\<^sub>v v"
    hence "?f i = 0" using fI0 by fastforce
    hence "v $ i = 0" using conjugate_square_0 by auto
    hence "v $ i = \<zero>\<^sub>v n $ i" using i v by auto
  }
  from vec_eqI[OF this] show "v = \<zero>\<^sub>v n" by auto
  next assume "v = \<zero>\<^sub>v n" thus "v \<bullet>c v = 0"
    unfolding scalar_prod_def by auto
qed

lemma vec_conjugate_rat[simp]: "(conjugate\<^sub>v :: rat vec \<Rightarrow> rat vec) = (\<lambda>x. x)" by force
lemma vec_conjugate_real[simp]: "(conjugate\<^sub>v :: real vec \<Rightarrow> real vec) = (\<lambda>x. x)" by force


subsection {* Orthogonality with Conjugates *}

definition "corthogonal vs \<equiv>
    \<forall>i < length vs. \<forall>j < length vs. vs ! i \<bullet>c vs ! j = 0 \<longleftrightarrow> i \<noteq> j"

lemma corthogonalD[elim]:
  "corthogonal vs \<Longrightarrow> i < length vs \<Longrightarrow> j < length vs \<Longrightarrow>
   vs ! i \<bullet>c vs ! j = 0 \<longleftrightarrow> i \<noteq> j"
  unfolding corthogonal_def by auto

lemma corthogonalI[intro]:
  "(\<And>i j. i < length vs \<Longrightarrow> j < length vs \<Longrightarrow> vs ! i \<bullet>c vs ! j = 0 \<longleftrightarrow> i \<noteq> j) \<Longrightarrow>
   corthogonal vs"
  unfolding corthogonal_def by auto

lemma corthogonal_distinct: "corthogonal us \<Longrightarrow> distinct us"
proof (induct us)
  case (Cons u us)
    have "u \<notin> set us"
    proof
      assume "u : set us"
      then obtain j where uj: "u = us!j" and j: "j < length us"
        using in_set_conv_nth by metis
      hence j': "j+1 < length (u#us)" by auto
      have "u \<bullet>c us!j = 0"
        using corthogonalD[OF Cons(2) _ j',of 0] by auto
      hence "u \<bullet>c u = 0" using uj by simp
      thus False using corthogonalD[OF Cons(2),of 0 0] by auto
    qed
    moreover have "distinct us"
    proof (rule Cons(1),intro corthogonalI)
      fix i j assume "i < length (us)" "j < length (us)"
      hence len: "i+1 < length (u#us)" "j+1 < length (u#us)" by auto
      show "(us!i \<bullet>c us!j = 0) = (i\<noteq>j)"
        using corthogonalD[OF Cons(2) len] by simp
    qed
    ultimately show ?case by simp
qed simp

lemma corthogonal_sort:
  assumes dist': "distinct us'"
      and mem: "set us = set us'"
  shows "corthogonal us \<Longrightarrow> corthogonal us'"
proof
  assume orth: "corthogonal us"
  hence dist: "distinct us" using corthogonal_distinct by auto
  fix i' j' assume i': "i' < length us'" and j': "j' < length us'"
  obtain i where ii': "us!i = us'!i'" and i: "i < length us"
    using mem i' in_set_conv_nth by metis
  obtain j where jj': "us!j = us'!j'" and j: "j < length us"
    using mem j' in_set_conv_nth by metis
  from corthogonalD[OF orth i j]
  have "(us!i \<bullet>c us!j = 0) = (i \<noteq> j)".
  hence "(us'!i' \<bullet>c us'!j' = 0) = (i \<noteq> j)" using ii' jj' by auto
  also have "... = (us!i \<noteq> us!j)" using nth_eq_iff_index_eq dist i j by auto
  also have "... = (us'!i' \<noteq> us'!j')" using ii' jj' by auto
  also have "... = (i' \<noteq> j')" using nth_eq_iff_index_eq dist' i' j' by auto
  finally show "(us'!i' \<bullet>c us'!j' = 0) = (i' \<noteq> j')".
qed

subsection{* The Algorithm  *}

fun adjuster :: "nat \<Rightarrow> 'a :: conjugatable_field vec \<Rightarrow> 'a vec list \<Rightarrow> 'a vec"
  where "adjuster n w [] = \<zero>\<^sub>v n"
    |  "adjuster n w (u#us) = -(w \<bullet>c u)/(u \<bullet>c u) \<odot>\<^sub>v u \<oplus>\<^sub>v adjuster n w us"

text {*
  The following formulation is easier to analyze,
  but outputs of the subroutine should be properly reversed.
*}

fun gram_schmidt_sub
  where "gram_schmidt_sub n us [] = us"
  | "gram_schmidt_sub n us (w # ws) =
     gram_schmidt_sub n ((adjuster n w us \<oplus>\<^sub>v w) # us) ws"

definition gram_schmidt :: "nat \<Rightarrow> 'a :: conjugatable_field vec list \<Rightarrow> 'a vec list"
  where "gram_schmidt n ws = rev (gram_schmidt_sub n [] ws)"

text {*
  The following formulation requires no reversal.
*}

fun gram_schmidt_sub2
  where "gram_schmidt_sub2 n us [] = []"
  | "gram_schmidt_sub2 n us (w # ws) =
     (let u = adjuster n w us \<oplus>\<^sub>v w in
      u # gram_schmidt_sub2 n (u # us) ws)"

lemma gram_schmidt_sub_eq:
  "rev (gram_schmidt_sub n us ws) = rev us @ gram_schmidt_sub2 n us ws"
  by (induct ws arbitrary:us, auto simp:Let_def)

lemma gram_schmidt_code[code]:
  "gram_schmidt n ws = gram_schmidt_sub2 n [] ws"
  unfolding gram_schmidt_def
  apply(subst gram_schmidt_sub_eq) by simp

subsection {* Properties of the Algorithms *}

locale cof_vec_space = vec_space f_ty for
  f_ty :: "'a :: conjugatable_ordered_field itself"
begin

lemma adjuster_finsum:
  assumes U: "set us \<subseteq> carrier\<^sub>v n"
    and dist: "distinct (us :: 'a vec list)"
  shows "adjuster n w us = finsum V (\<lambda>u. -(w \<bullet>c u)/(u \<bullet>c u) \<odot>\<^sub>v u) (set us)"
  using assms
proof (induct us)
  case Cons show ?case unfolding set_simps
  by (subst finsum_insert[OF finite_set], insert Cons, auto)
qed simp

lemma adjuster_lincomb:
  assumes w: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "adjuster n w us = lincomb (\<lambda>u. -(w \<bullet>c u)/(u \<bullet>c u)) (set us)"
    (is "_ = lincomb ?a _")
  using us dist unfolding lincomb_def
proof (induct us)
  case (Cons u us)
    let ?f = "\<lambda>u. ?a u \<odot>\<^sub>v u"
    have "?f : (set us) \<rightarrow> carrier\<^sub>v n" and "?f u : carrier\<^sub>v n" using w Cons by auto
    moreover have "u \<notin> set us" using Cons by auto
    ultimately show ?case
      unfolding adjuster.simps
      unfolding set_simps
      using finsum_insert[OF finite_set] Cons by auto
qed simp

lemma adjuster_in_span:
  assumes w: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "adjuster n w us : span (set us)"
  using adjuster_lincomb[OF assms]
  unfolding finite_span[OF finite_set us] by auto

lemma adjuster_carrier[simp]:
  assumes w: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "adjuster n w us : carrier\<^sub>v n"
  using adjuster_in_span span_closed assms by auto

lemma adjust_not_in_span:
  assumes w[simp]: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
    and ind: "w \<notin> span (set us)"
  shows "adjuster n w us \<oplus>\<^sub>v w \<notin> span (set us)"
  using span_add[OF us adjuster_in_span[OF w us dist] w]
  using vec_add_comm ind by auto

lemma adjust_not_mem:
  assumes w[simp]: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
    and ind: "w \<notin> span (set us)"
  shows "adjuster n w us \<oplus>\<^sub>v w \<notin> set us"
  using adjust_not_in_span[OF assms] span_mem[OF us] by auto

lemma adjust_in_span:
  assumes w[simp]: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "adjuster n w us \<oplus>\<^sub>v w : span (insert w (set us))" (is "?v \<oplus>\<^sub>v _ : span ?U")
proof -
  let ?a = "\<lambda>u. -(w \<bullet>c u)/(u \<bullet>c u)"
  have "?v = lincomb ?a (set us)" using adjuster_lincomb[OF assms].
  hence vU: "?v : span (set us)" unfolding finite_span[OF finite_set us] by auto
  hence v[simp]: "?v : carrier\<^sub>v n" using span_closed[OF us] by auto
  have vU': "?v : span ?U" using vU span_is_monotone[OF subset_insertI] by auto

  have "{w} \<subseteq> ?U" by simp
  from span_is_monotone[OF this]
  have wU': "w : span ?U" using span_self[OF w] by auto

  have "?U \<subseteq> carrier\<^sub>v n" using us w by simp
  from span_add[OF this wU' v] vU' vec_add_comm[OF w]
  show ?thesis by simp
qed

lemma adjust_not_lindep:
  assumes w[simp]: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
    and wus: "w \<notin> span (set us)"
    and ind: "~ lin_dep (set us)"
  shows "~ lin_dep (insert (adjuster n w us \<oplus>\<^sub>v w) (set us))"
    (is "~ _ (insert ?v _)")
proof -
  have v: "?v : carrier\<^sub>v n" using assms by auto
  have "?v \<notin> span (set us)"
    using adjust_not_in_span[OF w us dist wus]
    using vec_add_comm[OF adjuster_carrier[OF w us dist] w] by auto
  thus ?thesis
    using lin_dep_iff_in_span[OF us ind v] adjust_not_mem[OF w us dist wus] by auto
qed

lemma adjust_preserves_span:
  assumes w[simp]: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "w : span (set us) \<longleftrightarrow> adjuster n w us \<oplus>\<^sub>v w : span (set us)"
    (is "_ \<longleftrightarrow> ?v \<oplus>\<^sub>v _ : _")
proof -
  have "?v : span (set us)"
    using adjuster_lincomb[OF assms]
    unfolding finite_span[OF finite_set us] by auto
  hence [simp]: "?v : carrier\<^sub>v n" using span_closed[OF us] by auto
  show ?thesis
    using span_add[OF us adjuster_in_span[OF w us] w] vec_add_comm[OF w] dist
    by auto
qed

lemma in_span_adjust:
  assumes w[simp]: "(w :: 'a vec) : carrier\<^sub>v n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "w : span (insert (adjuster n w us \<oplus>\<^sub>v w) (set us))"
    (is "_ : span (insert ?v _)")
proof -
  have v: "?v : carrier\<^sub>v n" using assms by auto
  have a[simp]: "adjuster n w us : carrier\<^sub>v n"
   and neg: "\<ominus>\<^sub>v adjuster n w us : carrier\<^sub>v n" using assms by auto
  hence vU: "insert ?v (set us) \<subseteq> carrier\<^sub>v n" using us by auto
  have aS: "adjuster n w us : span (insert ?v (set us))"
    using adjuster_in_span[OF w us] span_is_monotone[OF subset_insertI] dist
    by auto
  have negS: "\<ominus>\<^sub>v adjuster n w us : span (insert ?v (set us))"
    using span_neg[OF vU aS] us by simp
  have [simp]:"\<ominus>\<^sub>v adjuster n w us \<oplus>\<^sub>v (adjuster n w us \<oplus>\<^sub>v w) = w"
    unfolding a_assoc[OF neg a w,symmetric] by simp
  have "{?v} \<subseteq> insert ?v (set us)" by simp
  from span_is_monotone[OF this]
  have vS: "?v : span (insert ?v (set us))" using span_self[OF v] by auto
  thus ?thesis using span_add[OF vU negS v] by auto
qed

lemma adjust_zero:
  assumes U: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and orth: "corthogonal us"
    and w[simp]: "w : carrier\<^sub>v n"
    and i: "i < length us"
  shows "(adjuster n w us \<oplus>\<^sub>v w) \<bullet>c us!i = 0"
proof -
  def u == "us!i"
  have u[simp]: "u : carrier\<^sub>v n" using i U u_def by auto
  hence cu[simp]: "conjugate\<^sub>v u : carrier\<^sub>v n" by auto
  have uU: "u : set us" using i u_def by auto
  let ?g = "\<lambda>u'::'a vec. (-(w \<bullet>c u')/(u' \<bullet>c u') \<odot>\<^sub>v u')"
  have g: "?g : set us \<rightarrow> carrier\<^sub>v n" using w U by auto
  hence carrier: "finsum V ?g (set us) : carrier\<^sub>v n" by simp
  let ?f = "\<lambda>u'. ?g u' \<bullet>c u"
  let ?U = "set us - {u}"
  have fU': "?f : ?U \<rightarrow> UNIV" by auto
  { fix u' assume u': "(u'::'a vec) : carrier\<^sub>v n"
    have [simp]: "dim\<^sub>v u = n" by auto
    have "?f u' = (- (w \<bullet>c u') / (u' \<bullet>c u')) * (u' \<bullet>c u)"
      using scalar_prod_scalar_left[of "u'" "conjugate\<^sub>v u"]
      unfolding vec_elemsD[OF u] vec_elemsD[OF u'] by auto
  } note conv = this
  have "?f : ?U \<rightarrow> {0}"
  proof (intro Pi_I)
    fix u' assume u'Uu: "u' : set us - {u}"
    hence u'U: "u' : set us" by auto
    hence u'[simp]: "u' : carrier\<^sub>v n" using U by auto
    obtain j where j: "j < length us" and u'j: "u' = us ! j"
      using u'U in_set_conv_nth by metis
    have "i \<noteq> j" using u'Uu u'j u_def by auto
    hence "u' \<bullet>c u = 0"
      unfolding u'j using corthogonalD[OF orth j i] u_def by auto
    hence "?f u' = 0" using mult_zero_right conv[OF u'] by auto
    thus "?f u' : {0}" by auto
  qed
  hence "restrict ?f ?U = restrict (\<lambda>u. 0) ?U" by force
  hence "setsum ?f ?U = setsum (\<lambda>u. 0) ?U"
    using R.finsum_restrict[OF fU'] by auto
  hence fU'0: "setsum ?f ?U = 0" by auto
  have uU': "u \<notin> ?U" by auto
  have "set us = insert u ?U"
    using insert_Diff_single uU by auto
  hence "setsum ?f (set us) = ?f u + setsum ?f ?U"
    using R.finsum_insert[OF _ uU'] by auto
  also have "... = ?f u" using fU'0 by auto
  also have "... = - (w \<bullet>c u) / (u \<bullet>c u) * (u \<bullet>c u)"
    using conv[OF u] by auto
  finally have main: "setsum ?f (set us) = - (w \<bullet>c u)"
    unfolding u_def
    by (simp add: i orth corthogonalD)
  show ?thesis
    unfolding u_def[symmetric]
    unfolding adjuster_finsum[OF U corthogonal_distinct[OF orth]]
    unfolding scalar_prod_left_distrib[OF carrier w cu]
    unfolding finsum_scalar_prod_setsum[OF g cu]
    unfolding main
    unfolding scalar_prod_comm[OF cu w]
    using left_minus by auto
qed

lemma adjust_nonzero:
  assumes U: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
    and w[simp]: "w : carrier\<^sub>v n"
    and wsU: "w \<notin> span (set us)"
  shows "adjuster n w us \<oplus>\<^sub>v w \<noteq> \<zero>\<^sub>v n" (is "?a \<oplus>\<^sub>v _ \<noteq> _")
proof
  have [simp]: "?a : carrier\<^sub>v n" using U dist by auto
  have [simp]: "\<ominus>\<^sub>v ?a : carrier\<^sub>v n" by auto
  have [simp]: "?a \<oplus>\<^sub>v w : carrier\<^sub>v n" by auto
  assume "?a \<oplus>\<^sub>v w = \<zero>\<^sub>v n"
  hence "\<ominus>\<^sub>v ?a = \<ominus>\<^sub>v ?a \<oplus>\<^sub>v (?a \<oplus>\<^sub>v w)" by auto
  also have "... = (\<ominus>\<^sub>v ?a \<oplus>\<^sub>v ?a) \<oplus>\<^sub>v w" apply(subst a_assoc) by auto
  also have "\<ominus>\<^sub>v ?a \<oplus>\<^sub>v ?a = \<zero>\<^sub>v n" using r_neg[OF w] unfolding vec_neg[OF w] by auto
  finally have "\<ominus>\<^sub>v ?a = w" by auto
  moreover have "\<ominus>\<^sub>v ?a : span (set us)"
    using span_neg[OF U adjuster_in_span[OF w U dist]] by auto
  ultimately show "False" using wsU by auto
qed

lemma adjust_orthogonal:
  assumes U: "set (us :: 'a vec list) \<subseteq> carrier\<^sub>v n"
    and orth: "corthogonal us"
    and w[simp]: "w : carrier\<^sub>v n"
    and wsU: "w \<notin> span (set us)"
  shows "corthogonal ((adjuster n w us \<oplus>\<^sub>v w) # us)"
    (is "corthogonal (?aw # _)")
proof
  have dist: "distinct us" using corthogonal_distinct orth by auto
  have aw[simp]: "?aw : carrier\<^sub>v n" using U dist by auto
  note adjust_nonzero[OF U dist w] wsU
  hence aw0: "?aw \<bullet>c ?aw \<noteq> 0" using vec_conjugate_square_zero[OF aw] by auto
  fix i j assume i: "i < length (?aw # us)" and j: "j < length (?aw # us)"
  show "((?aw # us) ! i \<bullet>c (?aw # us) ! j = 0) = (i \<noteq> j)"
  proof (cases "i = 0")
    case True note i0 = this
      show ?thesis
      proof (cases "j = 0")
        case True show ?thesis unfolding True i0 using aw0 by auto
        next case False
          def j' == "j-1"
          hence jfold: "j = j'+1" using False by auto
          hence j': "j' < length us" using j by auto
          show ?thesis unfolding i0 jfold
            using adjust_zero[OF U orth w j'] by auto
      qed
    next case False
      def i' == "i-1"
      hence ifold: "i = i'+1" using False by auto
      hence i': "i' < length us" using i by auto
      have [simp]: "us ! i' : carrier\<^sub>v n" using U i' by auto
      hence cu': "conjugate\<^sub>v (us ! i') : carrier\<^sub>v n" by auto
      show ?thesis
      proof (cases "j = 0")
        case True
          { assume "?aw \<bullet>c us ! i' = 0"
            hence "conjugate (?aw \<bullet>c us ! i') = 0" using conjugate_zero by auto
            hence "conjugate\<^sub>v ?aw \<bullet> us ! i' = 0"
              using vec_conjugate_dist_sprod[OF aw cu'] by auto
          }
          thus ?thesis unfolding True ifold
          using adjust_zero[OF U orth w i']
          by (subst scalar_prod_comm[of _ n], auto)
        next case False
          def j' == "j-1"
          hence jfold: "j = j'+1" using False by auto
          hence j': "j' < length us" using j by auto
          show ?thesis
            unfolding ifold jfold
            using orth i' j' by (auto simp: corthogonalD)
     qed
  qed
qed

lemma gram_schmidt_sub_span:
  assumes w[simp]: "w : carrier\<^sub>v n"
    and us: "set us \<subseteq> carrier\<^sub>v n"
    and dist: "distinct us"
  shows "span (set ((adjuster n w us \<oplus>\<^sub>v w) # us)) = span (set (w # us))"
  (is "span (set (?v # _)) = span ?wU")
proof (cases "w : span (set us)")
  case True
    hence "?v : span (set us)"
      using adjust_preserves_span[OF assms] by auto
    thus ?thesis using already_in_span[OF us] True by auto next
  case False show ?thesis
    proof
      have wU: "?wU \<subseteq> carrier\<^sub>v n" using us by simp 
      have vswU: "?v : span ?wU" using adjust_in_span[OF assms] by auto
      hence v: "?v : carrier\<^sub>v n" using span_closed[OF wU] by auto
      have wsvU: "w : span (insert ?v (set us))" using in_span_adjust[OF assms].
      show "span ?wU \<subseteq> span (set (?v # us))"
        using span_swap[OF finite_set us w False v wsvU] by auto
      have "?v \<notin> span (set us)"
        using False adjust_preserves_span[OF assms] by auto
      thus "span (set (?v # us)) \<subseteq> span ?wU"
        using span_swap[OF finite_set us v _ w] vswU by auto
    qed
qed

lemma gram_schmidt_sub_result:
  assumes "gram_schmidt_sub n us ws = us'"
    and "set ws \<subseteq> carrier\<^sub>v n"
    and "set us \<subseteq> carrier\<^sub>v n"
    and "distinct (us @ ws)"
    and "~ lin_dep (set (us @ ws))"
    and "corthogonal us"
  shows "set us' \<subseteq> carrier\<^sub>v n \<and>
         distinct us' \<and>
         corthogonal us' \<and>
         span (set (us @ ws)) = span (set us') \<and> length us' = length us + length ws"  
  using assms
proof (induct ws arbitrary: us us')
case (Cons w ws)
  let ?v = "adjuster n w us"
  have wW[simp]: "set (w#ws) \<subseteq> carrier\<^sub>v n" using Cons by simp
  hence W[simp]: "set ws \<subseteq> carrier\<^sub>v n"
   and w[simp]: "w : carrier\<^sub>v n" by auto
  have U[simp]: "set us \<subseteq> carrier\<^sub>v n" using Cons by simp
  have UW: "set (us@ws) \<subseteq> carrier\<^sub>v n" by simp
  have wU: "set (w#us) \<subseteq> carrier\<^sub>v n" by simp
  have dist: "distinct (us @ w # ws)" using Cons by simp
  hence dist_U: "distinct us"
    and dist_W: "distinct ws"
    and dist_UW: "distinct (us @ ws)"
    and w_U: "w \<notin> set us"
    and w_W: "w \<notin> set ws"
    and w_UW: "w \<notin> set (us @ ws)" by auto
  have ind: "~ lin_dep (set (us @ w # ws))" using Cons by simp
  have ind_U: "~ lin_dep (set us)"
    and ind_W: "~ lin_dep (set ws)"
    and ind_wU: "~ lin_dep (insert w (set us))"
    and ind_UW: "~ lin_dep (set (us @ ws))"
    by (subst subset_li_is_li[OF ind];auto)+
  have corth: "corthogonal us" using Cons by simp
  have U'def: "gram_schmidt_sub n ((?v \<oplus>\<^sub>v w)#us) ws = us'" using Cons by simp

  have v: "?v : carrier\<^sub>v n" using dist_U by auto
  hence vw: "?v \<oplus>\<^sub>v w : carrier\<^sub>v n" by auto
  hence vwU: "set ((?v \<oplus>\<^sub>v w) # us) \<subseteq> carrier\<^sub>v n" by auto
  have vsU: "?v : span (set us)" using adjuster_in_span[OF w] dist by auto
  hence vsUW: "?v : span (set (us @ ws))"
    using span_is_monotone[of "set us" "set (us@ws)"] by auto
  have wsU: "w \<notin> span (set us)"
    using lin_dep_iff_in_span[OF U ind_U w w_U] ind_wU by auto
  hence vwU: "?v \<oplus>\<^sub>v w \<notin> span (set us)" using adjust_not_in_span[OF w U dist_U] by auto

  have "w \<notin> span (set (us@ws))" using lin_dep_iff_in_span[OF _ ind_UW] dist ind by auto
  hence span: "?v \<oplus>\<^sub>v w \<notin> span (set (us@ws))" using span_add[OF UW vsUW w] by auto
  hence vwUS: "?v \<oplus>\<^sub>v w \<notin> set (us @ ws)" using span_mem by auto
  hence ind2: "~ lin_dep (set (((?v \<oplus>\<^sub>v w) # us) @ ws))"
    using lin_dep_iff_in_span[OF UW ind_UW vw] span by auto

  have vwU: "set ((?v \<oplus>\<^sub>v w) # us) \<subseteq> carrier\<^sub>v n" using U w dist by auto
  have dist2: "distinct (((?v \<oplus>\<^sub>v w) # us) @ ws)" using dist vwUS by simp

  have orth2: "corthogonal ((adjuster n w us \<oplus>\<^sub>v w) # us)"
    using adjust_orthogonal[OF U corth w wsU].

  show ?case
    using Cons(1)[OF U'def W vwU dist2 ind2] orth2
    using span_union[OF vwU wU gram_schmidt_sub_span[OF w U dist_U] W W] by auto
    
qed simp

lemma gram_schmidt_hd [simp]:
  assumes [simp]: "w : carrier\<^sub>v n" shows "hd (gram_schmidt n (w#ws)) = w"
  unfolding gram_schmidt_code by simp

theorem gram_schmidt_result:
  assumes ws: "set ws \<subseteq> carrier\<^sub>v n"
    and dist: "distinct ws"
    and ind: "~ lin_dep (set ws)"
    and us: "us = gram_schmidt n ws"
  shows "span (set ws) = span (set us)"
    and "corthogonal us"
    and "set us \<subseteq> carrier\<^sub>v n"
    and "length us = length ws"
proof -
  have main: "gram_schmidt_sub n [] ws = rev us"
    using us unfolding gram_schmidt_def
    using gram_schmidt_sub_eq by auto
  have orth: "corthogonal []" by auto
  have "span (set ws) = span (set (rev us))"
   and orth2: "corthogonal (rev us)"
   and "set us \<subseteq> carrier\<^sub>v n"
   and "length us = length ws"
    using gram_schmidt_sub_result[OF main ws]
    by (auto simp: assms orth)
  thus "span (set ws) = span (set us)" by simp
  show "set us \<subseteq> carrier\<^sub>v n" by fact
  show "length us = length ws" by fact
  show "corthogonal us"
    using corthogonal_distinct[OF orth2] unfolding distinct_rev
    using corthogonal_sort[OF _ set_rev orth2] by auto
qed


end

end