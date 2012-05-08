theory StutterEquivalence
imports Samplers

begin

section {* Stuttering Equivalence *}

text {*
  Stuttering equivalence of two sequences is formally defined as the equality
  of their maximally reduced versions.
*}

definition stutter_equiv  (infix "\<approx>" 50) where
  "\<sigma> \<approx> \<tau> \<equiv> \<sigma> \<circ> (max_stutter_sampler \<sigma>) = \<tau> \<circ> (max_stutter_sampler \<tau>)"

text {*
  Stuttering equivalence is an equivalence relation.
*}

lemma stutter_equiv_refl: "\<sigma> \<approx> \<sigma>"
  unfolding stutter_equiv_def ..

lemma stutter_equiv_sym [sym]: "\<sigma> \<approx> \<tau> \<Longrightarrow> \<tau> \<approx> \<sigma>"
  unfolding stutter_equiv_def by (rule sym)

lemma stutter_equiv_trans [trans]: "\<rho> \<approx> \<sigma> \<Longrightarrow> \<sigma> \<approx> \<tau> \<Longrightarrow> \<rho> \<approx> \<tau>"
  unfolding stutter_equiv_def by simp

text {*
  In particular, any stutter-reduced sequence is stuttering equivalent
  to the original one.
*}
lemma reduced_stutter_equiv:
  assumes "stutter_sampler f \<sigma>"
  shows "\<sigma> \<circ> f \<approx> \<sigma>"
  using assms unfolding stutter_equiv_def by (rule sym[OF sample_max_sample])

text {*
  For proving stuttering equivalence of two sequences, it is enough
  to exhibit two arbitrary sampling functions that equalize the reductions
  of the sequences. This can be more convenient than computing the
  maximal stutter-reduced version of the sequences.
*}

lemma stutter_equivI:
  assumes f: "stutter_sampler f \<sigma>" and g: "stutter_sampler g \<tau>" 
      and eq: "\<sigma> \<circ> f = \<tau> \<circ> g"
  shows "\<sigma> \<approx> \<tau>"
proof -
  from f have "\<sigma> \<circ> (max_stutter_sampler \<sigma>) = 
               \<sigma> \<circ> f \<circ> (max_stutter_sampler (\<sigma> \<circ> f))"
    by (rule sample_max_sample)
  also from eq have "... = \<tau> \<circ> g \<circ> (max_stutter_sampler (\<tau> \<circ> g))"
    by simp
  also from g have "... = \<tau> \<circ> (max_stutter_sampler \<tau>)"
    by (rule sym[OF sample_max_sample])
  finally show ?thesis
    unfolding stutter_equiv_def .
qed

text {*
  The corresponding elimination rule is easy to prove, given that the
  maximal stuttering sampling function is a stuttering sampling function.
*}

lemma stutter_equivE:
  assumes eq: "\<sigma> \<approx> \<tau>"
  and p: "\<And>f g. \<lbrakk> stutter_sampler f \<sigma>; stutter_sampler g \<tau>; \<sigma> \<circ> f = \<tau> \<circ> g \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (rule p)
  from eq show "\<sigma> \<circ> (max_stutter_sampler \<sigma>) = \<tau> \<circ> (max_stutter_sampler \<tau>)"
    unfolding stutter_equiv_def .
qed (rule max_stutter_sampler)+

text {*
  Therefore we get the following alternative characterization: two
  sequences are stuttering equivalent iff there are stuttering sampling
  functions that equalize the two sequences.
*}
lemma stutter_equiv_eq:
  "\<sigma> \<approx> \<tau> = (\<exists>f g. stutter_sampler f \<sigma> \<and> stutter_sampler g \<tau> \<and> \<sigma> \<circ> f = \<tau> \<circ> g)"
  by (blast intro: stutter_equivI elim: stutter_equivE)

text {*
  The initial elements of stutter equivalent sequences are equal.
*}
lemma stutter_equiv_0:
  assumes "\<sigma> \<approx> \<tau>"
  shows "\<sigma> 0 = \<tau> 0"
using assms proof (rule stutter_equivE)
  fix f g
  assume f: "stutter_sampler f \<sigma>" and g: "stutter_sampler g \<tau>"
     and eq: "\<sigma> \<circ> f = \<tau> \<circ> g"
  from eq have "\<sigma> (f 0) = \<tau> (g 0)" by (rule o_eq_dest)
  with f g show ?thesis by (simp add: stutter_sampler_0)
qed

text {*
  Given any stuttering sampling function @{text f} for sequence @{text "\<sigma>"},
  any suffix of @{text "\<sigma>"} starting at index @{text "f n"} is stuttering
  equivalent to the suffix of the stutter-reduced version of @{text "\<sigma>"}
  starting at @{text "n"}.
*}
lemma suffix_stutter_equiv:
  assumes f: "stutter_sampler f \<sigma>"
  shows "\<sigma>[f n ..] \<approx> (\<sigma> \<circ> f)[n ..]"
proof -
  from f have "stutter_sampler (\<lambda>k. f (n+k) - f n) (\<sigma>[f n ..])"
    by (rule stutter_sampler_suffix)
  moreover
  have "stutter_sampler id ((\<sigma> \<circ> f)[n ..])"
    by (rule id_stutter_sampler)
  moreover
  have "(\<sigma>[f n ..]) \<circ> (\<lambda>k. f (n+k) - f n) = ((\<sigma> \<circ> f)[n ..]) \<circ> id"
  proof (rule ext, auto)
    fix i
    from f[THEN stutter_sampler_mono, THEN strict_mono_mono]
    have "f n \<le> f (n+i)" by (rule monoD) simp
    thus "\<sigma> (f n + (f (n+i) - f n)) = \<sigma> (f (n+i))" by simp
  qed
  ultimately show ?thesis
    by (rule stutter_equivI)
qed

text {*
  Given a stuttering sampling function @{text f} and a point @{text "n"}
  within the interval from @{text "f k"} to @{text "f (k+1)"}, the suffix
  starting at @{text b} is stuttering equivalent to the suffix starting
  at @{text "f k"}.
*}
lemma stutter_equiv_within_interval:
  assumes f: "stutter_sampler f \<sigma>"
      and lo: "f k \<le> n" and hi: "n < f (Suc k)"
  shows "\<sigma>[n ..] \<approx> \<sigma>[f k ..]"
proof -
  have "stutter_sampler id (\<sigma>[n ..])" by (rule id_stutter_sampler)
  moreover
  from lo have "stutter_sampler (\<lambda>i. if i=0 then 0 else n + i - f k) (\<sigma>[f k ..])"
    (is "stutter_sampler ?f _")
  proof (auto simp: stutter_sampler_def strict_mono_def)
    fix i
    assume i: "i < Suc n - f k"
    from f show "\<sigma> (f k + i) = \<sigma> (f k)"
    proof (rule stutter_sampler_between)
      from i hi show "f k + i < f (Suc k)" by simp
    qed simp
  qed
  moreover
  have "(\<sigma>[n ..]) \<circ> id = (\<sigma>[f k ..]) \<circ> ?f"
  proof (rule ext, auto)
    from f lo hi show "\<sigma> n = \<sigma> (f k)" by (rule stutter_sampler_between)
  next
    fix i
    from lo show "\<sigma> (n+i) = \<sigma> (f k + (n + i - f k))" by simp
  qed
  ultimately show ?thesis by (rule stutter_equivI)
qed

text {*
  Given two stuttering equivalent sequences, for every suffix of one there
  is a stuttering-equivalent suffix of the other.
*}
theorem stutter_equiv_suffixes_left:
  assumes "\<sigma> \<approx> \<tau>"
  obtains m where "\<sigma>[m..] \<approx> \<tau>[n..]"
using assms proof (rule stutter_equivE)
  fix f g
  assume f: "stutter_sampler f \<sigma>"
     and g: "stutter_sampler g \<tau>"
     and eq: "\<sigma> \<circ> f = \<tau> \<circ> g"
  from g obtain k where k: "g k \<le> n" "n < g (Suc k)"
    by (rule stutter_sampler_interval)
  with g have "\<tau>[n..] \<approx> \<tau>[g k ..]"
    by (rule stutter_equiv_within_interval)
  also from g have "... \<approx> (\<tau> \<circ> g)[k ..]"
    by (rule suffix_stutter_equiv)
  also from eq have "... = (\<sigma> \<circ> f)[k ..]"
    by simp
  also from f have "... \<approx> \<sigma>[f k ..]"
    by (rule suffix_stutter_equiv[THEN stutter_equiv_sym])
  finally have "\<sigma>[f k ..] \<approx> \<tau>[n ..]"
    by (rule stutter_equiv_sym)
  with that show ?thesis .
qed

theorem stutter_equiv_suffixes_right:
  assumes "\<sigma> \<approx> \<tau>"
  obtains n where "\<sigma>[m..] \<approx> \<tau>[n..]"
proof -
  from assms have "\<tau> \<approx> \<sigma>" 
    by (rule stutter_equiv_sym)
  then obtain n where "\<tau>[n..] \<approx> \<sigma>[m..]" 
    by (rule stutter_equiv_suffixes_left)
  with that show ?thesis 
    by (blast dest: stutter_equiv_sym)
qed

text {*
  In particular, if @{text "\<sigma>"} and @{text "\<tau>"} are stutter equivalent then
  every element that occurs in one sequence also occurs in the other.
*}
lemma stutter_equiv_element_left:
  assumes "\<sigma> \<approx> \<tau>"
  obtains m where "\<sigma> m = \<tau> n"
proof -
  from assms obtain m where "\<sigma>[m..] \<approx> \<tau>[n..]"
    by (rule stutter_equiv_suffixes_left)
  with that show ?thesis
    by (auto dest: stutter_equiv_0)
qed

lemma stutter_equiv_element_right:
  assumes "\<sigma> \<approx> \<tau>"
  obtains n where "\<sigma> m = \<tau> n"
proof -
  from assms obtain n where "\<sigma>[m..] \<approx> \<tau>[n..]"
    by (rule stutter_equiv_suffixes_right)
  with that show ?thesis
    by (auto dest: stutter_equiv_0)
qed


end (* theory StutterEquivalence *)
