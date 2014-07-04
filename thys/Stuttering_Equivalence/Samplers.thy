theory Samplers
imports Main
begin

section {* Utility Lemmas *}

text {*
  The following lemmas about strictly monotonic functions could go
  to the standard library of Isabelle/HOL.
*}

text {*
  Strongly monotonic functions over the integers grow without bound.
*}
lemma strict_mono_exceeds:
  assumes f: "strict_mono (f::nat \<Rightarrow> nat)"
  shows "\<exists>k. n < f k"
proof (induct n)
  from f have "f 0 < f 1" by (rule strict_monoD) simp
  hence "0 < f 1" by simp
  thus "\<exists>k. 0 < f k" ..
next
  fix n
  assume "\<exists>k. n < f k"
  then obtain k where "n < f k" ..
  hence "Suc n \<le> f k" by simp
  also from f have "f k < f (Suc k)" by (rule strict_monoD) simp
  finally show "\<exists>k. Suc n < f k" ..
qed

text {*
  More precisely, any natural number @{text "n \<ge> f 0"} lies in the interval
  between @{text "f k"} and @{text "f (Suc k)"}, for some @{text k}.
*}
lemma strict_mono_interval:
  assumes f: "strict_mono (f::nat \<Rightarrow> nat)" and n: "f 0 \<le> n"
  obtains k where "f k \<le> n" and "n < f (Suc k)"
proof -
  from f[THEN strict_mono_exceeds] obtain m where m: "n < f m" ..
  have "m \<noteq> 0"
  proof
    assume "m = 0"
    with m n show "False" by simp
  qed
  with m obtain m' where m': "n < f (Suc m')" by (auto simp: gr0_conv_Suc)
  let ?k = "LEAST k. n < f (Suc k)"
  from m' have 1: "n < f (Suc ?k)" by (rule LeastI)
  have "f ?k \<le> n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence k: "n < f ?k" by simp
    show "False"
    proof (cases "?k")
      case 0 with k n show "False" by simp
    next
      case Suc with k show "False" by (auto dest: Least_le)
    qed
  qed
  with 1 that show ?thesis by simp
qed

lemma strict_mono_comp:
  assumes g: "strict_mono (g::'a::order \<Rightarrow> 'b::order)"
      and f: "strict_mono (f::'b::order \<Rightarrow> 'c::order)"
  shows "strict_mono (f \<circ> g)"
  using assms by (auto simp: strict_mono_def)


text {*
  We represent @{text \<omega>}-words as functions of type @{text "nat \<Rightarrow> 'a"}.
  Suffixes of @{text \<omega>}-words are simply obtained by index shifting,
  and we introduce a convenient notation.
*}

definition suffix :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)"   ("_[_ ..]" [80, 15] 80) where
  "\<sigma>[n..] \<equiv> \<lambda>i. \<sigma> (n + i)"

lemma suffix_elt [simp]: "(\<sigma>[n..]) i = \<sigma> (n+i)"
  by (simp add: suffix_def)

lemma suffix_0 [simp]: "\<sigma>[0..] = \<sigma>"
  by (simp add: suffix_def)

lemma suffix_suffix [simp]: "\<sigma>[n..][m..] = \<sigma>[n+m ..]"
  by (simp add: suffix_def add.assoc)


section {* Stuttering Sampling Functions *}

text {*
  Given an @{text \<omega>}-sequence @{text "\<sigma>"}, a stuttering sampling function 
  is a strictly monotonic function @{text "f::nat \<Rightarrow> nat"} such that
  @{text "f 0 = 0"} and for all @{text i} and all @{text "f i \<le> k < f (i+1)"},
  the elements @{text "\<sigma> k"} are the same. In other words, @{text f} skips some
  (but not necessarily all) stuttering steps, but never skips a non-stuttering step.
  Given such @{text "\<sigma>"} and @{text f}, the (stuttering-)sampled
  reduction of @{text "\<sigma>"} is the sequence of elements of @{text "\<sigma>"} at the
  indices @{text "f i"}, which can simply be written as @{text "\<sigma> \<circ> f"}.
*}


subsection {* Definition and elementary properties *}

definition stutter_sampler where
  -- {* f is a stuttering sampling function for @{text "\<sigma>"} *}
  "stutter_sampler (f::nat \<Rightarrow> nat) \<sigma> \<equiv>
     f 0 = 0
   \<and> strict_mono f
   \<and> (\<forall>k n. f k < n \<and> n < f (Suc k) \<longrightarrow> \<sigma> n = \<sigma> (f k))"

lemma stutter_sampler_0: "stutter_sampler f \<sigma> \<Longrightarrow> f 0 = 0"
  by (simp add: stutter_sampler_def)

lemma stutter_sampler_mono: "stutter_sampler f \<sigma> \<Longrightarrow> strict_mono f"
  by (simp add: stutter_sampler_def)

lemma stutter_sampler_between:
  assumes f: "stutter_sampler f \<sigma>"
      and lo: "f k \<le> n" and hi: "n < f (Suc k)"
    shows "\<sigma> n = \<sigma> (f k)"
  using assms by (auto simp: stutter_sampler_def less_le)

lemma stutter_sampler_interval:
  assumes f: "stutter_sampler f \<sigma>"
  obtains k where "f k \<le> n" and "n < f (Suc k)"
using f[THEN stutter_sampler_mono] proof (rule strict_mono_interval)
  from f show "f 0 \<le> n" by (simp add: stutter_sampler_0)
qed

text {*
  The identity function is a stuttering sampling function for any @{text "\<sigma>"}.
*}
lemma id_stutter_sampler [iff]: "stutter_sampler id \<sigma>"
  by (auto simp: stutter_sampler_def strict_mono_def)

text {*
  Stuttering sampling functions compose, sort of.
*}
lemma stutter_sampler_comp:
  assumes f: "stutter_sampler f \<sigma>"
      and g: "stutter_sampler g (\<sigma> \<circ> f)"
  shows "stutter_sampler (f \<circ> g) \<sigma>"
proof (auto simp: stutter_sampler_def)
  from f g show "f (g 0) = 0" by (simp add: stutter_sampler_0)
next
  from g[THEN stutter_sampler_mono] f[THEN stutter_sampler_mono]
  show "strict_mono (f \<circ> g)" by (rule strict_mono_comp)
next
  fix i k
  assume lo: "f (g i) < k" and hi: "k < f (g (Suc i))"
  from f obtain m where 1: "f m \<le> k" and 2: "k < f (Suc m)"
    by (rule stutter_sampler_interval)
  with f have 3: "\<sigma> k = \<sigma> (f m)" by (rule stutter_sampler_between)
  from lo 2 have "f (g i) < f (Suc m)" by simp
  with f[THEN stutter_sampler_mono] have 4: "g i \<le> m" by (simp add: strict_mono_less)
  from 1 hi have "f m < f (g (Suc i))" by simp
  with f[THEN stutter_sampler_mono] have 5: "m < g (Suc i)"by (simp add: strict_mono_less)
  from g 4 5 have "(\<sigma> \<circ> f) m = (\<sigma> \<circ> f) (g i)" by (rule stutter_sampler_between)
  with 3 show "\<sigma> k = \<sigma> (f (g i))" by simp
qed

text {*
  Stuttering sampling functions can be extended to suffixes.
*}
lemma stutter_sampler_suffix:
  assumes f: "stutter_sampler f \<sigma>"
  shows "stutter_sampler (\<lambda>k. f (n+k) - f n) (\<sigma>[f n ..])"
proof (auto simp: stutter_sampler_def strict_mono_def)
  fix i j
  assume ij: "(i::nat) < j"
  from f have mono: "strict_mono f" by (rule stutter_sampler_mono)

  from mono[THEN strict_mono_mono] have "f n \<le> f (n+i)"
    by (rule monoD) simp
  moreover
  from mono[THEN strict_mono_mono] have "f n \<le> f (n+j)"
    by (rule monoD) simp
  moreover
  from mono ij have "f (n+i) < f (n+j)" by (auto intro: strict_monoD)
  ultimately
  show "f (n+i) - f n < f (n+j) - f n" by simp
next
  fix i k
  assume lo: "f (n+i) - f n < k" and hi: "k < f (Suc (n+i)) - f n"
  from lo have "f (n+i) \<le> f n + k" by simp
  moreover
  from hi have "f n + k < f (Suc (n + i))" by simp
  moreover
  from f[THEN stutter_sampler_mono, THEN strict_mono_mono]
  have "f n \<le> f (n+i)" by (rule monoD) simp
  ultimately show "\<sigma> (f n + k) = \<sigma> (f n + (f (n+i) - f n))" 
    by (auto dest: stutter_sampler_between[OF f])
qed


subsection {* Preservation of properties through stuttering sampling *}

text {*
  Stuttering sampling preserves the initial element of the sequence, as well as
  the presence and relative ordering of different elements.
*}

lemma stutter_sampled_0:
  assumes "stutter_sampler f \<sigma>"
  shows "\<sigma> (f 0) = \<sigma> 0"
  using assms[THEN stutter_sampler_0] by simp

lemma stutter_sampled_in_range:
  assumes f: "stutter_sampler f \<sigma>" and s: "s \<in> range \<sigma>"
  shows "s \<in> range (\<sigma> \<circ> f)"
proof -
  from s obtain n where n: "\<sigma> n = s" by auto
  from f obtain k where "f k \<le> n" "n < f (Suc k)" by (rule stutter_sampler_interval)
  with f have "\<sigma> n = \<sigma> (f k)" by (rule stutter_sampler_between)
  with n show ?thesis by auto
qed

lemma stutter_sampled_range:
  assumes "stutter_sampler f \<sigma>"
  shows "range (\<sigma> \<circ> f) = range \<sigma>"
  using assms by (auto intro: stutter_sampled_in_range)

lemma stutter_sampled_precedence:
  assumes f: "stutter_sampler f \<sigma>" and ij: "i \<le> j"
  obtains k l where "k \<le> l" "\<sigma> (f k) = \<sigma> i" "\<sigma> (f l) = \<sigma> j"
proof -
  from f obtain k where k: "f k \<le> i" "i < f (Suc k)" by (rule stutter_sampler_interval)
  with f have 1: "\<sigma> i = \<sigma> (f k)" by (rule stutter_sampler_between)
  from f obtain l where l: "f l \<le> j" "j < f (Suc l)" by (rule stutter_sampler_interval)
  with f have 2: "\<sigma> j = \<sigma> (f l)" by (rule stutter_sampler_between)
  from k l ij have "f k < f (Suc l)" by simp
  with f[THEN stutter_sampler_mono] have "k \<le> l" by (simp add: strict_mono_less)
  with 1 2 that show ?thesis by simp
qed


subsection {* Maximal stuttering sampling *}

text {*
  We define a particular sampling function that is maximal in the sense that it
  eliminates all finite stuttering. If a sequence ends with infinite stuttering
  then it behaves as the identity over the (maximal such) suffix.
*}

fun max_stutter_sampler where
  "max_stutter_sampler \<sigma> 0 = 0"
| "max_stutter_sampler \<sigma> (Suc n) =
    (let prev = max_stutter_sampler \<sigma> n
     in  if (\<forall>k > prev. \<sigma> k = \<sigma> prev)
         then Suc prev
         else (LEAST k. prev < k \<and> \<sigma> k \<noteq> \<sigma> prev))"

text {*
  @{text max_stutter_sampler} is indeed a stuttering sampling function.
*}
lemma max_stutter_sampler: 
  "stutter_sampler (max_stutter_sampler \<sigma>) \<sigma>" (is "stutter_sampler ?ms _")
proof -
  have "?ms 0 = 0" by simp
  moreover
  have "\<forall>n. ?ms n < ?ms (Suc n)"
  proof
    fix n
    show "?ms n < ?ms (Suc n)" (is "?prev < ?next")
    proof (cases "\<forall>k > ?prev. \<sigma> k = \<sigma> ?prev")
      case True thus ?thesis by (simp add: Let_def)
    next
      case False
      hence "\<exists>k. ?prev < k \<and> \<sigma> k \<noteq> \<sigma> ?prev" by simp
      from this[THEN LeastI_ex] 
      have "?prev < (LEAST k. ?prev < k \<and> \<sigma> k \<noteq> \<sigma> ?prev)" ..
      with False show ?thesis by (simp add: Let_def)
    qed
  qed
  hence "strict_mono ?ms"
    unfolding strict_mono_def by (blast intro: lift_Suc_mono_less)
  moreover
  have "\<forall>n k. ?ms n < k \<and> k < ?ms (Suc n) \<longrightarrow> \<sigma> k = \<sigma> (?ms n)"
  proof (clarify)
    fix n k
    assume lo: "?ms n < k" (is "?prev < k")
       and hi: "k < ?ms (Suc n)" (is "k < ?next")
    show "\<sigma> k = \<sigma> ?prev"
    proof (cases "\<forall>k > ?prev. \<sigma> k = \<sigma> ?prev")
      case True
      hence "?next = Suc ?prev" by (simp add: Let_def)
      with lo hi show ?thesis by simp  -- {* no room for intermediate index *}
    next
      case False
      hence "?next = (LEAST k. ?prev < k \<and> \<sigma> k \<noteq> \<sigma> ?prev)"
        by (auto simp add: Let_def)
      with lo hi show ?thesis by (auto dest: not_less_Least)
    qed
  qed
  ultimately show ?thesis unfolding stutter_sampler_def by blast
qed

text {*
  We write @{text "\<natural>\<sigma>"} for the sequence @{text "\<sigma>"} sampled by the
  maximal stuttering sampler. Also, a sequence is \emph{stutter free}
  if it contains no finite stuttering: whenever two subsequent
  elements are equal then all subsequent elements are the same.
*}
definition stutter_reduced ("\<natural>_" [100] 100) where
  "\<natural>\<sigma> = \<sigma> \<circ> (max_stutter_sampler \<sigma>)"

definition stutter_free where
  "stutter_free \<sigma> \<equiv> \<forall>k. \<sigma> (Suc k) = \<sigma> k \<longrightarrow> (\<forall>n>k. \<sigma> n = \<sigma> k)"

lemma stutter_freeI:
  assumes "\<And>k n. \<lbrakk>\<sigma> (Suc k) = \<sigma> k; n>k\<rbrakk> \<Longrightarrow> \<sigma> n = \<sigma> k"
  shows "stutter_free \<sigma>"
  using assms unfolding stutter_free_def by blast

lemma stutter_freeD:
  assumes "stutter_free \<sigma>" and "\<sigma> (Suc k) = \<sigma> k" and "n>k"
  shows "\<sigma> n = \<sigma> k"
  using assms unfolding stutter_free_def by blast

text {*
  Any suffix of a stutter free sequence is itself stutter free.
*}
lemma stutter_free_suffix: 
  assumes sigma: "stutter_free \<sigma>"
  shows "stutter_free (\<sigma>[k..])"
proof (rule stutter_freeI)
  fix j n
  assume j: "(\<sigma>[k..]) (Suc j) = (\<sigma>[k..]) j" and n: "j < n"
  from j have "\<sigma> (Suc (k+j)) = \<sigma> (k+j)" by simp
  moreover from n have "k+n > k+j" by simp
  ultimately have "\<sigma> (k+n) = \<sigma> (k+j)" by (rule stutter_freeD[OF sigma])
  thus "(\<sigma>[k..]) n = (\<sigma>[k..]) j" by simp
qed

lemma stutter_reduced_0: "(\<natural>\<sigma>) 0 = \<sigma> 0"
  by (simp add: stutter_reduced_def stutter_sampled_0 max_stutter_sampler)

lemma stutter_free_reduced:
  assumes sigma: "stutter_free \<sigma>"
  shows "\<natural>\<sigma> = \<sigma>"
proof -
  {
    fix n
    have "max_stutter_sampler \<sigma> n = n" (is "?ms n = n")
    proof (induct n)
      show "?ms 0 = 0" by simp
    next
      fix n
      assume ih: "?ms n = n"
      show "?ms (Suc n) = Suc n"
      proof (cases "\<sigma> (Suc n) = \<sigma> (?ms n)")
        case True
        with ih have "\<sigma> (Suc n) = \<sigma> n" by simp
        with sigma have "\<forall>k > n. \<sigma> k = \<sigma> n"
          unfolding stutter_free_def by blast
        with ih show ?thesis by (simp add: Let_def)
      next
        case False
        with ih have "(LEAST k. k>n \<and> \<sigma> k \<noteq> \<sigma> (?ms n)) = Suc n"
          by (auto intro: Least_equality)
        with ih False show ?thesis by (simp add: Let_def)
      qed
    qed
  }
  thus ?thesis by (auto simp: stutter_reduced_def)
qed

text {*
  Whenever two sequence elements at two consecutive sampling points of the 
  maximal stuttering sampler are equal then the sequence stutters infinitely 
  from the first sampling point onwards. In particular, @{text "\<natural>\<sigma>"} is
  stutter free.
*}
lemma max_stutter_sampler_nostuttering:
  assumes stut: "\<sigma> (max_stutter_sampler \<sigma> (Suc k)) = \<sigma> (max_stutter_sampler \<sigma> k)"
      and n: "n > max_stutter_sampler \<sigma> k" (is "_ > ?ms k")
  shows "\<sigma> n = \<sigma> (?ms k)"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  with n have "?ms k < n \<and> \<sigma> n \<noteq> \<sigma> (?ms k)" (is "?diff n") ..
  hence "?diff (LEAST n. ?diff n)" by (rule LeastI)
  with contr have "\<sigma> (?ms (Suc k)) \<noteq> \<sigma> (?ms k)" by (auto simp add: Let_def)
  from this stut show "False" ..
qed

lemma stutter_reduced_stutter_free: "stutter_free (\<natural>\<sigma>)"
proof (rule stutter_freeI)
  fix k n
  assume k: "(\<natural>\<sigma>) (Suc k) = (\<natural>\<sigma>) k" and n: "k < n"
  from n have "max_stutter_sampler \<sigma> k < max_stutter_sampler \<sigma> n"
    using max_stutter_sampler[THEN stutter_sampler_mono, THEN strict_monoD]
    by blast
  with k show "(\<natural>\<sigma>) n = (\<natural>\<sigma>) k"
    unfolding stutter_reduced_def 
    by (auto elim: max_stutter_sampler_nostuttering 
             simp del: max_stutter_sampler.simps)
qed

lemma stutter_reduced_suffix: "\<natural>((\<natural>\<sigma>)[k..]) = (\<natural>\<sigma>)[k..]"
proof (rule stutter_free_reduced)
  have "stutter_free (\<natural>\<sigma>)" by (rule stutter_reduced_stutter_free)
  thus "stutter_free ((\<natural>\<sigma>)[k..])" by (rule stutter_free_suffix)
qed

lemma stutter_reduced_reduced: "\<natural>\<natural>\<sigma> = \<natural>\<sigma>"
  by (rule stutter_reduced_suffix[of "\<sigma>" "0", simplified])

text {*
  One can define a partial order on sampling functions for a given sequence
  @{text "\<sigma>"} by saying that function @{text g} is better than function @{text f}
  if the reduced sequence induced by @{text f} can be further reduced to obtain
  the reduced sequence corresponding to @{text g}, i.e. if there exists a
  stuttering sampling function @{text h} for the reduced sequence @{text "\<sigma> \<circ> f"}
  such that @{text "\<sigma> \<circ> f \<circ> h = \<sigma> \<circ> g"}. (Note that @{text "f \<circ> h"} is indeed a stuttering
  sampling function for @{text "\<sigma>"}, by theorem @{text "stutter_sampler_comp"}.)

  We do not formalize this notion but prove that @{text "max_stutter_sampler \<sigma>"}
  is the best sampling function according to this order.
*}

theorem sample_max_sample:
  assumes f: "stutter_sampler f \<sigma>"
  shows "\<natural>(\<sigma> \<circ> f) = \<natural>\<sigma>"
proof -
  let ?mss = "max_stutter_sampler \<sigma>"
  let ?mssf = "max_stutter_sampler (\<sigma> \<circ> f)"
  from f have mssf: "stutter_sampler (f \<circ> ?mssf) \<sigma>"
    by (blast intro: stutter_sampler_comp max_stutter_sampler)
  txt {*
    The following is the core invariant of the proof: the sampling functions
    @{text "max_stutter_sampler \<sigma>"} and @{text "f \<circ> (max_stutter_sampler (\<sigma> \<circ> f))"}
    work in lock-step (i.e., sample the same points), except if @{text "\<sigma>"} ends
    in infinite stuttering, at which point function @{text f} may make larger
    steps than the maximal sampling functions.
  *}
  {
    fix k
    have "  ?mss k = f (?mssf k)
          \<or> ?mss k \<le> f (?mssf k) \<and> (\<forall>n \<ge> ?mss k. \<sigma> (?mss k) = \<sigma> n)"
          (is "?P k" is "?A k \<or> ?B k")
    proof (induct k)
      from f mssf have "?mss 0 = f (?mssf 0)"
        by (simp add: max_stutter_sampler stutter_sampler_0)
      thus "?P 0" ..
    next
      fix k
      assume ih: "?P k"
      have b: "?B k \<longrightarrow> ?B (Suc k)"
      proof
        assume 0: "?B k" hence 1: "?mss k \<le> f (?mssf k)" ..
        (* NB: For some reason "... hence 1: ... and 2: ..." cannot be proved *)
        from 0 have 2: "\<forall>n \<ge> ?mss k. \<sigma> (?mss k) = \<sigma> n" ..
        hence "\<forall>n > ?mss k. \<sigma> (?mss k) = \<sigma> n" by auto
        hence "\<forall>n > ?mss k. \<sigma> n = \<sigma> (?mss k)" by auto
        hence 3: "?mss (Suc k) = Suc (?mss k)" by (simp add: Let_def)
        with 2 have "\<sigma> (?mss k) = \<sigma> (?mss (Suc k))"
          by (auto simp del: max_stutter_sampler.simps)
        from sym[OF this] 2 3 have "\<forall>n \<ge> ?mss (Suc k). \<sigma> (?mss (Suc k)) = \<sigma> n"
          by (auto simp del: max_stutter_sampler.simps)
        moreover
        from mssf[THEN stutter_sampler_mono, THEN strict_monoD] 
        have "f (?mssf k) < f (?mssf (Suc k))"
          by (simp del: max_stutter_sampler.simps)
        with 1 3 have "?mss (Suc k) \<le> f (?mssf (Suc k))"
          by (simp del: max_stutter_sampler.simps)
        ultimately show "?B (Suc k)" by blast
      qed
      from ih show "?P (Suc k)"
      proof
        assume a: "?A k"
        show ?thesis
        proof (cases "\<forall>n > ?mss k. \<sigma> n = \<sigma> (?mss k)")
          case True
          hence "\<forall>n \<ge> ?mss k. \<sigma> (?mss k) = \<sigma> n" by (auto simp: le_less)
          with a have "?B k" by simp
          with b show ?thesis by (simp del: max_stutter_sampler.simps)
        next
          case False
          hence diff: "\<sigma> (?mss (Suc k)) \<noteq> \<sigma> (?mss k)"
            by (blast dest: max_stutter_sampler_nostuttering)
          have "?A (Suc k)"
          proof (rule antisym)
            show "f (?mssf (Suc k)) \<le> ?mss (Suc k)"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence contr: "?mss (Suc k) < f (?mssf (Suc k))" by simp
              from mssf have "\<sigma> (?mss (Suc k)) = \<sigma> ((f \<circ> ?mssf) k)"
              proof (rule stutter_sampler_between)
                from max_stutter_sampler[of "\<sigma>", THEN stutter_sampler_mono]
                have "?mss k < ?mss (Suc k)" by (rule strict_monoD) simp
                with a show "(f \<circ> ?mssf) k \<le> ?mss (Suc k)"
                  by (simp add: o_def del: max_stutter_sampler.simps)
              next
                from contr show "?mss (Suc k) < (f \<circ> ?mssf) (Suc k)" by simp
              qed
              with a have "\<sigma> (?mss (Suc k)) = \<sigma> (?mss k)"
                by (simp add: o_def del: max_stutter_sampler.simps)
              with diff show "False" ..
            qed
          next
            have "\<exists>m > ?mssf k. f m = ?mss (Suc k)"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence contr: "\<forall>i. f ((?mssf k) + Suc i) \<noteq> ?mss (Suc k)" by simp
              {
                fix i
                have "f (?mssf k + i) < ?mss (Suc k)" (is "?F i")
                proof (induct i)
                  from a have "f (?mssf k + 0) = ?mss k" by (simp add: o_def)
                  also from max_stutter_sampler[of "\<sigma>", THEN stutter_sampler_mono] 
                       have "... < ?mss (Suc k)"
                         by (rule strict_monoD) simp
                  finally show "?F 0" .
                next
                  fix i
                  assume ih: "?F i"
                  show "?F (Suc i)"
                  proof (rule ccontr)
                    assume "\<not> ?thesis"
                    then have "?mss (Suc k) \<le> f (?mssf k + Suc i)" 
                      by (simp add: o_def)
                    moreover from contr have "f (?mssf k + Suc i) \<noteq> ?mss (Suc k)"
                      by blast
                    ultimately have i: "?mss (Suc k) < f (?mssf k + Suc i)"
                      by (simp add: less_le)
                    from f have "\<sigma> (?mss (Suc k)) = \<sigma> (f (?mssf k + i))"
                    proof (rule stutter_sampler_between)
                      from ih show "f (?mssf k + i) \<le> ?mss (Suc k)" 
                        by (simp add: o_def)
                    next
                      from i show "?mss (Suc k) < f (Suc (?mssf k + i))" 
                        by simp
                    qed
                    also from max_stutter_sampler have "... = \<sigma> (?mss k)"
                    proof (rule stutter_sampler_between)
                      from f[THEN stutter_sampler_mono, THEN strict_mono_mono]
                      have "f (?mssf k) \<le> f (?mssf k + i)" by (rule monoD) simp
                      with a show "?mss k \<le> f (?mssf k + i)" by (simp add: o_def)
                    qed (rule ih)
                    also note diff
                    finally show "False" by simp
                  qed
                qed
              } note bounded = this
              from f[THEN stutter_sampler_mono] 
              have "strict_mono (\<lambda>i. f (?mssf k + i))" 
                by (auto simp: strict_mono_def)
              then obtain i where i: "?mss (Suc k) < f (?mssf k + i)"
                by (blast dest: strict_mono_exceeds)
              from bounded have "f (?mssf k + i) < ?mss (Suc k)" .
              with i show "False" by (simp del: max_stutter_sampler.simps)
            qed
            then obtain m where m: "m > ?mssf k" and m': "f m = ?mss (Suc k)"
              by blast
            show "?mss (Suc k) \<le> f (?mssf (Suc k))"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence contr: "f (?mssf (Suc k)) < ?mss (Suc k)" by simp
              from mssf[THEN stutter_sampler_mono]
              have "(f \<circ> ?mssf) k < (f \<circ> ?mssf) (Suc k)" 
                by (rule strict_monoD) simp
              with a have "?mss k \<le> f (?mssf (Suc k))"
                by (simp add: o_def)
              from this contr have "\<sigma> (f (?mssf (Suc k))) = \<sigma> (?mss k)"
                by (rule stutter_sampler_between[OF max_stutter_sampler])
              with a have stut: "(\<sigma> \<circ> f) (?mssf (Suc k)) = (\<sigma> \<circ> f) (?mssf k)"
                by (simp add: o_def)
              from this m have "(\<sigma> \<circ> f) m = (\<sigma> \<circ> f) (?mssf k)"
                by (blast intro: max_stutter_sampler_nostuttering)
              with diff m' a show "False"
                by (simp add: o_def)
            qed
          qed
          thus ?thesis ..
        qed
      next
        assume "?B k" with b show ?thesis by (simp del: max_stutter_sampler.simps)
      qed
    qed
  }
  hence "\<natural>\<sigma> = \<natural>(\<sigma> \<circ> f)" unfolding stutter_reduced_def by force
  thus ?thesis by (rule sym)
qed


end  (* theory Samplers *)

