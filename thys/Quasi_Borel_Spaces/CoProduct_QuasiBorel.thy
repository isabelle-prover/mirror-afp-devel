(*  Title:   CoProduct_QuasiBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsubsection \<open> Countable Coproduct Spaces \<close>
theory CoProduct_QuasiBorel

imports
 "Product_QuasiBorel"
 "Binary_CoProduct_QuasiBorel"
begin

definition coprod_qbs_Mx :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) set" where
"coprod_qbs_Mx I X \<equiv> { \<lambda>r. (f r, \<alpha> (f r) r) |f \<alpha>. f \<in> real_borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>i\<in>range f. \<alpha> i \<in> qbs_Mx (X i))}"

lemma coprod_qbs_MxI:
  assumes "f \<in> real_borel \<rightarrow>\<^sub>M count_space I"
      and "\<And>i. i \<in> range f \<Longrightarrow> \<alpha> i \<in> qbs_Mx (X i)"
    shows "(\<lambda>r. (f r, \<alpha> (f r) r)) \<in> coprod_qbs_Mx I X"
  using assms unfolding coprod_qbs_Mx_def by blast

definition coprod_qbs_Mx' :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) set" where
"coprod_qbs_Mx' I X \<equiv> { \<lambda>r. (f r, \<alpha> (f r) r) |f \<alpha>. f \<in> real_borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>i. (i \<in> range f \<or> qbs_space (X i) \<noteq> {}) \<longrightarrow> \<alpha> i \<in> qbs_Mx (X i))}"

lemma coproduct_qbs_Mx_eq:
 "coprod_qbs_Mx I X = coprod_qbs_Mx' I X"
proof auto
  fix \<alpha>
  assume "\<alpha>  \<in> coprod_qbs_Mx I X"
  then obtain f \<beta> where hfb:
    "f \<in> real_borel \<rightarrow>\<^sub>M count_space I"
    "\<And>i. i \<in> range f \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)" "\<alpha> = (\<lambda>r. (f r, \<beta> (f r) r))"
    unfolding coprod_qbs_Mx_def by blast
  define \<beta>' where "\<beta>' \<equiv> (\<lambda>i. if i \<in> range f then \<beta> i
                              else if qbs_space (X i) \<noteq> {} then (SOME \<gamma>. \<gamma> \<in> qbs_Mx (X i))
                              else \<beta> i)"
  have 1:"\<alpha> = (\<lambda>r. (f r, \<beta>' (f r) r))"
    by(simp add: hfb(3) \<beta>'_def)
  have 2:"\<And>i. qbs_space (X i) \<noteq> {} \<Longrightarrow> \<beta>' i \<in> qbs_Mx (X i)"
  proof -
    fix i
    assume hne:"qbs_space (X i) \<noteq> {}"
    then obtain x where "x \<in> qbs_space (X i)" by auto
    hence "(\<lambda>r. x) \<in> qbs_Mx (X i)" by auto
    thus "\<beta>' i \<in> qbs_Mx (X i)"
      by(cases "i \<in> range f") (auto simp: \<beta>'_def hfb(2) hne intro!: someI2[where a="\<lambda>r. x"])
  qed
  show "\<alpha> \<in> coprod_qbs_Mx' I X"
    using hfb(1,2) 1 2 by(auto simp: coprod_qbs_Mx'_def intro!: exI[where x=f] exI[where x=\<beta>'])
next
  fix \<alpha>
  assume "\<alpha> \<in> coprod_qbs_Mx' I X"
  then obtain f \<beta> where hfb:
    "f \<in> real_borel \<rightarrow>\<^sub>M count_space I"  "\<And>i. qbs_space (X i) \<noteq> {} \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)"
    "\<And>i. i \<in> range f \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)"  "\<alpha> = (\<lambda>r. (f r, \<beta> (f r) r))"
    unfolding coprod_qbs_Mx'_def by blast
  show "\<alpha> \<in> coprod_qbs_Mx I X"
    by(auto simp: hfb(4) intro!: coprod_qbs_MxI[OF hfb(1) hfb(3)])
qed

definition coprod_qbs :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> ('a \<times> 'b) quasi_borel" where
"coprod_qbs I X \<equiv> Abs_quasi_borel (SIGMA i:I. qbs_space (X i), coprod_qbs_Mx I X)"

syntax
 "_coprod_qbs" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a quasi_borel \<Rightarrow> ('i \<times> 'a) quasi_borel" ("(3\<amalg>\<^sub>Q _\<in>_./ _)"  10)
translations
 "\<amalg>\<^sub>Q x\<in>I. M" \<rightleftharpoons> "CONST coprod_qbs I (\<lambda>x. M)"

lemma coprod_qbs_f[simp]: "coprod_qbs_Mx I X \<subseteq> UNIV \<rightarrow> (SIGMA i:I. qbs_space (X i))"
  by(fastforce simp: coprod_qbs_Mx_def dest: measurable_space)

lemma coprod_qbs_closed1: "qbs_closed1 (coprod_qbs_Mx I X)"
proof(rule qbs_closed1I)
  fix \<alpha> f
  assume "\<alpha> \<in> coprod_qbs_Mx I X"
    and 1[measurable]: "f \<in> real_borel \<rightarrow>\<^sub>M real_borel"
  then obtain \<beta> g where ha:
   "\<And>i. i \<in> range g \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)" "\<alpha> = (\<lambda>r. (g r, \<beta> (g r) r))" and [measurable]:"g \<in> real_borel \<rightarrow>\<^sub>M count_space I"
    by(fastforce simp: coprod_qbs_Mx_def)
  then have "\<And>i. i \<in> range g \<Longrightarrow> \<beta> i \<circ> f \<in> qbs_Mx (X i)"
    by simp
  thus "\<alpha> \<circ> f \<in> coprod_qbs_Mx I X"
    by(auto intro!: coprod_qbs_MxI[where f="g \<circ> f" and \<alpha>="\<lambda>i. \<beta> i \<circ> f",simplified comp_def] simp: ha(2) comp_def)
qed

lemma coprod_qbs_closed2: "qbs_closed2 (SIGMA i:I. qbs_space (X i)) (coprod_qbs_Mx I X)"
proof(rule qbs_closed2I,auto)
  fix i x
  assume "i \<in> I" "x \<in> qbs_space (X i)"
  then show "(\<lambda>r. (i,x)) \<in> coprod_qbs_Mx I X"
    by(auto simp: coprod_qbs_Mx_def intro!: exI[where x="\<lambda>r. i"])
qed

lemma coprod_qbs_closed3:
 "qbs_closed3 (coprod_qbs_Mx I X)"
proof(rule qbs_closed3I)
  fix P Fi
  assume h:"\<And>i :: nat. P -` {i} \<in> sets real_borel"
           "\<And>i :: nat. Fi i \<in> coprod_qbs_Mx I X"
  then have "\<forall>i. \<exists>fi \<alpha>i. Fi i = (\<lambda>r. (fi r, \<alpha>i (fi r) r)) \<and> fi \<in> real_borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>j. (j \<in> range fi \<or> qbs_space (X j) \<noteq> {}) \<longrightarrow> \<alpha>i j \<in> qbs_Mx (X j))"
    by(auto simp: coproduct_qbs_Mx_eq coprod_qbs_Mx'_def)
  then obtain fi where
   "\<forall>i. \<exists>\<alpha>i. Fi i = (\<lambda>r. (fi i r, \<alpha>i (fi i r) r)) \<and> fi i \<in> real_borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>j. (j \<in> range (fi i) \<or> qbs_space (X j) \<noteq> {}) \<longrightarrow> \<alpha>i j \<in> qbs_Mx (X j))"
    by(fastforce intro!: choice)
  then obtain \<alpha>i where
  "\<forall>i. Fi i = (\<lambda>r. (fi i r, \<alpha>i i (fi i r) r)) \<and> fi i \<in> real_borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>j. (j \<in> range (fi i) \<or> qbs_space (X j) \<noteq> {}) \<longrightarrow> \<alpha>i i j \<in> qbs_Mx (X j))"
    by(fastforce intro!: choice)
  then have hf:
   "\<And>i. Fi i = (\<lambda>r. (fi i r, \<alpha>i i (fi i r) r))" "\<And>i. fi i \<in> real_borel \<rightarrow>\<^sub>M count_space I" "\<And>i j. j \<in> range (fi i) \<Longrightarrow> \<alpha>i i j \<in> qbs_Mx (X j)" "\<And>i j. qbs_space (X j) \<noteq> {} \<Longrightarrow> \<alpha>i i j \<in> qbs_Mx (X j)"
    by auto

  define f' where "f' \<equiv> (\<lambda>r. fi (P r) r)"
  define \<alpha>' where "\<alpha>' \<equiv> (\<lambda>i r. \<alpha>i (P r) i r)"
  have 1:"(\<lambda>r. Fi (P r) r) = (\<lambda>r. (f' r, \<alpha>' (f' r) r))"
    by(simp add: \<alpha>'_def f'_def hf)
  have "f' \<in> real_borel \<rightarrow>\<^sub>M count_space I"
  proof -
    note [measurable] = separate_measurable[OF h(1)]
    have "(\<lambda>(n,r). fi n r) \<in> count_space UNIV \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M count_space I"
      by(auto intro!: measurable_pair_measure_countable1 simp: hf)
    hence [measurable]:"(\<lambda>(n,r). fi n r) \<in> nat_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M count_space I"
      using measurable_cong_sets[OF sets_pair_measure_cong[OF sets_borel_eq_count_space],of real_borel real_borel]
      by auto
    thus ?thesis
      using measurable_comp[of "\<lambda>r. (P r, r)" _ _ "(\<lambda>(n,r). fi n r)"]
      by(simp add: f'_def)
  qed
  moreover have "\<And>i. i \<in> range f' \<Longrightarrow> \<alpha>' i \<in> qbs_Mx (X i)"
  proof -
    fix i
    assume hi:"i \<in> range f'"
    then obtain r where hr:
     "i = fi (P r) r" by(auto simp: f'_def)
    hence "i \<in> range (fi (P r))" by simp
    hence "\<alpha>i (P r) i \<in> qbs_Mx (X i)" by(simp add: hf)
    hence "qbs_space (X i) \<noteq> {}"
      by(auto simp: qbs_empty_equiv)
    hence "\<And>j. \<alpha>i j i \<in> qbs_Mx (X i)"
      by(simp add: hf(4))
    then show "\<alpha>' i \<in> qbs_Mx (X i)"
      by(auto simp: \<alpha>'_def h(1) intro!: qbs_closed3_dest[of P "\<lambda>j. \<alpha>i j i"])
  qed
  ultimately show "(\<lambda>r. Fi (P r) r) \<in> coprod_qbs_Mx I X"
    by(auto intro!: coprod_qbs_MxI simp: 1)
qed

lemma coprod_qbs_correct: "Rep_quasi_borel (coprod_qbs I X) = (SIGMA i:I. qbs_space (X i), coprod_qbs_Mx I X)"
  unfolding coprod_qbs_def
  using is_quasi_borel_intro[OF coprod_qbs_f coprod_qbs_closed1 coprod_qbs_closed2 coprod_qbs_closed3]
  by(fastforce intro!: Abs_quasi_borel_inverse)

lemma coproduct_qbs_space[simp]: "qbs_space (coprod_qbs I X) = (SIGMA i:I. qbs_space (X i))"
  by(simp add: coprod_qbs_correct qbs_space_def)

lemma coproduct_qbs_Mx[simp]: "qbs_Mx (coprod_qbs I X) = coprod_qbs_Mx I X"
  by(simp add: coprod_qbs_correct qbs_Mx_def)


lemma ini_morphism:
  assumes "j \<in> I"
  shows "(\<lambda>x. (j,x)) \<in> X j \<rightarrow>\<^sub>Q (\<amalg>\<^sub>Q i\<in>I. X i)"
  by(fastforce intro!: qbs_morphismI exI[where x="\<lambda>r. j"] simp: coprod_qbs_Mx_def comp_def assms)

lemma coprod_qbs_canonical1:
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> f i \<in> X i \<rightarrow>\<^sub>Q Y"
    shows  "(\<lambda>(i,x). f i x) \<in> (\<amalg>\<^sub>Q i \<in>I. X i) \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (coprod_qbs I X)"
  then obtain \<beta> g where ha:
   "\<And>i. i \<in> range g \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)" "\<alpha> = (\<lambda>r. (g r, \<beta> (g r) r))" and hg[measurable]:"g \<in> real_borel \<rightarrow>\<^sub>M count_space I"
    by(fastforce simp: coprod_qbs_Mx_def)
  define f' where "f' \<equiv> (\<lambda>i r. f i (\<beta> i r))"
  have "range g \<subseteq> I"
    using measurable_space[OF hg] by auto
  hence 1:"(\<And>i. i \<in> range g \<Longrightarrow> f' i \<in> qbs_Mx Y)"
    using qbs_morphismE(3)[OF assms(2) ha(1),simplified comp_def]
    by(auto simp: f'_def)
  have "(\<lambda>(i, x). f i x) \<circ> \<alpha> = (\<lambda>r. f' (g r) r)"
    by(auto simp: ha(2) f'_def)
  also have "... \<in> qbs_Mx Y"
    by(auto intro!: qbs_closed3_dest2'[OF assms(1) hg,of f',OF 1])
  finally show "(\<lambda>(i, x). f i x) \<circ> \<alpha> \<in> qbs_Mx Y " .
qed

lemma coprod_qbs_canonical1':
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f (i,x)) \<in> X i \<rightarrow>\<^sub>Q Y"
    shows  "f \<in> (\<amalg>\<^sub>Q i \<in>I. X i) \<rightarrow>\<^sub>Q Y"
  using coprod_qbs_canonical1[where f="curry f"] assms by(auto simp: curry_def)


text \<open> $\coprod_{i=0,1} X_i \cong X_1 + X_2$. \<close>
lemma coproduct_binary_coproduct:
 "\<exists>f g. f \<in> (\<amalg>\<^sub>Q i\<in>UNIV. if i then X else Y) \<rightarrow>\<^sub>Q X <+>\<^sub>Q Y \<and> g \<in> X <+>\<^sub>Q Y \<rightarrow>\<^sub>Q (\<amalg>\<^sub>Q i\<in>UNIV. if i then X else Y) \<and>
        g \<circ> f = id \<and> f \<circ> g = id"
proof(auto intro!: exI[where x="\<lambda>(b,z). if b then Inl z else Inr z"] exI[where x="case_sum (\<lambda>z. (True,z)) (\<lambda>z. (False,z))"])
  show "(\<lambda>(b, z). if b then Inl z else Inr z) \<in> (\<amalg>\<^sub>Q i\<in>UNIV. if i then X else Y) \<rightarrow>\<^sub>Q X <+>\<^sub>Q Y"
  proof(rule qbs_morphismI)
    fix \<alpha>
    assume " \<alpha> \<in> qbs_Mx (\<amalg>\<^sub>Q i\<in>UNIV. if i then X else Y)"
    then obtain f \<beta> where hf:
      "\<alpha> = (\<lambda>r. (f r, \<beta> (f r) r))" "f \<in> real_borel \<rightarrow>\<^sub>M count_space UNIV" "\<And>i. i \<in> range f \<Longrightarrow> \<beta> i \<in> qbs_Mx (if i then X else Y)"
      by(auto simp: coprod_qbs_Mx_def)
    consider "range f = {True}" | "range f = {False}" | "range f = {True,False}"
      by auto
    thus "(\<lambda>(b, z). if b then Inl z else Inr z) \<circ> \<alpha> \<in> qbs_Mx (X <+>\<^sub>Q Y)"
    proof cases
      case 1
      then have "\<And>r. f r = True"
        by auto
      then show ?thesis
        using hf(3)
        by(auto intro!: bexI[where x="{}"] bexI[where x="\<beta> True"] simp: copair_qbs_Mx_def split_beta' comp_def hf(1))
    next
      case 2
      then have "\<And>r. f r = False"
        by auto
      then show ?thesis
        using hf(3)
        by(auto intro!: bexI[where x="UNIV"] bexI[where x="\<beta> False"] simp: copair_qbs_Mx_def split_beta' comp_def hf(1))
    next
      case 3
      then have 4:"f -` {True} \<in> sets real_borel"
        using measurable_sets[OF hf(2)] by simp
      have 5:"f -` {True} \<noteq> {} \<and> f -` {True} \<noteq> UNIV"
        using 3
        by (metis empty_iff imageE insertCI vimage_singleton_eq)
      have 6:"\<beta> True \<in> qbs_Mx X" "\<beta> False \<in> qbs_Mx Y"
        using hf(3)[of True] hf(3)[of False] by(auto simp: 3)
      show ?thesis
        apply(simp add: copair_qbs_Mx_def)
        apply(intro bexI[OF _ 4])
        apply(simp add: 5)
        apply(intro bexI[OF _ 6(1)] bexI[OF _ 6(2)])
        apply(auto simp add: hf(1) comp_def)
        done
    qed
  qed
next
  show "case_sum (Pair True) (Pair False) \<in> X <+>\<^sub>Q Y \<rightarrow>\<^sub>Q (\<amalg>\<^sub>Q i\<in>UNIV. if i then X else Y)"
  proof(rule qbs_morphismI)
    fix \<alpha>
    assume "\<alpha> \<in> qbs_Mx (X <+>\<^sub>Q Y)"
    then obtain S where hs:
    "S \<in> sets real_borel" "S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. \<alpha> = (\<lambda>r. Inl (\<alpha>1 r)))" "S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. \<alpha> = (\<lambda>r. Inr (\<alpha>2 r)))"
    "(S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. \<exists> \<alpha>2\<in> qbs_Mx Y. \<alpha> = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))"
      by(auto simp: copair_qbs_Mx_def)
    consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
    thus "case_sum (Pair True) (Pair False) \<circ> \<alpha>  \<in> qbs_Mx (\<amalg>\<^sub>Q i\<in>UNIV. if i then X else Y)"
    proof cases
      case 1
      then obtain \<alpha>1 where ha:
      "\<alpha>1\<in> qbs_Mx X" "\<alpha> = (\<lambda>r. Inl (\<alpha>1 r))"
        using hs(2) by auto
      hence "case_sum (Pair True) (Pair False) \<circ> \<alpha> = (\<lambda>r. (True, \<alpha>1 r))"
        by auto
      thus ?thesis
        by(auto intro!: coprod_qbs_MxI simp: ha)
    next
      case 2
      then obtain \<alpha>2 where ha:
      "\<alpha>2\<in> qbs_Mx Y" "\<alpha> = (\<lambda>r. Inr (\<alpha>2 r))"
        using hs(3) by auto
      hence "case_sum (Pair True) (Pair False) \<circ> \<alpha> = (\<lambda>r. (False, \<alpha>2 r))"
        by auto
      thus ?thesis
        by(auto intro!: coprod_qbs_MxI simp: ha)
    next
      case 3
      then obtain \<alpha>1 \<alpha>2 where ha:
       "\<alpha>1\<in> qbs_Mx X" "\<alpha>2\<in> qbs_Mx Y" "\<alpha> = (\<lambda>r. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
        using hs(4) by auto
      define f :: "real \<Rightarrow> bool" where "f \<equiv> (\<lambda>r. r \<in> S)"
      define \<alpha>' where "\<alpha>' \<equiv> (\<lambda>i. if i then \<alpha>1 else \<alpha>2)"
      have "case_sum (Pair True) (Pair False) \<circ> \<alpha> = (\<lambda>r. (f r, \<alpha>' (f r) r))"
        by(auto simp: f_def \<alpha>'_def ha(3))
      thus ?thesis
        using hs(1)
        by(auto intro!: coprod_qbs_MxI simp: ha \<alpha>'_def f_def)
    qed
  qed
next
  show "(\<lambda>(b, z). if b then Inl z else Inr z) \<circ> case_sum (Pair True) (Pair False) = id"
    by (auto simp add: sum.case_eq_if )
qed


subsubsection \<open> Lists \<close>
abbreviation "list_of X \<equiv> \<amalg>\<^sub>Q n\<in>(UNIV :: nat set). (\<Pi>\<^sub>Q i\<in>{..<n}. X)"
abbreviation list_nil :: "nat \<times> (nat \<Rightarrow> 'a)" where
"list_nil \<equiv> (0, \<lambda>n. undefined)"
abbreviation list_cons :: "['a, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
"list_cons x l \<equiv> (Suc (fst l), (\<lambda>n. if n = 0 then x else (snd l) (n - 1)))"

definition list_head :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
"list_head l = snd l 0"
definition list_tail :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
"list_tail l = (fst l - 1, \<lambda>m. (snd l) (Suc m))"


lemma list_simp1:
 "list_nil \<noteq> list_cons x l"
  by simp

lemma list_simp2:
  assumes "list_cons a al = list_cons b bl"
  shows "a = b" "al = bl"
proof -
  have "a = snd (list_cons a al) 0"
       "b = snd (list_cons b bl) 0"
    by auto
  thus "a = b"
    by(simp add: assms)
next
  have "fst al = fst bl"
    using assms by simp
  moreover have "snd al = snd bl"
  proof
    fix n
    have "snd al n = snd (list_cons a al) (Suc n)"
      by simp
    also have "... = snd (list_cons b bl) (Suc n)"
      by (simp add: assms)
    also have "... = snd bl n"
      by simp
    finally show "snd al n = snd bl n" .
  qed
  ultimately show "al = bl"
    by (simp add: prod.expand)
qed

lemma list_simp3:
  shows "list_head (list_cons a l) = a"
  by(simp add: list_head_def)

lemma list_simp4:
  assumes "l \<in> qbs_space (list_of X)"
  shows "list_tail (list_cons a l) = l"
  using assms by(simp_all add: list_tail_def)

lemma list_decomp1:
  assumes "l \<in> qbs_space (list_of X)"
  shows "l = list_nil \<or>
         (\<exists>a l'. a \<in> qbs_space X \<and> l' \<in> qbs_space (list_of X) \<and> l = list_cons a l')"
proof(cases l)
  case hl:(Pair n f)
  show ?thesis
  proof(cases n)
    case 0
    then show ?thesis
      using assms hl by simp
  next
    case hn:(Suc n')
    define f' where "f' \<equiv> \<lambda>m. f (Suc m)"
    have "l = list_cons (f 0) (n',f')"
    proof(simp add: hl hn, standard)
      fix m
      show "f m = (if m = 0 then f 0 else snd (n', f') (m - 1))"
        using assms hl by(cases m; fastforce simp: f'_def) 
    qed
    moreover have "(n', f') \<in> qbs_space (list_of X)"
    proof(simp,rule PiE_I)
      show "\<And>x. x \<in> {..<n'} \<Longrightarrow> f' x \<in> qbs_space X"
        using assms hl hn by(fastforce simp: f'_def)
    next
      fix x
      assume 1:"x \<notin> {..<n'}"
      thus " f' x = undefined"
        using hl assms hn by(auto simp: f'_def)
    qed
    ultimately show ?thesis
      using hl assms
      by(auto intro!: exI[where x="f 0"] exI[where x="(n',\<lambda>m. if m = 0 then undefined else f (Suc m))"])
  qed
qed

lemma list_simp5:
  assumes "l \<in> qbs_space (list_of X)"
      and "l \<noteq> list_nil"
    shows "l = list_cons (list_head l) (list_tail l)"
proof -
  obtain a l' where hl:
  "a \<in> qbs_space X" "l' \<in> qbs_space (list_of X)" "l = list_cons a l'"
    using list_decomp1[OF assms(1)] assms(2) by blast
  hence "list_head l = a" "list_tail l = l'"
    using list_simp3 list_simp4 by auto
  thus ?thesis
    using hl(3) list_simp2 by auto
qed

lemma list_simp6:
 "list_nil \<in> qbs_space (list_of X)"
  by simp

lemma list_simp7:
  assumes "a \<in> qbs_space X"
      and "l \<in> qbs_space (list_of X)"
    shows "list_cons a l \<in> qbs_space (list_of X)"
  using assms by(fastforce simp: PiE_def extensional_def)

lemma list_destruct_rule:
  assumes "l \<in> qbs_space (list_of X)"
          "P list_nil"
      and "\<And>a l'. a \<in> qbs_space X \<Longrightarrow> l' \<in> qbs_space (list_of X) \<Longrightarrow> P (list_cons a l')"
    shows "P l"
  by(rule disjE[OF list_decomp1[OF assms(1)]]) (use assms in auto)

lemma list_induct_rule:
  assumes "l \<in> qbs_space (list_of X)"
          "P list_nil"
      and "\<And>a l'. a \<in> qbs_space X \<Longrightarrow> l' \<in> qbs_space (list_of X) \<Longrightarrow> P l' \<Longrightarrow> P (list_cons a l')"
    shows "P l"
proof(cases l)
  case hl:(Pair n f)
  then show ?thesis
    using assms(1)
  proof(induction n arbitrary: f l)
    case 0
    then show ?case
      using assms(1,2) by simp
  next
    case ih:(Suc n)
    then obtain a l' where hl:
    "a \<in> qbs_space X" "l' \<in> qbs_space (list_of X)" "l = list_cons a l'"
      using list_decomp1 by blast
    have "P l'"
      using ih hl(3)
      by(auto intro!: ih(1)[OF _ hl(2),of "snd l'"])
    from assms(3)[OF hl(1,2) this]
    show ?case
      by(simp add: hl(3))
  qed
qed


fun from_list :: "'a list \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
 "from_list [] = list_nil" |
 "from_list (a#l) = list_cons a (from_list l)"

fun to_list' ::  "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
 "to_list' 0 _ = []" |
 "to_list' (Suc n) f = f 0 # to_list' n (\<lambda>n. f (Suc n))"

definition to_list :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
"to_list \<equiv> case_prod to_list'"

lemma to_list_simp1:
  shows "to_list list_nil = []"
  by(simp add: to_list_def)

lemma to_list_simp2:
  assumes "l \<in> qbs_space (list_of X)"
  shows "to_list (list_cons a l) = a # to_list l"
  using assms by(auto simp:PiE_def to_list_def)

lemma from_list_length:
 "fst (from_list l) = length l"
  by(induction l, simp_all)

lemma from_list_in_list_of:
  assumes "set l \<subseteq> qbs_space X"
  shows "from_list l \<in> qbs_space (list_of X)"
  using assms by(induction l) (auto simp: PiE_def extensional_def Pi_def)

lemma from_list_in_list_of':
  shows "from_list l \<in> qbs_space (list_of (Abs_quasi_borel (UNIV,UNIV)))"
proof -
  have "set l \<subseteq> qbs_space (Abs_quasi_borel (UNIV,UNIV))"
    by(simp add: qbs_space_def Abs_quasi_borel_inverse[of "(UNIV,UNIV)",simplified is_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def,simplified])
  thus ?thesis
    using from_list_in_list_of by blast
qed

lemma list_cons_in_list_of:
  assumes "set (a#l) \<subseteq> qbs_space X"
  shows "list_cons a (from_list l) \<in> qbs_space (list_of X)"
  using from_list_in_list_of[OF assms] by simp

lemma from_list_to_list_ident:
 "(to_list \<circ> from_list) l = l"
  by(induction l)
   (simp add: to_list_def,simp add: to_list_simp2[OF from_list_in_list_of'])

lemma to_list_from_list_ident:
  assumes "l \<in> qbs_space (list_of X)"
  shows "(from_list \<circ> to_list) l = l"
proof(rule list_induct_rule[OF assms])
  fix a l'
  assume h: "l' \<in> qbs_space (list_of X)"
     and ih:"(from_list \<circ> to_list) l' = l'"
  show "(from_list \<circ> to_list) (list_cons a l') = list_cons a l'"
    by(auto simp add: to_list_simp2[OF h] ih[simplified])
qed (simp add: to_list_simp1)


definition rec_list' :: "'b \<Rightarrow> ('a \<Rightarrow> (nat \<times> (nat \<Rightarrow> 'a)) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (nat \<times> (nat \<Rightarrow> 'a)) \<Rightarrow> 'b" where
"rec_list' t0 f l \<equiv> (rec_list t0 (\<lambda>x l'. f x (from_list l')) (to_list l))"

lemma rec_list'_simp1:
 "rec_list' t f list_nil = t"
  by(simp add: rec_list'_def to_list_simp1)

lemma rec_list'_simp2:
  assumes "l \<in> qbs_space (list_of X)"
  shows "rec_list' t f (list_cons x l) = f x l (rec_list' t f l)"
  by(simp add: rec_list'_def to_list_simp2[OF assms] to_list_from_list_ident[OF assms,simplified])

end