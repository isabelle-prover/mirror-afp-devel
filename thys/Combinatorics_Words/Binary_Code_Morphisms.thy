(*  Title:      Binary Code Morphisms
    File:       Combinatorics_Words.Binary_Code_Morphisms
    Author:     Štěpán Holub, Charles University
                Martin Raška, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Binary_Code_Morphisms
  imports CoWBasic Submonoids Morphisms

begin

chapter "Binary alphabet and binary morphisms"

section "Datatype of a binary alphabet"

text\<open>Basic elements for construction of binary words.\<close>

type_notation Enum.finite_2 ("binA")
notation finite_2.a\<^sub>1 ("bina")
notation finite_2.a\<^sub>2 ("binb")

lemmas bin_distinct = Enum.finite_2.distinct
lemmas bin_exhaust = Enum.finite_2.exhaust
lemmas bin_induct = Enum.finite_2.induct
lemmas bin_UNIV = Enum.UNIV_finite_2
lemmas bin_eq_neq_iff = Enum.neq_finite_2_a\<^sub>2_iff
lemmas bin_eq_neq_iff' = Enum.neq_finite_2_a\<^sub>1_iff

abbreviation bin_word_a  :: "binA list" ("\<aa>") where
  "bin_word_a \<equiv> [bina]"

abbreviation bin_word_b :: "binA list" ("\<bb>") where
  "bin_word_b \<equiv> [binb]"

abbreviation binUNIV :: "binA set" where "binUNIV \<equiv> UNIV"

lemma binUNIV_I [simp, intro]: "bina \<in> A \<Longrightarrow> binb \<in> A \<Longrightarrow> A = UNIV"
  unfolding UNIV_finite_2 by auto

lemma bin_basis_code: "code {\<aa>,\<bb>}"
  by (rule bin_code_code) blast

lemma bin_num: "bina = 0" "binb = 1"
  by simp_all

lemma binA_simps [simp]: "bina - binb = binb" "binb - bina = binb" "1 - bina = binb" "1 - binb = bina" "a - a = bina" "1 - (1 - a) = a"
  by simp_all

definition bin_swap :: "binA \<Rightarrow> binA" where "bin_swap x \<equiv> 1 - x"

lemma bin_swap_if_then: "1-x = (if x = bina then binb else bina)"
  by fastforce

definition bin_swap_morph where "bin_swap_morph \<equiv> map bin_swap"

lemma alphabet_or[simp]: "a = bina \<or> a = binb"
  by auto

lemma bin_im_or: "f [a] = f \<aa> \<or> f [a] = f \<bb>"
  by (rule bin_exhaust[of a], simp_all)

thm triv_forall_equality

lemma binUNIV_card: "card binUNIV = 2"
  unfolding bin_UNIV card_2_iff by auto

lemma other_letter: obtains b where "b \<noteq> (a :: binA)"
  using finite_2.distinct(1) by metis

lemma alphabet_or_neq: "x \<noteq> y \<Longrightarrow> x = (a :: binA) \<or> y = a"
  using alphabet_or[of x] alphabet_or[of y] alphabet_or[of a] by argo

lemma binA_neq_cases: assumes neq: "a \<noteq> b"
  obtains "a = bina" and "b = binb" | "a = binb" and "b = bina"
  using alphabet_or_neq assms by auto

lemma bin_neq_sym_pred: assumes "a \<noteq> b" and "P bina binb" and "P binb bina" shows "P a b"
  using assms(2-3) binA_neq_cases[OF \<open>a \<noteq> b\<close>, of "P a b"] by blast

lemma no_third: "(c :: binA) \<noteq> a \<Longrightarrow> b \<noteq> a \<Longrightarrow> b = c"
  using alphabet_or[of a] by fastforce

lemma two_in_bin_UNIV: assumes "a \<noteq> b" and  "a \<in> S" and "b \<in> S" shows "S = binUNIV"
  using  \<open>a \<in> S\<close> \<open>b \<in> S\<close> alphabet_or_neq[OF \<open>a \<noteq> b\<close>] by fast

lemmas two_in_bin_set = two_in_bin_UNIV[unfolded bin_UNIV]

lemma bin_not_comp_set_UNIV: assumes "\<not> u \<bowtie> v" shows "set (u \<cdot> v) = binUNIV"
proof-
  have uv: "u \<cdot> v = ((u \<and>\<^sub>p v) \<cdot> ([hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>u)] \<cdot> tl ((u \<and>\<^sub>p v)\<inverse>\<^sup>>u)))  \<cdot> (u \<and>\<^sub>p v) \<cdot> ([hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>v)] \<cdot> tl ((u \<and>\<^sub>p v)\<inverse>\<^sup>>v))"
    unfolding hd_tl[OF lcp_mismatch_lq(1)[OF assms]] hd_tl[OF lcp_mismatch_lq(2)[OF assms]] lcp_lq..
  from this[unfolded rassoc]
  have "hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>u) \<in> set (u \<cdot> v)" and "hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>v) \<in> set (u \<cdot> v)"
    unfolding uv by simp_all
  with lcp_mismatch_lq(3)[OF assms]
  show ?thesis
    using two_in_bin_UNIV by blast
qed

lemma bin_basis_singletons: "{[q] |q.  q \<in> {bina, binb}} = {\<aa>,\<bb>}"
  by blast

lemma bin_basis_generates: "\<langle>{\<aa>,\<bb>}\<rangle> = UNIV"
  using sings_gen_lists[of binUNIV, unfolded lists_UNIV bin_UNIV bin_basis_singletons, folded bin_UNIV, unfolded lists_UNIV].

lemma a_in_bin_basis: "[a] \<in> {\<aa>,\<bb>}"
  using Set.UNIV_I by auto

lemma lcp_zero_one_emp: "\<aa> \<and>\<^sub>p \<bb> = \<epsilon>" and lcp_one_zero_emp: "\<bb> \<and>\<^sub>p \<aa> = \<epsilon>"
  by simp+

lemma bin_neq_induct: "(a::binA) \<noteq> b \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow> P c"
proof (elim binA_neq_cases)
  show " P a \<Longrightarrow> P b \<Longrightarrow> a = bina \<Longrightarrow> b = binb \<Longrightarrow> P c"
    using finite_2.induct by blast
  show " P a \<Longrightarrow> P b \<Longrightarrow> a = binb \<Longrightarrow> b = bina \<Longrightarrow> P c"
    using finite_2.induct by blast
qed

lemma bin_neq_induct': assumes"(a::binA) \<noteq> b" and "P a" and "P b" shows "\<And> c. P c"
  using bin_neq_induct[OF assms] by blast

lemma neq_exhaust: assumes "(a::binA) \<noteq> b" obtains "c = a" | "c = b"
  using assms by (elim binA_neq_cases) (hypsubst, elim finite_2.exhaust, assumption)+

lemma bin_swap_neq [simp]: "1-(a :: binA) \<noteq> a"
    by simp
lemmas bin_swap_neq'[simp] = bin_swap_neq[symmetric]

lemmas bin_swap_induct = bin_neq_induct[OF bin_swap_neq']
   and bin_swap_exhaust = neq_exhaust[OF bin_swap_neq']

lemma bin_swap_induct': "P (a :: binA) \<Longrightarrow> P (1-a) \<Longrightarrow> (\<And> c. P c)"
  using bin_swap_induct by auto

lemma swap_UNIV: "{a, 1-a} = binUNIV" (is "?P a")
  using bin_swap_induct[of ?P bina, unfolded binA_simps] by fastforce

lemma bin_neq_swap'[intro]: "a \<noteq> b \<Longrightarrow> 1 - b = (a :: binA)"
   by (rule bin_swap_exhaust[of a b]) blast+

lemma bin_neq_swap[intro]: "a \<noteq> b \<Longrightarrow> 1 - a = (b :: binA)"
  using bin_neq_swap' by auto

lemma bin_neq_swap''[intro]: "a \<noteq> b \<Longrightarrow> b = 1-(a:: binA)"
  using bin_neq_swap by blast

lemma bin_neq_swap'''[intro]: "a \<noteq> b \<Longrightarrow> a = 1-(b:: binA)"
  using bin_neq_swap by blast

lemma bin_neq_iff: "c \<noteq> d \<longleftrightarrow> 1 - d = (c :: binA)"
  using bin_neq_swap[of d c] bin_swap_neq[of d] by argo

lemma bin_neq_iff': "c \<noteq> d \<longleftrightarrow> 1 - c = (d :: binA)"
  unfolding bin_neq_iff by force

lemma binA_neq_cases_swap: assumes neq: "a \<noteq> (b :: binA)"
  obtains "a = c" and "b = 1 - c" | "a = 1 - c" and "b = c"
  using assms bin_neq_swap bin_swap_exhaust[of a c] by metis

lemma im_swap_neq: "f a = f b \<Longrightarrow> f bina \<noteq> f binb \<Longrightarrow> a = b"
  using binA_neq_cases_swap[of a b bina False, unfolded binA_simps] by fastforce

lemma bin_without_letter: assumes "(a1 :: binA) \<notin> set w"
  obtains k where "w = [1-a1]\<^sup>@k"
proof-
  have "\<forall> c. c \<in> set w \<longrightarrow> c = 1-a1"
    using assms bin_swap_exhaust by blast
  from that unique_letter_wordE'[OF this]
  show thesis by blast
qed

lemma bin_empty_iff: "S = {} \<longleftrightarrow> (a :: binA) \<notin> S \<and> 1-a \<notin> S"
  using bin_swap_induct[of "\<lambda>a. a \<notin> S"] by blast

lemma bin_UNIV_iff: "S = binUNIV \<longleftrightarrow> a \<in> S \<and> 1-a \<in> S"
  using two_in_bin_UNIV[OF bin_swap_neq'] by blast

lemma bin_UNIV_I: "a \<in> S \<Longrightarrow> 1-a \<in> S \<Longrightarrow> S = binUNIV"
  using bin_UNIV_iff by blast

lemma bin_sing_iff: "A = {a :: binA} \<longleftrightarrow> a \<in> A \<and> 1-a \<notin> A"
proof (rule sym, intro iffI conjI, elim conjE)
  assume "a \<in> A" and "1-a \<notin> A"
  have "b \<in> A \<longleftrightarrow> b = a" for b
    using \<open>a \<in> A\<close> \<open>1-a \<notin> A\<close> bin_swap_neq
    by (intro bin_swap_induct[of "\<lambda>c. (c \<in> A) = (c = a)" a b]) blast+
  then show "A = {a}" by blast
qed simp_all

lemma bin_set_cases: obtains "S = {}" | "S = {bina}" | "S = {binb}" | "S = binUNIV"
  unfolding bin_empty_iff[of _ "bina"] bin_UNIV_iff[of _ "bina"] bin_sing_iff
  by fastforce

lemma not_UNIV_E: assumes "A \<noteq> binUNIV" obtains a where "A \<subseteq> {a}"
  using assms by (cases rule: bin_set_cases[of A]) auto

lemma not_UNIV_nempE: assumes "A \<noteq> binUNIV" and "A \<noteq> {}" obtains a where "A = {a}"
  using assms by (cases rule: bin_set_cases[of A]) auto

lemma bin_sing_gen_iff: "x \<in> \<langle>{[a]}\<rangle> \<longleftrightarrow> 1-(a :: binA) \<notin> set x"
  unfolding sing_gen_lists[symmetric] in_lists_conv_set using bin_empty_iff bin_sing_iff by metis

lemma set_hd_pow_conv: "w \<in> [hd w]* \<longleftrightarrow> set w \<noteq> binUNIV"
  unfolding root_sing_set_iff
proof
  assume "set w \<subseteq> {hd w}"
  thus "set w \<noteq> binUNIV"
    unfolding bin_UNIV  using bin_distinct(1) by force
next
  assume "set w \<noteq> binUNIV"
  thus "set w \<subseteq> {hd w}"
  proof (cases "w = \<epsilon>")
    assume "set w \<noteq> binUNIV" and "w \<noteq> \<epsilon>"
    from hd_tl[OF this(2)] this(2)
    have "hd w \<in> set w" by simp
    hence "1-hd w \<notin> set w"
      using \<open>set w \<noteq> binUNIV\<close> unfolding bin_UNIV_iff[of "set w" "hd w"] by blast
    thus "set w \<subseteq> {hd w}"
      using bin_sing_iff by auto
  qed simp
qed

lemma not_swap_eq: "P a b \<Longrightarrow> (\<And> (c :: binA). \<not> P c (1-c)) \<Longrightarrow> a = b"
  using bin_neq_iff by metis

lemma bin_distinct_letter: assumes "set w = binUNIV"
  obtains k w' where "[hd w]\<^sup>@Suc k \<cdot> [1-hd w] \<cdot> w' = w"
proof-
  from distinct_letter_in_hd'[of w, unfolded set_hd_pow_conv[of w] bool_simps(1), OF assms]
  obtain m b q where "[hd w] \<^sup>@ Suc m \<cdot> [b] \<cdot> q = w" "b \<noteq> hd w".
  with that bin_neq_swap'[OF this(2)]
  show thesis
    by blast
qed

lemma "P a \<longleftrightarrow> P (1-a) \<Longrightarrow> P a \<Longrightarrow> (\<And> (b :: binA). P b)"
  using bin_swap_induct' by blast

lemma bin_sym_all: "P (a :: binA) \<longleftrightarrow> P (1-a) \<Longrightarrow> P a \<Longrightarrow> P x"
  using bin_swap_induct[of "\<lambda> a. P a" a, unfolded binA_simps] by blast

lemma bin_sym_all_comm:
  "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a] \<Longrightarrow> f [b] \<cdot> f [1-b] \<noteq> f [1-b] \<cdot> f [(b :: binA)]" (is "?P a \<Longrightarrow> ?P b")
  using bin_sym_all[of ?P a, unfolded binA_simps, OF neq_commute].

lemma bin_sym_all_neq:
  "f [(a :: binA)] \<noteq> f [1-a] \<Longrightarrow> f [b] \<noteq> f [1-b]" (is "?P a \<Longrightarrow> ?P b")
  using bin_sym_all[of ?P a, unfolded binA_simps, OF neq_commute].

lemma bin_len_count:
  fixes w :: "binA list"
  shows "\<^bold>|w\<^bold>| = count_list w a  + count_list w (1-a)"
  using sum_count_set[of w "{a,1-a}"] swap_UNIV by force

lemma bin_len_count':
  fixes w :: "binA list"
  shows "\<^bold>|w\<^bold>| = count_list w bina  + count_list w binb"
  using bin_len_count[of w bina] by force

section \<open>Binary morphisms\<close>

lemma bin_map_core_lists: "(map f\<^sup>\<C> w) \<in> lists {f \<aa>, f \<bb>}"
  unfolding core_def by (induct w, simp, unfold map_hd)
  (rule append_in_lists, simp_all add: bin_im_or)

lemma bin_range: "range f = {f bina, f binb}"
  unfolding bin_UNIV by simp

lemma bin_core_range: "range f\<^sup>\<C> = {f \<aa>, f \<bb>}"
  unfolding core_def bin_range..

lemma bin_core_range_swap: "range f\<^sup>\<C> = {f [(a :: binA)], f [1-a]}" (is "?P a")
  by (rule bin_induct[of ?P, unfolded binA_simps], unfold bin_core_range, simp, force)

lemma bin_map_core_lists_swap: "(map f\<^sup>\<C> w) \<in> lists {f [(a :: binA)], f [1-a]}"
  using map_core_lists[of f, unfolded bin_core_range_swap[of f a]].

locale binary_morphism = morphism f
  for f :: "binA list \<Rightarrow> 'a list"
begin

lemma bin_len_count_im:
  fixes  a :: binA
  shows "\<^bold>|f w\<^bold>| = count_list w a * \<^bold>|f [a]\<^bold>| + count_list w (1-a) * \<^bold>|f [1-a]\<^bold>|"
proof (induct w)
  case (Cons b w)
  show ?case
    unfolding hd_word[of b w] morph lenmorph Cons.hyps count_list_append
    by (induct a) simp_all
qed simp

lemma bin_len_count_im':
  shows "\<^bold>|f w\<^bold>| = count_list w bina * \<^bold>|f \<aa>\<^bold>| + count_list w binb * \<^bold>|f \<bb>\<^bold>|"
  proof (induct w)
    case (Cons a w)
    show ?case
      unfolding hd_word[of a w] morph lenmorph Cons.hyps count_list_append
      by (induct a)  simp_all
  qed simp


lemma bin_neq_inj_core: assumes "f [a] \<noteq> f [1-a]" shows "inj f\<^sup>\<C>"
proof
  show "f\<^sup>\<C> x = f\<^sup>\<C> y \<Longrightarrow> x = y" for x y
  proof (rule ccontr)
    assume "x \<noteq> y"
    from bin_sym_all_neq[OF assms]
    have "f\<^sup>\<C> x \<noteq> f\<^sup>\<C> y"
      unfolding core_def bin_neq_swap''[OF \<open>x \<noteq> y\<close>].
    thus "f\<^sup>\<C> x = f\<^sup>\<C> y \<Longrightarrow> False"
      by blast
  qed
qed

lemma bin_code_morphism_inj: assumes  "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
  shows "inj f"
  unfolding inj_on_def
proof (rule ballI, rule ballI, rule impI)
  have "f [b]  \<noteq> f [1-b]" for b
    using bin_sym_all_comm[OF assms, of b] by force
  from bin_neq_inj_core[OF this]
  have "inj f\<^sup>\<C>".
  fix xs ys assume "f xs = f ys"
  hence "concat (map f\<^sup>\<C> xs) = concat (map f\<^sup>\<C> ys)"
    unfolding morph_concat_map.
  from bin_code_code[unfolded code_def, rule_format,
      OF \<open>f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]\<close> bin_map_core_lists_swap bin_map_core_lists_swap this]
  show "xs = ys"
    using \<open>inj f\<^sup>\<C>\<close> by simp
qed

lemma bin_code_morphismI: "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a] \<Longrightarrow> code_morphism f"
  using code_morphismI[OF bin_code_morphism_inj].

end

subsection \<open>Binary periodic morphisms\<close>

locale binary_periodic_morphism = periodic_morphism f
  for f :: "binA list \<Rightarrow> 'a list"
begin

sublocale binary_morphism
  by unfold_locales

definition fn0 where "fn0 \<equiv> (SOME n. f \<aa> = mroot\<^sup>@n)"
definition fn1 where "fn1 \<equiv> (SOME n. f \<bb> = mroot\<^sup>@n)"

lemma bin0_im: "f \<aa> = mroot\<^sup>@fn0"
  using per_morph_rootI[rule_format, of \<aa>] someI[of "\<lambda> n. f \<aa> = mroot\<^sup>@n"] unfolding fn0_def by blast

lemma  bin1_im: "f \<bb> = mroot\<^sup>@fn1"
  using per_morph_rootI[rule_format, of \<bb>] someI[of "\<lambda> n. f \<bb> = mroot\<^sup>@n"] unfolding fn1_def by blast

lemma sorted_image : "f w = (f [a])\<^sup>@(count_list w a) \<cdot> (f [1-a])\<^sup>@(count_list w (1-a))"
proof-
  obtain k where "f w = mroot\<^sup>@k"
    using per_morph_rootI by blast
  have len: "\<^bold>|f w\<^bold>| = \<^bold>|(f [a])\<^sup>@(count_list w a) \<cdot> (f [1-a])\<^sup>@(count_list w (1-a))\<^bold>|"
    using  bin_len_count_im unfolding lenmorph pow_len.
  have *: "(f [a])\<^sup>@(count_list w a) \<cdot> (f [1-a])\<^sup>@(count_list w (1-a)) = mroot\<^sup>@(fn0 * (count_list w bina) +  fn1 * (count_list w binb))"
    by (induct a) (unfold binA_simps bin0_im bin1_im, unfold pow_mult[symmetric] add_exps[symmetric], simp_all add: add.commute)
  show ?thesis
    using len nemp_len[OF prim_nemp[OF per_morph_root_prim]]
    unfolding * \<open>f w = mroot\<^sup>@k\<close> pow_len by force
qed

lemma bin_per_morph_expI: "f u = mroot\<^sup>@((mexp bina) * (count_list u bina) + (mexp binb) * (count_list u binb))"
  using sorted_image[of u bina, unfolded binA_simps]
  by (simp add: add_exps per_morph_expI' pow_mult)

end


section \<open>From two words to a binary morphism\<close>

definition bin_morph_of' :: "'a list \<Rightarrow> 'a list \<Rightarrow> binA list \<Rightarrow> 'a list" where "bin_morph_of' x y u = concat (map (\<lambda> a. (case a of bina \<Rightarrow> x | binb \<Rightarrow> y)) u)"

definition bin_morph_of :: "'a list \<Rightarrow> 'a list \<Rightarrow> binA list \<Rightarrow> 'a list" where "bin_morph_of x y u = concat (map (\<lambda> a. if a = bina then x else y) u)"

lemma case_finite_2_if_else: "case_finite_2 x y = (\<lambda> a. if a = bina then x else y)"
    by (standard, simp split: finite_2.split)

lemma bin_morph_of_case_def: "bin_morph_of x y u = concat (map (\<lambda> a. (case a of bina \<Rightarrow> x | binb \<Rightarrow> y)) u)"
  unfolding bin_morph_of_def case_finite_2_if_else..

lemma case_finiteD: "case_finite_2 (f \<aa>) (f \<bb>) = f\<^sup>\<C>"
proof
  show "(case x of bina \<Rightarrow> f \<aa> | binb \<Rightarrow> f \<bb>) = f\<^sup>\<C> x" for x
    unfolding core_def by (cases rule: finite_2.exhaust[of x]) auto
qed

lemma case_finiteD': "case_finite_2 (f \<aa>) (f \<bb>) u = f\<^sup>\<C> u"
  using case_finiteD by metis

lemma bin_morph_of_maps: "bin_morph_of x y = List.maps (case_finite_2 x y)"
  unfolding bin_morph_of_def maps_def unfolding case_finite_2_if_else by simp

lemma bin_morph_ofD: "(bin_morph_of x y) \<aa> = x" "(bin_morph_of x y) \<bb> = y"
  unfolding bin_morph_of_def by simp_all

lemma bin_range_swap: "range f = {f (a::binA), f (1-a)}" (is "?P a")
  using bin_swap_induct[of ?P bina] unfolding binA_simps bin_UNIV by auto

lemma bin_morph_of_core_range: "range (bin_morph_of x y)\<^sup>\<C> = {x,y}"
  unfolding bin_core_range bin_morph_ofD..

lemma bin_morph_of_morph: "morphism (bin_morph_of x y)"
  unfolding bin_morph_of_def by (simp add: morphism.intro)

lemma bin_morph_of_bin_morph: "binary_morphism (bin_morph_of x y)"
  unfolding binary_morphism_def using bin_morph_of_morph.

lemma bin_morph_of_range: "range (bin_morph_of x y) = \<langle>{x,y}\<rangle>"
  using morphism.range_hull[of "bin_morph_of x y", unfolded bin_morph_of_core_range, OF bin_morph_of_morph].

context binary_code
begin

lemma code_morph_of: "code_morphism (bin_morph_of u\<^sub>0 u\<^sub>1)"
  using binary_morphism.bin_code_morphismI[OF bin_morph_of_bin_morph, of u\<^sub>0 u\<^sub>1 bina]
  unfolding binA_simps bin_morph_ofD using non_comm.

lemma  inj_morph_of: "inj (bin_morph_of u\<^sub>0 u\<^sub>1)"
  using  code_morphism.code_morph[OF code_morph_of].

end

section \<open>Two binary morphism\<close>

locale two_binary_morphisms = two_morphisms g h
  for g h :: "binA list \<Rightarrow> 'a list"

begin

lemma eq_on_letters_eq: "g \<aa> = h \<aa> \<Longrightarrow> g \<bb> = h \<bb> \<Longrightarrow> g = h"
  by (rule def_on_sings_eq, rule bin_induct) blast+

sublocale g: binary_morphism g
  by unfold_locales
sublocale h: binary_morphism h
  by unfold_locales

lemma rev_morphs: "two_binary_morphisms (rev_map g) (rev_map h)"
  using rev_maps by (intro two_binary_morphisms.intro)

lemma solution_UNIV:
  assumes "s \<noteq> \<epsilon>" and "g s = h s" and "\<And>a. g [a] \<noteq> h [a]"
  shows "set s = UNIV"
proof (rule ccontr, elim not_UNIV_E unique_letter_wordE'')
  fix a k assume *: "s = [a] \<^sup>@ k"
  then have "0 < k" using \<open>s \<noteq> \<epsilon>\<close> by blast
  have "g [a] = h [a]" using \<open>g s = h s\<close> unfolding * g.pow_morph h.pow_morph
    by (fact pow_eq_eq[OF _ \<open>0 < k\<close>])
  then show False using \<open>g [a] \<noteq> h [a]\<close> by contradiction
qed

lemma solution_len_im_sing_less:
  assumes sol: "g s = h s" and set: "a \<in> set s" and less: "\<^bold>|g [a]\<^bold>| < \<^bold>|h [a]\<^bold>|"
  shows "\<^bold>|h [1-a]\<^bold>| < \<^bold>|g [1-a]\<^bold>|"
proof (intro not_le_imp_less notI)
  assume "\<^bold>|g [1-a]\<^bold>| \<le> \<^bold>|h [1-a]\<^bold>|"
  with less_imp_le[OF less] have "\<^bold>|g [b]\<^bold>| \<le> \<^bold>|h [b]\<^bold>|" for b
    by (fact bin_swap_induct)
  from this set less
  have "\<^bold>|g s\<^bold>| < \<^bold>|h s\<^bold>|" by (rule len_im_less[of s])
  then show False using lenarg[OF sol] by simp
qed

lemma solution_len_im_sing_le:
  assumes sol: "g s = h s" and set: "set s = UNIV" and less: "\<^bold>|g [a]\<^bold>| \<le> \<^bold>|h [a]\<^bold>|"
  shows "\<^bold>|h [1-a]\<^bold>| \<le> \<^bold>|g [1-a]\<^bold>|"
proof (intro leI notI)
  assume "\<^bold>|g [1-a]\<^bold>| < \<^bold>|h [1-a]\<^bold>|"
  from solution_len_im_sing_less[OF sol _ this]
  have "\<^bold>|h [a]\<^bold>| < \<^bold>|g [a]\<^bold>|" unfolding set binA_simps by blast
  then show False using \<open>\<^bold>|g [a]\<^bold>| \<le> \<^bold>|h [a]\<^bold>|\<close> by simp
qed

lemma solution_sing_len_cases:
  assumes set: "set s = UNIV" and sol: "g s = h s" and "g \<noteq> h"
  obtains a where "\<^bold>|g [a]\<^bold>| < \<^bold>|h [a]\<^bold>|" and "\<^bold>|h [1-a]\<^bold>| < \<^bold>|g [1-a]\<^bold>|"
proof (cases rule: linorder_cases)
  show "\<^bold>|g [hd s]\<^bold>| < \<^bold>|h [hd s]\<^bold>| \<Longrightarrow> thesis"
    using solution_len_im_sing_less[OF sol] that unfolding set by blast
  interpret swap: two_binary_morphisms h g by unfold_locales
  show "\<^bold>|h [hd s]\<^bold>| < \<^bold>|g [hd s]\<^bold>| \<Longrightarrow> thesis"
    using swap.solution_len_im_sing_less[OF sol[symmetric]]
      solution_len_im_sing_less[OF sol] that unfolding set by blast
  have "s \<noteq> \<epsilon>" using set by auto
  assume *: "\<^bold>|g [hd s]\<^bold>| = \<^bold>|h [hd s]\<^bold>|"
  moreover have "\<^bold>|g [1 - (hd s)]\<^bold>| = \<^bold>|h [1 - (hd s)]\<^bold>|"
  proof (rule ccontr, elim linorder_neqE)
    show "\<^bold>|g [1 - (hd s)]\<^bold>| < \<^bold>|h [1 - (hd s)]\<^bold>| \<Longrightarrow> False"
    using solution_len_im_sing_less[OF sol, of "1 - (hd s)"]
    unfolding set binA_simps * by blast
  next
    show "\<^bold>|h [1-(hd s)]\<^bold>| < \<^bold>|g [1-(hd s)]\<^bold>| \<Longrightarrow> False"
    using swap.solution_len_im_sing_less[OF sol[symmetric], of "1 - (hd s)"]
    unfolding set binA_simps * by blast
  qed
  ultimately have "\<^bold>|g [a]\<^bold>| = \<^bold>|h [a]\<^bold>|" for a by (fact bin_swap_induct)
  from def_on_sings[OF solution_eq_len_eq[OF sol this]]
  show thesis unfolding set using \<open>g \<noteq> h\<close> by blast
qed

lemma len_ims_sing_neq:
  assumes  "g s = h s" "g \<noteq> h" "set s = binUNIV"
  shows  "\<^bold>|g [c]\<^bold>| \<noteq> \<^bold>|h [c]\<^bold>|"
proof(rule solution_sing_len_cases[OF \<open>set s = binUNIV\<close> \<open>g s  = h s\<close> \<open>g \<noteq> h\<close>])
  fix a  assume less: "\<^bold>|g [a]\<^bold>| < \<^bold>|h [a]\<^bold>|" "\<^bold>|h [1 - a]\<^bold>| < \<^bold>|g [1 - a]\<^bold>|"
  show "\<^bold>|g [c]\<^bold>| \<noteq> \<^bold>|h [c]\<^bold>|"
    by (rule bin_swap_exhaust[of c a]) (use less in force)+
qed

end

lemma two_binary_morphismsI: "binary_morphism g \<Longrightarrow> binary_morphism h \<Longrightarrow> two_binary_morphisms g h"
  unfolding binary_morphism_def two_binary_morphisms_def using two_morphisms.intro.

section \<open>Binary code morphism\<close>

subsection \<open>Locale - binary code morphism\<close>

locale binary_code_morphism = code_morphism "f :: binA list \<Rightarrow> 'a list" for f

begin

lemma morph_bin_morph_of: "f = bin_morph_of (f \<aa>) (f \<bb>)"
  using morph_concat_map unfolding bin_morph_of_def case_finiteD
  case_finite_2_if_else[symmetric] by simp

lemma non_comm_morph [simp]: "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
  unfolding morph[symmetric] using  code_morph_code bin_swap_neq by blast

lemma non_comp_morph: "\<not> f [a] \<cdot> f [1-a] \<bowtie> f [1-a] \<cdot> f [a]"
  using comm_comp_eq non_comm_morph by blast

lemma swap_non_comm_morph [simp, intro]: "a \<noteq> b \<Longrightarrow> f [a] \<cdot> f [b] \<noteq> f [b] \<cdot> f [a]"
  using bin_neq_swap non_comm_morph by blast

thm bin_core_range[of f]

lemma bin_code_morph_rev_map: "binary_code_morphism (rev_map f)"
  unfolding binary_code_morphism_def using code_morphism_rev_map.

sublocale swap: binary_code "f \<bb>" "f \<aa>"
  using non_comm_morph[of binb] unfolding binA_simps by unfold_locales

sublocale binary_code "f \<aa>" "f \<bb>"
  using swap.bin_code_swap.

notation bin_code_lcp ("\<alpha>") and
         bin_code_lcs ("\<beta>") and
         bin_code_mismatch_fst ("c\<^sub>0") and
         bin_code_mismatch_snd ("c\<^sub>1")
term "bin_lcp (f \<aa>) (f \<bb>)"
abbreviation bin_morph_mismatch ("\<cc>")
  where "bin_morph_mismatch a \<equiv> bin_mismatch (f[a]) (f[1-a])"
abbreviation bin_morph_mismatch_suf ("\<dd>")
  where "bin_morph_mismatch_suf a \<equiv> bin_mismatch_suf (f[1-a]) (f[a])"

lemma bin_lcp_def': "\<alpha> =  f ([a] \<cdot> [1-a]) \<and>\<^sub>p f ([1-a] \<cdot> [a])"
  by (rule bin_exhaust[of a "\<alpha> =  f ([a] \<cdot> [1-a]) \<and>\<^sub>p f ([1-a] \<cdot> [a])"],
  unfold morph, use binA_simps(3-4) bin_lcp_def in force)
  (unfold bin_lcp_def lcp_sym[of "f[a] \<cdot> f[1-a]" "f[1-a] \<cdot> f[a]"],
  use  binA_simps(3-4) in auto)

lemma bin_lcp_neq: "a \<noteq> b \<Longrightarrow> \<alpha> =  f ([a] \<cdot> [b]) \<and>\<^sub>p f ([b] \<cdot> [a])"
  using bin_neq_swap[of a b] unfolding bin_lcp_def'[of a] by blast

lemma sing_im: "f [a] \<in>  {f \<aa>, f \<bb>}"
  using finite_2.exhaust[of a ?thesis] by fastforce

lemma bin_mismatch_inj: "inj \<cc>"
  unfolding inj_on_def
  using non_comm_morph[folded bin_mismatch_comm] bin_neq_swap by force

lemma map_in_lists: "map (\<lambda>x. f [x]) w \<in> lists {f \<aa>, f \<bb>}"
proof (induct w)
  case (Cons a w)
  then show ?case
    unfolding list.map(2)  using sing_im by simp
qed simp

lemma bin_morph_lcp_short: "\<^bold>|\<alpha>\<^bold>| < \<^bold>|f [a]\<^bold>| + \<^bold>|f[1-a]\<^bold>|"
  using finite_2.exhaust[of a ?thesis] bin_lcp_short by force

lemma swap_not_pref_bin_lcp:  "\<not> f([a] \<cdot> [1-a]) \<le>p \<alpha>"
  using pref_len[of "f [a] \<cdot> f [1-a]" \<alpha>] unfolding morph lenmorph using bin_morph_lcp_short[of a] by force

thm local.bin_mismatch_inj

lemma bin_mismatch_suf_inj: "inj \<dd>"
  using binary_code_morphism.bin_mismatch_inj[OF bin_code_morph_rev_map, reversed].

lemma bin_lcp_sing: "bin_lcp (f [a]) (f [1-a]) = \<alpha>"
  unfolding bin_lcp_def
  by (rule finite_2.exhaust[of a], simp_all add: lcp_sym)

lemma bin_lcs_sing: "bin_lcs (f [a]) (f [1-a]) = \<beta>"
  unfolding bin_lcs_def
  by (rule finite_2.exhaust[of a], simp_all add: lcs_sym)

lemma bin_code_morph_sing: "binary_code (f [a]) (f [1-a])"
  unfolding binary_code_def
  by (cases rule: binA_neq_cases[OF bin_swap_neq', of a]) simp_all

lemma bin_mismatch_swap_neq: "\<cc> a \<noteq> \<cc> (1-a)"
  using bin_code_morph_sing binary_code.bin_mismatch_neq by auto

lemma long_bin_lcp_hd: assumes "\<^bold>|f w\<^bold>| \<le> \<^bold>|\<alpha>\<^bold>|"
  shows "w \<in> [hd w]*"
proof (rule ccontr)
  assume "\<not> w \<in> [hd w]*"
  from distinct_letter_in_hd[OF this]
  obtain m b suf where w: "[hd w]\<^sup>@m \<cdot> [b]\<cdot> suf = w" and "b \<noteq> hd w" and "m \<noteq> 0".
  have ineq: "\<^bold>|f [b]\<^bold>| + \<^bold>|f [hd w]\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    using  quotient_smaller[OF \<open>m \<noteq> 0\<close>, of "\<^bold>|f [hd w]\<^bold>|"]
    unfolding arg_cong[OF w, of "\<lambda> x. \<^bold>|f(x)\<^bold>|", unfolded morph lenmorph pow_morph pow_len, symmetric]
    by linarith
  hence "\<^bold>|f \<aa>\<^bold>| + \<^bold>|f \<bb>\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    using \<open>b \<noteq> hd w\<close> alphabet_or[of b] alphabet_or[of "hd w"] add.commute by fastforce
  thus False
    using bin_lcp_short \<open>\<^bold>|f w\<^bold>| \<le> \<^bold>|\<alpha>\<^bold>|\<close>  by linarith
qed

thm nonerasing
    nonerasing_morphism.nonerasing
     lemmas nonerasing = nonerasing
thm nonerasing_morphism.nonerasing
    binary_code_morphism.nonerasing

lemma bin_morph_lcp_mismatch_pref:
 "\<alpha> \<cdot> [\<cc> a] \<le>p f [a] \<cdot> \<alpha>"
  using binary_code.bin_fst_mismatch[OF bin_code_morph_sing] unfolding bin_lcp_sing.

lemma "[\<dd> a] \<cdot> \<beta> \<le>s \<beta> \<cdot> f [a]"    using binary_code_morphism.bin_morph_lcp_mismatch_pref[OF bin_code_morph_rev_map, reversed].

lemma bin_lcp_pref_all: "\<alpha> \<le>p f w \<cdot> \<alpha>"
proof(induct w rule: rev_induct)
  case (snoc x xs)
  from pref_prolong[OF this, of "f[x]\<cdot>\<alpha>", unfolded lassoc]
  show ?case
    unfolding morph[of xs "[x]"] using bin_lcp_fst_lcp bin_lcp_snd_lcp alphabet_or[of x] by blast
qed simp

lemma bin_lcp_spref_all: "w \<noteq> \<epsilon> \<Longrightarrow> \<alpha> <p f w \<cdot> \<alpha>"
  using  per_rootI[OF bin_lcp_pref_all] nemp_to_nemp by presburger

lemma pref_mono_lcp: assumes "w \<le>p w'" shows "f w \<cdot> \<alpha> \<le>p f w' \<cdot> \<alpha>"
proof-
  from \<open>w \<le>p w'\<close>
  obtain z where "w' = w \<cdot> z"
    unfolding prefix_def by fast
  show ?thesis
    unfolding \<open>w' = w \<cdot> z\<close> morph rassoc pref_cancel_conv using bin_lcp_pref_all.
qed

lemma long_bin_lcp: assumes "w \<noteq> \<epsilon>" and "\<^bold>|f w\<^bold>| \<le> \<^bold>|\<alpha>\<^bold>|"
  shows "w \<in> [hd w]*"
proof(rule ccontr)
  assume "w \<notin> [hd w]*"
    obtain m b q where "[hd w]\<^sup>@m \<cdot> [b] \<cdot> q = w" and "b \<noteq> hd w" and "m \<noteq> 0"
      using  distinct_letter_in_hd[OF \<open>w \<notin> [hd w]*\<close>].
    have ineq: "\<^bold>|f ([hd w]\<^sup>@m \<cdot> [b])\<^bold>| \<le> \<^bold>|f w\<^bold>|"
      using arg_cong[OF \<open>[hd w] \<^sup>@ m \<cdot> [b] \<cdot> q = w\<close>, of "\<lambda> x. \<^bold>|f x\<^bold>|"]
      unfolding morph lenmorph by force
    have eq: "m*\<^bold>|f [hd w]\<^bold>| + \<^bold>|f [b]\<^bold>| = \<^bold>|f ([hd w]\<^sup>@m \<cdot> [b])\<^bold>|"
      by (simp add: morph pow_len pow_morph)
    have  "\<^bold>|f [hd w]\<^bold>| + \<^bold>|f [b]\<^bold>|  \<le> m*\<^bold>|f [hd w]\<^bold>| + \<^bold>|f [b]\<^bold>|"
      using ineq \<open>m \<noteq> 0\<close> by simp
    hence "\<^bold>|f [hd w]\<^bold>| + \<^bold>|f [b]\<^bold>|  \<le> \<^bold>|f w\<^bold>|"
      using eq ineq by linarith
    hence "\<^bold>|f \<aa>\<^bold>| + \<^bold>|f \<bb>\<^bold>| \<le> \<^bold>|f w\<^bold>|"
      using binA_neq_cases [OF \<open>b \<noteq> hd w\<close>] by fastforce
    thus False
      using bin_lcp_short \<open>\<^bold>|f w\<^bold>| \<le> \<^bold>|\<alpha>\<^bold>|\<close>  by linarith
qed

thm sing_to_nemp
    nonerasing

lemma bin_mismatch_code_morph: "c\<^sub>0 = \<cc> 0" "c\<^sub>1 = \<cc> 1"
  unfolding bin_mismatch_def bin_lcp_def by simp_all

lemma bin_lcp_mismatch_pref_all: "\<alpha> \<cdot> [\<cc> a] \<le>p f [a] \<cdot> f w \<cdot> \<alpha>"
  using pref_prolong[OF bin_fst_mismatch bin_lcp_pref_all[of w]]
        pref_prolong[OF bin_snd_mismatch bin_lcp_pref_all[of w]]
  unfolding bin_mismatch_code_morph
  by (cases rule: finite_2.exhaust[of a]) simp_all

lemma bin_fst_mismatch_all: "\<alpha> \<cdot> [c\<^sub>0] \<le>p f \<aa> \<cdot> f w \<cdot> \<alpha>"
  using pref_prolong[OF bin_fst_mismatch bin_lcp_pref_all[of w]].

lemma bin_snd_mismatch_all: "\<alpha> \<cdot> [c\<^sub>1] \<le>p f \<bb> \<cdot> f w \<cdot> \<alpha>"
  using pref_prolong[OF bin_snd_mismatch bin_lcp_pref_all[of w]] by simp

lemma bin_long_mismatch: assumes "\<^bold>|\<alpha>\<^bold>| < \<^bold>|f w\<^bold>|" shows "\<alpha> \<cdot> [\<cc> (hd w)] \<le>p f w"
proof-
  have "w \<noteq> \<epsilon>"
    using assms emp_to_emp emp_len by force
  have "f w = f[hd w] \<cdot> f (tl w)"
    unfolding pop_hd[symmetric] unfolding hd_word[of "hd w" "tl w"]
    hd_tl[OF \<open>w \<noteq> \<epsilon>\<close>]..
  have "\<alpha> \<cdot> [\<cc> (hd w)] \<le>p f w \<cdot> \<alpha>"
    using bin_lcp_mismatch_pref_all[of "hd w" "tl w"]
    unfolding lassoc \<open>f w = f[hd w] \<cdot> f (tl w)\<close>[symmetric].
  moreover have "\<^bold>|\<alpha> \<cdot> [\<cc> (hd w)]\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    unfolding lenmorph sing_len using assms by linarith
  ultimately show ?thesis by blast
qed

lemma sing_pow_mismatch: assumes "f [a] = [b]\<^sup>@Suc n" shows "\<cc> a = b"
proof-
  \<comment> \<open>auxiliary\<close>
  have aritm: "Suc n * Suc \<^bold>|\<alpha>\<^bold>|  = Suc (n*\<^bold>|\<alpha>\<^bold>| + n + \<^bold>|\<alpha>\<^bold>|)"
    by auto
  have set: "set ([b] \<^sup>@ (Suc n * Suc \<^bold>|\<alpha>\<^bold>|)) = {b}"
    unfolding aritm using sing_pow_set_Suc.
  have elem: "\<cc> a \<in> set (\<alpha> \<cdot> [\<cc> a])"
    by simp
  have hd: "hd ([a] \<^sup>@ Suc \<^bold>|\<alpha>\<^bold>|) = a"
    by fastforce
  \<comment> \<open>proof\<close>
  let ?w = "[a]\<^sup>@Suc \<^bold>|\<alpha>\<^bold>|"
  have fw: "f ?w = [b]\<^sup>@(Suc n*Suc \<^bold>|\<alpha>\<^bold>|)"
    unfolding pow_mult assms[symmetric] pow_morph..
  have "\<^bold>|\<alpha>\<^bold>| < \<^bold>|f ?w\<^bold>|"
    unfolding fw pow_len sing_len by force
  from set_mono_prefix[OF bin_long_mismatch[OF this, unfolded fw]]
  show "\<cc> a = b"
    unfolding hd set using elem by blast
qed

lemma sing_pow_mismatch_suf: "f [a] = [b]\<^sup>@Suc n \<Longrightarrow> \<dd> a = b"
  using binary_code_morphism.sing_pow_mismatch[OF bin_code_morph_rev_map, reversed].

lemma bin_lcp_swap_hd: "f [a] \<cdot> f w \<cdot> \<alpha>  \<and>\<^sub>p f [1-a] \<cdot> f w' \<cdot> \<alpha> = \<alpha>"
  using lcp_first_mismatch[OF bin_mismatch_swap_neq, of \<alpha> a]
        bin_lcp_mismatch_pref_all[of a w] bin_lcp_mismatch_pref_all[of "1-a" w']
  unfolding prefix_def rassoc by force

lemma bin_lcp_neq_hd: "a \<noteq> b \<Longrightarrow> f [a] \<cdot> f w \<cdot> \<alpha>  \<and>\<^sub>p f [b] \<cdot> f w' \<cdot> \<alpha> = \<alpha>"
  using bin_lcp_swap_hd bin_neq_swap by blast


lemma bin_mismatch_swap_not_comp: "\<not> f [a] \<cdot> f w \<cdot> \<alpha>  \<bowtie> f [1-a] \<cdot> f w' \<cdot> \<alpha>"
  unfolding prefix_comparable_def lcp_pref_conv[symmetric] bin_lcp_swap_hd
            bin_lcp_swap_hd[of "1-a", unfolded binA_simps] using sing_to_nemp by auto

lemma bin_lcp_root: "\<alpha> <p f [a] \<cdot> \<alpha>"
  using alphabet_or[of a] per_rootI[OF bin_lcp_pref_all[of \<bb>] bin_snd_nemp] per_rootI[OF bin_lcp_pref_all[of \<aa>] bin_fst_nemp] by blast

lemma bin_lcp_pref: assumes "w \<notin> \<bb>*" and  "w \<notin> \<aa>*"
  shows "\<alpha> \<le>p (f w)"
proof-
  have "w \<noteq> \<epsilon>"
    using \<open>\<not> (w \<in> \<bb>*)\<close> emp_all_roots by blast
  have "w \<notin> [hd w]*"
    using assms alphabet_or[of "hd w"]  by presburger
  hence "\<^bold>|\<alpha>\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    using long_bin_lcp[OF \<open>w \<noteq> \<epsilon>\<close>] nat_le_linear[of "\<^bold>|f w\<^bold>|" "\<^bold>|\<alpha>\<^bold>|" ] by blast
  show ?thesis
    using  pref_prod_le[OF bin_lcp_pref_all \<open>\<^bold>|\<alpha>\<^bold>| \<le> \<^bold>|f w\<^bold>|\<close>].
qed


lemma bin_lcp_pref'': "[a] \<le>f w \<Longrightarrow> [1-a] \<le>f w  \<Longrightarrow> \<alpha> \<le>p (f w)"
  using  bin_lcp_pref[of w]  sing_pow_fac'[OF bin_distinct(1),of w] sing_pow_fac'[OF bin_distinct(2), of w]
  by (cases rule: finite_2.exhaust[of a]) force+
lemma bin_lcp_pref': "\<aa> \<le>f w \<Longrightarrow> \<bb> \<le>f w  \<Longrightarrow> \<alpha> \<le>p (f w)"
  using bin_lcp_pref''[of bina, unfolded binA_simps].

lemma bin_lcp_mismatch_pref_all_set: assumes "1-a \<in> set w"
  shows  "\<alpha> \<cdot> [\<cc> a] \<le>p f [a] \<cdot> f w"
proof-
  have "\<^bold>|f[1-a]\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    using fac_len' morph split_list'[OF assms] by metis
  hence "\<^bold>|\<alpha> \<cdot> [\<cc> a]\<^bold>| \<le> \<^bold>|f [a] \<cdot> f w\<^bold>|"
    using bin_lcp_short unfolding lenmorph sing_len
    by (cases rule: finite_2.exhaust[of a]) fastforce+
  from bin_lcp_mismatch_pref_all[unfolded lassoc, THEN pref_prod_le, OF this]
  show ?thesis.
qed

lemma bin_lcp_comp_hd: "\<alpha> \<bowtie> f (\<aa> \<cdot> w0) \<and>\<^sub>p  f (\<bb> \<cdot> w1)"
  using  ruler[OF bin_lcp_pref_all[of "\<aa> \<cdot> w0"]
      pref_trans[OF lcp_pref[of "f (\<aa> \<cdot> w0)" "f (\<bb> \<cdot> w1)"], of "f (\<aa> \<cdot> w0) \<cdot> \<alpha>", OF triv_pref]]
  unfolding prefix_comparable_def.

lemma sing_mismatch: assumes "f \<aa> \<in> [a]*" shows "c\<^sub>0 = a"
proof-
  have "\<alpha> \<in> [a]*"
    using per_one[OF per_root_trans[OF bin_lcp_root assms]].
  hence "f \<aa> \<cdot> \<alpha> \<in> [a]*"
    using \<open>f \<aa> \<in> [a]*\<close> add_roots by blast
  from sing_pow_fac'[OF _ this, of "c\<^sub>0"]
  show "c\<^sub>0 = a"
    using facI'[OF lq_pref[OF bin_fst_mismatch, unfolded rassoc]] by blast
qed

lemma sing_mismatch': assumes "f \<bb> \<in> [a]*" shows "c\<^sub>1 = a"
proof-
  have "\<alpha> \<in> [a]*"
    using per_one[OF per_root_trans[OF bin_lcp_root assms]].
  hence "f \<bb> \<cdot> \<alpha> \<in> [a]*"
    using \<open>f \<bb> \<in> [a]*\<close> add_roots by blast
  from sing_pow_fac'[OF _ this, of "c\<^sub>1"]
  show ?thesis
    using facI'[OF lq_pref[OF bin_snd_mismatch, unfolded rassoc]] by blast
qed

lemma bin_lcp_comp_all: "\<alpha> \<bowtie> (f w)"
  unfolding prefix_comparable_def using ruler[OF bin_lcp_pref_all triv_pref].

lemma not_comp_bin_swap: "\<not> f [a] \<cdot> \<alpha> \<bowtie> f [1-a] \<cdot> \<alpha>"
  using not_comp_bin_fst_snd bin_exhaust[of a ?thesis]
  unfolding prefix_comparable_def
  by simp

lemma mismatch_pref:
  assumes "\<alpha> \<le>p f ([a] \<cdot> w0)" and "\<alpha> \<le>p f ([1-a] \<cdot> w1)"
  shows "\<alpha> = f ([a] \<cdot> w0) \<and>\<^sub>p f ([1-a] \<cdot> w1)"
proof-
  have "f ([a] \<cdot> w0) \<cdot> \<alpha> \<and>\<^sub>p f ([1-a] \<cdot> w1) \<cdot> \<alpha> = \<alpha>"
    unfolding morph using bin_lcp_swap_hd[unfolded lassoc].
  hence "f ([a] \<cdot> w0) \<and>\<^sub>p f ([1-a] \<cdot> w1) \<le>p \<alpha>"
    using lcp.mono[OF triv_pref[of "f ([a] \<cdot> w0)" \<alpha>] triv_pref[of "f ([1-a] \<cdot> w1)" \<alpha>]]
    by presburger
  moreover have "\<alpha> \<le>p f ([a] \<cdot> w0) \<and>\<^sub>p f ([1-a] \<cdot> w1)"
    using assms pref_pref_lcp by blast
  ultimately show ?thesis
    using pref_antisym by blast
qed

lemma  bin_set_UNIV_length: assumes "set w = UNIV" shows "\<^bold>|f [a]\<^bold>| + \<^bold>|f [1-a]\<^bold>| \<le> \<^bold>|f w\<^bold>|"
proof-
  have "w \<noteq> \<epsilon>"
    using \<open>set w = UNIV\<close> by force
  from set_ConsD[of "1- hd w" "hd w" "tl w", unfolded list.collapse[OF this] assms[folded swap_UNIV[of "hd w"]]]
  have "1 - (hd w) \<in> set (tl w)"
    using bin_swap_neq[of "hd w"] by blast
  from in_set_morph_len[OF this]
  have "\<^bold>|f [1-hd w]\<^bold>| \<le> \<^bold>|f (tl w)\<^bold>|".
  with lenarg[OF arg_cong[of _ _ f, OF hd_tl[OF \<open>w \<noteq> \<epsilon>\<close>]]]
  have "\<^bold>|f [hd w]\<^bold>| + \<^bold>|f [1-hd w]\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    unfolding morph lenmorph by linarith
  thus ?thesis
    using bin_swap_exhaust[of a "hd w" ?thesis] by force
qed

lemma set_UNIV_bin_lcp_pref: assumes "set w = UNIV" shows "\<alpha> \<cdot> [\<cc> (hd w)] \<le>p f w"
  using bin_long_mismatch[OF less_le_trans[OF bin_morph_lcp_short bin_set_UNIV_length[OF assms]]].

lemmas not_comp_bin_lcp_pref =  bin_not_comp_set_UNIV[THEN set_UNIV_bin_lcp_pref]

lemma marked_lcp_conv: "marked_morphism f \<longleftrightarrow> \<alpha> = \<epsilon>"
proof
  assume "marked_morphism f"
  then interpret marked_morphism f by blast
  from marked_core[unfolded core_def] core_nemp[unfolded core_def]
  have "hd (f \<aa> \<cdot> f \<bb>) \<noteq> hd (f \<bb> \<cdot> f \<aa>)"
    using hd_append finite_2.distinct by auto
  thus "\<alpha> = \<epsilon>"
    unfolding bin_lcp_def using lcp_distinct_hd by blast
next
  assume "\<alpha> = \<epsilon>"
  have "hd (f \<aa>) \<noteq> hd (f \<bb>)"
    by (rule nemp_lcp_distinct_hd[OF sing_to_nemp sing_to_nemp])
    (use  lcp_append_monotone[of "f \<aa>" "f \<bb>" "f \<bb>" "f \<aa>", unfolded \<open>\<alpha> = \<epsilon>\<close>[unfolded bin_lcp_def]]
    in simp)
  show "marked_morphism f"
  proof
    fix a b :: binA assume "hd (f\<^sup>\<C> a) = hd (f\<^sup>\<C> b)"
    from im_swap_neq[OF this[unfolded core_def] \<open>hd (f \<aa>) \<noteq> hd (f \<bb>)\<close>]
    show "a = b".
  qed
qed

lemma im_comm_lcp: "f w \<cdot> \<alpha> = \<alpha> \<cdot> f w \<Longrightarrow> (\<forall> a. a \<in> set w \<longrightarrow> f [a] \<cdot> \<alpha> = \<alpha> \<cdot> f [a])"
proof (induct w)
  case (Cons a w)
  then show ?case
  proof (cases "w = \<epsilon>")
    assume "w = \<epsilon>"
    show ?thesis
      using Cons.prems(1) unfolding \<open>w = \<epsilon>\<close> by force
  next
    assume "w \<noteq> \<epsilon>"
    have eq: "f [a] \<cdot> f w \<cdot> \<alpha> = \<alpha> \<cdot> f [a] \<cdot> f w"
      unfolding morph[symmetric]
      unfolding lassoc morph[symmetric] hd_tl[OF \<open>w \<noteq> \<epsilon>\<close>]
      using \<open>f (a # w) \<cdot> \<alpha> = \<alpha> \<cdot> f (a # w)\<close> by force
    have "f [a] \<cdot> \<alpha> \<le>p f [a] \<cdot> f w \<cdot> \<alpha>"
      unfolding pref_cancel_conv using bin_lcp_pref_all.
    hence "f [a] \<cdot> \<alpha> = \<alpha> \<cdot> f [a]"
      using eqd_eq[of "\<alpha> \<cdot> f [a]", OF _swap_len] unfolding prefix_def eq rassoc by metis
    from eq[unfolded lassoc, folded this, unfolded rassoc cancel]
    have "f w \<cdot> \<alpha> = \<alpha> \<cdot> f w".
    from Cons.hyps[OF this] \<open>f [a] \<cdot> \<alpha> = \<alpha> \<cdot> f [a]\<close>
    show ?thesis by fastforce
  qed
qed simp

lemma im_comm_lcp_nemp: assumes "f w \<cdot> \<alpha> = \<alpha> \<cdot> f w" and "w \<noteq> \<epsilon>" and "\<alpha> \<noteq> \<epsilon>"
  obtains k where "w = [hd w]\<^sup>@Suc k"
proof-
  have "set w = {hd w}"
  proof-
    have "hd w \<in> set w" using \<open>w \<noteq> \<epsilon>\<close> by force
    have "a = hd w" if "a \<in> set w" for a
    proof-
      have "f [a] \<cdot> \<alpha> = \<alpha> \<cdot> f [a]" and "f [hd w] \<cdot> \<alpha> = \<alpha> \<cdot> f [hd w]"
      using that im_comm_lcp[OF \<open>f w \<cdot> \<alpha> = \<alpha> \<cdot> f w\<close>] \<open>hd w \<in> set w\<close> by presburger+
    from comm_trans[OF this \<open>\<alpha> \<noteq> \<epsilon>\<close>]
    show "a = hd w"
      using swap_non_comm_morph by blast
    qed
    thus "set w = {hd w}"
      using \<open>hd w \<in> set w\<close> by blast
  qed
  from unique_letter_wordE[OF this]
  show thesis
    using that by blast
qed

lemma bin_lcp_ims_im_lcp: "f w \<cdot> \<alpha> \<and>\<^sub>p f w' \<cdot> \<alpha> = f (w \<and>\<^sub>p w') \<cdot> \<alpha>"
proof (cases "w \<bowtie> w'")
  assume "w \<bowtie> w'"
  from disjE[OF this[unfolded prefix_comparable_def]]
  consider "w \<le>p w'" | "w' \<le>p w" by blast
  thus ?thesis
  proof (cases)
    assume "w \<le>p w'"
    hence "f w \<cdot> \<alpha> \<le>p f w' \<cdot> \<alpha>"
      using pref_mono_lcp by blast
    from this[folded lcp_pref_conv]
    show ?thesis
      unfolding \<open>w \<le>p w'\<close>[folded lcp_pref_conv].
  next
    assume "w' \<le>p w"
    hence "f w' \<cdot> \<alpha> \<le>p f w \<cdot> \<alpha>"
      using pref_mono_lcp by blast
    from this[folded lcp_pref_conv]
    show ?thesis
      unfolding lcp_sym[of "f w \<cdot> \<alpha>"] \<open>w' \<le>p w\<close>[folded lcp_pref_conv, unfolded lcp_sym[of w']].
  qed
next
  assume "\<not> w \<bowtie> w'"
  from lcp_mismatchE[OF this]
  obtain ws ws' where "(w \<and>\<^sub>p w') \<cdot> ws = w" "(w \<and>\<^sub>p w') \<cdot> ws' = w'"
         "ws \<noteq> \<epsilon>" "ws' \<noteq> \<epsilon>" "hd ws \<noteq> hd ws'".
  note hd_tl[OF \<open>ws \<noteq> \<epsilon>\<close>] hd_tl[OF \<open>ws' \<noteq> \<epsilon>\<close>]
  have w: "(w \<and>\<^sub>p w') \<cdot> [hd ws] \<cdot> tl ws = w"
    using \<open>(w \<and>\<^sub>p w') \<cdot> ws = w\<close> \<open>[hd ws] \<cdot> tl ws = ws\<close> by auto
  have w': "(w \<and>\<^sub>p w') \<cdot> [hd ws'] \<cdot> tl ws' = w'"
    using \<open>(w \<and>\<^sub>p w') \<cdot> ws' = w'\<close> \<open>[hd ws'] \<cdot> tl ws' = ws'\<close> by auto
  have "f((w \<and>\<^sub>p w') \<cdot> [hd ws] \<cdot> tl ws) \<cdot> \<alpha> \<and>\<^sub>p f((w \<and>\<^sub>p w') \<cdot> [hd ws'] \<cdot> tl ws') \<cdot> \<alpha> =
        f(w \<and>\<^sub>p w') \<cdot> (f ([hd ws] \<cdot> tl ws) \<cdot> \<alpha> \<and>\<^sub>p f([hd ws'] \<cdot> tl ws') \<cdot> \<alpha>)"
    unfolding morph using lcp_ext_left by auto
  thus ?thesis
    unfolding w w' bin_lcp_neq_hd[OF \<open>hd ws \<noteq> hd ws'\<close>, folded rassoc morph].
qed

lemma per_comp:
  assumes "r <p f w \<cdot> r"
  shows "r \<bowtie> f w \<cdot> \<alpha>"
  using assms
proof-
  obtain n where "r <p f w\<^sup>@n" "0 < n"
    using per_root_powE[OF assms].
  have "f w \<cdot> \<alpha> \<le>p f w \<cdot> f w \<^sup>@ (n - 1) \<cdot> \<alpha>"
    using bin_lcp_pref_all[of "w\<^sup>@(n-1)"]
    unfolding pref_cancel_conv pow_morph.
  with ruler[OF pref_ext[OF sprefD1[OF \<open>r <p f w\<^sup>@n\<close>], of \<alpha>], of "f w \<cdot> \<alpha>"]
  show ?thesis
    unfolding prefix_comparable_def pow_pos[OF \<open>0 < n\<close>] rassoc.
qed

end

subsection \<open>More translations\<close>


lemma bin_code_morph_iff': "binary_code_morphism f \<longleftrightarrow> morphism f \<and> f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
proof
  assume "binary_code_morphism f"
  hence "morphism f"
    by (simp add: binary_code_morphism_def code_morphism_def)
  have "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
    using \<open>binary_code_morphism f\<close> binary_code_morphism.non_comm_morph by auto
  thus "morphism f \<and> f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
    using \<open>morphism f\<close> by blast
next
  assume "morphism f \<and> f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
  hence "morphism f" and "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]" by force+
  from binary_code_morphism.intro[OF binary_morphism.bin_code_morphismI[OF binary_morphism.intro], OF  this]
  show "binary_code_morphism f".
  qed

lemma bin_code_morph_iff: "binary_code_morphism (bin_morph_of x y) \<longleftrightarrow> x \<cdot> y \<noteq> y \<cdot> x"
  unfolding bin_code_morph_iff'[of "bin_morph_of x y" bina, unfolded binA_simps bin_morph_ofD]
  using bin_morph_of_morph by blast

lemma bin_noner_morph_iff: "nonerasing_morphism (bin_morph_of x y) \<longleftrightarrow> x \<noteq> \<epsilon> \<and> y \<noteq> \<epsilon>"
proof
  show "x \<noteq> \<epsilon> \<and> y \<noteq> \<epsilon> \<Longrightarrow> nonerasing_morphism (bin_morph_of x y)"
    by (rule morphism.nonerI[OF bin_morph_of_morph, of x y], unfold core_def  bin_morph_of_def)
    (simp split: finite_2.split)
  show "nonerasing_morphism (bin_morph_of x y) \<Longrightarrow> x \<noteq> \<epsilon> \<and> y \<noteq> \<epsilon>"
    using nonerasing_morphism.nemp_to_nemp[of "bin_morph_of x y", of "[bina]"]
          nonerasing_morphism.nemp_to_nemp[of "bin_morph_of x y", of "[binb]"]
    unfolding bin_morph_of_def by simp_all
qed

lemma morph_bin_morph_of: "morphism f \<longleftrightarrow> bin_morph_of (f \<aa>) (f \<bb>) = f"
proof
  show "morphism f \<Longrightarrow> bin_morph_of (f \<aa>) (f \<bb>) = f"
  using  morphism.morph_concat_map'[of f]
  unfolding bin_morph_of_def case_finiteD[symmetric, of f] case_finite_2_if_else  by  blast
qed (use bin_morph_of_morph in metis)

















lemma two_bin_code_morphs_nonerasing_morphs: "binary_code_morphism g \<Longrightarrow> binary_code_morphism h \<Longrightarrow> two_nonerasing_morphisms g h"
  by (simp add: binary_code_morphism.nonerasing binary_code_morphism_def code_morphism.axioms(1) nonerasing_morphism.intro nonerasing_morphism_axioms.intro two_morphisms_def two_nonerasing_morphisms.intro)

section "Marked binary morphism"

lemma marked_binary_morphI: assumes "morphism f" and "f [a :: binA] \<noteq> \<epsilon>" and "f [1-a] \<noteq> \<epsilon>" and "hd (f [a]) \<noteq> hd (f [1-a])"
  shows "marked_morphism f"
proof (unfold_locales)
  have "f [b] \<noteq> \<epsilon>" for b
    by (rule bin_swap_exhaust[of b a]) (use assms in force)+
  thus "w = \<epsilon>" if "f w  = \<epsilon>" for w
    using morphism.noner_sings_conv[OF \<open>morphism f\<close>] that by blast
  show "c = b" if "hd (f\<^sup>\<C> c) = hd (f\<^sup>\<C> b)" for c b
  proof (rule ccontr)
    assume "c \<noteq> b"
    have "hd (f [c]) \<noteq> hd (f [b])"
      by (rule binA_neq_cases_swap[OF \<open>c \<noteq> b\<close>, of a])
         (use \<open>hd (f [a]) \<noteq> hd (f [1-a])\<close> in fastforce)+
    thus False
      using that[unfolded core_def] by contradiction
  qed
qed (simp add: morphism.morph[OF assms(1)])

locale marked_binary_morphism = marked_morphism "f :: binA list \<Rightarrow> 'a list"  for f

begin

lemma bin_marked: "hd (f \<aa>) \<noteq> hd (f \<bb>)"
  using marked_morph[of bina binb] by blast

lemma bin_marked_sing: "hd (f [a]) \<noteq> hd (f [1-a])"
  by (cases rule: finite_2.exhaust[of a]) (simp_all add: bin_marked bin_marked[symmetric])

sublocale binary_code_morphism
  using binary_code_morphism_def code_morphism_axioms by blast

lemma marked_lcp_emp: "\<alpha> = \<epsilon>"
  unfolding bin_lcp_def
proof (rule lcp_distinct_hd)
  show "hd (f \<aa> \<cdot> f \<bb>) \<noteq> hd (f \<bb> \<cdot> f \<aa>)"
  unfolding hd_append if_not_P[OF sing_to_nemp]
  using bin_marked.
qed

lemma bin_marked': "(f \<aa>)!0 \<noteq> (f \<bb>)!0"
  using bin_marked unfolding hd_conv_nth[OF bin_snd_nemp] hd_conv_nth[OF bin_fst_nemp].


lemma marked_bin_morph_pref_code: "r \<bowtie> s \<or> f (r \<cdot> z1) \<and>\<^sub>p f (s \<cdot> z2) = f (r \<and>\<^sub>p s)"
 using lcp_ext_right marked_morph_lcp[of "r \<cdot> z1" "s \<cdot> z2"] by metis





end

lemma bin_marked_preimg_hd:
  assumes "marked_binary_morphism (f :: binA list \<Rightarrow> binA list)"
  obtains c where "hd (f [c]) = a"
proof-
  interpret marked_binary_morphism f
    using assms.
  from that alphabet_or_neq[OF bin_marked]
  show thesis
    by blast
qed

section "Marked version"

context binary_code_morphism

begin

definition  marked_version ("f\<^sub>m") where "f\<^sub>m = (\<lambda> w. \<alpha>\<inverse>\<^sup>>(f w \<cdot> \<alpha>))"

lemma marked_version_conjugates: "\<alpha> \<cdot> f\<^sub>m w = f w \<cdot> \<alpha>"
  unfolding marked_version_def using lq_pref[OF bin_lcp_pref_all, of w].

lemma marked_eq_conv: "f w = f w' \<longleftrightarrow> f\<^sub>m w = f\<^sub>m w'"
 using cancel[of \<alpha> "f\<^sub>m w" "f\<^sub>m w'"] unfolding marked_version_conjugates cancel_right.

lemma marked_marked: assumes "marked_morphism f" shows "f\<^sub>m = f"
  using marked_version_conjugates[unfolded emp_simps \<open>marked_morphism f\<close>[unfolded marked_lcp_conv]]
  by blast

lemma  marked_version_all_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> f\<^sub>m w \<noteq> \<epsilon>"
  unfolding marked_version_def  using bin_lcp_pref_all nonerasing conjug_emp_emp marked_version_def by blast

lemma marked_version_binary_code_morph: "binary_code_morphism f\<^sub>m"
  unfolding bin_code_morph_iff' morphism_def
proof (unfold_locales)
  have "f (u\<cdot>v) \<cdot> \<alpha> = (f u \<cdot> \<alpha>) \<cdot> \<alpha>\<inverse>\<^sup>>(f v \<cdot> \<alpha>)" for u v
    unfolding rassoc morph cancel lq_pref[OF bin_lcp_pref_all[of v]]..
  thus "\<And>u v. f\<^sub>m (u \<cdot> v) = f\<^sub>m u \<cdot> f\<^sub>m v"
    unfolding marked_version_def  lq_reassoc[OF bin_lcp_pref_all] by presburger
  from code_morph
  show "inj f\<^sub>m"
    unfolding inj_def marked_eq_conv.
qed

interpretation mv_bcm: binary_code_morphism f\<^sub>m
  using marked_version_binary_code_morph .

lemma marked_lcs: "bin_lcs (f\<^sub>m \<aa>) (f\<^sub>m \<bb>) = \<beta> \<cdot> \<alpha>"
  unfolding bin_lcs_def morph[symmetric] lcs_ext_right[symmetric] marked_version_conjugates[symmetric] mv_bcm.morph[symmetric]
  by (rule lcs_ext_left[of "f\<^sub>m (\<aa> \<cdot> \<bb>)" "f\<^sub>m (\<bb> \<cdot> \<aa>)" "f\<^sub>m (\<aa> \<cdot> \<bb>) \<and>\<^sub>s f\<^sub>m (\<bb> \<cdot> \<aa>)  = \<alpha> \<cdot> f\<^sub>m (\<aa> \<cdot> \<bb>) \<and>\<^sub>s \<alpha> \<cdot> f\<^sub>m (\<bb> \<cdot> \<aa>)" \<alpha> \<alpha>], unfold mv_bcm.morph)
  (use mv_bcm.bin_not_comp_suf in argo, simp)

lemma bin_lcp_shift: assumes "\<^bold>|\<alpha>\<^bold>| < \<^bold>|f w\<^bold>|" shows "(f w)!\<^bold>|\<alpha>\<^bold>| = hd (f\<^sub>m w)"
proof-
  have "w \<noteq> \<epsilon>"
    using assms emp_to_emp  by fastforce
  hence "f\<^sub>m w \<noteq> \<epsilon>"
    using marked_version_all_nemp by blast
  show ?thesis
    using pref_index[of "f w" "\<alpha>\<cdot> f\<^sub>m w" "\<^bold>|\<alpha>\<^bold>|", OF prefI[of "f w" \<alpha> " \<alpha> \<cdot> f\<^sub>m w", OF marked_version_conjugates[of w, symmetric]], OF assms]
    unfolding nth_append_length_plus[of \<alpha> "f\<^sub>m w" 0, unfolded add_0_right] hd_conv_nth[of "f\<^sub>m w", symmetric, OF \<open>f\<^sub>m w \<noteq> \<epsilon>\<close>].
qed

lemma mismatch_fst: "hd (f\<^sub>m \<aa>) = c\<^sub>0"
proof-
  have "(f [bina,binb])!\<^bold>|\<alpha>\<^bold>| = hd (f\<^sub>m [bina,binb])"
    using bin_lcp_shift[of "[bina,binb]", unfolded pop_hd[of bina \<bb>]  lenmorph, OF bin_lcp_short]
    unfolding pop_hd[of bina \<bb>].
  from this[unfolded  mv_bcm.pop_hd[of bina \<bb>, unfolded not_Cons_self2[of bina \<epsilon>]] hd_append2[OF mv_bcm.bin_fst_nemp, of "f\<^sub>m \<bb>"], symmetric]
  show ?thesis
    unfolding bin_mismatch_def hd_word[of bina \<bb>] morph.
qed

lemma mismatch_snd: "hd (f\<^sub>m \<bb>) = c\<^sub>1"
proof-
  have "(f [binb,bina])!\<^bold>|\<alpha>\<^bold>| = hd (f\<^sub>m [binb,bina])"
    using bin_lcp_shift[of "[binb,bina]", unfolded pop_hd[of binb \<aa>]  lenmorph, OF bin_lcp_short[unfolded add.commute[of "\<^bold>|f \<aa>\<^bold>|"  "\<^bold>|f \<bb>\<^bold>|"]]]
    unfolding pop_hd[of binb \<aa>].
  from this[unfolded  mv_bcm.pop_hd[of binb \<aa>, unfolded not_Cons_self2[of binb \<epsilon>]] hd_append2[OF mv_bcm.bin_snd_nemp, of "f\<^sub>m \<aa>"],symmetric]
  show ?thesis
    unfolding bin_mismatch_def hd_word[of binb \<aa>] morph bin_lcp_sym[of "f \<aa>"].
qed

lemma marked_hd_neq: "hd (f\<^sub>m [a]) \<noteq> hd (f\<^sub>m [1-a])" (is "?P (a :: binA)")
    by (rule bin_induct[of ?P, unfolded binA_simps])
    (use mismatch_fst mismatch_snd bin_mismatch_neq in presburger)+

lemma marked_version_marked_morph: "marked_morphism f\<^sub>m"
  by (standard, unfold core_def)
  (use  not_swap_eq[of "\<lambda> a b. hd (f\<^sub>m [a]) = hd (f\<^sub>m [b])", OF _ marked_hd_neq] in force)

interpretation mv_mbm: marked_binary_morphism f\<^sub>m
  using  marked_version_marked_morph
  by (simp add: marked_binary_morphism_def)

lemma bin_code_pref_morph: "f u \<cdot> \<alpha> \<le>p f w \<cdot> \<alpha> \<Longrightarrow> u \<le>p w"
  unfolding marked_version_conjugates[symmetric] pref_cancel_conv
  using mv_mbm.pref_free_morph.

lemma mismatch_pref0: "[c\<^sub>0] \<le>p f\<^sub>m \<aa>"
  using  mv_bcm.sing_to_nemp[THEN hd_pref, of bina] unfolding mismatch_fst.

lemma mismatch_pref1: "[c\<^sub>1] \<le>p f\<^sub>m \<bb>"
  using mv_bcm.bin_snd_nemp[THEN hd_pref] unfolding mismatch_snd.

lemma marked_version_len: "\<^bold>|f\<^sub>m w\<^bold>| = \<^bold>|f w\<^bold>|"
  using   add_left_imp_eq[OF
      lenmorph[of \<alpha> "f\<^sub>m w", unfolded lenmorph[of "f w" \<alpha>, folded marked_version_conjugates[of w]],symmetric,
        unfolded  add.commute[of "\<^bold>|f w\<^bold>|" "\<^bold>|\<alpha>\<^bold>|"]]].

lemma bin_code_lcp: "(f r \<cdot> \<alpha>) \<and>\<^sub>p (f s \<cdot> \<alpha>) = f (r \<and>\<^sub>p s) \<cdot> \<alpha>"
  by (metis lcp_ext_left marked_version_conjugates mv_mbm.marked_morph_lcp)

lemma  not_comp_lcp: assumes "\<not> r \<bowtie> s"
  shows "f (r \<and>\<^sub>p s) \<cdot> \<alpha> = f r \<cdot> f (r \<cdot> s) \<and>\<^sub>p f s \<cdot> f (r \<cdot> s)"
proof-
  let ?r' = "(r \<and>\<^sub>p s)\<inverse>\<^sup>>r"
  let ?s' = "(r \<and>\<^sub>p s)\<inverse>\<^sup>>s"
  from lcp_mismatch_lq[OF \<open>\<not> r \<bowtie>  s\<close>]
  have "?r' \<noteq> \<epsilon>" and "?s' \<noteq> \<epsilon>" and "hd ?r' \<noteq> hd ?s'".
  have "\<not> f ((r \<and>\<^sub>p s) \<cdot> [hd ?r'] \<cdot> tl ?r') \<cdot> \<alpha> \<bowtie> f ((r \<and>\<^sub>p s) \<cdot> [hd ?s'] \<cdot> tl ?s') \<cdot> \<alpha>"
    using  bin_mismatch_swap_not_comp
    unfolding morph prefix_comparable_def rassoc pref_cancel_conv
     \<open>hd ?r' \<noteq> hd ?s'\<close>[symmetric, unfolded bin_neq_iff, symmetric].
  hence "\<not> f r \<cdot> \<alpha> \<bowtie> f s \<cdot> \<alpha>"
    unfolding hd_tl[OF \<open>?r' \<noteq> \<epsilon>\<close>] hd_tl[OF \<open>?s' \<noteq> \<epsilon>\<close>] lcp_lq.
  have pref: "f w \<cdot> \<alpha> \<le>p  f w \<cdot> f (r \<cdot> s)" for w
    unfolding pref_cancel_conv
    using append_prefixD[OF not_comp_bin_lcp_pref, OF \<open>\<not> r \<bowtie> s\<close>]  by blast
  from prefE[OF pref[of r], unfolded rassoc]
  obtain gr' where gr': "f r \<cdot> f (r \<cdot> s) = f r \<cdot> \<alpha> \<cdot> gr'".
  from prefE[OF pref[of s], unfolded rassoc]
  obtain gs' where gs': "f s \<cdot> f (r \<cdot> s) = f s \<cdot> \<alpha> \<cdot> gs'".
  thus "f (r \<and>\<^sub>p s) \<cdot> \<alpha> = f r \<cdot> f (r \<cdot> s) \<and>\<^sub>p f s \<cdot> f (r \<cdot> s)"
    unfolding bin_code_lcp[symmetric, of r s] prefix_def using \<open>\<not> f r \<cdot> \<alpha> \<bowtie> f s \<cdot> \<alpha>\<close>
     lcp_ext_right[of "f r \<cdot> \<alpha>" "f s \<cdot> \<alpha>" _  gr' gs', unfolded rassoc, folded gr' gs'] by argo
qed

lemma bin_morph_pref_conv: "f u \<cdot> \<alpha> \<le>p f v \<cdot> \<alpha> \<longleftrightarrow> u \<le>p v"
proof
  assume "u \<le>p v"
  from this[unfolded prefix_def]
  obtain z where "v = u \<cdot> z" by blast
  show "f u \<cdot> \<alpha> \<le>p f v \<cdot> \<alpha>"
    unfolding arg_cong[OF \<open>v = u \<cdot> z\<close>, of f, unfolded morph] rassoc pref_cancel_conv using bin_lcp_pref_all.
next
  assume "f u \<cdot> \<alpha> \<le>p f v \<cdot> \<alpha>"
  then show "u \<le>p v"
  unfolding marked_version_conjugates[symmetric] prefix_comparable_def pref_cancel_conv
  using mv_mbm.pref_free_morph by meson
qed

lemma bin_morph_compare_conv: "f u \<cdot> \<alpha> \<bowtie> f v \<cdot> \<alpha> \<longleftrightarrow> u \<bowtie> v"
  using bin_morph_pref_conv unfolding prefix_comparable_def by auto

lemma code_lcp': "\<not> r \<bowtie> s \<Longrightarrow> \<alpha> \<le>p f z \<Longrightarrow> \<alpha> \<le>p f z' \<Longrightarrow> f (r \<cdot> z) \<and>\<^sub>p f (s \<cdot> z') = f (r \<and>\<^sub>p s) \<cdot> \<alpha>"
proof-
  assume "\<alpha> \<le>p f z" "\<alpha> \<le>p f z'" "\<not> r \<bowtie> s"
  hence eqs: "f (r \<cdot> z) = (f r \<cdot> \<alpha>) \<cdot> (\<alpha>\<inverse>\<^sup>>f z)"  "f (s \<cdot> z') = (f s \<cdot> \<alpha>) \<cdot> (\<alpha>\<inverse>\<^sup>>f z')"
    unfolding rassoc by (metis lq_pref morph)+
  show ?thesis
    using bin_morph_compare_conv  \<open>\<not> r \<bowtie> s\<close> bin_code_lcp lcp_ext_right unfolding eqs
    by metis
qed

lemma non_comm_im_lcp:  assumes "u \<cdot> v \<noteq> v \<cdot> u"
  shows "f (u \<cdot> v) \<and>\<^sub>p f (v \<cdot> u) = f (u \<cdot> v \<and>\<^sub>p v \<cdot> u) \<cdot> \<alpha>"
proof-
  have "\<not> f (u \<cdot> v) \<bowtie> f (v \<cdot> u)"
    using assms comm_comp_eq[of "f u" "f v", folded morph, THEN code_morph_code] by blast
  from lcp_ext_right_conv[OF this, of \<alpha> \<alpha>, unfolded bin_code_lcp, symmetric]
  show ?thesis.
qed

end

\<comment> \<open>Obtaining one morphism marked from two general morphisms by shift (conjugation)\<close>

locale binary_code_morphism_shift = binary_code_morphism +
  fixes \<alpha>'
  assumes shift_pref: "\<alpha>' \<le>p \<alpha>"

begin

definition shifted_f where "shifted_f = (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(f w \<cdot> \<alpha>'))"

lemma shift_pref_all: "\<alpha>' \<le>p f w \<cdot> \<alpha>'"
proof-
  have "\<alpha>' \<cdot> \<alpha>'\<inverse>\<^sup>>\<alpha> \<le>p f w \<cdot> \<alpha>' \<cdot> \<alpha>'\<inverse>\<^sup>>\<alpha>"
    unfolding lq_pref[OF shift_pref] rassoc using  bin_lcp_pref_all.
  thus ?thesis
    using pref_keeps_per_root by blast
qed

sublocale shifted: binary_code_morphism shifted_f
proof-
  have morph: "f (u\<cdot>v) \<cdot> \<alpha>' = (f u \<cdot> \<alpha>') \<cdot> \<alpha>'\<inverse>\<^sup>>(f v \<cdot> \<alpha>')" for u v
    unfolding rassoc morph cancel lq_pref[OF shift_pref_all]..
  then interpret morphism shifted_f
    unfolding shifted_f_def morphism_def
     using lq_reassoc[OF shift_pref_all] by presburger
  have "inj shifted_f"
    unfolding inj_on_def shifted_f_def using lq_pref[OF shift_pref_all]
    using cancel_right code_morph_code by metis
  then show "binary_code_morphism shifted_f"
    by unfold_locales
qed

lemma shifted_lcp: "\<alpha>' \<cdot> shifted.bin_code_lcp = \<alpha>"
  unfolding bin_lcp_def shifted_f_def lcp_ext_left[symmetric]
  unfolding lassoc lq_pref[OF shift_pref_all]
  unfolding rassoc lq_pref[OF shift_pref_all]
  using lcp_ext_right_conv[OF bin_not_comp, unfolded rassoc].

lemma "\<alpha>' = \<alpha> \<Longrightarrow> shifted_f = f\<^sub>m"
  unfolding shifted_f_def marked_version_def by fast

end

section "Two binary code morphisms"

locale  two_binary_code_morphisms =
  g: binary_code_morphism g +
  h: binary_code_morphism h
  for g h :: "binA list \<Rightarrow> 'a list"

begin

notation  h.bin_code_lcp ("\<alpha>\<^sub>h")
notation  g.bin_code_lcp ("\<alpha>\<^sub>g")
notation "g.marked_version" ("g\<^sub>m")
notation "h.marked_version" ("h\<^sub>m")

sublocale gm: marked_binary_morphism g\<^sub>m
  by (simp add: g.marked_version_marked_morph marked_binary_morphism.intro)

sublocale hm: marked_binary_morphism h\<^sub>m
  by (simp add: h.marked_version_marked_morph marked_binary_morphism.intro)

sublocale two_binary_morphisms g h..

sublocale marked: two_marked_morphisms g\<^sub>m h\<^sub>m..

(*NB: properties of g\<^sub>m and h\<^sub>m are available in the namespace gm and hm, not marked.g. and marked.h.
  It would be possible to get their properties of marked morphisms through marked.g. and marked.h.
  but not their properties of marked binary morphisms, since

  sublocale marked: two_binary_marked_morphisms g\<^sub>m h\<^sub>m..

  would loop.

  See, for illustration, the mixed solution:

-------------------
sublocale marked: two_marked_morphisms g\<^sub>m h\<^sub>m
proof-
  interpret marked_binary_morphism h\<^sub>m
    by (simp add: h.marked_version_marked_morph marked_binary_morphism.intro)
  show "two_marked_morphisms g\<^sub>m h\<^sub>m"..
qed
-------------------

instead of

-------------------
sublocale hm: marked_binary_morphism h\<^sub>m
  by (simp add: h.marked_version_marked_morph marked_binary_morphism.intro)

sublocale marked: two_marked_morphisms g\<^sub>m h\<^sub>m..
-------------------

and then

-------------------
find_theorems name: code_morph_code
--------------------
*)

sublocale code: two_code_morphisms g h
  by unfold_locales

lemma marked_two_binary_code_morphisms: "two_binary_code_morphisms g\<^sub>m h\<^sub>m"
      using g.marked_version_binary_code_morph h.marked_version_binary_code_morph
    by unfold_locales

lemma revs_two_binary_code_morphisms: "two_binary_code_morphisms (rev_map g) (rev_map h)"
  using code.revs_two_code_morphisms rev_morphs
  by (simp add: g.bin_code_morph_rev_map h.bin_code_morph_rev_map rev_morphs two_binary_code_morphisms_def)

lemma swap_two_binary_code_morphisms: "two_binary_code_morphisms h g"
    by unfold_locales

text\<open>Each successful overflow has a unique minimal successful continuation\<close>
lemma  min_completionE:
  assumes "z \<cdot> g\<^sub>m r = z' \<cdot> h\<^sub>m s"
  obtains p q where "z \<cdot> g\<^sub>m p = z' \<cdot> h\<^sub>m q" and
    "\<And> r s. z \<cdot> g\<^sub>m r = z' \<cdot> h\<^sub>m s  \<Longrightarrow> p \<le>p r \<and> q \<le>p s"
proof-
  interpret swap: two_binary_code_morphisms h g
    by unfold_locales
  define P where "P = (\<lambda> m. \<exists> p q. z \<cdot> g\<^sub>m p = z' \<cdot> h\<^sub>m q \<and> \<^bold>|p\<^bold>| = m)"
  have "P \<^bold>|r\<^bold>|" using assms P_def
    by blast
  obtain n where ndef: "n = (LEAST m. P m)"
    by simp
  then obtain p q where "z \<cdot> g\<^sub>m p = z' \<cdot> h\<^sub>m q" "\<^bold>|p\<^bold>| = n" using \<open>P \<^bold>|r\<^bold>|\<close>
    using LeastI P_def by metis
  have "p \<le>p r' \<and> q \<le>p s'" if "z \<cdot> g\<^sub>m r' = z' \<cdot> h\<^sub>m s'" for r' s'
  proof
    have "z \<cdot> g\<^sub>m (p \<and>\<^sub>p r') = z' \<cdot> h\<^sub>m (q \<and>\<^sub>p s')"
      using \<open>z \<cdot> g\<^sub>m p = z' \<cdot> h\<^sub>m q\<close> \<open>z \<cdot> g\<^sub>m r' = z' \<cdot> h\<^sub>m s'\<close>
        marked.unique_continuation by blast
    thus "p \<le>p r'"
      using  P_def le_antisym \<open>\<^bold>|p\<^bold>| = n\<close> lcp_len' ndef not_less_Least
      by metis
    from this[folded lcp_pref_conv]
    have "h\<^sub>m q =  h\<^sub>m (q \<and>\<^sub>p s')"
      using \<open>z \<cdot> g\<^sub>m (p \<and>\<^sub>p r') = z' \<cdot> h\<^sub>m (q \<and>\<^sub>p s')\<close> \<open>z \<cdot> g\<^sub>m p = z' \<cdot> h\<^sub>m q\<close>
      by force
    thus "q \<le>p s'"
      using hm.code_morph_code lcp_pref_conv by metis
  qed
  thus thesis
    using \<open>z \<cdot> g\<^sub>m p = z' \<cdot> h\<^sub>m q\<close> that by blast
qed

lemma two_equals:
  assumes "g r = h r" and "g s = h s" and "\<not> r \<bowtie> s"
  shows  "g (r \<and>\<^sub>p s) \<cdot> \<alpha>\<^sub>g = h (r \<and>\<^sub>p s) \<cdot> \<alpha>\<^sub>h"
  unfolding g.not_comp_lcp[OF \<open>\<not> r \<bowtie> s\<close>] h.not_comp_lcp[OF \<open>\<not> r \<bowtie> s\<close>] g.morph h.morph assms..

lemma solution_sing_len_diff: assumes "g \<noteq> h" and "g s = h s" and "set s = binUNIV"
  shows "\<^bold>|g [c]\<^bold>| \<noteq> \<^bold>|h [c]\<^bold>|"
proof (rule solution_sing_len_cases[OF \<open>set s = binUNIV\<close> \<open>g s = h s\<close> \<open>g \<noteq> h\<close>])
  fix a  assume less: "\<^bold>|g [a]\<^bold>| < \<^bold>|h [a]\<^bold>|" "\<^bold>|h [1 - a]\<^bold>| < \<^bold>|g [1 - a]\<^bold>|"
  show "\<^bold>|g [c]\<^bold>| \<noteq> \<^bold>|h [c]\<^bold>|"
    by (rule bin_swap_exhaust[of c a]) (use less in force)+
qed

lemma  alphas_pref: assumes "\<^bold>|\<alpha>\<^sub>h\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>g\<^bold>|" and "g r =\<^sub>m h s" shows "\<alpha>\<^sub>h \<le>p \<alpha>\<^sub>g"
proof-
  have "s \<noteq> \<epsilon>" and "r \<noteq> \<epsilon>"
    using min_coinD'[OF \<open>g r =\<^sub>m h s\<close>]  by force+
  from
    root_ruler[OF h.bin_lcp_spref_all[OF \<open>s \<noteq> \<epsilon>\<close>] g.bin_lcp_spref_all[OF \<open>r \<noteq> \<epsilon>\<close>, unfolded min_coinD[OF \<open>g r =\<^sub>m h s\<close>]]]
  show "\<alpha>\<^sub>h \<le>p \<alpha>\<^sub>g"
    unfolding prefix_comparable_def using ruler_le[OF self_pref _ assms(1)] by blast
qed

end

locale  binary_codes_coincidence = two_binary_code_morphisms +
  assumes alphas_len: "\<^bold>|\<alpha>\<^sub>h\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>g\<^bold>|" and
    coin_ex: "\<exists> r s. g r =\<^sub>m h s"
begin

lemma  alphas_pref: "\<alpha>\<^sub>h \<le>p \<alpha>\<^sub>g"
  using alphas_pref[OF alphas_len] coin_ex by force

definition \<alpha> where "\<alpha> \<equiv> \<alpha>\<^sub>h\<inverse>\<^sup>>\<alpha>\<^sub>g"
definition critical_overflow ("\<c>") where "critical_overflow \<equiv> \<alpha>\<^sub>g\<^sup><\<inverse>\<alpha>\<^sub>h"

lemma lcp_diff: "\<alpha>\<^sub>h \<cdot> \<alpha> = \<alpha>\<^sub>g"
  unfolding \<alpha>_def lq_pref using lq_pref[OF alphas_pref].

lemma  solution_marked_version_conv: "g r = h s \<longleftrightarrow> \<alpha> \<cdot>  g\<^sub>m r = h\<^sub>m s \<cdot> \<alpha> "
  unfolding cancel[of  \<alpha>\<^sub>h "\<alpha> \<cdot> g\<^sub>m r" "h\<^sub>m s \<cdot> \<alpha>", symmetric]
  unfolding lassoc lcp_diff h.marked_version_conjugates g.marked_version_conjugates
  unfolding rassoc lcp_diff cancel_right..

end

locale binary_code_coincidence_sym = two_binary_code_morphisms
 + assumes
  coin_ex: "\<exists> r s. g r =\<^sub>m h s"
begin

lemma coinE: obtains u v where "g u =\<^sub>m h v" and  "h v =\<^sub>m g u"
  using coin_ex code.min_coin_prefE[OF min_solD[of _ g h]] min_coin_sym  by metis

definition \<alpha>' where "\<alpha>' = (if \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>| then \<alpha>\<^sub>g else \<alpha>\<^sub>h)"
definition g' where "g' = (if \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>| then (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(g w \<cdot> \<alpha>')) else (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(h w \<cdot> \<alpha>')))"
definition h' where "h' = (if \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>| then (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(h w \<cdot> \<alpha>')) else (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(g w \<cdot> \<alpha>')))"

lemma shift_pref_fst: "\<alpha>' \<le>p \<alpha>\<^sub>g"
  unfolding \<alpha>'_def
proof (cases "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|", simp)
  show "\<not> \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>| \<Longrightarrow> (if \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>| then \<alpha>\<^sub>g else \<alpha>\<^sub>h) \<le>p \<alpha>\<^sub>g"
    using  alphas_pref coinE  by fastforce
qed

interpretation gshift: binary_code_morphism_shift g \<alpha>'
   using shift_pref_fst by unfold_locales

interpretation swap: two_binary_code_morphisms h g
    by (simp add: swap_two_binary_code_morphisms)

lemma shift_pref_snd: "\<alpha>' \<le>p \<alpha>\<^sub>h"
  unfolding \<alpha>'_def
proof (cases "\<not> \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|", simp_all)
  show "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>| \<Longrightarrow> \<alpha>\<^sub>g \<le>p \<alpha>\<^sub>h"
    using  swap.alphas_pref[OF _ coinE] by blast
qed

interpretation hshift: binary_code_morphism_shift h \<alpha>'
   using shift_pref_snd by unfold_locales

lemma shifted_eq_conv:"g r = h s \<longleftrightarrow> g' r = h' s"
  oops

lemma shifted_eq_conv:"g r = h r \<longleftrightarrow> g' r = h' r"
proof-
  have "g r = h r \<longleftrightarrow> \<alpha>'\<inverse>\<^sup>>(g r \<cdot> \<alpha>') = \<alpha>'\<inverse>\<^sup>>(h r \<cdot> \<alpha>')"
    using cancel_right lq_pref gshift.shift_pref_all hshift.shift_pref_all by metis
  thus "g r = h r \<longleftrightarrow> g' r = h' r"
    unfolding g'_def h'_def
    by (cases "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|", presburger)
     fastforce
qed

lemma shifted_eq_conv':"g = h \<longleftrightarrow> g' = h'"
  using shifted_eq_conv by fastforce

interpretation shifted_g: binary_code_morphism "(\<lambda> w. \<alpha>'\<inverse>\<^sup>>(g w \<cdot> \<alpha>'))"
    using gshift.shifted.binary_code_morphism_axioms[unfolded gshift.shifted_f_def].

interpretation shifted_h: binary_code_morphism "(\<lambda> w. \<alpha>'\<inverse>\<^sup>>(h w \<cdot> \<alpha>'))"
    using hshift.shifted.binary_code_morphism_axioms[unfolded hshift.shifted_f_def].

lemma shifted_min_sol_conv: "r \<in> g =\<^sub>M h \<longleftrightarrow> r \<in> g' =\<^sub>M h'"
  unfolding min_sol_def using shifted_eq_conv by blast

lemma shifted_not_triv: "g = h \<longleftrightarrow> g' = h'"
  using shifted_eq_conv by fastforce

sublocale shifted: two_binary_code_morphisms g' h'
proof-
  interpret g': binary_code_morphism g'
    unfolding g'_def using shifted_g.binary_code_morphism_axioms shifted_h.binary_code_morphism_axioms by presburger
  interpret h': binary_code_morphism h'
    unfolding h'_def using shifted_g.binary_code_morphism_axioms shifted_h.binary_code_morphism_axioms by presburger
  show "two_binary_code_morphisms g' h'"..
qed

lemma shifted_fst_lcp_emp:  "shifted.g.bin_code_lcp = \<epsilon>"
  unfolding bin_lcp_def
proof (cases "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|")
  assume "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|"
  hence *: "\<alpha>' = \<alpha>\<^sub>g" "g' = (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(g w \<cdot> \<alpha>'))"
    unfolding \<alpha>'_def g'_def by simp_all
  have "g\<^sub>m \<aa> \<cdot> g\<^sub>m \<bb> \<and>\<^sub>p g\<^sub>m \<bb> \<cdot> g\<^sub>m \<aa> = \<epsilon>"
    using gm.marked_lcp_emp unfolding bin_lcp_def.
  thus "g' \<aa> \<cdot> g' \<bb> \<and>\<^sub>p g' \<bb> \<cdot> g' \<aa> = \<epsilon>"
    unfolding * g.marked_version_def.
next
  assume "\<not> \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|"
  hence c: "\<alpha>' = \<alpha>\<^sub>h" "g' = (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(h w \<cdot> \<alpha>'))"
    unfolding \<alpha>'_def g'_def by simp_all
  have "h\<^sub>m \<aa> \<cdot> h\<^sub>m \<bb> \<and>\<^sub>p h\<^sub>m \<bb> \<cdot> h\<^sub>m \<aa> = \<epsilon>"
    using hm.marked_lcp_emp unfolding bin_lcp_def.
  thus "g' \<aa> \<cdot> g' \<bb> \<and>\<^sub>p g' \<bb> \<cdot> g' \<aa> = \<epsilon>"
    unfolding c h.marked_version_def.
qed

lemma shifted_alphas: assumes le:  "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|"
  shows "\<alpha>' \<cdot> shifted.g.bin_code_lcp = \<alpha>\<^sub>g" and "\<alpha>' \<cdot> shifted.h.bin_code_lcp = \<alpha>\<^sub>h"
proof-
  have c: "\<alpha>' = \<alpha>\<^sub>g" "g' = (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(g w \<cdot> \<alpha>'))" "h' = (\<lambda> w. \<alpha>'\<inverse>\<^sup>>(h w \<cdot> \<alpha>'))"
    using le unfolding \<alpha>'_def g'_def h'_def by simp_all
  interpret binary_codes_coincidence h g
  proof
    show "\<exists>r s. h r =\<^sub>m g s"
    using coin_ex[unfolded min_coin_sym_iff[of g]] by blast
  qed fact
  show "\<alpha>' \<cdot> shifted.g.bin_code_lcp = \<alpha>\<^sub>g"
    unfolding c
    unfolding bin_lcp_def[of "g' \<aa>", unfolded c] lcp_ext_left[symmetric]
    unfolding lassoc lq_pref[OF g.bin_lcp_pref_all]
    unfolding rassoc lq_pref[OF g.bin_lcp_pref_all]
    unfolding lcp_ext_right_conv[OF g.non_comp_morph[of bina], unfolded binA_simps rassoc]
    unfolding bin_lcp_def..
  from pref_prod_pref[OF pref_trans[OF alphas_pref h.bin_lcp_pref_all] alphas_pref]
  have pref_all:  "\<alpha>\<^sub>g \<le>p h w \<cdot> \<alpha>\<^sub>g" for w.
  show "\<alpha>' \<cdot> shifted.h.bin_code_lcp = \<alpha>\<^sub>h"
    unfolding c
    unfolding bin_lcp_def[of "h' \<aa>", unfolded c] lcp_ext_left[symmetric]
    unfolding lassoc lq_pref[OF pref_all]
    unfolding rassoc lq_pref[OF pref_all]
    unfolding lcp_ext_right_conv[OF h.non_comp_morph[of bina], unfolded binA_simps rassoc]
    unfolding bin_lcp_def..
qed

interpretation swapped: binary_code_coincidence_sym h g
proof
  show "\<exists>r s. h r =\<^sub>m g s"
  using coin_ex[unfolded min_coin_sym_iff[of g]] by blast
qed

lemma eq_len_eq_conv: "\<alpha>\<^sub>g = \<alpha>\<^sub>h \<longleftrightarrow> \<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|"
proof
  show "\<alpha>\<^sub>g = \<alpha>\<^sub>h" if  "\<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|"
    using swap.alphas_pref[OF eq_imp_le[OF that]] alphas_pref[OF eq_imp_le[OF that[symmetric]]]
    using coinE[of "\<alpha>\<^sub>g = \<alpha>\<^sub>h"] by fastforce
qed simp

lemma shift_swapped: "swapped.\<alpha>' = \<alpha>'"
  unfolding \<alpha>'_def swapped.\<alpha>'_def using eq_len_eq_conv by fastforce

lemma morphs_swapped: assumes "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<noteq> \<^bold>|\<alpha>\<^sub>h\<^bold>|" shows "swapped.g' = g'" "swapped.h' = h'"
  unfolding g'_def swapped.g'_def h'_def swapped.h'_def shift_swapped using assms by fastforce+

lemma morphs_swapped': assumes "\<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|" shows "swapped.g' = h'" "swapped.h' = g'"
  unfolding g'_def swapped.g'_def h'_def swapped.h'_def shift_swapped using assms by fastforce+

lemma shifted_lcp_len_eq: "\<^bold>|shifted.g.bin_code_lcp\<^bold>| = \<^bold>|shifted.h.bin_code_lcp\<^bold>| \<longleftrightarrow> \<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|" and
  shifted_lcp_len_le: "\<^bold>|shifted.g.bin_code_lcp\<^bold>| \<le> \<^bold>|shifted.h.bin_code_lcp\<^bold>|"
  unfolding atomize_conj
proof (cases)
  assume le:  "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|"
  note shifted_alphas[OF this]
  from lenarg[OF this(1)] lenarg[OF this(2)]
  show "(\<^bold>|shifted.g.bin_code_lcp\<^bold>| = \<^bold>|shifted.h.bin_code_lcp\<^bold>| \<longleftrightarrow> \<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|) \<and> \<^bold>|shifted.g.bin_code_lcp\<^bold>| \<le> \<^bold>|shifted.h.bin_code_lcp\<^bold>|"
    unfolding lenmorph using le by fastforce+
next
  assume "\<not> \<^bold>|\<alpha>\<^sub>g\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>h\<^bold>|"
  hence le:  "\<^bold>|\<alpha>\<^sub>h\<^bold>| \<le> \<^bold>|\<alpha>\<^sub>g\<^bold>|" by fastforce
  note swapped.shifted_alphas[OF this]
  note lens = lenarg[OF this(1)] lenarg[OF this(2)]
  show "(\<^bold>|shifted.g.bin_code_lcp\<^bold>| = \<^bold>|shifted.h.bin_code_lcp\<^bold>| \<longleftrightarrow> \<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|) \<and> \<^bold>|shifted.g.bin_code_lcp\<^bold>| \<le> \<^bold>|shifted.h.bin_code_lcp\<^bold>|"
  proof (cases)
    assume eq: "\<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|"
    show "(\<^bold>|shifted.g.bin_code_lcp\<^bold>| = \<^bold>|shifted.h.bin_code_lcp\<^bold>| \<longleftrightarrow> \<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|) \<and> \<^bold>|shifted.g.bin_code_lcp\<^bold>| \<le> \<^bold>|shifted.h.bin_code_lcp\<^bold>|"
      using lens eq unfolding shift_swapped lenmorph bin_lcp_def morphs_swapped'[OF eq] by linarith+
  next
    assume neq: "\<^bold>|\<alpha>\<^sub>g\<^bold>| \<noteq> \<^bold>|\<alpha>\<^sub>h\<^bold>|"
    from  lens
    show "(\<^bold>|shifted.g.bin_code_lcp\<^bold>| = \<^bold>|shifted.h.bin_code_lcp\<^bold>| \<longleftrightarrow> \<^bold>|\<alpha>\<^sub>g\<^bold>| = \<^bold>|\<alpha>\<^sub>h\<^bold>|) \<and> \<^bold>|shifted.g.bin_code_lcp\<^bold>| \<le> \<^bold>|shifted.h.bin_code_lcp\<^bold>|"
      using le unfolding shift_swapped lenmorph bin_lcp_def morphs_swapped[OF neq] by fastforce+
  qed
qed

          end









locale two_marked_binary_morphisms = two_marked_morphisms g h
  for g h :: "binA list \<Rightarrow> 'a list"
begin

sublocale two_binary_code_morphisms g h ..

lemma not_comm_im: assumes "g \<noteq> h" and "g s = h s" and "s \<noteq> \<epsilon>"
  and "hd s = a" and "set s = binUNIV"
shows "g[a] \<cdot> h [a] \<noteq> h[a] \<cdot> g[a]"
proof (rule notI)
  assume comm: "g[a] \<cdot> h [a] = h[a] \<cdot> g[a]"
  from hd_im_comm_eq[OF \<open>g s = h s\<close> \<open>s \<noteq> \<epsilon>\<close>] comm
  have "g [a] = h [a]"
    unfolding core_def \<open>hd s  = a\<close> by blast
  thus False
    using len_ims_sing_neq[OF \<open>g s = h s\<close> \<open>g \<noteq> h\<close> \<open>set s = binUNIV\<close>] by metis
qed

lemma sol_set_not_com_hd:
  assumes
    morphs_neq: "g \<noteq> h" and
    sol: "g s = h s" and
    sol_set: "set s = binUNIV"
  shows "g ([hd s]) \<cdot>  h ([hd s]) \<noteq> h ([hd s]) \<cdot>  g ([hd s])"
proof
  assume comm: "g [hd s] \<cdot> h [hd s] = h [hd s] \<cdot> g [hd s]"
  obtain n s' where s: "[hd s]\<^sup>@Suc n \<cdot> [1 - hd s] \<cdot> s' = s"
    using bin_distinct_letter[OF sol_set].
  have "[hd s] \<^sup>@ Suc n \<cdot> [1 - hd s] \<cdot> s' \<noteq> \<epsilon>" by blast
  from hd_im_comm_eq[OF _ this]
  have "g [hd s] = h [hd s]"
    unfolding core_def s comm using sol by blast
  thus False
    using len_ims_sing_neq[OF sol \<open>g \<noteq> h\<close> sol_set, of "hd s"] by argo
qed

sublocale g: marked_binary_morphism g
  using g.marked_marked g.marked_morphism_axioms gm.marked_binary_morphism_axioms by auto

sublocale h: marked_binary_morphism h
  using h.marked_marked h.marked_morphism_axioms hm.marked_binary_morphism_axioms by auto

sublocale revs: two_binary_code_morphisms "rev_map g"  "rev_map h"
  using revs_two_binary_code_morphisms.

end

section \<open>Two marked binary morphisms with blocks\<close>







locale two_binary_marked_blocks = two_marked_binary_morphisms +
  assumes both_blocks: "\<And> a. blockP a"

begin

sublocale sucs: two_marked_binary_morphisms suc_fst suc_snd
  using  sucs_marked_morphs[OF both_blocks, folded two_marked_binary_morphisms_def].

sublocale sucs_enc: two_marked_binary_morphisms suc_fst' suc_snd'
  using encoded_sucs[OF both_blocks, folded two_marked_binary_morphisms_def].

lemma bin_blocks_swap: "two_binary_marked_blocks h g"
proof (unfold_locales)
  fix a
  obtain c where "hd (suc_snd [c]) = a"
    using bin_marked_preimg_hd[of suc_snd]
      marked_binary_morphism_def sucs.h.marked_morphism_axioms by blast
  show "two_marked_morphisms.blockP h g a"
  proof (rule two_marked_morphisms.blockI, unfold_locales)
    show "hd (suc_snd [c]) = a" by fact
    show "h (suc_snd [c]) =\<^sub>m g (suc_fst [c])"
      using min_coin_sym[OF blockP_D[OF both_blocks]].
  qed
qed

lemma blocks_all_letters_fst: "[b] \<le>f suc_fst ([a] \<cdot> [1-a])"
proof-
  have *: "suc_fst ([a] \<cdot> [1 - a]) = [a] \<cdot> tl (suc_fst [a]) \<cdot> [1-a] \<cdot> tl (suc_fst [1 - a])"
    unfolding sucs.g.morph lassoc hd_tl[OF sucs.g.sing_to_nemp, unfolded blockP_D_hd[OF both_blocks]]..
  show ?thesis
    by (cases rule: neq_exhaust[OF bin_swap_neq, of b a], unfold *)
      (blast+)
qed

lemma blocks_all_letters_snd: "[b] \<le>f suc_snd ([a] \<cdot> [1-a])"
proof-
  have *: "suc_snd ([a] \<cdot> [1 - a]) = [hd (suc_snd [a])] \<cdot> tl (suc_snd [a]) \<cdot> [hd (suc_snd [1-a])] \<cdot> tl (suc_snd [1-a])"
    unfolding sucs.h.morph rassoc hd_tl[OF sucs.h.sing_to_nemp, unfolded blockP_D_hd[OF both_blocks]]
    unfolding  lassoc hd_tl[OF sucs.h.sing_to_nemp, unfolded blockP_D_hd[OF both_blocks]]..
        show ?thesis
  proof (cases rule: neq_exhaust[OF sucs.h.bin_marked_sing, of b a])
    assume b: "b = hd (suc_snd [a])"
    show ?thesis
      unfolding b * by blast
  next
    assume b: "b = hd (suc_snd [1-a])"
    show ?thesis
      unfolding b * by blast
  qed
qed

lemma lcs_suf_blocks_fst: "g.bin_code_lcs \<le>s g (suc_fst ([a] \<cdot> [1-a]))"
  using revs.g.bin_lcp_pref''[reversed]  g.bin_lcp_pref'' blocks_all_letters_fst by simp

lemma lcs_suf_blocks_snd: "h.bin_code_lcs \<le>s h (suc_snd ([a] \<cdot> [1-a]))"
  using revs.h.bin_lcp_pref''[reversed] h.bin_lcp_pref'' blocks_all_letters_snd by simp

lemma lcs_fst_suf_snd: "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h  sucs.h.bin_code_lcs"
proof-
  have "g.bin_code_lcs \<le>s g (suc_fst [a] \<cdot> suc_fst [1-a])" for a
    using lcs_suf_blocks_fst[of a]
    unfolding binA_simps sucs.g.morph.
  have "g.bin_code_lcs \<le>s g (suc_fst \<aa> \<cdot> suc_fst \<bb>)" and "g.bin_code_lcs \<le>s g (suc_fst \<bb> \<cdot> suc_fst \<aa>)"
    using lcs_suf_blocks_fst[of bina] lcs_suf_blocks_fst[of binb]
    unfolding binA_simps sucs.g.morph.
  hence "g.bin_code_lcs \<le>s h (suc_snd \<aa> \<cdot> suc_snd \<bb>)" and "g.bin_code_lcs \<le>s h (suc_snd \<bb> \<cdot> suc_snd \<aa>)"
    unfolding g.morph h.morph  block_eq[OF both_blocks].
  from suf_ext[OF this(1)] suf_ext[OF this(2)]
  have "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h (suc_snd \<aa> \<cdot> suc_snd \<bb>)" and "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h (suc_snd \<bb> \<cdot> suc_snd \<aa>)".
  hence "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h (suc_snd \<aa> \<cdot> suc_snd \<bb>) \<and>\<^sub>s h.bin_code_lcs \<cdot> h (suc_snd \<bb> \<cdot> suc_snd \<aa>)"
    using suf_lcs_iff by blast
  thus "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h sucs.h.bin_code_lcs"
    unfolding  revs.h.bin_code_lcp[reversed] bin_lcs_def[symmetric].
qed

lemma suf_comp_lcs: "g.bin_code_lcs \<bowtie>\<^sub>s h.bin_code_lcs"
  using lcs_suf_blocks_fst lcs_suf_blocks_snd
  unfolding  g.morph h.morph sucs.g.morph sucs.h.morph  block_eq[OF both_blocks] suf_comp_or using ruler[reversed] by blast

end

section \<open>Binary primitivity preserving morphism given by a pair of words\<close>

definition bin_prim :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "bin_prim x y \<longleftrightarrow> primitivity_preserving_morphism (bin_morph_of x y)"

lemma bin_prim_code:
  assumes "bin_prim x y"
  shows "x \<cdot> y \<noteq> y \<cdot> x"
proof -
  have "inj (bin_morph_of x y)"
    using \<open>bin_prim x y\<close> primitivity_preserving_morphism.code_morph
    by (simp add: bin_prim_def)
  then have "(bin_morph_of x y) (\<aa> \<cdot> \<bb>) \<noteq> (bin_morph_of x y) (\<bb> \<cdot> \<aa>)"
    by (blast dest: injD)
  then show "x \<cdot> y \<noteq> y \<cdot> x"
    by (simp add: bin_morph_of_def)
qed

subsection \<open>Translating to to list concatenation\<close>

lemma bin_concat_prim_pres_noner1:
  assumes "x \<noteq> y"
  and prim_pres: "\<And> ws. ws \<in> lists {x,y} \<Longrightarrow> 2 \<le> \<^bold>|ws\<^bold>| \<Longrightarrow> primitive ws \<Longrightarrow>  primitive (concat ws)"
  shows "x \<noteq> \<epsilon>"
proof
  assume "x = \<epsilon>"
  with \<open>x \<noteq> y\<close> have "y \<noteq> \<epsilon>"
    by blast
  have "primitive [x, y, y]"
    using prim_abk[OF \<open>x \<noteq> y\<close>, of 2] by simp
  with \<open>x \<noteq> y\<close> have "primitive (concat [x, y, y])"
    by (intro prim_pres) simp_all
  then show False
    by (simp add: \<open>x = \<epsilon>\<close> eq_append_not_prim)
qed

lemma bin_concat_prim_pres_noner:
  assumes "x \<noteq> y"
  and prim_pres: "\<And> ws. ws \<in> lists {x,y} \<Longrightarrow> 2 \<le> \<^bold>|ws\<^bold>| \<Longrightarrow> primitive ws \<Longrightarrow>  primitive (concat ws)"
  shows "nonerasing_morphism (bin_morph_of x y)"
proof (intro morphism.nonerI bin_morph_of_morph)
  fix a
  have "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>"
    using \<open>x \<noteq> y\<close> prim_pres
    by (fact bin_concat_prim_pres_noner1, intro bin_concat_prim_pres_noner1)
       (unfold insert_commute[of x y] eq_commute[of x y])
  then show "(bin_morph_of x y)\<^sup>\<C> a \<noteq> \<epsilon>"
    by (simp add: bin_morph_of_def core_def)
qed

lemma bin_prim_concat_prim_pres_conv:
  assumes "x \<noteq> y"
  shows "bin_prim x y \<longleftrightarrow> (\<forall>ws \<in> lists {x,y}. 2 \<le> \<^bold>|ws\<^bold>| \<longrightarrow> primitive ws \<longrightarrow> primitive (concat ws))"
  (is "_ \<longleftrightarrow> ?condition")
proof -
  define f where "f = (\<lambda>a. (if a = bina then x else y))"
  have "inj f"
    using \<open>x \<noteq> y\<close>
    by (intro linorder_injI) (simp add: less_finite_2_def f_def)
  moreover have "f ` UNIV = {x, y}"
    by (simp add: f_def insert_commute)
  ultimately have "bij_betw f UNIV {x, y}"
    unfolding bij_betw_def..
  then have bij: "bij_betw (map f) (lists UNIV) (lists {x, y})"
    by (fact bij_lists)
  have concat_map_f: "concat (map f w) = bin_morph_of x y w" for w
    by (simp add: bin_morph_of_def f_def)
  have "?condition \<Longrightarrow> nonerasing_morphism (bin_morph_of x y)"
    by (simp add: \<open>x \<noteq> y\<close> bin_concat_prim_pres_noner)
  then show "bin_prim x y \<longleftrightarrow> ?condition"
    unfolding bin_prim_def primitivity_preserving_morphism_def primitivity_preserving_morphism_axioms_def
    unfolding bij_betw_ball[OF bij] prim_map_iff[OF \<open>inj f\<close>] concat_map_f
    by auto
qed

lemma bin_prim_concat_prim_pres:
  assumes "bin_prim x y"
  shows "ws \<in> lists {x, y} \<Longrightarrow> 2 \<le> \<^bold>|ws\<^bold>| \<Longrightarrow> primitive ws \<Longrightarrow> primitive (concat ws)"
  using bin_prim_code[OF \<open>bin_prim x y\<close>] \<open>bin_prim x y\<close> bin_prim_concat_prim_pres_conv[of x y]
  by (cases "x = y") blast+

lemma bin_prim_altdef1:
  "bin_prim x y \<longleftrightarrow>
    (x \<noteq> y) \<and> (\<forall>ws \<in> lists {x,y}. 2 \<le> \<^bold>|ws\<^bold>| \<longrightarrow> primitive ws \<longrightarrow> primitive (concat ws))"
  using bin_prim_code[of x y] bin_prim_concat_prim_pres_conv[of x y]
  by blast

lemma bin_prim_altdef2:
  "bin_prim x y \<longleftrightarrow>
    (x \<cdot> y \<noteq> y \<cdot> x) \<and> (\<forall>ws \<in> lists {x,y}. 2 \<le> \<^bold>|ws\<^bold>| \<longrightarrow> primitive ws \<longrightarrow> primitive (concat ws))"
  using bin_prim_code[of x y] bin_prim_concat_prim_pres_conv[of x y]
  by blast

subsection \<open>Basic properties of @{term bin_prim}\<close>

lemma bin_prim_irrefl: "\<not> bin_prim x x"
 using bin_prim_code by blast

lemma bin_prim_symm [sym]: "bin_prim x y \<Longrightarrow> bin_prim y x"
  using bin_prim_concat_prim_pres_conv[of x y] bin_prim_concat_prim_pres_conv[of y x]
  unfolding eq_commute[of y x] insert_commute[of y x]
  by blast

lemma bin_prim_commutes: "bin_prim x y \<longleftrightarrow> bin_prim y x"
  by (blast intro: bin_prim_symm)


end
