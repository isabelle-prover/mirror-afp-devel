(*  Title:      Binary Code Morphisms
    File:       CoW.Binary_Code_Morphisms
    Author:     Štěpán Holub, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Binary_Code_Morphisms     
  imports CoWBasic Submonoids Morphisms 

begin

chapter "Binary alphabet and binary morphisms"

section "Datatype of a binary alphabet"

text\<open>Basic elements for construction of binary words.\<close>

type_notation Enum.finite_2 ("binA")
notation finite_2.a\<^sub>1 ("bin0")
notation finite_2.a\<^sub>2 ("bin1")

lemmas bin_distinct = Enum.finite_2.distinct
lemmas bin_exhaust = Enum.finite_2.exhaust
lemmas bin_induct = Enum.finite_2.induct
lemmas bin_UNIV = Enum.UNIV_finite_2 
lemmas bin_eq_neq_iff = Enum.neq_finite_2_a\<^sub>2_iff
lemmas bin_eq_neq_iff' = Enum.neq_finite_2_a\<^sub>1_iff

abbreviation bin_word_0  :: "binA list" ("\<zero>") where
  "bin_word_0 \<equiv> [bin0]"

abbreviation bin_word_1 :: "binA list" ("\<one>") where
  "bin_word_1 \<equiv> [bin1]"

abbreviation binUNIV :: "binA set" where "binUNIV \<equiv> UNIV"

lemma bin_basis_code: "code {\<zero>,\<one>}"
  by (rule bin_code_code) blast

lemma bin_num: "bin0 = 0" "bin1 = 1"
  by simp_all

lemma binsimp[simp]: "bin0 - bin1 = bin1" "bin1 - bin0 = bin1" "1 - bin0 = bin1" "1 - bin1 = bin0" "a - a = bin0" "1 - (1 - a) = a"
  by simp_all

definition bin_swap :: "binA \<Rightarrow> binA" where "bin_swap x \<equiv> 1 - x"

lemma bin_swap_if_then: "1-x = (if x = bin0 then bin1 else bin0)"
  by fastforce

definition bin_swap_morph where "bin_swap_morph \<equiv> map bin_swap"

lemma alphabet_or[simp]: "a = bin0 \<or> a = bin1" 
  by auto

lemma bin_im_or: "f [a] = f \<zero> \<or> f [a] = f \<one>" 
  by (rule bin_exhaust[of a], simp_all) 

thm triv_forall_equality

lemma binUNIV_card: "card binUNIV = 2" 
  unfolding bin_UNIV card_2_iff by auto

lemma other_letter: obtains b where "b \<noteq> (a :: binA)"
  using finite_2.distinct(1) by metis

lemma alphabet_or_neq: "x \<noteq> y \<Longrightarrow> x = (a :: binA) \<or> y = a"
  using alphabet_or[of x] alphabet_or[of y] alphabet_or[of a] by argo

lemma binA_neq_cases: assumes neq: "a \<noteq> b"
  obtains "a = bin0" and "b = bin1" | "a = bin1" and "b = bin0"
  using alphabet_or_neq assms by auto

lemma bin_neq_sym_pred: assumes "a \<noteq> b" and "P bin0 bin1" and "P bin1 bin0" shows "P a b" 
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

lemma bin_basis_singletons: "{[q] |q.  q \<in> {bin0, bin1}} = {\<zero>,\<one>}"
  by blast

lemma bin_basis_generates: "\<langle>{\<zero>,\<one>}\<rangle> = UNIV" 
  using sings_gen_lists[of binUNIV, unfolded lists_UNIV bin_UNIV bin_basis_singletons, folded bin_UNIV, unfolded lists_UNIV]. 

lemma a_in_bin_basis: "[a] \<in> {\<zero>,\<one>}"
  using Set.UNIV_I by auto

lemma lcp_zero_one_emp: "\<zero> \<and>\<^sub>p \<one> = \<epsilon>" and lcp_one_zero_emp: "\<one> \<and>\<^sub>p \<zero> = \<epsilon>"
  by simp+

lemma neq_induct: "(a::binA) \<noteq> b \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow> P c"
  by (elim binA_neq_cases) (hypsubst, rule finite_2.induct, assumption+)+

lemma neq_exhaust: assumes "(a::binA) \<noteq> b" obtains "c = a" | "c = b"
  using assms by (elim binA_neq_cases) (hypsubst, elim finite_2.exhaust, assumption)+

lemma bin_swap_neq [simp]: "1-(a :: binA) \<noteq> a" 
    by simp
lemmas bin_swap_neq'[simp] = bin_swap_neq[symmetric]

lemmas bin_swap_induct = neq_induct[OF bin_swap_neq']
   and bin_swap_exhaust = neq_exhaust[OF bin_swap_neq']

lemma bin_swap_induct': "P (a :: binA) \<Longrightarrow> P (1-a) \<Longrightarrow> (\<And> c. P c)"
  using bin_swap_induct by auto 

lemma bin_UNIV_swap: "{a, 1-a} = binUNIV" (is "?P a")
  using bin_swap_induct[of ?P bin0, unfolded binsimp] by fastforce

lemma neq_bin_swap: "c \<noteq> d \<Longrightarrow> d = 1-(c :: binA)"
   by (rule bin_swap_exhaust[of d c]) blast+

lemma neq_bin_swap': "c \<noteq> d \<Longrightarrow> c = 1-(d :: binA)"
  using neq_bin_swap by presburger

lemma bin_neq_iff: "c \<noteq> d \<longleftrightarrow> d = 1-(c :: binA)"
  using neq_bin_swap[of c d] bin_swap_neq[of c]  by argo

lemma bin_neq_iff': "c \<noteq> d \<longleftrightarrow> c = 1-(d :: binA)"
  unfolding bin_neq_iff by force

lemma bin_neq_swap': "a \<noteq> b \<Longrightarrow> b = 1-(a:: binA)"
  by (simp add: bin_neq_iff')

lemma binA_neq_cases_swap: assumes neq: "a \<noteq> (b :: binA)"
  obtains "a = c" and "b = 1 - c" | "a = 1 - c" and "b = c"
  using  bin_neq_swap'[OF assms] bin_swap_exhaust by auto

lemma bin_without_letter: assumes "(a1 :: binA) \<notin> set w"
  obtains k where "w = [1-a1]\<^sup>@k"
proof-
  have "\<forall> c. c \<in> set w \<longrightarrow> c = 1-a1"
    using assms bin_swap_exhaust by blast 
  from that unique_letter_wordE'[OF this]
  show thesis by blast
qed

lemma bin_neq_swap[intro]: "a \<noteq> b \<Longrightarrow> a = 1-(b:: binA)"
  by (simp add: bin_neq_iff')

lemma bin_empty_iff: "S = {} \<longleftrightarrow> (a :: binA) \<notin> S \<and> 1-a \<notin> S"
  using bin_swap_induct[of "\<lambda>a. a \<notin> S"] by blast

lemma bin_UNIV_iff: "S = binUNIV \<longleftrightarrow> a \<in> S \<and> 1-a \<in> S"
  using two_in_bin_UNIV[OF bin_swap_neq'] by blast

lemma bin_UNIV_I: "a \<in> S \<Longrightarrow> 1-a \<in> S \<Longrightarrow> S = binUNIV"
  using bin_UNIV_iff by blast
 
lemma swap_UNIV: "{a,1-a} = binUNIV"
  unfolding bin_UNIV_iff[of "{a,1-a}" a] by fast 

lemma bin_sing_iff: "A = {a :: binA} \<longleftrightarrow> a \<in> A \<and> 1-a \<notin> A"
proof (rule sym, intro iffI conjI, elim conjE)
  assume "a \<in> A" and "1-a \<notin> A"
  have "b \<in> A \<longleftrightarrow> b = a" for b 
    using \<open>a \<in> A\<close> \<open>1-a \<notin> A\<close> bin_swap_neq
    by (intro bin_swap_induct[of "\<lambda>c. (c \<in> A) = (c = a)" a b]) blast+
  then show "A = {a}" by blast
qed simp_all

lemma bin_set_cases: obtains "S = {}" | "S = {bin0}" | "S = {bin1}" | "S = binUNIV"
  unfolding bin_empty_iff[of _ "bin0"] bin_UNIV_iff[of _ "bin0"] bin_sing_iff  
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
  proof (cases "w = \<epsilon>", simp)
    assume "set w \<noteq> binUNIV" and "w \<noteq> \<epsilon>"
    from hd_tl[OF this(2)] this(2)
    have "hd w \<in> set w" by simp
    hence "1-hd w \<notin> set w" 
      using \<open>set w \<noteq> binUNIV\<close> unfolding swap_UNIV[symmetric, of "hd w"] by fast
    thus "set w \<subseteq> {hd w}"
      using bin_sing_iff by auto
  qed
qed

lemma not_swap_eq: "P a b \<Longrightarrow> (\<And> (c :: binA). \<not> P c (1-c)) \<Longrightarrow> a = b"
  using bin_neq_iff by metis 

lemma bin_distinct_letter: assumes "set w = binUNIV" 
  obtains k w' where "[hd w]\<^sup>@Suc k \<cdot> [1-hd w] \<cdot> w' = w"
proof-
  from distinct_letter_in_hd'[of w, unfolded set_hd_pow_conv[of w] bool_simps(1), OF assms]
  obtain m b q where "[hd w] \<^sup>@ Suc m \<cdot> [b] \<cdot> q = w" "b \<noteq> hd w".
  from that[OF this(1)[unfolded bin_neq_swap[of _ "hd w", OF this(2)]]]
  show thesis.
qed

lemma "P a \<longleftrightarrow> P (1-a) \<Longrightarrow> P a \<Longrightarrow> (\<And> (b :: binA). P b)"
  using bin_swap_induct' by blast

lemma bin_sym_all: "P (a :: binA) \<longleftrightarrow> P (1-a) \<Longrightarrow> P a \<Longrightarrow> P x"
  using bin_swap_induct[of "\<lambda> a. P a" a, unfolded binsimp] by blast

lemma bin_sym_all_comm:
  "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a] \<Longrightarrow> f [b] \<cdot> f [1-b] \<noteq> f [1-b] \<cdot> f [(b :: binA)]" (is "?P a \<Longrightarrow> ?P b")
  using bin_sym_all[of ?P a, unfolded binsimp, OF neq_commute].

lemma bin_sym_all_neq:
  "f [(a :: binA)] \<noteq> f [1-a] \<Longrightarrow> f [b] \<noteq> f [1-b]" (is "?P a \<Longrightarrow> ?P b")
  using bin_sym_all[of ?P a, unfolded binsimp, OF neq_commute].

section \<open>Binary code morphism\<close>

subsection \<open>From a binary code to a binary morphism\<close>

definition bin_morph_of' :: "'a list \<Rightarrow> 'a list \<Rightarrow> binA list \<Rightarrow> 'a list" where "bin_morph_of' x y u = concat (map (\<lambda> a. (case a of bin0 \<Rightarrow> x | bin1 \<Rightarrow> y)) u)"

definition bin_morph_of :: "'a list \<Rightarrow> 'a list \<Rightarrow> binA list \<Rightarrow> 'a list" where "bin_morph_of x y u = concat (map (\<lambda> a. if a = bin0 then x else y) u)"

lemma case_finite_2_if_else: "case_finite_2 x y = (\<lambda> a. if a = bin0 then x else y)"
    by (standard, simp split: finite_2.split)

lemma bin_morph_of_case_def: "bin_morph_of x y u = concat (map (\<lambda> a. (case a of bin0 \<Rightarrow> x | bin1 \<Rightarrow> y)) u)"
  unfolding bin_morph_of_def case_finite_2_if_else.. 

lemma case_finiteD: "case_finite_2 (f \<zero>) (f \<one>) = f\<^sup>\<C>"
proof
  show "(case x of bin0 \<Rightarrow> f \<zero> | bin1 \<Rightarrow> f \<one>) = f\<^sup>\<C> x" for x 
    unfolding core_def by (cases rule: finite_2.exhaust[of x]) auto  
qed

lemma case_finiteD': "case_finite_2 (f \<zero>) (f \<one>) u = f\<^sup>\<C> u"
  using case_finiteD by metis  

lemma bin_morph_of_maps: "bin_morph_of x y = List.maps (case_finite_2 x y)"
  unfolding bin_morph_of_def maps_def unfolding case_finite_2_if_else by simp

lemma bin_morph_of_morph: "morphism (bin_morph_of x y)"
  unfolding bin_morph_of_def by (simp add: morphism.intro)

lemma bin_morph_ofD: "(bin_morph_of x y) \<zero> = x" "(bin_morph_of x y) \<one> = y"
  unfolding bin_morph_of_def by simp_all

lemma bin_range: "range f = {f bin0, f bin1}"
  unfolding bin_UNIV by simp

lemma bin_range_swap: "range f = {f (a::binA), f (1-a)}" (is "?P a")
  using bin_swap_induct[of ?P bin0] unfolding binsimp bin_UNIV by auto

lemma bin_core_range: "range f\<^sup>\<C> = {f \<zero>, f \<one>}"
  unfolding core_def bin_range..

lemma bin_core_range_swap: "range f\<^sup>\<C> = {f [(a :: binA)], f [1-a]}" (is "?P a")
  by (rule bin_induct[of ?P, unfolded binsimp], unfold bin_core_range, simp, force)

lemma bin_map_core_lists: "(map f\<^sup>\<C> w) \<in> lists {f \<zero>, f \<one>}"
  unfolding core_def by (induct w, simp, unfold map_hd)
  (rule append_in_lists, simp_all add: bin_im_or) 

lemma bin_map_core_lists_swap: "(map f\<^sup>\<C> w) \<in> lists {f [(a :: binA)], f [1-a]}"
  using map_core_lists[of f, unfolded bin_core_range_swap[of f a]]. 

lemma bin_morph_of_core_range: "range (bin_morph_of x y)\<^sup>\<C> = {x,y}" 
  unfolding bin_core_range bin_morph_ofD.. 

lemma bin_morph_of_range: "range (bin_morph_of x y) = \<langle>{x,y}\<rangle>"
  using morphism.range_hull[of "bin_morph_of x y", unfolded bin_morph_of_core_range, OF bin_morph_of_morph]. 

lemma bin_neq_inj_core: assumes "f [(a :: binA)] \<noteq> f [1-a]" shows "inj f\<^sup>\<C>"
proof
  show "f\<^sup>\<C> x = f\<^sup>\<C> y \<Longrightarrow> x = y" for x y
  proof (rule ccontr)
    assume "x \<noteq> y"
    from bin_sym_all_neq[OF assms] 
    have "f\<^sup>\<C> x \<noteq> f\<^sup>\<C> y"
      unfolding core_def bin_neq_swap'[OF \<open>x \<noteq> y\<close>].
    thus "f\<^sup>\<C> x = f\<^sup>\<C> y \<Longrightarrow> False"
      by blast
  qed
qed

lemma bin_code_morphismI: "morphism f \<Longrightarrow> f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [(a :: binA)] \<Longrightarrow> code_morphism f"
proof (standard, simp add: morphism.morph)
  assume "morphism f" and "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [(a :: binA)]"
  from bin_sym_all_comm[OF this(2)] 
  have "f [b] \<cdot> f [1-b] \<noteq> f [1-b] \<cdot> f [b]" for b.
  hence "inj f\<^sup>\<C>"
    using bin_neq_inj_core[of f] by fastforce  
  show "inj f"
    unfolding inj_on_def
  proof (standard+)
    fix xs ys assume "f xs = f ys"
    hence "concat (map f\<^sup>\<C> xs) = concat (map f\<^sup>\<C> ys)"
      by (simp add: morphism.morph_concat_map[OF \<open>morphism f\<close>])
    from bin_code_code[unfolded code_def, rule_format,
      OF \<open>f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]\<close> bin_map_core_lists_swap bin_map_core_lists_swap this] 
    show "xs = ys"
      using \<open>inj f\<^sup>\<C>\<close> by simp
  qed
qed

subsection \<open>Locale - binary code morphism\<close>

locale binary_code_morphism = code_morphism "f :: binA list \<Rightarrow> 'a list" for f  

begin

lemma morph_bin_morph_of: "f = bin_morph_of (f \<zero>) (f \<one>)" 
  using morph_concat_map unfolding bin_morph_of_def case_finiteD
  case_finite_2_if_else[symmetric] by simp

lemma non_comm_morph [simp]: "f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]"
  unfolding morph[symmetric] using  code_morph_code bin_swap_neq by blast

lemma non_comp_morph: "\<not> f [a] \<cdot> f [1-a] \<bowtie> f [1-a] \<cdot> f [a]"
  using comm_comp_eq non_comm_morph by blast 

lemma swap_non_comm_morph [simp, intro]: "a \<noteq> b \<Longrightarrow> f [a] \<cdot> f [b] \<noteq> f [b] \<cdot> f [a]"
  using bin_neq_swap' non_comm_morph by blast

thm bin_core_range[of f]

lemma bin_code_morph_rev_map: "binary_code_morphism (rev_map f)" 
  unfolding binary_code_morphism_def using code_morphism_rev_map.


sublocale swap: binary_code "f \<one>" "f \<zero>"
  using non_comm_morph[of bin1] unfolding binsimp by unfold_locales

sublocale binary_code "f \<zero>" "f \<one>"
  using swap.bin_code_swap.

notation bin_code_lcp ("\<alpha>") and
         bin_code_lcs ("\<beta>") and
         bin_code_mismatch_fst ("c\<^sub>0") and
         bin_code_mismatch_snd ("c\<^sub>1")
term "bin_lcp (f \<zero>) (f \<one>)"
abbreviation bin_morph_mismatch ("\<cc>")
  where "bin_morph_mismatch a \<equiv> bin_mismatch (f[a]) (f[1-a])" 
abbreviation bin_morph_mismatch_suf ("\<dd>")
  where "bin_morph_mismatch_suf a \<equiv> bin_mismatch_suf (f[1-a]) (f[a])" 

lemma bin_lcp_def': "\<alpha> =  f ([a] \<cdot> [1-a]) \<and>\<^sub>p f ([1-a] \<cdot> [a])" 
  by (rule bin_exhaust[of a "\<alpha> =  f ([a] \<cdot> [1-a]) \<and>\<^sub>p f ([1-a] \<cdot> [a])"], 
  unfold morph, use binsimp(3-4) bin_lcp_def in force)
  (unfold bin_lcp_def lcp_sym[of "f[a] \<cdot> f[1-a]" "f[1-a] \<cdot> f[a]"],
  use  binsimp(3-4) in auto)

lemma bin_lcp_neq: "a \<noteq> b \<Longrightarrow> \<alpha> =  f ([a] \<cdot> [b]) \<and>\<^sub>p f ([b] \<cdot> [a])" 
  using neq_bin_swap[of a b] unfolding bin_lcp_def'[of a] by blast

lemma sing_im: "f [a] \<in>  {f \<zero>, f \<one>}" 
  using finite_2.exhaust[of a ?thesis] by fastforce 

lemma bin_mismatch_inj: "inj \<cc>"
  unfolding inj_on_def
  using non_comm_morph[folded bin_mismatch_comm] neq_bin_swap by force 

lemma map_in_lists: "map (\<lambda>x. f [x]) w \<in> lists {f \<zero>, f \<one>}" 
proof (induct w, simp)
  case (Cons a w)
  then show ?case
    unfolding list.map(2)  using sing_im by simp
qed

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
  hence "\<^bold>|f \<zero>\<^bold>| + \<^bold>|f \<one>\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    using \<open>b \<noteq> hd w\<close> alphabet_or[of b] alphabet_or[of "hd w"] add.commute by fastforce 
  thus False
    using bin_lcp_short \<open>\<^bold>|f w\<^bold>| \<le> \<^bold>|\<alpha>\<^bold>|\<close>  by linarith  
qed

(*registering nonerasing in binary_code_morphism*)
lemmas nonerasing = nonerasing
thm nonerasing_morphism.nonerasing
    binary_code_morphism.nonerasing

lemma bin_morph_lcp_mismatch_pref:
 "\<alpha> \<cdot> [\<cc> a] \<le>p f [a] \<cdot> \<alpha>"
  using binary_code.bin_fst_mismatch[OF bin_code_morph_sing] unfolding bin_lcp_sing.

lemma "[\<dd> a] \<cdot> \<beta> \<le>s \<beta> \<cdot> f [a]"    using binary_code_morphism.bin_morph_lcp_mismatch_pref[OF bin_code_morph_rev_map, reversed].

lemma bin_lcp_pref_all: "\<alpha> \<le>p f w \<cdot> \<alpha>" 
proof(induct w rule: rev_induct, simp)
  case (snoc x xs)
  from pref_prolong[OF this, of "f[x]\<cdot>\<alpha>", unfolded lassoc]
  show ?case
    unfolding morph[of xs "[x]"] using bin_lcp_fst_lcp bin_lcp_snd_lcp alphabet_or[of x] by blast    
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
    hence "\<^bold>|f \<zero>\<^bold>| + \<^bold>|f \<one>\<^bold>| \<le> \<^bold>|f w\<^bold>|"
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

lemma bin_fst_mismatch_all: "\<alpha> \<cdot> [c\<^sub>0] \<le>p f \<zero> \<cdot> f w \<cdot> \<alpha>"
  using pref_prolong[OF bin_fst_mismatch bin_lcp_pref_all[of w]].

lemma bin_snd_mismatch_all: "\<alpha> \<cdot> [c\<^sub>1] \<le>p f \<one> \<cdot> f w \<cdot> \<alpha>"
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
    unfolding power_mult assms[symmetric] pow_morph..  
  have "\<^bold>|\<alpha>\<^bold>| < \<^bold>|f ?w\<^bold>|" 
    unfolding fw pow_len sing_len by force 
  from set_mono_prefix[OF bin_long_mismatch[OF this, unfolded fw]]
  show "\<cc> a = b"
    unfolding hd set using elem by blast
qed

lemma sing_pow_mismatch_suf: "f [a] = [b]\<^sup>@Suc n \<Longrightarrow> \<dd> a = b"
  using binary_code_morphism.sing_pow_mismatch[OF bin_code_morph_rev_map, reversed].

lemma bin_mismatch_swap_all: "f [a] \<cdot> f w \<cdot> \<alpha>  \<and>\<^sub>p f [1-a] \<cdot> f w' \<cdot> \<alpha> = \<alpha>"
  using lcp_first_mismatch[OF bin_mismatch_swap_neq, of \<alpha> a]
        bin_lcp_mismatch_pref_all[of a w] bin_lcp_mismatch_pref_all[of "1-a" w']
  unfolding pref_def rassoc by force

lemma bin_mismatch_all: "f \<zero> \<cdot> f w \<cdot> \<alpha>  \<and>\<^sub>p f \<one> \<cdot> f w' \<cdot> \<alpha> = \<alpha>"
  using bin_mismatch_swap_all[of bin0, unfolded binsimp].

lemma bin_mismatch_swap_not_comp: "\<not> f [a] \<cdot> f w \<cdot> \<alpha>  \<bowtie> f [1-a] \<cdot> f w' \<cdot> \<alpha>"
  unfolding prefix_comparable_def lcp_pref_conv[symmetric] bin_mismatch_swap_all 
            bin_mismatch_swap_all[of "1-a", unfolded binsimp] using sing_to_nemp by auto 

lemma bin_lcp_root: "\<alpha> \<le>p (f [a])\<^sup>\<omega>"
  using alphabet_or[of a] per_rootI[OF bin_lcp_pref_all[of \<one>] bin_snd_nemp] per_rootI[OF bin_lcp_pref_all[of \<zero>] bin_fst_nemp] by blast 

lemma bin_lcp_pref: assumes "w \<notin> \<one>*" and  "w \<notin> \<zero>*"
  shows "\<alpha> \<le>p (f w)"
proof-
  have "w \<noteq> \<epsilon>"
    using \<open>\<not> (w \<in> \<one>*)\<close> emp_all_roots by blast
  have "w \<notin> [hd w]*" 
    using assms alphabet_or[of "hd w"]  by presburger
  hence "\<^bold>|\<alpha>\<^bold>| \<le> \<^bold>|f w\<^bold>|"
    using long_bin_lcp[OF \<open>w \<noteq> \<epsilon>\<close>] nat_le_linear[of "\<^bold>|f w\<^bold>|" "\<^bold>|\<alpha>\<^bold>|" ] by blast
  show ?thesis
    using  pref_prod_le[OF bin_lcp_pref_all \<open>\<^bold>|\<alpha>\<^bold>| \<le> \<^bold>|f w\<^bold>|\<close>].
qed

lemma bin_mismatch_sings: "a \<noteq> b \<Longrightarrow> f [a] \<cdot> \<alpha>  \<and>\<^sub>p f [b] \<cdot> \<alpha> = \<alpha>" 
  using bin_mismatch bin_mismatch[unfolded lcp_sym[of "f \<zero> \<cdot> \<alpha>" "f \<one> \<cdot> \<alpha>"]]
  by  (elim bin_neq_sym_pred)

lemma bin_lcp_pref'': "[a] \<le>f w \<Longrightarrow> [1-a] \<le>f w  \<Longrightarrow> \<alpha> \<le>p (f w)"
  using  bin_lcp_pref[of w]  sing_pow_fac'[OF bin_distinct(1),of w] sing_pow_fac'[OF bin_distinct(2), of w]
  by (cases rule: finite_2.exhaust[of a]) force+

lemma bin_lcp_pref': "\<zero> \<le>f w \<Longrightarrow> \<one> \<le>f w  \<Longrightarrow> \<alpha> \<le>p (f w)" 
  using bin_lcp_pref''[of bin0, unfolded binsimp]. 

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

lemma bin_lcp_comp_hd: "\<alpha> \<bowtie> f (\<zero> \<cdot> w0) \<and>\<^sub>p  f (\<one> \<cdot> w1)"
  using  ruler[OF bin_lcp_pref_all[of "\<zero> \<cdot> w0"]
      pref_trans[OF lcp_pref[of "f (\<zero> \<cdot> w0)" "f (\<one> \<cdot> w1)"], of "f (\<zero> \<cdot> w0) \<cdot> \<alpha>", OF triv_pref]] 
  unfolding prefix_comparable_def. 

lemma sing_mismatch: assumes "f \<zero> \<in> [a]*" shows "c\<^sub>0 = a"
proof- 
  have "\<alpha> \<in> [a]*"
    using per_one[OF per_root_trans[OF bin_lcp_root assms]].
  hence "f \<zero> \<cdot> \<alpha> \<in> [a]*"
    using \<open>f \<zero> \<in> [a]*\<close> add_roots by blast 
  from sing_pow_fac'[OF _ this, of "c\<^sub>0"]
  show "c\<^sub>0 = a"  
    using facI'[OF lq_pref[OF bin_fst_mismatch, unfolded rassoc]] by blast
qed

lemma sing_mismatch': assumes "f \<one> \<in> [a]*" shows "c\<^sub>1 = a" 
proof- 
  have "\<alpha> \<in> [a]*"
    using per_one[OF per_root_trans[OF bin_lcp_root assms]].
  hence "f \<one> \<cdot> \<alpha> \<in> [a]*"
    using \<open>f \<one> \<in> [a]*\<close> add_roots by blast 
  from sing_pow_fac'[OF _ this, of "c\<^sub>1"]
  show ?thesis
    using facI'[OF lq_pref[OF bin_snd_mismatch, unfolded rassoc]] by blast 
qed

lemma bin_lcp_comp_all: "\<alpha> \<bowtie> (f w)"
  unfolding prefix_comparable_def using ruler[OF bin_lcp_pref_all triv_pref].

lemma not_comp_bin_swap: "\<not> f [a] \<cdot> \<alpha> \<bowtie> f [1-a] \<cdot> \<alpha>" 
  by (rule bin_exhaust[of a ?thesis], use not_comp_bin_fst_snd in simp_all)

lemma mismatch_pref: 
  assumes "\<alpha> \<le>p f ([a] \<cdot> w0)" and "\<alpha> \<le>p f ([1-a] \<cdot> w1)" 
  shows "\<alpha> = f ([a] \<cdot> w0) \<and>\<^sub>p f ([1-a] \<cdot> w1)" 
proof-
  have "f ([a] \<cdot> w0) \<cdot> \<alpha> \<and>\<^sub>p f ([1-a] \<cdot> w1) \<cdot> \<alpha> = \<alpha>"
    unfolding morph using bin_mismatch_swap_all[unfolded lassoc]. 
  hence "f ([a] \<cdot> w0) \<and>\<^sub>p f ([1-a] \<cdot> w1) \<le>p \<alpha>"
    using lcp_pref_monotone[OF triv_pref[of "f ([a] \<cdot> w0)" \<alpha>] triv_pref[of "f ([1-a] \<cdot> w1)" \<alpha>]]
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
  have "hd (f \<zero> \<cdot> f \<one>) \<noteq> hd (f \<one> \<cdot> f \<zero>)"
    using hd_append finite_2.distinct by auto
  thus "\<alpha> = \<epsilon>"
    unfolding bin_lcp_def using lcp_distinct_hd by blast 
next
  assume "\<alpha> = \<epsilon>"
  have "hd (f \<zero>) \<noteq> hd (f \<one>)" 
    by (rule nemp_lcp_distinct_hd[OF sing_to_nemp sing_to_nemp])
    (use  lcp_append_monotone[of "f \<zero>" "f \<one>" "f \<one>" "f \<zero>", unfolded \<open>\<alpha> = \<epsilon>\<close>[unfolded bin_lcp_def]]
    in simp)
  show "marked_morphism f"
  proof 
    fix a b :: binA assume "hd (f\<^sup>\<C> a) = hd (f\<^sup>\<C> b)" 
    thus "a = b" 
      unfolding core_def using \<open>hd (f \<zero>) \<noteq> hd (f \<one>)\<close> 
      by (induction a) (rule bin_exhaust[of b], simp_all, rule bin_exhaust[of b], simp_all)
  qed
qed

lemma im_comm_lcp: "f w \<cdot> \<alpha> = \<alpha> \<cdot> f w \<Longrightarrow> (\<forall> a. a \<in> set w \<longrightarrow> f [a] \<cdot> \<alpha> = \<alpha> \<cdot> f [a])"
proof (induct w, simp)
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
      using eqd_eq[of "\<alpha> \<cdot> f [a]", OF _swap_len] unfolding pref_def eq rassoc by metis
    from eq[unfolded lassoc, folded this, unfolded rassoc cancel]
    have "f w \<cdot> \<alpha> = \<alpha> \<cdot> f w".
    from Cons.hyps[OF this] \<open>f [a] \<cdot> \<alpha> = \<alpha> \<cdot> f [a]\<close>
    show ?thesis by fastforce
  qed
qed

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

end

subsection \<open>More translations\<close>

lemma bin_code_code_morph: "binary_code x y \<Longrightarrow> code_morphism (bin_morph_of x y)"
  using bin_code_morphismI[of _ bin0, unfolded binsimp, OF bin_morph_of_morph, unfolded bin_morph_ofD, OF binary_code.non_comm]. 

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
  interpret morphism f
    using \<open>morphism f\<close>.
  interpret binary_code "f [a]" "f [1-a]"
    using binary_code.intro[OF \<open>f [a] \<cdot> f [1-a] \<noteq> f [1-a] \<cdot> f [a]\<close>]. 
  show "binary_code_morphism f"
    using \<open>morphism f \<and> f [a] \<cdot> f [1 - a] \<noteq> f [1 - a] \<cdot> f [a]\<close> bin_code_morphismI binary_code_morphism.intro by blast 
  qed

lemma bin_code_morph_iff: "binary_code_morphism (bin_morph_of x y) \<longleftrightarrow> x \<cdot> y \<noteq> y \<cdot> x"
  unfolding bin_code_morph_iff'[of "bin_morph_of x y" bin0, unfolded binsimp bin_morph_ofD] 
  using bin_morph_of_morph by blast

lemma bin_noner_morph_iff: "nonerasing_morphism (bin_morph_of x y) \<longleftrightarrow> x \<noteq> \<epsilon> \<and> y \<noteq> \<epsilon>"
proof
  show "x \<noteq> \<epsilon> \<and> y \<noteq> \<epsilon> \<Longrightarrow> nonerasing_morphism (bin_morph_of x y)"
    by (rule morphism.nonerI[OF bin_morph_of_morph, of x y], unfold core_def  bin_morph_of_def)
    (simp split: finite_2.split)
  show "nonerasing_morphism (bin_morph_of x y) \<Longrightarrow> x \<noteq> \<epsilon> \<and> y \<noteq> \<epsilon>"
    using nonerasing_morphism.nemp_to_nemp[of "bin_morph_of x y", of "[bin0]"]
          nonerasing_morphism.nemp_to_nemp[of "bin_morph_of x y", of "[bin1]"]
    unfolding bin_morph_of_def by simp_all
qed

thm bin_neq_inj_core
    bin_core_range


lemma morph_bin_morph_of: "morphism f \<longleftrightarrow> bin_morph_of (f \<zero>) (f \<one>) = f" 
proof 
  show "morphism f \<Longrightarrow> bin_morph_of (f \<zero>) (f \<one>) = f"  
  using  morphism.morph_concat_map'[of f] 
  unfolding bin_morph_of_def case_finiteD[symmetric, of f] case_finite_2_if_else  by  blast 
qed (use bin_morph_of_morph in metis)

subsection \<open>Example of a simple symmetry: swap\<close>

context binary_code_morphism

begin

definition f_swap where "f_swap \<equiv> f \<circ> bin_swap_morph"

lemma f_swap_sing [simp]: "f_swap [a] = f [1-a]"
  unfolding f_swap_def bin_swap_morph_def bin_swap_def by force

sublocale swap_morph: morphism f_swap 
  unfolding f_swap_def bin_swap_morph_def
  using morph_compose morph_map morphism_axioms by blast 


lemma inj_bin_swap: "inj bin_swap"
  unfolding inj_def bin_swap_def by force

lemma inj_bin_swap_morph: "inj bin_swap_morph"
  unfolding bin_swap_morph_def using inj_bin_swap  by force

lemma swap_bin_code_morph: "binary_code_morphism f_swap" 
  by (standard, unfold f_swap_def)
   (use code_morph inj_bin_swap_morph in force)

(* interpretation swap1: binary_code_morphism f_swap *) 
  (* using swap_bin_code_morph. *)

(* lemma dual_bin_lcp: "swap.bin_code_lcp = \<alpha>" *)
  (* unfolding bin_lcp_def bin_lcp_def *)
  (* unfolding f_swap_sing binsimp using lcp_sym by blast *)

(* lemma dual_mismatch_fst: "swap.bin_code_mismatch_fst = c\<^sub>1" *)
  (* unfolding bin_mismatch_def dual_bin_lcp *)
  (* unfolding f_swap_sing binsimp bin_lcp_sym[of "f \<zero>"] by simp *)

(* lemma dual_mismatch_snd: "swap.bin_code_mismatch_snd = c\<^sub>0" *)
  (* unfolding bin_mismatch_def dual_bin_lcp *)
  (* unfolding f_swap_sing binsimp bin_lcp_sym[of "f \<zero>"] by simp *)

(* lemmas swap_morph = swap_morph.morph *)

(* lemmas bin_lcp_pref_all_swap = bin_lcp_pref_all[unfolded dual_bin_lcp] *)

end

section "Marked binary morphism"

lemma marked_binary_morphI: assumes "morphism f" and "f [a :: binA] \<noteq> \<epsilon>" and "f [1-a] \<noteq> \<epsilon>" and "hd (f [a]) \<noteq> hd (f [1-a])"
  shows "marked_morphism f"
proof (standard, simp add: \<open>morphism f\<close> morphism.morph)
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
qed

locale marked_binary_morphism = marked_morphism "f :: binA list \<Rightarrow> 'a list"  for f 

begin

lemma bin_marked: "hd (f \<zero>) \<noteq> hd (f \<one>)"
  using marked_morph[of bin0 bin1] by blast

lemma bin_marked_sing: "hd (f [a]) \<noteq> hd (f [1-a])"
  by (cases rule: finite_2.exhaust[of a]) (simp_all add: bin_marked bin_marked[symmetric]) 


sublocale binary_code_morphism
  using binary_code_morphism_def code_morphism_axioms by blast

lemma marked_lcp_emp: "\<alpha> = \<epsilon>" 
  unfolding bin_lcp_def
proof (rule lcp_distinct_hd)
  show "hd (f \<zero> \<cdot> f \<one>) \<noteq> hd (f \<one> \<cdot> f \<zero>)"
  unfolding hd_append if_not_P[OF sing_to_nemp]
  using bin_marked.
qed

lemma bin_marked': "(f \<zero>)!0 \<noteq> (f \<one>)!0"
  using bin_marked unfolding hd_conv_nth[OF bin_snd_nemp] hd_conv_nth[OF bin_fst_nemp]. 

lemma marked_bin_morph_pref_code: assumes "f r \<le>p f s" shows "r \<le>p s"
  using code_morph_code[OF assms[folded lcp_pref_conv, folded  marked_morph_lcp[of r s]], unfolded lcp_pref_conv[of r s]].

lemma marked_bin_morph_pref_code': "r \<bowtie> s \<or> f (r \<cdot> z1) \<and>\<^sub>p f (s \<cdot> z2) = f (r \<and>\<^sub>p s)"
 using lcp_ext_right marked_morph_lcp[of "r \<cdot> z1" "s \<cdot> z2"] by metis

lemma swap_marked: "hd(f_swap [a]) \<noteq> hd (f_swap [1-a])"
  using bin_marked_sing f_swap_sing by presburger 

lemma swap_marked': "hd (f_swap [a]) = hd (f_swap [b]) \<Longrightarrow> a = b"
  using swap_marked bin_neq_swap by auto

lemma swap_nonerasing: "f_swap w = \<epsilon> \<Longrightarrow> w = \<epsilon>"
  unfolding f_swap_def bin_swap_morph_def using nonerasing by auto

lemma swap_interpret_marked_binary_morph: "marked_morphism f_swap" 
  by (standard, unfold core_def) (use swap_nonerasing swap_marked' in blast)+

lemma period_comp:
  assumes "r \<le>p f w\<^sup>\<omega>"
  shows "r \<bowtie> f w \<cdot> \<alpha>"
proof-
  obtain n where "r \<le>p f w\<^sup>@Suc n" 
    using assms[unfolded per_pref] pref_pow_ext[of r "f w"] by blast
  from ruler[OF _ pref_ext[OF this, of \<alpha>], of "f w \<cdot> \<alpha>", unfolded pow_Suc rassoc pref_cancel_conv] 
  show ?thesis 
    unfolding prefix_comparable_def using bin_lcp_pref_all[of "w\<^sup>@n", unfolded pow_morph] by blast
qed 

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

thm marked_lcp_conv

lemma marked_marked: assumes "marked_morphism f" shows "f\<^sub>m = f"
  using marked_version_conjugates[unfolded clean_emp \<open>marked_morphism f\<close>[unfolded marked_lcp_conv]]
  by blast

lemma  marked_version_all_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> f\<^sub>m w \<noteq> \<epsilon>"
  unfolding marked_version_def  using bin_lcp_pref_all nonerasing conjug_emp_emp marked_version_def by blast

lemma marked_version_interpret_binary_code_morph: "binary_code_morphism f\<^sub>m"
  unfolding bin_code_morph_iff' morphism_def
proof (standard+)
  have "f (u\<cdot>v) \<cdot> \<alpha> = (f u \<cdot> \<alpha>) \<cdot> \<alpha>\<inverse>\<^sup>>(f v \<cdot> \<alpha>)" for u v
    unfolding rassoc morph cancel lq_pref[OF bin_lcp_pref_all[of v]]..
  thus "\<And>u v. f\<^sub>m (u \<cdot> v) = f\<^sub>m u \<cdot> f\<^sub>m v"  
    unfolding marked_version_def  lq_reassoc[OF bin_lcp_pref_all] by presburger  
  from code_morph
  show "inj f\<^sub>m"
    unfolding inj_def marked_eq_conv.
qed

(* TODO marked? *)
interpretation mv_bcm: binary_code_morphism f\<^sub>m
  using marked_version_interpret_binary_code_morph .

lemma marked_lcs: "bin_lcs (f\<^sub>m \<zero>) (f\<^sub>m \<one>) = \<beta> \<cdot> \<alpha>"
  unfolding bin_lcs_def morph[symmetric] lcs_ext_right[symmetric] marked_version_conjugates[symmetric] mv_bcm.morph[symmetric] 
  by (rule lcs_ext_left[of "f\<^sub>m (\<zero> \<cdot> \<one>)" "f\<^sub>m (\<one> \<cdot> \<zero>)" "f\<^sub>m (\<zero> \<cdot> \<one>) \<and>\<^sub>s f\<^sub>m (\<one> \<cdot> \<zero>)  = \<alpha> \<cdot> f\<^sub>m (\<zero> \<cdot> \<one>) \<and>\<^sub>s \<alpha> \<cdot> f\<^sub>m (\<one> \<cdot> \<zero>)" \<alpha> \<alpha>], unfold mv_bcm.morph)
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

lemma mismatch_fst: "hd (f\<^sub>m \<zero>) = c\<^sub>0"
proof-
  have "(f [bin0,bin1])!\<^bold>|\<alpha>\<^bold>| = hd (f\<^sub>m [bin0,bin1])" 
    using bin_lcp_shift[of "[bin0,bin1]", unfolded pop_hd[of bin0 \<one>]  lenmorph, OF bin_lcp_short]
    unfolding pop_hd[of bin0 \<one>].
  from this[unfolded  mv_bcm.pop_hd[of bin0 \<one>, unfolded not_Cons_self2[of bin0 \<epsilon>]] hd_append2[OF mv_bcm.bin_fst_nemp, of "f\<^sub>m \<one>"], symmetric]
  show ?thesis 
    unfolding bin_mismatch_def hd_word[of bin0 \<one>] morph.
qed

lemma mismatch_snd: "hd (f\<^sub>m \<one>) = c\<^sub>1"
proof-
  have "(f [bin1,bin0])!\<^bold>|\<alpha>\<^bold>| = hd (f\<^sub>m [bin1,bin0])" 
    using bin_lcp_shift[of "[bin1,bin0]", unfolded pop_hd[of bin1 \<zero>]  lenmorph, OF bin_lcp_short[unfolded add.commute[of "\<^bold>|f \<zero>\<^bold>|"  "\<^bold>|f \<one>\<^bold>|"]]]
    unfolding pop_hd[of bin1 \<zero>].
  from this[unfolded  mv_bcm.pop_hd[of bin1 \<zero>, unfolded not_Cons_self2[of bin1 \<epsilon>]] hd_append2[OF mv_bcm.bin_snd_nemp, of "f\<^sub>m \<zero>"],symmetric]
  show ?thesis 
    unfolding bin_mismatch_def hd_word[of bin1 \<zero>] morph bin_lcp_sym[of "f \<zero>"].
qed

lemma marked_hd_neq: "hd (f\<^sub>m [a]) \<noteq> hd (f\<^sub>m [1-a])" (is "?P (a :: binA)")
    by (rule bin_induct[of ?P, unfolded binsimp])
    (use mismatch_fst mismatch_snd bin_mismatch_neq in presburger)+

lemma marked_version_marked_morph: "marked_morphism f\<^sub>m"
  by (standard, unfold core_def)
  (use  not_swap_eq[of "\<lambda> a b. hd (f\<^sub>m [a]) = hd (f\<^sub>m [b])", OF _ marked_hd_neq] in force)

interpretation mv_mbm: marked_binary_morphism f\<^sub>m
  using  marked_version_marked_morph
  by (simp add: marked_binary_morphism_def)

lemma mismatch_pref0: "[c\<^sub>0] \<le>p f\<^sub>m \<zero>"
  using  mv_bcm.sing_to_nemp[THEN hd_pref, of bin0] unfolding mismatch_fst.

lemma mismatch_pref1: "[c\<^sub>1] \<le>p f\<^sub>m \<one>"
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
             \<open>hd ?r' \<noteq> hd ?s'\<close>[symmetric, unfolded bin_neq_iff'].
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
    unfolding bin_code_lcp[symmetric, of r s] pref_def using \<open>\<not> f r \<cdot> \<alpha> \<bowtie> f s \<cdot> \<alpha>\<close> 
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
  using mv_mbm.marked_bin_morph_pref_code by meson
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

lemma pref_im_pref: "r \<le>p s \<Longrightarrow> f r \<cdot> \<alpha> \<le>p f s \<cdot> \<alpha>"
  using marked_version_conjugates
  by (metis bin_code_lcp lcp_pref_conv)

lemma per_comp:
  assumes "r \<le>p (f w)\<^sup>\<omega>"
  shows "r \<bowtie> f w \<cdot> \<alpha>"
proof-
  obtain n where "r \<le>p f w\<^sup>@Suc n \<cdot> \<alpha>" 
    using per_pref_ex[OF assms] pref_trans prefix_def
      pref_pow_ext by metis    
  from ruler[OF this, folded pow_morph, OF pref_im_pref]
  show ?thesis
    unfolding prefix_comparable_def pow_Suc by simp
qed 

end

section \<open>Two binary morphisms\<close>

locale two_binary_morphisms = two_morphisms g h
  for g h :: "binA list \<Rightarrow> 'a list"
begin

lemma rev_morphs: "two_binary_morphisms (rev_map g) (rev_map h)"
  using rev_maps by (intro two_binary_morphisms.intro)

lemma solution_UNIV:
  assumes "s \<noteq> \<epsilon>" and "g s = h s" and "\<And>a. g [a] \<noteq> h [a]"
  shows "set s = UNIV"
proof (rule ccontr, elim not_UNIV_E unique_letter_wordE'')
  fix a k assume *: "s = [a] \<^sup>@ k"
  then have "k \<noteq> 0" using \<open>s \<noteq> \<epsilon>\<close> by (intro notI) simp
  have "g [a] = h [a]" using \<open>g s = h s\<close> unfolding * g.pow_morph h.pow_morph
    by (fact pow_eq_eq[OF _ \<open>k \<noteq> 0\<close>])
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
  have "\<^bold>|h [a]\<^bold>| < \<^bold>|g [a]\<^bold>|" unfolding set binsimp by blast
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
    unfolding set binsimp * by blast
  next
    show "\<^bold>|h [1-(hd s)]\<^bold>| < \<^bold>|g [1-(hd s)]\<^bold>| \<Longrightarrow> False"
    using swap.solution_len_im_sing_less[OF sol[symmetric], of "1 - (hd s)"]
    unfolding set binsimp * by blast
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

lemma two_bin_code_morphs_nonerasing_morphs: "binary_code_morphism g \<Longrightarrow> binary_code_morphism h \<Longrightarrow> two_nonerasing_morphisms g h"
  by (simp add: binary_code_morphism.nonerasing binary_code_morphism_def code_morphism.axioms(1) nonerasing_morphism.intro nonerasing_morphism_axioms.intro two_morphisms_def two_nonerasing_morphisms.intro)

section "Two binary code morphisms"

locale  two_binary_code_morphisms = two_binary_morphisms +
  g: binary_code_morphism g + 
  h: binary_code_morphism h 

begin

notation  h.bin_code_lcp ("\<alpha>\<^sub>h")
notation  g.bin_code_lcp ("\<alpha>\<^sub>g")
notation "g.marked_version" ("g\<^sub>m") 
notation "h.marked_version" ("h\<^sub>m") 

sublocale marked: two_marked_morphisms g\<^sub>m h\<^sub>m
proof-
  interpret gm: marked_morphism g\<^sub>m
    by (simp add: g.marked_version_marked_morph)
  interpret hm: marked_morphism h\<^sub>m
    by (simp add: h.marked_version_marked_morph)
  show "two_marked_morphisms g\<^sub>m h\<^sub>m"
    by unfold_locales
qed

sublocale code: two_code_morphisms g h
  by unfold_locales

lemma marked_two_binary_code_morphisms: "two_binary_code_morphisms g\<^sub>m h\<^sub>m" 
      using g.marked_version_interpret_binary_code_morph h.marked_version_interpret_binary_code_morph
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
      using marked.h.code_morph_code lcp_pref_conv by metis
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
  have "h s \<noteq> \<epsilon>"
    using  h.nemp_to_nemp min_coinD'[OF \<open>g r =\<^sub>m h s\<close>] by force 
  from
    root_ruler[OF h.bin_lcp_pref_all[of s] g.bin_lcp_pref_all[of r, folded min_coinD[OF \<open>g r =\<^sub>m h s\<close>, symmetric]] this]
  show "\<alpha>\<^sub>h \<le>p \<alpha>\<^sub>g"
    unfolding prefix_comparable_def using ruler_le[OF self_pref _ assms(1)] by blast
qed


end

section \<open>Two marked binary morphisms with blocks\<close>

locale two_binary_marked_morphisms = two_marked_morphisms g h
  for g h :: "binA list \<Rightarrow> 'a list"
begin

sublocale g: marked_binary_morphism g
  by (simp add: g.marked_morphism_axioms marked_binary_morphism_def)

sublocale h: marked_binary_morphism h
  by (simp add: h.marked_morphism_axioms marked_binary_morphism_def)

sublocale two_binary_code_morphisms g h
  by unfold_locales

sublocale revs: two_binary_code_morphisms "rev_map g"  "rev_map h"
  using revs_two_binary_code_morphisms. 

end

locale two_binary_marked_blocks = two_binary_marked_morphisms +
  assumes both_blocks: "\<And> a. blockP a"

begin
 
sublocale sucs: two_binary_marked_morphisms suc_fst suc_snd 
  using  sucs_marked_morphs[OF both_blocks, folded two_binary_marked_morphisms_def].

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
    by (cases rule: neq_exhaust[OF sucs.h.bin_marked_sing, of b a], unfold *) 
      (blast+)
qed      

lemma lcs_suf_blocks_fst: "g.bin_code_lcs \<le>s g (suc_fst ([a] \<cdot> [1-a]))"
  using revs.g.bin_lcp_pref''[reversed] g.bin_lcp_pref'' blocks_all_letters_fst by simp

lemma lcs_suf_blocks_snd: "h.bin_code_lcs \<le>s h (suc_snd ([a] \<cdot> [1-a]))"
  using revs.h.bin_lcp_pref''[reversed] h.bin_lcp_pref'' blocks_all_letters_snd by simp

lemma lcs_fst_suf_snd: "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h  sucs.h.bin_code_lcs" 
proof-
  have "g.bin_code_lcs \<le>s g (suc_fst [a] \<cdot> suc_fst [1-a])" for a
    using lcs_suf_blocks_fst[of a]
    unfolding binsimp sucs.g.morph.
  have "g.bin_code_lcs \<le>s g (suc_fst \<zero> \<cdot> suc_fst \<one>)" and "g.bin_code_lcs \<le>s g (suc_fst \<one> \<cdot> suc_fst \<zero>)" 
    using lcs_suf_blocks_fst[of bin0] lcs_suf_blocks_fst[of bin1]
    unfolding binsimp sucs.g.morph. 
  hence "g.bin_code_lcs \<le>s h (suc_snd \<zero> \<cdot> suc_snd \<one>)" and "g.bin_code_lcs \<le>s h (suc_snd \<one> \<cdot> suc_snd \<zero>)"
    unfolding g.morph h.morph  block_eq[OF both_blocks].
  from suf_ext[OF this(1)] suf_ext[OF this(2)]
  have "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h (suc_snd \<zero> \<cdot> suc_snd \<one>)" and "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h (suc_snd \<one> \<cdot> suc_snd \<zero>)".
  hence "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h (suc_snd \<zero> \<cdot> suc_snd \<one>) \<and>\<^sub>s h.bin_code_lcs \<cdot> h (suc_snd \<one> \<cdot> suc_snd \<zero>)"
    using suf_lcs_iff by blast 
  thus "g.bin_code_lcs \<le>s h.bin_code_lcs \<cdot> h sucs.h.bin_code_lcs"
    unfolding  revs.h.bin_code_lcp[reversed] bin_lcs_def[symmetric].
qed

lemma suf_comp_lcs: "g.bin_code_lcs \<bowtie>\<^sub>s h.bin_code_lcs"
  using lcs_suf_blocks_fst lcs_suf_blocks_snd
  unfolding  g.morph h.morph sucs.g.morph sucs.h.morph  block_eq[OF both_blocks] suf_comp_or using ruler[reversed] by blast 

end

end
