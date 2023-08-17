(*  Title:      CoW/CoWBasic.thy
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University
    Author:     Štěpán Starosta, CTU in Prague
*)

theory CoWBasic
  imports "HOL-Library.Sublist" Arithmetical_Hints Reverse_Symmetry "HOL-Eisbach.Eisbach_Tools"
begin

chapter "Basics of Combinatorics on Words"

text\<open>Combinatorics on Words, as the name suggests, studies words, finite or infinite sequences of elements from a, usually finite, alphabet.
The essential operation on finite words is the concatenation of two words, which is associative and noncommutative.
This operation yields many simply formulated problems, often in terms of \emph{equations on words}, that are mathematically challenging.

See for instance @{cite ChoKa97} for an introduction to Combinatorics on Words, and \cite{Lo,Lo2,Lo3} as another reference for Combinatorics on Words.
This theory deals exclusively with finite words and  provides basic facts of the field which can be considered as folklore.

The most natural way to represent finite words is by the type @{typ "'a list"}.
 From an algebraic viewpoint, lists are free monoids. On the other hand, any free monoid is isomoporphic to a monoid of lists of its generators.
The algebraic point of view and the combinatorial point of view therefore overlap significantly in Combinatorics on Words.
\<close>

section "Definitions and notations"

text\<open>First, we introduce elementary definitions and notations.\<close>

text\<open>The concatenation @{term append} of two finite lists/words is the very basic operation in Combinatorics on Words, its notation is usually omitted.
In this field, a common notation for this operation is $\cdot$, which we use and add here.\<close>

notation append (infixr "\<cdot>" 65)

lemmas rassoc = append_assoc
lemmas lassoc = append_assoc[symmetric]

text\<open>We add a common notation for the length of a given word $|w|$.\<close>


notation
  length  ("\<^bold>|_\<^bold>|") \<comment> \<open>note that it's bold |\<close>
notation (latex output)
  length  ("\<^latex>\<open>\\ensuremath{\\left| \<close>_\<^latex>\<open>\\right|}\<close>")
notation longest_common_prefix  (infixr "\<and>\<^sub>p" 61) \<comment> \<open>provided by Sublist.thy\<close>

subsection \<open>Empty and nonempty word\<close>

text\<open>As the word of length zero @{term Nil} or @{term "[]"} will be used often, we adopt its frequent notation $\varepsilon $ in this formalization.\<close>

notation Nil ("\<epsilon>")


named_theorems emp_simps
lemmas [emp_simps] = append_Nil2 append_Nil list.map(1) list.size(3)

subsection \<open>Prefix\<close>

text\<open>The property of being a prefix shall be frequently used, and we give it yet another frequent shorthand notation.
Analogously, we introduce shorthand notations for non-empty prefix and strict prefix, and continue with suffixes and factors.
\<close>

notation prefix (infixl "\<le>p" 50)
notation (latex output) prefix  ("\<le>\<^sub>p")

lemmas prefI'[intro] = prefixI

lemma prefI[intro]: "p \<cdot> s = w \<Longrightarrow> p \<le>p w"
  by auto

lemma prefD: "u \<le>p v \<Longrightarrow> \<exists> z. v = u \<cdot> z"
  unfolding prefix_def.

definition prefix_comparable :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<bowtie>" 50)
  where "(prefix_comparable u v) \<equiv> u \<le>p v \<or> v \<le>p u"

lemma pref_compI1: "u \<le>p v  \<Longrightarrow> u \<bowtie> v"
  unfolding prefix_comparable_def..

lemma pref_compI2: "v \<le>p u \<Longrightarrow> u \<bowtie> v"
  unfolding prefix_comparable_def..

lemma pref_compE [elim]: assumes "u \<bowtie> v" obtains "u \<le>p v" | "v \<le>p u"
  using assms unfolding prefix_comparable_def..

lemma pref_compI[intro]: "u \<le>p v \<or> v \<le>p u \<Longrightarrow> u \<bowtie> v"
  unfolding prefix_comparable_def
  by simp


definition nonempty_prefix (infixl "\<le>np" 50) where nonempty_prefix_def[simp]:  "u \<le>np v \<equiv> u \<noteq> \<epsilon> \<and> u \<le>p v"
notation (latex output) nonempty_prefix  ("\<le>\<^bsub>np\<^esub>" 50)

lemma npI[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> u \<le>p v \<Longrightarrow> u \<le>np v"
  by auto

lemma npI'[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> (\<exists> z. u \<cdot> z = v) \<Longrightarrow> u \<le>np v"
  by auto

lemma npD: "u \<le>np v \<Longrightarrow> u \<le>p v"
  by simp

lemma npD': "u \<le>np v \<Longrightarrow> u \<noteq> \<epsilon>"
  by simp

notation strict_prefix (infixl "<p" 50)
notation (latex output) strict_prefix  ("<\<^sub>p")
lemmas [simp] = strict_prefix_def

interpretation lcp: semilattice_order "(\<and>\<^sub>p)" prefix strict_prefix
proof
  fix a b c :: "'a list"
  show "(a \<and>\<^sub>p b) \<and>\<^sub>p c = a \<and>\<^sub>p b \<and>\<^sub>p c"
    by (rule prefix_order.antisym)
    (meson longest_common_prefix_max_prefix longest_common_prefix_prefix1 longest_common_prefix_prefix2 prefix_order.trans)+
  show "a \<and>\<^sub>p b = b \<and>\<^sub>p a"
    by (simp add: longest_common_prefix_max_prefix longest_common_prefix_prefix1 longest_common_prefix_prefix2 prefix_order.antisym)
  show "a \<and>\<^sub>p a = a"
    by (simp add: longest_common_prefix_max_prefix longest_common_prefix_prefix1 prefix_order.eq_iff)
  show "a \<le>p b = (a = a \<and>\<^sub>p b)"
    by (metis longest_common_prefix_max_prefix longest_common_prefix_prefix1 longest_common_prefix_prefix2 prefix_order.dual_order.eq_iff)
  thus "(a <p b) = (a = a \<and>\<^sub>p b \<and> a \<noteq> b)"
    by simp
qed

lemmas sprefI = strict_prefixI

lemma sprefI1[intro]: "v = u \<cdot> z \<Longrightarrow> z \<noteq> \<epsilon> \<Longrightarrow> u <p v"
  by simp

lemma sprefI1'[intro]: "u \<cdot> z = v \<Longrightarrow> z \<noteq> \<epsilon> \<Longrightarrow> u <p v"
  by force

lemma sprefI2[intro]: "u \<le>p v \<Longrightarrow> \<^bold>|u\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u <p v"
  by force

lemma sprefD: "u <p v \<Longrightarrow> u \<le>p v \<and> u \<noteq> v"
  by auto

lemmas sprefD1[dest] = prefix_order.strict_implies_order and
       sprefD2 = prefix_order.less_imp_neq

lemmas sprefE[elim?] = strict_prefixE

lemma spref_exE[elim?]: assumes "u <p v" obtains z where "u \<cdot> z = v" and "z \<noteq> \<epsilon>"
   using assms unfolding strict_prefix_def prefix_def by blast

subsection \<open>Suffix\<close>

notation suffix (infixl "\<le>s" 50)
notation (latex output) suffix ("\<le>\<^sub>s")

lemma sufI[intro]: "p \<cdot> s = w \<Longrightarrow> s \<le>s w"
  by (auto simp add: suffix_def)

lemma sufD[elim]: "u \<le>s v \<Longrightarrow> \<exists> z. z \<cdot> u = v"
  by (auto simp add: suffix_def)


notation strict_suffix (infixl "<s" 50)
notation (latex output) strict_suffix  ("<\<^sub>s")
lemmas [simp] = strict_suffix_def

lemmas [intro] = suffix_order.le_neq_trans

lemmas ssufI = suffix_order.le_neq_trans

lemma ssufI1[intro]: "u \<cdot> v = w \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v <s w"
  by blast

lemma ssufI2[intro]: "u \<le>s v \<Longrightarrow> length u < length v \<Longrightarrow> u <s v"
  by blast

lemma ssufE: "u <s v \<Longrightarrow> (u \<le>s v \<Longrightarrow> u \<noteq> v \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by auto

lemma ssufI3[intro]: "u \<cdot> v = w \<Longrightarrow> u \<le>np w \<Longrightarrow> v <s w"
  unfolding nonempty_prefix_def by blast

lemma ssufD[elim]: "u <s v \<Longrightarrow> u \<le>s v \<and> u \<noteq> v"
  by auto

lemmas ssufD1[elim] = suffix_order.strict_implies_order and
  ssufD2[elim] = suffix_order.less_imp_neq

definition suffix_comparable :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<bowtie>\<^sub>s" 50)
  where "(suffix_comparable u v) \<longleftrightarrow> (rev u) \<bowtie> (rev v)"

lemma suf_compI1[intro]: "u \<le>s v \<Longrightarrow> u \<bowtie>\<^sub>s v"
  by (simp add: pref_compI suffix_comparable_def suffix_to_prefix)

lemma suf_compI2[intro]: "v \<le>s u \<Longrightarrow> u \<bowtie>\<^sub>s v"
  by (simp add: pref_compI suffix_comparable_def suffix_to_prefix)

definition nonempty_suffix (infixl "\<le>ns" 60) where nonempty_suffix_def[simp]:  "u \<le>ns v \<equiv> u \<noteq> \<epsilon> \<and> u \<le>s v"
notation (latex output) nonempty_suffix  ("\<le>\<^bsub>ns\<^esub>" 50)

lemma nsI[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> u \<le>s v \<Longrightarrow> u \<le>ns v"
  by auto

lemma nsI'[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> (\<exists> z. z \<cdot> u = v) \<Longrightarrow> u \<le>ns v"
  by blast

lemma nsD: "u \<le>ns v \<Longrightarrow> u \<le>s v"
  by simp

lemma nsD': "u \<le>ns v \<Longrightarrow> u \<noteq> \<epsilon>"
  by simp

subsection \<open>Factor\<close>

text\<open>A @{term sublist} of some word is in Combinatorics of Words called a factor.
We adopt a common shorthand notation for the property of being a factor, strict factor and nonempty factor (the latter we also define).\<close>


notation sublist (infixl "\<le>f" 50)
notation (latex output) sublist ("\<le>\<^sub>f")
lemmas fac_def = sublist_def


notation strict_sublist (infixl "<f" 50)
notation (latex output) strict_sublist ("<\<^bsub>f\<^esub>")
lemmas strict_factor_def[simp] = strict_sublist_def

definition nonempty_factor (infixl "\<le>nf" 60) where nonempty_factor_def[simp]:  "u \<le>nf v \<equiv> u \<noteq> \<epsilon> \<and> (\<exists> p s. p\<cdot>u\<cdot>s = v)"
notation (latex output) nonempty_factor ("\<le>\<^bsub>nf\<^esub>")

lemmas facI = sublist_appendI

lemma facI': "a \<cdot> u \<cdot> b = w \<Longrightarrow> u \<le>f w"
  by auto

lemma facE[elim]: assumes "u \<le>f v"
  obtains p s where "v = p \<cdot> u \<cdot> s"
  using assms unfolding fac_def
  by blast

lemma facE'[elim]: assumes "u \<le>f v"
  obtains p s where "p \<cdot> u \<cdot> s = v"
  using assms unfolding fac_def
  by blast

section "Various elementary lemmas"

lemmas drop_all_iff = drop_eq_Nil \<comment> \<open>backward compatibility with Isabelle 2021\<close>

lemma exE2: "\<exists> x y. P x y \<Longrightarrow> (\<And> x y. P x y \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by auto

lemmas concat_morph = concat_append

lemmas cancel = same_append_eq and
  cancel_right = append_same_eq

lemmas disjI = verit_and_neg(3)

lemma rev_in_conv: "rev u \<in> A \<longleftrightarrow> u \<in> rev ` A"
  by force

lemmas map_rev_involution = list.map_comp[of rev rev, unfolded rev_involution' list.map_id]

lemma map_rev_lists_rev:  "map rev ` (lists (rev ` A)) = lists A"
  unfolding lists_image[of rev] image_comp
  by (simp add: rev_involution')

lemma inj_on_map_lists: assumes "inj_on f A"
  shows "inj_on (map f) (lists A)"
proof
  fix xs ys
  assume "xs \<in> lists A" and "ys \<in> lists A" and "map f xs = map f ys"
  have "x = y" if "x \<in> set xs" and "y \<in> set ys" and  "f x =  f y"  for x y
    using in_listsD[OF \<open>xs \<in> lists A\<close>, rule_format, OF \<open>x \<in> set xs\<close>]
          in_listsD[OF \<open>ys \<in> lists A\<close>, rule_format, OF \<open>y \<in> set ys\<close>]
         \<open>inj_on f A\<close>[unfolded inj_on_def, rule_format, OF _ _ \<open>f x =  f y\<close>] by blast
  from list.inj_map_strong[OF this  \<open>map f xs = map f ys\<close>]
  show "xs = ys".
qed

lemma bij_lists: "bij_betw f X Y \<Longrightarrow> bij_betw (map f) (lists X) (lists Y)"
  unfolding bij_betw_def using inj_on_map_lists lists_image by metis

lemma concat_sing': "concat [r] = r"
  by simp

lemma concat_sing: assumes "s = [a]" shows "concat s = a"
  using concat_sing' unfolding \<open>s = [a]\<close>.

lemma rev_sing: "rev [x] = [x]"
  by simp

lemma hd_word: "a#ws = [a] \<cdot> ws"
  by simp

lemma pref_singE: assumes "p \<le>p [a]" obtains "p = \<epsilon>" | "p = [a]"
  using assms unfolding  prefix_Cons by fastforce

lemma map_hd:  "map f (a#v) = [f a] \<cdot> (map f v)"
  by simp

lemma hd_tl: "w \<noteq> \<epsilon> \<Longrightarrow> [hd w] \<cdot> tl w = w"
  by simp

lemma hd_tlE: assumes "w \<noteq> \<epsilon>"
  obtains a w' where "w = a#w'"
  using exE2[OF assms[unfolded neq_Nil_conv]].

lemma hd_tl_lenE: assumes "0 < \<^bold>|w\<^bold>|"
  obtains a w' where "w = a#w'"
  using exE2[OF assms[unfolded length_greater_0_conv neq_Nil_conv]].

lemma hd_tl_longE: assumes "Suc 0 < \<^bold>|w\<^bold>|"
  obtains a w' where "w = a#w'" and "w' \<noteq> \<epsilon>" and "hd w = a" and "tl w = w'"
proof-
  obtain a w' where "w = a#w'"
    using  hd_tl_lenE[OF Suc_lessD[OF  assms]].
  hence "w' \<noteq> \<epsilon>" and  "hd w = a" and "tl w = w'" using assms by auto
  from that[OF \<open>w = a#w'\<close> this] show thesis.
qed

lemma hd_pref: "w \<noteq> \<epsilon> \<Longrightarrow> [hd w] \<le>p w"
  using hd_tl
  by blast

lemma add_nth: assumes "n < \<^bold>|w\<^bold>|" shows "(take n w) \<cdot> [w!n] \<le>p w"
  using take_is_prefix[of "Suc n" w, unfolded take_Suc_conv_app_nth[OF assms]].

lemma hd_pref': assumes "w \<noteq> \<epsilon>" shows "[w!0] \<le>p w"
  using hd_pref[OF \<open>w \<noteq> \<epsilon>\<close>, folded hd_conv_nth[OF \<open>w \<noteq> \<epsilon>\<close>, symmetric]].

lemma sub_lists_mono: "A \<subseteq> B \<Longrightarrow> x \<in> lists A \<Longrightarrow> x \<in> lists B"
  by auto

lemma lists_hd_in_set[simp]: "us \<noteq> \<epsilon> \<Longrightarrow> us \<in> lists Q \<Longrightarrow> hd us \<in> Q"
  by fastforce

lemma lists_last_in_set[simp]: "us \<noteq> \<epsilon> \<Longrightarrow> us \<in> lists Q \<Longrightarrow> last us \<in> Q"
  by fastforce

lemma replicate_in_lists: "replicate k z \<in> lists {z}"
  by (induction k) auto

lemma tl_in_lists: assumes "us \<in> lists A" shows "tl us \<in> lists A"
  using suffix_lists[OF suffix_tl assms].

lemmas lists_butlast = tl_in_lists[reversed]

lemma long_list_tl: assumes "1 < \<^bold>|us\<^bold>|" shows "tl us \<noteq> \<epsilon>"
proof
  assume "tl us = \<epsilon>"
  from assms
  have "us \<noteq> \<epsilon>" and "\<^bold>|us\<^bold>| = Suc \<^bold>|tl us\<^bold>|" and "\<^bold>|us\<^bold>| \<noteq> Suc 0"
    by auto
  thus False
    using \<open>tl us = \<epsilon>\<close> by simp
qed

lemma tl_set: "x \<in> set (tl a) \<Longrightarrow> x \<in> set a"
  using list.sel(2) list.set_sel(2) by metis

lemma drop_take_inv: "n \<le> \<^bold>|u\<^bold>| \<Longrightarrow> drop n (take n u \<cdot> w) = w"
  by simp

lemma split_list_long: assumes "1 < \<^bold>|us\<^bold>|" and "u \<in> set us"
  obtains xs ys where "us = xs \<cdot> [u] \<cdot> ys" and "xs\<cdot>ys\<noteq>\<epsilon>"
proof-
  obtain xs ys where "us = xs \<cdot> [u] \<cdot> ys"
    using split_list_first[OF \<open>u \<in> set us\<close>] by auto
  hence "xs\<cdot>ys\<noteq>\<epsilon>"
    using \<open>1 < \<^bold>|us\<^bold>|\<close> by auto
  from that[OF \<open>us = xs \<cdot> [u] \<cdot> ys\<close> this]
  show thesis.
qed

lemma flatten_lists: "G \<subseteq> lists B \<Longrightarrow> xs \<in> lists G \<Longrightarrow> concat xs \<in> lists B"
 by (induct xs, simp_all add: subset_iff)

lemma concat_map_sing_ident: "concat (map (\<lambda> x. [x]) xs) = xs"
  by auto

lemma hd_concat_tl: assumes "ws \<noteq> \<epsilon>" shows "hd ws \<cdot> concat (tl ws) = concat ws"
  using concat.simps(2)[of "hd ws" "tl ws", unfolded list.collapse[OF \<open>ws \<noteq> \<epsilon>\<close>], symmetric].

lemma concat_butlast_last: assumes "ws \<noteq> \<epsilon>" shows "concat (butlast ws) \<cdot> last ws = concat ws"
  using  concat_morph[of "butlast ws" "[last ws]", unfolded concat_sing' append_butlast_last_id[OF \<open>ws \<noteq> \<epsilon>\<close>], symmetric].

lemma spref_butlast_pref: assumes "u \<le>p v" and "u \<noteq> v" shows "u \<le>p butlast v"
  using butlast_append prefixE[OF \<open>u \<le>p v\<close>] \<open>u \<noteq> v\<close> append_Nil2 prefixI by metis

lemma last_concat: "xs \<noteq> \<epsilon> \<Longrightarrow> last xs \<noteq> \<epsilon> \<Longrightarrow> last (concat xs) = last (last xs)"
  using concat_butlast_last last_appendR by metis

lemma concat_last_suf: "ws \<noteq> \<epsilon> \<Longrightarrow> last ws \<le>s concat ws"
  using concat_butlast_last by blast

lemma concat_hd_pref: "ws \<noteq> \<epsilon> \<Longrightarrow> hd ws \<le>p concat ws"
  using hd_concat_tl by blast

lemma set_nemp_concat_nemp: assumes "ws \<noteq> \<epsilon>" and "\<epsilon> \<notin> set ws" shows "concat ws \<noteq> \<epsilon>"
  using \<open>\<epsilon> \<notin> set ws\<close> last_in_set[OF \<open>ws \<noteq> \<epsilon>\<close>] concat_butlast_last[OF \<open>ws \<noteq> \<epsilon>\<close>] by fastforce

lemmas takedrop = append_take_drop_id

lemma suf_drop_conv: "u \<le>s w \<longleftrightarrow> drop (\<^bold>|w\<^bold>| - \<^bold>|u\<^bold>|) w = u"
  using suffix_take append_take_drop_id same_append_eq suffix_drop by metis

lemma comm_rev_iff: "rev u \<cdot> rev v = rev v \<cdot> rev u \<longleftrightarrow> u \<cdot> v = v \<cdot> u"
  unfolding rev_append[symmetric] rev_is_rev_conv eq_ac(1)[of "u \<cdot> v"] by blast

lemma rev_induct2:
  "\<lbrakk> P [] [];
  \<And>x xs. P (xs\<cdot>[x]) [];
  \<And>y ys. P [] (ys\<cdot>[y]);
  \<And>x xs y ys. P xs ys  \<Longrightarrow> P (xs\<cdot>[x]) (ys\<cdot>[y]) \<rbrakk>
 \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case
    using rev_induct[of "P \<epsilon>"]
    by presburger
next
  case (snoc x xs)
  hence "P xs ys'" for ys'
    by simp
  then show ?case
    by (simp add: rev_induct snoc.prems(2) snoc.prems(4))
qed

lemma fin_bin: "finite {x,y}"
  by simp

lemma rev_rev_image_eq [reversal_rule]: "rev ` rev ` X = X"
  by (simp add: image_comp)

lemma last_take_conv_nth: assumes "n < length xs" shows "last (take (Suc n) xs) = xs!n"
  unfolding take_Suc_conv_app_nth[OF assms] by simp

lemma inj_map_inv: "inj_on f A \<Longrightarrow> u \<in> lists A \<Longrightarrow> u = map (the_inv_into A f) (map f u)"
  by (induct u,  simp, simp add: the_inv_into_f_f)

lemma last_sing[simp]: "last [c] = c"
   by simp

lemma hd_hdE: "(u = \<epsilon> \<Longrightarrow> thesis) \<Longrightarrow> (u = [hd u] \<Longrightarrow> thesis) \<Longrightarrow> (u = [hd u, hd (tl u)] \<cdot> tl (tl u) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  using Cons_eq_appendI[of "hd u" "[hd (tl u)]" _ "tl u" "tl (tl u)"] hd_tl[of u] hd_tl[of "tl u"] hd_word
   by fastforce

lemma same_sing_pref: "u \<cdot> [a] \<le>p v \<Longrightarrow> u \<cdot> [b] \<le>p v \<Longrightarrow> a = b"
  using prefix_same_cases by fastforce

lemma compow_Suc: "(f^^(Suc k)) w = f ((f^^k) w)"
  by simp

lemma compow_Suc': "(f^^(Suc k)) w = (f^^k) (f w)"
  by (simp add: funpow_swap1)

subsection \<open>General facts\<close>

lemma two_elem_sub: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> {x,y} \<subseteq> A"
  by simp

thm fun.inj_map[THEN injD]

lemma inj_comp: assumes "inj (f :: 'a list \<Rightarrow> 'b list)" shows "(g  w = h w \<longleftrightarrow> (f \<circ> g) w = (f \<circ> h) w)"
  by (rule iffI, simp) (use injD[OF assms] in fastforce)

lemma inj_comp_eq: assumes "inj (f :: 'a list \<Rightarrow> 'b list)" shows "(g = h \<longleftrightarrow> f \<circ> g = f \<circ> h)"
  by (rule, fast)  (use fun.inj_map[OF assms, unfolded inj_on_def] in fast)

lemma two_elem_cases[elim!]: assumes "u \<in> {x, y}" obtains (fst) "u = x" | (snd) "u = y"
  using assms by blast

lemma two_elem_cases2[elim]: assumes "u \<in> {x, y}" "v \<in> {x,y}" "u \<noteq> v"
  shows "(u = x \<Longrightarrow> v = y \<Longrightarrow> thesis) \<Longrightarrow> (u = y \<Longrightarrow> v = x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  using assms by blast

lemma two_elemP: "u \<in> {x, y} \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> P u"
  by blast

lemma pairs_extensional: "(\<And> r s. P r s \<longleftrightarrow> (\<exists> a b. Q a b \<and> r = fa a \<and> s = fb b)) \<Longrightarrow>  {(r,s). P r s} = {(fa a, fb b) | a b. Q a b}"
  by auto

lemma pairs_extensional': "(\<And> r s. P r s \<longleftrightarrow> (\<exists> t. Q t \<and> r = fa t \<and> s = fb t)) \<Longrightarrow>  {(r,s). P r s} = {(fa t, fb t) | t. Q t}"
  by auto

lemma doubleton_subset_cases: assumes "A \<subseteq> {x,y}"
  obtains  "A = {}" | "A = {x}" | "A = {y}" | "A = {x,y}"
  using assms by blast

subsection \<open>Map injective function\<close>

lemma map_pref_conv [reversal_rule]: assumes "inj f" shows "map f u \<le>p map f v \<longleftrightarrow> u \<le>p v"
  using map_mono_prefix[of "map f u" "map f v" "inv f"] map_mono_prefix
  unfolding map_map inv_o_cancel[OF \<open>inj f\<close>] list.map_id..

lemma map_suf_conv [reversal_rule]: assumes "inj f" shows "map f u \<le>s map f v \<longleftrightarrow> u \<le>s v"
  using map_mono_suffix[of "map f u" "map f v" "inv f"] map_mono_suffix
  unfolding map_map inv_o_cancel[OF \<open>inj f\<close>] list.map_id..

lemma map_fac_conv [reversal_rule]: assumes "inj f" shows "map f u \<le>f map f v \<longleftrightarrow> u \<le>f v"
  using map_mono_sublist[of "map f u" "map f v" "inv f"] map_mono_sublist
  unfolding map_map inv_o_cancel[OF \<open>inj f\<close>] list.map_id..

lemma map_lcp_conv: assumes "inj f" shows "(map f xs) \<and>\<^sub>p (map f ys) = map f (xs \<and>\<^sub>p ys)"
proof (induct xs ys rule: list_induct2')
  case (4 x xs y ys)
  then show ?case
  proof (cases "x = y")
    assume "x = y"
    thus ?case
      using "4.hyps" by simp
  next
    assume "x \<noteq> y"
    hence "f x \<noteq> f y"
      using inj_eq[OF \<open>inj f\<close>] by simp
    thus ?case using \<open>x \<noteq> y\<close> by simp
  qed
qed simp_all

subsection \<open>Orderings on lists: prefix, suffix, factor\<close>

lemmas self_pref = prefix_order.refl and
       pref_antisym = prefix_order.antisym and
       pref_trans = prefix_order.trans and
       spref_trans = prefix_order.less_trans and
       suf_trans = suffix_order.trans and
       fac_trans[intro] = sublist_order.order.trans

subsection "On the empty word"

lemma nemp_elem_setI[intro]: "u \<in> S \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> u \<in> S - {\<epsilon>}"
  by simp


lemma emp_concat_emp: "us \<in> lists (S - {\<epsilon>}) \<Longrightarrow> concat us = \<epsilon> \<Longrightarrow> us = \<epsilon>"
  using DiffD2 by auto

lemma take_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> 0 < n \<Longrightarrow> take n w \<noteq> \<epsilon>"
  by simp

lemma pref_nemp [intro]: "u \<noteq> \<epsilon> \<Longrightarrow> u \<cdot> v \<noteq> \<epsilon>"
  unfolding append_is_Nil_conv by simp

lemma suf_nemp [intro]: "v \<noteq> \<epsilon> \<Longrightarrow> u \<cdot> v \<noteq> \<epsilon>"
  unfolding append_is_Nil_conv by simp

lemma pref_of_emp: "u \<cdot> v = \<epsilon> \<Longrightarrow> u = \<epsilon>"
  using append_is_Nil_conv by simp

lemma suf_of_emp: "u \<cdot> v = \<epsilon> \<Longrightarrow> v = \<epsilon>"
  using append_is_Nil_conv by simp

lemma nemp_comm: "(u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<cdot> v = v \<cdot> u) \<Longrightarrow> u \<cdot> v = v \<cdot> u"
  by force

lemma non_triv_comm [intro]: "(u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<cdot> v = v \<cdot> u) \<Longrightarrow> u \<cdot> v = v \<cdot> u"
  by force

lemma split_list': "a \<in> set ws \<Longrightarrow> \<exists>p s. ws = p \<cdot> [a] \<cdot> s"
  using split_list by fastforce

lemma split_listE: assumes "a \<in> set w"
  obtains p s where "w = p \<cdot> [a] \<cdot> s"
  using exE2[OF split_list'[OF assms]].

subsection \<open>Counting letters\<close>

declare count_list_rev [reversal_rule]

lemma count_list_map_conv [reversal_rule]:
  assumes "inj f" shows "count_list (map f ws) (f a) = count_list ws a"
  by (induction ws) (simp_all add: inj_eq[OF assms])

subsection "Set inspection method"

text\<open>This section defines a simple method that splits a goal into subgoals by enumerating
  all possibilites for @{term "x"} in a premise such as @{term "x \<in> {a,b,c}"}.
  See the demonstrations below.\<close>

method set_inspection = (
    (unfold insert_iff),
    (elim disjE emptyE),
    (simp_all only: singleton_iff refl True_implies_equals)
    )

lemma "u \<in> {x,y} \<Longrightarrow> P u"
  apply(set_inspection)
  oops

lemma "\<And>u. u \<in> {x,y} \<Longrightarrow> u = x \<or> u = y"
  by(set_inspection, simp_all)


section "Length and its properties"

lemmas lenarg = arg_cong[of _ _ length] and
       lenmorph = length_append

lemma lenarg_not: "\<^bold>|u\<^bold>| \<noteq> \<^bold>|v\<^bold>| \<Longrightarrow> u \<noteq> v"
  using size_neq_size_imp_neq.

lemma len_less_neq: "\<^bold>|u\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u \<noteq> v"
  by blast

lemmas len_nemp_conv = length_greater_0_conv

lemma npos_len: "\<^bold>|u\<^bold>| \<le> 0 \<Longrightarrow> u = \<epsilon>"
  by simp

lemma nemp_pos_len: "w \<noteq> \<epsilon> \<Longrightarrow> 0 < \<^bold>|w\<^bold>|"
  by blast

lemma nemp_le_len: "r \<noteq> \<epsilon> \<Longrightarrow> 1 \<le> \<^bold>|r\<^bold>|"
  by (simp add: leI)

lemma swap_len: "\<^bold>|u \<cdot> v\<^bold>| = \<^bold>|v \<cdot> u\<^bold>|"
  by simp

lemma len_after_drop: "p + q \<le> \<^bold>|w\<^bold>| \<Longrightarrow>  q \<le> \<^bold>|drop p w\<^bold>|"
  by simp

lemma short_take_append: "n \<le> \<^bold>|u\<^bold>|\<Longrightarrow> take n (u \<cdot> v) = take n u"
  by simp

lemma sing_word: "\<^bold>|us\<^bold>| = 1 \<Longrightarrow> [hd us] = us"
  by (cases us) simp+

lemma sing_word_concat: assumes "\<^bold>|us\<^bold>| = 1" shows "[concat us] = us"
  unfolding concat_sing[OF sing_word[OF \<open>\<^bold>|us\<^bold>| = 1\<close>, symmetric]] using sing_word[OF \<open>\<^bold>|us\<^bold>| = 1\<close>].

lemma len_one_concat_in: "ws \<in> lists A \<Longrightarrow> \<^bold>|ws\<^bold>| = 1 \<Longrightarrow> concat ws \<in> A"
  using Cons_in_lists_iff sing_word_concat by metis

lemma concat_nemp:  "concat us \<noteq> \<epsilon> \<Longrightarrow> us \<noteq> \<epsilon>"
  using concat.simps(1) by blast

lemma sing_len: "\<^bold>|[a]\<^bold>| = 1"
  by simp

lemmas pref_len = prefix_length_le and
       suf_len = suffix_length_le

lemmas spref_len = prefix_length_less and
       ssuf_len = suffix_length_less

lemma pref_len': "\<^bold>|u\<^bold>| \<le> \<^bold>|u \<cdot> z\<^bold>|"
  by auto

lemma suf_len': "\<^bold>|u\<^bold>| \<le> \<^bold>|z \<cdot> u\<^bold>|"
  by auto

lemma fac_len: "u \<le>f v \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|"
  by auto

lemma fac_len': "\<^bold>|w\<^bold>| \<le> \<^bold>|u \<cdot> w \<cdot> v\<^bold>|"
  by simp

lemma fac_len_eq: "u \<le>f v \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  unfolding fac_def using lenmorph npos_len by fastforce

thm length_take

lemma len_take1: "\<^bold>|take p w\<^bold>| \<le> p"
  by simp

lemma len_take2: "\<^bold>|take p w\<^bold>| \<le> \<^bold>|w\<^bold>|"
  by simp

lemma drop_len: "\<^bold>|u \<cdot> w\<^bold>| \<le> \<^bold>|u \<cdot> v \<cdot> w\<^bold>|"
  by simp

lemma drop_pref: "drop \<^bold>|u\<^bold>| (u \<cdot> w) = w"
  by simp

lemma take_len: "p \<le> \<^bold>|w\<^bold>| \<Longrightarrow> \<^bold>|take p w\<^bold>| = p"
  using  min_absorb2[of p "\<^bold>|w\<^bold>|", folded length_take[of p w]].

lemma conj_len: "p \<cdot> x = x \<cdot> s \<Longrightarrow> \<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|"
  using lenmorph[of p x] lenmorph[of x s] add.commute add_left_imp_eq
  by auto

lemma take_nemp_len: "u \<noteq> \<epsilon> \<Longrightarrow> r \<noteq> \<epsilon> \<Longrightarrow> take \<^bold>|r\<^bold>| u \<noteq> \<epsilon>"
  by simp

lemma nemp_len: "u \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|u\<^bold>| \<noteq> 0"
  by simp

lemma emp_len: "w = \<epsilon> \<Longrightarrow> \<^bold>|w\<^bold>| = 0"
  by simp

lemma take_self: "take \<^bold>|w\<^bold>| w = w"
  using take_all[of w "\<^bold>|w\<^bold>|", OF order.refl].

lemma len_le_concat: "\<epsilon> \<notin>  set ws \<Longrightarrow> \<^bold>|ws\<^bold>| \<le> \<^bold>|concat ws\<^bold>|"
proof (induct ws)
  case (Cons a ws)
  hence "1 \<le> \<^bold>|a\<^bold>|"
    using list.set_intros(1)[of a ws] nemp_le_len[of a] by blast
  then show ?case
    unfolding   concat.simps(2)  unfolding  lenmorph hd_word[of a ws] sing_len
    using Cons.hyps Cons.prems by simp
qed simp

lemma eq_len_iff: assumes eq: "x \<cdot> y = u \<cdot> v" shows "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<longleftrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|y\<^bold>|"
  using lenarg[OF eq] unfolding lenmorph by auto

lemma eq_len_iff_less: assumes eq: "x \<cdot> y = u \<cdot> v" shows "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>| \<longleftrightarrow> \<^bold>|v\<^bold>| < \<^bold>|y\<^bold>|"
  using lenarg[OF eq] unfolding lenmorph by auto

lemma Suc_len_nemp: "\<^bold>|w\<^bold>| = Suc n \<Longrightarrow> w \<noteq> \<epsilon>"
  by force

lemma same_sufix_nil: assumes "z \<cdot> u \<le>p u" shows "z = \<epsilon>"
  using prefix_length_le[OF assms] unfolding lenmorph by simp

lemma count_list_gr_0_iff: "0 < count_list u a \<longleftrightarrow> a \<in> set u"
  by (intro iffI, use count_notin[folded not_gr0, of a u] in blast) (induction u, auto)

lemma mid_fac_ex: assumes "2 \<le> \<^bold>|w\<^bold>|"
  shows "w = [hd w]\<cdot>(butlast (tl w))\<cdot>[last w]"
  using long_list_tl[OF \<open>2 \<le> \<^bold>|w\<^bold>|\<close>[folded One_less_Two_le_iff]] append_butlast_last_id[of "tl w"] len_nemp_conv[of w]
  by (simp add: last_tl tl_Nil)

section "List inspection method"

text\<open>In this section we define a proof method, named list\_inspection, which splits the goal into subgoals which enumerate possibilities
  on lists with fixed length and given alphabet.
  More specifically, it looks for a premise of the form  such as @{term "\<^bold>|w\<^bold>| = 2 \<and> w \<in> lists {x,y,z}"} or @{term "\<^bold>|w\<^bold>| \<le> 2 \<and> w \<in> lists {x,y,z}"}
  and substitutes the goal by the goals listing all possibilities for the word @{term w}, see demonstrations
  after the method definition.\<close>

context
begin

text\<open>First, we define an elementary lemma used for unfolding the premise.
Since it is very specific, we keep it private.\<close>

private lemma hd_tl_len_list_iff:  "\<^bold>|w\<^bold>| = Suc n \<and> w \<in> lists A \<longleftrightarrow> hd w \<in> A \<and>  w = hd w # tl w \<and> \<^bold>|tl w\<^bold>| = n \<and> tl w \<in> lists A" (is "?L = ?R")
proof
  show "?L \<Longrightarrow> ?R"
  proof (elim conjE)
    assume "\<^bold>|w\<^bold>| = Suc n" and "w \<in> lists A"
    note Suc_len_nemp[OF \<open>\<^bold>|w\<^bold>| = Suc n\<close>]
    from lists_hd_in_set[OF \<open>w \<noteq> \<epsilon>\<close> \<open>w \<in> lists A\<close>] list.collapse[OF \<open>w \<noteq> \<epsilon>\<close>] tl_in_lists[OF \<open>w \<in> lists A\<close>]
    show "hd w \<in> A \<and> w = hd w # tl w \<and> \<^bold>|tl w\<^bold>| = n \<and> tl w \<in> lists A"
      using \<open>\<^bold>|w\<^bold>| = Suc n\<close> by simp
  qed
next
  show "?R \<Longrightarrow> ?L"
    using Cons_in_lists_iff[of "hd w" "tl w"] length_Cons[of "hd w" "tl w"] by presburger
qed

text\<open>We define a list of lemmas used for the main unfolding step.\<close>

private lemmas len_list_word_dec =
    numeral_nat hd_tl_len_list_iff
    insert_iff empty_iff simp_thms length_0_conv

text\<open>The method itself accepts an argument called `add`, which is supplied to the method
 simp\_all to solve some simple cases, and thus lower the number of produced goals on the fly.\<close>

method list_inspection = (
    ((match premises in len[thin]: "\<^bold>|w\<^bold>| \<le> k" and list[thin]: "w \<in> lists A"  for w k A \<Rightarrow>
        \<open>insert conjI[OF len list]\<close>)+)?,
    (unfold numeral_nat le_Suc_eq le_0_eq), \<comment> \<open>unfold numeral and e.g. @{term "k \<le> 2"}\<close>
    (unfold conj_ac(1)[of "w \<in> lists A" "\<^bold>|w\<^bold>| \<le> k" for w A k]
          conj_disj_distribR[where ?R = "w \<in> lists A" for w A])?,
    ((match premises in len[thin]: "\<^bold>|w\<^bold>| = k" and list[thin]: "w \<in> lists A"  for w k A \<Rightarrow>
        \<open>insert conjI[OF len list]\<close>)+)?,
        \<comment> \<open>transform into the conjuction such as @{term "length w = 2 \<and> w \<in> lists {x,y,z}"}\<close>
    (unfold conj_ac(1)[of "w \<in> lists A" "\<^bold>|w\<^bold>| = k" for w A k] len_list_word_dec), \<comment> \<open>unfold w\<close>
    (elim disjE conjE), \<comment> \<open>split into all cases\<close>
    (simp_all only: singleton_iff lists.Nil list.sel refl True_implies_equals)?, \<comment> \<open>replace w everywhere\<close>
    (simp_all only: empty_iff lists.Nil bool_simps)? \<comment> \<open>solve simple cases\<close>
)

subsubsection "List inspection demonstrations"

text\<open>The required premise in the form of conjuction.
First, inequality bound on the length, second, equality bound.\<close>

lemma "\<^bold>|w\<^bold>| = 2 \<and> w \<in> lists {x,y,z} \<Longrightarrow> P w"
  apply(list_inspection)
  oops

text\<open>The required premise as 2 separate assumptions.\<close>
lemma "\<^bold>|w\<^bold>| \<le> 2 \<Longrightarrow> w \<in> lists {x,y,z} \<Longrightarrow> P w"
  apply(list_inspection)
  oops


lemma "w \<le>p w \<Longrightarrow> \<^bold>|w\<^bold>| \<le> 2 \<Longrightarrow> w \<in> lists {a,b} \<Longrightarrow> hd w = a \<Longrightarrow> w \<noteq> \<epsilon> \<Longrightarrow>  w = [a, b] \<or> w = [a, a] \<or> w = [a]"
  by list_inspection

lemma "w \<le>p w \<Longrightarrow> \<^bold>|w\<^bold>| = 2 \<Longrightarrow> w \<in> lists {a,b} \<Longrightarrow> hd w = a \<Longrightarrow>  w = [a, b] \<or> w = [a, a]"
  by list_inspection

lemma "w \<le>p w \<Longrightarrow> \<^bold>|w\<^bold>| = 2 \<and> w \<in> lists {a,b} \<Longrightarrow> hd w = a \<Longrightarrow>  w = [a, b] \<or> w = [a, a]"
  by list_inspection

lemma "w \<le>p w \<Longrightarrow> w \<in> lists {a,b} \<and> \<^bold>|w\<^bold>| = 2 \<Longrightarrow> hd w = a \<Longrightarrow>  w = [a, b] \<or> w = [a, a]"
  by list_inspection

end
section "Prefix and prefix comparability properties"

lemmas pref_emp = prefix_bot.extremum_uniqueI

lemma triv_pref: "r \<le>p r \<cdot> s"
  using prefI[OF refl].

lemma triv_spref: "s \<noteq> \<epsilon> \<Longrightarrow> r <p r \<cdot> s"
  by simp

lemma pref_cancel: "z \<cdot> u \<le>p z \<cdot> v \<Longrightarrow> u \<le>p v"
  by simp

lemma pref_cancel': "u \<le>p v \<Longrightarrow> z \<cdot> u \<le>p z \<cdot> v"
  by simp

lemma spref_cancel: "z \<cdot> u <p z \<cdot> v \<Longrightarrow> u <p v"
  by simp

lemma spref_cancel': "u <p v \<Longrightarrow> z \<cdot> u <p z \<cdot> v"
  by simp

lemmas pref_cancel_conv = same_prefix_prefix and
       suf_cancel_conv = same_suffix_suffix \<comment> \<open>provided by Sublist.thy\<close>

lemma pref_cancel_hd_conv: "a # u \<le>p a # v \<longleftrightarrow> u \<le>p v"
  by simp

lemma spref_cancel_conv: "z \<cdot> x <p z \<cdot> y \<longleftrightarrow> x <p y"
  by auto

lemma spref_snoc_iff [simp]: "u <p v \<cdot> [a] \<longleftrightarrow> u \<le>p v"
  by (auto simp only: strict_prefix_def prefix_snoc) simp

lemma spref_two_lettersE: assumes "p <p [a,b]" obtains "p = \<epsilon>" | "p = [a]"
  using assms pref_singE[of p a thesis]
  unfolding hd_word[of a "[b]"] spref_snoc_iff by fastforce

lemmas pref_ext[intro] = prefix_prefix \<comment> \<open>provided by Sublist.thy\<close>

lemmas pref_extD = append_prefixD and
       suf_extD =  suffix_appendD

lemma spref_extD: "x \<cdot> y <p z \<Longrightarrow> x <p z"
  using prefix_order.le_less_trans[OF triv_pref].

lemma spref_ext: "r <p u \<Longrightarrow> r <p u \<cdot> v"
  by force

lemma pref_ext_nemp: "r \<le>p u \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> r <p u \<cdot> v"
  by auto

lemma pref_take: "p \<le>p w \<Longrightarrow> take \<^bold>|p\<^bold>| w = p"
  unfolding prefix_def  by force

lemma pref_take_conv: "take (\<^bold>|r\<^bold>|) w = r \<longleftrightarrow> r \<le>p w"
  using pref_take[of r w] take_is_prefix[of "\<^bold>|r\<^bold>|" w] by argo

lemma le_suf_drop: assumes "i \<le> j" shows "drop j w \<le>s drop i w"
  using suffix_drop[of "j - i" "drop i w", unfolded drop_drop le_add_diff_inverse2[OF \<open>i \<le> j\<close>]].

lemma spref_take: "p <p w \<Longrightarrow> take \<^bold>|p\<^bold>| w = p"
  by (elim spref_exE) force

lemma pref_same_len: "u \<le>p v \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by (fastforce elim: prefixE)

lemma pref_same_len': "u \<cdot> z \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
   by (fastforce elim: prefixE)

lemma pref_comp_eq: "u \<bowtie> v \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  using pref_same_len by fastforce

lemma ruler_eq_len: "u \<le>p w \<Longrightarrow> v \<le>p w \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by (fastforce simp add: prefix_def)

lemma pref_prod_eq: "u \<le>p v \<cdot> z \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by (fastforce simp add: prefix_def)

lemmas  pref_comm_eq = pref_same_len[OF _ swap_len] and
        pref_comm_eq' = pref_prod_eq[OF _ swap_len, unfolded rassoc]

lemma pref_comm_eq_conv: "u \<cdot> v \<le>p v \<cdot> u \<longleftrightarrow> u \<cdot> v = v \<cdot> u"
  using pref_comm_eq self_pref by metis

lemma add_nth_pref: assumes "u <p w" shows "u \<cdot> [w!\<^bold>|u\<^bold>|] \<le>p w"
  using add_nth[OF prefix_length_less[OF \<open>u <p w\<close>], unfolded spref_take[OF \<open>u <p w\<close>]].

lemma index_pref: "\<^bold>|u\<^bold>| \<le> \<^bold>|w\<^bold>| \<Longrightarrow> (\<forall> i < \<^bold>|u\<^bold>|.  u!i = w!i) \<Longrightarrow> u \<le>p w"
  using trans[OF sym[OF take_all[OF order_refl]] nth_take_lemma[OF order_refl], of u w]
    take_is_prefix[of "\<^bold>|u\<^bold>|" w] by auto

lemma pref_index: assumes "u \<le>p w" "i < \<^bold>|u\<^bold>|" shows "u!i = w!i"
  using nth_take[OF \<open>i < \<^bold>|u\<^bold>|\<close>, of w, unfolded pref_take[OF \<open>u \<le>p w\<close>]].


lemma pref_drop: "u \<le>p v \<Longrightarrow> drop p u \<le>p drop p v"
  using prefI[OF sym[OF drop_append]] unfolding prefix_def by blast

subsection "Prefix comparability"

lemma pref_comp_sym[sym]: "u \<bowtie> v \<Longrightarrow> v \<bowtie> u"
  by blast

lemma not_pref_comp_sym[sym]: "\<not> u \<bowtie> v \<Longrightarrow> \<not> v \<bowtie> u"
  by blast

lemma pref_comp_sym_iff: "u \<bowtie> v \<longleftrightarrow> v \<bowtie> u"
  by blast

lemmas ruler_le = prefix_length_prefix and
  ruler = prefix_same_cases and
  ruler' = prefix_same_cases[folded prefix_comparable_def]

lemma ruler_eq: "u \<cdot> x = v \<cdot> y \<Longrightarrow> u \<le>p v \<or> v \<le>p u"
  by (metis prefI prefix_same_cases)

lemma ruler_eq': "u \<cdot> x = v \<cdot> y \<Longrightarrow> u \<le>p v \<or> v <p u"
  using ruler_eq prefix_order.le_less by blast

lemmas ruler_eqE = ruler_eq[THEN disjE] and
       ruler_eqE' = ruler_eq'[THEN disjE] and
       ruler_pref = ruler[OF append_prefixD triv_pref] and
       ruler'[THEN pref_comp_eq]
lemmas ruler_prefE = ruler_pref[THEN disjE]

lemma ruler_comp: "u \<le>p v \<Longrightarrow> u' \<le>p v' \<Longrightarrow> v \<bowtie> v' \<Longrightarrow> u \<bowtie> u'"
  unfolding prefix_comparable_def
  using disjE[OF _ ruler[OF pref_trans] ruler[OF _ pref_trans]].

lemma ruler_pref': "w \<le>p v\<cdot>z \<Longrightarrow> w \<le>p v \<or> v \<le>p w"
  using ruler by blast

lemma ruler_pref'': "w \<le>p v\<cdot>z \<Longrightarrow> w \<bowtie> v"
  unfolding prefix_comparable_def using ruler_pref'.

lemma pref_cancel_right: assumes "u \<cdot> z \<le>p v \<cdot> z" shows "u \<le>p v"
proof-
  have "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|"
    using prefix_length_le[OF assms] by force
  from ruler_le[of u "v \<cdot> z" v, OF pref_extD[OF assms] triv_pref this]
  show "u \<le>p v".
qed

lemma pref_prod_pref_short: "u \<le>p z \<cdot> w \<Longrightarrow> v \<le>p w \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|z \<cdot> v\<^bold>| \<Longrightarrow> u \<le>p z \<cdot> v"
  using ruler_le[OF _ pref_cancel'].

lemma pref_prod_pref: "u \<le>p z \<cdot> w \<Longrightarrow> u \<le>p w \<Longrightarrow>  u \<le>p z \<cdot> u"
  using pref_prod_pref_short[OF _ _ suf_len'].

lemma pref_prod_pref': assumes "u \<le>p z\<cdot>u\<cdot>w" shows "u \<le>p z\<cdot>u"
  using pref_prod_pref[of  u z "u \<cdot> w", OF \<open>u \<le>p z\<cdot>u\<cdot>w\<close> triv_pref].

lemma pref_prod_long: "u \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> v \<le>p u"
  using ruler_le[OF triv_pref].

lemmas pref_prod_long_ext = pref_prod_long[OF append_prefixD]

lemma pref_prod_long_less: assumes "u \<le>p v \<cdot> w" and  "\<^bold>|v\<^bold>| < \<^bold>|u\<^bold>|" shows  "v <p u"
  using sprefI2[OF  pref_prod_long[OF \<open>u \<le>p v \<cdot> w\<close> less_imp_le[OF \<open>\<^bold>|v\<^bold>| < \<^bold>|u\<^bold>|\<close>]] \<open>\<^bold>|v\<^bold>| < \<^bold>|u\<^bold>|\<close>].

lemma pref_keeps_per_root: "u \<le>p r \<cdot> u \<Longrightarrow> v \<le>p u \<Longrightarrow> v \<le>p r \<cdot> v"
  using pref_prod_pref[of v r u] pref_trans[of v u "r\<cdot>u"] by blast

lemma pref_keeps_per_root': "u <p r \<cdot> u \<Longrightarrow> v \<le>p u \<Longrightarrow> v <p r \<cdot> v"
  using pref_keeps_per_root by auto

lemma per_root_pref_sing: "w <p r \<cdot> w \<Longrightarrow> u \<cdot> [a] \<le>p w \<Longrightarrow> u \<cdot> [a] \<le>p r \<cdot> u"
  using append_assoc pref_keeps_per_root' spref_snoc_iff by metis

lemma pref_prolong:  "w \<le>p z \<cdot> r \<Longrightarrow> r \<le>p s \<Longrightarrow> w \<le>p z \<cdot> s"
  using pref_trans[OF _ pref_cancel'].

lemma spref__pref_prolong:  "w <p z \<cdot> r \<Longrightarrow> r \<le>p s \<Longrightarrow> w <p z \<cdot> s"
  using prefix_order.less_le_trans[OF _ pref_cancel'].

lemma pref_spref_prolong:  "w \<le>p z \<cdot> r \<Longrightarrow> r <p s \<Longrightarrow> w <p z \<cdot> s"
  using prefix_order.le_less_trans[OF _ spref_cancel'].

lemma spref_spref_prolong:  "w <p z \<cdot> r \<Longrightarrow> r <p s \<Longrightarrow> w <p z \<cdot> s"
  using prefix_order.less_trans[OF _ spref_cancel'].

lemmas pref_shorten = pref_trans[OF pref_cancel']

lemma pref_prolong': "u \<le>p w \<cdot> z \<Longrightarrow> v \<cdot> u \<le>p z \<Longrightarrow> u \<le>p w \<cdot> v \<cdot> u"
  using ruler_le[OF _ pref_cancel' le_trans[OF suf_len' suf_len']].

lemma pref_prolong_per_root: "u \<le>p r \<cdot> s \<Longrightarrow> s \<le>p r \<cdot> s \<Longrightarrow> u \<le>p r \<cdot> u"
  using pref_prolong[of u r s "r \<cdot> s", THEN pref_prod_pref].

thm pref_compE
lemma pref_prolong_comp: "u \<le>p w \<cdot> z \<Longrightarrow> v \<cdot> u \<bowtie> z \<Longrightarrow> u \<le>p w \<cdot> v \<cdot> u"
  using pref_prolong' pref_prolong by (elim pref_compE)

lemma pref_prod_le[intro]: "u \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> u \<le>p v"
  using ruler_le[OF _ triv_pref].

lemma prod_pref_prod_le: "u\<cdot>v \<le>p x\<cdot>y \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>| \<Longrightarrow> u \<le>p x"
  using  pref_prod_le[OF append_prefixD].

lemma pref_prod_less: "u \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|u\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u <p v"
  using pref_prod_le[OF _ less_imp_le, THEN sprefI2].

lemma eq_le_pref[elim]: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> x \<le>p u"
  using pref_prod_le[OF prefI].

lemma eq_less_pref: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| < \<^bold>|u\<^bold>| \<Longrightarrow> x <p u"
  using pref_prod_less[OF prefI].

lemma eq_less_suf: assumes "x \<cdot> y = u \<cdot> v" shows "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>| \<Longrightarrow> v <s y"
  using eq_less_pref[reversed, folded strict_suffix_to_prefix, OF \<open>x \<cdot> y = u \<cdot> v\<close>[symmetric]]
  unfolding eq_len_iff_less[OF \<open>x \<cdot> y = u \<cdot> v\<close>].

lemma pref_prod_cancel: assumes "u \<le>p p\<cdot>w\<cdot>q" and "\<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|" and "\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|"
  obtains r where "p \<cdot> r = u" and "r \<le>p w"
proof-
  obtain r where [symmetric]: "u = p \<cdot> r" using pref_prod_long[OF \<open>u \<le>p p\<cdot>w\<cdot>q\<close>  \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>]..
  moreover have "r \<le>p w"
    using pref_prod_le[OF \<open>u \<le>p p\<cdot>w\<cdot>q\<close>[unfolded lassoc] \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|\<close>]
    unfolding \<open>p \<cdot> r = u\<close>[symmetric] by simp
  ultimately show thesis..
qed

lemma pref_prod_cancel': assumes "u \<le>p p\<cdot>w\<cdot>q" and "\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|" and "\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|"
  obtains r where "p \<cdot> r = u" and "r \<le>p w" and "r \<noteq> \<epsilon>"
proof-
  obtain r where "p \<cdot> r = u" and "r \<le>p w"
    using pref_prod_cancel[OF \<open>u \<le>p p\<cdot>w\<cdot>q\<close> less_imp_le[OF \<open>\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|\<close>] \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|\<close>].
  moreover have "r \<noteq> \<epsilon>" using  \<open>p \<cdot> r = u\<close> less_imp_neq[OF \<open>\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|\<close>] by fastforce
  ultimately show thesis..
qed

lemma non_comp_parallel: "\<not> u \<bowtie> v \<longleftrightarrow> u \<parallel> v"
  unfolding prefix_comparable_def parallel_def de_Morgan_disj..

lemma comp_refl: "u \<bowtie> u"
  unfolding prefix_comparable_def
  by simp

lemma incomp_cancel: "\<not> p\<cdot>u \<bowtie> p\<cdot>v \<Longrightarrow> \<not> u \<bowtie> v"
  unfolding prefix_comparable_def
  by simp

lemma comm_ruler: "r \<cdot> s \<le>p w1 \<Longrightarrow> s \<cdot> r \<le>p w2 \<Longrightarrow> w1 \<bowtie> w2 \<Longrightarrow> r \<cdot> s = s \<cdot> r"
  using pref_comp_eq[OF ruler_comp swap_len].

lemma comm_comp_eq: "r \<cdot> s \<bowtie> s \<cdot> r \<Longrightarrow> r \<cdot> s = s \<cdot> r"
  using comm_ruler by blast

lemma pref_share_take: "u \<le>p v \<Longrightarrow> q \<le> \<^bold>|u\<^bold>| \<Longrightarrow> take q u = take q v"
  by (auto simp add: prefix_def)

lemma pref_prod_longer: "u \<le>p z \<cdot> w \<Longrightarrow> v \<le>p w \<Longrightarrow> \<^bold>|z \<cdot> v\<^bold>| \<le> \<^bold>|u\<^bold>|  \<Longrightarrow> z \<cdot> v \<le>p u"
  using ruler_le[OF pref_cancel'].

lemma pref_comp_not_pref: "u \<bowtie> v \<Longrightarrow> \<not> v \<le>p u \<Longrightarrow> u <p v"
  by auto

lemma pref_comp_not_spref: "u \<bowtie> v \<Longrightarrow> \<not> u <p v \<Longrightarrow> v \<le>p u"
  using contrapos_np[OF _ pref_comp_not_pref].

lemma hd_prod: "u \<noteq> \<epsilon> \<Longrightarrow> (u \<cdot> v)!0 = u!0"
  by (cases u) (blast, simp)

lemma distinct_first: assumes "w \<noteq> \<epsilon>" "z \<noteq> \<epsilon>" "w!0 \<noteq> z!0" shows "w \<cdot> w' \<noteq> z \<cdot> z'"
  using hd_prod[of w w', OF \<open>w \<noteq> \<epsilon>\<close>] hd_prod[of z z', OF \<open>z \<noteq> \<epsilon>\<close>] \<open>w!0 \<noteq> z!0\<close> by auto

lemmas last_no_split = prefix_snoc

lemma last_no_split': "u <p w \<Longrightarrow> w \<le>p u \<cdot> [a] \<Longrightarrow> w = u \<cdot> [a]"
  unfolding prefix_order.less_le_not_le last_no_split by blast

lemma comp_shorter: "v \<bowtie> w \<Longrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>| \<Longrightarrow> v \<le>p w"
  unfolding prefix_comparable_def
  by (auto simp add: prefix_def)

lemma comp_shorter_conv: "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> u \<bowtie> v \<longleftrightarrow> u \<le>p v"
  using comp_shorter by auto

lemma pref_comp_len_trans: "w \<le>p v \<Longrightarrow> u \<bowtie> v \<Longrightarrow> \<^bold>|w\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> w \<le>p u"
  using ruler_le pref_trans by (elim pref_compE)

lemma comp_cancel: "z \<cdot> w1 \<bowtie> z \<cdot> w2 \<longleftrightarrow> w1 \<bowtie> w2"
  unfolding prefix_comparable_def
  using pref_cancel by auto

lemma emp_pref: "\<epsilon> \<le>p u"
  by simp

lemma emp_spref:  "u \<noteq> \<epsilon> \<Longrightarrow> \<epsilon> <p u"
  by simp

lemma long_pref: "u \<le>p v \<Longrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> u = v"
  by (auto simp add: prefix_def)

lemma not_comp_ext: "\<not> w1 \<bowtie>  w2 \<Longrightarrow> \<not> w1 \<cdot> z \<bowtie> w2 \<cdot> z'"
  using contrapos_nn[OF _ ruler_comp[OF triv_pref triv_pref]].

lemma mismatch_incopm: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> u \<cdot> [x] \<bowtie> v \<cdot> [y]"
  by (auto simp add: prefix_def)

lemma comp_prefs_comp: "u \<cdot> z \<bowtie> v \<cdot> w \<Longrightarrow> u \<bowtie> v"
  using ruler_comp[OF triv_pref triv_pref].

lemma comp_hd_eq: "u \<bowtie> v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> hd u = hd v"
  unfolding prefix_comparable_def
  by (auto simp add: prefix_def)

lemma pref_hd_eq': "p \<le>p u \<Longrightarrow> p \<le>p v \<Longrightarrow> p \<noteq> \<epsilon> \<Longrightarrow>  hd u = hd v"
  by (auto simp add: prefix_def)

lemma pref_hd_eq: "u \<le>p v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow>  hd u = hd v"
  by (auto simp add: prefix_def)

lemma sing_pref_hd: "[a] \<le>p v \<Longrightarrow> hd v = a"
  by (auto simp add: prefix_def)

lemma suf_last_eq: "p \<le>s u \<Longrightarrow> p \<le>s v \<Longrightarrow> p \<noteq> \<epsilon> \<Longrightarrow>  last u = last v"
  by (auto simp add: suffix_def)

lemma comp_hd_eq': "u \<cdot> r \<bowtie> v \<cdot> s \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> hd u = hd v"
using comp_hd_eq[OF comp_prefs_comp].

subsection \<open>Minimal and maximal prefix with a given property\<close>

lemma le_take_pref: assumes "k \<le> n" shows "take k ws \<le>p take n ws"
  using take_add[of k "(n-k)" ws, unfolded le_add_diff_inverse[OF \<open>k \<le> n\<close>]]
  by force

lemma min_pref: assumes  "u \<le>p w" and "P u"
  obtains v where "v \<le>p w" and "P v" and  "\<And> y. y \<le>p w \<Longrightarrow> P y \<Longrightarrow> v \<le>p y"
  using assms
proof(induction "\<^bold>|u\<^bold>|" arbitrary: u rule: less_induct)
  case (less u')
  then show ?case
  proof (cases "\<forall> y. y \<le>p w \<longrightarrow> P y \<longrightarrow> u' \<le>p y", blast)
    assume "\<not> (\<forall>y. y \<le>p w \<longrightarrow> P y \<longrightarrow> u' \<le>p y)"
    then obtain x where "x \<le>p w" and "P x" and " \<not> u' \<le>p x"
      by blast
    have "\<^bold>|x\<^bold>| < \<^bold>|u'\<^bold>|"
      using prefix_length_less[OF pref_comp_not_pref[OF ruler'[OF \<open>x \<le>p w\<close> \<open>u' \<le>p w\<close>]\<open> \<not> u' \<le>p x\<close>]].
    from less.hyps[OF this _ \<open>x \<le>p w\<close> \<open>P x\<close>] that
    show thesis by blast
  qed
qed


lemma min_pref': assumes  "u \<le>p w" and "P u"
  obtains v where "v \<le>p w" and "P v" and  "\<And> y. y \<le>p v \<Longrightarrow> P y \<Longrightarrow> y = v"
proof-
  from min_pref[of _  _ P, OF assms]
  obtain v where "v \<le>p w" and "P v" and min: "\<And>y. y \<le>p w \<Longrightarrow> P y \<Longrightarrow> v \<le>p y" by blast
  have "y = v" if "y \<le>p v" and "P y" for y
    using min[OF pref_trans[OF \<open>y \<le>p v\<close> \<open>v \<le>p w\<close>] \<open>P y\<close>] \<open>y \<le>p v\<close> by force
  from that[OF \<open>v \<le>p w\<close> \<open>P v\<close> this]
  show thesis.
qed

lemma max_pref: assumes  "u \<le>p w" and "P u"
  obtains v where "v \<le>p w" and "P v" and  "\<And> y. y \<le>p w \<Longrightarrow> P y \<Longrightarrow> y \<le>p v"
  using assms
proof(induction "\<^bold>|w\<^bold>|-\<^bold>|u\<^bold>|" arbitrary: u rule: less_induct)
  case (less u')
  then show ?case
  proof (cases "\<forall> y. y \<le>p w \<longrightarrow> P y \<longrightarrow> y \<le>p u'", blast)
    assume "\<not> (\<forall>y. y \<le>p w \<longrightarrow> P y \<longrightarrow>  y \<le>p  u')"
    then obtain x where "x \<le>p w" and "P x" and "\<not> x \<le>p u'" and "u' \<noteq> w"
      by blast
    from ruler'[OF \<open>x \<le>p w\<close> \<open>u' \<le>p w\<close>]
    have "\<^bold>|u'\<^bold>| < \<^bold>|x\<^bold>|"
      using  comp_shorter[OF \<open>x \<bowtie> u'\<close>] \<open>\<not> x \<le>p u'\<close> by fastforce
    hence "\<^bold>|w\<^bold>| - \<^bold>|x\<^bold>| < \<^bold>|w\<^bold>| - \<^bold>|u'\<^bold>|"
      using  \<open>x \<le>p w\<close>  \<open>u' \<noteq> w\<close> diff_less_mono2 leI[THEN long_pref[OF \<open>u' \<le>p w\<close>]] by blast
    from less.hyps[OF this _  \<open>x \<le>p w\<close> \<open>P x\<close>] that
    show thesis by blast
  qed
qed

section "Suffix and suffix comparability  properties"

lemmas suf_emp = suffix_bot.extremum_uniqueI

lemma triv_suf: "u \<le>s v \<cdot> u"
  by (simp add: suffix_def)

lemma emp_ssuf: "u \<noteq> \<epsilon> \<Longrightarrow> \<epsilon> <s u"
  by simp

lemma suf_cancel: "u\<cdot>v \<le>s w\<cdot>v \<Longrightarrow> u \<le>s w"
  by simp

lemma suf_cancel': "u \<le>s w \<Longrightarrow> u\<cdot>v \<le>s w\<cdot>v"
  by simp

lemma ssuf_cancel_conv: "x \<cdot> z <s y \<cdot> z \<longleftrightarrow> x <s y"
  by auto

text\<open>Straightforward relations of suffix and prefix follow.\<close>

lemmas suf_rev_pref_iff = suffix_to_prefix \<comment> \<open>provided by Sublist.thy\<close>

lemmas ssuf_rev_pref_iff = strict_suffix_to_prefix \<comment> \<open>provided by Sublist.thy\<close>

lemma pref_rev_suf_iff: "u \<le>p v \<longleftrightarrow> rev u \<le>s rev v"
  using suffix_to_prefix[of "rev u" "rev v"] unfolding rev_rev_ident
  by blast

lemma spref_rev_suf_iff: "s <p w \<longleftrightarrow> rev s <s rev w"
  using strict_suffix_to_prefix[of "rev s" "rev w", unfolded rev_rev_ident, symmetric].

lemma nsuf_rev_pref_iff: "s \<le>ns w \<longleftrightarrow> rev s \<le>np rev w"
  unfolding nonempty_prefix_def nonempty_suffix_def suffix_to_prefix
  by fast

lemma npref_rev_suf_iff: "s \<le>np w \<longleftrightarrow> rev s \<le>ns rev w"
  unfolding nonempty_prefix_def nonempty_suffix_def pref_rev_suf_iff
  by fast

lemmas [reversal_rule] =
  suf_rev_pref_iff[symmetric]
  pref_rev_suf_iff[symmetric]
  nsuf_rev_pref_iff[symmetric]
  npref_rev_suf_iff[symmetric]
  ssuf_rev_pref_iff[symmetric]
  spref_rev_suf_iff[symmetric]

lemmas sufE = prefixE[reversed] and
       prefE = prefixE and
       ssuf_exE = spref_exE[reversed]

lemmas suf_prod_long_ext  = pref_prod_long_ext[reversed]

lemmas suf_prolong_per_root = pref_prolong_per_root[reversed]

lemmas suf_ext = suffix_appendI \<comment> \<open>provided by Sublist.thy\<close>

lemmas ssuf_ext = spref_ext[reversed] and
  ssuf_extD = spref_extD[reversed] and
  suf_ext_nem = pref_ext_nemp[reversed] and
  suf_same_len = pref_same_len[reversed] and
  suf_take = pref_drop[reversed] and
  suf_share_take = pref_share_take[reversed] and
  long_suf = long_pref[reversed] and
  strict_suffixE' = strict_prefixE'[reversed] and
  ssuf_tl_suf  = spref_butlast_pref[reversed]


lemma ssuf_Cons_iff [simp]: "u <s a # v \<longleftrightarrow> u \<le>s v"
  by (auto simp only: strict_suffix_def suffix_Cons) (simp add: suffix_def)

lemma ssuf_induct [case_names ssuf]:
  assumes "\<And>u. (\<And>v. v <s u \<Longrightarrow> P v) \<Longrightarrow> P u"
  shows "P u"
proof (induction u rule: list.induct[of "\<lambda>u. \<forall>v. v \<le>s u \<longrightarrow> P v", rule_format, OF _ _ triv_suf],
       use assms suffix_bot.extremum_strict in blast)
qed (metis assms ssuf_Cons_iff suffix_Cons)

subsection "Suffix comparability"

lemma eq_le_suf[elim]: assumes "x \<cdot> y = u \<cdot> v" "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" shows "v \<le>s y"
  using eq_le_pref[reversed, OF assms(1)[symmetric]]
  lenarg[OF \<open>x \<cdot> y = u \<cdot> v\<close>, unfolded lenmorph] \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|\<close> by linarith

lemmas eq_le_suf'[elim] = eq_le_pref[reversed]

lemma eq_le_suf''[elim]: assumes "v \<cdot> u = y \<cdot> x" "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" shows "x \<le>s u"
  using eq_le_suf'[OF assms(1)[symmetric] assms(2)].

lemma pref_comp_rev_suf_comp[reversal_rule]: "(rev w) \<bowtie>\<^sub>s (rev v) \<longleftrightarrow> w \<bowtie> v"
  unfolding suffix_comparable_def by simp

lemma suf_comp_rev_pref_comp[reversal_rule]: "(rev w) \<bowtie> (rev v) \<longleftrightarrow> w \<bowtie>\<^sub>s v"
  unfolding suffix_comparable_def by simp

lemmas suf_ruler_le = suffix_length_suffix \<comment> \<open>provided by Sublist.thy, same as ruler\_le[reversed]\<close>

lemmas suf_ruler = suffix_same_cases \<comment> \<open>provided by Sublist.thy, same as ruler[reversed]\<close>

lemmas suf_ruler_eq_len = ruler_eq_len[reversed] and
  suf_ruler_comp = ruler_comp[reversed] and
  ruler_suf = ruler_pref[reversed] and
  ruler_suf' = ruler_pref'[reversed] and
  ruler_suf'' = ruler_pref''[reversed] and
  suf_prod_le = pref_prod_le[reversed] and
  prod_suf_prod_le = prod_pref_prod_le[reversed] and
  suf_prod_eq = pref_prod_eq[reversed] and
  suf_prod_less = pref_prod_less[reversed] and
  suf_prod_cancel = pref_prod_cancel[reversed] and
  suf_prod_cancel' = pref_prod_cancel'[reversed] and
  suf_prod_suf_short = pref_prod_pref_short[reversed] and
  suf_prod_suf = pref_prod_pref[reversed] and
  suf_prod_suf' = pref_prod_pref'[reversed, unfolded rassoc] and
  suf_prolong = pref_prolong[reversed] and
  suf_prolong' = pref_prolong'[reversed, unfolded rassoc] and
  suf_prolong_comp = pref_prolong_comp[reversed, unfolded rassoc] and
  suf_prod_long = pref_prod_long[reversed] and
  suf_prod_long_less = pref_prod_long_less[reversed] and
  suf_prod_longer = pref_prod_longer[reversed] and
  suf_keeps_root = pref_keeps_per_root[reversed] and
  comm_suf_ruler = comm_ruler[reversed]

lemmas comp_sufs_comp = comp_prefs_comp[reversed] and
  suf_comp_not_suf = pref_comp_not_pref[reversed] and
  suf_comp_not_ssuf = pref_comp_not_spref[reversed] and
    suf_comp_cancel = comp_cancel[reversed] and
  suf_not_comp_ext = not_comp_ext[reversed] and
  mismatch_suf_incopm = mismatch_incopm[reversed] and
  suf_comp_sym[sym] = pref_comp_sym[reversed] and
  suf_comp_refl = comp_refl[reversed]

lemma suf_comp_or: "u \<bowtie>\<^sub>s v \<longleftrightarrow> u \<le>s v \<or> v \<le>s u"
  unfolding suffix_comparable_def prefix_comparable_def suf_rev_pref_iff..

lemma comm_comp_eq_conv: "r \<cdot> s \<bowtie> s \<cdot> r \<longleftrightarrow> r \<cdot> s = s \<cdot> r"
  using pref_comp_eq[OF _ swap_len] comp_refl by metis

lemma comm_comp_eq_conv_suf: "r \<cdot> s \<bowtie>\<^sub>s s \<cdot> r \<longleftrightarrow> r \<cdot> s = s \<cdot> r"
  using pref_comp_eq[reversed, OF _ swap_len, of r s] suf_comp_refl[of "r \<cdot> s"] by argo

lemma suf_comp_last_eq: assumes "u \<bowtie>\<^sub>s v" "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
  shows "last u = last v"
   using comp_hd_eq[reversed, OF assms] unfolding hd_rev hd_rev.

lemma suf_comp_last_eq': "r \<cdot> u \<bowtie>\<^sub>s s \<cdot> v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> last u = last v"
  using comp_sufs_comp suf_comp_last_eq  by blast

section "Left and Right Quotient"

text\<open>A useful function of left quotient is given. Note that the function is sometimes undefined.\<close>

definition left_quotient:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"   ("(_\<inverse>\<^sup>>)(_)" [75,74] 74)
  where  "left_quotient u v  = drop \<^bold>|u\<^bold>| v"
notation (latex output) left_quotient  ("\<^latex>\<open>\\ensuremath{ {\<close>_ \<^latex>\<open>}^{-1} \\cdot {\<close> _ \<^latex>\<open>}}\<close>")


text\<open>Analogously, we define the right quotient.\<close>

definition right_quotient :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  ("(_)(\<^sup><\<inverse>_) " [76,77] 76)
  where "right_quotient u v  = rev ((rev v)\<inverse>\<^sup>>(rev u))"
notation (latex output) right_quotient ("\<^latex>\<open>\\ensuremath{ {\<close>_ \<^latex>\<open>} \\cdot {\<close> _ \<^latex>\<open>}^{-1}}\<close>")

lemmas lq_def = left_quotient_def and
       rq_def = right_quotient_def

text\<open>Priorities of these operations are as follows:\<close>

lemma "u\<^sup><\<inverse>v\<^sup><\<inverse>w = (u\<^sup><\<inverse>v)\<^sup><\<inverse>w"
  by simp

lemma "u\<inverse>\<^sup>>v\<inverse>\<^sup>>w = u\<inverse>\<^sup>>(v\<inverse>\<^sup>>w)"
  by simp

lemma "u\<inverse>\<^sup>>v\<^sup><\<inverse>w = u\<inverse>\<^sup>>(v\<^sup><\<inverse>w)"
  by simp

lemma "r \<cdot> u\<inverse>\<^sup>>w\<^sup><\<inverse>v \<cdot> s = r \<cdot> (u\<inverse>\<^sup>>w\<^sup><\<inverse>v) \<cdot> s"
  by simp

lemma rq_rev_lq[reversal_rule]: "(rev v)\<^sup><\<inverse>(rev u) = rev (u\<inverse>\<^sup>>v)"
  unfolding right_quotient_def
  by simp

lemma lq_rev_rq[reversal_rule]: "(rev v)\<inverse>\<^sup>>rev u = rev (u\<^sup><\<inverse>v)"
  unfolding right_quotient_def
  by simp

subsection \<open>Left Quotient\<close>

lemma lqI:  "u \<cdot> z = v \<Longrightarrow> u\<inverse>\<^sup>>v = z"
  unfolding left_quotient_def
  by force

lemma lq_triv[simp]:  "u\<inverse>\<^sup>>(u \<cdot> z) = z"
  using lqI[OF refl].

lemma lq_triv'[simp]:  "u \<cdot> u\<inverse>\<^sup>>(u \<cdot> z) = u \<cdot>z"
  by simp

lemma append_lq: assumes "u\<cdot>v \<le>p w" shows "(u\<cdot>v)\<inverse>\<^sup>>w = v\<inverse>\<^sup>>(u\<inverse>\<^sup>>w)"
  using lq_triv[of "u\<cdot>v"] lq_triv[of "v"] lq_triv[of "u" "v\<cdot>_"] assms[unfolded prefix_def]
  by force

lemma lq_self[simp]: "u\<inverse>\<^sup>>u = \<epsilon>"
  unfolding left_quotient_def
  by simp

lemma lq_emp[simp]: "\<epsilon>\<inverse>\<^sup>>u = u"
  unfolding left_quotient_def
  by simp

lemma lq_pref[simp]: "u \<le>p v \<Longrightarrow> u \<cdot> (u\<inverse>\<^sup>>v) = v"
  unfolding left_quotient_def prefix_def
  by fastforce

lemma lq_pref_conv: "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> u \<le>p v \<longleftrightarrow> u \<cdot> u\<inverse>\<^sup>>v = v"
  using lq_pref by blast

lemma lq_len:  "\<^bold>|u\<inverse>\<^sup>>v\<^bold>| = \<^bold>|v\<^bold>| - \<^bold>|u\<^bold>|"
    unfolding left_quotient_def using length_drop.

lemmas lcp_lq = lq_pref[OF longest_common_prefix_prefix1] lq_pref[OF longest_common_prefix_prefix2]

lemma lq_pref_cancel: "u \<le>p v \<Longrightarrow> v \<cdot> r = u \<cdot> s \<Longrightarrow>  (u\<inverse>\<^sup>>v) \<cdot> r = s"
  unfolding prefix_def
  by force

lemma lq_the: assumes "u \<le>p v"
  shows "(THE z. u \<cdot> z = v) = (u\<inverse>\<^sup>>v)"
proof-
  have "u\<cdot>z = v \<Longrightarrow> z = (u\<inverse>\<^sup>>v)" for z
    by fastforce
  from the_equality[of "\<lambda>z. u\<cdot>z=v", OF lq_pref this, OF assms]
  show ?thesis.
qed

lemma lq_same_len: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u\<inverse>\<^sup>>v = \<epsilon>"
  unfolding left_quotient_def by simp

lemma lq_assoc: "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> (u\<inverse>\<^sup>>v)\<inverse>\<^sup>>w = v\<inverse>\<^sup>>(u \<cdot> w)"
  unfolding  left_quotient_def using prefix_length_le by auto

lemma lq_assoc': "(u \<cdot> w)\<inverse>\<^sup>>v = w\<inverse>\<^sup>>(u\<inverse>\<^sup>>v)"
  unfolding left_quotient_def lenmorph
  by (simp add: add.commute)

lemma lq_reassoc: "u \<le>p v \<Longrightarrow> (u\<inverse>\<^sup>>v)\<cdot>w = u\<inverse>\<^sup>>(v\<cdot>w)"
  unfolding prefix_def
  by force

lemma lq_trans: "u \<le>p v \<Longrightarrow> v \<le>p w \<Longrightarrow> (u\<inverse>\<^sup>>v) \<cdot> (v\<inverse>\<^sup>>w) = u\<inverse>\<^sup>>w"
  by (simp add: lq_reassoc)

lemma lq_rq_reassoc_suf: assumes "u \<le>p z" "u \<le>s w" shows "w\<cdot>u\<inverse>\<^sup>>z = w\<^sup><\<inverse>u \<cdot> z"
  using rassoc[of "w\<^sup><\<inverse>u"  u  "u\<inverse>\<^sup>>z", unfolded lq_pref[OF \<open>u \<le>p z\<close>] lq_pref[reversed, OF \<open>u \<le>s w\<close>]].

lemma lq_ne: "p \<le>p u\<cdot>p \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> p\<inverse>\<^sup>>(u\<cdot>p) \<noteq> \<epsilon>"
  using lq_pref[of p "u \<cdot> p"] by fastforce

lemma lq_spref: "u <p v \<Longrightarrow> u\<inverse>\<^sup>>v \<noteq> \<epsilon>"
  using lq_pref by (auto simp add: prefix_def)

lemma lq_suf_suf: "r \<le>p s \<Longrightarrow> (r\<inverse>\<^sup>>s) \<le>s s"
  by (auto simp add: prefix_def)

lemma lq_short_len: "r \<le>p s \<Longrightarrow> \<^bold>|r\<^bold>| +  \<^bold>|r\<inverse>\<^sup>>s\<^bold>| = \<^bold>|s\<^bold>|"
  by (auto simp add: prefix_def)

lemma pref_lq: "v \<le>p w \<Longrightarrow> u\<inverse>\<^sup>>v \<le>p u\<inverse>\<^sup>>w"
  unfolding left_quotient_def prefix_def
  using drop_append by blast

lemma spref_lq: "u \<le>p v \<Longrightarrow> v <p w \<Longrightarrow> u\<inverse>\<^sup>>v <p u\<inverse>\<^sup>>w"
  by (auto simp add: prefix_def)

lemma pref_gcd_lq: assumes "u \<le>p v" shows "(gcd \<^bold>|u\<^bold>| \<^bold>|u\<inverse>\<^sup>>v\<^bold>|) = gcd \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|"
  using gcd_add2[of "\<^bold>|u\<^bold>|" "\<^bold>|u\<inverse>\<^sup>>v\<^bold>|", unfolded lq_short_len[OF assms], symmetric].

lemma conjug_lq: "x \<cdot> z = z \<cdot> y \<Longrightarrow> y = z\<inverse>\<^sup>>(x \<cdot> z)"
  by simp

lemma conjug_emp_emp: "p \<le>p u \<cdot> p \<Longrightarrow> p\<inverse>\<^sup>>(u \<cdot> p) = \<epsilon> \<Longrightarrow> u = \<epsilon>"
  using lq_ne by blast


lemma hd_lq_conv_nth: assumes "u <p v" shows "hd(u\<inverse>\<^sup>>v) = v!\<^bold>|u\<^bold>|"
  using prefix_length_less[OF assms, THEN hd_drop_conv_nth] unfolding lq_def.

lemma concat_morph_lq: "us \<le>p ws \<Longrightarrow> concat (us\<inverse>\<^sup>>ws) = (concat us)\<inverse>\<^sup>>(concat ws)"
  by (auto simp add: prefix_def)


lemma pref_cancel_lq: assumes "u \<le>p x \<cdot> y"
  shows "x\<inverse>\<^sup>>u \<le>p y"
  using pref_lq[OF \<open>u \<le>p x \<cdot> y\<close>, of x, unfolded lq_triv].

lemma pref_cancel_lq_ext: assumes "u \<cdot> v \<le>p x \<cdot> y" and  "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" shows "x\<inverse>\<^sup>>u \<cdot> v \<le>p y"
proof-
  note pref_prod_long[OF append_prefixD, OF \<open>u \<cdot> v \<le>p x \<cdot> y\<close> \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>]
  from  pref_cancel_lq[OF \<open>u \<cdot> v \<le>p x \<cdot> y\<close>]
  show "x\<inverse>\<^sup>>u \<cdot> v \<le>p y"
    unfolding lq_reassoc[OF \<open>x \<le>p u\<close>] using \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|\<close> by force
qed

lemma pref_cancel_lq_ext': assumes "u \<cdot> v \<le>p x \<cdot> y" and  "\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|" shows "v \<le>p u\<inverse>\<^sup>>x \<cdot> y"
  using pref_lq[OF \<open>u \<cdot> v \<le>p x \<cdot> y\<close>, of u]
  unfolding lq_triv lq_reassoc[OF pref_prod_le[OF append_prefixD[OF \<open>u \<cdot> v \<le>p x \<cdot> y\<close>] \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>]].

lemma empty_lq_eq: "r \<le>p z \<Longrightarrow> r\<inverse>\<^sup>>z = \<epsilon> \<Longrightarrow> r = z"
  unfolding prefix_def by force

lemma le_if_then_lq: "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> (if \<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>| then v\<inverse>\<^sup>>u  else u\<inverse>\<^sup>>v) = u\<inverse>\<^sup>>v"
  by (cases "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|", simp_all add: lq_same_len)

lemma append_comp_lq: "u \<cdot> v \<bowtie> w \<Longrightarrow> v \<bowtie> u\<inverse>\<^sup>>w"
proof (elim pref_compE)
  assume "u \<cdot> v \<le>p w"
  from pref_drop[OF this, of "\<^bold>|u\<^bold>|", unfolded drop_pref]
  show "v \<bowtie> u\<inverse>\<^sup>>w"
    unfolding left_quotient_def by (rule pref_compI1)
next
  assume "w \<le>p u \<cdot> v"
  from pref_drop[OF this, of "\<^bold>|u\<^bold>|", unfolded drop_pref]
  show "v \<bowtie> u\<inverse>\<^sup>>w"
    unfolding left_quotient_def by (rule pref_compI2)
qed

subsection "Right quotient"

lemmas rqI = lqI[reversed] and
  rq_triv[simp] = lq_triv[reversed] and
  rq_triv'[simp] = lq_triv'[reversed] and
  rq_self[simp] = lq_self[reversed] and
  rq_emp[simp] = lq_emp[reversed] and
  rq_suf[simp] = lq_pref[reversed] and
  rq_ssuf = lq_spref[reversed] and
  rq_reassoc = lq_reassoc[reversed] and
  rq_len = lq_len[reversed] and
  rq_trans = lq_trans[reversed] and
  rq_lq_reassoc_suf = lq_rq_reassoc_suf[reversed] and
  rq_ne = lq_ne[reversed] and
  rq_suf_suf = lq_suf_suf[reversed] and
  suf_rq = pref_lq[reversed] and
  ssuf_rq = spref_lq[reversed] and
  conjug_rq = conjug_lq[reversed] and
  conjug_emp_emp' = conjug_emp_emp[reversed] and
  rq_take = lq_def[reversed] and
  empty_rq_eq = empty_lq_eq[reversed] and
  append_rq = append_lq[reversed] and
  rq_same_len = lq_same_len[reversed] and
  rq_assoc = lq_assoc[reversed] and
  rq_assoc' = lq_assoc'[reversed] and
  le_if_then_rq =  le_if_then_lq[reversed] and
  append_comp_rq = append_comp_lq[reversed]

subsection \<open>Left and right quotients combined\<close>

lemma pref_lq_rq_id:  "p \<le>p w \<Longrightarrow> w\<^sup><\<inverse>(p\<inverse>\<^sup>>w) = p"
  unfolding prefix_def
  using rq_triv[of p "p\<inverse>\<^sup>>w"] by force

lemmas suf_rq_lq_id = pref_lq_rq_id[reversed]

lemma rev_lq': "r \<le>p s \<Longrightarrow> rev (r\<inverse>\<^sup>>s) = (rev s)\<^sup><\<inverse>(rev r)"
  by (simp add: rq_rev_lq)

lemma pref_rq_suf_lq: "s \<le>s u \<Longrightarrow> r \<le>p (u\<^sup><\<inverse>s) \<Longrightarrow> s \<le>s (r\<inverse>\<^sup>>u)"
  using lq_reassoc[of r "u\<^sup><\<inverse>s" s] rq_suf[of s u] triv_suf[of s "r\<inverse>\<^sup>>u\<^sup><\<inverse>s"]
  by presburger

lemmas suf_lq_pref_rq = pref_rq_suf_lq[reversed]

lemma "w\<cdot>s = v \<Longrightarrow> v\<^sup><\<inverse>s = w" using rqI.

lemma lq_rq_assoc: "s \<le>s u \<Longrightarrow> r \<le>p (u\<^sup><\<inverse>s) \<Longrightarrow> (r\<inverse>\<^sup>>u)\<^sup><\<inverse>s = r\<inverse>\<^sup>>(u\<^sup><\<inverse>s)"
  using lq_reassoc[of r "u\<^sup><\<inverse>s" s] rq_suf[of s u] rqI[of "r\<inverse>\<^sup>>u\<^sup><\<inverse>s" s "r\<inverse>\<^sup>>u"]
  by argo

lemmas rq_lq_assoc = lq_rq_assoc[reversed]

lemma lq_prod: "u \<le>p v\<cdot>u \<Longrightarrow> u \<le>p w \<Longrightarrow>  u\<inverse>\<^sup>>(v\<cdot>u)\<cdot>u\<inverse>\<^sup>>w = u\<inverse>\<^sup>>(v\<cdot>w)"
  using lq_reassoc[of u "v \<cdot> u" "u\<inverse>\<^sup>>w"] lq_rq_reassoc_suf[of u w "v \<cdot> u", unfolded rq_triv[of v u]]
  by (simp add: suffix_def)

lemmas rq_prod = lq_prod[reversed]

lemma pref_suf_mid: assumes "p\<cdot>w\<cdot>s = p'\<cdot>v\<cdot>s'" and "p \<le>p p'" and "s \<le>s s'"
  shows "v \<le>f w"
proof-
  have "p\<cdot>w\<cdot>s  = (p \<cdot> p\<inverse>\<^sup>>p') \<cdot> v \<cdot> (s'\<^sup><\<inverse>s  \<cdot> s)"
    using \<open>p\<cdot>w\<cdot>s = p'\<cdot>v\<cdot>s'\<close>
    unfolding lq_pref[OF \<open>p \<le>p p'\<close>] rq_suf[OF \<open>s \<le>s s'\<close>].
  thus ?thesis
    by simp
qed

section \<open>Equidivisibility\<close>

text\<open>Equidivisibility is the following property: if
\[
xy = uv,
\]
then there exists a word $t$ such that $xt = u$ and $ty = v$, or $ut = x$ and $y = tv$.
For monoids over words, this property is equivalent to the freeness of the monoid.
As the monoid of all words is free, we can prove that it is equidivisible.
Related lemmas based on this property follow.
\<close>

thm append_eq_conv_conj[folded left_quotient_def]
lemma eqd: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> \<exists> t. x \<cdot> t = u \<and> t \<cdot> v = y"
  by (simp add: append_eq_conv_conj)

lemma eqdE: assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|"
  obtains t where "x \<cdot> t = u" and "t \<cdot> v = y"
  using eqd[OF assms] by blast

lemma eqd_lessE: assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>|"
  obtains t where "x \<cdot> t = u" and "t \<cdot> v = y" and "t \<noteq> \<epsilon>"
  using eqdE[OF assms(1) less_imp_le[OF assms(2)]] assms(2)
  using append.right_neutral less_not_refl by metis

lemma eqdE': assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|v\<^bold>| \<le> \<^bold>|y\<^bold>|"
  obtains t where "x \<cdot> t = u" and "t \<cdot> v = y"
  using eqdE[OF assms(1)] lenarg[OF assms(1), unfolded lenmorph] assms(2)
  by auto

thm long_pref

lemma eqd_pref_suf_iff: assumes "x \<cdot> y = u \<cdot> v" shows "x \<le>p u \<longleftrightarrow> v \<le>s y"
  by (rule linorder_le_cases[of "\<^bold>|x\<^bold>|" "\<^bold>|u\<^bold>|"], use eqd[OF assms] in blast)
  (use eqd[OF assms[symmetric]] in fastforce)


lemma eqd_spref_ssuf_iff: assumes "x \<cdot> y = u \<cdot> v" shows "x <p u \<longleftrightarrow> v <s y"
  using eqd_pref_suf_iff[OF assms] assms by force

lemma eqd_pref: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> x \<cdot> (x\<inverse>\<^sup>>u) = u \<and> (x\<inverse>\<^sup>>u) \<cdot> v = y"
  using eqd lq_triv by blast

lemma eqd_pref1: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> x \<cdot> (x\<inverse>\<^sup>>u) = u"
  using eqd_pref by blast

lemma eqd_pref2: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> (x\<inverse>\<^sup>>u) \<cdot> v = y"
  using eqd_pref by blast

lemma eqd_eq: assumes "x \<cdot> y = u \<cdot> v" "\<^bold>|x\<^bold>| = \<^bold>|u\<^bold>|" shows "x = u" "y = v"
  using assms by simp_all

lemma eqd_eq_suf: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|y\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> x = u \<and> y = v"
  by simp

lemma eqd_comp: assumes "x \<cdot> y = u \<cdot> v" shows "x \<bowtie> u"
  using le_cases[of "\<^bold>|x\<^bold>|" "\<^bold>|u\<^bold>|" "x \<bowtie> u"]
    eqd_pref1[of x y u v, THEN prefI[of x "x\<inverse>\<^sup>>u" u], OF assms]
    eqd_pref1[of u v x y, THEN prefI[of u "u\<inverse>\<^sup>>x" x], OF assms[symmetric]] by auto

\<comment> \<open>not equal to eqd\_pref1[reversed]\<close>
lemma eqd_suf1: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> (y\<^sup><\<inverse>v)\<cdot>v = y"
  using eqd_pref2 rq_triv by blast

\<comment> \<open>not equal to eqd\_pref2[reversed]\<close>
lemma eqd_suf2: assumes "x \<cdot> y = u \<cdot> v" "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" shows "x \<cdot> (y\<^sup><\<inverse>v) = u"
  using rq_reassoc[OF sufI[OF eqd_suf1[OF \<open>x \<cdot> y = u \<cdot> v\<close> \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>]], of x, unfolded \<open>x \<cdot> y = u \<cdot> v\<close> rq_triv[of u v]].

\<comment> \<open> not equal to eqd\_pref[reversed] \<close>
lemma eqd_suf: assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|"
  shows "(y\<^sup><\<inverse>v)\<cdot>v = y \<and> x \<cdot> (y\<^sup><\<inverse>v) = u"
  using eqd_suf1[OF assms] eqd_suf2[OF assms] by blast

lemma eqd_exchange_aux:
  assumes "u \<cdot> v = x \<cdot> y" and "u \<cdot> v' = x \<cdot> y'" and "u' \<cdot> v = x' \<cdot> y" and "\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|"
  shows "u' \<cdot> v' = x' \<cdot> y'"
  using eqd[OF \<open>u \<cdot> v = x \<cdot> y\<close> \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>] eqd[OF \<open>u \<cdot> v' = x \<cdot> y'\<close> \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>] \<open>u' \<cdot> v = x' \<cdot> y\<close> by force

lemma eqd_exchange:
  assumes "u \<cdot> v = x \<cdot> y" and "u \<cdot> v' = x \<cdot> y'" and "u' \<cdot> v = x' \<cdot> y"
  shows "u' \<cdot> v' = x' \<cdot> y'"
  using eqd_exchange_aux[OF assms]  eqd_exchange_aux[OF assms[symmetric], symmetric] by force

hide_fact eqd_exchange_aux

section \<open>Longest common prefix\<close>

lemmas lcp_simps = longest_common_prefix.simps \<comment> \<open>provided by Sublist.thy\<close>

lemmas lcp_sym = lcp.commute

\<comment> \<open>provided by Sublist.thy\<close>
lemmas lcp_pref = longest_common_prefix_prefix1
lemmas lcp_pref' = longest_common_prefix_prefix2
lemmas pref_pref_lcp[intro] = longest_common_prefix_max_prefix

lemma lcp_pref_ext: "u \<le>p v \<Longrightarrow> u \<le>p (u \<cdot> w) \<and>\<^sub>p (v \<cdot> z)"
  using longest_common_prefix_max_prefix prefix_prefix triv_pref by metis

lemma pref_non_pref_lcp_pref: assumes "u \<le>p w" and "\<not> u \<le>p z" shows "w \<and>\<^sub>p z <p u"
proof-
  note ruler'[OF \<open>u \<le>p w\<close> lcp_pref, of z, unfolded prefix_comparable_def]
  with pref_trans[of u "w \<and>\<^sub>p z", OF _ lcp_pref'] \<open>\<not> u \<le>p z\<close>
  show "w \<and>\<^sub>p z <p u"
    by auto
qed

lemmas lcp_take = pref_take[OF lcp_pref] and
       lcp_take' = pref_take[OF lcp_pref']

lemma lcp_take_eq: "take (\<^bold>|u \<and>\<^sub>p v\<^bold>|) u = take (\<^bold>|u \<and>\<^sub>p v\<^bold>|) v"
  unfolding lcp_take lcp_take'..

lemma lcp_pref_conv: "u \<and>\<^sub>p v = u \<longleftrightarrow> u \<le>p v"
  unfolding prefix_order.eq_iff[of "u \<and>\<^sub>p v" u]
  using lcp_pref'[of u v]
    lcp_pref[of u v] longest_common_prefix_max_prefix[OF self_pref[of u], of v]
  by auto

lemma lcp_pref_conv': "u \<and>\<^sub>p v = v \<longleftrightarrow> v \<le>p u"
  using lcp_pref_conv[of v u, unfolded lcp_sym[of v]].

lemmas lcp_left_idemp[simp] = lcp_pref[folded lcp_pref_conv'] and
       lcp_right_idemp[simp] = lcp_pref'[folded lcp_pref_conv] and
       lcp_left_idemp'[simp] = lcp_pref'[folded lcp_pref_conv'] and
       lcp_right_idemp'[simp] = lcp_pref[folded lcp_pref_conv]

lemma lcp_per_root:  "r \<cdot> s \<and>\<^sub>p s \<cdot> r \<le>p r \<cdot> (r \<cdot> s \<and>\<^sub>p s \<cdot> r)"
  using  pref_prod_pref[OF pref_prolong[OF lcp_pref triv_pref] lcp_pref'].

lemma lcp_per_root':  "r \<cdot> s \<and>\<^sub>p s \<cdot> r \<le>p s \<cdot> (r \<cdot> s \<and>\<^sub>p s \<cdot> r)"
  using lcp_per_root[of s r, unfolded lcp_sym[of "s \<cdot> r"]].

lemma pref_lcp_pref: "w \<le>p u \<and>\<^sub>p v \<Longrightarrow> w \<le>p u"
  using lcp_pref pref_trans by blast

lemma pref_lcp_pref': "w \<le>p u \<and>\<^sub>p v \<Longrightarrow> w \<le>p v"
  using pref_lcp_pref[of w v u, unfolded lcp_sym[of v u]].

lemmas lcp_self = lcp.idem

lemma lcp_eq_len: "\<^bold>|u\<^bold>| = \<^bold>|u \<and>\<^sub>p v\<^bold>| \<Longrightarrow> u = u \<and>\<^sub>p v"
  using  long_pref[OF lcp_pref, of u v] by auto

lemma lcp_len: "\<^bold>|u\<^bold>| \<le> \<^bold>|u \<and>\<^sub>p v\<^bold>| \<Longrightarrow> u \<le>p v"
  using long_pref[OF lcp_pref, of u v] unfolding lcp_pref_conv[symmetric].

lemma lcp_len': "\<not> u \<le>p v \<Longrightarrow> \<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|u\<^bold>|"
  using not_le_imp_less[OF contrapos_nn[OF _ lcp_len]].

lemma incomp_lcp_len: "\<not> u \<bowtie> v \<Longrightarrow> \<^bold>|u \<and>\<^sub>p v\<^bold>| < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|"
  using lcp_len'[of u v] lcp_len'[of v u] unfolding lcp_sym[of v] min_less_iff_conj by blast

lemma lcp_ext_right_conv: "\<not> r \<bowtie> r' \<Longrightarrow> (r \<cdot> u) \<and>\<^sub>p (r' \<cdot> v) = r \<and>\<^sub>p r'"
  unfolding prefix_comparable_def
  by (induct r r' rule: list_induct2') simp_all

lemma lcp_ext_right [case_names comp non_comp]: obtains  "r \<bowtie> r'" | "(r \<cdot> u) \<and>\<^sub>p (r' \<cdot> v) = r \<and>\<^sub>p r'"
  using lcp_ext_right_conv by blast

lemma lcp_same_len: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<cdot> w \<and>\<^sub>p v \<cdot> w' = u \<and>\<^sub>p v"
  using pref_comp_eq by (cases rule: lcp_ext_right) (elim notE)

lemma lcp_mismatch: "\<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|u\<^bold>| \<Longrightarrow> \<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u! \<^bold>|u \<and>\<^sub>p v\<^bold>| \<noteq> v! \<^bold>|u \<and>\<^sub>p v\<^bold>|"
  by (induct u v rule: list_induct2') auto

lemma lcp_mismatch': "\<not> u \<bowtie> v \<Longrightarrow> u! \<^bold>|u \<and>\<^sub>p v\<^bold>| \<noteq> v! \<^bold>|u \<and>\<^sub>p v\<^bold>|"
  using incomp_lcp_len lcp_mismatch unfolding min_less_iff_conj..

lemma lcp_mismatchE: assumes "\<not> us \<bowtie> vs"
  obtains us' vs'
  where "(us \<and>\<^sub>p vs) \<cdot> us' = us" and "(us \<and>\<^sub>p vs) \<cdot> vs' = vs" and
    "us' \<noteq> \<epsilon>" and "vs' \<noteq> \<epsilon>" and "hd us' \<noteq> hd vs'"
proof -
  obtain us' vs' where us: "(us \<and>\<^sub>p vs) \<cdot> us' = us" and vs: "(us \<and>\<^sub>p vs) \<cdot> vs' = vs"
    using prefixE[OF lcp_pref prefixE[OF lcp_pref']]
    unfolding eq_commute[of "x\<cdot>y" for x y].
  with \<open>\<not> us \<bowtie> vs\<close> have "us' \<noteq> \<epsilon>" and "vs' \<noteq> \<epsilon>"
    unfolding prefix_comparable_def lcp_pref_conv[symmetric] lcp_sym[of vs]
    by fastforce+
  hence "us! \<^bold>|us \<and>\<^sub>p vs\<^bold>| = hd us'" and "vs! \<^bold>|us \<and>\<^sub>p vs\<^bold>| = hd vs'"
    using hd_lq_conv_nth[OF triv_spref, symmetric] unfolding lq_triv
    unfolding arg_cong[OF us[symmetric], of nth] arg_cong[OF vs[symmetric], of nth]
    by blast+
  from lcp_mismatch'[OF \<open>\<not> us \<bowtie> vs\<close>, unfolded this]
  have "hd us' \<noteq> hd vs'".
  from that[OF us vs \<open>us' \<noteq> \<epsilon>\<close> \<open>vs' \<noteq> \<epsilon>\<close> this]
  show thesis.
qed

lemma lcp_mismatch_lq: assumes "\<not> u \<bowtie> v"
  shows
  "(u \<and>\<^sub>p v)\<inverse>\<^sup>>u \<noteq> \<epsilon>" and
  "(u \<and>\<^sub>p v)\<inverse>\<^sup>>v \<noteq> \<epsilon>" and
  "hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>u) \<noteq> hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>v)"
proof-
  from lcp_mismatchE[OF assms]
  obtain su sv where "(u \<and>\<^sub>p v) \<cdot> su = u" and
      "(u \<and>\<^sub>p v) \<cdot> sv = v" and "su \<noteq> \<epsilon>" and "sv \<noteq> \<epsilon>" and "hd su \<noteq> hd sv".
  thus "(u \<and>\<^sub>p v)\<inverse>\<^sup>>u \<noteq> \<epsilon>" and "(u \<and>\<^sub>p v)\<inverse>\<^sup>>v \<noteq> \<epsilon>" and "hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>u) \<noteq> hd ((u \<and>\<^sub>p v)\<inverse>\<^sup>>v)"
    using lqI[OF \<open>(u \<and>\<^sub>p v) \<cdot> su = u\<close>] lqI[OF \<open>(u \<and>\<^sub>p v) \<cdot> sv = v\<close>] by blast+
qed

lemma lcp_ext_left: "(z \<cdot> u) \<and>\<^sub>p (z \<cdot> v) = z \<cdot> (u \<and>\<^sub>p v)"
  by (induct z) auto

lemma lcp_first_letters: "u!0 \<noteq> v!0 \<Longrightarrow> u \<and>\<^sub>p v = \<epsilon>"
  by (induct u v rule: list_induct2') auto

lemma lcp_first_mismatch: "a \<noteq> b \<Longrightarrow> w \<cdot> [a] \<cdot> u \<and>\<^sub>p w \<cdot> [b] \<cdot> v  = w"
  by (simp add: lcp_ext_left)

lemma lcp_first_mismatch': "a \<noteq> b \<Longrightarrow> u \<cdot> [a] \<and>\<^sub>p u \<cdot> [b] = u"
  using lcp_first_mismatch[of a b u \<epsilon> \<epsilon>] by simp

lemma lcp_mismatch_eq_len: assumes "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|" "x \<noteq> y" shows "u \<cdot> [x] \<and>\<^sub>p v \<cdot> [y] = u \<and>\<^sub>p v"
  using lcp_self lcp_first_mismatch'[OF \<open>x \<noteq> y\<close>] lcp_same_len[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close>]
  by (cases "u = v") auto

lemma lcp_first_mismatch_pref: assumes "p \<cdot> [a] \<le>p u" and "p \<cdot> [b] \<le>p v" and "a \<noteq> b"
  shows "u \<and>\<^sub>p v = p"
  using assms(1-2) lcp_first_mismatch[OF \<open>a \<noteq> b\<close>]
  unfolding  prefix_def rassoc by blast

lemma lcp_append_monotone: "u \<and>\<^sub>p x \<le>p (u \<cdot> v) \<and>\<^sub>p (x \<cdot> y)"
  by (simp add: lcp.mono)

lemma lcp_distinct_hd: "hd u \<noteq> hd v \<Longrightarrow> u \<and>\<^sub>p v = \<epsilon>"
  using pref_hd_eq'[OF lcp_pref lcp_pref'] by blast

lemma nemp_lcp_distinct_hd: assumes "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" and "u \<and>\<^sub>p v = \<epsilon>"
  shows "hd u \<noteq> hd v"
proof
  assume "hd u = hd v"
  from lcp_ext_left[of "[hd u]" "tl u" "tl v",
       unfolded hd_tl[OF \<open>u \<noteq> \<epsilon>\<close>] hd_tl[OF \<open>v \<noteq> \<epsilon>\<close>, folded this]]
  show False
    using \<open>u \<and>\<^sub>p v = \<epsilon>\<close> by simp
qed

lemma lcp_lenI: assumes "i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|" and "take i u = take i v" and "u!i \<noteq> v!i"
  shows "i = \<^bold>|u \<and>\<^sub>p v\<^bold>|"
proof-
  have u: "take i u \<cdot> [u ! i] \<cdot> drop (Suc i) u = u"
    using \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close> id_take_nth_drop[of i u] by simp
  have v: "take i u \<cdot> [v ! i] \<cdot> drop (Suc i) v = v"
    using \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close>
    unfolding \<open>take i u = take i v\<close> using id_take_nth_drop[of i v] by force
  from lcp_first_mismatch[OF \<open>u!i \<noteq> v!i\<close>, of "take i u" "drop (Suc i) u" "drop (Suc i) v", unfolded u v]
  have "u \<and>\<^sub>p v = take i u".
  thus ?thesis
    using \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close> by auto
qed

lemma lcp_prefs: "\<^bold>|u \<cdot> w \<and>\<^sub>p v \<cdot> w'\<^bold>| < \<^bold>|u\<^bold>| \<Longrightarrow> \<^bold>|u \<cdot> w \<and>\<^sub>p v \<cdot> w'\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u \<and>\<^sub>p v = u \<cdot> w \<and>\<^sub>p v \<cdot> w'"
  by (induct u v rule: list_induct2') auto

lemma lcp_extend_eq: assumes "u \<le>p v" and "u' \<le>p v'" and
              "\<^bold>|v \<and>\<^sub>p v'\<^bold>| \<le> \<^bold>|u\<^bold>|" and "\<^bold>|v \<and>\<^sub>p v'\<^bold>| \<le> \<^bold>|u'\<^bold>|"
            shows "u \<and>\<^sub>p u' = v \<and>\<^sub>p v'"
proof-
  consider "\<^bold>|v \<and>\<^sub>p v'\<^bold>| = \<^bold>|u\<^bold>|" | "\<^bold>|v \<and>\<^sub>p v'\<^bold>| = \<^bold>|u'\<^bold>|" | "\<^bold>|v \<and>\<^sub>p v'\<^bold>| < \<^bold>|u\<^bold>| \<and> \<^bold>|v \<and>\<^sub>p v'\<^bold>| < \<^bold>|u'\<^bold>|"
    using assms(3-4) by force
  thus ?thesis
  proof (cases)
    assume "\<^bold>|v \<and>\<^sub>p v'\<^bold>| = \<^bold>|u\<^bold>|"
    from ruler_eq_len[OF longest_common_prefix_prefix1 \<open>u \<le>p v\<close> this]
    have "u \<le>p u'"
      using  prefix_length_prefix[OF longest_common_prefix_prefix2 assms(2,4)] by blast
    thus ?thesis
      unfolding \<open>v \<and>\<^sub>p v' = u\<close> lcp_pref_conv.
  next
    assume "\<^bold>|v \<and>\<^sub>p v'\<^bold>| = \<^bold>|u'\<^bold>|"
    from ruler_eq_len[OF longest_common_prefix_prefix2 \<open>u' \<le>p v'\<close> this]
    have "u' \<le>p u"
      using  prefix_length_prefix[OF longest_common_prefix_prefix1 assms(1,3)] by blast
    thus ?thesis
      unfolding \<open>v \<and>\<^sub>p v' = u'\<close>  lcp_pref_conv'.
  next
    assume "\<^bold>|v \<and>\<^sub>p v'\<^bold>| < \<^bold>|u\<^bold>| \<and> \<^bold>|v \<and>\<^sub>p v'\<^bold>| < \<^bold>|u'\<^bold>|"
    thus ?thesis
      using  lcp_prefs[of u "u\<inverse>\<^sup>>v" u' "u'\<inverse>\<^sup>>v'", unfolded lq_pref[OF \<open>u \<le>p v\<close>] lq_pref[OF \<open>u' \<le>p v'\<close>]]
      by blast
  qed
qed

lemma long_lcp_same: assumes "\<not> (u \<and>\<^sub>p v \<le>p w)" shows "u \<and>\<^sub>p w = v \<and>\<^sub>p w"
proof-
  have "v \<and>\<^sub>p w \<le>p u"
    using ruler[OF lcp_pref' lcp_pref', of u v w] assms unfolding lcp_sym[of v] by force
  have  "u \<and>\<^sub>p w \<le>p v"
    using ruler[OF lcp_pref lcp_pref, of u v w] assms by force
  show ?thesis
    unfolding prefix_order.eq_iff
    using \<open>v \<and>\<^sub>p w \<le>p u\<close> \<open>u \<and>\<^sub>p w \<le>p v\<close> by force
qed

lemma long_lcp_sameE: obtains "u \<and>\<^sub>p v \<le>p w" | "u \<and>\<^sub>p w = v \<and>\<^sub>p w"
  using long_lcp_same by blast

lemma ruler_spref_lcp: assumes "u \<and>\<^sub>p w <p v \<and>\<^sub>p w"
  shows "u \<and>\<^sub>p v = u \<and>\<^sub>p w"
proof-
  have "\<not> v \<and>\<^sub>p w \<le>p u"
    using prefix_order.leD[of "v \<and>\<^sub>p w" "u \<and>\<^sub>p w"] assms by force
  from long_lcp_same[OF this]
  show ?thesis
    unfolding lcp_sym[of u].
qed

subsection "Longest common prefix and prefix comparability"
find_theorems name:ruler
lemma lexord_cancel_right: "(u \<cdot> z, v \<cdot> w) \<in> lexord r \<Longrightarrow> \<not> u \<bowtie> v \<Longrightarrow> (u,v) \<in> lexord r"
  unfolding prefix_comparable_def
  by (induction rule: list_induct2') auto

lemma lcp_rulersE: assumes "r \<le>p s" and "r' \<le>p s'" obtains "r \<bowtie> r'" | "s \<and>\<^sub>p s' = r \<and>\<^sub>p r'"
  by (cases rule: lcp_ext_right[of _ _ _ "r\<inverse>\<^sup>>s" "r'\<inverse>\<^sup>>s'"]) (assumption, simp only: assms lq_pref)

lemma lcp_rulers: "r \<le>p s \<Longrightarrow> r' \<le>p s' \<Longrightarrow> (r \<bowtie> r' \<or>  s \<and>\<^sub>p s' = r \<and>\<^sub>p r')"
  by (cases rule: lcp_ext_right[of _ _ _ "r\<inverse>\<^sup>>s" "r'\<inverse>\<^sup>>s'"], blast) (meson lcp_rulersE)

lemma lcp_rulers': "w \<le>p r \<Longrightarrow> w' \<le>p s \<Longrightarrow> \<not> w \<bowtie> w' \<Longrightarrow> (r \<and>\<^sub>p s) = w \<and>\<^sub>p w'"
  using lcp_rulers by blast

lemma lcp_ruler: "r \<bowtie> w1 \<Longrightarrow> r \<bowtie> w2 \<Longrightarrow> \<not> w1 \<bowtie> w2 \<Longrightarrow> r \<le>p w1 \<and>\<^sub>p w2"
  unfolding prefix_comparable_def by (meson pref_pref_lcp pref_trans ruler)

lemma comp_monotone: "w \<bowtie> r  \<Longrightarrow> u \<le>p w \<Longrightarrow> u \<bowtie> r"
  using pref_compI1[OF pref_trans] ruler' by (elim pref_compE)

lemma comp_monotone': "w \<bowtie> r  \<Longrightarrow> w \<and>\<^sub>p w' \<bowtie> r"
  using comp_monotone[OF _ lcp_pref].

lemma double_ruler_aux: assumes "w \<bowtie> r" and "w' \<bowtie> r'" and "\<not> r \<bowtie> r'" and "\<^bold>|w\<^bold>| \<le> \<^bold>|w'\<^bold>|"
  shows "w \<and>\<^sub>p w' = take \<^bold>|w\<^bold>| (r \<and>\<^sub>p r')"
proof-
  have pref1: "w \<and>\<^sub>p w' \<le>p r \<and>\<^sub>p r'"
    using comp_monotone'[OF \<open>w' \<bowtie> r'\<close>]  lcp_ruler[OF comp_monotone'[OF \<open>w \<bowtie> r\<close>] _ \<open>\<not> r \<bowtie> r'\<close>]
    unfolding lcp_sym[of w'] by simp
  show ?thesis
  proof (cases)
    assume "w \<bowtie> w'"
    hence "w \<and>\<^sub>p w' = w"
      using \<open>\<^bold>|w\<^bold>| \<le> \<^bold>|w'\<^bold>|\<close>
      by (simp add: comp_shorter lcp.absorb1)
    show ?thesis
      using pref_take[OF pref1, symmetric] unfolding \<open>w \<and>\<^sub>p w' = w\<close>.
  next
    assume "\<not> w \<bowtie> w'"
    hence pref2: "r \<and>\<^sub>p r' \<le>p w \<and>\<^sub>p w'"
      using comp_monotone'[OF \<open>w' \<bowtie> r'\<close>[symmetric]]  lcp_ruler[OF comp_monotone'[OF \<open>w \<bowtie> r\<close>[symmetric]] _ \<open>\<not> w \<bowtie> w'\<close>]
      unfolding lcp_sym[of r'] by simp
    hence "w \<and>\<^sub>p w' = r \<and>\<^sub>p r'"
      using pref1 pref_antisym by blast
    then show ?thesis
      using lcp_take len_take2 take_all_iff by metis
  qed
qed

lemma double_ruler: assumes "w \<bowtie> r" and "w' \<bowtie> r'" and "\<not> r \<bowtie> r'"
  shows "w \<and>\<^sub>p w' = take (min \<^bold>|w\<^bold>| \<^bold>|w'\<^bold>|) (r \<and>\<^sub>p r')"
  by (cases "\<^bold>|w\<^bold>|" "\<^bold>|w'\<^bold>|" rule: le_cases)
  (use double_ruler_aux[OF assms] double_ruler_aux[OF assms(2,1) assms(3)[symmetric], unfolded lcp_sym[of r'] lcp_sym[of w']]
  in linarith)+

hide_fact double_ruler_aux

lemmas pref_lcp_iff = lcp.bounded_iff

lemma pref_comp_ruler: assumes "w \<bowtie> u \<cdot> [x]" and "w \<bowtie> v \<cdot> [y]" and "x \<noteq> y" and "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
  shows "w \<le>p u \<and> w \<le>p v"
  using double_ruler[OF \<open>w \<bowtie> u \<cdot> [x]\<close> \<open>w \<bowtie> v \<cdot> [y]\<close> mismatch_incopm[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close> \<open>x \<noteq> y\<close>]]
   take_is_prefix  lcp_self lcp_mismatch_eq_len[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close> \<open>x \<noteq> y\<close>] pref_lcp_iff by metis

lemma  comp_per_partes:
  shows "(u \<bowtie> w \<and> v \<bowtie> u\<inverse>\<^sup>>w) \<longleftrightarrow> u \<cdot> v \<bowtie> w"
proof
  assume "u \<cdot> v \<bowtie> w"
  from comp_monotone[OF _ triv_pref, OF this] append_comp_lq[OF this]
  show  "u \<bowtie> w \<and> v \<bowtie> u\<inverse>\<^sup>>w"
    by blast
next
  assume c2: "u \<bowtie> w \<and> v \<bowtie> u\<inverse>\<^sup>>w"
  hence "u \<cdot> v \<bowtie> u \<cdot> u\<inverse>\<^sup>>w"
    unfolding comp_cancel by blast
  show "u \<cdot> v \<bowtie> w"
    by (rule pref_compE[OF conjunct1[OF c2]], use \<open>u \<cdot> v \<bowtie> u \<cdot> u\<inverse>\<^sup>>w\<close> in force,blast)
qed

lemmas  scomp_per_partes = comp_per_partes[reversed]


subsection \<open>Longest common suffix\<close>

definition longest_common_suffix ("_ \<and>\<^sub>s _ " [61,62] 64)
  where
    "longest_common_suffix u v \<equiv> rev (rev u \<and>\<^sub>p rev v)"

lemma lcs_lcp [reversal_rule]: "rev u \<and>\<^sub>p rev v = rev (u \<and>\<^sub>s v)"
  unfolding longest_common_suffix_def rev_rev_ident..

lemmas lcs_simp = lcp_simps[reversed] and
       lcs_sym = lcp_sym[reversed] and
       lcs_suf = lcp_pref[reversed] and
       lcs_suf' = lcp_pref'[reversed] and
       suf_suf_lcs = pref_pref_lcp[reversed] and
       suf_non_suf_lcs_suf = pref_non_pref_lcp_pref[reversed] and
       lcs_drop_eq = lcp_take_eq[reversed] and
       lcs_take = lcp_take[reversed] and
       lcs_take' = lcp_take'[reversed] and
       lcs_suf_conv = lcp_pref_conv[reversed] and
       lcs_suf_conv' = lcp_pref_conv'[reversed] and
       lcs_per_root = lcp_per_root[reversed] and
       lcs_per_root' = lcp_per_root'[reversed] and
       suf_lcs_suf = pref_lcp_pref[reversed] and
       suf_lcs_suf' = pref_lcp_pref'[reversed] and
       lcs_self[simp] = lcp_self[reversed] and
       lcs_eq_len = lcp_eq_len[reversed] and
       lcs_len = lcp_len[reversed] and
       lcs_len' = lcp_len'[reversed] and
       suf_incomp_lcs_len = incomp_lcp_len[reversed] and
       lcs_ext_left_conv = lcp_ext_right_conv[reversed] and
       lcs_ext_left [case_names comp non_comp] = lcp_ext_right[reversed] and
       lcs_same_len = lcp_same_len[reversed] and
       lcs_mismatch = lcp_mismatch[reversed] and
       lcs_mismatch' = lcp_mismatch'[reversed] and
       lcs_mismatchE = lcp_mismatchE[reversed] and
       lcs_mismatch_rq = lcp_mismatch_lq[reversed] and
       lcs_ext_right = lcp_ext_left[reversed] and
       lcs_first_mismatch = lcp_first_mismatch[reversed, unfolded rassoc] and
       lcs_first_mismatch' = lcp_first_mismatch'[reversed, unfolded rassoc] and
       lcs_mismatch_eq_len = lcp_mismatch_eq_len[reversed] and
       lcs_first_mismatch_suf = lcp_first_mismatch_pref[reversed] and
       lcs_rulers = lcp_rulers[reversed] and
       lcs_rulers' = lcp_rulers'[reversed] and
       suf_suf_lcs' = lcp.mono[reversed] and
       lcs_distinct_last = lcp_distinct_hd[reversed] and
       lcs_lenI = lcp_lenI[reversed] and
       lcs_sufs = lcp_prefs[reversed]

lemmas lcs_ruler = lcp_ruler[reversed] and
       suf_comp_monotone = comp_monotone[reversed] and
       suf_comp_monotone' = comp_monotone'[reversed] and
       double_ruler_suf = double_ruler[reversed] and
       suf_lcs_iff = pref_lcp_iff[reversed] and
       suf_comp_ruler = pref_comp_ruler[reversed]

section "Mismatch"

text \<open>The first pair of letters on which two words/lists disagree\<close>

function mismatch_pair :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a)" where
  "mismatch_pair \<epsilon> v = (\<epsilon>!0, v!0)" |
  "mismatch_pair v \<epsilon> = (v!0, \<epsilon>!0)" |
  "mismatch_pair (a#u) (b#v) = (if a=b then mismatch_pair u v else (a,b))"
  using shuffles.cases by blast+
termination
  by (relation "measure (\<lambda> (t,s). length t)", simp_all)

text \<open>Alternatively, mismatch pair may be defined using the longest common prefix as follows.\<close>

lemma mismatch_pair_lcp: "mismatch_pair u v = (u!\<^bold>|u\<and>\<^sub>pv\<^bold>|,v!\<^bold>|u\<and>\<^sub>pv\<^bold>|)"
  by (induction u v rule: mismatch_pair.induct) simp_all

text \<open>For incomparable words the pair is out of diagonal.\<close>

lemma incomp_neq: "\<not> u \<bowtie> v \<Longrightarrow> (mismatch_pair u v) \<notin> Id"
  unfolding mismatch_pair_lcp by (simp add: lcp_mismatch')

lemma mismatch_ext_left: "\<not> u \<bowtie> v \<Longrightarrow> mismatch_pair u v = mismatch_pair (p\<cdot>u) (p\<cdot>v)"
  unfolding mismatch_pair_lcp by (simp add: lcp_ext_left)

lemma mismatch_ext_right: assumes  "\<not> u \<bowtie> v"
  shows "mismatch_pair u v = mismatch_pair (u\<cdot>z) (v\<cdot>w)"
proof-
  have less1: "\<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|u\<^bold>|" and less2: "\<^bold>|v \<and>\<^sub>p u\<^bold>| < \<^bold>|v\<^bold>|"
    using lcp_len'[of u v] lcp_len'[of v u] assms  by auto
  show ?thesis
    unfolding mismatch_pair_lcp unfolding pref_index[OF triv_pref less1, of z]  pref_index[OF triv_pref less2, of w, unfolded lcp_sym[of v]]
    using assms lcp_ext_right[of u v _ z w] by metis
qed

lemma mismatchI: "\<not> u \<bowtie> v \<Longrightarrow> i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>| \<Longrightarrow> take i u = take i v \<Longrightarrow> u!i \<noteq> v!i
   \<Longrightarrow> mismatch_pair u v = (u!i,v!i)"
  unfolding mismatch_pair_lcp using lcp_lenI by blast

text \<open>For incomparable words, the mismatch letters work in a similar way as the lexicographic order\<close>

lemma mismatch_lexord: assumes "\<not> u \<bowtie> v" and "mismatch_pair u v \<in> r"
  shows "(u,v) \<in> lexord r"
  unfolding lexord_take_index_conv mismatch_pair_lcp
  using  \<open>mismatch_pair u v \<in> r\<close>[unfolded mismatch_pair_lcp]
    incomp_lcp_len[OF assms(1)] lcp_take_eq by blast

text \<open>However, the equivalence requires r to be irreflexive.
(Due to the definition of lexord which is designed for irreflexive relations.)\<close>

lemma lexord_mismatch: assumes "\<not> u \<bowtie> v" and "irrefl r"
  shows "mismatch_pair u v \<in> r \<longleftrightarrow> (u,v) \<in> lexord r"
proof
  assume "(u,v) \<in> lexord r"
  obtain i where  "i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|" and  "take i u = take i v" and "(u ! i, v ! i) \<in> r"
    using \<open>(u,v) \<in> lexord r\<close>[unfolded lexord_take_index_conv] \<open>\<not> u \<bowtie> v\<close> pref_take_conv by blast
  have "u!i \<noteq> v!i"
    using  \<open>irrefl r\<close>[unfolded irrefl_def] \<open>(u ! i, v ! i) \<in> r\<close> by fastforce
  from \<open>(u ! i, v ! i) \<in> r\<close>[folded mismatchI[OF \<open>\<not> u \<bowtie> v\<close> \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close> \<open>take i u = take i v\<close> \<open>u!i \<noteq> v!i\<close>]]
  show  "mismatch_pair u v \<in> r".
next
  from mismatch_lexord[OF \<open>\<not> u \<bowtie> v\<close>]
  show "mismatch_pair u v \<in> r \<Longrightarrow> (u, v) \<in> lexord r".
qed

section "Factor properties"

lemmas [simp] = sublist_Cons_right

lemma rev_fac[reversal_rule]: "rev u \<le>f rev v \<longleftrightarrow> u \<le>f v"
  using Sublist.sublist_rev.

lemma fac_pref: "u \<le>f v \<equiv> \<exists> p. p \<cdot> u \<le>p v"
  by (simp add: prefix_def fac_def)

lemma fac_pref_suf: "u \<le>f v \<Longrightarrow> \<exists> p. p \<le>p v \<and> u \<le>s p"
  using sublist_altdef by blast

lemma pref_suf_fac: "r \<le>p v \<Longrightarrow> u \<le>s r \<Longrightarrow> u \<le>f v"
  using sublist_altdef by blast

lemmas
  fac_suf = fac_pref[reversed] and
  fac_suf_pref = fac_pref_suf[reversed] and
  suf_pref_fac = pref_suf_fac[reversed]

lemma suf_pref_eq: "s \<le>s p \<Longrightarrow> p \<le>p s \<Longrightarrow> p = s"
  using sublist_order.order.eq_iff by blast

lemma fac_triv: "p\<cdot>x\<cdot>q = x \<Longrightarrow> p = \<epsilon>"
  using long_pref[OF prefI suf_len'] unfolding append_self_conv2 rassoc.

lemma fac_triv': "p\<cdot>x\<cdot>q = x \<Longrightarrow> q = \<epsilon>"
  using fac_triv[reversed] unfolding rassoc.

lemmas
  suf_fac = suffix_imp_sublist and
  pref_fac = prefix_imp_sublist

lemma fac_ConsE: assumes "u \<le>f (a#v)"
  obtains "u \<le>p (a#v)" | "u \<le>f v"
  using assms unfolding sublist_Cons_right
  by blast

lemmas
  fac_snocE = fac_ConsE[reversed]

lemma fac_elim_suf: assumes "f \<le>f m\<cdot>s" "\<not> f \<le>f s"
  shows "f \<le>f m\<cdot>(take (\<^bold>|f\<^bold>|-1) s)"
  using assms
proof(induction s rule:rev_induct)
  case (snoc s ss)
  have "\<not> f \<le>f ss"
    using \<open>\<not> f \<le>f ss \<cdot> [s]\<close>[unfolded sublist_append] by blast

  show ?case
  proof(cases)
    assume  "f \<le>f m \<cdot> ss"
    hence "f \<le>f m \<cdot> take (\<^bold>|f\<^bold>| - 1) ss"
      using \<open>\<not> f \<le>f ss\<close> snoc.IH by blast
    then show ?thesis
      unfolding take_append lassoc using append_assoc sublist_append by metis
  next
    assume "\<not> f \<le>f m \<cdot> ss"
    hence "f \<le>s m \<cdot> ss \<cdot> [s]"
      using  snoc.prems(1)[unfolded lassoc sublist_snoc, unfolded rassoc] by blast
    from suf_prod_le[OF this, THEN suffix_imp_sublist] \<open>\<not> f \<le>f ss \<cdot> [s]\<close>
    have "\<^bold>|ss \<cdot> [s]\<^bold>| < \<^bold>|f\<^bold>|"
      by linarith
    from this Suc_less_iff_Suc_le length_append_singleton[of ss s]
    show ?thesis
      using snoc.prems(1) take_all_iff by metis
  qed
qed auto

lemmas fac_elim_pref = fac_elim_suf[reversed]

lemma fac_elim: assumes "f \<le>f p\<cdot>m\<cdot>s" and  "\<not> f \<le>f p" and "\<not> f \<le>f s"
  shows "f \<le>f (drop (\<^bold>|p\<^bold>| - (\<^bold>|f\<^bold>| - 1)) p) \<cdot> m \<cdot> (take (\<^bold>|f\<^bold>|-1) s)"
  using  fac_elim_suf[OF fac_elim_pref[OF \<open>f \<le>f p\<cdot>m\<cdot>s\<close>, unfolded lassoc], unfolded rassoc, OF assms(2-3)].

lemma fac_ext_pref: "u \<le>f w \<Longrightarrow> u \<le>f p \<cdot> w"
  by (meson sublist_append)

lemma fac_ext_suf: "u \<le>f w \<Longrightarrow> u \<le>f w \<cdot> s"
  by (meson sublist_append)

lemma fac_ext: "u \<le>f w \<Longrightarrow> u \<le>f p \<cdot> w \<cdot> s"
  by (meson fac_ext_pref fac_ext_suf)

lemma fac_ext_hd:"u \<le>f w \<Longrightarrow> u \<le>f a#w"
  by (metis sublist_Cons_right)

lemma card_switch_fac: assumes "2 \<le> card (set ws)"
  obtains c d where "c \<noteq> d" and  "[c,d] \<le>f ws"
  using assms
proof (induct ws, force)
  case (Cons a ws)
  then show ?case
  proof (cases)
    assume "2 \<le> card (set ws)"
    from Cons.hyps[OF _ this] Cons.prems(1) fac_ext_hd
    show thesis by metis
  next
    assume "\<not> 2 \<le> card (set ws)"
    have "ws \<noteq> \<epsilon>"
      using \<open>2 \<le> card (set (a # ws))\<close>  by force
    hence "a = hd ws \<Longrightarrow> set (a # ws) = set ws"
      using hd_Cons_tl[OF \<open>ws \<noteq> \<epsilon>\<close>] by force
    hence "a \<noteq> hd ws"
      using \<open>2 \<le> card (set (a # ws))\<close> \<open>\<not> 2 \<le> card (set ws)\<close>  by force
    from Cons.prems(1)[OF this]
    show thesis
      using  Cons_eq_appendI[OF _ hd_tl[OF \<open>ws \<noteq> \<epsilon>\<close>, symmetric]] sublist_append_rightI by blast
  qed
qed

lemma fac_overlap_len: assumes "u \<le>f x \<cdot> y \<cdot> z" and "\<^bold>|u\<^bold>| \<le> \<^bold>|y\<^bold>|"
  shows "u \<le>f x \<cdot> y \<or> u \<le>f y \<cdot> z"
proof-
  obtain s p where eq: "x \<cdot> y \<cdot> z = p \<cdot> u \<cdot> s"
    using \<open>u \<le>f x \<cdot> y \<cdot> z\<close> unfolding fac_def by blast
  show ?thesis
  proof (rule le_cases)
    assume "\<^bold>|p\<^bold>| \<le> \<^bold>|x\<^bold>|"
    from add_le_mono[OF this \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|y\<^bold>|\<close>]
    have "\<^bold>|p \<cdot> u\<^bold>| \<le> \<^bold>|x \<cdot> y\<^bold>|"
      unfolding lenmorph.
    from eq_le_pref[OF eq[symmetric, unfolded lassoc] this]
    have "u \<le>f x \<cdot> y"
      using fac_pref by blast
    thus ?thesis by blast
  next
    assume "\<^bold>|x\<^bold>| \<le> \<^bold>|p\<^bold>|"
    from eqd[OF eq this]
    show "u \<le>f x \<cdot> y \<or> u \<le>f y \<cdot> z"
      unfolding fac_def by metis
  qed
qed

section "Power and its properties"

text\<open>Word powers are often investigated in Combinatorics on Words.
We thus interpret words as @{term monoid_mult} and adopt a notation for the word power.
\<close>


primrec list_power :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"  (infixr "\<^sup>@" 80)
  where
    pow_0: "u \<^sup>@ 0 = \<epsilon>"
  | pow_Suc: "u \<^sup>@ Suc n = u \<cdot> u \<^sup>@ n"

term power.power








context
begin

interpretation monoid_mult "\<epsilon>" "append"
  rewrites "power u n = u\<^sup>@n"
proof-
  show "class.monoid_mult \<epsilon> (\<cdot>)"
    by (unfold_locales, simp_all)
  show "power.power \<epsilon> (\<cdot>) u n = u \<^sup>@ n"
    unfolding power.power_def list_power_def by blast
qed


\<comment> \<open>inherited power properties\<close>

lemma emp_pow_emp[simp]: "r = \<epsilon> \<Longrightarrow> r\<^sup>@n = \<epsilon>"
  by simp

lemma pow_pos:"0 < k \<Longrightarrow> a\<^sup>@k = a \<cdot> a\<^sup>@(k-1)"
  by (simp add: power_eq_if)

lemma pow_pos':"0 < k \<Longrightarrow> a\<^sup>@k = a\<^sup>@(k-1) \<cdot> a"
  using power_minus_mult by metis

lemma pow_diff: "k < n \<Longrightarrow> a\<^sup>@(n - k) = a \<cdot> a\<^sup>@(n-k-1)"
  by (rule pow_pos) simp

lemma pow_diff': "k < n \<Longrightarrow> a\<^sup>@(n - k) = a\<^sup>@(n-k-1) \<cdot> a"
  by (rule pow_pos') simp

lemmas pow_zero = power.power_0 and
  pow_one = power_Suc0_right and
  pow_1 = power_one_right and
  emp_pow[emp_simps] = power_one and
  pow_two[simp] = power2_eq_square and
  pow_Suc = power_Suc and
  pow_Suc' = power_Suc2 and
  pow_comm = power_commutes and
  add_exps = power_add and
  pow_eq_if_list = power_eq_if and
  pow_mult = power_mult and
   comm_add_exp = power_commuting_commutes

lemma pow_rev_emp_conv[reversal_rule]: "power.power (rev \<epsilon>) (\<cdot>) = (\<^sup>@)"
      unfolding power.power_def list_power_def by simp

lemma pow_rev_map_rev_emp_conv [reversal_rule]: "power.power (rev (map rev  \<epsilon>)) (\<cdot>) = (\<^sup>@)"
    unfolding power.power_def list_power_def by simp
end

named_theorems exp_simps
lemmas [exp_simps]  = pow_zero pow_one emp_pow
                    numeral_nat less_eq_Suc_le neq0_conv pow_mult[symmetric]

named_theorems cow_simps
lemmas [cow_simps] = emp_simps exp_simps

\<comment> \<open>more power properties\<close>

lemma sing_Cons_to_pow: "[a, a] = [a] \<^sup>@ Suc (Suc 0)" "a # [a] \<^sup>@ k = [a] \<^sup>@ Suc k"
  by simp_all

lemma zero_exp: "n = 0 \<Longrightarrow> r\<^sup>@n = \<epsilon>"
  by simp

lemma nemp_pow: "t\<^sup>@m \<noteq> \<epsilon> \<Longrightarrow> 0 < m"
  using zero_exp by blast

lemma pow_nemp_pos[intro]: assumes "u = t\<^sup>@m" "u \<noteq> \<epsilon>" shows "0 < m"
  using nemp_pow[OF \<open>u \<noteq> \<epsilon>\<close>[unfolded \<open>u = t\<^sup>@m\<close>]].



lemma nemp_exp_pos[intro]: "w \<noteq> \<epsilon> \<Longrightarrow> r\<^sup>@k = w \<Longrightarrow> 0 < k"
  using nemp_pow by blast

lemma nemp_exp_pos'[intro]: "w \<noteq> \<epsilon> \<Longrightarrow> w = r\<^sup>@k \<Longrightarrow> 0 < k"
  using nemp_pow by blast

lemma nemp_pow_nemp[intro]: "t\<^sup>@m \<noteq> \<epsilon> \<Longrightarrow> t \<noteq> \<epsilon>"
  using emp_pow by auto

lemma sing_pow_nth:"i < m \<Longrightarrow> ([a]\<^sup>@m) ! i = a"
  by (induct i m rule: diff_induct) auto

lemma pow_is_concat_replicate: "u\<^sup>@n = concat (replicate n u)"
  by (induct n) auto

lemma pow_slide: "u \<cdot> (v \<cdot> u)\<^sup>@n  \<cdot> v = (u \<cdot> v)\<^sup>@(Suc n)"
  by (induct n) simp+

lemma hd_pow: assumes "0 < n" shows "hd(u\<^sup>@n) = hd u"
  unfolding pow_pos[OF \<open>0 < n\<close>] using  hd_append2 by (cases "u = \<epsilon>", simp_all)

lemma pop_pow: "m \<le> k \<Longrightarrow>u\<^sup>@m \<cdot> u\<^sup>@(k-m) =  u\<^sup>@k"
  using le_add_diff_inverse add_exps  by metis

lemma pop_pow_cancel: "u\<^sup>@k \<cdot> v = u\<^sup>@m \<cdot> w \<Longrightarrow> m \<le> k \<Longrightarrow> u\<^sup>@(k-m) \<cdot> v = w"
  using  lassoc pop_pow[of m k u] same_append_eq[of "u\<^sup>@m" "u\<^sup>@(k-m)\<cdot>v" w, unfolded lassoc] by argo

lemma pows_comm: "t\<^sup>@k \<cdot> t\<^sup>@m = t\<^sup>@m \<cdot> t\<^sup>@k"
  unfolding add_exps[symmetric] add.commute[of k]..

lemma comm_add_exps: assumes "r \<cdot> u = u \<cdot> r" shows "r\<^sup>@m \<cdot> u\<^sup>@k = u\<^sup>@k \<cdot> r\<^sup>@m"
  using comm_add_exp[OF comm_add_exp[OF assms, symmetric], symmetric].

lemma rev_pow: "rev (x\<^sup>@m) = (rev x)\<^sup>@m"
  by (induct m, simp, simp add: pow_comm)

lemma pows_comp: "x\<^sup>@i \<bowtie> x\<^sup>@j"
  unfolding prefix_comparable_def using ruler_eqE[OF pows_comm, of x i j] by blast

lemmas pows_suf_comp = pows_comp[reversed, folded rev_pow suffix_comparable_def]

lemmas [reversal_rule] = rev_pow[symmetric]

lemmas pow_eq_if_list' = pow_eq_if_list[reversed] and
  pop_pow_one' = pow_pos[reversed] and
  pop_pow' = pop_pow[reversed] and
  pop_pow_cancel' = pop_pow_cancel[reversed]

lemma pow_len:  "\<^bold>|u\<^sup>@k\<^bold>| = k * \<^bold>|u\<^bold>|"
  by (induct k) simp+

lemma pow_set: "set (w\<^sup>@Suc k) = set w"
  by (induction k, simp_all)

lemma eq_pow_exp[simp]: assumes "u \<noteq> \<epsilon>" shows "u\<^sup>@k = u\<^sup>@m \<longleftrightarrow> k = m"
proof
  assume "k = m" thus "u\<^sup>@k = u\<^sup>@m" by simp
next
  assume "u\<^sup>@k = u\<^sup>@m"
  from lenarg[OF this, unfolded pow_len mult_cancel2]
  show "k = m"
    using \<open>u \<noteq> \<epsilon>\<close>[folded length_0_conv] by blast
qed

lemma emp_pow_pos_emp [intro]: assumes "v\<^sup>@j = \<epsilon>" "0 < j" shows "v = \<epsilon>"
  using pow_pos[OF \<open>0 < j\<close>, of v, unfolded \<open>v\<^sup>@j = \<epsilon>\<close>] by blast

lemma nemp_emp_pow: assumes "u \<noteq> \<epsilon>" shows "u\<^sup>@m = \<epsilon> \<longleftrightarrow> m = 0"
  using  eq_pow_exp[OF assms, of m 0, unfolded pow_zero].

lemma nemp_pow_nemp_pos_conv: assumes "u \<noteq> \<epsilon>" shows "u\<^sup>@m \<noteq> \<epsilon> \<longleftrightarrow> 0 < m"
  unfolding nemp_emp_pow[OF assms] by blast

lemma nemp_Suc_pow_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> u\<^sup>@Suc k \<noteq> \<epsilon>"
  by simp

lemma nonzero_pow_emp: "0 < m \<Longrightarrow> u\<^sup>@m = \<epsilon> \<longleftrightarrow>  u = \<epsilon>"
  by (cases "u = \<epsilon>", simp)
  (use nemp_emp_pow[of u m] in blast)

lemma pow_eq_eq:
  assumes "u\<^sup>@k = v\<^sup>@k" and "0 < k"
  shows "u = v"
proof-
  have "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
    using lenarg[OF \<open>u\<^sup>@k = v\<^sup>@k\<close>, unfolded pow_len] \<open>0 < k\<close> by simp
  from eqd_eq[of u "u\<^sup>@(k-1)" v "v\<^sup>@(k-1)", OF _ this]
  show ?thesis
    using \<open>u\<^sup>@k = v\<^sup>@k\<close> unfolding pow_pos[OF \<open>0 < k\<close>] by blast
qed

lemma Suc_pow_eq_eq[elim]: "u\<^sup>@Suc k = v\<^sup>@Suc k \<Longrightarrow> u = v"
  using pow_eq_eq by blast

lemma map_pow[simp]: "map f (r\<^sup>@k) = (map f r)\<^sup>@k"
  by (induct k, simp_all)

lemmas [reversal_rule] = map_pow[symmetric]

lemma concat_pow[simp]: "concat (r\<^sup>@k) = (concat r)\<^sup>@k"
  by (induct k, simp_all)

lemma concat_sing_pow[simp]: "concat ([a]\<^sup>@k) = a\<^sup>@k"
  unfolding concat_pow concat_sing'..

lemma sing_pow_empty: "[a]\<^sup>@n = \<epsilon> \<longleftrightarrow> n = 0"
  using nemp_emp_pow[OF list.simps(3), of _ \<epsilon>].

lemma sing_pow_lists: "a \<in> A \<Longrightarrow> [a]\<^sup>@n \<in> lists A"
  by (induct n, auto)

lemma long_pow: "r \<noteq> \<epsilon> \<Longrightarrow> m \<le> \<^bold>|r\<^sup>@m\<^bold>|"
  unfolding pow_len[of r m] using nemp_le_len[of r] by simp

lemma long_pow_exp': "r \<noteq> \<epsilon> \<Longrightarrow> m < \<^bold>|r\<^sup>@(Suc m)\<^bold>|"
  using Suc_le_lessD long_pow by blast

lemma long_pow_expE: assumes "r \<noteq> \<epsilon>" obtains n where  "m \<le> \<^bold>|r\<^sup>@Suc n\<^bold>|"
  using long_pow_exp'[OF \<open>r \<noteq> \<epsilon>\<close>] nat_less_le by blast

lemma pref_pow_ext: "x \<le>p r\<^sup>@k \<Longrightarrow> x \<le>p r\<^sup>@Suc k"
  using pref_trans[OF _ prefI[OF pow_Suc'[symmetric]]].

lemma pref_pow_ext': "u \<le>p r\<^sup>@k \<Longrightarrow> u \<le>p r \<cdot> r\<^sup>@k"
  using pref_pow_ext[unfolded pow_Suc].

lemma pref_pow_root_ext: "x \<le>p r\<^sup>@k \<Longrightarrow> r \<cdot> x \<le>p r\<^sup>@Suc k"
  by simp

lemma pref_prod_root: "u \<le>p r\<^sup>@k \<Longrightarrow> u \<le>p r \<cdot> u"
  using pref_pow_ext'[THEN pref_prod_pref].

lemma le_exps_pref:  "k \<le> l \<Longrightarrow> r\<^sup>@k \<le>p r\<^sup>@l"
  using leI pop_pow[of k l r] by blast

lemma pref_exp_le: assumes "u \<noteq> \<epsilon>" "u\<^sup>@m \<le>p u\<^sup>@n" shows "m \<le> n"
  using mult_cancel_le[OF nemp_len[OF \<open>u \<noteq> \<epsilon>\<close>], of m n]
    prefix_length_le[OF \<open>u\<^sup>@m \<le>p u\<^sup>@n\<close>, unfolded pow_len[of u m] pow_len[of u n]]
  by blast

lemma sing_exp_pref_iff: assumes "a \<noteq> b"
  shows "[a]\<^sup>@i \<le>p [a]\<^sup>@k\<cdot>[b] \<cdot> w \<longleftrightarrow> i \<le> k"
proof
  assume "i \<le> k"
  thus "[a]\<^sup>@i \<le>p [a]\<^sup>@k\<cdot>[b] \<cdot> w"
    using pref_ext[OF le_exps_pref[OF \<open>i \<le> k\<close>]] by blast
next
  have "\<not> [a]\<^sup>@i \<le>p [a]\<^sup>@k\<cdot>[b] \<cdot> w" if "\<not> i \<le> k"
  proof (rule notI)
  assume "[a]\<^sup>@i \<le>p [a]\<^sup>@k\<cdot>[b] \<cdot> w"
  hence "k < i" and "0 < i - k" using \<open>\<not> i \<le> k\<close> by force+
  from pop_pow[OF less_imp_le, OF this(1)]
  have "[a]\<^sup>@k \<cdot> [a]\<^sup>@(i - k) = [a]\<^sup>@i".
  from \<open>[a]\<^sup>@i \<le>p [a]\<^sup>@k\<cdot>[b] \<cdot> w\<close>[folded this, unfolded pref_cancel_conv
       pow_pos[OF \<open>0 < i - k\<close>]]
  show False
    using \<open>a \<noteq> b\<close> by simp
 qed
 thus "[a] \<^sup>@ i \<le>p [a] \<^sup>@ k \<cdot> [b] \<cdot> w \<Longrightarrow> i \<le> k"
   by blast
qed

lemmas
  suf_pow_ext = pref_pow_ext[reversed] and
  suf_pow_ext'= pref_pow_ext'[reversed] and
  suf_pow_root_ext = pref_pow_root_ext[reversed] and
  suf_prod_root = pref_prod_root[reversed] and
  suf_exps_pow = le_exps_pref[reversed] and
  suf_exp_le = pref_exp_le[reversed] and
  sing_exp_suf_iff = sing_exp_pref_iff[reversed]

lemma comm_common_power: assumes "r \<cdot> u = u \<cdot> r" shows "r\<^sup>@\<^bold>|u\<^bold>| = u\<^sup>@\<^bold>|r\<^bold>|"
  using eqd_eq[OF comm_add_exps[OF \<open>r \<cdot> u = u \<cdot> r\<close>], of "\<^bold>|u\<^bold>|" "\<^bold>|r\<^bold>|"]
  unfolding pow_len by fastforce

lemma one_generated_list_power: "u \<in> lists {x} \<Longrightarrow> \<exists>k. concat u = x\<^sup>@k"
  by(induction u rule: lists.induct, unfold concat.simps(1), use pow_zero[of x, symmetric] in fast,
        unfold concat.simps(2))
  (use pow_Suc[symmetric, of x] singletonD in metis)

lemma pow_lists: assumes "0 < k" shows "u\<^sup>@k \<in> lists B \<Longrightarrow> u \<in> lists B"
  unfolding pow_Suc[of u "k-1", unfolded Suc_minus_pos[OF \<open>0 < k\<close>]] by simp

lemma concat_morph_power: "xs \<in> lists B \<Longrightarrow> xs = ts\<^sup>@k \<Longrightarrow> concat ts\<^sup>@k = concat xs"
  by (induct k arbitrary: xs ts) simp_all


lemma per_exp_pref: "u \<le>p r \<cdot> u \<Longrightarrow> u \<le>p r\<^sup>@k \<cdot> u"
proof(induct k)
  case (Suc k) show ?case
    unfolding pow_Suc rassoc
    using Suc.hyps Suc.prems pref_prolong by blast
qed simp

lemmas
    per_exp_suf = per_exp_pref[reversed]

lemma hd_sing_pow: "k \<noteq> 0 \<Longrightarrow> hd ([a]\<^sup>@k) = a"
  by (induction k) simp+


lemma sing_pref_comp_mismatch:
  assumes "b \<noteq> a" and "c \<noteq> a" and "[a]\<^sup>@k \<cdot> [b] \<bowtie> [a]\<^sup>@l \<cdot> [c]"
  shows "k = l \<and> b = c"
proof
  show "k = l"
    using assms
  proof (induction k l rule: diff_induct)
    show " b \<noteq> a \<Longrightarrow> c \<noteq> a \<Longrightarrow> [a] \<^sup>@ x \<cdot> [b] \<bowtie> [a] \<^sup>@ 0 \<cdot> [c] \<Longrightarrow> x = 0" for x
      by (rule ccontr, elim not0_SucE) fastforce
  qed (simp add:prefix_comparable_def)+
  show "b = c"
    using assms(3) unfolding \<open>k = l\<close> by auto
qed

lemma sing_pref_comp_lcp: assumes "r \<noteq> s" and "a \<noteq> b" and "a \<noteq> c"
  shows  "[a]\<^sup>@r \<cdot> [b] \<cdot> u \<and>\<^sub>p [a]\<^sup>@s \<cdot> [c] \<cdot> v = [a]\<^sup>@(min r s)"
proof-
  have "r \<noteq> s \<longrightarrow>  [a]\<^sup>@r \<cdot> [b] \<cdot> u \<and>\<^sub>p [a]\<^sup>@s \<cdot> [c] \<cdot> v = [a]\<^sup>@(min r s)"
  proof (rule diff_induct[of "\<lambda> r s. r \<noteq> s \<longrightarrow> [a]\<^sup>@r \<cdot> [b] \<cdot> u \<and>\<^sub>p [a]\<^sup>@s \<cdot> [c] \<cdot> v = [a]\<^sup>@(min r s)"])
    have "[a] \<^sup>@ Suc (x - 1) \<cdot> [b] \<cdot> u \<and>\<^sub>p [c] \<cdot> v = [a] \<^sup>@ min x 0" if "x \<noteq> 0" for x
      unfolding pow_Suc  min_0R exp_simps rassoc by (simp add: \<open>a \<noteq> c\<close>)
    thus "x \<noteq> 0 \<longrightarrow> [a] \<^sup>@ x \<cdot> [b] \<cdot> u \<and>\<^sub>p [a] \<^sup>@ 0 \<cdot> [c] \<cdot> v = [a] \<^sup>@ min x 0" for x  by force
    show "0 \<noteq> Suc y \<longrightarrow> [a] \<^sup>@ 0 \<cdot> [b] \<cdot> u \<and>\<^sub>p [a] \<^sup>@ Suc y \<cdot> [c] \<cdot> v = [a] \<^sup>@ min 0 (Suc y)" for y
      unfolding pow_Suc  min_0L exp_simps rassoc using \<open>a \<noteq> b\<close> by auto
    show "x \<noteq> y \<longrightarrow> [a] \<^sup>@ x \<cdot> [b] \<cdot> u \<and>\<^sub>p [a] \<^sup>@ y \<cdot> [c] \<cdot> v = [a] \<^sup>@ min x y \<Longrightarrow>
           Suc x \<noteq> Suc y \<longrightarrow> [a] \<^sup>@ Suc x \<cdot> [b] \<cdot> u \<and>\<^sub>p [a] \<^sup>@ Suc y \<cdot> [c] \<cdot> v = [a] \<^sup>@ min (Suc x) (Suc y)" for x y
      unfolding pow_Suc rassoc min_Suc_Suc by simp
  qed
  with assms
  show ?thesis by blast
qed

lemmas sing_suf_comp_mismatch = sing_pref_comp_mismatch[reversed]

lemma exp_pref_cancel: assumes "t\<^sup>@m \<cdot> y = t\<^sup>@k" shows "y = t\<^sup>@(k - m)"
  using lqI[of "t\<^sup>@m" "t\<^sup>@(k-m)" "t\<^sup>@k"]  unfolding lqI[OF \<open>t\<^sup>@m \<cdot> y = t\<^sup>@k\<close>]
  using  nat_le_linear[of m k] pop_pow[of m k t] diff_is_0_eq[of k m]   append.right_neutral[of "t\<^sup>@k"] pow_zero[of t]
    pref_antisym[of "t\<^sup>@m" "t\<^sup>@k", OF prefI[OF  \<open>t\<^sup>@m \<cdot> y = t\<^sup>@k\<close>] le_exps_pref[of k m t]]
  by presburger

lemmas exp_suf_cancel = exp_pref_cancel[reversed]

lemma index_pow_mod: "i < \<^bold>|r\<^sup>@k\<^bold>| \<Longrightarrow> (r\<^sup>@k)!i = r!(i mod \<^bold>|r\<^bold>|)"
proof(induction k)
  have aux:  "\<^bold>|r\<^sup>@(Suc l)\<^bold>| = \<^bold>|r\<^sup>@l\<^bold>| + \<^bold>|r\<^bold>|" for l
    by simp
  have aux1: "\<^bold>|(r\<^sup>@l)\<^bold>| \<le> i \<Longrightarrow> i < \<^bold>|r\<^sup>@l\<^bold>| + \<^bold>|r\<^bold>| \<Longrightarrow>  i mod \<^bold>|r\<^bold>| = i -  \<^bold>|r\<^sup>@l\<^bold>|" for l
    unfolding pow_len[of r l] using less_diff_conv2[of "l * \<^bold>|r\<^bold>|" i "\<^bold>|r\<^bold>|", unfolded add.commute[of "\<^bold>|r\<^bold>|"  "l * \<^bold>|r\<^bold>|"]]
      get_mod[of "i - l * \<^bold>|r\<^bold>|" "\<^bold>|r\<^bold>|" l] le_add_diff_inverse[of "l*\<^bold>|r\<^bold>|" i] by argo
  case (Suc k)
  show ?case
    unfolding aux sym[OF pow_Suc'[symmetric]] nth_append le_mod_geq
    using aux1[ OF _ Suc.prems[unfolded aux]]
      Suc.IH pow_Suc'[symmetric] Suc.prems[unfolded aux] leI[of i "\<^bold>|r \<^sup>@ k\<^bold>|"] by presburger
qed auto

lemma sing_pow_len [simp]: "\<^bold>|[r]\<^sup>@l\<^bold>| = l"
  by (induct l) auto

lemma take_sing_pow: "k \<le> l \<Longrightarrow> take k ([r]\<^sup>@l) = [r]\<^sup>@k"
proof (induct k)
  case (Suc k)
  have "k < \<^bold>|[r]\<^sup>@l\<^bold>|" using Suc_le_lessD[OF \<open>Suc k \<le> l\<close>] unfolding sing_pow_len.
  from take_Suc_conv_app_nth[OF this]
  show ?case
    unfolding Suc.hyps[OF Suc_leD[OF \<open>Suc k \<le> l\<close>]] pow_Suc'
    unfolding sing_pow_nth[OF Suc_le_lessD[OF \<open>Suc k \<le> l\<close>]].
qed simp

lemma concat_take_sing: assumes "k \<le> l" shows "concat (take k ([r]\<^sup>@l)) = r\<^sup>@k"
  unfolding take_sing_pow[OF \<open>k \<le> l\<close>] using concat_sing_pow.

lemma unique_letter_word: assumes "\<And>c. c \<in> set w \<Longrightarrow> c = a" shows "w = [a]\<^sup>@\<^bold>|w\<^bold>|"
  using assms proof (induction w)
  case (Cons b w)
  have "[a] \<^sup>@ \<^bold>|w\<^bold>| = w" using Cons.IH[OF Cons.prems[OF list.set_intros(2)]]..
  then show "b # w = [a] \<^sup>@ \<^bold>|b # w\<^bold>|"
    unfolding Cons.prems[OF list.set_intros(1)] by auto
qed simp

lemma card_set_le_1_imp_hd_pow: assumes "card (set u) \<le> 1" shows "[hd u] \<^sup>@ \<^bold>|u\<^bold>| = u"
proof (cases "u = \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  then have "card (set u) = 1" using \<open>card (set u) \<le> 1\<close>
    unfolding le_less less_one card_0_eq[OF finite_set] set_empty by blast
  then have "set u = {hd u}" using hd_in_set[OF \<open>u \<noteq> \<epsilon>\<close>]
  by (elim card_1_singletonE) simp
  then show "[hd u]\<^sup>@\<^bold>|u\<^bold>| = u"
    by (intro unique_letter_word[symmetric]) blast
qed simp

lemma unique_letter_wordE'[elim]: assumes "(\<forall> c. c \<in> set w \<longrightarrow> c = a)" obtains k where "w = [a]\<^sup>@k"
  using unique_letter_word assms by metis

lemma unique_letter_wordE''[elim]: assumes "set w \<subseteq> {a}" obtains k where "w = [a] \<^sup>@ k"
  using assms unique_letter_word[of w a] by blast

lemma unique_letter_wordE[elim]: assumes "set w = {a}" obtains k where "w = [a]\<^sup>@Suc k"
proof-
  have "w \<noteq> \<epsilon>" using assms by force
  obtain l where "w = [a]\<^sup>@l"
    using unique_letter_wordE''[of w a thesis] assms by force
  with \<open>w \<noteq> \<epsilon>\<close>
  have "l \<noteq> 0"
    by blast
  show thesis
    using that[of "l-1"] unfolding \<open>w = [a]\<^sup>@l\<close> Suc_minus[OF \<open>l \<noteq> 0\<close>] by blast
qed

lemma conjug_pow: "x \<cdot> z = z \<cdot> y \<Longrightarrow> x\<^sup>@k \<cdot> z = z \<cdot> y\<^sup>@k"
  by (induct k) fastforce+

lemma lq_conjug_pow: assumes "p \<le>p x \<cdot> p" shows "p\<inverse>\<^sup>>(x\<^sup>@k \<cdot> p) = (p\<inverse>\<^sup>>(x \<cdot> p))\<^sup>@k"
  using lqI[OF sym[OF conjug_pow[of x p  "p\<inverse>\<^sup>>(x \<cdot> p)", OF sym[OF lq_pref[OF \<open>p \<le>p x \<cdot> p\<close>]], of k]]].

lemmas rq_conjug_pow = lq_conjug_pow[reversed]

lemma pow_pref_root_one: assumes "0 < k" and "r \<noteq> \<epsilon>" and "r\<^sup>@k \<le>p r"
  shows  "k = 1"
  unfolding eq_pow_exp[OF \<open>r \<noteq> \<epsilon>\<close>, of k 1, symmetric] pow_1
  using \<open>r\<^sup>@k \<le>p r\<close> triv_pref[of r "r\<^sup>@(k-1)", folded pow_pos[OF \<open>0 < k\<close>]] by auto

lemma count_list_pow: "count_list (w\<^sup>@k) a = k * (count_list w a)"
  by (induction k, simp, simp)

lemma comp_pows_pref: assumes  "v \<noteq> \<epsilon>" and "(u \<cdot> v)\<^sup>@k \<cdot> u \<le>p (u \<cdot> v)\<^sup>@m" shows "k \<le> m"
  using pref_exp_le[OF _  pref_extD[OF assms(2)]] assms(1) by blast

lemma comp_pows_pref': assumes  "v \<noteq> \<epsilon>" and "(u \<cdot> v)\<^sup>@k \<le>p (u \<cdot> v)\<^sup>@m \<cdot> u" shows "k \<le> m"
proof(rule ccontr)
  assume "\<not> k \<le> m"
  hence "Suc m \<le> k" by simp
  from le_exps_pref[OF this, unfolded pow_Suc']
  have "(u \<cdot> v)\<^sup>@m \<cdot> (u \<cdot> v) \<le>p (u \<cdot> v)\<^sup>@k".
  from pref_trans[OF this assms(2)] \<open>v \<noteq> \<epsilon>\<close>
  show False by auto
qed

lemma comp_pows_not_pref: "\<not> (u \<cdot> v)\<^sup>@k \<cdot> u \<le>p (u \<cdot> v)\<^sup>@m \<Longrightarrow> m \<le> k"
  by (induction k m rule: diff_induct) auto

lemma comp_pows_spref: "u\<^sup>@k <p u\<^sup>@m \<Longrightarrow> k < m"
  by (induction k m rule: diff_induct) auto

lemma comp_pows_spref_ext: "(u \<cdot> v)\<^sup>@k \<cdot> u <p (u \<cdot> v)\<^sup>@m \<Longrightarrow> k < m"
  by (induction k m rule: diff_induct) auto

lemma comp_pows_pref_zero:"(u \<cdot> v)\<^sup>@k <p u \<Longrightarrow> k = 0"
  by (induct k) auto

lemma comp_pows_spref': "(u \<cdot> v)\<^sup>@k <p (u \<cdot> v)\<^sup>@m \<cdot> u \<Longrightarrow> k < Suc m"
  by (induction k m rule: diff_induct, simp_all add: comp_pows_pref_zero)

lemmas comp_pows_suf = comp_pows_pref[reversed] and
       comp_pows_suf' =  comp_pows_pref'[reversed] and
       comp_pows_not_suf = comp_pows_not_pref[reversed] and
       comp_pows_ssuf = comp_pows_spref[reversed] and
       comp_pows_ssuf_ext = comp_pows_spref_ext[reversed] and
       comp_pows_suf_zero = comp_pows_pref_zero[reversed] and
       comp_pows_ssuf' = comp_pows_spref'[reversed]

subsection Comparison

\<comment> \<open>Lemmas allowing to compare complicated terms with powers\<close>

named_theorems shifts
lemma shift_pow[shifts]: "(u\<cdot>v)\<^sup>@k\<cdot>u = u\<cdot>(v\<cdot>u)\<^sup>@k"
  using conjug_pow[OF rassoc].
  lemma[shifts]: "(u \<cdot> v)\<^sup>@k \<cdot> u \<cdot> z = u \<cdot> (v \<cdot> u)\<^sup>@k \<cdot> z"
  by (simp add: shift_pow)
lemma[shifts]: "u\<^sup>@k \<cdot> u \<cdot> z = u \<cdot> u\<^sup>@k \<cdot> z"
  by (simp add: conjug_pow)
lemma[shifts]: "r\<^sup>@k \<le>p r \<cdot> r\<^sup>@k"
  by (simp add: pow_comm[symmetric])
lemma [shifts]: "r\<^sup>@k \<le>p r \<cdot> r\<^sup>@k \<cdot> z"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc by blast
lemma [shifts]: "(r \<cdot> q)\<^sup>@k \<le>p r \<cdot> q \<cdot>  (r \<cdot> q)\<^sup>@k \<cdot> z"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc by simp
lemma [shifts]: "(r \<cdot> q)\<^sup>@k \<le>p r \<cdot> q \<cdot>  (r \<cdot> q)\<^sup>@k"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc by simp
lemma[shifts]: "r\<^sup>@k \<cdot> u \<le>p r \<cdot> r\<^sup>@k \<cdot> v \<longleftrightarrow> u \<le>p r \<cdot> v"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc pref_cancel_conv..
lemma[shifts]: "u \<cdot> u\<^sup>@k \<cdot> z = u\<^sup>@k \<cdot> w \<longleftrightarrow> u \<cdot> z = w"
   unfolding lassoc pow_comm[symmetric] unfolding rassoc cancel..
lemma[shifts]: "(r \<cdot> q)\<^sup>@k \<cdot> u \<le>p r \<cdot> q  \<cdot> (r \<cdot> q)\<^sup>@k \<cdot> v \<longleftrightarrow> u \<le>p r \<cdot> q \<cdot> v"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc pref_cancel_conv..
lemma[shifts]: "(r \<cdot> q)\<^sup>@k \<cdot> u = r \<cdot> q  \<cdot> (r \<cdot> q)\<^sup>@k \<cdot> v \<longleftrightarrow> u = r \<cdot> q \<cdot> v"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc cancel..
lemma[shifts]: "r \<cdot> q  \<cdot> (r \<cdot> q)\<^sup>@k \<cdot> v = (r \<cdot> q)\<^sup>@k \<cdot> u \<longleftrightarrow> r \<cdot> q \<cdot> v = u"
  unfolding lassoc pow_comm[symmetric] unfolding rassoc cancel..
lemma shifts_spec [shifts]: "(u\<^sup>@k \<cdot> v)\<^sup>@l \<cdot> u \<cdot> u\<^sup>@k \<cdot> z = u\<^sup>@k \<cdot> (v \<cdot> u\<^sup>@k)\<^sup>@l \<cdot> u \<cdot> z"
  unfolding lassoc cancel_right unfolding rassoc pow_comm[symmetric]
  unfolding lassoc cancel_right shift_pow..
lemmas [shifts] = shifts_spec[of "r \<cdot> q", unfolded rassoc] for r q
lemmas [shifts] = shifts_spec[of "r \<cdot> q" _ _ _ \<epsilon> , unfolded rassoc emp_simps] for r q
lemmas [shifts] = shifts_spec[of "r \<cdot> q" _ "r \<cdot> q", unfolded rassoc] for r q
lemmas [shifts] = shifts_spec[of "r \<cdot> q" _ "r \<cdot> q" _ \<epsilon> , unfolded rassoc emp_simps] for r q
lemma[shifts]: "(u \<cdot> (v \<cdot> u)\<^sup>@k)\<^sup>@j \<cdot> (u \<cdot> v)\<^sup>@k = (u \<cdot> v)\<^sup>@k \<cdot> (u \<cdot> (u \<cdot> v)\<^sup>@k)\<^sup>@j"
  by (metis shift_pow)
lemma[shifts]: "(u \<cdot> (v \<cdot> u)\<^sup>@k \<cdot> z)\<^sup>@j \<cdot> (u \<cdot> v)\<^sup>@k = (u \<cdot> v)\<^sup>@k \<cdot> (u \<cdot> z \<cdot> (u \<cdot> v)\<^sup>@k)\<^sup>@j"
  by (simp add: conjug_pow)
lemmas[shifts] = pow_comm cancel rassoc pow_Suc pref_cancel_conv suf_cancel_conv add_exps cancel_right numeral_nat pow_zero emp_simps
lemmas[shifts] = less_eq_Suc_le
lemmas[shifts] =  neq0_conv
lemma shifts_hd_hd [shifts]: "a#b#v = [a] \<cdot> b#v"
  using hd_word.
lemmas [shifts] =  shifts_hd_hd[of _ _ \<epsilon>]
lemma[shifts]: "n \<le> k \<Longrightarrow> x\<^sup>@k = x\<^sup>@(n + (k -n))"
  by simp
lemma[shifts]: "n < k \<Longrightarrow> x\<^sup>@k = x\<^sup>@(n + (k -n))"
  by simp
lemmas[shifts] = cancel cancel_right pref_cancel_conv suf_cancel_conv triv_pref
lemmas[shifts] = pow_diff

lemmas shifts_rev = shifts[reversed]

lemmas shift_simps = shifts shifts[reversed]

method comparison = ((simp only: shifts; fail) | (simp only: shifts_rev; fail))

section \<open>Rotation\<close>

lemma rotate_root_self: "rotate \<^bold>|r\<^bold>| (r\<^sup>@k) = r\<^sup>@k"
proof (cases "r = \<epsilon>")
  assume "r \<noteq> \<epsilon>"
  show ?thesis
  proof (cases k)
    fix pred
    assume k: "k = Suc pred"
    show ?thesis
      unfolding k pow_Suc rotate_append pow_comm..
  qed simp
qed simp

lemma rotate_pow_self: "rotate (l*\<^bold>|u\<^bold>|) (u\<^sup>@k) = u\<^sup>@k"
proof(induct l)
  case (Suc l)
  show ?case
    unfolding mult_Suc rotate_rotate[symmetric] Suc.hyps
    using rotate_root_self.
qed simp

lemma rotate_pow_mod:  "rotate n (u\<^sup>@k) = rotate (n mod \<^bold>|u\<^bold>|) (u\<^sup>@k)"
  using rotate_rotate[of "n mod \<^bold>|u\<^bold>|" "n div \<^bold>|u\<^bold>| * \<^bold>|u\<^bold>|" "u\<^sup>@k", symmetric]
  unfolding rotate_pow_self[of "n div \<^bold>|u\<^bold>|" u k] div_mult_mod_eq[of n "\<^bold>|u\<^bold>|", unfolded add.commute[of "n div \<^bold>|u\<^bold>| * \<^bold>|u\<^bold>|" "n mod \<^bold>|u\<^bold>|"]].

lemma rotate_conj_pow: "rotate \<^bold>|u\<^bold>| ((u\<cdot>v)\<^sup>@k) = (v\<cdot>u)\<^sup>@k"
 by (induct k, simp, simp add: rotate_append shift_pow)

lemma rotate_pow_comm: "rotate n (u\<^sup>@k) = (rotate n u)\<^sup>@k"
proof (cases "u = \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  show ?thesis
    unfolding rotate_drop_take[of n u] rotate_pow_mod[of n u k]
    using rotate_conj_pow[of "take (n mod \<^bold>|u\<^bold>|) u" "drop (n mod \<^bold>|u\<^bold>|) u" k, unfolded append_take_drop_id[of "n mod \<^bold>|u\<^bold>|" u]]
    unfolding  mod_le_divisor[of "\<^bold>|u\<^bold>|" n, THEN take_len, OF \<open>u\<noteq>\<epsilon>\<close>[unfolded length_greater_0_conv[symmetric]]].
qed simp

lemmas rotate_pow_comm_two = rotate_pow_comm[of _ _ 2, unfolded pow_two]

lemma rotate_back: "rotate (\<^bold>|u\<^bold>| - n mod \<^bold>|u\<^bold>|) (rotate n u) = u"
proof  (cases "u = \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  show ?thesis
  unfolding rotate_conv_mod[of n u] rotate_rotate[of "\<^bold>|u\<^bold>| - n mod \<^bold>|u\<^bold>|" "n mod \<^bold>|u\<^bold>|" u]
  le_add_diff_inverse2[OF mod_le_divisor, OF nemp_pos_len[OF \<open>u \<noteq> \<epsilon>\<close>]]
  by simp
qed simp


lemma rotate_backE: obtains m where "rotate m (rotate n u) = u"
  using rotate_back by blast

lemma rotate_back': assumes "rotate m w = rotate n w"
  shows "rotate (m-n) w = w"
proof (cases)
  assume "n \<le> m"
  from rotate_backE obtain k where   "rotate k (rotate n w) = w".
  hence nk: "rotate n (rotate k w) = w"
    unfolding rotate_rotate add.commute[of _ k].
  have mn: "rotate m (rotate k w) = (rotate n (rotate k w))"
    unfolding rotate_rotate add.commute[of _ k] unfolding rotate_rotate[symmetric] assms..
  have "rotate (m - n) (rotate n (rotate k w)) = rotate m (rotate k w)"
    unfolding rotate_rotate using \<open>n \<le> m\<close> by simp
  from this[unfolded mn nk]
  show ?thesis.
qed simp

lemma rotate_class_rotate': "(\<exists>n. rotate n w = u) \<longleftrightarrow> (\<exists>n. rotate n (rotate l w) = u)"
proof
  obtain m where rot_m: "rotate m (rotate l w) = w" using rotate_backE.
  assume "\<exists>n. rotate n w = u"
  then obtain n where rot_n: "rotate n w = u" by blast
  show "\<exists>n. rotate n (rotate l w) = u"
    using  exI[of "\<lambda> x. rotate x (rotate l w) = u" "n+m", OF
        rotate_rotate[symmetric, of n m "rotate l w", unfolded rot_m rot_n]].
next
  show "\<exists>n. rotate n (rotate l w) = u \<Longrightarrow> \<exists>n. rotate n w = u"
    using rotate_rotate[symmetric] by blast
qed

lemma rotate_class_rotate: "{u . \<exists>n. rotate n w = u} = {u . \<exists>n. rotate n (rotate l w) = u}"
  using rotate_class_rotate' by blast

lemma rotate_comp_eq:"w \<bowtie> rotate n w \<Longrightarrow> rotate n w = w"
  using  pref_same_len[OF _ length_rotate[of n w]] pref_same_len[OF _ length_rotate[of n w, symmetric], symmetric]
  by blast

corollary mismatch_iff_lexord: assumes "rotate n w \<noteq> w" and "irrefl r"
  shows "mismatch_pair w (rotate  n w) \<in> r \<longleftrightarrow> (w,rotate n w) \<in> lexord r"
proof-
  have "\<not> w \<bowtie> rotate n w"
    using rotate_comp_eq \<open>rotate n w \<noteq> w\<close>
    unfolding prefix_comparable_def by blast
  from lexord_mismatch[OF this \<open>irrefl r\<close>]
  show ?thesis.
qed


section \<open>Lists of words and their concatenation\<close>

text\<open>The helpful lemmas of this section deal with concatenation of a list of words @{term concat}.
The main objective is to cover elementary facts needed to study factorizations of words.
\<close>

lemma concat_take_is_prefix: "concat(take n ws) \<le>p concat ws"
  using concat_morph[of "take n ws" "drop n ws",symmetric, unfolded append_take_drop_id[of n ws], THEN prefI].

lemma concat_take_Suc: assumes "j < \<^bold>|ws\<^bold>|" shows "concat(take j ws) \<cdot> ws!j = concat(take (Suc j) ws)"
  unfolding take_Suc_conv_app_nth[OF \<open>j < \<^bold>|ws\<^bold>|\<close>]
  using sym[OF concat_append[of "(take j ws)" "[ws ! j]",
        unfolded concat.simps(2)[of "ws!j" \<epsilon>, unfolded concat.simps(1) append_Nil2]]].

lemma pref_mod_list: assumes "u <p concat ws"
  obtains j r where "j < \<^bold>|ws\<^bold>|" and "r <p ws!j" and "concat (take j ws) \<cdot> r = u"
proof-
  have "\<^bold>|ws\<^bold>| \<noteq> 0"
    using assms by auto
  then obtain l where "Suc l = \<^bold>|ws\<^bold>|"
    using Suc_pred by blast
  let ?P = "\<lambda> j. u <p concat(take (Suc j) ws)"
  have "?P l"
    using assms  \<open>Suc l = \<^bold>|ws\<^bold>|\<close> by auto
  define j where "j = (LEAST j. ?P j)" \<comment> \<open>smallest j such that concat (take (Suc j) ws) <p u\<close>
  have "u <p concat(take (Suc j) ws)"
    using  LeastI[of ?P, OF \<open>?P l\<close>] unfolding sym[OF j_def].
  have  "j < \<^bold>|ws\<^bold>|"
    using Least_le[of ?P, OF \<open>?P l\<close>] \<open>Suc l = \<^bold>|ws\<^bold>|\<close> unfolding sym[OF j_def]
    by auto
  have "concat(take j ws) \<le>p u"
    using Least_le[of ?P "(j - Suc 0)", unfolded sym[OF j_def]]
      ruler[OF concat_take_is_prefix sprefD1[OF assms], of j]
    by (cases "j = 0", simp) force
  from prefixE[OF this]
  obtain r where "u = concat(take j ws) \<cdot> r".
  from \<open>u <p concat (take (Suc j) ws)\<close>[unfolded this]
  have "r <p ws!j"
    unfolding concat_take_Suc[OF \<open>j < \<^bold>|ws\<^bold>|\<close>, symmetric]  spref_cancel_conv.
  show thesis
    using that[OF \<open>j < \<^bold>|ws\<^bold>|\<close> \<open>r <p ws!j\<close> \<open>u = concat(take j ws) \<cdot> r\<close>[symmetric]].
qed

thm prefI

lemma pref_mod_pow: assumes "u \<le>p w\<^sup>@l" and "w \<noteq> \<epsilon>"
  obtains k z where "k \<le> l" and "z <p w" and "w\<^sup>@k\<cdot>z = u"
proof (cases "u = w\<^sup>@l")
  assume "u \<noteq> w\<^sup>@l"
  from sprefI[OF \<open>u \<le>p w\<^sup>@l\<close> this]
  have "u <p w \<^sup>@ l".
  have "w\<^sup>@l = concat ([w]\<^sup>@l)"
    by simp
  from pref_mod_list[of u "[w]\<^sup>@l", unfolded sing_pow_len concat_sing_pow, OF \<open>u <p w\<^sup>@l\<close>]
  obtain j r where "j < l" "r <p ([w] \<^sup>@ l) ! j" "concat (take j ([w] \<^sup>@ l)) \<cdot> r = u".
  hence "j \<le> l" and "r <p w" and "w\<^sup>@j \<cdot> r = u"
    unfolding sing_pow_nth[OF \<open>j < l\<close>] concat_take_sing[OF less_imp_le[OF \<open>j < l\<close>]] by auto
  from that[OF this]
  show thesis.
qed (use emp_spref assms in blast)

lemma pref_mod_pow': assumes "u <p w\<^sup>@l"
  obtains k z where "k < l" and "z <p w" and "w\<^sup>@k\<cdot>z = u"
proof-
  have "w \<noteq> \<epsilon>" using assms by force
  from pref_mod_pow[OF sprefD1[OF assms] this]
  obtain k z where "k \<le> l" "z <p w" "w \<^sup>@ k \<cdot> z = u".
  note spref_extD[OF \<open>u <p w\<^sup>@l\<close>[folded \<open>w \<^sup>@ k \<cdot> z = u\<close>]]
  have "k < l"
    using comp_pows_spref[OF \<open>w \<^sup>@ k <p w \<^sup>@ l\<close>].
  from that[OF this \<open>z <p w\<close> \<open>w \<^sup>@ k \<cdot> z = u\<close>]
  show thesis.
qed

lemma split_pow: assumes "u \<cdot> v = w\<^sup>@k" "0 < k" "v \<noteq> \<epsilon>"
  obtains p s i j where "w = p \<cdot> s" "s \<noteq> \<epsilon>" "u = (p \<cdot> s)\<^sup>@i \<cdot> p" "v = (s \<cdot> p)\<^sup>@j \<cdot> s" "k = i + j + 1"
proof-
  have "u <p w\<^sup>@k"
    using assms(1,3) by blast
  from pref_mod_pow'[OF this]
  obtain ku p where "ku < k" "p <p w" "w \<^sup>@ ku \<cdot> p = u".
  from spref_exE[OF this(2)]
  obtain s where "p \<cdot> s = w" "s \<noteq> \<epsilon>".
  obtain kv where "k = Suc(ku + kv)"
    using  less_imp_Suc_add[OF \<open>ku < k\<close>] by blast
  from \<open>u \<cdot> v = w\<^sup>@k\<close>[folded this[symmetric] \<open>p \<cdot> s = w\<close> \<open>w \<^sup>@ ku \<cdot> p = u\<close>, unfolded rassoc pow_Suc']
  have "v = s \<cdot> w\<^sup>@kv"
    unfolding shifts unfolding lassoc shift_pow[symmetric] unfolding rassoc cancel \<open>p \<cdot> s = w\<close>.
  show thesis
    using that[OF \<open>p \<cdot> s = w\<close>[symmetric] \<open>s \<noteq> \<epsilon>\<close> \<open>w \<^sup>@ ku \<cdot> p = u\<close>[folded \<open>p\<cdot>s = w\<close>, symmetric]
          \<open>v = s \<cdot> w\<^sup>@kv\<close>[folded \<open>p\<cdot>s = w\<close>,folded shift_pow] \<open>k = Suc(ku + kv)\<close>[unfolded Suc_eq_plus1]].
qed










lemma del_emp_concat: "concat us = concat (filter (\<lambda>x. x \<noteq> \<epsilon>) us)"
  by (induct us) simp+

lemma lists_minus: "us \<in> lists (C - A) \<Longrightarrow> us \<in> lists C"
  by blast

lemma lists_minus': "us \<in> lists C \<Longrightarrow> (filter (\<lambda>x. x \<noteq> \<epsilon>) us) \<in> lists (C - {\<epsilon>})"
  by (simp add: in_lists_conv_set)

lemma pref_concat_pref: "us \<le>p ws \<Longrightarrow> concat us \<le>p concat ws"
  by (auto simp add: prefix_def)

lemmas suf_concat_suf = pref_concat_pref[reversed]

lemma concat_mono_fac: "us \<le>f ws \<Longrightarrow> concat us \<le>f concat ws"
  using  concat_morph facE facI' by metis

lemma ruler_concat_less: assumes "us \<le>p ws" and "vs \<le>p ws" and "\<^bold>|concat us\<^bold>| < \<^bold>|concat vs\<^bold>|"
  shows "us <p vs"
  using ruler[OF \<open>us \<le>p ws\<close> \<open>vs \<le>p ws\<close>] pref_concat_pref[of vs us, THEN prefix_length_le] \<open>\<^bold>|concat us\<^bold>| < \<^bold>|concat vs\<^bold>|\<close>
  by force

lemma concat_take_mono_strict: assumes "concat (take i ws) <p concat (take j ws)"
  shows "take i ws <p take j ws"
  using ruler_concat_less[OF _ _ prefix_length_less, OF take_is_prefix take_is_prefix assms].

lemma take_pp_less: assumes "take k ws <p take n ws" shows "k < n"
  using  conjunct2[OF sprefD[OF assms]]
    leI[of k n, THEN[2] le_take_pref[of n k ws, THEN[2] pref_antisym[of "take k ws" "take n ws"]], OF conjunct1[OF sprefD[OF assms]]]
  by blast

lemma concat_pp_less: assumes "concat (take k ws) <p concat (take n ws)" shows "k < n"
  using le_take_pref[of n k ws, THEN pref_concat_pref] conjunct1[OF sprefD[OF assms]]
    conjunct2[OF sprefD[OF assms]] pref_antisym[of "concat(take k ws)" "concat(take n ws)"]
  by fastforce

lemma take_le_take: "j \<le> k \<Longrightarrow> take j (take k xs) = take j xs"
proof (rule disjE[OF le_less_linear, of k "\<^bold>|xs\<^bold>|"])
  assume "j \<le> k" and "k \<le> \<^bold>|xs\<^bold>|"
  show ?thesis
    using pref_share_take[OF take_is_prefix, of j k xs, unfolded take_len[OF \<open>k \<le> \<^bold>|xs\<^bold>|\<close>], OF \<open>j \<le> k\<close>].
qed simp

lemma concat_interval: assumes "concat (take k vs) = concat (take j vs) \<cdot> s" shows "concat (drop j (take k vs)) = s"
proof (rule disjE[OF le_less_linear, of k j])
  note eq1 = assms[folded  arg_cong[OF takedrop[of j "take k vs"], of concat, unfolded concat_morph]]
  assume "j < k"
  from eq1[unfolded take_le_take[OF less_imp_le[OF this]]]
  show ?thesis
    unfolding cancel.
next
  note eq1 = assms[folded  arg_cong[OF takedrop[of j "take k vs"], of concat, unfolded concat_morph]]
  assume "k \<le> j"
  from pref_concat_pref[OF le_take_pref, OF this, of vs, unfolded assms]
  have "s = \<epsilon>"
    by force
  from drop_all[OF le_trans[OF len_take1 \<open>k \<le> j\<close>], of vs]
  have "concat (drop j (take k vs)) = \<epsilon>"
    using concat.simps(1) by force
  with \<open>s = \<epsilon>\<close>
  show ?thesis by blast
qed

lemma bin_lists_count_zero': assumes "ws \<in> lists {x,y}" and "count_list ws y = 0"
  shows "ws \<in> lists {x}"
  using assms
proof (induct ws)
  case (Cons a ws)
  have "a \<noteq> y"
    using \<open>count_list (a # ws) y = 0\<close> count_list.simps(2) by force
  hence "count_list ws y = 0"
    using \<open>count_list (a # ws) y = 0\<close> count_list.simps(2) by force
  from Cons.hyps(3)[OF this]
  show ?case
    using \<open>a \<in> {x,y}\<close>  \<open>a \<noteq> y\<close> by auto
qed simp

lemma bin_lists_count_zero: assumes "ws \<in> lists {x,y}" and "count_list ws x = 0"
  shows "ws \<in> lists {y}"
  using assms unfolding insert_commute[of x y "{}"] using  bin_lists_count_zero' by metis

lemma count_in: "count_list ws a \<noteq> 0 \<Longrightarrow> a \<in> set ws"
  using count_notin[of a ws] by fast

lemma count_in_conv: "count_list w a \<noteq> 0 \<longleftrightarrow>  a \<in> set w"
  by (induct w, auto)

lemma two_in_set_concat_len: assumes "u \<noteq> v" and "{u,v} \<subseteq> set ws"
  shows "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|concat ws\<^bold>|"
proof-
  let ?ws = "filter (\<lambda> x. x \<in> {u,v}) ws"
  have set: "set ?ws = {u,v}"
    using \<open>{u,v} \<subseteq> set ws\<close> by auto
  have "\<^bold>|concat ?ws\<^bold>| \<le> \<^bold>|concat ws\<^bold>|"
    unfolding length_concat  using sum_list_filter_le_nat by blast
  have sum: "sum (\<lambda> x. count_list ?ws x * \<^bold>|x\<^bold>|) {u,v} = (count_list ?ws u) * \<^bold>|u\<^bold>| + (count_list ?ws v)*\<^bold>|v\<^bold>|"
    using assms by simp
  have "count_list ?ws u \<noteq> 0" and "count_list ?ws v \<noteq> 0"
    unfolding count_in_conv using assms by simp_all
  hence "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|concat ?ws\<^bold>|"
    unfolding length_concat sum_list_map_eq_sum_count set sum
    using add_le_mono quotient_smaller by presburger
  thus ?thesis
    using \<open>\<^bold>|concat ?ws\<^bold>| \<le> \<^bold>|concat ws\<^bold>|\<close> by linarith
qed


section \<open>Root\<close>

definition root :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<in> _*" [51,51] 60 )
  where  "u \<in> r* =  (\<exists> k. r\<^sup>@k = u)"
notation (latex output) root ("_ \<in> _\<^sup>*")

abbreviation not_root :: "['a list, 'a list] \<Rightarrow> bool"  ("_ \<notin> _*" [51,51] 60 )
  where "u \<notin> r* \<equiv> \<not> (u \<in> r*)"

text\<open>Empty word has all roots, including the empty root.\<close>

lemma emp_all_roots [simp]: "\<epsilon> \<in> r*"
  unfolding root_def using pow_0 by blast

lemma emp_all_roots'[elim]: "u = \<epsilon> \<Longrightarrow> u \<in> r*"
  using emp_all_roots by blast

lemma rootI: "r\<^sup>@k \<in> r*"
  using root_def by auto

lemma self_root: "u \<in> u*"
  using rootI[of u "Suc 0"] by simp

lemma rootE[elim]: assumes "u \<in> r*" obtains k where "r\<^sup>@k = u"
  using assms root_def by blast

lemma root_exp: "x \<in> r* \<longleftrightarrow> x = r\<^sup>@(\<^bold>|x\<^bold>| div \<^bold>|r\<^bold>|)"
proof (rule iffI, cases "r = \<epsilon>", force)
  assume "x \<in> r*" and "r \<noteq> \<epsilon>"
  then obtain k where "r\<^sup>@k = x"
    unfolding root_def by blast
  from lenarg[OF this, unfolded pow_len]
  have "k = \<^bold>|x\<^bold>| div \<^bold>|r\<^bold>|"
    using nonzero_mult_div_cancel_right[OF nemp_len[OF \<open>r \<noteq> \<epsilon>\<close>], of k]  by auto
  from \<open>r\<^sup>@k = x\<close>[unfolded this, symmetric]
  show "x = r \<^sup>@ (\<^bold>|x\<^bold>| div \<^bold>|r\<^bold>|)".
qed (use root_def in metis)

lemma root_nemp_expE: assumes "w \<in> r*" and "w \<noteq> \<epsilon>"
  obtains k where "r\<^sup>@k = w" "0 < k"
  using assms(1) assms(2) nemp_exp_pos root_exp by metis

lemma root_rev_iff[reversal_rule]: "rev u \<in> rev t* \<longleftrightarrow> u \<in> t*"
  unfolding root_def[reversed] using root_def..

lemma per_root_pref: "w \<noteq> \<epsilon> \<Longrightarrow> w \<in> r* \<Longrightarrow> r \<le>p w"
  using root_nemp_expE pow_pos triv_pref by metis

lemmas per_root_suf =  per_root_pref[reversed]

lemma per_exp_eq: "u \<le>p r\<cdot>u \<Longrightarrow> \<^bold>|u\<^bold>| = k*\<^bold>|r\<^bold>| \<Longrightarrow> u \<in> r*"
  using per_exp_pref[THEN pref_prod_eq] unfolding pow_len root_def by blast

lemma take_root: assumes "0 < k" shows "r = take \<^bold>|r\<^bold>| (r\<^sup>@k)"
  unfolding pow_pos[OF assms] by force

lemma root_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> r* \<Longrightarrow> r \<noteq> \<epsilon>"
  unfolding root_def using emp_pow by auto

lemma root_shorter: assumes "u \<noteq> \<epsilon>" "u \<in> r*" "u \<noteq> r" shows "\<^bold>|r\<^bold>| < \<^bold>|u\<^bold>|"
proof (rule not_le_imp_less)
  from root_nemp_expE[OF \<open>u \<in> r*\<close> \<open>u \<noteq> \<epsilon>\<close>]
  obtain k where "r\<^sup>@k = u" and "0 < k".
  from take_root[OF \<open>0 < k\<close>, of r, unfolded \<open>r \<^sup>@ k = u\<close>]
  show "\<not> \<^bold>|u\<^bold>| \<le> \<^bold>|r\<^bold>|"
    using \<open>u \<noteq> r\<close> by force
qed

lemma root_shorter_eq: "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> r* \<Longrightarrow> \<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>|"
  using root_shorter le_eq_less_or_eq by auto

lemma root_trans[trans]: "\<lbrakk>v \<in> u*; u \<in> t*\<rbrakk> \<Longrightarrow> v \<in> t*"
  by (metis root_def pow_mult)

lemma root_pow_root[intro]: "v \<in> u* \<Longrightarrow> v\<^sup>@n \<in> u*"
  using rootI root_trans by blast

lemma root_len: "u \<in> q* \<Longrightarrow> \<exists>k. \<^bold>|u\<^bold>| = k*\<^bold>|q\<^bold>|"
  unfolding root_def using pow_len by auto

lemma root_len_dvd: "u \<in> t* \<Longrightarrow> \<^bold>|t\<^bold>| dvd \<^bold>|u\<^bold>|"
  using root_len root_def by force

lemma common_root_len_gcd: "u \<in> t* \<Longrightarrow> v \<in> t* \<Longrightarrow> \<^bold>|t\<^bold>| dvd (gcd \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|)"
  by (simp add: root_len_dvd)

lemma add_root[simp]: "z \<cdot> w \<in> z* \<longleftrightarrow> w \<in> z*"
proof
  assume "w \<in> z*" thus "z \<cdot> w \<in> z*"
    unfolding root_def using pow_Suc by blast
next
  assume "z \<cdot> w \<in> z*" thus "w \<in> z*"
    unfolding root_def
    using exp_pref_cancel[of z 1 w, unfolded pow_1] by metis
qed

lemma add_roots[intro]: "w \<in> z* \<Longrightarrow> w' \<in> z* \<Longrightarrow> w \<cdot> w' \<in> z*"
  unfolding root_def using add_exps by blast

lemma concat_sing_list_pow: "ws \<in> lists {u} \<Longrightarrow> \<^bold>|ws\<^bold>| = k \<Longrightarrow> concat ws = u\<^sup>@k"
proof(induct k arbitrary: ws)
  case (Suc k)
  have "ws \<noteq> \<epsilon>"
    using  list.size(3) nat.distinct(2)[of k, folded \<open>\<^bold>|ws\<^bold>| = Suc k\<close>] by blast
  from hd_Cons_tl[OF this]
  have "ws = hd ws # tl ws"  and "\<^bold>|tl ws\<^bold>| = k"
    using \<open> \<^bold>|ws\<^bold>| = Suc k\<close> by simp+
  then show ?case
    unfolding  pow_Suc hd_concat_tl[OF \<open>ws \<noteq> \<epsilon>\<close>, symmetric]
    using Suc.hyps[OF tl_in_lists[OF \<open> ws \<in> lists {u}\<close>] \<open>\<^bold>|tl ws\<^bold>| = k\<close>]
      Nitpick.size_list_simp(2) lists_hd_in_set[of "ws" "{u}"] \<open>ws \<in> lists{u}\<close> by blast
qed simp

lemma concat_sing_list_pow': "ws \<in> lists{u} \<Longrightarrow> concat ws = u\<^sup>@\<^bold>|ws\<^bold>|"
  by (simp add: concat_sing_list_pow)

lemma root_pref_cancel[elim]: assumes "x\<cdot>y \<in> t*" and  "x \<in> t*" shows "y \<in> t*"
proof-
  obtain n m where "t\<^sup>@m = x \<cdot> y" and "t\<^sup>@n = x"
    using \<open>x\<cdot>y \<in> t*\<close>[unfolded root_def] \<open>x \<in> t*\<close>[unfolded root_def] by blast
  from exp_pref_cancel[of t n y m, unfolded this]
  show "y \<in> t*"
    using rootI by auto
qed

lemma root_suf_cancel [elim]: "u \<cdot> v \<in> r* \<Longrightarrow> v \<in> r* \<Longrightarrow> u \<in> r*"
  using exp_suf_cancel[of u r] unfolding root_def by metis

section Commutation

text\<open>The solution of the easiest nontrivial word equation, @{term "x \<cdot> y = y \<cdot> x"}, is in fact already contained in List.thy as the fact @{thm comm_append_are_replicate[no_vars]}.\<close>

theorem comm:  "x \<cdot> y = y \<cdot> x  \<longleftrightarrow>  (\<exists> t k m. x = t\<^sup>@k \<and> y = t\<^sup>@m)"
  using  comm_append_are_replicate[of x y, folded pow_is_concat_replicate] pows_comm by auto

corollary comm_root:  "x \<cdot> y = y \<cdot> x   \<longleftrightarrow>  (\<exists> t. x \<in> t* \<and> y \<in> t*)"
  unfolding root_def comm by fast

lemma comm_rootI:  "x \<in> t* \<Longrightarrow> y \<in> t* \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  using comm_root  by blast

lemma commE[elim]: assumes  "x \<cdot> y = y \<cdot> x"
  obtains  t m k where "x = t\<^sup>@k" and "y = t\<^sup>@m" and "t \<noteq> \<epsilon>"
proof-
  from assms[unfolded comm]
  obtain t k m where "x = t\<^sup>@k" and "y = t\<^sup>@m"
    by blast
  from that[OF this]
  show thesis
  proof (cases "x \<noteq> \<epsilon> \<or> y \<noteq> \<epsilon>")
    assume "x \<noteq> \<epsilon> \<or> y \<noteq> \<epsilon>"
    thus thesis
      unfolding \<open>x = t\<^sup>@k\<close> \<open>y = t\<^sup>@m\<close> using \<open>t \<noteq> \<epsilon> \<Longrightarrow> thesis\<close>
      by fastforce
  next
    assume "\<not> (x \<noteq> \<epsilon> \<or> y \<noteq> \<epsilon>)"
    hence "x = \<epsilon>" "y = \<epsilon>"
      by blast+
    from that[of "[undefined]" 0 0, unfolded this]
    show thesis
      by simp
  qed
qed

lemma comm_nemp_eqE: assumes "u \<cdot> v = v \<cdot> u" "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
  obtains k m where  "u\<^sup>@k = v\<^sup>@m" "0 < k" "0 < m"
proof-
  from commE[OF \<open>u \<cdot> v = v \<cdot> u\<close>]
  obtain t m k where "u = t\<^sup>@k" and "v = t\<^sup>@m".
  hence "0 < m" "0 < k"
    using \<open>u \<noteq> \<epsilon>\<close> \<open>v \<noteq> \<epsilon>\<close> by blast+
  have "u\<^sup>@m = v\<^sup>@k"
    unfolding \<open>u = t\<^sup>@k\<close> \<open>v = t\<^sup>@m\<close> pow_mult[symmetric]
    by (simp add: mult.commute)
  from that[OF this \<open>0 < m\<close> \<open>0 < k\<close>]
  show thesis.
qed

lemma comm_prod[intro]: assumes "r\<cdot>u = u\<cdot>r" and "r\<cdot>v = v\<cdot>r"
  shows "r\<cdot>(u\<cdot>v) = (u\<cdot>v)\<cdot>r"
  unfolding lassoc \<open>r\<cdot>u = u\<cdot>r\<close> unfolding rassoc \<open>r\<cdot>v = v\<cdot>r\<close>..

lemma LS_comm:
  assumes "y \<^sup>@ k \<cdot> x = z \<^sup>@ l"
      and "z \<cdot> y = y \<cdot> z"
    shows "x \<cdot> y = y \<cdot> x"
proof -
  from \<open>z \<cdot> y = y \<cdot> z\<close>
  have "(y \<^sup>@ k \<cdot> x) \<cdot> y = y \<cdot> (y \<^sup>@ k \<cdot> x)"
    unfolding \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close> by (fact comm_add_exp)
  then show "x \<cdot> y = y \<cdot> x"
    unfolding lassoc pow_comm[symmetric] unfolding rassoc cancel.
qed

section \<open>Periods\<close>

text\<open>Periodicity is probably the most studied property of words. It captures the fact that a word overlaps with itself.
Another possible point of view is that the periodic word is a prefix of an (infinite) power of some nonempty
word, which can be called its period word. Both these points of view are expressed by the following definition.
\<close>

subsection "Periodic root"


lemma "u <p r \<cdot> u \<longleftrightarrow> u \<le>p r \<cdot> u \<and> r \<noteq> \<epsilon>"
  by simp

lemma per_rootI[intro]: "u \<le>p r \<cdot> u \<Longrightarrow> r \<noteq> \<epsilon> \<Longrightarrow> u <p r \<cdot> u"
  by simp

lemma per_rootI'[intro]: assumes "u \<le>p r\<^sup>@k" and  "r \<noteq> \<epsilon>" shows  "u <p r \<cdot> u"
  using per_rootI[OF  pref_prod_pref[OF pref_pow_ext'[OF \<open>u \<le>p r\<^sup>@k\<close>] \<open>u \<le>p r\<^sup>@k\<close>] \<open>r\<noteq>\<epsilon>\<close>].

lemma per_root_nemp[dest]: "u <p r \<cdot> u \<Longrightarrow> r \<noteq> \<epsilon>"
  by simp

text \<open>Empty word is not a periodic root but it has all nonempty periodic roots.\<close>



text \<open>Any nonempty word is its own periodic root.\<close>

lemmas root_self = triv_spref

text\<open>"Short roots are prefixes"\<close>

lemma "w <p r \<cdot> u \<Longrightarrow> \<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>| \<Longrightarrow>  r \<le>p w"
  using pref_prod_long[OF sprefD1].

text \<open>Periodic words are prefixes of the power of the root, which motivates the notation\<close>

lemma pref_pow_ext_take: assumes "u \<le>p r\<^sup>@k" shows "u \<le>p take \<^bold>|r\<^bold>| u \<cdot> r\<^sup>@k"
proof (rule le_cases[of "\<^bold>|u\<^bold>|" "\<^bold>|r\<^bold>|"])
  assume "\<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>|"
  show "u \<le>p take \<^bold>|r\<^bold>| u \<cdot> r \<^sup>@ k"
    unfolding pref_take[OF pref_prod_long[OF pref_pow_ext'[OF \<open>u \<le>p r\<^sup>@k\<close>] \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>]]  using pref_pow_ext'[OF \<open>u \<le>p r\<^sup>@k\<close>].
qed simp

lemma pref_pow_take: assumes "u \<le>p r\<^sup>@k" shows "u \<le>p take \<^bold>|r\<^bold>| u \<cdot> u"
  using pref_prod_pref[of u "take \<^bold>|r\<^bold>| u" "r\<^sup>@k", OF pref_pow_ext_take \<open>u \<le>p r\<^sup>@k\<close>, OF \<open>u \<le>p r\<^sup>@k\<close>].


lemma per_root_powE: assumes "u <p r \<cdot> u"
  obtains k where "u <p r\<^sup>@k" and "0 < k"
  using pref_prod_less[OF per_exp_pref[OF sprefD1]
  long_pow_exp'[OF per_root_nemp], OF assms assms] by blast

thm per_rootI per_rootI'

lemma per_root_powE': assumes "x <p r \<cdot> x"
  obtains k where "x \<le>p r\<^sup>@k" and "0 < k"
  using per_root_powE[OF assms] sprefD1 by metis

lemma per_root_modE' [elim]: assumes "u <p r \<cdot> u"
  obtains p where "p <p r" and "r\<^sup>@(\<^bold>|u\<^bold>| div \<^bold>|r\<^bold>|) \<cdot> p = u"
proof-
  have "r \<noteq> \<epsilon>"
    using assms by blast
  obtain m where "u <p r\<^sup>@m"
    using per_root_powE[OF \<open>u <p r \<cdot> u\<close>].
  from pref_mod_pow[OF sprefD1[OF this] per_root_nemp[OF assms]]
  obtain k z where "k \<le> m" and "z <p r" and "r \<^sup>@ k \<cdot> z = u".
  have "k = (\<^bold>|u\<^bold>| div \<^bold>|r\<^bold>|)"
    using lenarg[OF \<open>r \<^sup>@ k \<cdot> z = u\<close>, unfolded lenmorph pow_len]
    get_div[OF prefix_length_less[OF \<open>z <p r\<close>]] by metis
  thus ?thesis
    using that \<open>r \<^sup>@ k \<cdot> z = u\<close> \<open>z <p r\<close> by blast
qed

lemma per_root_modE [elim]: assumes "u <p r \<cdot> u"
  obtains n p s where "p \<cdot> s = r" and "r\<^sup>@n \<cdot> p = u" and "s \<noteq> \<epsilon>"
  using per_root_modE'[OF assms] spref_exE by metis

    lemma nemp_per_root_conv: "r \<noteq> \<epsilon> \<Longrightarrow> u <p r \<cdot> u \<longleftrightarrow> u \<le>p r \<cdot> u"
   by force



lemma root_ruler: assumes "w <p u\<cdot>w" "v <p u\<cdot>v"
  shows "w \<bowtie> v"
proof-
  obtain k l where "w <p u\<^sup>@k" "v <p u\<^sup>@l"
    using assms per_root_powE by metis
  moreover have "u\<^sup>@k \<bowtie> u\<^sup>@l"
    using conjug_pow eqd_comp by metis
  ultimately show ?thesis
    by (rule ruler_comp[OF sprefD1 sprefD1])
qed

lemmas same_len_nemp_root_eq = root_ruler[THEN pref_comp_eq]







lemma per_root_add_exp: assumes "u <p r \<cdot> u" "0 < m" shows "u <p r\<^sup>@m \<cdot> u"
  using \<open>0 < m\<close>
proof (induct m)
    case (Suc m)
    then show ?case
      unfolding pow_Suc rassoc
      using spref_trans[OF \<open>u <p r \<cdot> u\<close>, of "r \<cdot> r \<^sup>@ m \<cdot> u"] \<open>u <p r \<cdot> u\<close>
      unfolding spref_cancel_conv by (cases "m = 0") simp_all
 qed simp

theorem per_root_pow_conv: "x <p r \<cdot> x \<longleftrightarrow> (\<exists> k. x \<le>p r\<^sup>@k) \<and> r \<noteq> \<epsilon>"
  by (rule iffI) (use per_root_powE' per_root_nemp in metis, use per_rootI' in blast)

lemma per_root_exp': assumes "x \<le>p r\<^sup>@k" shows "x \<le>p r\<^sup>@\<^bold>|x\<^bold>|"
proof(cases "r = \<epsilon>")
  assume "r \<noteq> \<epsilon>"
  have "\<^bold>|x\<^bold>| \<le> \<^bold>|r\<^sup>@\<^bold>|x\<^bold>|\<^bold>|"
    unfolding pow_len using nemp_le_len[OF \<open>r \<noteq> \<epsilon>\<close>] by force
  with pref_ext[OF \<open>x \<le>p r\<^sup>@k\<close>, of "r\<^sup>@\<^bold>|x\<^bold>|", unfolded pows_comm[of r k]]
  show ?thesis
    by blast
qed (use assms in force)

lemma per_root_exp: assumes "x <p r \<cdot> x" shows "x \<le>p r\<^sup>@\<^bold>|x\<^bold>|"
proof-
  obtain k where "x \<le>p r\<^sup>@k"
    using \<open>x <p r \<cdot> x\<close> unfolding per_root_pow_conv by blast
  from per_root_exp'[OF this]
  show "x \<le>p r\<^sup>@\<^bold>|x\<^bold>|".
qed

lemma per_root_drop_exp: "u <p (r\<^sup>@m) \<cdot> u  \<Longrightarrow> u <p r \<cdot> u"
  unfolding per_root_pow_conv unfolding pow_mult[symmetric]
  using emp_pow by blast

lemma per_root_exp_conv: "u <p (r\<^sup>@Suc m) \<cdot> u  \<longleftrightarrow> u <p r \<cdot> u"
  by (rule iffI) (use per_root_drop_exp in blast, use per_root_add_exp in blast)

lemma pref_drop_exp: assumes "x \<le>p z \<cdot> x\<^sup>@m" shows "x \<le>p z \<cdot> x"
  using assms pow_comm pref_prod_pref pref_prolong triv_pref by metis

lemma per_root_drop_exp': "x \<le>p r\<^sup>@(Suc k) \<cdot> x\<^sup>@m \<Longrightarrow>  x \<le>p  r \<cdot> x"
  using nemp_Suc_pow_nemp per_rootI per_root_drop_exp pref_drop_exp sprefD by metis

lemma per_drop_exp': "0 < k \<Longrightarrow> x \<le>p r\<^sup>@k \<cdot> x \<Longrightarrow> x \<le>p  r \<cdot> x"
  using  nonzero_pow_emp per_rootI per_root_drop_exp sprefD by metis

lemmas per_drop_exp_rev = per_drop_exp'[reversed]

corollary comm_drop_exp: assumes "0 < m" and "u \<cdot> r\<^sup>@m = r\<^sup>@m' \<cdot> u" shows "r \<cdot> u = u \<cdot> r"
proof
  assume "r \<noteq> \<epsilon>" "u \<noteq> \<epsilon>"
  hence "m = m'"
    using lenarg[OF \<open>u \<cdot> r\<^sup>@m = r\<^sup>@m' \<cdot> u\<close>] unfolding lenmorph pow_len
    by auto
  have "u\<cdot>r \<le>p u\<cdot>r\<^sup>@m"
    unfolding pow_pos[OF \<open>0 < m\<close>] by simp
    have "u\<cdot>r \<le>p r\<^sup>@m' \<cdot> u \<cdot> r"
      using pref_ext[of "u \<cdot> r" "r\<^sup>@m \<cdot> u" r, unfolded rassoc \<open>m = m'\<close>, OF  \<open>u\<cdot>r \<le>p u\<cdot>r\<^sup>@m\<close>[unfolded \<open>u \<cdot> r\<^sup>@m = r\<^sup>@m' \<cdot> u\<close>]].
    hence "u\<cdot>r \<le>p r\<cdot>(u\<cdot>r)"
      using per_root_drop_exp[of "u\<cdot>r" r m'] \<open>0 < m\<close>[unfolded \<open>m = m'\<close>] per_drop_exp' by blast
    from comm_ruler[OF self_pref[of "r \<cdot> u"], of "r \<cdot> u \<cdot> r", OF this]
    show "r \<cdot> u = u \<cdot> r"
      unfolding prefix_comparable_def
      by force
qed

lemma comm_drop_exp': assumes "u\<^sup>@k \<cdot> v = v \<cdot> u\<^sup>@k'" "0 < k'" shows "u \<cdot> v = v \<cdot> u"
  using  comm_drop_exp[OF \<open>0 < k'\<close> assms(1)[symmetric]].

lemma comm_drop_exps[elim]: assumes "u\<^sup>@m \<cdot> v\<^sup>@k = v\<^sup>@k \<cdot> u\<^sup>@m" and "0 < m" and "0 < k" shows "u \<cdot> v = v \<cdot> u"
  using comm_drop_exp[OF \<open>0 < k\<close> \<open>u\<^sup>@m \<cdot> v\<^sup>@k = v\<^sup>@k \<cdot> u\<^sup>@m\<close>] comm_drop_exp[OF \<open>0 < m\<close>, of v u m] by blast

lemma comm_pow_roots:
  assumes "0 < m" and "0 < k"
  shows "u\<^sup>@m \<cdot> v\<^sup>@k = v\<^sup>@k \<cdot> u\<^sup>@m \<longleftrightarrow> u \<cdot> v = v \<cdot> u"
  by (rule, use comm_drop_exps[OF _ assms] in blast)
  (use comm_add_exps in blast)

corollary pow_comm_comm: assumes "x\<^sup>@j = y\<^sup>@k" and "0 < j" shows "x\<cdot>y = y\<cdot>x"
  using  comm_drop_exp[OF \<open>0 < j\<close>, of y x j, unfolded \<open>x\<^sup>@j = y\<^sup>@k\<close>, OF pow_comm[symmetric]].


lemma pow_comm_comm': assumes comm: "u\<^sup>@(Suc k) = v\<^sup>@(Suc l)" shows "u \<cdot> v = v \<cdot> u"
  using comm pow_comm_comm by blast

lemma comm_trans: assumes uv: "u\<cdot>v =  v\<cdot>u" and vw: "w\<cdot>v = v\<cdot>w" and nemp: "v \<noteq> \<epsilon>" shows "u \<cdot> w = w \<cdot> u"
proof -
  consider (u_emp) "u = \<epsilon>" | (w_emp) "w = \<epsilon>" | (nemp') "u \<noteq> \<epsilon>" and "w \<noteq> \<epsilon>" by blast
  then show ?thesis proof (cases)
    case nemp'
    have eq: "u\<^sup>@(\<^bold>|v\<^bold>| * \<^bold>|w\<^bold>|) = w\<^sup>@(\<^bold>|v\<^bold>| * \<^bold>|u\<^bold>|)"
      unfolding pow_mult comm_common_power[OF uv] comm_common_power[OF vw]
      unfolding pow_mult[symmetric] mult.commute[of "\<^bold>|u\<^bold>|"]..
    obtain k l where k: "\<^bold>|v\<^bold>| * \<^bold>|w\<^bold>| = Suc k" and l: "\<^bold>|v\<^bold>| * \<^bold>|u\<^bold>| = Suc l"
      using nemp nemp' unfolding length_0_conv[symmetric]
      using not0_implies_Suc[OF no_zero_divisors]
      by presburger
    show ?thesis
      using pow_comm_comm'[OF eq[unfolded k l]].
  qed simp+
qed

lemma root_comm_root: assumes "x \<le>p u \<cdot> x" and "v \<cdot> u = u \<cdot> v" and "u \<noteq> \<epsilon>"
  shows "x \<le>p v \<cdot> x"
  using per_rootI[OF \<open>x \<le>p u\<cdot>x\<close> \<open>u \<noteq> \<epsilon>\<close>] per_exp_pref  commE[OF \<open>v \<cdot> u = u \<cdot> v\<close>] per_drop_exp'
   assms(1) assms(3) nemp_pow by metis


lemma drop_per_pref: assumes "w <p u \<cdot> w" shows "drop \<^bold>|u\<^bold>| w \<le>p w"
  using pref_drop[OF sprefD1[OF \<open>w <p u \<cdot> w\<close>], of "\<^bold>|u\<^bold>|", unfolded drop_pref[of u w]].

lemma per_root_trans[intro]: assumes "w <p u \<cdot> w" and "u \<in> t*" shows "w <p t \<cdot> w"
  using per_root_drop_exp rootE[OF \<open>u \<in> t*\<close>] \<open>w <p u \<cdot> w\<close> by metis

lemma per_root_trans'[intro]: "w \<le>p u \<cdot> w \<Longrightarrow> u \<in> r* \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> w \<le>p r \<cdot> w"
  using per_root_trans sprefD1 per_rootI by metis

lemmas per_root_trans_suf'[intro] = per_root_trans'[reversed]

text\<open>Note that
@{term "w <p u \<cdot> w \<Longrightarrow> u <p t \<cdot> u \<Longrightarrow> w <p t \<cdot> w"}
does not hold.
\<close>

lemma per_root_same_prefix:"w <p r \<cdot> w \<Longrightarrow> w' \<le>p r \<cdot> w' \<Longrightarrow>  w \<bowtie> w'"
  using root_ruler by auto

lemma take_after_drop:  "\<^bold>|u\<^bold>| + q \<le> \<^bold>|w\<^bold>| \<Longrightarrow> w <p u \<cdot> w \<Longrightarrow> take q (drop \<^bold>|u\<^bold>| w) = take q w"
  using pref_share_take[OF drop_per_pref[of w u] len_after_drop[of "\<^bold>|u\<^bold>|" q w]].

text\<open>The following lemmas are a weak version of the Periodicity lemma\<close>

lemma two_pers:
  assumes pu: "w \<le>p u \<cdot> w" and pv: "w \<le>p v \<cdot> w" and len: "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>|"
  shows "u \<cdot> v = v \<cdot> u"
proof-
  have uv: "w \<le>p (u \<cdot> v) \<cdot> w" using pref_prolong[OF pu pv] unfolding lassoc.
  have vu: "w \<le>p (v \<cdot> u) \<cdot> w" using pref_prolong[OF pv pu] unfolding lassoc.
  have "u \<cdot> v \<le>p w" using len pref_prod_long[OF uv] by simp
  moreover have "v \<cdot> u \<le>p w" using len pref_prod_long[OF vu] by simp
  ultimately show "u \<cdot> v = v \<cdot> u" by (rule pref_comp_eq[unfolded prefix_comparable_def, OF ruler swap_len])
qed

lemma two_pers_root: assumes "w <p u \<cdot> w" and  "w <p v \<cdot> w" and "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>|" shows "u\<cdot>v = v\<cdot>u"
  using two_pers[OF sprefD1[OF assms(1)] sprefD1[OF assms(2)] assms(3)].

subsection \<open>Maximal root-prefix\<close>

lemma max_root_mismatch: assumes "u \<cdot> [a] <p r \<cdot> u \<cdot> [a]" and "u \<cdot> [b] \<le>p w" and "a \<noteq> b"
  shows "w \<and>\<^sub>p r \<cdot> w = u"
proof (rule lcp_first_mismatch_pref[OF \<open>u \<cdot> [b] \<le>p w\<close> _ \<open>a \<noteq> b\<close>[symmetric]])
  have "u \<cdot> [a] \<le>p r \<cdot> u"
    using assms(1)[unfolded lassoc spref_snoc_iff].
  thus "u \<cdot> [a] \<le>p r \<cdot> w"
    using append_prefixD[OF \<open>u \<cdot> [b] \<le>p w\<close>] pref_prolong by blast
qed


lemma max_pref_per_root:  "u \<and>\<^sub>p r \<cdot> u \<le>p r \<cdot> (u \<and>\<^sub>p r \<cdot> u)"
  by (rule pref_prod_pref[of _ _ u]) force+

lemma max_pref_pref:
  assumes "r \<noteq> \<epsilon>"
  shows "u \<and>\<^sub>p r \<cdot> u \<le>p r\<^sup>@\<^bold>|u \<and>\<^sub>p r \<cdot> u\<^bold>|"
proof-
  have "u \<and>\<^sub>p r \<cdot> u <p r \<cdot> (u \<and>\<^sub>p r \<cdot> u)"
    using assms max_pref_per_root by auto
  from per_root_exp[OF this]
  show ?thesis.
qed


lemma max_pref_lcp_root_pow: assumes "r \<noteq> \<epsilon>" and "\<^bold>|u \<and>\<^sub>p r \<cdot> u\<^bold>| \<le> k"
  shows "u \<and>\<^sub>p r \<cdot> u = u \<and>\<^sub>p r\<^sup>@k" (is "?max = u \<and>\<^sub>p r\<^sup>@k")
proof (rule pref_antisym)
  from max_pref_pref[OF assms(1)] le_exps_pref[OF assms(2)]
  have "?max \<le>p r\<^sup>@k"
    using pref_trans by blast
  thus "?max \<le>p u \<and>\<^sub>p r\<^sup>@k"
    by force
  show "u \<and>\<^sub>p r\<^sup>@k \<le>p ?max"
  proof (rule lcp.boundedI, force)
    show "u \<and>\<^sub>p r \<^sup>@ k \<le>p r \<cdot> u"
    proof (rule pref_prolong)
      show "u \<and>\<^sub>p r \<^sup>@ k \<le>p r \<cdot> (u \<and>\<^sub>p r \<^sup>@ k)"
        using  lcp.cobounded2  by (rule pref_prod_root[of "u \<and>\<^sub>p r\<^sup>@k"])
      show "u \<and>\<^sub>p r \<^sup>@ k \<le>p u"
        using lcp.cobounded1.
    qed
  qed
qed

lemma max_pref_shorter_lcp: assumes "u \<and>\<^sub>p r \<cdot> u <p v \<and>\<^sub>p r \<cdot> v"
  shows "u \<and>\<^sub>p v = u \<and>\<^sub>p r \<cdot> u"
proof (cases)
  assume "r = \<epsilon>"
  then show ?thesis
  using assms by (clarify, unfold emp_simps lcp.idem) (use lcp.absorb3 in blast)
next
  let ?u = "u \<and>\<^sub>p r \<cdot> u" and ?v = "v \<and>\<^sub>p r \<cdot> v"
  assume "r \<noteq> \<epsilon>"
  from max_pref_lcp_root_pow[OF this]
  obtain k where "?u = u \<and>\<^sub>p r\<^sup>@k" and "?v = v \<and>\<^sub>p r\<^sup>@k"
    using pref_len' suf_len' by meson
  from ruler_spref_lcp[OF assms[unfolded this], folded \<open>?u = u \<and>\<^sub>p r\<^sup>@k\<close>]
  show "u \<and>\<^sub>p v = u \<and>\<^sub>p r \<cdot> u".
qed


find_theorems "?u \<and>\<^sub>p ?r \<cdot> ?u"


subsection "Period - numeric"

text\<open>Definition of a period as the length of the periodic root is often offered as the basic one. From our point of view,
it is secondary, and less convenient for reasoning.\<close>

definition period :: "'a list \<Rightarrow> nat \<Rightarrow> bool"
  where [simp]: "period w n \<equiv> w <p (take n w) \<cdot> w"

lemma period_I': "w \<noteq> \<epsilon> \<Longrightarrow> 0 < n \<Longrightarrow> w \<le>p (take n w) \<cdot> w \<Longrightarrow> period w n"
  unfolding period_def  by fastforce

lemma periodI[intro]: "w \<noteq> \<epsilon> \<Longrightarrow> w <p r \<cdot> w \<Longrightarrow> period w \<^bold>|r\<^bold>|"
  by (elim period_I'[of _ "\<^bold>|r\<^bold>|", OF _ nemp_pos_len])
     (blast, use pref_pow_take per_root_powE' in metis)

text\<open>The numeric definition respects the following convention about empty words and empty periods.\<close>

lemma emp_no_period: "\<not> period \<epsilon> n"
  by simp

lemma "\<not> period w 0"
  by simp



lemma per_nemp: "period w n \<Longrightarrow>  w \<noteq> \<epsilon>"
  by simp

lemma per_not_zero: "period w n \<Longrightarrow>  0 < n"
  by simp

lemma per_pref: "period w n \<Longrightarrow>  w \<le>p take n w \<cdot> w"
  by simp

text\<open>A nonempty word has all "long" periods\<close>

lemma all_long_pers: "\<lbrakk> w \<noteq> \<epsilon>; \<^bold>|w\<^bold>| \<le> n \<rbrakk> \<Longrightarrow> period w n"
  by simp

lemma len_is_per: "w \<noteq> \<epsilon> \<Longrightarrow> period w \<^bold>|w\<^bold>|"
  by simp

text\<open>The standard numeric definition of a period uses indeces.\<close>

lemma period_indeces: assumes "period w n" and "i + n < \<^bold>|w\<^bold>|" shows "w!i = w!(i+n)"
proof-
  have "w ! i = (take n w \<cdot> w) ! (n + i)"
    using nth_append_length_plus[of "take n w" w i, symmetric]
    unfolding take_len[OF less_imp_le[OF add_lessD2[OF \<open>i + n < \<^bold>|w\<^bold>|\<close>]]].
  also have "... = w ! (i + n)"
    using pref_index[OF per_pref[OF \<open>period w n\<close>] \<open>i + n < \<^bold>|w\<^bold>|\<close>, symmetric] unfolding add.commute[of n i].
  finally show ?thesis.
qed

lemma indeces_period:
  assumes  "w \<noteq> \<epsilon>" and "0 < n" and  forall: "\<And> i. i + n < \<^bold>|w\<^bold>| \<Longrightarrow> w!i = w!(i+n)"
  shows "period w n"
proof-
  have "\<^bold>|w\<^bold>| \<le> \<^bold>|take n w \<cdot> w\<^bold>|"
    by auto
  {fix j assume "j < \<^bold>|w\<^bold>|"
    have "w ! j = (take n w \<cdot> w) ! j"
    proof (cases "j < \<^bold>|take n w\<^bold>|")
      assume "j < \<^bold>|take n w\<^bold>|" show "w ! j = (take n w \<cdot> w) ! j"
        using pref_index[OF take_is_prefix \<open>j < \<^bold>|take n w\<^bold>|\<close>, symmetric]
        unfolding pref_index[OF triv_pref \<open>j < \<^bold>|take n w\<^bold>|\<close>, of w].
    next
      assume "\<not> j < \<^bold>|take n w\<^bold>|"
      from leI[OF this] \<open>j < \<^bold>|w\<^bold>|\<close>
      have "\<^bold>|take n w\<^bold>| = n"
        by force
      hence "j = (j - n) + n" and "(j - n) + n < \<^bold>|w\<^bold>|"
        using  leI[OF \<open>\<not> j < \<^bold>|take n w\<^bold>|\<close>] \<open>j < \<^bold>|w\<^bold>|\<close> by simp+
      hence "w!j = w!(j - n)"
        using forall by simp
      from this[folded nth_append_length_plus[of "take n w" w "j-n", unfolded \<open>\<^bold>|take n w\<^bold>| = n\<close>]]
      show "w ! j = (take n w \<cdot> w) ! j"
        using \<open>j = (j - n) + n\<close> by simp
    qed}
  with index_pref[OF \<open>\<^bold>|w\<^bold>| \<le> \<^bold>|take n w \<cdot> w\<^bold>|\<close>]
  have "w \<le>p take n w \<cdot> w" by blast
  thus ?thesis
    using assms by force
qed

text\<open>In some cases, the numeric definition is more useful than the definition using the period root.\<close>

lemma period_rev: assumes "period w p" shows "period (rev w) p"
proof (rule indeces_period[of "rev w" p, OF _ per_not_zero[OF assms]])
  show "rev w \<noteq> \<epsilon>"
    using assms[unfolded period_def] by force
next
  fix i assume "i + p < \<^bold>|rev w\<^bold>|"
  from this[unfolded length_rev] add_lessD1
  have "i < \<^bold>|w\<^bold>|" and "i + p < \<^bold>|w\<^bold>|" by blast+
  have e: "\<^bold>|w\<^bold>| - Suc (i + p) + p = \<^bold>|w\<^bold>| - Suc i" using \<open>i + p < \<^bold>|rev w\<^bold>|\<close> by simp
  have "\<^bold>|w\<^bold>| - Suc (i + p) + p < \<^bold>|w\<^bold>|"
    using \<open>i + p < \<^bold>|w\<^bold>|\<close> Suc_diff_Suc \<open>i < \<^bold>|w\<^bold>|\<close>
      diff_less_Suc e less_irrefl_nat not_less_less_Suc_eq by metis
  from period_indeces[OF assms this] rev_nth[OF \<open>i  < \<^bold>|w\<^bold>|\<close>, folded e] rev_nth[OF \<open>i + p < \<^bold>|w\<^bold>|\<close>]
  show "rev w ! i = rev w !(i+p)" by presburger
qed

lemma period_rev_conv [reversal_rule]: "period (rev w) n \<longleftrightarrow> period w n"
  using period_rev period_rev[of "rev w"] unfolding rev_rev_ident by (intro iffI)

lemma period_fac: assumes "period (u\<cdot>w\<cdot>v) p" and "w \<noteq> \<epsilon>"
  shows "period w p"
proof (rule indeces_period)
  show "0 < p" using per_not_zero[OF \<open>period (u\<cdot>w\<cdot>v) p\<close>].
  fix i assume "i + p < \<^bold>|w\<^bold>|"
  hence "\<^bold>|u\<^bold>| + i + p  < \<^bold>|u\<cdot>w\<cdot>v\<^bold>|"
    by simp
  from period_indeces[OF \<open>period (u\<cdot>w\<cdot>v) p\<close> this]
  have "(u\<cdot>w\<cdot>v)!(\<^bold>|u\<^bold>| + i) = (u\<cdot>w\<cdot>v)! (\<^bold>|u\<^bold>| + (i + p))"
    by (simp add: add.assoc)
  thus "w!i = w!(i+p)"
    using nth_append_length_plus[of u "w\<cdot>v" i, unfolded lassoc] \<open>i + p < \<^bold>|w\<^bold>|\<close> add_lessD1[OF \<open>i + p < \<^bold>|w\<^bold>|\<close>]
      nth_append[of w v] by auto
qed (simp add: \<open>w \<noteq> \<epsilon>\<close>)

lemma period_fac': "period v p \<Longrightarrow> u \<le>f v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> period u p"
  by (elim facE, hypsubst, rule period_fac)

lemma pow_per[intro]: assumes "y \<noteq> \<epsilon>" and "0 < k" shows "period (y\<^sup>@k) \<^bold>|y\<^bold>|"
  using period_I'[OF _ nemp_pos_len[OF \<open>y \<noteq> \<epsilon>\<close>] pref_pow_ext_take, OF _ self_pref]
  assms by blast

lemma per_fac: assumes "w \<noteq> \<epsilon>" and "w \<le>f y\<^sup>@k" shows "period w \<^bold>|y\<^bold>|"
proof-
  have "y \<noteq> \<epsilon>"
    using assms  by force
  have "0 < k"
    using assms nemp_exp_pos sublist_Nil_right by metis
  from pow_per[OF \<open>y \<noteq> \<epsilon>\<close> this] period_fac  facE[OF \<open>w \<le>f y\<^sup>@k\<close>] \<open>w \<noteq> \<epsilon>\<close>
  show "period w \<^bold>|y\<^bold>|" by metis
qed

text\<open>The numeric definition is equivalent to being prefix of a power.\<close>

theorem period_pref: "period w n \<longleftrightarrow> (\<exists>k r. w \<le>np r\<^sup>@k \<and> \<^bold>|r\<^bold>| = n)" (is "_ \<longleftrightarrow> ?R")
proof(cases "w = \<epsilon>")
  assume "w \<noteq> \<epsilon>"
  show "period w n \<longleftrightarrow> ?R"
  proof
    assume "period w n"
    consider (short) "\<^bold>|w\<^bold>| \<le> n" |  (long) "n < \<^bold>|w\<^bold>|"
      by linarith
    then show ?R
    proof(cases)
      assume "\<^bold>|w\<^bold>| \<le> n"
      from le_add_diff_inverse[OF this]
      obtain z where "\<^bold>|w \<cdot> z\<^bold>| = n"
        unfolding lenmorph using exE[OF Ex_list_of_length[of "n - \<^bold>|w\<^bold>|"]] by metis
      thus ?R
        using  pow_1 npI'[OF \<open>w \<noteq> \<epsilon>\<close>] by metis
    next
      assume "n < \<^bold>|w\<^bold>|"
      then show ?R
        unfolding nonempty_prefix_def
        using \<open>w \<noteq> \<epsilon>\<close> take_len[OF less_imp_le[OF \<open>n < \<^bold>|w\<^bold>|\<close>]]
        per_root_powE[OF \<open>period w n\<close>[unfolded period_def]]
        sprefD1 by metis
    qed
  next
    assume ?R
    then obtain k r where "w \<le>np r\<^sup>@k" and "n = \<^bold>|r\<^bold>|" by blast
    have "w \<le>p take n w \<cdot> w"
      using  pref_pow_take[OF npD[OF \<open>w \<le>np r \<^sup>@ k\<close>], folded \<open>n = \<^bold>|r\<^bold>|\<close>].
    have "n \<noteq> 0"
      unfolding length_0_conv[of r, folded \<open>n = \<^bold>|r\<^bold>|\<close>] using \<open>w \<le>np r \<^sup>@ k\<close> by force
    hence "take n w \<noteq> \<epsilon>"
      unfolding \<open>n = \<^bold>|r\<^bold>|\<close> using \<open>w \<noteq> \<epsilon>\<close> by simp
    thus "period w n"
      unfolding period_def using \<open>w \<le>p take n w \<cdot> w\<close> by blast
  qed
qed simp

text \<open>Two more characterizations of a period\<close>

theorem per_shift: assumes "w \<noteq> \<epsilon>" "0 < n"
  shows "period w n \<longleftrightarrow> drop n w \<le>p w"
proof
  assume "period w n" show "drop n w \<le>p w"
    using drop_per_pref[OF \<open>period w n\<close>[unfolded period_def]]
      append_take_drop_id[of n w, unfolded append_eq_conv_conj] by argo
next
  assume "drop n w \<le>p w"
  show "period w n"
    using conjI[OF pref_cancel'[OF \<open>drop n w \<le>p w\<close>, of "take n w"] take_nemp[OF \<open>w \<noteq> \<epsilon>\<close> \<open>0 < n\<close>]]
    unfolding  append_take_drop_id  by force
qed

lemma rotate_per_root: assumes "w \<noteq> \<epsilon>" and "0 < n" and "w = rotate n w"
  shows "period w n"
proof (cases "\<^bold>|w\<^bold>| \<le> n")
  assume "\<^bold>|w\<^bold>| \<le> n"
  from all_long_pers[OF \<open>w \<noteq> \<epsilon>\<close>, OF this]
  show "period w n".
next
  assume not: "\<not> \<^bold>|w\<^bold>| \<le> n"
  have "drop (n mod \<^bold>|w\<^bold>|) w \<le>p w"
    using prefI[OF rotate_drop_take[symmetric, of n w]]
    unfolding \<open>w = rotate n w\<close>[symmetric].
  from per_shift[OF \<open>w \<noteq> \<epsilon>\<close> \<open>0 < n\<close>] this[unfolded mod_less[OF not[unfolded not_le]]]
  show "period w n"..
qed

subsubsection \<open>Various lemmas on periods\<close>

lemma period_drop: assumes "period w p" and "p < \<^bold>|w\<^bold>|"
  shows "period (drop p w) p"
  using period_fac[of "take p w" "drop p w" \<epsilon> p] \<open>p < \<^bold>|w\<^bold>|\<close> \<open>period w p\<close>
  unfolding append_take_drop_id drop_eq_Nil not_le append_Nil2 by blast

lemma ext_per_left: assumes "period w p" and  "p \<le> \<^bold>|w\<^bold>|"
  shows "period (take p w \<cdot> w) p"
proof-
  have f: "take p (take p w \<cdot> w) = take p w"
    using \<open>p \<le> \<^bold>|w\<^bold>|\<close> by simp
  show ?thesis
    using  \<open>period w p\<close> pref_cancel'[of w "take p w \<cdot> w" "take p w" ]
    unfolding f period_def
    by blast
qed

lemma ext_per_left_power: "period w p \<Longrightarrow> p \<le> \<^bold>|w\<^bold>| \<Longrightarrow> period ((take p w)\<^sup>@k \<cdot> w) p"
proof (induction k)
  case (Suc k)
  show ?case
    using ext_per_left[OF Suc.IH[OF \<open>period w p\<close> \<open>p \<le> \<^bold>|w\<^bold>|\<close>]] \<open>p \<le> \<^bold>|w\<^bold>|\<close>
    unfolding pref_share_take[OF per_exp_pref[OF per_pref[OF \<open>period w p\<close>]] \<open>p \<le> \<^bold>|w\<^bold>|\<close>,symmetric]
      lassoc pow_Suc[symmetric] by fastforce
qed auto

lemma take_several_pers: assumes "period w n" and "m*n \<le> \<^bold>|w\<^bold>|"
  shows "(take n w)\<^sup>@m = take (m*n) w"
proof (cases "m = 0")
  assume "m \<noteq> 0"
  have "\<^bold>|(take n w)\<^sup>@m\<^bold>| = m*n"
    unfolding pow_len nat_prod_le[OF \<open>m \<noteq> 0\<close> \<open>m*n \<le> \<^bold>|w\<^bold>|\<close>, THEN take_len] by blast
  have "(take n w)\<^sup>@m \<le>p w"
    using  \<open>period w n\<close>[unfolded period_def]
        ruler_le[of "take n w\<^sup>@m" "take n w\<^sup>@m \<cdot> w" w, OF triv_pref] \<open>m * n \<le> \<^bold>|w\<^bold>|\<close>[folded \<open>\<^bold>|take n w\<^sup>@m\<^bold>| = m * n\<close>]
        per_exp_pref sprefD by metis
  show ?thesis
    using pref_take[OF \<open>take n w\<^sup>@m \<le>p w\<close>, unfolded  \<open>\<^bold>|take n w\<^sup>@m\<^bold>| = m * n\<close>, symmetric].
qed simp

lemma per_div: assumes "n dvd \<^bold>|w\<^bold>|" and "period w n"
  shows "(take n w)\<^sup>@(\<^bold>|w\<^bold>| div n) = w"
  using take_several_pers[OF \<open>period w n\<close> div_times_less_eq_dividend] unfolding dvd_div_mult_self[OF \<open>n dvd \<^bold>|w\<^bold>|\<close>] take_self.

lemma per_mult: assumes "period w n" and "0 < m" shows "period w (m*n)"
proof (cases "m*n \<le> \<^bold>|w\<^bold>|")
  have "w \<noteq> \<epsilon>" using per_nemp[OF \<open>period w n\<close>].
  assume "\<not> m * n \<le> \<^bold>|w\<^bold>|" thus "period w (m*n)"
    using all_long_pers[of  w "m * n", OF \<open>w \<noteq> \<epsilon>\<close>] by linarith
next
  assume "m * n \<le> \<^bold>|w\<^bold>|"
  show "period w (m*n)"
    using  \<open>period w n\<close>
    unfolding period_def
    using per_root_add_exp[of w "take n w"] \<open>0 < m\<close>
     take_several_pers[OF \<open>period w n\<close> \<open>m*n \<le> \<^bold>|w\<^bold>|\<close>, symmetric]
    by presburger
qed


theorem  two_periods:
  assumes "period w p" "period w q"  "p + q \<le> \<^bold>|w\<^bold>|"
  shows "period w (gcd p q)"
proof-
  obtain t where "take p w \<in> t*" "take q w \<in> t*"
    using two_pers_root[OF \<open>period w p\<close>[unfolded period_def] \<open>period w q\<close>[unfolded period_def],
        unfolded take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]] take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]],
        OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>, unfolded comm_root[of "take p w" "take q w"]] by blast
  hence "w <p t \<cdot> w"
    using \<open>period w p\<close> period_def per_root_trans by blast
  have "period w \<^bold>|t\<^bold>|"
    using  periodI[OF  per_nemp[OF \<open>period w p\<close>] \<open>w <p t \<cdot> w\<close>].
  have "\<^bold>|t\<^bold>| dvd (gcd p q)"
    using gcd_nat.boundedI[OF root_len_dvd[OF \<open>take p w \<in> t*\<close>] root_len_dvd[OF \<open>take q w \<in> t*\<close>]]
    unfolding take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]] take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]].
  from dvd_div_eq_0_iff[OF this]
  have "0 < gcd p q div \<^bold>|t\<^bold>|"
    using per_not_zero[OF \<open>period w p\<close>] unfolding  gcd_nat.eq_neutr_iff by blast
  from per_mult[OF \<open>period w \<^bold>|t\<^bold>|\<close> this]
  show ?thesis
    unfolding dvd_div_mult_self[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>].
qed

lemma index_mod_per_root: assumes "r \<noteq> \<epsilon>" and i: "\<forall> i < \<^bold>|w\<^bold>|. w!i = r!(i mod \<^bold>|r\<^bold>|)" shows  "w <p r \<cdot> w"
proof-
  have "i < \<^bold>|w\<^bold>| \<Longrightarrow> (r \<cdot> w) ! i = r ! (i mod \<^bold>|r\<^bold>|)" for i
    by (simp add: i mod_if nth_append)
  hence "w \<le>p r \<cdot> w"
    using index_pref[of w "r \<cdot> w"] i
    by simp
  thus ?thesis  using \<open>r \<noteq> \<epsilon>\<close> by auto
qed

lemma index_pref_pow_mod: "w \<le>p r\<^sup>@k \<Longrightarrow> i < \<^bold>|w\<^bold>| \<Longrightarrow>  w!i = r!(i mod \<^bold>|r\<^bold>| )"
  using  index_pow_mod[of i r k] less_le_trans[of i "\<^bold>|w\<^bold>|" "\<^bold>|r\<^sup>@k\<^bold>|"] prefix_length_le[of w "r\<^sup>@k"] pref_index[of w "r\<^sup>@k" i] by argo

lemma index_per_root_mod: "w <p r \<cdot> w \<Longrightarrow> i < \<^bold>|w\<^bold>| \<Longrightarrow>  w!i = r!(i mod \<^bold>|r\<^bold>|)"
  using index_pref_pow_mod[of w r _ i] per_root_powE' by metis

lemma root_divisor: assumes "period w k" and  "k dvd \<^bold>|w\<^bold>|" shows "w \<in> (take k w)*"
  using rootI[of "take k w" "(\<^bold>|w\<^bold>| div k)"] unfolding
    take_several_pers[OF \<open>period w k\<close>, of "\<^bold>|w\<^bold>| div k", unfolded dvd_div_mult_self[OF \<open>k dvd \<^bold>|w\<^bold>|\<close>] take_self, OF , OF order_refl].

lemma per_pref': assumes "u \<noteq> \<epsilon>" and "period v k" and  "u \<le>p v" shows "period u k"
proof-
  { assume "k \<le> \<^bold>|u\<^bold>|"
    have "take k v = take k u"
      using  pref_share_take[OF \<open>u \<le>p v\<close> \<open>k \<le> \<^bold>|u\<^bold>|\<close>]  by auto
    hence "take k v \<noteq> \<epsilon>"
      using \<open>period v k\<close> by auto
    hence "take k u \<noteq> \<epsilon>"
      by (simp add: \<open>take k v = take k u\<close>)
    have "u \<le>p take k u \<cdot> v"
      using  \<open>period v k\<close>
      unfolding period_def   \<open>take k v = take k u\<close>
      using pref_trans[OF \<open>u \<le>p v\<close>, of "take k u \<cdot> v"]
      by blast
    hence "u \<le>p take k u \<cdot> u"
      using \<open>u \<le>p v\<close> pref_prod_pref by blast
    hence ?thesis
      using \<open>take k u \<noteq> \<epsilon>\<close> period_def by blast
  }
  thus ?thesis
    using \<open>u \<noteq> \<epsilon>\<close> all_long_pers nat_le_linear by blast
qed

subsection "Period: overview"
notepad
begin
  fix w r::"'a list"
  fix n::nat
  assume "w \<noteq> \<epsilon>" "r \<noteq> \<epsilon>" "0 < n"
  have "\<not> w <p \<epsilon> \<cdot> w"
    by simp
  have "\<not> \<epsilon> <p \<epsilon> \<cdot> \<epsilon>"
    by simp
  have "\<epsilon> <p r \<cdot> \<epsilon>"
    using \<open>r \<noteq> \<epsilon>\<close> by blast
  have "\<not> period w 0"
    by simp
  have "\<not> period \<epsilon> 0"
    by simp
  have "\<not> period \<epsilon> n"
    by simp
end

subsection \<open>Singleton and its power\<close>

primrec letter_pref_exp :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "letter_pref_exp \<epsilon> a = 0" |
  "letter_pref_exp (b # xs) a = (if b \<noteq> a then 0 else Suc (letter_pref_exp xs a))"

definition letter_suf_exp :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "letter_suf_exp w a = letter_pref_exp (rev w) a"

lemma concat_len_one: assumes "\<^bold>|us\<^bold>| = 1" shows "concat us = hd us"
  using concat_sing[OF sing_word[OF \<open>\<^bold>|us\<^bold>| = 1\<close>, symmetric]].

lemma sing_pow_hd_tl: "c # w \<in> [a]* \<longleftrightarrow> c = a \<and> w \<in> [a]*"
proof
  assume "c = a \<and> w \<in> [a]*"
  thus "c # w \<in> [a]*"
    unfolding  hd_word[of _ w]  using add_root[of "[c]" w] by simp
next
  assume "c # w \<in> [a]*"
  then obtain k where "[a]\<^sup>@k = c # w" unfolding root_def by blast
  thus "c = a \<and> w \<in> [a]*"
  proof (cases "0 < k")
    assume "[a] \<^sup>@ k = c # w" and "0 < k"
    from eqd_eq[of "[a]", OF this(1)[unfolded hd_word[of _ w] pow_pos[OF \<open>0 < k\<close>]]]
    show ?thesis
      unfolding root_def by auto
  qed simp
qed

lemma pref_sing_pow: assumes "w \<le>p [a]\<^sup>@m" shows "w = [a]\<^sup>@(\<^bold>|w\<^bold>|)"
proof-
  have  "[a]\<^sup>@m = [a]\<^sup>@(\<^bold>|w\<^bold>|)\<cdot>[a]\<^sup>@(m-\<^bold>|w\<^bold>|)"
    using pop_pow[OF prefix_length_le[OF assms, unfolded sing_pow_len], of "[a]", symmetric].
  show ?thesis
    using  eqd_eq(1)[of w "w\<inverse>\<^sup>>[a]\<^sup>@m" "[a]\<^sup>@(\<^bold>|w\<^bold>|)""[a]\<^sup>@(m-\<^bold>|w\<^bold>|)",
          unfolded lq_pref[OF assms] sing_pow_len,
          OF \<open>[a]\<^sup>@m = [a]\<^sup>@(\<^bold>|w\<^bold>|)\<cdot>[a]\<^sup>@(m-\<^bold>|w\<^bold>|)\<close> refl].
qed

lemma sing_pow_palindrom: assumes "w = [a]\<^sup>@k" shows "rev w = w"
  using rev_pow[of "[a]" "\<^bold>|w\<^bold>|", unfolded rev_sing]
  unfolding pref_sing_pow[of w a k, unfolded assms[unfolded root_def, symmetric], OF self_pref, symmetric].

lemma suf_sing_power: assumes "w \<le>s [a]\<^sup>@m" shows "w \<in> [a]*"
  using sing_pow_palindrom[of "rev w" a "\<^bold>|rev w\<^bold>|", unfolded rev_rev_ident]
    pref_sing_pow[of "rev w" a m, OF \<open>w \<le>s [a]\<^sup>@m\<close>[unfolded suffix_to_prefix rev_pow rev_rev_ident rev_sing]]
    rootI[of "[a]" "\<^bold>|rev w\<^bold>|"]  by auto

lemma sing_fac_pow: assumes "w \<in> [a]*" and  "v \<le>f w" shows "v \<in> [a]*"
proof-
  obtain k where "w = [a]\<^sup>@k" using \<open>w \<in> [a]*\<close>[unfolded root_def] by blast
  obtain p where "p \<le>p w" and "v \<le>s p"
    using fac_pref_suf[OF \<open> v \<le>f w\<close>] by blast
  hence "v \<le>s [a]\<^sup>@ \<^bold>|p\<^bold>|"
    using pref_sing_pow[OF \<open>p \<le>p w\<close>[unfolded \<open>w = [a]\<^sup>@k\<close>]] by argo
  from suf_sing_power[OF this]
  show ?thesis.
qed

lemma sing_pow_fac': assumes "a \<noteq> b" and  "w \<in> [a]*" shows "\<not> ([b] \<le>f w)"
  using sing_fac_pow[OF \<open> w \<in> [a]*\<close>, of "[b]"] unfolding sing_pow_hd_tl[of b \<epsilon>]
  using \<open>a \<noteq> b\<close> by auto

lemma all_set_sing_pow: "(\<forall> b. b \<in> set w \<longrightarrow> b = a) \<longleftrightarrow> w \<in> [a]*" (is "?All \<longleftrightarrow> _")
proof
  assume ?All
  then show "w \<in> [a]*"
  proof (induct w)
    case (Cons c w)
    then show ?case
      by (simp add: sing_pow_hd_tl)
  qed simp
next
  assume "w \<in> [a]*"
  then show ?All
  proof (induct w)
    case (Cons c w)
    then show ?case
      unfolding sing_pow_hd_tl by simp
  qed simp
qed

lemma sing_fac_set: "[a] \<le>f x \<Longrightarrow> a \<in> set x"
  by fastforce

lemma set_sing_pow_hd [simp]: assumes "0 < k" shows "a \<in> set ([a]\<^sup>@k)"
  using assms gr0_conv_Suc by force

lemma neq_set_not_root: "a \<noteq> b \<Longrightarrow> b \<in> set x \<Longrightarrow> x \<notin> [a]*"
  using all_set_sing_pow by metis

lemma sing_pow_set_Suc[simp]: "set ([a]\<^sup>@Suc k) = {a}"
  by (induct k, simp_all)

lemma sing_pow_set[simp]: assumes "0 < k" shows "set ([a]\<^sup>@k) = {a}"
  using sing_pow_set_Suc[of _ "k-1", unfolded Suc_minus_pos[OF assms]].

lemma sing_pow_set_sub: "set ([a]\<^sup>@k) \<subseteq> {a}"
  by (induct k, simp_all)

lemma unique_letter_fac_expE: assumes "w \<le>f [a]\<^sup>@k"
  obtains m where "w = [a]\<^sup>@m"
  using unique_letter_wordE''[OF subset_trans[OF set_mono_sublist[OF assms] sing_pow_set_sub]] by blast


lemma neq_in_set_not_pow: "a \<noteq> b \<Longrightarrow> b \<in> set x \<Longrightarrow> x \<noteq> [a]\<^sup>@k"
  by (cases "0 < k", use sing_pow_set singleton_iff in metis) force

lemma sing_pow_card_set_Suc: assumes "c = [a]\<^sup>@Suc k" shows "card(set c) = 1"
proof-
  have "card {a} = 1" by simp
  from this[folded sing_pow_set_Suc[of a k]]
  show "card(set c) = 1"
    unfolding assms.
qed

lemma sing_pow_card_set:  assumes "k \<noteq> 0" and "c = [a]\<^sup>@k" shows "card(set c) = 1"
  using sing_pow_card_set_Suc[of c a "k - 1", unfolded Suc_minus[OF \<open>k \<noteq> 0\<close>], OF \<open>c = [a]\<^sup>@k\<close>].

lemma sing_pow_set': "u \<in> [a]* \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> set u = {a}"
  unfolding all_set_sing_pow[symmetric]
  using lists_hd_in_set[of u] is_singletonI'[unfolded is_singleton_the_elem, of "set u"]
    singleton_iff[of a "the_elem (set u)"]
  by auto

lemma root_sing_set_iff: "u \<in> [a]* \<longleftrightarrow> set u \<subseteq> {a}"
  by (rule, use sing_pow_set'[of u a, folded set_empty2] in force, use all_set_sing_pow[of u a] in force)

lemma letter_pref_exp_hd: "u \<noteq> \<epsilon> \<Longrightarrow> hd u = a \<Longrightarrow> letter_pref_exp u a \<noteq> 0"
  by (induct u, auto)


lemma letter_pref_exp_pref: "[a]\<^sup>@(letter_pref_exp w a) \<le>p w "
  by(induct w, simp, simp)

lemma letter_pref_exp_Suc: "\<not> [a]\<^sup>@(Suc (letter_pref_exp w a)) \<le>p w "
  by (induct w, simp_all add: prefix_def)

lemma takeWhile_letter_pref_exp: "takeWhile (\<lambda>x. x = a) w =[a]\<^sup>@(letter_pref_exp w a)"
  by (induct w, simp, simp)

lemma concat_takeWhile_sing: "concat (takeWhile (\<lambda> x. x = u) ws) = u\<^sup>@\<^bold>|takeWhile (\<lambda> x. x = u) ws\<^bold>|"
  unfolding takeWhile_letter_pref_exp  concat_sing_pow  sing_pow_len ..

lemma dropWhile_distinct: assumes "w \<noteq> [a]\<^sup>@(letter_pref_exp w a)"
  shows "[a]\<^sup>@(letter_pref_exp w a)\<cdot>[hd (dropWhile (\<lambda>x. x = a) w)] \<le>p w"
proof-
  have nemp: "dropWhile (\<lambda>x. x = a) w \<noteq> \<epsilon>"
    using takeWhile_dropWhile_id[of "\<lambda>x. x = a" w, unfolded  takeWhile_letter_pref_exp] \<open>w \<noteq> [a]\<^sup>@(letter_pref_exp w a)\<close>
    by force
  from takeWhile_dropWhile_id[of "\<lambda>x. x = a" w, unfolded takeWhile_letter_pref_exp]
  have "[a]\<^sup>@(letter_pref_exp w a)\<cdot>[hd (dropWhile (\<lambda>x. x = a) w)]\<cdot> tl (dropWhile (\<lambda>x. x = a) w) = w"
    unfolding hd_tl[OF nemp].
  thus ?thesis
    unfolding lassoc using triv_pref by blast
qed

lemma letter_pref_exp_mismatch: "u = [a]\<^sup>@letter_pref_exp u a \<cdot> v \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> hd v \<noteq> a"
  using hd_pref letter_pref_exp_Suc[unfolded pow_Suc'] same_prefix_prefix by metis

lemma takeWhile_sing_root: "takeWhile (\<lambda> x. x = a) w \<in> [a]*"
  unfolding all_set_sing_pow[symmetric] using set_takeWhileD[of _ "\<lambda> x. x = a" w] by blast

lemma takeWhile_sing_pow: "takeWhile (\<lambda> x. x = a) w = w \<longleftrightarrow> w = [a]\<^sup>@\<^bold>|w\<^bold>|"
  by(induct w,  auto)

lemma dropWhile_sing_pow: "dropWhile (\<lambda> x. x = a) w = \<epsilon> \<longleftrightarrow> w = [a]\<^sup>@\<^bold>|w\<^bold>|"
  by(induct w,  auto)

lemma nemp_takeWhile_hd: "us \<noteq> \<epsilon> \<Longrightarrow> hd (takeWhile (\<lambda> a. a = hd us) us) = hd us"
  by (simp add: pref_hd_eq takeWhile_eq_Nil_iff takeWhile_is_prefix)

lemma nemp_takeWhile_last: "us \<noteq> \<epsilon> \<Longrightarrow> last (takeWhile (\<lambda> a. a = hd us) us) = hd us"
proof (induct us)
  case (Cons a us)
  then show ?case
    by (simp add: takeWhile_eq_Nil_iff) blast
qed simp

lemma card_set_decompose: assumes "1 < card (set us)"
  shows "takeWhile (\<lambda> a. a = hd us) us \<noteq> \<epsilon>" and "dropWhile (\<lambda> a. a = hd us) us \<noteq> \<epsilon>" and
         "set (takeWhile (\<lambda> a. a = hd us) us) = {hd us}" and
         "last (takeWhile (\<lambda> a. a = hd us) us) \<noteq> hd(dropWhile (\<lambda> a. a = hd us) us)"
proof-
  have "us \<noteq> \<epsilon>"
    using assms by force
  thus "takeWhile (\<lambda>a. a = hd us) us \<noteq> \<epsilon>"
    by (simp add: takeWhile_eq_Nil_iff)
  from sing_pow_set'[OF takeWhile_sing_root this]
  show set: "set (takeWhile (\<lambda> a. a = hd us) us) = {hd us}".
  show "dropWhile (\<lambda>a. a = hd us) us \<noteq> \<epsilon>"
  proof (rule notI)
    assume "dropWhile (\<lambda>a. a = hd us) us = \<epsilon>"
    from set[unfolded takeWhile_dropWhile_id[of "(\<lambda>a. a = hd us)" us, unfolded this emp_simps]]
    show False
      using assms by force
  qed
  from hd_dropWhile[OF this]
  show "last (takeWhile (\<lambda> a. a = hd us) us) \<noteq> hd(dropWhile (\<lambda> a. a = hd us) us)"
    unfolding nemp_takeWhile_last[OF \<open>us \<noteq> \<epsilon>\<close>] by simp
qed

lemma distinct_letter_in: assumes "w \<notin> [a]*"
  obtains m b q where "[a]\<^sup>@m \<cdot> [b] \<cdot> q = w" and "b \<noteq> a"
proof-
  have "dropWhile (\<lambda> x. x = a) w \<noteq> \<epsilon>"
    unfolding dropWhile_sing_pow using assms rootI[of "[a]" "\<^bold>|w\<^bold>|"] by auto
  hence eq: "takeWhile (\<lambda> x. x = a) w \<cdot> [hd (dropWhile (\<lambda> x. x = a) w)] \<cdot> tl (dropWhile (\<lambda> x. x = a) w) = w"
    by simp
  have root:"takeWhile (\<lambda> x. x = a) w \<in> [a]*"
    by (simp add: takeWhile_sing_root)
  have  "hd (dropWhile (\<lambda> x. x = a) w) \<noteq> a"
    using hd_dropWhile[OF \<open>dropWhile (\<lambda>x. x = a) w \<noteq> \<epsilon>\<close>].
  from that[OF _  this]
  show thesis
    using eq root unfolding root_def by metis
qed

lemma distinct_letter_in_hd: assumes "w \<notin> [hd w]*"
  obtains m b q where  "[hd w]\<^sup>@m \<cdot> [b] \<cdot> q = w" and "b \<noteq> hd w" and "m \<noteq> 0"
proof-
  obtain m b q where a1: "[hd w]\<^sup>@m \<cdot> [b] \<cdot> q = w" and a2: "b \<noteq> hd w"
    using distinct_letter_in[OF assms].
  have "m \<noteq> 0"
  proof (rule notI)
    assume "m = 0"
    note a1[unfolded this pow_zero emp_simps, folded hd_word]
    thus False using a2 by force
  qed
  from that[OF a1 a2 this]
  show thesis.
qed

lemma distinct_letter_in_hd': assumes "w \<notin> [hd w]*"
  obtains m b q where  "[hd w]\<^sup>@Suc m \<cdot> [b] \<cdot> q = w" and "b \<noteq> hd w"
using distinct_letter_in_hd[OF assms] Suc_minus by metis

lemma distinct_letter_in_suf: assumes "w \<notin> [a]*"
  obtains m b where "[b] \<cdot> [a]\<^sup>@m  \<le>s w" and "b \<noteq> a"
  using distinct_letter_in[reversed, unfolded rassoc, OF assms]
  unfolding suffix_def by metis

lemma sing_pow_exp: assumes "w \<in> [a]*" shows "w = [a]\<^sup>@\<^bold>|w\<^bold>|"
proof-
  obtain k where "[a] \<^sup>@ k = w"
    using rootE[OF assms].
  from this[folded  sing_pow_len[of a k, folded this, unfolded this], symmetric]
  show ?thesis.
qed

lemma sing_power': assumes "w \<in> [a]*" and "i < \<^bold>|w\<^bold>|" shows "w ! i = a"
  using  sing_pow_nth[OF \<open>i < \<^bold>|w\<^bold>|\<close>, of a, folded sing_pow_exp[OF \<open>w \<in> [a]*\<close>]].

lemma rev_sing_power: "x \<in> [a]* \<Longrightarrow> rev x = x"
  unfolding root_def using rev_pow rev_singleton_conv  by metis

lemma lcp_letter_power:
  assumes "w \<noteq> \<epsilon>" and "w \<in> [a]*" and "[a]\<^sup>@m \<cdot> [b] \<le>p z" and  "a \<noteq> b"
  shows "w \<cdot> z \<and>\<^sub>p z \<cdot> w = [a]\<^sup>@m"
proof-
  obtain k z' where "w = [a]\<^sup>@k" "z = [a]\<^sup>@m \<cdot> [b] \<cdot> z'" "k \<noteq> 0"
    using \<open>w \<in> [a]*\<close> \<open>[a]\<^sup>@m \<cdot> [b] \<le>p z\<close> \<open>w \<noteq> \<epsilon>\<close> nemp_pow[of "[a]"]
    unfolding root_def
    by (auto simp add: prefix_def)
  hence eq1: "w \<cdot> z = [a]\<^sup>@m \<cdot> ([a]\<^sup>@k \<cdot> [b] \<cdot> z')" and eq2: "z \<cdot> w = [a]\<^sup>@m \<cdot> ([b] \<cdot> z'\<cdot> [a]\<^sup>@k)"
    by (simp add: \<open>w = [a]\<^sup>@k\<close> \<open>z = [a]\<^sup>@m \<cdot> [b] \<cdot> z'\<close> pows_comm)+
  have "hd ([a]\<^sup>@k \<cdot> [b] \<cdot> z') = a"
    using hd_append2[OF \<open>w \<noteq> \<epsilon>\<close>, of "[b]\<cdot>z'",
        unfolded \<open>w = (a # \<epsilon>)\<^sup>@k\<close> hd_sing_pow[OF \<open>k \<noteq> 0\<close>, of a]].
  moreover have "hd([b] \<cdot> z'\<cdot> [a]\<^sup>@k) = b"
    by simp
  ultimately have "[a]\<^sup>@k \<cdot> [b] \<cdot> z' \<and>\<^sub>p [b] \<cdot> z'\<cdot> [a]\<^sup>@k = \<epsilon>"
    by (simp add: \<open>a \<noteq> b\<close> lcp_distinct_hd)
  thus ?thesis using eq1 eq2 lcp_ext_left[of "[a]\<^sup>@m" "[a]\<^sup>@k \<cdot> [b] \<cdot> z'" "[b] \<cdot> z'\<cdot> [a]\<^sup>@k"]
    by simp
qed

lemma per_one: assumes "w <p [a] \<cdot> w" shows "w \<in> [a]*"
proof-
  have "w <p (a # \<epsilon>) \<^sup>@ n \<Longrightarrow> 0 < n  \<Longrightarrow> w \<in> [a]*" for n
    using pref_sing_pow[of w a] sprefD1 rootI[of "[a]" "\<^bold>|w\<^bold>|"] by metis
  with  rootI per_root_powE[OF assms]
  show ?thesis
    by blast
qed

lemma per_one': "w \<in> [a]* \<Longrightarrow> w <p [a] \<cdot> w"
  using comm_root  self_root triv_spref[OF not_Cons_self2]  by blast

lemma per_sing_one: assumes "w \<noteq> \<epsilon>" "w <p [a] \<cdot> w" shows "period w 1"
  using periodI[OF \<open>w \<noteq> \<epsilon>\<close> \<open>w <p [a] \<cdot> w\<close>] unfolding sing_len[of a].

section "Border"

text\<open>A non-empty word  $x \neq w$ is a \emph{border} of a word $w$ if it is both its prefix and suffix. This elementary property captures how much the word $w$ overlaps
with itself, and it is in the obvious way related to a period of $w$. However, in many cases it is much easier to reason about borders than about periods.\<close>

definition border :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<le>b _" [51,51] 60 )
  where [simp]: "border x w = (x \<le>p w \<and> x \<le>s w \<and> x \<noteq> w \<and> x \<noteq> \<epsilon>)"

definition bordered :: "'a list \<Rightarrow> bool"
  where [simp]: "bordered w = (\<exists>b. b \<le>b w)"

lemma borderI[intro]: "x \<le>p w \<Longrightarrow> x \<le>s w \<Longrightarrow> x \<noteq> w \<Longrightarrow> x \<noteq> \<epsilon> \<Longrightarrow> x \<le>b w"
  unfolding border_def by blast

lemma borderD_pref: "x \<le>b w \<Longrightarrow> x \<le>p w"
  unfolding border_def by blast

lemma borderD_spref: "x \<le>b w \<Longrightarrow> x <p w"
  unfolding border_def  by simp

lemma borderD_suf: "x \<le>b w \<Longrightarrow> x \<le>s w"
  unfolding border_def by blast

lemma borderD_ssuf: "x \<le>b w \<Longrightarrow> x <s w"
  unfolding border_def by blast

lemma borderD_nemp: "x \<le>b w \<Longrightarrow> x \<noteq> \<epsilon>"
  using border_def by blast

lemma borderD_neq: "x \<le>b w \<Longrightarrow> x \<noteq> w"
  unfolding border_def by blast

lemma borderedI: "u \<le>b w \<Longrightarrow> bordered w"
  unfolding bordered_def by fast

lemma border_lq_nemp: assumes "x \<le>b w" shows "x\<inverse>\<^sup>>w \<noteq> \<epsilon>"
  using assms borderD_spref lq_spref by blast

lemma border_rq_nemp: assumes "x \<le>b w" shows "w\<^sup><\<inverse>x \<noteq> \<epsilon>"
  using assms borderD_ssuf rq_ssuf by blast

lemma border_trans[trans]: assumes "t \<le>b x" "x \<le>b w"
  shows "t \<le>b w"
  using assms unfolding border_def
  using suffix_order.antisym pref_trans[of t x w] suf_trans[of t x w] by blast

lemma border_rev_conv[reversal_rule]: "rev x \<le>b rev w \<longleftrightarrow> x \<le>b w"
  unfolding border_def
  using rev_is_Nil_conv[of x] rev_swap[of w] rev_swap[of x]
    suf_rev_pref_iff[of x w] pref_rev_suf_iff[of x w]
  by fastforce

lemma border_lq_comp: "x \<le>b w \<Longrightarrow> (w\<^sup><\<inverse>x) \<bowtie> x"
  unfolding border_def using rq_suf_suf ruler' by metis

lemmas border_lq_suf_comp = border_lq_comp[reversed]

subsection "The shortest border"

lemma border_len:  assumes "x \<le>b w"
  shows "1 < \<^bold>|w\<^bold>|" and "0 < \<^bold>|x\<^bold>|" and "\<^bold>|x\<^bold>| < \<^bold>|w\<^bold>|"
proof-
  show "\<^bold>|x\<^bold>| < \<^bold>|w\<^bold>|"
    using assms prefix_length_less unfolding border_def strict_prefix_def
    by blast
  show "0 < \<^bold>|x\<^bold>|"
    using assms unfolding border_def by blast
  thus "1 < \<^bold>|w\<^bold>|"
    using assms \<open>\<^bold>|x\<^bold>| < \<^bold>|w\<^bold>|\<close> unfolding border_def
    by linarith
qed

lemma borders_compare: assumes "x \<le>b w" and "x' \<le>b w" and "\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|"
  shows "x' \<le>b x"
  using ruler_le[OF borderD_pref[OF \<open>x' \<le>b w\<close>] borderD_pref[OF \<open>x \<le>b w\<close>] less_imp_le_nat[OF \<open>\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|\<close>]]
    suf_ruler_le[OF borderD_suf[OF \<open>x' \<le>b w\<close>] borderD_suf[OF \<open>x \<le>b w\<close>] less_imp_le_nat[OF \<open>\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|\<close>]]
    borderD_nemp[OF \<open>x' \<le>b w\<close>] \<open>\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|\<close>
    borderI by blast

lemma unbordered_border:
  "bordered w \<Longrightarrow>  \<exists> x. x \<le>b w \<and> \<not> bordered x"
proof (induction "\<^bold>|w\<^bold>|" arbitrary: w rule: less_induct)
  case less
  obtain x' where "x' \<le>b w"
    using bordered_def less.prems by blast
  show ?case
  proof (cases "bordered x'")
    assume "\<not> bordered x'"
    thus ?case
      using \<open>x' \<le>b w\<close> by blast
  next
    assume "bordered x'"
    from less.hyps[OF border_len(3)[OF \<open>x' \<le>b w\<close>] this]
    show ?case
      using  border_trans[of _ x' w] \<open>x' \<le>b w\<close> by blast
  qed
qed

lemma unbordered_border_shortest: "x \<le>b w \<Longrightarrow> \<not> bordered x \<Longrightarrow>  y \<le>b w \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|"
  using bordered_def[of x] borders_compare[of x w y] not_le_imp_less[of "\<^bold>|x\<^bold>|" "\<^bold>|y\<^bold>|"] by blast

lemma long_border_bordered: assumes long: "\<^bold>|w\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|x\<^bold>|" and border: "x \<le>b w"
  shows "(w\<^sup><\<inverse>x)\<inverse>\<^sup>>x \<le>b x"
proof-
  define p s where "p = w\<^sup><\<inverse>x" and "s = x\<inverse>\<^sup>>w"
  hence eq: "p\<cdot>x = x\<cdot>s"
    using assms unfolding border_def using lq_pref[of x w] rq_suf[of x w]  by simp
  have "\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|"
    using lenarg[OF p_def] long unfolding rq_len by linarith
  have px: "p \<cdot> p\<inverse>\<^sup>>x = x" and sx: "p\<inverse>\<^sup>>x \<cdot> s = x"
    using eqd_pref[OF eq less_imp_le, OF \<open>\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|\<close>] by blast+
  have "p\<inverse>\<^sup>>x \<noteq> \<epsilon>"
    using \<open>\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|\<close> px by fastforce
  have "p \<noteq> \<epsilon>"
    using border_rq_nemp[OF border] p_def
    by presburger
  have "p\<inverse>\<^sup>>x \<noteq> x"
    using \<open>p \<noteq> \<epsilon>\<close> px by force
  have "(p\<inverse>\<^sup>>x) \<le>b x"
    unfolding border_def
    using eqd_pref[OF eq less_imp_le, OF \<open>\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|\<close>] \<open>p\<inverse>\<^sup>>x \<noteq> \<epsilon>\<close> \<open>p\<inverse>\<^sup>>x \<noteq> x\<close> by blast
  thus ?thesis
    unfolding p_def.
qed

thm long_border_bordered[reversed]

lemma border_short_dec: assumes border: "x \<le>b w" and short: "\<^bold>|x\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|w\<^bold>|"
  shows "x \<cdot> x\<inverse>\<^sup>>(w\<^sup><\<inverse>x) \<cdot> x = w"
proof-
  have eq: "x\<cdot>x\<inverse>\<^sup>>w = w\<^sup><\<inverse>x\<cdot>x"
    using lq_pref[OF borderD_pref[OF border]] rq_suf[OF borderD_suf[OF border]] by simp
  have "\<^bold>|x\<^bold>| \<le> \<^bold>|w\<^sup><\<inverse>x\<^bold>|"
    using short unfolding rq_len by linarith
  from  lq_pref[of x w, OF borderD_pref[OF border], folded conjunct2[OF eqd_pref[OF eq this]]]
  show ?thesis.
qed

lemma bordered_dec: assumes "bordered w"
  obtains u v where "u\<cdot>v\<cdot>u = w" and "u \<noteq> \<epsilon>"
proof-
  obtain u where "u \<le>b w" and "\<not> bordered u"
    using unbordered_border[OF assms] by blast
  have "\<^bold>|u\<^bold>| + \<^bold>|u\<^bold>| \<le> \<^bold>|w\<^bold>|"
    using long_border_bordered[OF _ \<open>u \<le>b w\<close>] \<open>\<not> bordered u\<close> bordered_def leI by blast
  from border_short_dec[OF \<open>u \<le>b w\<close> this, THEN that, OF borderD_nemp[OF \<open>u \<le>b w\<close>]]
  show thesis.
qed

lemma emp_not_bordered: "\<not> bordered \<epsilon>"
  by simp

lemma bordered_nemp: "bordered w \<Longrightarrow> w \<noteq> \<epsilon>"
  using emp_not_bordered by blast

lemma sing_not_bordered: "\<not> bordered [a]"
  using bordered_dec[of "[a]" False] append_eq_Cons_conv[of _ _ a \<epsilon>] suf_nemp by fast

subsection "Relation to period and conjugation"

lemma border_conjug_eq: "x \<le>b w \<Longrightarrow> (w\<^sup><\<inverse>x) \<cdot> w = w \<cdot> (x\<inverse>\<^sup>>w)"
  using lq_rq_reassoc_suf[OF borderD_pref borderD_suf, symmetric] by blast

lemma border_per_root: "x \<le>b w \<Longrightarrow> w \<le>p (w\<^sup><\<inverse>x) \<cdot> w"
  using border_conjug_eq by blast

lemma per_root_border: assumes "\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|" and "r \<noteq> \<epsilon>" and "w \<le>p r \<cdot> w"
  shows "r\<inverse>\<^sup>>w \<le>b w"
proof
  have "\<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>|" and "r \<le>p w"
    using less_imp_le[OF \<open>\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|\<close>] pref_prod_long[OF \<open>w \<le>p r \<cdot> w\<close>] by blast+
  show "r\<inverse>\<^sup>>w \<le>p w"
    using pref_lq[OF \<open>w \<le>p r \<cdot> w\<close>, of r] unfolding lq_triv.
  show "r\<inverse>\<^sup>>w \<le>s w"
    using \<open>r \<le>p w\<close> by (auto simp add: prefix_def)
  show "r\<inverse>\<^sup>>w \<noteq> w"
    using \<open>r \<le>p w\<close> \<open>r \<noteq> \<epsilon>\<close> unfolding prefix_def  by fastforce
  show "r\<inverse>\<^sup>>w \<noteq> \<epsilon>"
    using lq_pref[OF \<open>r \<le>p w\<close>] \<open>\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|\<close> by force
qed

lemma pref_suf_neq_per: assumes "x \<le>p w" and "x \<le>s w" and "x \<noteq> w" shows "period w (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|)"
proof-
  have "(w\<^sup><\<inverse>x)\<cdot>x = w"
    using  rq_suf[OF \<open>x \<le>s w\<close>].
  have "x\<cdot>(x\<inverse>\<^sup>>w) = w"
    using  lq_pref[OF \<open>x \<le>p w\<close>].
  have take: "w\<^sup><\<inverse>x = take (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|) w"
    using rq_take.
  have nemp: "take (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|) w \<noteq> \<epsilon>"
    using \<open>x \<le>p w\<close> \<open>x \<noteq> w\<close> unfolding prefix_def by auto
  have "w \<le>p take (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|) w \<cdot> w"
    using triv_pref[of w "x\<inverse>\<^sup>>w"]
    unfolding lassoc[of "w\<^sup><\<inverse>x" x "x\<inverse>\<^sup>>w", unfolded \<open>x \<cdot> x\<inverse>\<^sup>>w = w\<close> \<open>w\<^sup><\<inverse>x \<cdot> x = w\<close>, symmetric] take.
  thus "period w (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|)"
    unfolding period_def   using nemp by blast
qed

lemma border_per: "x \<le>b w \<Longrightarrow> period w (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|)"
  unfolding  border_def using pref_suf_neq_per by blast

lemma per_border: assumes "n < \<^bold>|w\<^bold>|" and "period w n"
  shows "take (\<^bold>|w\<^bold>| - n) w  \<le>b w"
proof-
  have eq: "take (\<^bold>|w\<^bold>| - n) w = drop n w"
    using pref_take[OF \<open>period w n\<close>[unfolded
   per_shift[OF per_nemp[OF \<open>period w n\<close>] per_not_zero[OF \<open>period w n\<close>]]], unfolded length_drop].
  have "take (\<^bold>|w\<^bold>| - n) w \<noteq> \<epsilon>"
    using \<open>n < \<^bold>|w\<^bold>|\<close> take_eq_Nil by fastforce
  moreover have "take (\<^bold>|w\<^bold>| - n) w \<noteq> w"
    using  per_not_zero[OF \<open>period w n\<close>] \<open>n < \<^bold>|w\<^bold>|\<close> unfolding take_all_iff[of "\<^bold>|w\<^bold>|-n" w] by fastforce
  ultimately show ?thesis
    unfolding border_def using take_is_prefix[of "\<^bold>|w\<^bold>|-n" w] suffix_drop[of n w, folded eq] by blast
qed

section \<open>The longest border and the shortest period\<close>

subsection \<open>The longest border\<close>

definition max_borderP :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "max_borderP u w = (u \<le>p w \<and> u \<le>s w \<and> (u = w \<longrightarrow> w = \<epsilon>) \<and> (\<forall> v. v \<le>b w \<longrightarrow>  v \<le>p u))"

lemma max_borderP_emp_emp: "max_borderP \<epsilon> \<epsilon>"
  unfolding max_borderP_def by simp

lemma max_borderP_exE: obtains u where "max_borderP u w"
proof-
  define P where "P = (\<lambda> x. x \<le>p w \<and> x \<le>s w \<and> (x = w \<longrightarrow> w = \<epsilon>))"
  have "P \<epsilon>"
    unfolding P_def by blast
  obtain v where "v \<le>p w" and "P v" and "(\<And>y. y \<le>p w \<Longrightarrow> P y \<Longrightarrow> y \<le>p v)"
    using max_pref[of \<epsilon> w P thesis, OF prefix_bot.extremum \<open>P \<epsilon>\<close>] by blast
  hence "max_borderP v w"
    unfolding  max_borderP_def border_def P_def by presburger
  from that[OF this]
  show thesis.
qed

lemma max_borderP_of_nemp: "max_borderP u \<epsilon> \<Longrightarrow> u = \<epsilon>"
  by (metis max_borderP_def suffix_bot.extremum_unique)

lemma max_borderP_D_neq: "w \<noteq> \<epsilon> \<Longrightarrow> max_borderP u w \<Longrightarrow> u \<noteq> w"
  by (simp add: max_borderP_def)

lemma max_borderP_D_pref: "max_borderP u w \<Longrightarrow> u \<le>p w"
  by (simp add: max_borderP_def)

lemma max_borderP_D_suf: "max_borderP u w \<Longrightarrow> u \<le>s w"
  by (simp add: max_borderP_def)

lemma max_borderP_D_max: "max_borderP u w \<Longrightarrow> v \<le>b w \<Longrightarrow>  v \<le>p u"
  by (simp add: max_borderP_def)

lemma  max_borderP_D_max': "max_borderP u w \<Longrightarrow> v \<le>b w \<Longrightarrow> v \<le>s u"
  unfolding max_borderP_def using borderD_suf  suf_pref_eq suffix_same_cases by metis

lemma unbordered_max_border_emp:  "\<not> bordered w \<Longrightarrow> max_borderP u w \<Longrightarrow> u = \<epsilon>"
  unfolding max_borderP_def bordered_def border_def by blast

lemma bordered_max_border_nemp:  "bordered w \<Longrightarrow> max_borderP u w \<Longrightarrow> u \<noteq> \<epsilon>"
  unfolding max_borderP_def bordered_def border_def using prefix_Nil by blast

lemma max_borderP_border: "max_borderP u w \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> u \<le>b w"
  unfolding max_borderP_def border_def by blast

lemma max_borderP_rev: "max_borderP (rev u) (rev w) \<Longrightarrow> max_borderP u w"
proof-
  assume "max_borderP (rev u) (rev w)"
  from this[unfolded max_borderP_def rev_is_rev_conv, folded pref_rev_suf_iff suf_rev_pref_iff]
  have "u = w \<longrightarrow> w = \<epsilon>" and "u \<le>p w" and "u \<le>s w" and allv: "v \<le>b rev w \<Longrightarrow> v \<le>p rev u" for v
    by blast+
  show "max_borderP u w"
  proof (unfold max_borderP_def, intro conjI, simp_all only: \<open>u \<le>p w\<close> \<open>u \<le>s w\<close>)
    show "u = w \<longrightarrow> w = \<epsilon>" by fact
    show "\<forall>v. v \<le>b w \<longrightarrow> v \<le>p u"
  proof (rule allI, rule impI)
      fix v assume "v \<le>b w"
      show "v \<le>p u"
        using \<open>max_borderP (rev u) (rev w)\<close> \<open>v \<le>b w\<close> border_rev_conv max_borderP_D_max' pref_rev_suf_iff by metis
    qed
  qed
qed

lemma max_borderP_rev_conv: "max_borderP (rev u) (rev w) \<longleftrightarrow> max_borderP u w"
  using max_borderP_rev max_borderP_rev[of "rev u" "rev w", unfolded rev_rev_ident] by blast

(* TODO zkusit use argmax?
  SH: nasledujici jednoduche dukazy ukazuji, ze se tim asi nic neziska *)
term arg_max
definition max_border :: "'a list \<Rightarrow> 'a list" where
  "max_border w = (THE u. (max_borderP u w))"

lemma max_border_unique: assumes "max_borderP u w" "max_borderP v w"
  shows "u = v"
  using max_borderP_D_max[OF \<open>max_borderP u w\<close>, OF max_borderP_border[OF \<open>max_borderP v w\<close>]]
        max_borderP_D_max[OF \<open>max_borderP v w\<close>, OF max_borderP_border[OF \<open>max_borderP u w\<close>]]
  by force

lemma max_border_ex: "max_borderP (max_border w) w"
proof (rule max_borderP_exE[of w])
  fix u assume "max_borderP u w"
  with max_border_unique[OF this]
  show ?thesis
    unfolding max_border_def
    by (elim theI[of "\<lambda> x. max_borderP x w"]) simp
qed

lemma max_borderP_max_border: "max_borderP u w \<Longrightarrow> max_border w = u"
  using max_border_unique[OF max_border_ex].

lemma max_border_len_rev: "\<^bold>|max_border u\<^bold>| =  \<^bold>|max_border (rev u)\<^bold>|"
  by (cases "u = \<epsilon>", simp, metis length_rev max_borderP_max_border max_borderP_rev_conv max_border_ex)

lemma max_border_border: assumes "bordered w" shows "max_border w \<le>b w"
  using max_border_ex bordered_max_border_nemp[OF assms, of "max_border w"]
  unfolding max_borderP_def border_def by blast

theorem max_border_border':  "max_border w \<noteq> \<epsilon> \<Longrightarrow> max_border w \<le>b w"
  using max_borderP_border max_border_ex  by blast

lemma max_border_sing_emp: "max_border [a] = \<epsilon>"
  using max_border_ex[THEN unbordered_max_border_emp[OF sing_not_bordered]] by fast

lemma max_border_suf: "max_border w \<le>s w"
  using max_borderP_D_suf max_border_ex by auto

lemma max_border_nemp_neq: "w \<noteq> \<epsilon> \<Longrightarrow> max_border w \<noteq> w"
  by (simp add: max_borderP_D_neq max_border_ex)

lemma max_borderI: assumes "u \<noteq> w" and "u \<le>p w" and "u \<le>s w" and "\<forall> v. v \<le>b w \<longrightarrow> v \<le>p u"
  shows "max_border w = u"
  using assms max_border_ex
  by (intro max_borderP_max_border, unfold max_borderP_def border_def, blast)

lemma max_border_less_len: assumes "w \<noteq> \<epsilon>" shows "\<^bold>|max_border w\<^bold>| < \<^bold>|w\<^bold>|"
  using assms border_len(3) leI list.size(3) max_border_border' npos_len by metis

theorem max_border_max_pref: assumes "u \<le>b w" shows "u \<le>p max_border w"
  using  max_borderP_D_max[OF max_border_ex \<open>u \<le>b w\<close>].

theorem max_border_max_suf: assumes "u \<le>b w" shows "u \<le>s max_border w"
  using  max_borderP_D_max'[OF max_border_ex \<open>u \<le>b w\<close>].

lemma bordered_max_bord_nemp_conv[code]: "bordered w \<longleftrightarrow> max_border w \<noteq> \<epsilon>"
  using bordered_max_border_nemp max_border_ex unbordered_max_border_emp by blast

lemma max_bord_take: "max_border w = take \<^bold>|max_border w\<^bold>| w"
proof (cases "bordered w")
  assume "bordered w"
  from borderD_pref[OF max_border_border[OF this]]
  show "max_border w = take \<^bold>|max_border w\<^bold>| w"
    by (simp add: pref_take)
next
  assume "\<not> bordered w"
  hence "max_border w = \<epsilon>"
    using bordered_max_bord_nemp_conv by blast
  thus "max_border w = take \<^bold>|max_border w\<^bold>| w"
    by simp
qed


subsection \<open>The shortest period\<close>

(* TODO define min_period first, then use it here
  SH: prazdne slovo bude mit nedefinovanou periodu
*)
definition min_period_root :: "'a list \<Rightarrow> 'a list" ("\<pi>") where
  "min_period_root w = take (LEAST n. period w n) w"

definition min_period :: "'a list \<Rightarrow> nat" where
  "min_period w = \<^bold>|\<pi> w\<^bold>|"

lemma min_per_emp[simp]: "\<pi> \<epsilon> = \<epsilon>"
  unfolding min_period_root_def by simp

lemma min_per_zero[simp]: "min_period \<epsilon> = 0"
  by (simp add: min_period_def)

lemma min_per_per: "w \<noteq> \<epsilon> \<Longrightarrow> period w (min_period w)"
  unfolding min_period_def min_period_root_def
  using len_is_per LeastI_ex period_def periodI by metis

lemma min_per_pos: "w \<noteq> \<epsilon> \<Longrightarrow> 0 < min_period w"
  using min_per_per by auto

lemma min_per_len:  "min_period w \<le> \<^bold>|w\<^bold>|"
  unfolding min_period_def min_period_root_def using len_is_per Least_le by simp

lemmas min_per_root_len = min_per_len[unfolded min_period_def]

lemma min_per_sing: "min_period [a] = 1"
  using min_per_pos[of "[a]"] min_per_len[of "[a]"] by simp

lemma min_per_root_per_root: assumes "w \<noteq> \<epsilon>" shows "w <p (\<pi> w) \<cdot> w"
  using LeastI_ex assms len_is_per period_def unfolding min_period_root_def by metis

lemma min_per_pref: "\<pi> w \<le>p w"
  unfolding  min_period_root_def using take_is_prefix by blast

lemma min_per_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> \<pi> w \<noteq> \<epsilon>"
  using min_per_root_per_root by blast

lemma min_per_min: assumes "w <p r \<cdot> w" shows "\<pi> w \<le>p r"
proof (cases "w = \<epsilon>")
  assume "w \<noteq> \<epsilon>"
  have "period w \<^bold>|\<pi> w\<^bold>|"
    using \<open>w \<noteq> \<epsilon>\<close> min_per_root_per_root periodI by blast
  have "period w \<^bold>|r\<^bold>|"
    using \<open>w \<noteq> \<epsilon>\<close> assms periodI by blast
  from Least_le[of "\<lambda> n. period w n", OF this]
  have "\<^bold>|\<pi> w\<^bold>| \<le> \<^bold>|r\<^bold>|"
    unfolding  min_period_root_def using dual_order.trans len_take1 by metis
  with pref_trans[OF  min_per_pref sprefD1[OF \<open>w <p r \<cdot> w\<close>]]
  show "\<pi> w \<le>p r"
    using pref_prod_le by blast
qed simp

lemma lq_min_per_pref:  "\<pi> w\<inverse>\<^sup>>w \<le>p w"
  unfolding same_prefix_prefix[of "\<pi> w" _ w, symmetric]  lq_pref[OF min_per_pref] using sprefD1[OF min_per_root_per_root]
  by (cases "w = \<epsilon>", simp)

lemma max_bord_emp: "max_border \<epsilon> = \<epsilon>"
  by (simp add: max_borderP_of_nemp max_border_ex)

theorem min_per_max_border: "\<pi> w \<cdot> max_border w = w"
proof (cases "w = \<epsilon>")
  assume "w \<noteq> \<epsilon>"
  have "max_border w = (\<pi> w)\<inverse>\<^sup>>w"
  proof (intro max_borderI)
    show "\<pi> w\<inverse>\<^sup>>w \<noteq> w"
      using  min_per_nemp[OF \<open>w \<noteq> \<epsilon>\<close>]  lq_pref[OF min_per_pref]  append_self_conv2 by metis
    show "\<pi> w\<inverse>\<^sup>>w \<le>s w"
      using lq_suf_suf[OF min_per_pref].
    show "\<pi> w\<inverse>\<^sup>>w \<le>p w"
      using lq_min_per_pref by blast
    show "\<forall>v. v \<le>b w \<longrightarrow> v \<le>p \<pi> w\<inverse>\<^sup>>w"
    proof (rule allI, rule impI)
      fix v assume "v \<le>b w"
      have "w <p (w\<^sup><\<inverse>v) \<cdot> w"
        using per_border \<open>v \<le>b w\<close> border_per_root[OF \<open>v \<le>b w\<close>] border_rq_nemp[OF \<open>v \<le>b w\<close>]   by blast
      from min_per_min[OF this]
      have "\<pi> w \<le>p w\<^sup><\<inverse>v".
      from pref_rq_suf_lq[OF borderD_suf[OF \<open>v \<le>b w\<close>] this]
      have "v \<le>s \<pi> w\<inverse>\<^sup>>w".
      from  suf_pref_eq[OF this] ruler[OF borderD_pref[OF \<open>v \<le>b w\<close>] \<open>\<pi> w\<inverse>\<^sup>>w \<le>p w\<close>]
      show "v \<le>p \<pi> w\<inverse>\<^sup>>w"
        by blast
    qed
  qed
  thus ?thesis
    using lq_pref[OF min_per_pref, of w] by simp
qed (simp add:  max_bord_emp)

lemma min_per_len_diff: "min_period w = \<^bold>|w\<^bold>| - \<^bold>|max_border w\<^bold>|"
  unfolding min_period_def  using lenarg[OF min_per_max_border,unfolded lenmorph,of w] by linarith

lemma min_per_root_take [code]: "\<pi> w = take (\<^bold>|w\<^bold>| - \<^bold>|max_border w\<^bold>|) w"
  using cancel_right max_border_suf min_per_max_border suffix_take by metis

section \<open>Primitive words\<close>

text\<open>If a word $w$ is not a non-trivial power of some other word, we say it is primitive.\<close>

definition primitive :: "'a list \<Rightarrow> bool"
  where  "primitive u = (\<forall> r k. r\<^sup>@k = u \<longrightarrow> k = 1)"

lemma emp_not_prim[simp]: "\<not> primitive \<epsilon>"
  unfolding primitive_def
  by (metis pow_eq_if_list zero_neq_one)

lemma primI[intro]: "(\<And> r k. r\<^sup>@k = u \<Longrightarrow> k = 1) \<Longrightarrow> primitive u"
  by (simp add: primitive_def)

lemma prim_nemp: "primitive u \<Longrightarrow> u \<noteq> \<epsilon>"
  by force

lemma prim_exp_one: "primitive u \<Longrightarrow> r\<^sup>@k = u \<Longrightarrow> k = 1"
  using primitive_def by blast

lemma pow_nemp_imprim[intro]: "2 \<le> k  \<Longrightarrow> \<not> primitive (u\<^sup>@k)"
  using prim_exp_one by fastforce

lemma pow_not_prim: "\<not> primitive (u\<^sup>@Suc(Suc k))"
  using prim_exp_one by fastforce

lemma pow_non_prim: "k \<noteq> 1 \<Longrightarrow> \<not> primitive (w\<^sup>@k)"
  using prim_exp_one
  by auto

lemma prim_exp_eq: "primitive u \<Longrightarrow> r\<^sup>@k = u \<Longrightarrow> u = r"
  using prim_exp_one pow_1 by blast

lemma prim_per_div: assumes "primitive v" and "n \<noteq> 0" and "n \<le> \<^bold>|v\<^bold>|" and "period v (gcd \<^bold>|v\<^bold>| n)"
  shows "n = \<^bold>|v\<^bold>|"
proof-
  have "gcd \<^bold>|v\<^bold>| n dvd \<^bold>|v\<^bold>|"
    by simp
  from  prim_exp_eq[OF \<open>primitive v\<close> per_div[OF this \<open>period v (gcd \<^bold>|v\<^bold>| n)\<close>]]
  have "gcd \<^bold>|v\<^bold>| n = \<^bold>|v\<^bold>|"
    using take_len[OF le_trans[OF gcd_le2_nat[OF \<open>n \<noteq> 0\<close>] \<open>n \<le> \<^bold>|v\<^bold>|\<close>], of "\<^bold>|v\<^bold>|"]  by presburger
  from gcd_le2_nat[OF \<open>n \<noteq> 0\<close>, of "\<^bold>|v\<^bold>|", unfolded this] \<open>n \<le> \<^bold>|v\<^bold>|\<close>
  show "n = \<^bold>|v\<^bold>|" by force
qed

lemma prim_triv_root: "primitive u \<Longrightarrow> u \<in> t* \<Longrightarrow> t = u"
  using prim_exp_eq unfolding root_def
  unfolding primitive_def root_def by fastforce

lemma prim_comm_root[elim]: assumes "primitive r" and "u \<cdot> r = r \<cdot> u" shows "u \<in> r*"
  using \<open>u\<cdot>r = r\<cdot>u\<close>[unfolded comm] prim_exp_eq[OF \<open>primitive r\<close>] rootI by metis

lemma prim_comm_exp[elim]: assumes "primitive r" and "u\<cdot>r = r\<cdot>u" obtains k where "r\<^sup>@k = u"
  using rootE[OF prim_comm_root[OF assms]].

lemma pow_prim_root: assumes "w\<^sup>@k = r\<^sup>@n" and "0 < n" "primitive r"
  shows "w \<in> r*"
  using pow_comm_comm[OF \<open>w\<^sup>@k = r\<^sup>@n\<close>[symmetric] \<open>0 < n\<close>] prim_comm_root[OF \<open>primitive r\<close>]
    by presburger

lemma prim_root_drop_exp[elim]: assumes "u\<^sup>@k \<in> r*" and "0 < k" and  "primitive r"
  shows "u \<in> r*"
  using pow_comm_comm[of u k r, OF _ \<open>0 < k\<close>, THEN  prim_comm_root[OF \<open>primitive r\<close>]]
    \<open>u\<^sup>@k \<in> r*\<close>[unfolded root_def] unfolding root_def by metis

lemma prim_card_set: assumes "primitive u" and "\<^bold>|u\<^bold>| \<noteq> 1" shows "1 < card (set u)"
  using \<open>\<^bold>|u\<^bold>| \<noteq> 1\<close> \<open>primitive u\<close> pow_non_prim[OF \<open>\<^bold>|u\<^bold>| \<noteq> 1\<close>, of "[hd u]"]
  by (elim not_le_imp_less[OF contrapos_nn] card_set_le_1_imp_hd_pow[elim_format]) simp

lemma comm_not_prim: assumes "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>" "u \<cdot> v = v \<cdot> u" shows "\<not> primitive (u \<cdot> v)"
proof-
  obtain t k m where "u = t\<^sup>@k"  "v = t\<^sup>@m"
    using \<open>u\<cdot>v = v\<cdot>u\<close>[unfolded comm] by blast
  show ?thesis using pow_non_prim[of "k+m" "t"]
    unfolding \<open>u = t\<^sup>@k\<close> \<open>v = t\<^sup>@m\<close> add_exps[of t k m]
    using nemp_pow[OF \<open>u \<noteq> \<epsilon>\<close>[unfolded \<open>u = t\<^sup>@k\<close>]] nemp_pow[OF \<open>v \<noteq> \<epsilon>\<close>[unfolded \<open>v = t\<^sup>@m\<close>]]
    by linarith
qed

lemma prim_rotate_conv: "primitive w \<longleftrightarrow> primitive (rotate n w)"
proof
  assume "primitive w" show "primitive (rotate n w)"
  proof (rule primI)
    fix r k assume "r\<^sup>@k = rotate n w"
    obtain l where "(rotate l r)\<^sup>@k = w"
      using rotate_backE[of n w, folded \<open>r\<^sup>@k = rotate n w\<close>, unfolded rotate_pow_comm] by blast
    from prim_exp_one[OF \<open>primitive w\<close> this]
    show "k = 1".
  qed
next
  assume "primitive (rotate n w)"  show "primitive w"
  proof (rule primI)
    fix r k assume "r\<^sup>@k = w"
    from prim_exp_one[OF \<open>primitive (rotate n w)\<close>, OF rotate_pow_comm[of n r k, unfolded this, symmetric]]
    show "k = 1".
  qed
qed

lemma non_prim: assumes "\<not> primitive w" and "w \<noteq> \<epsilon>"
  obtains r k where "r \<noteq> \<epsilon>" and "1 < k" and "r\<^sup>@k = w" and "w \<noteq> r"
proof-
  from \<open>\<not> primitive w\<close>[unfolded primitive_def]
  obtain r k where "k \<noteq> 1" and "r\<^sup>@k = w"  by blast
  have "r \<noteq> \<epsilon>"
    using \<open>w \<noteq> \<epsilon>\<close> \<open>r\<^sup>@k = w\<close> emp_pow by blast
  have "k \<noteq> 0"
    using \<open>w \<noteq> \<epsilon>\<close> \<open>r\<^sup>@k = w\<close> pow_zero[of r] by meson
  have "w \<noteq> r"
    using \<open>k \<noteq> 1\<close>[folded eq_pow_exp[OF \<open>r \<noteq> \<epsilon>\<close>, of k 1, unfolded \<open>r \<^sup>@ k = w\<close>]] by simp
  show thesis
    using that[OF \<open>r \<noteq> \<epsilon>\<close> _ \<open>r\<^sup>@k = w\<close> \<open>w \<noteq> r\<close>] \<open>k \<noteq> 0\<close> \<open>k \<noteq> 1\<close> less_linear by blast
qed

lemma prim_no_rotate: assumes "primitive w" and "0 < n" and "n < \<^bold>|w\<^bold>|"
  shows "rotate n w \<noteq> w"
proof
  assume "rotate n w = w"
  have "take n w \<cdot> drop n w = drop n w \<cdot> take n w"
    using rotate_append[of "take n w" "drop n w"]
    unfolding take_len[OF less_imp_le_nat[OF \<open>n < \<^bold>|w\<^bold>|\<close>]] append_take_drop_id \<open>rotate n w = w\<close>.
  have "take n w \<noteq> \<epsilon>" "drop n w \<noteq> \<epsilon>"
    using \<open>0 < n\<close> \<open>n < \<^bold>|w\<^bold>|\<close> by auto+
  from \<open>primitive w\<close> show False
    using comm_not_prim[OF \<open>take n w \<noteq> \<epsilon>\<close> \<open>drop n w \<noteq> \<epsilon>\<close> \<open>take n w \<cdot> drop n w = drop n w \<cdot> take n w\<close>, unfolded append_take_drop_id]
    by simp
qed

lemma no_rotate_prim: assumes  "w \<noteq> \<epsilon>" and "\<And> n. 0 < n \<Longrightarrow> n < \<^bold>|w\<^bold>| \<Longrightarrow> rotate n w \<noteq> w"
  shows "primitive w"
proof (rule ccontr)
  assume "\<not> primitive w"
  from non_prim[OF this \<open>w \<noteq> \<epsilon>\<close>]
  obtain r l where "r \<noteq> \<epsilon>" and "1 < l" and "r\<^sup>@l = w" and "w \<noteq> r" by blast
  have "rotate \<^bold>|r\<^bold>| w = w"
    using rotate_root_self[of r l, unfolded \<open>r\<^sup>@l = w\<close>].
  moreover have "0 < \<^bold>|r\<^bold>|"
    by (simp add: \<open>r \<noteq> \<epsilon>\<close>)
  moreover have "\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|"
    unfolding pow_len[of r l, unfolded \<open>r\<^sup>@l = w\<close>]  using  \<open>1 < l\<close> \<open>0 < \<^bold>|r\<^bold>|\<close>  by auto
  ultimately show False
    using assms(2) by blast
qed

corollary prim_iff_rotate: assumes "w \<noteq> \<epsilon>" shows
  "primitive w \<longleftrightarrow> (\<forall> n. 0 < n \<and> n < \<^bold>|w\<^bold>| \<longrightarrow> rotate n w \<noteq> w)"
  using no_rotate_prim[OF \<open>w \<noteq> \<epsilon>\<close>] prim_no_rotate by blast

lemma prim_sing: "primitive [a]"
  using prim_iff_rotate[of "[a]"] by fastforce

lemma sing_pow_conv [simp]: "[u] = t\<^sup>@k \<longleftrightarrow> t = [u] \<and> k = 1"
  using pow_non_prim pow_1 prim_sing by metis

lemma prim_rev_iff[reversal_rule]: "primitive (rev u) \<longleftrightarrow> primitive u"
  unfolding primitive_def[reversed] using primitive_def..

lemma prim_map_prim: "primitive (map f ws) \<Longrightarrow> primitive ws"
  unfolding primitive_def using map_pow  by metis

lemma inj_map_prim: assumes "inj_on f A" and "u \<in> lists A" and
  "primitive u"
shows "primitive (map f u)"
  using prim_map_prim[of "the_inv_into A f" "map f u", folded inj_map_inv[OF assms(1-2)], OF assms(3)].

lemma prim_map_iff [reversal_rule]:
  assumes "inj f" shows "primitive (map f ws) = primitive (ws)"
  using inj_map_prim[of _ UNIV, unfolded lists_UNIV, OF \<open>inj f\<close> UNIV_I]
    prim_map_prim by (intro iffI)

lemma prim_concat_prim: "primitive (concat ws) \<Longrightarrow> primitive ws"
  unfolding primitive_def using concat_pow by metis

lemma eq_append_not_prim: "x = y \<Longrightarrow> \<not> primitive (x \<cdot> y)"
  by (metis append_Nil2 comm_not_prim prim_nemp)

section \<open>Primitive root\<close>

text\<open>Given a non-empty word $w$ which is not primitive, it is natural to look for the shortest $u$ such that $w = u^k$.
Such a word is primitive, and it is the primitive root of $w$.\<close>







definition primitive_root :: "'a list \<Rightarrow> 'a list" ("\<rho>") where
  "primitive_root x = (if x \<noteq> \<epsilon> then (THE r. primitive r \<and> (\<exists> k. x = r\<^sup>@k)) else \<epsilon>)"

definition primitive_root_exp :: "'a list \<Rightarrow> nat" ("e\<^sub>\<rho>") where
 "primitive_root_exp x = (if x \<noteq> \<epsilon> then (THE k. x = (\<rho> x)\<^sup>@k) else 0)"



lemma primroot_emp[simp]: "\<rho> \<epsilon> = \<epsilon>"
  unfolding primitive_root_def by simp

lemma comm_prim: assumes "primitive r" and  "primitive s" and "r\<cdot>s = s\<cdot>r"
  shows "r = s"
  using \<open>r\<cdot>s = s\<cdot>r\<close>[unfolded comm] assms[unfolded primitive_def, rule_format] by metis

lemma primroot_ex: assumes "x \<noteq> \<epsilon>" shows "\<exists> r k. primitive r \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
  using \<open>x \<noteq> \<epsilon>\<close>
proof(induction "\<^bold>|x\<^bold>|" arbitrary: x rule: less_induct)
  case less
  then show "\<exists> r k.  primitive r \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
  proof (cases "primitive x")
    assume "\<not> primitive x"
    from non_prim[OF this \<open>x \<noteq> \<epsilon>\<close>]
    obtain r l where "r \<noteq> \<epsilon>" and "1 < l" and "r\<^sup>@l = x" and "x \<noteq> r" by blast
    from less.hyps[OF root_shorter[OF \<open>x \<noteq> \<epsilon>\<close> rootI[of r l, unfolded \<open>r\<^sup>@l = x\<close>] \<open>x \<noteq> r\<close>]  \<open>r \<noteq> \<epsilon>\<close>]
    obtain k pr where "primitive pr" "k \<noteq> 0" "r = pr\<^sup>@k"
      by blast
    have "k*l \<noteq> 0"
      using \<open>1 < l\<close> \<open>k \<noteq> 0\<close> by force
    have "x = pr\<^sup>@(k*l)"
      using pow_mult[of pr k l, folded \<open>r = pr\<^sup>@k\<close>, unfolded \<open>r\<^sup>@l = x\<close>, symmetric].
    thus "\<exists>r k. primitive r \<and> k \<noteq> 0 \<and> x = r \<^sup>@ k"
      using \<open>primitive pr\<close> \<open>k*l \<noteq> 0\<close> by fast
  next
    assume "primitive x"
    have "x = x\<^sup>@Suc 0"
      by simp
    thus "\<exists> r k.  primitive r \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
      using \<open>primitive x\<close> by force
  qed
qed

lemma primroot_exE: assumes"x \<noteq> \<epsilon>"
  obtains r k where "primitive r" and "0 < k" and "x = r\<^sup>@k"
  using assms  primroot_ex[OF \<open> x \<noteq> \<epsilon>\<close>] by blast

text\<open>Uniqueness of the primitive root follows from the following lemma\<close>

lemma primroot_unique: assumes "u \<noteq> \<epsilon>" and "primitive r" and "u = r\<^sup>@k" shows "\<rho> u = r"
proof-
  have "0 < k"
    using \<open>u \<noteq> \<epsilon>\<close> \<open>u = r\<^sup>@k\<close> by blast
  have "s = r" if "primitive s" and "u = s\<^sup>@l" for s l
  proof-
    from pow_comm_comm[OF \<open>u = s\<^sup>@l\<close>[unfolded \<open>u = r\<^sup>@k\<close>] \<open>0 < k\<close>]
    obtain t where "s \<in> t*" and "r \<in> t*"
      using comm_root by blast
    from prim_exp_eq[OF \<open>primitive r\<close>, of t] prim_exp_eq[OF \<open>primitive s\<close>, of t]
    show "s = r"
      using rootE[OF \<open>s \<in> t*\<close>, of "s=r"] rootE[OF \<open>r \<in> t*\<close>, of "r = t"] by fastforce
  qed
  hence "primitive s \<and> (\<exists>k. u = s \<^sup>@ k) \<Longrightarrow> s = r" for s
    by presburger
  from the_equality[of "\<lambda> r. primitive r \<and> (\<exists>k. u = r \<^sup>@ k)" r, OF _ this]
  show "\<rho> u = r"
    using \<open>primitive r\<close> \<open>u = r\<^sup>@k\<close>  unfolding primitive_root_def if_P[OF \<open>u \<noteq> \<epsilon>\<close>] by blast
qed

lemma primroot_unique': assumes "0 < k" "primitive r" and "u = r\<^sup>@k" shows "\<rho> u = r"
  using  primroot_unique[OF _ assms(2,3)] using prim_nemp[OF \<open>primitive r\<close>] \<open>0 < k\<close> unfolding \<open>u = r\<^sup>@k\<close>
  using nonzero_pow_emp by blast

lemma prim_self_root[intro]: "primitive x \<Longrightarrow> \<rho> x  = x"
  using emp_not_prim primroot_unique pow_1 by metis

lemma primroot_exp_unique: assumes "u \<noteq> \<epsilon>" and "(\<rho> u)\<^sup>@k = u" shows "e\<^sub>\<rho> u = k"
  unfolding primitive_root_exp_def if_P[OF \<open>u \<noteq> \<epsilon>\<close>]
proof (rule the_equality)
  show "u = (\<rho> u)\<^sup>@k" using \<open>(\<rho> u)\<^sup>@k = u\<close>[symmetric].
  have "\<rho> u \<noteq> \<epsilon>"
    using assms by force
  show "ka = k" if "u = \<rho> u \<^sup>@ ka" for ka
    using eq_pow_exp[OF \<open>\<rho> u \<noteq> \<epsilon>\<close>, of k ka, folded \<open>u = (\<rho> u)\<^sup>@k\<close> that] by blast
qed

lemma primroot_prim[intro]:  "x \<noteq> \<epsilon> \<Longrightarrow> primitive (\<rho> x)"
  using primroot_unique primroot_ex by metis

text\<open>Existence and uniqueness of the primitive root justifies the function @{term primitive_root}: it indeed yields the primitive root of a nonempty word.\<close>


lemma primroot_is_root[simp]: "x \<in> (\<rho> x)*"
  by (cases "x = \<epsilon>", force, unfold root_def) (use primroot_exE primroot_unique in metis)


lemma primroot_expE: obtains k where "(\<rho> x)\<^sup>@k = x" and "0 < k"
proof (cases "x = \<epsilon>")
  assume "x \<noteq> \<epsilon>"
  with primroot_is_root[unfolded root_def] that
  show thesis by fastforce
qed auto

lemma primroot_exp_eq [simp]: "(\<rho> u)\<^sup>@(e\<^sub>\<rho> u) = u"
  using primroot_expE[of u "\<rho> u \<^sup>@ e\<^sub>\<rho> u = u"] primroot_exp_unique pow_0 primitive_root_exp_def by metis

lemma primroot_exp_len:
  shows "e\<^sub>\<rho> w * \<^bold>|\<rho> w\<^bold>| = \<^bold>|w\<^bold>|"
  using lenarg[OF primroot_exp_eq] unfolding pow_len.

lemma primroot_exp_nemp [intro]: "u \<noteq> \<epsilon> \<Longrightarrow> 0 < e\<^sub>\<rho> u"
  using  primroot_exp_eq nemp_pow by metis



lemma primroot_nemp[intro!]: "x \<noteq> \<epsilon> \<Longrightarrow> \<rho> x \<noteq> \<epsilon>"
  using prim_nemp by blast

lemma primroot_idemp[simp]: "\<rho> (\<rho> x) = \<rho> x"
 by (cases "x = \<epsilon>")  (simp only: primroot_emp, use prim_self_root in blast)

lemma prim_primroot_conv: assumes "w \<noteq> \<epsilon>" shows "primitive w \<longleftrightarrow> \<rho> w = w"
  using assms prim_self_root primroot_prim[OF \<open>w \<noteq> \<epsilon>\<close>] by metis

lemma not_prim_primroot_expE: assumes "\<not> primitive w"
  obtains k where "\<rho> w \<^sup>@k = w" and "2 \<le> k"
  using primroot_exp_eq primroot_prim assms
proof (cases "w = \<epsilon>")
  assume "w \<noteq> \<epsilon>"
  with primroot_exp_eq[of w]
  have "e\<^sub>\<rho> w \<noteq> 1" "e\<^sub>\<rho> w \<noteq> 0"
    using pow_zero pow_1 primroot_prim[OF \<open>w \<noteq> \<epsilon>\<close>] \<open>\<not> primitive w\<close> by force+
  with that[OF \<open>\<rho> w \<^sup>@ e\<^sub>\<rho> w = w\<close>]
  show thesis by force
qed force


lemma not_prim_expE: assumes "\<not> primitive x" and "x \<noteq> \<epsilon>"
  obtains r k where "primitive r" and "2 \<le> k" and "r\<^sup>@k = x"
  using not_prim_primroot_expE[OF \<open>\<not> primitive x\<close>] primroot_prim[OF \<open>x \<noteq> \<epsilon>\<close>] by metis

lemma primroot_of_root: assumes "u \<noteq> \<epsilon>" and "u \<in> q*" shows "\<rho> q = \<rho> u"
proof-
  have "q \<noteq> \<epsilon>"
    using assms by force
  from primroot_unique[OF \<open>u \<noteq> \<epsilon>\<close> primroot_prim[OF this], symmetric]
  root_trans[OF \<open>u \<in> q*\<close> primroot_is_root[of q]]
  show ?thesis
    unfolding root_def by blast
qed



lemma primroot_shorter_root: assumes "u \<noteq> \<epsilon>" and "u \<in> q*" shows "\<^bold>|\<rho> u\<^bold>| \<le> \<^bold>|q\<^bold>|"
  unfolding primroot_of_root[OF assms, symmetric]
  using root_nemp[OF assms] root_shorter_eq[of q, OF _ primroot_is_root] by blast


lemma primroot_len_le: "u \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|\<rho> u\<^bold>| \<le> \<^bold>|u\<^bold>|"
  using primroot_expE primroot_shorter_root[OF _ self_root] by auto

lemma primroot_take: assumes "u \<noteq> \<epsilon>" shows "\<rho> u = (take ( \<^bold>|\<rho> u\<^bold>| ) u)"
proof-
  obtain k where "(\<rho> u)\<^sup>@k = u" and "0 < k"
    using primroot_expE by blast
  show "\<rho> u = (take ( \<^bold>|\<rho> u\<^bold>| ) u)"
    using take_root[of _ "(\<rho> u)", OF \<open>0 < k\<close>, unfolded \<open>(\<rho> u)\<^sup>@k = u\<close>].
qed


lemma primroot_rotate_comm: assumes "w \<noteq> \<epsilon>" shows "\<rho> (rotate n w) = rotate n (\<rho> w)"
proof-
  obtain l where  "(\<rho> w)\<^sup>@l = w"
    using primroot_expE.
  hence "rotate n w \<in> (rotate n (\<rho> w))*"
    using rotate_pow_comm root_def by metis
  have "rotate n w \<noteq> \<epsilon>"
    using assms by auto
  have "primitive (rotate n (\<rho> w))"
    using assms prim_rotate_conv by blast
  show  ?thesis
    using primroot_unique[OF \<open>rotate n w \<noteq> \<epsilon>\<close> \<open>primitive (rotate n (\<rho> w))\<close>]
    rootE[OF \<open>rotate n w \<in> (rotate n (\<rho> w))*\<close>] by metis
qed

lemma primroot_rotate: "\<rho> w = r \<longleftrightarrow> \<rho> (rotate (k*\<^bold>|r\<^bold>|) w) = r" (is "?L \<longleftrightarrow> ?R")
proof(cases "w = \<epsilon>")
  case False
  show ?thesis
    unfolding primroot_rotate_comm[OF \<open>w \<noteq> \<epsilon>\<close>, of "k*\<^bold>|r\<^bold>|"]
    using length_rotate[of "k*\<^bold>|r\<^bold>|" "\<rho> w"] mod_mult_self2_is_0[of k "\<^bold>|r\<^bold>|"]
      rotate_id[of "k*\<^bold>|r\<^bold>|" "\<rho> w"]
    by metis
qed (simp add: rotate_is_Nil_conv[of "k*\<^bold>|r\<^bold>|" w])

lemma primrootI[intro]: assumes pow: "u = r\<^sup>@(Suc k)" and "primitive r" shows "\<rho> u = r"
proof-
  have "u \<noteq> \<epsilon>"
    using pow \<open>primitive r\<close> prim_nemp by auto
  show "\<rho> u = r"
    using primroot_unique[OF \<open>u \<noteq> \<epsilon>\<close> \<open>primitive r\<close> \<open>u = r\<^sup>@(Suc k)\<close>].
qed

lemma primroot_pref: "\<rho> u \<le>p u"
  by (cases "u = \<epsilon>", use primroot_emp in blast)
     (simp add: per_root_pref[OF _ primroot_is_root])

lemma short_primroot: assumes "u \<noteq> \<epsilon>" "\<not> primitive u" shows "\<^bold>|\<rho> u\<^bold>| < \<^bold>|u\<^bold>|"
  using primroot_prim[OF \<open>u \<noteq> \<epsilon>\<close>]  le_neq_implies_less pref_len primroot_pref
        long_pref assms by metis

lemma prim_primroot_cases: obtains "u = \<epsilon>" | "primitive u" | "\<^bold>|\<rho> u\<^bold>| < \<^bold>|u\<^bold>|"
  using short_primroot by blast

text\<open>We also have the standard characterization of commutation for nonempty words.\<close>

lemma comm_rootE: assumes  "x \<cdot> y = y \<cdot> x"
  obtains  t where "x \<in>  t*" and "y \<in> t*" and "t \<noteq> \<epsilon>"
  using assms[unfolded comm_root]
  using emp_all_roots list.discI root_nemp by metis

theorem comm_primroots: assumes "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" shows "u \<cdot> v = v \<cdot> u \<longleftrightarrow> \<rho> u = \<rho> v"
proof
  assume "u \<cdot> v = v \<cdot> u"
  from comm_rootE[OF this]
  obtain t where "u \<in> t*" and "v \<in> t*".
  show "\<rho> u = \<rho> v"
    using primroot_of_root[OF \<open>v \<noteq> \<epsilon>\<close> \<open>v \<in> t*\<close>, unfolded primroot_of_root[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> t*\<close>]].
next
  assume "\<rho> u = \<rho> v"
  from pows_comm[of "\<rho> u" "e\<^sub>\<rho> u" "e\<^sub>\<rho> v"]
  show "u \<cdot> v = v \<cdot> u"
    unfolding primroot_exp_eq unfolding \<open>\<rho> u = \<rho> v\<close> primroot_exp_eq.
qed

lemma comm_primroots': "u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> u \<cdot> v = v \<cdot> u \<Longrightarrow> \<rho> u = \<rho> v"
  by (simp add: comm_primroots)

lemma same_primroots_comm:  "\<rho> x = \<rho> y \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  using comm_primroots by blast

lemma pow_primroot: assumes "x \<noteq> \<epsilon>" shows "\<rho> (x\<^sup>@Suc k) = \<rho> x"
  using  comm_primroots'[OF nemp_Suc_pow_nemp, OF assms assms, of k, folded pow_Suc' pow_Suc] by blast

lemma comm_primroot_exp: assumes "v \<noteq> \<epsilon>" and "u \<cdot> v = v \<cdot> u"
  obtains n where "(\<rho> v)\<^sup>@n = u"
proof(cases)
  assume "u = \<epsilon>" thus thesis using that pow_0 by blast
next
  assume "u \<noteq> \<epsilon>" thus thesis using that[OF primroot_expE] \<open>u \<cdot> v = v \<cdot> u\<close>[unfolded comm_primroots[OF \<open>u \<noteq> \<epsilon>\<close> \<open>v \<noteq> \<epsilon>\<close>]] by metis
qed

lemma comm_primrootE: assumes  "x \<cdot> y = y \<cdot> x"
  obtains t where "x \<in> t*" and "y \<in> t*" and "primitive t"
  using comm_primroots assms emp_all_roots prim_sing primroot_is_root primroot_prim by metis

lemma primE: obtains t where "primitive t"
  using comm_primrootE by metis

lemma comm_primrootE':  assumes  "x \<cdot> y = y \<cdot> x"
  obtains  t m k where "x = t\<^sup>@k" and "y = t\<^sup>@m" and "primitive t"
  using comm_primrootE[OF \<open>x \<cdot> y = y \<cdot> x\<close>, unfolded root_def] by metis

lemma comm_nemp_pows_posE: assumes  "x \<cdot> y = y \<cdot> x" and "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>"
  obtains t k m where "x = t\<^sup>@k" and "y = t\<^sup>@m" and "0 < k" and "0 < m" and "primitive t"
proof-
  from comm_primrootE[OF \<open>x \<cdot> y = y \<cdot> x\<close>, unfolded root_def]
  obtain t k m where "t\<^sup>@k = x" "t\<^sup>@m = y" "primitive t"
    by metis
  note nemp_exp_pos[OF \<open>x \<noteq> \<epsilon>\<close> \<open>t\<^sup>@k = x\<close>] nemp_exp_pos[OF \<open>y \<noteq> \<epsilon>\<close> \<open>t\<^sup>@m = y\<close>]
  show thesis
    using that[OF \<open>t\<^sup>@k = x\<close>[symmetric] \<open>t\<^sup>@m = y\<close>[symmetric] \<open>0 < k\<close> \<open>0 < m\<close> \<open>primitive t\<close>].
qed

lemma comm_primroot_conv:  "u \<cdot> v = v \<cdot> u \<longleftrightarrow> u \<cdot> \<rho> v = \<rho> v \<cdot> u"
proof (cases "u = \<epsilon> \<or> v = \<epsilon>")
  assume "\<not> (u = \<epsilon> \<or> v = \<epsilon>)"
  hence "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
    by blast+
  show ?thesis
    using comm_primroots[OF \<open>u \<noteq> \<epsilon>\<close> \<open>v \<noteq> \<epsilon>\<close>, folded
   comm_primroots[OF \<open>u \<noteq> \<epsilon>\<close> primroot_nemp[OF \<open>v \<noteq> \<epsilon>\<close>], unfolded primroot_idemp]].
qed force

lemma comm_primroot [simp, intro]: "u \<cdot> \<rho> u = \<rho> u \<cdot> u"
  using comm_primroot_conv by blast

lemma comp_primroot_conv': shows "u \<cdot> v = v \<cdot> u \<longleftrightarrow> \<rho> u \<cdot> \<rho> v = \<rho> v \<cdot> \<rho> u"
  using comm_primroot_conv[of u v] comm_primroot_conv[of "\<rho> v" u]
  unfolding eq_sym_conv[of "\<rho> v \<cdot> u"] eq_sym_conv[of "\<rho> v \<cdot> \<rho> u"] by blast

lemma per_root_primroot: "w <p r \<cdot> w \<Longrightarrow>  w <p \<rho> r \<cdot> w"
  using per_root_trans[OF _ primroot_is_root].

lemma primroot_per_root: "r \<noteq> \<epsilon> \<Longrightarrow>  r <p \<rho> r \<cdot> r"
  by blast

lemma prim_comm_short_emp: assumes "primitive p" and "u\<cdot>p=p\<cdot>u" and "\<^bold>|u\<^bold>| < \<^bold>|p\<^bold>|"
  shows "u = \<epsilon>"
proof (rule ccontr)
  assume "u \<noteq> \<epsilon>"
  from \<open>u \<cdot> p = p \<cdot> u\<close>
  have "\<rho> u = \<rho> p"
    unfolding comm_primroots[OF \<open>u \<noteq> \<epsilon>\<close> prim_nemp, OF \<open>primitive p\<close>].
  have "\<rho> u = p"
    using prim_self_root[OF \<open>primitive p\<close>, folded \<open>\<rho> u = \<rho> p\<close>].
  from \<open>\<^bold>|u\<^bold>| < \<^bold>|p\<^bold>|\<close>[folded this]
  show False
    using primroot_len_le[OF \<open>u \<noteq> \<epsilon>\<close>] by auto
qed

lemma primroot_rev[reversal_rule]: shows "\<rho> (rev u) = rev (\<rho> u)"
proof (cases "u = \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  hence "rev u \<noteq> \<epsilon>"
    by simp
  have "primitive (rev (\<rho> u))"
    using primroot_prim[OF \<open>u \<noteq> \<epsilon>\<close>] unfolding prim_rev_iff.
  have "rev u = (rev (\<rho> u))\<^sup>@e\<^sub>\<rho> u"
    unfolding rev_pow[symmetric] primroot_exp_eq..
  from primroot_unique[OF \<open>rev u \<noteq> \<epsilon>\<close> \<open>primitive (rev (\<rho> u))\<close> this]
  show ?thesis.
qed simp

lemmas primroot_suf = primroot_pref[reversed]

lemma per_le_prim_iff:
  assumes "u \<le>p p \<cdot> u" and "p \<noteq> \<epsilon>" and "2 * \<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|"
  shows "primitive u \<longleftrightarrow> u \<cdot> p \<noteq> p \<cdot> u"
proof
  have "\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|" using  \<open>2 * \<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>
      nemp_len[OF \<open>p \<noteq> \<epsilon>\<close>] by linarith
  with \<open>p \<noteq> \<epsilon>\<close>
  show "primitive u \<Longrightarrow> u \<cdot> p \<noteq> p \<cdot> u"
    by (intro notI, elim notE) (rule prim_comm_short_emp[OF _ sym])
  show "u \<cdot> p \<noteq> p \<cdot> u \<Longrightarrow> primitive u"
  proof (elim swap[of "_ = _"], elim not_prim_primroot_expE)
    fix k z assume "2 \<le> k" and eq: "z \<^sup>@ k = u"
    from this(1) lenarg[OF this(2)] \<open>2 * \<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>
    have "\<^bold>|z\<^bold>| + \<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|"
      by (elim at_least2_Suc) (simp only: pow_Suc lenmorph[of z])
    with \<open>u \<le>p p \<cdot> u\<close> have "z \<cdot> p = p \<cdot> z"
      by (rule two_pers[rotated 1]) (simp flip: eq pow_comm)
    from comm_add_exp[OF this, of k]
    show "u \<cdot> p = p \<cdot> u" unfolding eq.
  qed
qed

lemma per_root_mod_primE [elim]: assumes "u <p r \<cdot> u"
  obtains n p s where "p \<cdot> s = \<rho> r" and "(p\<cdot>s)\<^sup>@n \<cdot> p = u" and "s \<noteq> \<epsilon>"
  using per_root_modE[OF per_root_primroot[OF assms]] primroot_prim[OF per_root_nemp[OF assms]]
   emp_not_prim by metis

subsection \<open>Primitivity and the shortest period\<close>

lemma min_per_primitive: assumes "w \<noteq> \<epsilon>" shows "primitive (\<pi> w)"
proof-
  have "\<rho>(\<pi> w) \<noteq> \<epsilon>"
    using assms min_per_nemp primroot_nemp by blast
  obtain k where "\<pi> w = (\<rho> (\<pi> w))\<^sup>@k"
    using  primroot_expE by metis
  from rootI[of "\<rho> (\<pi> w)" k, folded this]
  have "w <p (\<rho> (\<pi> w)) \<cdot> w"
    using  min_per_root_per_root[OF assms, THEN per_root_trans]  by presburger
  from pow_pref_root_one[OF _ \<open>\<rho>(\<pi> w) \<noteq> \<epsilon>\<close>, of k, folded  \<open>\<pi> w = (\<rho> (\<pi> w))\<^sup>@k\<close>, OF _ min_per_min[OF this]]
  have "k = 1"
    using  \<open>\<pi> w = (\<rho> (\<pi> w))\<^sup>@k\<close> min_per_nemp[OF \<open>w \<noteq> \<epsilon>\<close>] pow_zero[of "\<rho> (\<pi> w)"] by fastforce
  show "primitive (\<pi> w)"
    using primroot_prim[OF \<open>\<rho> (\<pi> w) \<noteq> \<epsilon>\<close>, folded \<open>\<pi> w = (\<rho> (\<pi> w))\<^sup>@k\<close>[unfolded \<open>k = 1\<close> One_nat_def pow_one]].
qed

lemma min_per_short_primroot: assumes "w \<noteq> \<epsilon>" and "(\<rho> w)\<^sup>@k = w" and "k \<noteq> 1"
  shows "\<pi> w = \<rho> w"
proof-
  have "k \<noteq> 0"
    using assms pow_zero by blast
  with \<open>k \<noteq> 1\<close>  have "2 \<le> k"
    by fastforce
           have "w <p (\<rho> w) \<cdot> w"
    using assms(1) assms(2) per_root_drop_exp root_self by metis
  have "w <p (\<pi> w) \<cdot> w"
    using assms(1) min_per_root_per_root by blast
  have "\<pi> w \<le>p \<rho> w"
    using min_per_min[OF \<open>w <p (\<rho> w) \<cdot> w\<close>].
  from  prefix_length_le[OF this]
  have "\<^bold>|\<pi> w\<^bold>| + \<^bold>|\<rho> w\<^bold>| \<le> \<^bold>|w\<^bold>|"
    unfolding lenarg[OF \<open>(\<rho> w)\<^sup>@k =w\<close>, unfolded pow_len, symmetric] using
     mult_le_mono1[OF \<open>2 \<le> k\<close>, of "\<^bold>|\<rho> w\<^bold>|"] unfolding one_add_one[symmetric] distrib_right mult_1
    by simp
  from two_pers_root[OF \<open>w <p (\<pi> w) \<cdot> w\<close> \<open>w <p (\<rho> w) \<cdot> w\<close> this]
  have "\<pi> w \<cdot> \<rho> w = \<rho> w \<cdot> \<pi> w".
  from this[unfolded comm_primroots[OF per_root_nemp[OF \<open>w <p (\<pi> w) \<cdot> w\<close>] per_root_nemp[OF \<open>w <p (\<rho> w) \<cdot> w\<close>]]]
  show "\<pi> w = \<rho> w"
    unfolding prim_self_root[of "\<rho> w", OF primroot_prim[OF \<open>w \<noteq> \<epsilon>\<close>]]
      prim_self_root[of "\<pi> w", OF min_per_primitive[OF \<open>w \<noteq> \<epsilon>\<close>]].
qed


lemma primitive_iff_per: "primitive w \<longleftrightarrow> w \<noteq> \<epsilon> \<and> (\<pi> w = w \<or> \<pi> w \<cdot> w \<noteq> w \<cdot> \<pi> w)"
proof
  assume "primitive w"
  hence "w \<noteq> \<epsilon>" by fastforce
  show "w \<noteq> \<epsilon> \<and> (\<pi> w = w \<or> \<pi> w \<cdot> w \<noteq> w \<cdot> \<pi> w)"
  proof (rule conjI)
    show "\<pi> w = w \<or> \<pi> w \<cdot> w \<noteq> w \<cdot> \<pi> w"
      using comm_prim [OF min_per_primitive[OF \<open>w \<noteq> \<epsilon>\<close>] \<open>primitive w\<close>]
      by (intro verit_or_neg(1))
  qed fact
next
  assume asm: "w \<noteq> \<epsilon> \<and> (\<pi> w = w \<or> \<pi> w \<cdot> w \<noteq> w \<cdot> \<pi> w)"
  have "w \<noteq> \<epsilon>" and imp: "\<pi> w \<cdot> w = w \<cdot> \<pi> w \<Longrightarrow> \<pi> w = w"
    using asm by blast+
  obtain k where "(\<rho> w)\<^sup>@k = w" "0 < k"
    using primroot_expE.
  show "primitive w"
  proof-
    from imp[unfolded min_per_short_primroot[OF \<open>w \<noteq> \<epsilon>\<close> \<open>(\<rho> w)\<^sup>@k = w\<close>]]
    have "\<rho> w = w"
      using pow_comm[symmetric, of "\<rho> w" k, unfolded \<open>\<rho> w \<^sup>@k = w\<close>]
       \<open>\<rho> w \<^sup>@ k = w\<close> min_per_short_primroot[OF \<open>w \<noteq> \<epsilon>\<close> \<open>\<rho> w\<^sup>@k = w\<close>] pow_1 \<open>w \<noteq> \<epsilon>\<close> by metis
    thus "primitive w"
      using prim_primroot_conv[OF \<open>w \<noteq> \<epsilon>\<close>] by simp
  qed
qed

section \<open>Conjugation\<close>

text\<open>Two words $x$ and $y$ are conjugated if one is a rotation of the other.
Or, equivalently, there exists $z$ such that
\[
xz = zy.
\]
\<close>

definition conjugate (infix "\<sim>" 51)
  where "u \<sim> v \<equiv> \<exists>r s. r \<cdot> s = u \<and> s \<cdot> r = v"

lemma conjugE [elim]:
  assumes "u \<sim> v"
  obtains r s where "r \<cdot> s = u" and "s \<cdot> r = v"
  using assms unfolding conjugate_def  by (elim exE conjE)

lemma conjugE_nemp[elim]:
  assumes "u \<sim> v" and "u \<noteq> \<epsilon>"
  obtains r s where "r \<cdot> s = u" and "s \<cdot> r = v" and "s \<noteq> \<epsilon>"
  using assms unfolding conjugate_def
proof (cases "u = v")
  assume "u \<noteq> v"
  obtain r s where "r \<cdot> s = u" and "s \<cdot> r = v" using conjugE[OF \<open>u \<sim> v\<close>].
  hence "s \<noteq> \<epsilon>" using \<open>u \<noteq> v\<close> by force
  thus thesis using that[OF \<open>r \<cdot> s = u\<close> \<open>s \<cdot> r = v\<close>] by blast
qed (simp add: that[OF _ _ \<open>u \<noteq> \<epsilon>\<close>])

lemma conjugE1 [elim]:
  assumes "u \<sim> v"
  obtains r where "u \<cdot> r = r \<cdot> v"
proof -
  obtain r s where u: "r \<cdot> s = u" and v: "s \<cdot> r = v" using assms..
  have "u \<cdot> r = r \<cdot> v" unfolding u[symmetric] v[symmetric] using rassoc.
  then show thesis by fact
qed

lemma conjug_rev_conv [reversal_rule]: "rev u \<sim> rev v \<longleftrightarrow> u \<sim> v"
  unfolding conjugate_def[reversed] using conjugate_def by blast

lemma conjug_rotate_iff: "u \<sim> v \<longleftrightarrow> (\<exists> n. v = rotate n u)"
  unfolding conjugate_def
  using rotate_drop_take[of _ u] takedrop[of _ u] rotate_append
  by metis

lemma rotate_conjug: "w \<sim> rotate n w"
  using conjug_rotate_iff by blast

lemma conjug_rotate_iff_le:
  shows "u \<sim> v \<longleftrightarrow> (\<exists> n \<le> \<^bold>|u\<^bold>| - 1. v = rotate n u)"
proof
  show "\<exists>n \<le> \<^bold>|u\<^bold>| - 1 . v = rotate n u \<Longrightarrow> u \<sim> v"
    using conjug_rotate_iff by blast
next
  assume "u \<sim> v"
  thus "\<exists> n \<le> \<^bold>|u\<^bold>| - 1. v = rotate n u"
  proof (cases "u = \<epsilon>")
    assume "u \<noteq> \<epsilon>"
    obtain r s where "r \<cdot> s = u" and  "s \<cdot> r = v" and "s \<noteq> \<epsilon>"
      using conjugE_nemp[OF \<open>u \<sim> v\<close> \<open>u \<noteq> \<epsilon>\<close>].
    hence "v = rotate \<^bold>|r\<^bold>| u"
      using rotate_append[of r s] by argo
    moreover have "\<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>| - 1"
      using lenarg[OF \<open>r \<cdot> s = u\<close>, unfolded lenmorph] nemp_len[OF \<open>s \<noteq> \<epsilon>\<close>] by linarith
    ultimately  show "\<exists>n \<le> \<^bold>|u\<^bold>| - 1. v = rotate n u"
      by blast
  qed auto
qed

lemma conjugI [intro]: "r \<cdot> s = u \<Longrightarrow> s \<cdot> r = v \<Longrightarrow> u \<sim> v"
  unfolding conjugate_def by (intro exI conjI)

lemma conjugI' [intro!]: "r \<cdot> s \<sim> s \<cdot> r"
  unfolding conjugate_def by (intro exI conjI) standard+

lemma conjug_refl: "u \<sim> u"
  by standard+

lemma conjug_sym[sym]: "u \<sim> v \<Longrightarrow> v \<sim> u"
  by (elim conjugE, intro conjugI) assumption

lemma conjug_swap: "u \<sim> v \<longleftrightarrow> v \<sim> u"
  by blast

lemma conjug_nemp_iff: "u \<sim> v \<Longrightarrow> u = \<epsilon> \<longleftrightarrow> v = \<epsilon>"
  by (elim conjugE1, intro iffI) simp+

lemma conjug_len: "u \<sim> v  \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
  by (elim conjugE, hypsubst, rule swap_len)

lemma pow_conjug:
  assumes eq: "t\<^sup>@i \<cdot> r \<cdot> u = t\<^sup>@k" and t: "r \<cdot> s = t"
  shows "u \<cdot> t\<^sup>@i \<cdot> r = (s \<cdot> r)\<^sup>@k"
proof -
  have "t\<^sup>@i \<cdot> r \<cdot> u \<cdot> t\<^sup>@i \<cdot> r = t\<^sup>@i \<cdot> t\<^sup>@k \<cdot> r" unfolding eq[unfolded lassoc] lassoc append_same_eq pows_comm..
  also have "\<dots>  = t\<^sup>@i \<cdot> r \<cdot> (s \<cdot> r)\<^sup>@k" unfolding conjug_pow[OF rassoc, symmetric] t..
  finally show "u \<cdot> t\<^sup>@i \<cdot> r = (s \<cdot> r)\<^sup>@k" unfolding same_append_eq.
qed

lemma conjug_set: assumes "u \<sim> v" shows "set u = set v"
  using conjugE[OF \<open>u \<sim> v\<close>] set_append Un_commute by metis

lemma conjug_concat_conjug: "xs \<sim> ys \<Longrightarrow> concat xs \<sim> concat ys"
  unfolding conjugate_def using concat_morph by metis

text\<open>The solution of the equation
\[
xz = zy
\]
is given by the next lemma.
\<close>

lemma conjug_eqE [elim, consumes 2]:
  assumes eq: "x \<cdot> z = z \<cdot> y" and "x \<noteq> \<epsilon>"
  obtains u v k where "u \<cdot> v = x" and "v \<cdot> u = y" and "(u \<cdot> v)\<^sup>@k \<cdot> u = z" and "v \<noteq> \<epsilon>"
proof -
  have "z \<le>p x \<cdot> z" using eq[symmetric]..
  from this and \<open>x \<noteq> \<epsilon>\<close> have "z <p x \<cdot> z"..
  then obtain k u v where "x\<^sup>@k \<cdot> u = z" and x: "u \<cdot> v = x" and "v \<noteq> \<epsilon>"..
  have z: "(u\<cdot>v)\<^sup>@k \<cdot> u = z" unfolding x \<open>x\<^sup>@k \<cdot> u = z\<close>..
  have "z \<cdot> y = (u\<cdot>v) \<cdot> ((u\<cdot>v)\<^sup>@k \<cdot> u)" unfolding z unfolding x eq..
  also have "\<dots> = (u\<cdot>v)\<^sup>@k \<cdot> u \<cdot> (v \<cdot> u)" unfolding lassoc pow_comm[symmetric]..
  finally have y: "v \<cdot> u = y" unfolding z[symmetric] rassoc same_append_eq..
  from x y z \<open>v \<noteq> \<epsilon>\<close> show thesis..
qed

theorem conjugation: assumes "x\<cdot>z = z\<cdot>y" and "x \<noteq> \<epsilon>"
  shows "\<exists> u v k. u \<cdot> v = x \<and> v \<cdot> u  = y \<and> (u \<cdot> v)\<^sup>@k \<cdot> u = z"
  using assms by blast

lemma conjug_eq_primrootE' [elim, consumes 2]:
  assumes eq: "x \<cdot> z = z \<cdot> y" and "x \<noteq> \<epsilon>"
  obtains r s i n where
    "(r \<cdot> s)\<^sup>@i = x" and
    "(s \<cdot> r)\<^sup>@i = y" and
    "(r \<cdot> s)\<^sup>@n \<cdot> r = z" and
    "s \<noteq> \<epsilon>" and "0 < i" and "primitive (r \<cdot> s)"
     proof -
  obtain i where "(\<rho> x)\<^sup>@i = x" "0 < i"
    using primroot_expE by blast
  have "z <p x \<cdot> z" using prefI[OF \<open>x \<cdot> z = z \<cdot> y\<close>[symmetric]] \<open>x \<noteq> \<epsilon>\<close>..
  from per_root_primroot[OF this]
  have "z <p (\<rho> x) \<cdot> z".
  from per_root_modE[OF this]
  obtain n r s where "r \<cdot> s = \<rho> x" "\<rho> x \<^sup>@ n \<cdot> r = z" "s \<noteq> \<epsilon>".
  have x: "(r\<cdot>s)\<^sup>@i = x" unfolding \<open>r \<cdot> s = \<rho> x\<close> \<open>(\<rho> x)\<^sup>@i = x\<close>..
  have z: "(r\<cdot>s)\<^sup>@n \<cdot> r = z" unfolding \<open>r \<cdot> s = \<rho> x\<close> using  \<open>(\<rho> x)\<^sup>@n \<cdot> r = z\<close>.
  have y [symmetric]: "y = (s\<cdot>r)\<^sup>@i"
    using eq[symmetric, folded x z, unfolded lassoc pows_comm[of _ i], unfolded rassoc cancel,
          unfolded shift_pow cancel].
  from \<open>x \<noteq> \<epsilon>\<close> have "primitive (r \<cdot> s)" unfolding \<open>r \<cdot> s = \<rho> x\<close>..
  from that[OF x y z \<open>s \<noteq> \<epsilon>\<close> \<open>0 < i\<close> this]
  show thesis.
qed

lemma conjugI1 [intro]:
  assumes eq: "u \<cdot> r = r \<cdot> v"
  shows "u \<sim> v"
proof (cases)
  assume "u = \<epsilon>"
  have "v = \<epsilon>" using eq unfolding \<open>u = \<epsilon>\<close> by simp
  show "u \<sim> v" unfolding \<open>u = \<epsilon>\<close> \<open>v = \<epsilon>\<close> using conjug_refl.
next
  assume "u \<noteq> \<epsilon>"
  show "u \<sim> v" using eq \<open>u \<noteq> \<epsilon>\<close> by (cases rule: conjug_eqE, intro conjugI)
qed

lemma pow_conjug_conjug_conv: assumes "0 < k" shows "u\<^sup>@k \<sim> v\<^sup>@k \<longleftrightarrow> u \<sim> v"
proof
  assume "u \<^sup>@ k \<sim> v \<^sup>@ k"
  obtain r s where "r \<cdot> s = u\<^sup>@k" and "s \<cdot> r = v\<^sup>@k"
    using conjugE[OF \<open>u\<^sup>@k \<sim> v\<^sup>@k\<close>].
  hence "v\<^sup>@k = (rotate \<^bold>|r\<^bold>| u)\<^sup>@k"
    using rotate_append rotate_pow_comm by metis
  hence "v = rotate \<^bold>|r\<^bold>| u"
    using pow_eq_eq[OF _ \<open>0 < k\<close>] by blast
  thus "u \<sim> v"
    using rotate_conjug by blast
next
  assume "u \<sim> v"
  obtain r s where "u = r \<cdot> s" and "v = s \<cdot> r"
    using conjugE[OF \<open>u \<sim> v\<close>] by metis
  have "u\<^sup>@k \<cdot> r = r \<cdot> v\<^sup>@k"
    unfolding \<open>u = r \<cdot> s\<close> \<open>v = s \<cdot> r\<close> shift_pow..
  thus "u\<^sup>@k \<sim> v\<^sup>@k"
    using conjugI1 by blast
qed

lemma conjug_trans [trans]:
  assumes uv: "u \<sim> v" and vw: "v \<sim> w"
  shows "u \<sim> w"
  using assms  unfolding conjug_rotate_iff using rotate_rotate by blast

lemma conjug_trans': assumes uv': "u \<cdot> r = r \<cdot> v" and vw': "v \<cdot> s = s \<cdot> w" shows "u \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> w"
proof -
  have "u \<cdot> (r \<cdot> s) = (r \<cdot> v) \<cdot> s" unfolding uv'[symmetric] rassoc..
  also have "\<dots> = r \<cdot> (s \<cdot> w)" unfolding vw'[symmetric] rassoc..
  finally show "u \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> w" unfolding rassoc.
qed

text\<open>Of course, conjugacy is an equivalence relation.\<close>
lemma conjug_equiv: "equivp (\<sim>)"
  by (simp add: conjug_refl conjug_sym conjug_trans equivpI reflpI sympI transpI)

lemma rotate_fac_pref: assumes "u \<le>f w"
  obtains w' where "w' \<sim> w" and "u \<le>p w'"
proof-
  from facE[OF \<open>u \<le>f w\<close>]
  obtain p s where "w = p \<cdot> u \<cdot> s".
  from that[OF conjugI'[of "u \<cdot> s" p, unfolded rassoc, folded this] triv_pref]
  show thesis.
qed

lemma rotate_into_pos_sq: assumes "s\<cdot>p \<le>f w\<cdot>w" and  "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|" and "\<^bold>|p\<^bold>| \<le> \<^bold>|w\<^bold>|"
obtains w' where "w \<sim> w'" "p \<le>p w'" "s \<le>s w'"
proof-
  obtain pw where "pw\<cdot>s\<cdot>p \<le>p w\<cdot>w"
    by (meson assms(1) fac_pref)
  hence "pw \<cdot> s \<le>p w\<cdot> w"
    unfolding lassoc prefix_def by force

  hence "take \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w) = pw \<cdot> s"
    using pref_take by blast

  have "p \<le>p drop \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w)"
    using pref_drop[OF \<open>pw\<cdot>s\<cdot>p \<le>p w\<cdot>w\<close>[unfolded lassoc]] drop_pref  by metis

  let ?w = "rotate \<^bold>|pw \<cdot> s\<^bold>| w"

  have "\<^bold>|?w\<^bold>| = \<^bold>|w\<^bold>|" by auto

  have "rotate \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w) = ?w \<cdot> ?w"
    using rotate_pow_comm_two.

  hence eq: "?w \<cdot> ?w = (drop \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w)) \<cdot> take \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w)"
    by (metis \<open>pw \<cdot> s \<le>p w \<cdot> w\<close> append_take_drop_id pref_take rotate_append)

  have "p \<le>p ?w"
    using pref_prod_le[OF _ \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|w\<^bold>|\<close>[folded \<open>\<^bold>|?w\<^bold>| = \<^bold>|w\<^bold>|\<close>]]
          prefix_prefix[OF \<open>p \<le>p drop \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w)\<close>, of "take \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w)", folded eq].

  have "s \<le>s ?w"
    using pref_prod_le[reversed, OF _ \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|\<close>[folded \<open>\<^bold>|?w\<^bold>| = \<^bold>|w\<^bold>|\<close>], of ?w]
    unfolding eq \<open>take \<^bold>|pw \<cdot> s\<^bold>| (w \<cdot> w) = pw \<cdot> s\<close> lassoc by blast

  show thesis
    using that[OF rotate_conjug \<open>p \<le>p ?w\<close> \<open>s \<le>s ?w\<close>].
qed

lemma rotate_into_pref_sq: assumes "p \<le>f w\<cdot>w" and  "\<^bold>|p\<^bold>| \<le> \<^bold>|w\<^bold>|"
obtains w' where "w \<sim> w'" "p \<le>p w'"
  using rotate_into_pos_sq[of \<epsilon>, unfolded emp_simps, OF \<open>p \<le>f w\<cdot>w\<close> _ \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|w\<^bold>|\<close>] by auto

lemmas rotate_into_suf_sq = rotate_into_pref_sq[reversed]

lemma rotate_into_pos: assumes "s\<cdot>p \<le>f w"
  obtains w' where "w \<sim> w'" "p \<le>p w'" "s \<le>s w'"
proof(rule rotate_into_pos_sq)
  show "s\<cdot>p \<le>f w\<cdot>w"
    using \<open>s \<cdot> p \<le>f w\<close> by blast
  show "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|"
    using order.trans[OF pref_len' fac_len[OF \<open>s \<cdot> p \<le>f w\<close>] ].
  show "\<^bold>|p\<^bold>| \<le> \<^bold>|w\<^bold>|"
    using order.trans[OF suf_len' fac_len[OF \<open>s \<cdot> p \<le>f w\<close>]].
qed

lemma rotate_into_pos_conjug: assumes "w \<sim> v" and "s\<cdot>p \<le>f v"
  obtains w' where "w \<sim> w'" "p \<le>p w'" "s \<le>s w'"
  using assms conjug_trans rotate_into_pos by metis

lemma nconjug_neq: "\<not> u \<sim> v \<Longrightarrow> u \<noteq> v"
  by blast

lemma prim_conjug:
  assumes prim: "primitive u" and conjug: "u \<sim> v"
  shows "primitive v"
proof -
  have "v \<noteq> \<epsilon>" using prim_nemp[OF prim] unfolding conjug_nemp_iff[OF conjug].
  from conjug[symmetric] obtain t where "v \<cdot> t = t \<cdot> u"..
  from this \<open>v \<noteq> \<epsilon>\<close> obtain r s i where
    v: "(r \<cdot> s)\<^sup>@i = v" and u: "(s \<cdot> r)\<^sup>@i = u" and prim': "primitive (r \<cdot> s)" and "0 < i"..
  have "r \<cdot> s = v" using v unfolding prim_exp_one[OF prim u] pow_1.
  show "primitive v" using prim' unfolding \<open>r \<cdot> s = v\<close>.
qed

lemma conjug_prim_iff: assumes "u \<sim> v" shows "primitive u = primitive v"
  using prim_conjug[OF _ \<open>u \<sim> v\<close>] prim_conjug[OF _ conjug_sym[OF \<open>u \<sim> v\<close>]]..

lemmas conjug_prim_iff' =  conjug_prim_iff[OF conjugI']

lemmas conjug_concat_prim_iff = conjug_concat_conjug[THEN conjug_prim_iff]

lemma conjug_eq_primrootE [elim, consumes 2]:
  assumes eq: "x \<cdot> z = z \<cdot> y" and "x \<noteq> \<epsilon>"
  obtains r s i n where
    "(r \<cdot> s)\<^sup>@i = x" and
    "(s \<cdot> r)\<^sup>@i = y" and
    "(r \<cdot> s)\<^sup>@n \<cdot> r = z" and
    "s \<noteq> \<epsilon>" and "0 < i" and "primitive (r \<cdot> s)"
     and "primitive (s \<cdot> r)"
  using conjug_eq_primrootE'[OF assms] conjug_prim_iff' by metis


lemma conjug_primrootsE: assumes "\<rho> p \<sim> \<rho> q"
  obtains r s k l where "p = (r \<cdot> s)\<^sup>@k" and "q = (s \<cdot> r)\<^sup>@l"  and "primitive (r\<cdot>s)"
proof(cases)
  assume "p = \<epsilon> \<and> q = \<epsilon>"
  obtain w::"'a list" where "primitive w"
    by blast
  from that[of w \<epsilon> 0 0, unfolded emp_simps]
  show ?thesis
    by (simp add: \<open>p = \<epsilon> \<and> q = \<epsilon>\<close> \<open>primitive w\<close>)
next
  assume "\<not> (p = \<epsilon> \<and> q = \<epsilon>)"
  hence "primitive (\<rho> p)"
    using assms conjug_prim_iff by auto
  from conjugE[OF \<open>\<rho> p \<sim> \<rho> q\<close>]
  obtain r s where
    "r \<cdot> s = \<rho> p" and
    "s \<cdot> r = \<rho> q".
  from that[of r s "e\<^sub>\<rho> p" "e\<^sub>\<rho> q", unfolded this, OF _ _ \<open>primitive (\<rho> p)\<close>]
  show ?thesis
    using primroot_exp_eq[symmetric]
    by blast
qed

lemma root_conjug: "u \<le>p r \<cdot> u \<Longrightarrow> u\<inverse>\<^sup>>(r\<cdot>u) \<sim> r"
  using conjugI1 conjug_sym lq_pref by metis

lemmas conjug_prim_iff_pref = conjug_prim_iff[OF root_conjug]

lemma conjug_primroot_word:
  assumes conjug: "u \<cdot> t = t \<cdot> v"
  shows "(\<rho> u) \<cdot> t = t \<cdot> (\<rho> v)"
proof (cases "u = \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  from \<open>u \<cdot> t = t \<cdot> v\<close> \<open>u \<noteq> \<epsilon>\<close> obtain r s i n where
    u: "(r \<cdot> s)\<^sup>@i = u" and v: "(s \<cdot> r)\<^sup>@i = v" and prim: "primitive (r \<cdot> s)"
    and "(r \<cdot> s)\<^sup>@n \<cdot> r = t" and "0 < i"..
  have rs: "\<rho> u = r \<cdot> s" and sr: "\<rho> v = s \<cdot> r"
    using prim_conjug[OF prim conjugI'] u v \<open>0 < i\<close> prim
     primroot_unique' by meson+
  show ?thesis
    unfolding \<open>(r \<cdot> s)\<^sup>@n \<cdot> r = t\<close>[symmetric] rs sr
    by comparison
next
  assume "u = \<epsilon>"
  hence "v = \<epsilon>"
    using assms by force
  show ?thesis
    unfolding \<open>u = \<epsilon>\<close> \<open>v = \<epsilon>\<close> by simp
qed

lemma conjug_primroot:
  assumes "u \<sim> v"
  shows "\<rho> u \<sim> \<rho> v"
proof(cases)
  assume "u = \<epsilon>" with \<open>u \<sim> v\<close> show "\<rho> u \<sim> \<rho> v"
    using conjug_nemp_iff by blast
next
  assume "u \<noteq> \<epsilon>"
  from \<open>u \<sim> v\<close> obtain t where "u \<cdot> t = t \<cdot> v"..
  from conjug_primroot_word[OF this]
  show "\<rho> u \<sim> \<rho> v"
    by (simp add: conjugI1)
qed

lemma conjug_primroots_nemp:  assumes "x \<cdot> y \<noteq> y \<cdot> x" and "r \<cdot> s = \<rho> (x \<cdot> y)" and  "s \<cdot> r = \<rho> (y \<cdot> x)"
  shows "r \<noteq> \<epsilon>" and "s \<noteq> \<epsilon>"
proof-
  have "x \<cdot> y \<noteq> \<epsilon>" and "y \<cdot> x \<noteq> \<epsilon>"
    using assms(1) by force+
  have "r \<noteq> \<epsilon> \<and> s \<noteq> \<epsilon>"
  proof (rule contrapos_np[OF assms(1)])
    assume "\<not> (r \<noteq> \<epsilon> \<and> s \<noteq> \<epsilon>)"
    hence "\<rho> (x \<cdot> y) = \<rho> (y \<cdot> x)"
      using assms(2-3) by force
    with comm_primroots[symmetric, OF \<open>x \<cdot> y \<noteq> \<epsilon>\<close> \<open>y \<cdot> x \<noteq> \<epsilon>\<close>]
    show "x \<cdot> y = y \<cdot> x"
      using eqd_eq[OF _ swap_len] by meson
  qed
  thus "r \<noteq> \<epsilon>" and "s \<noteq> \<epsilon>"
    by blast+
qed

lemma conjugE_primrootsE[elim]: assumes "x \<cdot> y \<noteq> y \<cdot> x"
  obtains r s where "r \<cdot> s = \<rho> (x \<cdot> y)" and "s \<cdot> r = \<rho> (y \<cdot> x)" and "r \<noteq> \<epsilon>" and "s \<noteq> \<epsilon>"
proof-
  have "\<rho> (x \<cdot> y) \<noteq> \<epsilon>"
    using assms by force
  from conjugE_nemp[OF conjug_primroot[OF conjugI', of x y] this] conjug_primroots_nemp[OF assms] that
  show thesis
    by auto
qed

lemma conjug_add_exp: "u \<sim> v \<Longrightarrow>  u\<^sup>@k \<sim> v\<^sup>@k"
  by (elim conjugE1, intro conjugI1, rule conjug_pow)

lemma conjug_primroot_iff:
  assumes nemp:"u \<noteq> \<epsilon>" and len: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
  shows "\<rho> u  \<sim> \<rho> v \<longleftrightarrow> u \<sim> v"
proof
  show "u \<sim> v \<Longrightarrow> \<rho> u  \<sim> \<rho> v" using conjug_primroot.
  assume conjug: "\<rho> u  \<sim> \<rho> v"
  have "v \<noteq> \<epsilon>" using nemp_len[OF nemp] unfolding len length_0_conv.
  with nemp obtain k l where roots: "(\<rho> u)\<^sup>@k = u" "(\<rho> v)\<^sup>@l = v"
    using primroot_exp_eq by blast

  have "\<^bold>|(\<rho> u)\<^sup>@k\<^bold>| = \<^bold>|(\<rho> v)\<^sup>@l\<^bold>|" using len unfolding roots.
  then have "k = l" using primroot_nemp[OF \<open>v \<noteq> \<epsilon>\<close>]
    unfolding pow_len conjug_len[OF conjug] by simp
  show "u \<sim> v" using conjug_add_exp[OF conjug, of l] unfolding roots[unfolded \<open>k = l\<close>].
qed

lemma two_conjugs_aux: assumes "u\<cdot>v = x\<cdot>y" and "v\<cdot>u = y\<cdot>x" and "u \<noteq> \<epsilon>" and  "u \<noteq> x" and "\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|"
  obtains r s k l m n where
    "u = (s \<cdot> r)\<^sup>@k \<cdot> s" and  "v = (r \<cdot> s)\<^sup>@l \<cdot> r" and
    "x = (s \<cdot> r)\<^sup>@m \<cdot> s" and  "y = (r \<cdot> s)\<^sup>@n \<cdot> r" and
    "primitive (r \<cdot> s)" and "primitive (s \<cdot> r)"
proof-
  have "\<^bold>|u\<^bold>| < \<^bold>|x\<^bold>|"
    using \<open>u \<noteq> x\<close> eqd_eq(1)[OF \<open>u\<cdot>v = x\<cdot>y\<close>] le_neq_implies_less[OF \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>] by blast
  hence "x \<noteq> \<epsilon>"
    by force
  from eqd_lessE[OF \<open>u\<cdot>v = x\<cdot>y\<close> \<open>\<^bold>|u\<^bold>| < \<^bold>|x\<^bold>|\<close>]
  obtain t where "u \<cdot> t = x" "t \<cdot> y = v" "t \<noteq> \<epsilon>".
  from \<open>v\<cdot>u = y\<cdot>x\<close>[folded this(1-2)]
  obtain exp where "y \<cdot> u = (\<rho> t)\<^sup>@exp"
    using comm_primroot_exp[OF \<open>t \<noteq> \<epsilon>\<close>, of "y \<cdot> u"] unfolding rassoc by metis
  hence "0 < exp"
    using \<open>u \<noteq> \<epsilon>\<close> by blast
  from split_pow[OF \<open>y \<cdot> u = (\<rho> t)\<^sup>@exp\<close> this \<open>u \<noteq> \<epsilon>\<close>]
  obtain r s n k  where  "u = (s \<cdot> r)\<^sup>@k \<cdot> s" "y = (r \<cdot> s)\<^sup>@n \<cdot> r" "r \<cdot> s = \<rho> t"
    by metis
  have "primitive (r \<cdot> s)"
    unfolding \<open>r \<cdot> s = \<rho> t\<close> using \<open>t \<noteq> \<epsilon>\<close> by blast
  hence "primitive (s \<cdot> r)"
    using conjug_prim_iff' by blast
  define e where "e = e\<^sub>\<rho> t"
  have t: "t = (r\<cdot>s)\<^sup>@e"
    unfolding \<open>r \<cdot> s = \<rho> t\<close> e_def by simp
  have eq1: "t \<cdot> (r \<cdot> s) \<^sup>@ n \<cdot> r = (r \<cdot> s) \<^sup>@ (e\<^sub>\<rho> t + n) \<cdot> r"
    unfolding add_exps \<open>r \<cdot> s = \<rho> t\<close> primroot_exp_eq rassoc..
  have eq2: "((s \<cdot> r) \<^sup>@ k \<cdot> s) \<cdot> t = (s \<cdot> r) \<^sup>@ (k + e) \<cdot> s"
    unfolding t by comparison
  show thesis
    using that[OF \<open>u = (s \<cdot> r)\<^sup>@k \<cdot> s\<close> _ _  \<open>y = (r \<cdot> s)\<^sup>@n \<cdot> r\<close> \<open>primitive (r \<cdot> s)\<close> \<open>primitive (s \<cdot> r)\<close>,
          folded \<open>u \<cdot> t = x\<close> \<open>t \<cdot> y = v\<close>, unfolded \<open>u = (s \<cdot> r)\<^sup>@k \<cdot> s\<close> \<open>y = (r \<cdot> s)\<^sup>@n \<cdot> r\<close>, OF eq1 eq2].
qed

lemma two_conjugs: assumes "u\<cdot>v = x\<cdot>y" and "v\<cdot>u = y\<cdot>x" and "u \<noteq> \<epsilon>" and "x \<noteq> \<epsilon>" and "u \<noteq> x"
  obtains r s k l m n where
    "u = (s \<cdot> r)\<^sup>@k \<cdot> s" and  "v = (r \<cdot> s)\<^sup>@l \<cdot> r" and
    "x = (s \<cdot> r)\<^sup>@m \<cdot> s" and  "y = (r \<cdot> s)\<^sup>@n \<cdot> r" and
    "primitive (r \<cdot> s)" and "primitive (s \<cdot> r)"
  by (rule le_cases[of "\<^bold>|u\<^bold>|" "\<^bold>|x\<^bold>|"],
  use two_conjugs_aux[OF assms(1-3,5)] in metis)
  (use two_conjugs_aux[OF assms(1-2)[symmetric] assms(4) assms(5)[symmetric]] in metis)

lemma fac_pow_pref_conjug:
  assumes "u \<le>f t\<^sup>@k"
  obtains t' where "t \<sim> t'" and "u \<le>p t'\<^sup>@k"
proof (cases "t = \<epsilon>")
  assume "t \<noteq> \<epsilon>"
  obtain p q where eq: "p \<cdot> u \<cdot> q = t\<^sup>@k" using facE'[OF assms].
  obtain i r where "i \<le> k" and "r <p t" and p: "t\<^sup>@i \<cdot> r = p"
    using pref_mod_pow[OF prefI[OF eq] \<open>t \<noteq>\<epsilon>\<close>].
  from \<open>r <p t\<close> obtain s where t: "r \<cdot> s = t"..
  have eq': "t\<^sup>@i \<cdot> r \<cdot> (u \<cdot> q) = t\<^sup>@k" using eq unfolding lassoc p.
  have  "u \<le>p (s \<cdot> r)\<^sup>@k" using pow_conjug[OF eq' t] unfolding rassoc..
  with conjugI'[of r s] show thesis unfolding t..
qed (use assms in auto)

lemmas fac_pow_suf_conjug = fac_pow_pref_conjug[reversed]

lemma fac_pow_len_conjug[intro]: assumes  "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|" and "u \<le>f v\<^sup>@k" shows "v \<sim> u"
proof-
  obtain t where "v \<sim> t" and "u \<le>p t\<^sup>@k"
    using fac_pow_pref_conjug[OF \<open>u \<le>f v \<^sup>@ k\<close>].
  have "u = t"
    using pref_prod_eq[OF pref_prod_root[OF \<open>u \<le>p t\<^sup>@k\<close>] conjug_len[OF \<open>v \<sim> t\<close>,folded \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close>]].
  from \<open>v \<sim> t\<close>[folded this]
  show "v \<sim> u".
qed

lemma conjug_fac_sq:
  "u \<sim> v \<Longrightarrow> u \<le>f v \<cdot> v"
  by (elim conjugE, unfold eq_commute[of "_ \<cdot> _"]) (intro facI', simp)

lemma conjug_fac_pow_conv: assumes "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|" and "2 \<le> k"
  shows "u \<sim> v \<longleftrightarrow> u \<le>f v\<^sup>@k"
proof
  assume "u \<sim> v"
  have f:  "v \<cdot> v \<le>f v \<^sup>@k"
    using \<open>2 \<le> k\<close>  unfolding pow_two[symmetric] using le_exps_pref by blast
  from fac_trans[OF conjug_fac_sq[OF \<open>u \<sim> v\<close>] this]
  show "u \<le>f v \<^sup>@ k".
next
  show " u \<le>f v \<^sup>@ k \<Longrightarrow> u \<sim> v"
    using fac_pow_len_conjug[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close>, THEN conjug_sym].
qed

lemma conjug_fac_Suc: assumes "t \<sim> v"
  shows "t\<^sup>@k \<le>f v\<^sup>@Suc k"
proof-
  obtain r s where "v = r \<cdot> s" and "t = s \<cdot> r"
    using \<open>t \<sim> v\<close> by blast
  show ?thesis
    unfolding \<open>v = r \<cdot> s\<close> \<open>t = s \<cdot> r\<close>
    unfolding pow_slide[of r s k, symmetric]
    by force
qed

lemma fac_pow_conjug: assumes "u \<le>f v\<^sup>@k" and  "t \<sim> v"
  shows "u \<le>f t\<^sup>@Suc k"
proof-
  obtain r s where "v = r \<cdot> s" and "t = s \<cdot> r"
    using \<open>t \<sim> v\<close> by blast
  have "s \<cdot> v\<^sup>@k \<cdot> r = t\<^sup>@Suc k"
    unfolding \<open>v = r \<cdot> s\<close> \<open>t = s \<cdot> r\<close> shift_pow pow_Suc rassoc..
  from facI[of "v\<^sup>@k" s r, unfolded this]
  show "u \<le>f t\<^sup>@Suc k"
    using \<open>u \<le>f v\<^sup>@k\<close> by blast
qed

lemma border_conjug: "x \<le>b w \<Longrightarrow> w\<^sup><\<inverse>x \<sim> x\<inverse>\<^sup>>w"
  using border_conjug_eq conjugI1 by blast

lemma count_list_conjug: assumes "u \<sim> v" shows "count_list u a = count_list v a"
proof-
  from  conjugE[OF \<open>u \<sim> v\<close>]
  obtain r s where "r \<cdot> s = u" "s \<cdot> r = v".
  show "count_list u a = count_list v a"
    unfolding \<open>r \<cdot> s = u\<close>[symmetric] \<open>s \<cdot> r = v\<close>[symmetric] count_list_append by presburger
qed

lemma conjug_in_lists: "us \<sim> vs \<Longrightarrow> vs \<in> lists A \<Longrightarrow> us \<in> lists A"
  unfolding conjugate_def  by auto

lemma conjug_in_lists': "us \<sim> vs \<Longrightarrow> us \<in> lists A \<Longrightarrow> vs \<in> lists A"
  unfolding conjugate_def  by auto

lemma conjug_in_lists_iff: "us \<sim> vs \<Longrightarrow> us \<in> lists A \<longleftrightarrow> vs \<in> lists A"
  unfolding conjugate_def  by auto


lemma prim_conjug_unique: assumes "primitive (u \<cdot> v)" and "u \<cdot> v = r \<cdot> s" and "v \<cdot> u = s \<cdot> r" and "u \<cdot> v \<noteq> v \<cdot> u"
  shows "u = r" and "v = s"
proof-
  have "u = r" if "primitive (u \<cdot> v)" and "u \<cdot> v = r \<cdot> s" and "v \<cdot> u = s \<cdot> r" and "u \<cdot> v  \<noteq> v \<cdot> u" and  "\<^bold>|v\<^bold>| \<le> \<^bold>|s\<^bold>|" for u v r s :: "'a list"
  proof-
    from eqdE[OF \<open>v \<cdot> u = s \<cdot> r\<close> \<open>\<^bold>|v\<^bold>| \<le> \<^bold>|s\<^bold>|\<close>]
    obtain t where "v \<cdot> t = s" "t \<cdot> r = u".
    have "t \<cdot> (r \<cdot> v) = (r \<cdot> v) \<cdot> t"
      unfolding lassoc \<open>t \<cdot> r = u\<close> unfolding rassoc \<open>v \<cdot> t = s\<close> by fact
    from comm_not_prim[OF _ _ this, unfolded lassoc \<open>t \<cdot> r = u\<close>]
    have "t = \<epsilon>"
      using \<open>primitive (u \<cdot> v)\<close> \<open>u \<cdot> v \<noteq> v \<cdot> u\<close> by blast
    thus "u = r"
      using \<open>t \<cdot> r = u\<close> by force
  qed
  from this[OF assms]
  this[OF \<open>primitive (u \<cdot> v)\<close>[unfolded \<open>u \<cdot> v = r \<cdot> s\<close>] assms(2-3)[symmetric] assms(4)[unfolded \<open>u \<cdot> v = r \<cdot> s\<close> \<open>v \<cdot> u = s \<cdot> r\<close>]]
  show "u = r"
    by fastforce
  thus "v = s"
    using \<open>u \<cdot> v = r \<cdot> s\<close> by fast
qed

lemma prim_conjugE[elim, consumes 3]:  assumes "(u \<cdot> v) \<cdot> z = z \<cdot> (v \<cdot> u)" and "primitive (u \<cdot> v)" and "v \<noteq> \<epsilon>"
  obtains k where "(u \<cdot> v)\<^sup>@k \<cdot> u = z"
proof-
  from conjug_eqE[OF assms(1) prim_nemp[OF assms(2)]]
  obtain x y m where "x \<cdot> y = u \<cdot> v" and "y \<cdot> x = v \<cdot> u" and "(x \<cdot> y)\<^sup>@m \<cdot> x = z" and "y \<noteq> \<epsilon>".
  from prim_conjug_unique[OF \<open>primitive (u \<cdot> v)\<close> \<open>x \<cdot> y = u \<cdot> v\<close>[symmetric] \<open>y \<cdot> x = v \<cdot> u\<close>[symmetric]]
  consider "u \<cdot> v = v \<cdot> u" | "u = x \<and> v = y" by blast
  thus thesis
  proof (cases)
    assume "u \<cdot> v = v \<cdot> u"
    from comm_not_prim[OF _ \<open>v \<noteq> \<epsilon>\<close> this] \<open>primitive (u \<cdot> v)\<close>
    have "u = \<epsilon>" by blast
    from \<open>(u \<cdot> v) \<cdot> z = z \<cdot> (v \<cdot> u)\<close>[symmetric] \<open>primitive (u \<cdot> v)\<close>
    obtain k where "z = (u \<cdot> v)\<^sup>@k \<cdot> u"
      unfolding \<open>u = \<epsilon>\<close> emp_simps  by blast
    from that[OF this[symmetric]]
    show thesis.
  next
    assume "u = x \<and> v = y"
    with \<open>(x \<cdot> y)\<^sup>@m \<cdot> x = z\<close> that
    show thesis by blast
  qed
qed

lemma prim_conjugE'[elim, consumes 3]: assumes "(r \<cdot> s) \<cdot> z = z \<cdot> (s \<cdot> r)" and "primitive (r \<cdot> s)" and "z \<noteq> \<epsilon>"
  obtains k where "(r \<cdot> s)\<^sup>@k \<cdot> r = z"
proof (cases \<open>s = \<epsilon>\<close>)
  assume "s = \<epsilon>"
  from assms(1-2)[unfolded this emp_simps]
  have  "primitive r" and "z \<cdot> r = r \<cdot> z"  by force+
  from prim_comm_exp[OF this]
  obtain k where "z = r\<^sup>@k" "0 < k"
    using nemp_exp_pos[OF \<open>z \<noteq> \<epsilon>\<close>] by metis
  have "r\<^sup>@(k-1)\<cdot>r = z"
    unfolding pow_pos'[OF \<open>0 < k\<close>, of r, folded \<open>z = r\<^sup>@k\<close>]..
  from that[unfolded \<open>s = \<epsilon>\<close> emp_simps, OF this]
  show thesis.
qed (use prim_conjugE[OF assms(1-2)] in blast)

lemma conjug_primroots_unique:  assumes "x \<cdot> y \<noteq> y \<cdot> x" and
       "r \<cdot> s = \<rho> (x \<cdot> y)" and  "s \<cdot> r = \<rho> (y \<cdot> x)" and
       "r' \<cdot> s' = \<rho> (x \<cdot> y)" and  "s' \<cdot> r' = \<rho> (y \<cdot> x)"
     shows "r = r'" and "s = s'"
proof-
  have "x \<cdot> y \<noteq> \<epsilon>" and "y \<cdot> x \<noteq> \<epsilon>" and "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" and "(x \<cdot> y) \<cdot> (y \<cdot> x) \<noteq> (y \<cdot> x) \<cdot> (x \<cdot> y)"
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> eqd_eq[OF _ swap_len] by blast+
  show "r = r'"
  proof (rule prim_conjug_unique(1))
    from primroot_prim[OF \<open>x \<cdot> y \<noteq> \<epsilon>\<close>, folded \<open>r \<cdot> s = \<rho> (x \<cdot> y)\<close>]
    show "primitive (r \<cdot> s)".
    from \<open>r \<cdot> s = \<rho> (x \<cdot> y)\<close>[folded \<open>r' \<cdot> s' = \<rho> (x \<cdot> y)\<close>] \<open>s \<cdot> r = \<rho> (y \<cdot> x)\<close>[folded \<open>s' \<cdot> r' = \<rho> (y \<cdot> x)\<close>]
    show "r \<cdot> s = r' \<cdot> s'" and "s \<cdot> r = s' \<cdot> r'".
    show "r \<cdot> s \<noteq> s \<cdot> r"
      unfolding \<open>r \<cdot> s = \<rho> (x \<cdot> y)\<close>  \<open>s \<cdot> r = \<rho> (y \<cdot> x)\<close>
      using same_primroots_comm \<open>(x \<cdot> y) \<cdot> (y \<cdot> x) \<noteq> (y \<cdot> x) \<cdot> (x \<cdot> y)\<close> by blast
  qed
  thus "s = s'"
    using \<open>r \<cdot> s = \<rho> (x \<cdot> y)\<close>[folded \<open>r' \<cdot> s' = \<rho> (x \<cdot> y)\<close>] by blast
qed

lemma prim_conjug_pref: assumes "primitive (s \<cdot> r)" and "u \<cdot> r \<cdot> s \<le>p (s \<cdot> r)\<^sup>@n" and "r \<noteq> \<epsilon>"
  obtains n where "(s \<cdot> r)\<^sup>@n \<cdot> s = u"
proof-
  have "u \<cdot> r \<cdot> s \<le>p (s \<cdot> r \<cdot> u) \<cdot> r \<cdot> s"
    using pref_prod_root[OF \<open>u \<cdot> r \<cdot> s \<le>p (s \<cdot> r)\<^sup>@n\<close>] unfolding rassoc.
  from pref_prod_eq[OF this, unfolded lenmorph]
  have "(s \<cdot> r) \<cdot> u = u \<cdot> (r \<cdot> s)"
    unfolding rassoc by force
  from prim_conjugE[OF this \<open>primitive (s \<cdot> r)\<close> \<open>r \<noteq> \<epsilon>\<close>]
  show thesis
    using that.
qed

lemma fac_per_conjug: assumes "period w n" and  "v \<le>f w" and "\<^bold>|v\<^bold>| = n"
  shows "v \<sim> take n w"
proof-
  have "\<^bold>|take n w\<^bold>| = \<^bold>|v\<^bold>|"
    using fac_len[OF \<open>v \<le>f w\<close>] \<open>\<^bold>|v\<^bold>| = n\<close> take_len by blast
  from per_root_powE'[OF \<open>period w n\<close>[unfolded period_def]]
  obtain k where "w \<le>p take n w \<^sup>@ k".
  from fac_pow_len_conjug[OF \<open>\<^bold>|take n w\<^bold>| = \<^bold>|v\<^bold>|\<close>[symmetric], THEN conjug_sym]
       fac_trans[OF  \<open>v \<le>f w\<close> pref_fac, OF this]
  show ?thesis.
qed

lemma fac_pers_conjug: assumes "period w n" and  "v \<le>f w" and "\<^bold>|v\<^bold>| = n" and "u \<le>f w" and "\<^bold>|u\<^bold>| = n"
  shows "v \<sim> u"
  using  conjug_trans[OF fac_per_conjug[OF \<open>period w n\<close> \<open>v \<le>f w\<close> \<open>\<^bold>|v\<^bold>| = n\<close>]
      conjug_sym[OF fac_per_conjug[OF \<open>period w n\<close> \<open>u \<le>f w\<close> \<open>\<^bold>|u\<^bold>| = n\<close>]]].

lemma conjug_pow_powE: assumes "w \<sim> r\<^sup>@k" obtains s where "w = s\<^sup>@k"
proof-
  obtain u v where "w = u \<cdot> v" and "v \<cdot> u = r\<^sup>@k"
    using assms by blast
  have "w = (v\<inverse>\<^sup>>(r\<cdot>v))\<^sup>@k"
    unfolding \<open>w = u \<cdot> v\<close> lq_conjug_pow[OF pref_prod_root, OF prefI[OF \<open>v \<cdot> u = r \<^sup>@ k\<close>], symmetric] \<open>v \<cdot> u = r \<^sup>@ k\<close>[symmetric]
    by simp
  from that[OF this]
  show thesis.
qed

lemma find_second_letter:  assumes "a \<noteq> b" and  "set ws = {a,b}"
  shows "dropWhile (\<lambda> c. c = a) ws \<noteq> \<epsilon>" and "hd (dropWhile (\<lambda> c. c = a) ws) = b"
proof-
  let ?a = "(\<lambda> c. c = a)"

  define wsb where "wsb = dropWhile ?a ws \<cdot> takeWhile ?a ws"
  have "wsb \<sim> ws"
    unfolding wsb_def using takeWhile_dropWhile_id[of ?a ws] conjugI' by blast
  hence "set wsb = {a,b}"
    using \<open>set ws = {a,b}\<close> by (simp add: conjug_set)

  have "takeWhile ?a ws \<noteq> ws"
    unfolding takeWhile_eq_all_conv using \<open>set ws = {a,b}\<close> \<open>a \<noteq> b\<close> by simp
  thus "dropWhile ?a ws \<noteq> \<epsilon>" by simp
  from hd_dropWhile[OF this] set_dropWhileD[OF hd_in_set[OF this], unfolded \<open>set ws = {a,b}\<close>]
  show "hd (dropWhile ?a ws) = b"
    by blast
qed

lemma fac_conjuq_sq:
  assumes "u \<sim> v" and "\<^bold>|w\<^bold>| \<le> \<^bold>|u\<^bold>|" and "w \<le>f u \<cdot> u"
  shows "w \<le>f v \<cdot> v"
proof -
  have assm_le: "w \<le>f s \<cdot> r \<cdot> s \<cdot> r"
    if "p \<cdot> w \<cdot> q = r \<cdot> s \<cdot> r \<cdot> s" and "\<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>|" for w s r p q :: "'a list"
  proof -
    obtain p' where "r \<cdot> p' = p"
      using \<open>p \<cdot> w \<cdot> q = r \<cdot> s \<cdot> r \<cdot> s\<close> \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>|\<close> unfolding rassoc by (rule eqdE[OF sym])
    show "w \<le>f s \<cdot> r \<cdot> s \<cdot> r"
      using \<open>p \<cdot> w \<cdot> q = r \<cdot> s \<cdot> r \<cdot> s\<close>
      by (intro facI'[of p' _ "q \<cdot> r"]) (simp flip: \<open>r \<cdot> p' = p\<close>)
  qed
  obtain r s where "r \<cdot> s = u" and "s \<cdot> r = v" using \<open>u \<sim> v\<close>..
  obtain p q where "p \<cdot> w \<cdot> q = u \<cdot> u" using \<open>w \<le>f u \<cdot> u\<close> ..
  from lenarg[OF this] \<open>\<^bold>|w\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>
  have "\<^bold>|r\<^bold>| \<le> \<^bold>|p\<^bold>| \<or> \<^bold>|s\<^bold>| \<le> \<^bold>|q\<^bold>|"
    unfolding \<open>r \<cdot> s = u\<close>[symmetric] lenmorph by linarith
  then show "w \<le>f v \<cdot> v"
    using \<open>p \<cdot> w \<cdot> q = u \<cdot> u\<close> unfolding \<open>r \<cdot> s = u\<close>[symmetric] \<open>s \<cdot> r = v\<close>[symmetric]
    by (elim disjE) (simp only: assm_le rassoc, simp only: assm_le[reversed] lassoc)
qed

lemma fac_conjuq_sq_iff:
  assumes "u \<sim> v" shows "\<^bold>|w\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> w \<le>f u \<cdot> u \<longleftrightarrow> w \<le>f v \<cdot> v"
  using fac_conjuq_sq[OF \<open>u \<sim> v\<close>] fac_conjuq_sq[OF \<open>u \<sim> v\<close>[symmetric]]
  unfolding conjug_len[OF \<open>u \<sim> v\<close>[symmetric]]..

lemma map_conjug:
  "u \<sim> v \<Longrightarrow> map f u \<sim> map f v"
  by (elim conjugE, unfold eq_commute[of "_ \<cdot> _"]) auto

lemma map_conjug_iff [reversal_rule]:
  assumes "inj f" shows "map f u \<sim> map f v \<longleftrightarrow> u \<sim> v"
  using map_conjug map_conjug[of "map f u" "map f v" "inv f"]
  unfolding map_map inv_o_cancel[OF \<open>inj f\<close>] list.map_id by (intro iffI)

lemma card_conjug: assumes "w \<noteq> \<epsilon>"
  shows "card (Collect (conjugate w)) = \<^bold>|\<rho> w\<^bold>|"
proof-
  define f where "f = (\<lambda>n. rotate n w)"

  have "\<rho> w \<noteq> \<epsilon>"
    by (simp add: assms primroot_nemp)
  obtain k where "(\<rho> w)\<^sup>@k = w"
    using primroot_expE
    by blast
  have "f`{0..<\<^bold>|\<rho> w\<^bold>|} = {w'. w \<sim> w'}"
    unfolding set_eq_iff
    unfolding mem_Collect_eq conjug_rotate_iff image_iff
    unfolding atLeast0LessThan
    unfolding f_def
    using lessThan_iff rotate_pow_mod[of _ "\<rho> w" k] mod_less_divisor[OF nemp_pos_len[OF \<open>\<rho> w \<noteq> \<epsilon>\<close>]]
    unfolding \<open>(\<rho> w)\<^sup>@k = w\<close>
    by meson

  have "inj_on f {0..<\<^bold>|\<rho> w\<^bold>|}"
  proof (rule inj_onI)
    fix x y
    assume "x \<in> {0..<\<^bold>|\<rho> w\<^bold>|}" "y \<in> {0..<\<^bold>|\<rho> w\<^bold>|}" "f x = f y"
    hence roxy: "rotate x (\<rho> w) = rotate y (\<rho> w)"
      unfolding f_def
      by (metis assms primroot_rotate_comm)
    show "x = y"
      using prim_no_rotate[OF primroot_prim[OF \<open>w \<noteq> \<epsilon>\<close>]] rotate_back'[OF roxy] rotate_back'[OF roxy[symmetric]] \<open>x \<in> {0..<\<^bold>|\<rho> w\<^bold>|}\<close> \<open>y \<in> {0..<\<^bold>|\<rho> w\<^bold>|}\<close>
      unfolding atLeast0LessThan lessThan_iff
      using bot_nat_0.not_eq_extremum less_imp_diff_less nat_le_linear zero_diff_eq by metis
  qed
  from card_image[OF this]
  show ?thesis
    unfolding \<open>f ` {0..<\<^bold>|\<rho> w\<^bold>|} = {w'. w \<sim> w'}\<close>
    unfolding atLeast0LessThan card_lessThan.
qed

lemma finite_Bex_conjug: assumes "finite A"
  shows "finite {r. Bex A (conjugate r)}"
  unfolding finite_Collect_bex[OF \<open>finite A\<close>, of conjugate]
proof
  fix y
  assume "y \<in> A"
  show "finite {r. r \<sim> y}"
  proof(cases "y = \<epsilon>")
    case True
    then show ?thesis
      unfolding conjug_swap[of _ y]
      by (metis (mono_tags, opaque_lifting) \<open>y \<in> A\<close> assms conjug_nemp_iff finite_subset mem_Collect_eq subset_eq)
  next
    case False
    then show ?thesis
      unfolding conjug_swap[of _ y]
      by (simp add: card_conjug card_ge_0_finite primroot_nemp)
  qed
qed

subsection \<open>Enumerating conjugates\<close>

definition bounded_conjug
  where "bounded_conjug w' w k \<equiv> (\<exists> n \<le> k. w = rotate n w')"

named_theorems bounded_conjug

lemma[bounded_conjug]: "bounded_conjug w' w 0 \<longleftrightarrow> w = w'"
  unfolding bounded_conjug_def by auto

lemma[bounded_conjug]: "bounded_conjug w' w (Suc k) \<longleftrightarrow> bounded_conjug w' w k \<or> w = rotate (Suc k) w'"
  unfolding bounded_conjug_def using le_SucE le_imp_less_Suc le_less by metis

lemma[bounded_conjug]: "w' \<sim> w \<longleftrightarrow> bounded_conjug w w' (\<^bold>|w\<^bold>|-1)"
  unfolding bounded_conjug_def conjug_swap[of w'] using conjug_rotate_iff_le.

lemma "w \<sim> [a,b,c] \<longleftrightarrow> w = [a,b,c] \<or> w = [b,c,a] \<or> w = [c,a,b]"
  by (simp add: bounded_conjug)

subsection \<open>General lemmas using  conjugation\<close>

lemma switch_fac: assumes "x \<noteq> y" and  "set ws = {x,y}" shows "[x,y] \<le>f ws \<cdot> ws"
proof-
  let ?y = "(\<lambda> a. a = y)" and ?x = "(\<lambda> a. a = x)"
  have "ws \<noteq> \<epsilon>"
    using \<open>set ws = {x,y}\<close> by force

  define wsx where "wsx = dropWhile ?y ws \<cdot> takeWhile ?y ws"
  have "wsx \<sim> ws"
    unfolding wsx_def using takeWhile_dropWhile_id[of ?y ws] conjugI' by blast
  have "set wsx = {x,y}"
    unfolding wsx_def using \<open>set ws = {x,y}\<close> conjugI' conjug_set takeWhile_dropWhile_id by metis
  from find_second_letter[OF  \<open>x \<noteq> y\<close>[symmetric] \<open>set ws = {x,y}\<close>[unfolded insert_commute[of x]]]
  have  "dropWhile (\<lambda>c. c = y) ws \<noteq> \<epsilon>" and "hd wsx = x"
    unfolding wsx_def using hd_append by simp_all
  hence "takeWhile ?x wsx \<noteq> \<epsilon>"
    unfolding wsx_def takeWhile_eq_Nil_iff by blast
  from root_nemp_expE[OF takeWhile_sing_root[of x wsx] this]
  obtain k where [symmetric]: "[x]\<^sup>@k = takeWhile ?x wsx" and "0 < k".
  note find_second_letter[OF \<open>x \<noteq> y\<close> \<open>set wsx = {x,y}\<close>]
  have "wsx = [x]\<^sup>@(k - 1) \<cdot> [x] \<cdot> [hd (dropWhile ?x wsx)] \<cdot> tl (dropWhile ?x wsx)"
    unfolding lassoc pow_pos'[OF \<open>0 < k\<close>,symmetric] \<open>takeWhile ?x wsx = [x]\<^sup>@k\<close>[symmetric]
    unfolding rassoc hd_tl[OF \<open>dropWhile ?x wsx \<noteq> \<epsilon>\<close>] takeWhile_dropWhile_id..
  from this[unfolded \<open>hd (dropWhile ?x wsx) = y\<close>]
  have "[x,y] \<le>f wsx" by (auto simp add: fac_def)
  thus "[x,y] \<le>f ws \<cdot> ws"
    using fac_trans[OF _ conjug_fac_sq[OF \<open>wsx \<sim> ws\<close>]] by blast
qed

lemma imprim_ext_pref_comm: assumes "\<not> primitive (u \<cdot> v)" and "\<not> primitive (u \<cdot> v \<cdot> u)"
  shows "u \<cdot> v = v \<cdot> u"
using \<open>\<not> primitive (u \<cdot> v)\<close> proof (elim not_prim_primroot_expE)
  fix z n assume "z \<^sup>@ n = u \<cdot> v" and "2 \<le> n"
  have "2 * \<^bold>|z\<^bold>| \<le> \<^bold>|u \<cdot> v \<cdot> u\<^bold>|"
    by (simp add: pow_len \<open>2 \<le> n\<close> trans_le_add1 flip: \<open>z\<^sup>@n = u \<cdot> v\<close> rassoc)
  moreover have "u \<cdot> v \<cdot> u \<le>p z \<cdot> u \<cdot> v \<cdot> u"
    by (intro pref_prod_root[of _ _ "n + n"]) (simp add: \<open>z \<^sup>@ n = u \<cdot> v\<close> add_exps)
  ultimately have "(u \<cdot> v \<cdot> u) \<cdot> z = z \<cdot> u \<cdot> v \<cdot> u"
    using \<open>\<not> primitive (u \<cdot> v \<cdot> u)\<close>  per_le_prim_iff
    by (cases "z = \<epsilon>") blast+
  from comm_add_exp[OF this[symmetric], of n]
  show "u \<cdot> v = v \<cdot> u"
    unfolding \<open>z \<^sup>@ n = u \<cdot> v\<close> by simp
qed

lemma imprim_ext_suf_comm:
  "\<not> primitive (u \<cdot> v) \<Longrightarrow> \<not> primitive (u \<cdot> v \<cdot> v) \<Longrightarrow> u \<cdot> v = v \<cdot> u"
  by (intro imprim_ext_pref_comm[symmetric])
     (unfold conjug_prim_iff[OF conjugI', of v] rassoc)

lemma prim_xyky: assumes "2 \<le> k" and "\<not> primitive ((x \<cdot> y)\<^sup>@k \<cdot> y)" shows "x \<cdot> y = y \<cdot> x"
proof-
  have "k \<noteq> 0" using \<open>2 \<le> k\<close> by simp
  have "(x \<cdot> y)\<^sup>@k = (x \<cdot> y)\<^sup>@(k - 1) \<cdot> x \<cdot> y"
    unfolding rassoc pow_Suc'[symmetric] Suc_minus[OF \<open>k \<noteq> 0\<close>]..
  have "(x \<cdot> y)\<^sup>@k \<cdot> y = ((x \<cdot> y)\<^sup>@(k -1) \<cdot> x) \<cdot> y \<cdot> y"
    unfolding lassoc cancel_right unfolding rassoc pow_Suc'[symmetric] Suc_minus[OF \<open>k \<noteq> 0\<close>]..
  from imprim_ext_suf_comm[OF _ \<open>\<not> primitive ((x \<cdot> y)\<^sup>@k \<cdot> y)\<close>[unfolded this],
       unfolded rassoc pow_Suc'[symmetric] Suc_minus[OF \<open>k \<noteq> 0\<close>], OF pow_nemp_imprim[OF \<open>2 \<le> k\<close>]]
  show "x \<cdot> y = y \<cdot> x"
    unfolding \<open>(x \<cdot> y)\<^sup>@k = (x \<cdot> y)\<^sup>@(k -1) \<cdot> x \<cdot> y\<close> shift_pow
     pow_Suc'[of "x \<cdot> y", unfolded rassoc, symmetric] pow_Suc[of "y \<cdot> x", unfolded rassoc, symmetric]
    using pow_eq_eq by blast
qed

lemma fac_pow_div: assumes "u \<le>f w\<^sup>@l" "primitive w"
  shows "w\<^sup>@((\<^bold>|u\<^bold>| div \<^bold>|w\<^bold>|) - 1) \<le>f u"
proof-
  obtain w' where
    "w \<sim> w'" and
    "u \<le>p w' \<^sup>@ l"
    using fac_pow_pref_conjug[OF \<open>u \<le>f w\<^sup>@l\<close>].

  note prim_nemp[OF \<open>primitive w\<close>]
  hence "w' \<noteq> \<epsilon>"
    using conjug_nemp_iff \<open>w \<sim> w'\<close> by blast

  obtain s where  "s <p w'" and  "w' \<^sup>@ (\<^bold>|u\<^bold>| div \<^bold>|w'\<^bold>|) \<cdot> s = u"
    using per_root_modE'[OF per_rootI', OF \<open>u \<le>p w' \<^sup>@ l\<close> \<open>w' \<noteq> \<epsilon>\<close>].

  have "w\<^sup>@((\<^bold>|u\<^bold>| div \<^bold>|w\<^bold>|) - 1) \<le>f w' \<^sup>@ (\<^bold>|u\<^bold>| div \<^bold>|w'\<^bold>|)"
    unfolding conjug_len[OF \<open>w \<sim> w'\<close>]
    using conjug_fac_Suc[OF \<open>w \<sim> w'\<close>]
    by (cases "(\<^bold>|u\<^bold>| div \<^bold>|w'\<^bold>|) = 0", force)
    (use Suc_minus in metis)
  thus ?thesis
    using fac_ext_suf[of _ "w' \<^sup>@ (\<^bold>|u\<^bold>| div \<^bold>|w'\<^bold>|)" s, unfolded \<open>w' \<^sup>@ (\<^bold>|u\<^bold>| div \<^bold>|w'\<^bold>|) \<cdot> s = u\<close>]
    by presburger
qed

section \<open>Element of lists: a method for testing if a word is in lists A\<close>

lemma append_in_lists[simp, intro]: "u \<in> lists A \<Longrightarrow> v \<in> lists A \<Longrightarrow> u \<cdot> v \<in> lists A"
  by simp

lemma pref_in_lists: "u \<le>p v \<Longrightarrow> v \<in> lists A \<Longrightarrow> u \<in> lists A"
  by (auto simp add: prefix_def)

lemmas suf_in_lists = pref_in_lists[reversed]

lemma fac_in_lists: "ws \<in> lists S \<Longrightarrow> vs \<le>f ws \<Longrightarrow> vs \<in> lists S"
  by force

lemma lq_in_lists: "v \<in> lists A \<Longrightarrow> u\<inverse>\<^sup>>v \<in> lists A"
  unfolding left_quotient_def using fac_in_lists[OF _ sublist_drop].

lemmas rq_in_lists = lq_in_lists[reversed]

lemma take_in_lists: "w \<in> lists A \<Longrightarrow> take j w \<in> lists A"
  using pref_in_lists[OF take_is_prefix].

lemma drop_in_lists: "w \<in> lists A \<Longrightarrow> drop j w \<in> lists A"
  using suf_in_lists[OF suffix_drop].

lemma lcp_in_lists: "u \<in> lists A \<Longrightarrow>  u \<and>\<^sub>p v \<in> lists A"
  using pref_in_lists[OF lcp_pref].

lemma lcp_in_lists': "v \<in> lists A \<Longrightarrow>  u \<and>\<^sub>p v \<in> lists A"
  using pref_in_lists[OF lcp_pref'].

lemma append_in_lists_dest: "u \<cdot> v \<in> lists A \<Longrightarrow> u \<in> lists A"
  by simp

lemma append_in_lists_dest': "u \<cdot> v \<in> lists A \<Longrightarrow> v \<in> lists A"
  by simp

lemma pow_in_lists: "u \<in> lists A \<Longrightarrow> u\<^sup>@k \<in> lists A"
  by (induct k) auto

lemma takeWhile_in_list: "u \<in> lists A \<Longrightarrow> takeWhile P u \<in> lists A"
  using take_in_lists[of u _ "\<^bold>|takeWhile P u\<^bold>|", folded takeWhile_eq_take].

lemma rev_in_lists: "u \<in> lists A \<Longrightarrow> rev u \<in> lists A"
  by auto

lemma append_in_lists_dest1: "u \<cdot> v = w \<Longrightarrow> w \<in> lists A \<Longrightarrow> u \<in> lists A"
  by auto

lemma append_in_lists_dest2: "u \<cdot> v = w \<Longrightarrow> w \<in> lists A \<Longrightarrow> v \<in> lists A"
  by auto

lemma pow_in_lists_dest1: "u \<cdot> v = w\<^sup>@n \<Longrightarrow> w \<in> lists A \<Longrightarrow> u \<in> lists A"
  using append_in_lists_dest pow_in_lists by metis

lemma pow_in_lists_dest1_sym: "w\<^sup>@n = u \<cdot> v \<Longrightarrow> w \<in> lists A \<Longrightarrow> u \<in> lists A"
  using append_in_lists_dest pow_in_lists by metis

lemma pow_in_lists_dest2: "u \<cdot> v = w\<^sup>@n \<Longrightarrow> w \<in> lists A \<Longrightarrow> v \<in> lists A"
  using append_in_lists_dest' pow_in_lists by metis

lemma pow_in_lists_dest2_sym: "w\<^sup>@n = u \<cdot> v \<Longrightarrow> w \<in> lists A \<Longrightarrow> v \<in> lists A"
  using append_in_lists_dest' pow_in_lists by metis

lemma per_in_lists: "w <p r \<cdot> w \<Longrightarrow> r \<in> lists A \<Longrightarrow> w \<in> lists A"
  using  pow_in_lists[of r A] pref_in_lists per_root_pow_conv by metis

lemma nth_in_lists: "j < \<^bold>|w\<^bold>| \<Longrightarrow> w \<in> lists A \<Longrightarrow> w ! j \<in> A"
  using in_lists_conv_set nth_mem by force

method inlists =
 (insert method_facts, use nothing in \<open>
   ((elim suf_in_lists | elim pref_in_lists[elim_format] | rule lcp_in_lists | rule drop_in_lists |
    rule lq_in_lists | rule rq_in_lists |
     rule take_in_lists | intro lq_in_lists | rule nth_in_lists |
     rule append_in_lists | elim conjug_in_lists | rule pow_in_lists | rule takeWhile_in_list
   | elim append_in_lists_dest1 | elim append_in_lists_dest2
   | elim pow_in_lists_dest2 | elim pow_in_lists_dest2_sym
   | elim pow_in_lists_dest1 | elim pow_in_lists_dest1_sym)
   | (simp | fact))+\<close>)

section \<open>Reversed mappings\<close>

definition rev_map :: "('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list)" where
  "rev_map f = rev \<circ> f \<circ> rev"

lemma rev_map_idemp[simp]: "rev_map (rev_map f) = f"
  unfolding rev_map_def by auto

lemma rev_map_arg: "rev_map f u = rev (f (rev u))"
  by (simp add: rev_map_def)

lemma rev_map_arg': "rev ((rev_map f) w) = f (rev w)"
  by (simp add: rev_map_def)

lemmas rev_map_arg_rev[reversal_rule] = rev_map_arg[reversed add: rev_rev_ident]

lemma rev_map_sing: "rev_map f [a] =  rev (f [a])"
  unfolding rev_map_def by simp

lemma rev_maps_eq_iff[simp]: "rev_map g = rev_map h \<longleftrightarrow> g = h"
  using arg_cong[of "rev_map g" "rev_map h" rev_map, unfolded rev_map_idemp] by fast

lemma rev_map_funpow[reversal_rule]: "(rev_map (f::'a list \<Rightarrow>'a list)) ^^ k = rev_map  (f ^^ k)"
  unfolding funpow.simps rev_map_def
  by(induct k, simp+)

section \<open>Overlapping powers, periods, prefixes and suffixes\<close>

lemma pref_suf_overlapE: assumes "p \<le>p w" and "s \<le>s w" and "\<^bold>|w\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|"
  obtains p1 u s1 where "p1 \<cdot> u \<cdot> s1 = w" and "p1 \<cdot> u = p" and "u \<cdot> s1 = s"
proof-
  define u where "u = (w\<^sup><\<inverse>s)\<inverse>\<^sup>>p"
  have "u \<le>s p"
    unfolding u_def lq_def using suffix_drop.
  obtain p1 s1 where "p1 \<cdot> u = p" and "p \<cdot> s1 = w"
    using  suffixE[OF \<open>u \<le>s p\<close>] prefixE[OF \<open>p \<le>p w\<close>] by metis
  note \<open>p \<cdot> s1 = w\<close>[folded \<open>p1 \<cdot> u = p\<close>, unfolded rassoc]

  have "\<^bold>|s1\<^bold>| \<le> \<^bold>|s\<^bold>|"
    using \<open>\<^bold>|w\<^bold>| \<le> \<^bold>|p\<^bold>| + \<^bold>|s\<^bold>|\<close>[folded \<open>p \<cdot> s1 = w\<close>, unfolded lenmorph] by force
  hence "s1 \<le>s s"
    using \<open>p \<cdot> s1 = w\<close> \<open>s \<le>s w\<close> suf_prod_long by blast

  from rq_lq_assoc[OF rq_suf_suf[OF \<open>s \<le>s w\<close>], of s1] u_def[folded rqI[OF \<open>p \<cdot> s1 = w\<close>]]
  have "u = s\<^sup><\<inverse>s1"
    using suf_rq_lq_id[OF \<open>s \<le>s w\<close>] \<open>s1 \<le>s s\<close> by presburger
  hence "u \<cdot> s1 = s"
    using  rq_suf[OF \<open>s1 \<le>s s\<close>] by blast

  from that[OF \<open>p1 \<cdot> u \<cdot> s1 = w\<close> \<open>p1 \<cdot> u = p\<close> this]
  show thesis.
qed

lemma mid_sq: assumes "p\<cdot>x\<cdot>q=x\<cdot>x" shows "x\<cdot>p=p\<cdot>x" and "x\<cdot>q=q\<cdot>x"
proof-
  have "(x\<cdot>p)\<cdot>x\<cdot>q = (p\<cdot>x)\<cdot>q\<cdot>x"
    using assms by auto
  from eqd_eq[OF this]
  show "x\<cdot>p=p\<cdot>x" and "x\<cdot>q=q\<cdot>x"
    by simp+
qed

lemma mid_sq': assumes "p\<cdot>x\<cdot>q=x\<cdot>x" shows "q \<cdot> p = x" and "p \<cdot> q = x"
proof-
  have "p\<cdot>q\<cdot>x = x\<cdot>x"
    using assms[unfolded  mid_sq(2)[OF assms]].
  thus "p\<cdot>q = x"  by auto
  from assms[folded this] this
  show "q\<cdot>p = x"  by auto
qed

lemma mid_sq_pref: "p \<cdot> u \<le>p u \<cdot> u \<Longrightarrow> p \<cdot> u = u \<cdot> p"
  using mid_sq(1)[symmetric] unfolding prefix_def rassoc by metis

lemmas mid_sq_suf = mid_sq_pref[reversed]

lemma mid_sq_pref_suf: assumes "p\<cdot>x\<cdot>q=x\<cdot>x" shows "p \<le>p x" and "p \<le>s x" and "q \<le>p x" and "q \<le>s x"
  using assms mid_sq'[OF assms] by blast+

lemma mid_pow: assumes "p\<cdot>x\<^sup>@(Suc l)\<cdot>q = x\<^sup>@k"
  shows "x\<cdot>p=p\<cdot>x" and "x\<cdot>q=q\<cdot>x"
proof-
  have "x\<cdot>p\<cdot>x\<^sup>@l\<cdot>x\<cdot>q = x\<cdot>(p\<cdot>x\<^sup>@Suc l \<cdot> q)"
    by comparison
  also have "... = (p\<cdot>x\<^sup>@Suc l \<cdot> q) \<cdot> x"
    unfolding rassoc assms  by comparison
  also have "... =  p\<cdot>x\<cdot>x\<^sup>@l\<cdot>q\<cdot>x" by simp
  finally have eq: "x\<cdot>p\<cdot>x\<^sup>@l\<cdot>x\<cdot>q = p\<cdot>x\<cdot>x\<^sup>@l\<cdot>q\<cdot>x".

  have "(x\<cdot>p)\<cdot>x\<^sup>@l\<cdot>x\<cdot>q = (p\<cdot>x)\<cdot>x\<^sup>@l\<cdot>q\<cdot>x"
    using eq unfolding rassoc.
  from eqd_comp[OF this]
  show "x\<cdot>p = p\<cdot>x"
    using comm_ruler by blast

  have "(x\<cdot>p\<cdot>x\<^sup>@l)\<cdot>(x\<cdot>q) = (x\<cdot>p\<cdot>x\<^sup>@l)\<cdot>(q\<cdot>x)"
    using eq unfolding lassoc \<open>x\<cdot>p = p\<cdot>x\<close>.
  from this[unfolded cancel]
  show "x\<cdot>q = q\<cdot>x".
qed

lemma root_suf_comm: assumes "x \<le>p r \<cdot> x" and  "r \<le>s r \<cdot> x" shows "r \<cdot> x = x \<cdot> r"
proof-
  have "r \<cdot> x = x \<cdot> x\<inverse>\<^sup>>(r \<cdot> x)"
    using lq_pref[OF \<open>x \<le>p r \<cdot> x\<close>, symmetric].
  from this and conj_len[OF this]
  have "r = x\<inverse>\<^sup>>(r \<cdot> x)"
    using lq_pref[OF \<open>x \<le>p r \<cdot> x\<close>] suf_ruler_eq_len[OF \<open>r \<le>s r \<cdot> x\<close>, of "x\<inverse>\<^sup>>(r \<cdot> x)"] by blast
  from \<open>r \<cdot> x = x \<cdot> x\<inverse>\<^sup>>(r \<cdot> x)\<close>[folded this]
  show "r \<cdot> x = x \<cdot> r".
qed

lemma pref_marker: assumes "w \<le>p v \<cdot> w" and "u \<cdot> v \<le>p w"
  shows "u \<cdot> v = v \<cdot> u"
  using append_prefixD[OF \<open>u \<cdot> v \<le>p w\<close>] comm_ruler[OF \<open>u \<cdot> v \<le>p w\<close>, of "v \<cdot> w", unfolded same_prefix_prefix]
    \<open>w \<le>p v \<cdot> w\<close> by blast

lemma pref_marker_ext: assumes "\<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|" and "v \<noteq> \<epsilon>" and "y \<cdot> v \<le>p x \<cdot> v\<^sup>@k"
  obtains n where "y = x \<cdot> (\<rho> v)\<^sup>@n"
proof-
  note pref_prod_long_ext[OF \<open>y \<cdot> v \<le>p x \<cdot> v\<^sup>@k\<close> \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|\<close>]
  have "x\<inverse>\<^sup>>y \<cdot> v \<le>p v\<^sup>@k"
    using pref_cancel_lq_ext[OF \<open>y \<cdot> v \<le>p x \<cdot> v\<^sup>@k\<close> \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|\<close>].
  from pref_marker[OF _ this]
  have "x\<inverse>\<^sup>>y \<cdot> v = v \<cdot> x\<inverse>\<^sup>>y"
    unfolding pow_comm[symmetric] by blast
  then obtain n where "x\<inverse>\<^sup>>y = (\<rho> v)\<^sup>@n"
    using \<open>v \<noteq> \<epsilon>\<close>
    using comm_primroots pow_zero primroot_expE by metis
  hence "y = x \<cdot> (\<rho> v)\<^sup>@n"
    using \<open>x \<le>p y\<close> by (auto simp add: prefix_def)
  from that[OF this] show thesis.
qed

lemma pref_marker_sq: "p \<cdot> x \<le>p x \<cdot> x \<Longrightarrow> p \<cdot> x = x \<cdot> p"
  using pref_marker same_prefix_prefix triv_pref by metis

lemmas suf_marker_sq = pref_marker_sq[reversed]

lemma pref_marker_conjug: assumes "w \<noteq> \<epsilon>" and "w \<cdot> r \<cdot> s \<le>p s \<cdot> (r \<cdot> s)\<^sup>@m" and "primitive (r \<cdot> s)"
  obtains n where "w = s \<cdot> (r \<cdot> s)\<^sup>@n"
proof-
  have "(r \<cdot> w) \<cdot> r \<cdot> s \<le>p (r \<cdot> s)\<^sup>@Suc m"
    using \<open>w \<cdot> r \<cdot> s \<le>p s \<cdot> (r \<cdot> s)\<^sup>@m\<close> by auto
  from pref_marker[OF _ this, folded pow_comm, OF triv_pref]
  have "(r \<cdot> w) \<cdot> r \<cdot> s = (r \<cdot> s) \<cdot> r \<cdot> w".
  from comm_primroots'[OF _ prim_nemp[OF \<open>primitive (r \<cdot> s)\<close>] this, unfolded prim_self_root[OF \<open>primitive (r \<cdot> s)\<close>]]
  have "\<rho> (r \<cdot> w) = r \<cdot> s"
    using \<open>w \<noteq> \<epsilon>\<close> by blast
  then obtain n where "r \<cdot> w = (r \<cdot> s)\<^sup>@n" "0 < n"
    using \<open>w \<noteq> \<epsilon>\<close> primroot_expE by metis
  thus thesis
    using pow_pos[OF \<open>0 < n\<close>, of "r \<cdot> s", folded \<open>r \<cdot> w = (r \<cdot> s)\<^sup>@n\<close>,
    unfolded rassoc cancel] that by force
qed

lemmas pref_marker_reversed = pref_marker[reversed]

lemma suf_marker_per_root: assumes "w \<le>p v \<cdot> w" and "p \<cdot> v \<cdot> u \<le>p w"
  shows "u \<le>p v \<cdot> u"
proof-
  have "p \<cdot> v = v \<cdot> p"
    using pref_marker[OF \<open>w \<le>p v \<cdot> w\<close>, of p] \<open>p \<cdot> v \<cdot> u \<le>p w\<close> by (auto simp add: prefix_def)
  from pref_trans[OF \<open>p \<cdot> v \<cdot> u \<le>p w\<close>[unfolded lassoc this, unfolded rassoc] \<open>w \<le>p v \<cdot> w\<close>]
  have "p \<cdot> u \<le>p w"
    using pref_cancel by auto
  from  ruler_le[OF this \<open>p \<cdot> v \<cdot> u \<le>p w\<close>]
  have "p \<cdot> u \<le>p p \<cdot> v \<cdot> u"
    by force
  thus ?thesis
    unfolding pref_cancel_conv.
qed

lemma suf_marker_per_root': assumes "w \<le>p v \<cdot> w" and "p \<cdot> v \<cdot> u \<le>p w" and "v \<noteq> \<epsilon>"
  shows "u \<le>p p \<cdot> u"
proof-
  have "p \<cdot> v = v \<cdot> p"
    using pref_marker[OF \<open>w \<le>p v \<cdot> w\<close>, of p] \<open>p \<cdot> v \<cdot> u \<le>p w\<close> by (fastforce simp add: prefix_def)
  from root_comm_root[OF suf_marker_per_root[OF \<open>w \<le>p v \<cdot> w\<close> \<open>p \<cdot> v \<cdot> u \<le>p w\<close>] this \<open>v \<noteq> \<epsilon>\<close>]
  show "u \<le>p p \<cdot> u".
qed

lemma marker_fac_pref: assumes "u \<le>f r\<^sup>@k" and  "r \<le>p u" shows "u \<le>p r\<^sup>@k"
  using assms
proof (cases "r = \<epsilon>")
  assume "r \<noteq> \<epsilon>"
  have "\<^bold>|u\<^bold>| \<le> \<^bold>|r\<^sup>@k\<^bold>|"
    using \<open>u \<le>f r\<^sup>@k\<close> by force
  obtain u' where "r \<cdot> u' = u"
    using \<open>r \<le>p u\<close> by (auto simp add: prefix_def)
  obtain p s where "p \<cdot> u \<cdot> s = r\<^sup>@k"
    using \<open>u \<le>f r\<^sup>@k\<close> by blast
  from suf_marker_per_root[of "r\<^sup>@k" r p "u' \<cdot> s", folded pow_comm, OF triv_pref]
  have "u' \<cdot> s \<le>p r \<cdot> (u' \<cdot> s)"
    using \<open>p \<cdot> u \<cdot> s = r\<^sup>@k\<close>[folded \<open>r \<cdot> u' = u\<close>, unfolded rassoc] by fastforce
  hence "u' \<cdot> s \<le>p r\<^sup>@k \<cdot> (u' \<cdot> s)"
    using per_exp_pref by blast
  hence "u \<le>p (r\<^sup>@k \<cdot> r) \<cdot> (u' \<cdot> s)"
    unfolding \<open>r \<cdot> u' = u\<close>[symmetric] pow_Suc'[symmetric] pow_Suc rassoc
       by (auto simp add: prefix_def)
  thus "u \<le>p r\<^sup>@k"
    unfolding rassoc using \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|r\<^sup>@k\<^bold>|\<close> by blast
qed simp

lemma marker_fac_pref_len: assumes "u \<le>f r\<^sup>@k" and "t \<le>p u" and "\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|"
  shows "u \<le>p t\<^sup>@k"
proof-
  have "\<^bold>|u\<^bold>| \<le> \<^bold>|r\<^sup>@k\<^bold>|"
    using \<open>u \<le>f r\<^sup>@k\<close> by force
  hence "\<^bold>|u\<^bold>| \<le> \<^bold>|t\<^sup>@k\<^bold>|"
    unfolding pow_len \<open>\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|\<close>.
  have "t \<le>f r\<^sup>@k"
    using assms by blast
  hence "t \<sim> r"
    using \<open>\<^bold>|t\<^bold>| = \<^bold>|r\<^bold>|\<close> by (simp add: conjug_sym fac_pow_len_conjug)
  from fac_pow_conjug[OF \<open>u \<le>f r\<^sup>@k\<close> this]
  have "u \<le>p t\<^sup>@Suc k"
    using marker_fac_pref[OF _  \<open>t \<le>p u\<close>] by blast
  thus "u \<le>p t\<^sup>@k"
    using \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|t\<^sup>@k\<^bold>|\<close> unfolding pow_Suc' by blast
qed

lemma root_suf_comm': "x \<le>p r \<cdot> x \<Longrightarrow> r \<le>s x \<Longrightarrow> r \<cdot> x = x \<cdot> r"
  using root_suf_comm suffix_appendI[of r x r] by blast

lemmas suf_root_pref_comm = root_suf_comm'[reversed]

lemma marker_pref_suf_fac:  assumes "u \<le>p v" and "u \<le>s v" and "v \<le>f u\<^sup>@k"
  shows "u \<cdot> v = v \<cdot> u"
  using root_suf_comm'[OF pref_prod_root[OF  marker_fac_pref[OF \<open>v \<le>f u\<^sup>@k\<close> \<open>u \<le>p v\<close>]] \<open>u \<le>s v\<close>].

lemma pref_suf_per_fac_comm:
  assumes "v \<le>p u \<cdot> v" and "v \<le>s v \<cdot> u" and "u \<le>f v\<^sup>@k" shows "u \<cdot> v = v \<cdot> u"
      using marker_pref_suf_fac[OF _ _ \<open>u \<le>f v\<^sup>@k\<close>] root_suf_comm[OF \<open>v \<le>p u \<cdot> v\<close> suf_ext] root_suf_comm[reversed, OF \<open>v \<le>s v \<cdot> u\<close> pref_ext]
      ruler_pref'[OF \<open>v \<le>p u \<cdot> v\<close>] ruler_suf'[OF \<open>v \<le>s v \<cdot> u\<close>] by argo

lemma mid_long_pow: assumes eq: "y\<^sup>@m = u \<cdot> x\<^sup>@(Suc k) \<cdot> v" and "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^sup>@k\<^bold>|"
  shows "(u \<cdot> v) \<cdot> y = y \<cdot> (u \<cdot> v)" and  "(u \<cdot> x\<^sup>@l \<cdot> v) \<cdot> y = y \<cdot> (u \<cdot> x\<^sup>@l \<cdot> v)" and "(u\<inverse>\<^sup>>(y\<cdot>u)) \<cdot> x = x \<cdot> (u\<inverse>\<^sup>>(y\<cdot>u))"
proof-
  have eq': "x\<cdot> x \<cdot>v \<cdot> u = u\<inverse>\<^sup>>(u\<cdot>x\<cdot>x\<cdot>v)\<cdot>u" by simp
  let ?y = "u\<inverse>\<^sup>>(y\<cdot>u)"
  have "u \<le>p y \<cdot> u"
    using eq prefI pref_prod_root[of u y m,unfolded eq] by simp
  hence "?y \<sim> y"
    using root_conjug by blast
  from conjug_len[OF this]
  have "\<^bold>|?y\<^bold>| \<le> \<^bold>|x\<^sup>@k\<^bold>|"
    using \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^sup>@k\<^bold>|\<close> by simp
  from lq_conjug_pow[OF \<open>u \<le>p y \<cdot> u\<close>, of m]
  have "?y\<^sup>@m = x\<^sup>@Suc k\<cdot>v\<cdot>u"
    unfolding eq eq' by simp
  hence "x\<^sup>@Suc k \<le>p ?y \<cdot> x\<^sup>@Suc k"
    using rassoc prefI pref_prod_root[of "x\<^sup>@Suc k" ?y m] by blast
  have "x \<^sup>@ Suc k \<le>p x \<cdot> x \<^sup>@ Suc k"
    using pref_pow_ext' by blast
  have com: "?y \<cdot> x = x \<cdot> ?y"
    using  \<open>\<^bold>|?y\<^bold>| \<le> \<^bold>|x\<^sup>@k\<^bold>|\<close> two_pers[OF \<open>x\<^sup>@Suc k \<le>p ?y \<cdot> x\<^sup>@Suc k\<close> \<open>x \<^sup>@ Suc k \<le>p x \<cdot> x \<^sup>@ Suc k\<close>]
    unfolding pow_Suc' lenmorph by linarith
  thus "?y \<cdot> x = x \<cdot> ?y"
    by blast
  have "?y \<cdot> x\<^sup>@Suc k = x\<^sup>@Suc k \<cdot> ?y"
    using com comm_add_exp by metis
  from pow_comm[of ?y m, unfolded \<open>?y \<^sup>@ m = x\<^sup>@(Suc k) \<cdot> v \<cdot> u\<close>, unfolded lassoc this, unfolded rassoc]
  have "x\<^sup>@Suc k \<cdot> v \<cdot> u \<cdot> ?y = x\<^sup>@Suc k \<cdot> ?y \<cdot> v \<cdot> u".
  hence "u \<cdot> ?y \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> ?y" by simp
  thus "(u \<cdot> v) \<cdot>  y = y \<cdot> (u \<cdot> v)"
    unfolding lassoc lq_pref[OF \<open>u \<le>p y \<cdot> u\<close>] by fastforce
  have "u \<cdot> x\<^sup>@l \<cdot> v \<cdot>  u \<cdot> ?y =  u \<cdot> (?y \<cdot> x\<^sup>@l) \<cdot> v \<cdot> u"
    unfolding comm_add_exp[OF com[symmetric], of l, symmetric] rassoc cancel
    using \<open>u \<cdot> ?y \<cdot> v \<cdot> u = u \<cdot> v \<cdot> u \<cdot> ?y\<close>[unfolded cancel, symmetric].
  thus "(u \<cdot> x\<^sup>@l \<cdot> v) \<cdot> y = y \<cdot> (u \<cdot> x\<^sup>@l \<cdot> v)"
    unfolding lq_pref[OF \<open>u \<le>p y \<cdot> u\<close>] lassoc by blast
qed

lemma mid_pow_pref_suf': assumes  "s\<cdot>w\<^sup>@(Suc l)\<cdot>p \<le>f w\<^sup>@k" shows "p \<le>p w\<^sup>@k"  and "s \<le>s w\<^sup>@k"
proof-
  obtain v u where dec: "v \<cdot> s \<cdot>  w\<^sup>@(Suc l) \<cdot> p \<cdot> u = w\<^sup>@k"
    using facE'[OF assms, unfolded rassoc].
  hence "(v \<cdot> s) \<cdot> w = w \<cdot> (v \<cdot> s)" and "w \<cdot> (p \<cdot> u) = (p \<cdot> u) \<cdot> w"
    using mid_pow[of "v \<cdot> s" w l "p \<cdot> u" k] unfolding rassoc by presburger+
  have "\<^bold>|p\<^bold>| \<le> \<^bold>|w\<^sup>@k\<^bold>|" and "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^sup>@k\<^bold>|"
    using fac_len[OF assms] unfolding lenmorph by linarith+

  from per_exp_pref[of "p \<cdot> u" w k, unfolded \<open>w \<cdot> (p \<cdot> u) = (p \<cdot> u) \<cdot> w\<close>, OF triv_pref]
  have "p \<le>p w\<^sup>@k \<cdot> (p \<cdot> u)"
    using   prefix_order.trans[OF triv_pref[of p u]] by blast
  thus "p \<le>p w\<^sup>@k"
    using \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|w \<^sup>@ k\<^bold>|\<close> pref_prod_le by blast

  from per_exp_suf[of "v \<cdot> s" w k, unfolded \<open>(v \<cdot> s) \<cdot> w = w \<cdot> (v \<cdot> s)\<close>, OF triv_suf]
  have "s \<le>s (v \<cdot> s) \<cdot> w\<^sup>@k"
    using  suffix_order.trans[OF triv_suf[of s v], of "(v \<cdot> s) \<cdot> w\<^sup>@k"] by blast
  thus "s \<le>s w\<^sup>@k"
    using \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|w \<^sup>@ k\<^bold>|\<close> suf_prod_le by blast
qed

lemma mid_pow_pref_suf: assumes  "s\<cdot>w\<cdot>p \<le>f w\<^sup>@k" shows "p \<le>p w\<^sup>@k"  and "s \<le>s w\<^sup>@k"
  using mid_pow_pref_suf'[of s w 0 p k, unfolded pow_one, OF assms].

lemma fac_marker_pref: "y \<cdot> x \<le>f y\<^sup>@k \<Longrightarrow> x \<le>p y \<cdot> x"
  using mid_pow_pref_suf(1)[of \<epsilon>, unfolded emp_simps, THEN pref_prod_root].

lemmas fac_marker_suf = fac_marker_pref[reversed]

lemma prim_overlap_sqE [consumes 2]:
  assumes prim: "primitive r" and eq: "p \<cdot> r \<cdot> q = r \<cdot> r"
  obtains (pref_emp) "p = \<epsilon>" | (suff_emp) "q = \<epsilon>"
proof (cases "\<^bold>|p\<^bold>| = 0", blast)
  assume "\<^bold>|p\<^bold>| \<noteq> 0" and qemp: "q = \<epsilon> \<Longrightarrow> thesis"
  hence "\<^bold>|q\<^bold>| < \<^bold>|r\<^bold>|"
    using lenarg[OF eq] unfolding lenmorph by linarith
  have "q = \<epsilon>"
    using prim_comm_short_emp[OF prim  mid_sq(2)[OF eq, symmetric] \<open>\<^bold>|q\<^bold>| < \<^bold>|r\<^bold>|\<close>].
  from qemp[OF this]
  show thesis.
qed

lemma prim_overlap_sqE' [consumes 2]:
  assumes prim: "primitive r" and eq: "p \<cdot> r \<cdot> q = r \<cdot> r"
  obtains (pref_emp) "p = \<epsilon>" | (suff_emp) "p = r"
  using append_Nil2 eq mid_sq'(2) prim prim_overlap_sqE by metis

lemma prim_overlap_sq:
  assumes prim: "primitive r" and eq: "p \<cdot> r \<cdot> q = r \<cdot> r"
  shows "p = \<epsilon> \<or> q = \<epsilon>"
  using prim_overlap_sqE[OF prim eq disjI1 disjI2].

lemma prim_overlap_sq':
  assumes prim: "primitive r" and pref: "p \<cdot> r \<le>p r \<cdot> r" and len: "\<^bold>|p\<^bold>| < \<^bold>|r\<^bold>|"
  shows "p = \<epsilon>"
  using mid_sq(1)[symmetric, THEN prim_comm_short_emp[OF prim _ len ]] pref
   by (auto simp add: prefix_def)

lemma prim_overlap_pow:
  assumes prim: "primitive r" and pref: "u \<cdot> r \<le>p r\<^sup>@k"
  obtains i where "u = r\<^sup>@i" and "i < k"
proof-
  obtain q where eq: "u \<cdot> r \<^sup>@ Suc 0 \<cdot> q = r \<^sup>@ k"
    using pref by (auto simp add: prefix_def)
  from mid_pow(1)[OF this, symmetric]
  have "u \<cdot> r = r \<cdot> u".
  from prim_comm_exp[OF \<open>primitive r\<close> this]
  obtain i where "r\<^sup>@i = u".
  hence "\<^bold>|r \<^sup>@ Suc i\<^bold>| \<le> \<^bold>|r \<^sup>@ k\<^bold>|"
    using pref by (auto simp add: prefix_def)
  from mult_cancel_le[OF nemp_len[OF prim_nemp[OF prim]] this[unfolded pow_len]]
  have "i < k"  by auto
  from that[OF \<open>r\<^sup>@i = u\<close>[symmetric] this]
  show thesis.
qed

lemma prim_overlap_pow':
  assumes prim: "primitive r" and pref: "u \<cdot> r \<le>p r\<^sup>@k" and less: "\<^bold>|u\<^bold>| < \<^bold>|r\<^bold>|"
  shows "u = \<epsilon>"
proof-
  obtain i where "u = r\<^sup>@i"
    using prim_overlap_pow[OF prim pref] by force
  from less[unfolded pow_len[of r i, folded this]]
  have "i = 0" by force
  from \<open>u = r\<^sup>@i\<close>[unfolded this pow_zero]
  show "u = \<epsilon>".
qed

lemma prim_sqs_overlap:
  assumes prim: "primitive r" and comp: "u \<cdot> r \<cdot> r \<bowtie> v \<cdot> r \<cdot> r"
    and len_u: "\<^bold>|u\<^bold>| < \<^bold>|v\<^bold>| + \<^bold>|r\<^bold>|" and len_v: "\<^bold>|v\<^bold>| < \<^bold>|u\<^bold>| + \<^bold>|r\<^bold>|"
  shows "u = v"
proof (cases rule: le_cases)
  have wlog_le: "u = v" if comp: "u \<cdot> (r \<cdot> r) \<bowtie> v \<cdot> (r \<cdot> r)" and len_v: "\<^bold>|v\<^bold>| < \<^bold>|u\<^bold>| + \<^bold>|r\<^bold>|"
    and "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|" for u v
  proof -
    obtain w where v: "u \<cdot> w = v"
      using comp_shorter[OF comp_prefs_comp[OF comp] \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|\<close>] by (auto simp add: prefix_def)
    have "\<^bold>|w\<^bold>| < \<^bold>|r\<^bold>|" using len_v unfolding v[symmetric] by simp
    have comp': "r \<cdot> r \<bowtie> (w \<cdot> r) \<cdot> r" using comp unfolding v[symmetric] rassoc comp_cancel.
    moreover have "\<^bold>|w \<cdot> r\<^bold>| \<le> \<^bold>|r \<cdot> r\<^bold>|" using less_imp_le_nat[OF \<open>\<^bold>|w\<^bold>| < \<^bold>|r\<^bold>|\<close>] by simp
    ultimately have pref: "w \<cdot> r \<le>p r \<cdot> r"
      by (rule pref_comp_len_trans[OF triv_pref])
    from this \<open>\<^bold>|w\<^bold>| < \<^bold>|r\<^bold>|\<close> have "w = \<epsilon>" by (rule prim_overlap_sq'[OF prim])
    show "u = v" using v unfolding \<open>w = \<epsilon>\<close> append_Nil2.
  qed
  show "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> u = v" using wlog_le[OF comp len_v].
  show "\<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> u = v" using wlog_le[OF comp[symmetric] len_u, symmetric].
qed

lemma drop_pref_prim: assumes "Suc n < \<^bold>|w\<^bold>|" and "w \<le>p drop (Suc n) (w \<cdot> w)" and "primitive w"
  shows False
  using assms
proof (cases "w = \<epsilon>")
  assume "w \<noteq> \<epsilon>"
  obtain s where "drop (Suc n) (w \<cdot> w) = w \<cdot> s"
    using prefD[OF \<open>w \<le>p drop (Suc n) (w \<cdot> w)\<close>] by blast
  note takedrop[of "Suc n" "w \<cdot> w", unfolded this]
  from \<open>Suc n < \<^bold>|w\<^bold>|\<close> \<open>w \<noteq> \<epsilon>\<close> prim_overlap_sqE'[OF \<open>primitive w\<close> this]
  show False by auto
qed simp

lemma root_suf_conjug: assumes "primitive (s \<cdot> r)" and "y \<le>p (s \<cdot> r) \<cdot> y" and "y \<le>s y \<cdot> (r \<cdot> s)" and "\<^bold>|s \<cdot> r\<^bold>| \<le> \<^bold>|y\<^bold>|"
             obtains l where "y = (s \<cdot> r)\<^sup>@l \<cdot> s"
proof-
  have "y \<noteq> \<epsilon>"
    using assms(1) assms(4) by force
  have "r \<cdot> s \<le>s y"
    using suf_prod_long[OF \<open>y \<le>s y \<cdot> (r \<cdot> s)\<close> \<open>\<^bold>|s \<cdot> r\<^bold>| \<le> \<^bold>|y\<^bold>|\<close>[unfolded swap_len]].
  have "primitive (r \<cdot> s)"
    using prim_conjug[OF \<open>primitive (s \<cdot> r)\<close> conjugI'].
  have "r \<cdot> y \<le>p (r \<cdot> s) \<cdot> (r \<cdot> y)"
    using \<open>y \<le>p (s \<cdot> r) \<cdot> y\<close> by auto
  from prim_comm_exp[OF \<open>primitive (r \<cdot> s)\<close> root_suf_comm'[OF this suf_ext[OF \<open>r \<cdot> s \<le>s y\<close>], symmetric]]
  obtain k where [symmetric]: "(r \<cdot> s)\<^sup>@k = r \<cdot> y" and "0 < k"
    using \<open>y \<noteq> \<epsilon>\<close> using nemp_exp_pos sufI suf_emp by metis
  hence "y = (s \<cdot> r)\<^sup>@(k-1) \<cdot> s"
    unfolding pow_pos[of _ "r\<cdot>s", OF \<open>0 < k\<close>] rassoc cancel shift_pow by blast
  from that[OF this]
  show thesis.
qed

lemma pref_suf_pows_comm: assumes "x \<le>p y\<^sup>@(Suc k)\<cdot>x\<^sup>@l" and  "y \<le>s y\<^sup>@m \<cdot> x\<^sup>@(Suc n)"
  shows "x \<cdot> y = y \<cdot> x"
  using root_suf_comm[OF per_root_drop_exp'[OF assms(1)] per_root_drop_exp'[reversed, OF assms(2)], symmetric].

lemma root_suf_pow_comm: assumes "x \<le>p r \<cdot> x" and  "r \<le>s x\<^sup>@(Suc k)" shows "r \<cdot> x = x \<cdot> r"
  using  root_suf_comm[OF \<open>x \<le>p r \<cdot> x\<close> suf_prod_root[OF \<open>r \<le>s x\<^sup>@(Suc k)\<close>]].

lemma suf_pow_short_suf: "r \<le>s x\<^sup>@k \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|r\<^bold>| \<Longrightarrow> x \<le>s r"
  using suf_prod_root[THEN suf_prod_long].

thm suf_pow_short_suf[reversed]

lemma sq_short_per: assumes "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|" and "v\<cdot>v \<le>p u\<cdot>(v\<cdot>v)"
  shows "u\<cdot>v = v\<cdot>u"
  using
    pref_marker[of "v\<cdot>v", OF \<open>v\<cdot>v \<le>p u\<cdot>(v\<cdot>v)\<close>
    pref_prod_long[OF append_prefixD[OF \<open>v\<cdot>v \<le>p u\<cdot>(v\<cdot>v)\<close>] \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|\<close>,
      THEN pref_cancel'], symmetric].

lemma fac_marker: assumes "w \<le>p u\<cdot>w" and "u\<cdot>v\<cdot>u \<le>f w"
  shows "u \<cdot> v = v \<cdot> u"
proof-
  obtain p s where "w = p\<cdot>u\<cdot>v\<cdot>u\<cdot>s"
    using \<open>u\<cdot>v\<cdot>u \<le>f w\<close>[unfolded fac_def]
    by auto

  hence "p\<cdot>u\<cdot>v\<cdot>u = u\<cdot>p\<cdot>u\<cdot>v"
    using pref_marker[OF \<open>w \<le>p u\<cdot>w\<close>, unfolded \<open>w = p\<cdot>u\<cdot>v\<cdot>u\<cdot>s\<close>, of "p \<cdot> u \<cdot> v"]
    by force

  thus "u\<cdot>v = v\<cdot>u"
    using eqd_eq[of "p \<cdot> u" "v \<cdot> u" "u \<cdot> p" "u \<cdot> v", unfolded rassoc, OF _ swap_len]
    by presburger
qed

lemma "4 = Suc(Suc(Suc(Suc 0)))"
  using [[simp_trace]] by simp


lemma xyxy_conj_yxxy: assumes "x \<cdot> y \<cdot> x \<cdot> y \<sim> y \<cdot> x \<cdot> x \<cdot> y"
  shows "x \<cdot> y = y \<cdot> x"
proof-
  have four: "x\<^sup>@4 = x\<cdot>x\<cdot>x\<cdot>x" for x :: "'a list"
    unfolding numeral_Bit0 by simp
  from conjug_fac_sq[OF assms[symmetric]]
  have "y \<cdot> x \<cdot> x \<cdot> y \<le>f (x \<cdot> y)\<^sup>@4"
    unfolding four rassoc.
  from marker_fac_pref[reversed,
      OF this triv_suf[of "x\<cdot>y" "y\<cdot>x", unfolded rassoc]]
  have "y \<cdot> x \<cdot> x \<cdot> y \<le>s (x \<cdot> y) \<^sup>@ 4".
  hence "y \<cdot> x \<cdot> x \<cdot> y \<le>s (x\<cdot>y\<cdot>x\<cdot>y)\<cdot>x\<cdot>y\<cdot>x\<cdot>y"
    unfolding four rassoc.
  from suf_prod_eq[OF this]
  show "x \<cdot> y = y \<cdot> x"
    by simp
qed


lemma per_glue: assumes "period u n" and "period v n" and "u \<le>p w" and "v \<le>s w" and
              "\<^bold>|w\<^bold>| + n \<le> \<^bold>|u\<^bold>| + \<^bold>|v\<^bold>|"
            shows "period w n"
proof (rule indeces_period)
  show  "w \<noteq> \<epsilon>"
    using \<open>period u n\<close> \<open>u \<le>p w\<close> by force
  show "0 < n"
    using \<open>period u n\<close> per_not_zero by metis
  fix i assume "i + n < \<^bold>|w\<^bold>|"
  show "w ! i = w ! (i + n)"
  proof (cases)
    assume "i + n < \<^bold>|u\<^bold>|"
    hence "w ! i = u ! i" and "w ! (i+n) = u ! (i+n)"
      using add_lessD1 \<open>u \<le>p w\<close> pref_index by metis+
    thus "w ! i = w ! (i + n)"
      unfolding \<open>w ! i = u ! i\<close> \<open>w ! (i+n) = u ! (i+n)\<close>
      using period_indeces[OF \<open>period u n\<close> \<open>i + n < \<^bold>|u\<^bold>|\<close>]  by blast
  next
    assume "\<not> i + n < \<^bold>|u\<^bold>|"
    obtain p where "w = p \<cdot> v"
      using \<open>v \<le>s w\<close> by (auto simp add: suffix_def)
    have "\<not> i < \<^bold>|p\<^bold>|"
      using  \<open>\<not> i + n < \<^bold>|u\<^bold>|\<close> \<open>\<^bold>|w\<^bold>| + n \<le> \<^bold>|u\<^bold>| + \<^bold>|v\<^bold>|\<close> unfolding lenarg[OF \<open>w = p \<cdot> v\<close>, unfolded lenmorph]
      by auto
    hence "w!i = v!(i - \<^bold>|p\<^bold>|)" and "w!(i+n) = v!((i - \<^bold>|p\<^bold>|) + n)"
      unfolding \<open>w = p \<cdot> v\<close> nth_append by simp_all
    have "i - \<^bold>|p\<^bold>| + n < \<^bold>|v\<^bold>|"
      using \<open>\<not> i < \<^bold>|p\<^bold>|\<close> \<open>i + n < \<^bold>|w\<^bold>|\<close> \<open>w = p \<cdot> v\<close> by auto
    from period_indeces[OF \<open>period v n\<close> this]
    show "w ! i = w ! (i + n)"
      unfolding \<open>w!i = v!(i - \<^bold>|p\<^bold>|)\<close> \<open>w!(i+n) = v!(i - \<^bold>|p\<^bold>| + n)\<close>.
  qed
qed

lemma per_glue_facs: assumes "u \<cdot> z \<le>f w\<^sup>@k" and "z \<cdot> v \<le>f w\<^sup>@m" and "\<^bold>|w\<^bold>| \<le> \<^bold>|z\<^bold>|"
  obtains l where "u \<cdot> z \<cdot> v \<le>f w\<^sup>@l"
  using assms
proof (cases "k = 0")
  assume "k \<noteq> 0"
  have "z \<le>f w\<^sup>@k"
    using \<open>u \<cdot> z \<le>f w\<^sup>@k\<close> by blast
  have "z \<le>f w\<^sup>@m"
    using \<open>z \<cdot> v \<le>f w\<^sup>@m\<close> by blast
  define t where "t = take \<^bold>|w\<^bold>| z"
  have "\<^bold>|t\<^bold>| = \<^bold>|w\<^bold>|" and "t \<le>p z"
    unfolding t_def using \<open>\<^bold>|w\<^bold>| \<le> \<^bold>|z\<^bold>|\<close> take_is_prefix by (force,blast)
  hence "w \<sim> t"
    using \<open>z \<le>f w\<^sup>@m\<close> by blast
  from marker_fac_pref_len[OF \<open>z \<cdot> v \<le>f (w) \<^sup>@ m\<close> _ \<open>\<^bold>|t\<^bold>| = \<^bold>|w\<^bold>|\<close> ]
  have "z \<cdot> v \<le>p t\<^sup>@m"
    using  \<open>t \<le>p z\<close> by force
  have "u \<cdot> z \<le>f t\<^sup>@Suc k"
    using  fac_pow_conjug[OF \<open>u \<cdot> z \<le>f w\<^sup>@k\<close>  \<open>w \<sim> t\<close>[symmetric]].
  with \<open>t \<le>p z\<close>
  have "u \<le>s t\<^sup>@Suc k"
    using mid_pow_pref_suf(2)[of u t "t\<inverse>\<^sup>>z" "Suc k"] lq_pref by metis
  have "(t\<^sup>@Suc k\<^sup><\<inverse>u)\<cdot> (u \<cdot> z \<cdot> v) \<cdot> (z \<cdot> v)\<inverse>\<^sup>>(t\<^sup>@m) = t\<^sup>@Suc k \<cdot> t\<^sup>@m"
    unfolding lassoc rq_suf[OF \<open>u \<le>s t\<^sup>@Suc k\<close>] unfolding rassoc cancel  using  lq_pref[OF \<open>z \<cdot> v \<le>p t\<^sup>@m\<close>] unfolding rassoc.
  from facI[of "u \<cdot> z \<cdot> v" "t\<^sup>@Suc k\<^sup><\<inverse>u" "(z \<cdot> v)\<inverse>\<^sup>>(t\<^sup>@m)", unfolded this, folded add_exps]
  obtain l where "u \<cdot> z \<cdot> v \<le>f t\<^sup>@l"
    by metis
  from that[OF fac_pow_conjug[OF this \<open>w \<sim> t\<close>]]
  show thesis.
qed simp

lemma per_fac_pow_fac: assumes "period w n" and "v \<le>f w" and "\<^bold>|v\<^bold>| = n"
  obtains k where "w \<le>f v\<^sup>@k"
proof-
  obtain m where "w \<le>f (take n w)\<^sup>@m"
    using  per_root_powE[OF \<open>period w n\<close>[unfolded  period_def]] pref_fac sprefD1 by metis
  obtain r s where "r \<cdot> s = v" and "s \<cdot> r = take n w"
    using fac_per_conjug[OF assms, THEN conjugE].
  hence "r \<cdot> (take n w)\<^sup>@m \<cdot> s = v\<^sup>@Suc m"
    by (metis pow_slide)
  from that[OF fac_trans, OF \<open>w \<le>f (take n w)\<^sup>@m\<close>] sublist_appendI[of "(take n w)\<^sup>@m" r s, unfolded this]
  show thesis
    by blast
qed

lemma refine_per: assumes "period w n" and "v \<le>f w" and "n \<le> \<^bold>|v\<^bold>|" and "period v k" and "k dvd n"
  shows "period w k"
proof-
  have "n \<noteq> 0"
    using \<open>period w n\<close> by auto
  have "w \<noteq> \<epsilon>"
    using \<open>period w n\<close> by auto
  have "v \<noteq> \<epsilon>"
    using \<open>period v k\<close> by auto
  have "\<^bold>|take n w\<^bold>| = n"
    using take_len[OF le_trans[OF \<open>n \<le> \<^bold>|v\<^bold>|\<close> fac_len[OF \<open>v \<le>f w\<close>]]].
  have "\<^bold>|take n v\<^bold>| = n"
    using take_len[OF \<open>n \<le> \<^bold>|v\<^bold>|\<close>].
  have "period v n"
    using  period_fac'[OF \<open>period w n\<close> \<open>v \<le>f w\<close> \<open>v \<noteq> \<epsilon>\<close>] by blast
  have "take n v \<le>f w"
    using \<open>v \<le>f w\<close> \<open>n \<le> \<^bold>|v\<^bold>|\<close> sublist_order.dual_order.trans sublist_take by metis
  have "period (take n v) k"
    using \<open>period w n\<close> \<open>period v k\<close> per_not_zero per_pref' take_is_prefix take_nemp by metis
  have "k \<le> n"
    using \<open>k dvd n\<close> \<open>n \<noteq> 0\<close> by auto
  hence "take k (take n v) =  take k v"
    using take_le_take by blast
  hence "(take k v)\<^sup>@(n div k) = take n v"
    using  per_div[OF _ \<open>period (take n v) k\<close>, unfolded \<open>\<^bold>|take n v\<^bold>| = n\<close>, OF \<open>k dvd n\<close>] by presburger
  have "\<^bold>|take k v\<^bold>| = k"
    using  order.trans[OF \<open>k \<le> n\<close> \<open>n \<le> \<^bold>|v\<^bold>|\<close>, THEN take_len].
  obtain e where  "w \<le>f (take n v)\<^sup>@e"
    using per_fac_pow_fac[OF \<open>period w n\<close> \<open>take n v \<le>f w\<close> \<open>\<^bold>|take n v\<^bold>| = n\<close>].
  from per_fac[OF \<open>w \<noteq> \<epsilon>\<close> this[folded \<open>(take k v)\<^sup>@(n div k) = take n v\<close>, folded  pow_mult]]
  show ?thesis
    unfolding \<open>\<^bold>|take k v\<^bold>| = k\<close> by blast
qed

lemma xy_per_comp: assumes "x\<cdot>y \<le>p q\<cdot>x\<cdot>y"
  and "q \<noteq> \<epsilon>" and "q \<bowtie> y"
shows "x \<bowtie> y"
proof(cases rule: pref_compE[OF \<open>q \<bowtie> y\<close>])
  assume "q \<le>p y"
  have "x\<cdot>q = q\<cdot>x"
    using
      pref_cancel'[OF \<open>q \<le>p y\<close>, of x, THEN pref_trans, OF \<open>x \<cdot> y \<le>p q \<cdot> x \<cdot> y\<close>]
    unfolding lassoc
    using ruler_eq_len[OF _ triv_pref swap_len]
    by blast
  thus ?thesis
    using assms(1) assms(2) pref_comp_sym root_comm_root
      ruler_pref'' same_prefix_prefix by metis
next
  assume "y \<le>p q"
  then show ?thesis
    by (meson append_prefixD prefix_append ruler' assms)
qed

lemma prim_xyxyy: "x \<cdot> y \<noteq> y \<cdot> x \<Longrightarrow> primitive (x \<cdot> y \<cdot> x \<cdot> y \<cdot> y)"
proof (rule prim_conjug)
  show "y \<cdot> x \<cdot> y \<cdot> x \<cdot> y \<sim> x \<cdot> y \<cdot> x \<cdot> y \<cdot> y"
    by (intro conjugI1) simp
  show "x \<cdot> y \<noteq> y \<cdot> x \<Longrightarrow> primitive (y \<cdot> x \<cdot> y \<cdot> x \<cdot> y)"
    by (intro iffD2[OF per_le_prim_iff[of _ "y \<cdot> x"]]) auto
qed

lemma prim_min_per_suf_eq: assumes "primitive x" and "\<pi> x \<le>s x" shows "\<pi> x = x"
  using assms(1) min_per_root_per_root[OF prim_nemp[OF \<open>primitive x\<close>], unfolded  ] root_suf_comm'[OF _ \<open>\<pi> x \<le>s x\<close>]
  unfolding primitive_iff_per  by blast

lemma primroot_code[code]: "\<rho> x = (if x \<noteq> \<epsilon> then (if \<pi> x \<le>s x then \<pi> x else x) else Code.abort (STR ''Empty word has no primitive root.'') (\<lambda>_. (\<rho> x)))"
proof(cases "x = \<epsilon>")
  assume "x \<noteq> \<epsilon>"
  thus ?thesis
    unfolding if_P[OF \<open>x \<noteq> \<epsilon>\<close>]
  proof(cases)
    assume "e\<^sub>\<rho> x = 1"
    have "primitive x"
      using primroot_exp_eq[of x, unfolded \<open>e\<^sub>\<rho> x = 1\<close> exp_simps]
      unfolding prim_primroot_conv[OF \<open>x \<noteq> \<epsilon>\<close>].
    from prim_min_per_suf_eq[OF this] prim_self_root[OF this]
    show "\<rho> x = (if \<pi> x \<le>s x then \<pi> x else x)"
      by argo
  next
    assume "e\<^sub>\<rho> x \<noteq> 1"
    show "\<rho> x = (if \<pi> x \<le>s x then \<pi> x else x)"
      using primroot_suf
      unfolding min_per_short_primroot[OF \<open>x \<noteq> \<epsilon>\<close> primroot_exp_eq \<open>e\<^sub>\<rho> x \<noteq> 1\<close>]
      by auto
  qed
qed (simp add: primitive_root_def)

lemma per_lemma_pref_suf: assumes "w <p p \<cdot> w" and "w <s w \<cdot> q" and
  fw: "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| \<le> \<^bold>|w\<^bold>|"
obtains r s k l m where "p = (r \<cdot> s)\<^sup>@k" and "q = (s \<cdot> r)\<^sup>@l" and "w = (r \<cdot> s)\<^sup>@m \<cdot> r" and "primitive (r\<cdot>s)"
proof-
  let ?q = "(w \<cdot> q)\<^sup><\<inverse>w"
  have "w <p ?q \<cdot> w"
    using ssufD1[OF \<open>w <s w \<cdot> q\<close>] rq_suf[symmetric, THEN per_rootI[OF prefI rq_ssuf[OF \<open>w <s w \<cdot> q\<close>]]]
    by argo
  have "q \<sim> ?q"
    by (meson assms(2) conjugI1 conjug_sym rq_suf suffix_order.less_imp_le)

  have nemps': "p \<noteq> \<epsilon>" "?q\<noteq> \<epsilon>"
    using assms(1) \<open>w <p ?q\<cdot>w\<close> by fastforce+
  from two_pers[OF sprefD1[OF \<open>w <p p \<cdot> w\<close>] sprefD1[OF \<open>w <p ?q\<cdot>w\<close>]] fw
  have "p \<cdot> ?q = ?q \<cdot> p"
    unfolding conjug_len[OF \<open>q \<sim> (w \<cdot> q)\<^sup><\<inverse>w\<close>]
    by blast
  then have "\<rho> p = \<rho> ?q" using comm_primroots[OF nemps'] by force
  hence [symmetric]: "\<rho> q \<sim> \<rho> p"
    using conjug_primroot[OF \<open>q \<sim> (w \<cdot> q)\<^sup><\<inverse>w\<close>]
    by argo
  from conjug_primrootsE[OF this]
  obtain r s k l where
    "p = (r \<cdot> s) \<^sup>@ k" and
    "q = (s \<cdot> r) \<^sup>@ l" and
    "primitive (r \<cdot> s)".
  have "w \<le>p (r\<cdot>s)\<cdot>w"
    using assms per_root_drop_exp  sprefD1 \<open>p = (r \<cdot> s) \<^sup>@ k\<close>
    by meson
  have "w \<le>s w\<cdot>(s\<cdot>r)"
    using assms(2) per_root_drop_exp[reversed] ssufD1 \<open>q = (s \<cdot> r) \<^sup>@ l\<close>
    by meson
  have "\<^bold>|r \<cdot> s\<^bold>| \<le> \<^bold>|w\<^bold>|"
    using conjug_nemp_iff[OF \<open>q \<sim> ?q\<close>] dual_order.trans length_0_conv  nemps' primroot_len_le[OF nemps'(1)] fw
    unfolding primroot_unique[OF nemps'(1) \<open>primitive (r \<cdot> s)\<close> \<open>p = (r \<cdot> s) \<^sup>@ k\<close>]
    by linarith
  from root_suf_conjug[OF \<open>primitive (r \<cdot> s)\<close> \<open>w \<le>p (r\<cdot>s)\<cdot>w\<close> \<open>w \<le>s w\<cdot>(s\<cdot>r)\<close> this]
  obtain m where "w = (r \<cdot> s) \<^sup>@ m \<cdot> r".
  from that[OF \<open>p = (r \<cdot> s) \<^sup>@ k\<close> \<open>q = (s \<cdot> r) \<^sup>@ l\<close> this \<open>primitive (r \<cdot> s)\<close>]
  show ?thesis.
qed

lemma fac_two_conjug_primroot:
  assumes facs: "w \<le>f p\<^sup>@k" "w \<le>f q\<^sup>@l" and nemps: "p \<noteq> \<epsilon>" "q \<noteq> \<epsilon>" and len: "\<^bold>|p\<^bold>| + \<^bold>|q\<^bold>| \<le> \<^bold>|w\<^bold>|"
  obtains r s m where "\<rho> p \<sim> r \<cdot> s" and "\<rho> q \<sim> r \<cdot> s" and "w = (r \<cdot> s)\<^sup>@m \<cdot> r" and "primitive (r\<cdot>s)"
proof -
  obtain p' where "w <p p'\<cdot>w" "p \<sim> p'" "p' \<noteq> \<epsilon>"
    using conjug_nemp_iff fac_pow_pref_conjug[OF facs(1)] nemps(1) per_rootI' by metis
  obtain q' where "w <s w\<cdot>q'" "q \<sim> q'" "q' \<noteq> \<epsilon>"
    using fac_pow_pref_conjug[reversed, OF \<open>w \<le>f q\<^sup>@l\<close>] conjug_nemp_iff  nemps(2) per_rootI'[reversed] by metis
  from per_lemma_pref_suf[OF \<open>w <p p'\<cdot>w\<close> \<open>w <s w\<cdot>q'\<close>]
  obtain r s k l m where
    "p' = (r \<cdot> s) \<^sup>@ k" and
    "q' = (s \<cdot> r) \<^sup>@ l" and
    "w = (r \<cdot> s) \<^sup>@ m \<cdot> r" and
    "primitive (r \<cdot> s)"
    using len[unfolded conjug_len[OF \<open>p \<sim> p'\<close>] conjug_len[OF \<open>q \<sim> q'\<close>]]
    by blast
  moreover have "\<rho> p' = r\<cdot>s"
    using \<open>p' = (r \<cdot> s) \<^sup>@ k\<close> \<open>primitive (r \<cdot> s)\<close> \<open>p' \<noteq> \<epsilon>\<close> primroot_unique by blast
  hence "\<rho> p \<sim> r\<cdot>s"
    using conjug_primroot[OF \<open>p \<sim> p'\<close>]
    by simp
  moreover have "\<rho> q' = s\<cdot>r"
    using \<open>q' = (s \<cdot> r) \<^sup>@ l\<close> \<open>primitive (r \<cdot> s)\<close>[unfolded conjug_prim_iff'[of r]] \<open>q' \<noteq> \<epsilon>\<close> primroot_unique by blast
  hence "\<rho> q \<sim> s\<cdot>r"
    using conjug_primroot[OF \<open>q \<sim> q'\<close>]  by simp
  hence "\<rho> q \<sim> r\<cdot>s"
    using conjug_trans[OF _ conjugI']
    by meson
  ultimately show ?thesis
    using that by blast
qed

corollary fac_two_conjug_primroot':
   assumes facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l" and nemps: "r \<noteq> \<epsilon>" "s \<noteq> \<epsilon>" and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| \<le> \<^bold>|u\<^bold>|"
   shows "\<rho> r \<sim> \<rho> s"
  using fac_two_conjug_primroot[OF assms] conjug_trans[OF _ conjug_sym[of "\<rho> s"]]
  by metis

lemma fac_two_conjug_primroot'':
  assumes facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l" and "u \<noteq> \<epsilon>" and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| \<le> \<^bold>|u\<^bold>|"
  shows "\<rho> r \<sim> \<rho> s"
proof -
  have nemps: "r \<noteq> \<epsilon>" "s \<noteq> \<epsilon>" using facs \<open>u \<noteq> \<epsilon>\<close> by auto
  show "conjugate (\<rho> r) (\<rho> s)" using fac_two_conjug_primroot'[OF facs nemps len].
qed

lemma  fac_two_prim_conjug:
  assumes "w \<le>f u\<^sup>@n" "w \<le>f v\<^sup>@m" "primitive u" "primitive v" "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>|"
  shows "u \<sim> v"
  using fac_two_conjug_primroot'[OF assms(1-2) _ _ assms(5)] prim_nemp[OF \<open>primitive u\<close>] prim_nemp[OF \<open>primitive v\<close>]
  unfolding prim_self_root[OF \<open>primitive u\<close>] prim_self_root[OF \<open>primitive v\<close>].

lemma fac_pow_conjug_primroot: assumes "u\<^sup>@k \<le>f v\<^sup>@l" and "\<^bold>|u\<^sup>@k\<^bold>| \<ge> 2*\<^bold>|v\<^bold>|" and "2 \<le> k" and "u \<noteq> \<epsilon>"
  shows "\<rho> u \<sim> \<rho> v"
proof(rule fac_two_conjug_primroot''[OF _ assms(1)], force)
  have "0 < k"
     using \<open>2 \<le> k\<close> by linarith
  show "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|u \<^sup>@ k\<^bold>|"
  proof(cases "\<^bold>|u\<^bold>|" "\<^bold>|v\<^bold>|" rule: le_cases)
    assume "\<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|"
    thus ?thesis
      using assms(2) by linarith
  next
    assume "\<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>|"
    hence " \<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> 2*\<^bold>|u\<^bold>|"
      by simp
    thus ?thesis
      unfolding pow_len
      using mult_le_mono1[OF \<open>2 \<le> k\<close>] le_trans
      by blast
  qed
  show "u \<^sup>@ k \<noteq> \<epsilon>"
    using \<open>u \<noteq> \<epsilon>\<close> \<open>0 < k\<close> by blast
qed

section \<open>Testing primitivity\<close>

text\<open>This section defines a proof method used to prove that a word is primitive.\<close>

lemma primitive_iff [code]: "primitive w \<longleftrightarrow> \<not> w \<le>f tl w \<cdot> butlast w"
proof-
  have "\<not> primitive w \<longleftrightarrow> w \<le>f tl w \<cdot> butlast w"
  proof
    assume "\<not> primitive w"
    then obtain r k where "k \<noteq> 1" and "w = r\<^sup>@k"
      unfolding primitive_def by blast
    show "w \<le>f tl w \<cdot> butlast w"
    proof (cases "w = \<epsilon>")
      assume "w \<noteq> \<epsilon>"
      from this[unfolded \<open>w = r\<^sup>@k\<close>]
      have  "0 < k"
        using nemp_pow by blast
      have "r \<noteq> \<epsilon>"
        using pow_zero \<open>r \<^sup>@ k \<noteq> \<epsilon>\<close> by force
      have "r\<^sup>@(k-1) \<noteq> \<epsilon>"
        unfolding nemp_emp_pow[OF \<open>r \<noteq> \<epsilon>\<close>, of "k-1"]
        using \<open>0 < k\<close> \<open>k \<noteq> 1\<close> by force
      have "r \<cdot> w \<cdot> r\<^sup>@(k-1) = w \<cdot> w"
        unfolding \<open>w = r\<^sup>@k\<close> pows_comm[of r k "k - 1"]
        unfolding lassoc cancel_right pow_pos[OF \<open>0 < k\<close>]..
      hence "[hd r] \<cdot> tl r \<cdot> w \<cdot> butlast (r\<^sup>@(k-1)) \<cdot> [last (r\<^sup>@(k-1))] = [hd w] \<cdot> tl w \<cdot> butlast w \<cdot> [last w]"
        unfolding hd_tl[reversed, OF \<open>r\<^sup>@(k-1) \<noteq> \<epsilon>\<close>] hd_tl[reversed, OF \<open>w \<noteq> \<epsilon>\<close>]
        unfolding lassoc hd_tl[OF \<open>r \<noteq> \<epsilon>\<close>] hd_tl[OF \<open>w \<noteq> \<epsilon>\<close>].
      hence "tl r \<cdot> w \<cdot> butlast (r\<^sup>@(k-1)) = tl w \<cdot> butlast w"
        by force
      thus ?thesis
        unfolding fac_def by metis
    qed simp
  next
    assume "w \<le>f tl w \<cdot> butlast w"
    show "\<not> primitive w"
    proof (cases "w = \<epsilon>")
      assume "w \<noteq> \<epsilon>"
      from facE[OF \<open>w \<le>f tl w \<cdot> butlast w\<close>]
      obtain p s where "tl w \<cdot> butlast w = p \<cdot> w \<cdot> s".
      have "[hd w] \<cdot> (p \<cdot> w \<cdot> s) \<cdot> [last w] = w \<cdot> w"
        unfolding \<open>tl w \<cdot> butlast w = p \<cdot> w \<cdot> s\<close>[symmetric]
        unfolding lassoc hd_tl[OF \<open>w \<noteq> \<epsilon>\<close>]
        unfolding rassoc hd_tl[reversed, OF \<open>w \<noteq> \<epsilon>\<close>]..
      from prim_overlap_sqE[of w "[hd w] \<cdot> p" "s \<cdot> [last w]" False, unfolded rassoc, OF _  this[unfolded rassoc]]
      show "\<not> primitive w"
        by blast
    qed simp
  qed
  thus ?thesis by blast
qed

method primitivity_inspection =  (insert method_facts, use nothing in
    \<open>simp add: primitive_iff pow_pos\<close>)

\<comment> \<open>This is out of scope of the method, and has to be proved separately\<close>
lemma alternate_prim: assumes "x \<noteq> y" shows "primitive ([x,y]\<^sup>@n\<cdot>[x])"
proof-
  consider "n = 0" | "n = 1" | "2 \<le> n" by linarith
  then show ?thesis
  proof(cases)
   assume "2 \<le> n"
   have pref: "[x, y] \<^sup>@ n \<cdot> [x] \<le>p [x, y] \<cdot> [x, y] \<^sup>@ n \<cdot> [x]"
     by comparison
   have neq: "([x, y] \<^sup>@ n \<cdot> [x]) \<cdot> [x, y] \<noteq> [x, y] \<cdot> [x, y] \<^sup>@ n \<cdot> [x]"
     using  \<open>x \<noteq> y\<close> by force
   then show ?thesis
     using per_le_prim_iff[of "[x,y]\<^sup>@n\<cdot>[x]" "[x,y]", OF pref] \<open>2 \<le> n\<close>
     unfolding lenmorph pow_len
     by fastforce
 qed (simp_all add: \<open>x \<noteq> y\<close> primitive_iff)
qed








end
