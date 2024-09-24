theory HOL_Basis
imports
  (* Main *)
  "tools/Strengthen" \<comment>\<open> l4v: rewriting using monotonicity \<close>
  "HOL-Library.Complete_Partial_Order2" \<comment>\<open> \<^verbatim>\<open>partial_function\<close> setup \<close>
  "HOL-Library.Monad_Syntax"
  "Coinductive.TLList" \<comment>\<open> Terminated coinductive lists. imports \<open>HOL-Library.Sublist\<close> \<close>
  "HOL-Library.BNF_Corec" \<comment>\<open> for TLS \<close>
begin

section\<open> Extra HOL \<close>

(* Syntax *)

declare [[coercion_enabled = false]]

hide_const (open) BNF_Cardinal_Order_Relation.stable
hide_const (open) Topological_Spaces.incseq
hide_const (open) Topological_Spaces.decseq

no_notation Binomial.binomial (infixl \<open>choose\<close> 65)
no_notation Sublist.parallel (infixl \<open>\<parallel>\<close> 50)

consts parallel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>\<parallel>\<close> 53) \<comment>\<open> for adhoc overloading \<close>

consts Parallel :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" \<comment>\<open> for adhoc overloading \<close>

syntax
  "_PAR1"     :: "pttrns \<Rightarrow> 'a set \<Rightarrow> 'b"                    (\<open>(3\<Parallel>_./ _)\<close> [0, 10] 10)
  "_PAR"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"               (\<open>(3\<Parallel>_\<in>_./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_PAR1" "_PAR" \<rightleftharpoons> Parallel

translations
  "\<Parallel>x y. f"   \<rightleftharpoons> "\<Parallel>x. \<Parallel>y. f"
  "\<Parallel>x. f"     \<rightleftharpoons> "CONST Parallel CONST UNIV (\<lambda>x. f)"
  "\<Parallel>x\<in>A. f"   \<rightleftharpoons> "CONST Parallel A (\<lambda>x. f)"

(* Pure *)

lemmas conj_explode = conj_imp_eq_imp_imp

(* HOL *)

lemma If_Not[simp]:
  shows "(if \<not>P then Q else R) = (if P then R else Q)"
by simp

lemma Let_distrib:
  shows "f (let x = a in e x) = (let x = a in f (e x))"
by simp

lemma stronger_disjE:
  assumes "P \<or> Q"
  assumes "P \<Longrightarrow> R"
  assumes "\<lbrakk>\<not>P; Q\<rbrakk> \<Longrightarrow> R"
  shows "R"
using assms by blast

(* Set *)

abbreviation (input) Collect2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) set" where
  "Collect2 P \<equiv> Collect (case_prod P)"

lemma mono_Set_bind:
  shows "mono (\<lambda>X. Set.bind X f)"
unfolding Set.bind_def by (rule monoI) fast

lemma
    minus_False[simp]: "-{False} = {True}"
and minus_True[simp]: "-{True} = {False}"
by blast+

lemma
  shows Collect_True[simp]: "{x. x} = {True}"
    and Collect_bot[simp]: "Collect \<bottom> = {}"
    and Collect_Not[simp]: "Collect Not = {False}"
by blast+

lemma const_image_conv:
  shows "(\<lambda>_. c) ` X \<subseteq> Y \<longleftrightarrow> (c \<notin> Y \<longrightarrow> X = {})"
by blast

lemma inv_vimage:
  assumes "surj f"
  shows "inv f -` f -` x = x"
using assms by (metis image_comp image_f_inv_f surj_iff surj_image_vimage_eq vimage_comp)

lemma Union_singleton:
  shows "\<Union>{{x} |x. x \<in> X} = X"
by blast

lemma UNIV_minus_uminus[simp]:
  shows "UNIV - X = -X"
by auto

lemmas insert_Image = Un_Image[where R="{r}", simplified] for r

lemma Image_UNIV:
  fixes R :: "('a \<times> 'b) set"
  shows "R `` UNIV = snd ` R"
by force

lemma insert_Diff_UNIV:
  shows "insert x (- {x}) = UNIV"
    and "insert x (UNIV - {x}) = UNIV"
by blast+

(* commute LHS of conversions *)

lemmas eq_commute_conv = HOL.eq_iff_swap

lemma inf_commute_conv:
  fixes x :: "_::semilattice_inf"
  assumes "x \<sqinter> y = z"
  shows "y \<sqinter> x = z"
by (simp add: assms inf_commute)

(* Fun *)

abbreviation (input) uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c" where "uncurry \<equiv> case_prod"

lemmas fun_eqI = ext

lemma override_on_cong[cong]:
  assumes "A = A'"
  assumes "\<And>x. x \<notin> A' \<Longrightarrow> f x = f' x"
  assumes "\<And>x. x \<in> A' \<Longrightarrow> g x = g' x"
  shows "override_on f g A = override_on f' g' A'"
using assms by (simp add: override_on_def fun_eq_iff)

lemma override_on_comp:
  shows "h \<circ> override_on f g A = override_on (h \<circ> f) (h \<circ> g) A"
by (simp_all add: override_on_def fun_eq_iff)

lemma refine_compose:
  assumes "\<forall>x y. f x = f y \<longrightarrow> g x = g y"
  obtains h where "g = h \<circ> f"
proof atomize_elim
  from assms have "g = (g \<circ> inv f) \<circ> f"
    unfolding o_def inv_def by (metis (mono_tags, lifting) someI_ex)
  then show "\<exists>h. g = h \<circ> f" by blast
qed

lemma inj_Not[iff]:
  shows "inj Not"
by (simp add: inj_def)

lemma bij_Not[iff]:
  shows "bij Not"
unfolding bij_def by blast

lemma bij_inv_eq_iff:
  assumes "bij p"
  shows "x = inv p y \<longleftrightarrow> p x = y"
    and "inv p y = x \<longleftrightarrow> p x = y"
by (simp_all add: assms bij_inv_eq_iff eq_commute_conv[OF bij_inv_eq_iff])

lemma bij_inv:
  assumes "bij f"
  shows "f (inv f x) = x"
    and "f \<circ> inv f = id"
by (simp_all add: assms fun_eq_iff flip: bij_inv_eq_iff)

lemma image_image_set_diff_singleton:
  assumes "inj f"
  shows "f ` A - {f a} = f ` (A - {a})"
by (simp add: assms image_set_diff)

lemma image_Inter_subseteq:
  shows "f ` \<Inter>A \<subseteq> \<Inter>{f ` x |x. x \<in> A}"
by blast

lemma fst_image:
  shows "fst ` Collect (\<lambda>x. \<exists>s. x = (v, s, s)) = {v}"
by force

lemma Least_equality:
  fixes x :: "_::order"
  assumes "P x"
  assumes "\<And>y. P y \<Longrightarrow> x \<le> y"
  shows "Least P = x"
    and "x = Least P"
using Least_equality assms by blast+

(* Product_Type *)

declare map_prod.id[simp]
declare map_prod.compositionality[simp]

lemma map_prod_image_Collect:
  fixes f :: "'a \<Rightarrow> 'b"
  fixes g :: "'c \<Rightarrow> 'd"
  shows "map_prod f g ` Collect P = {(f x, g y) |x y. P (x, y)}"
by blast

lemma range_map_prod:
  shows "range (map_prod f g) = range f \<times> range g"
by blast

declare unit.case_cong_weak[cong del] \<comment>\<open> sometimes introduces schematics \<close>

lemma lambda_unit_futzery:
  shows "(\<lambda>_. P) = (\<lambda>(). P)"
by auto

lemma fun_unit_id:
  shows "(f :: unit \<Rightarrow> unit) = id"
by (simp add: fun_eq_iff)

lemma surj_unit_range[iff]:
  shows "surj (f :: _ \<Rightarrow> unit)"
unfolding surj_def by simp

lemma split_pairs:
  shows "((x, y) = z) \<longleftrightarrow> (fst z = x \<and> snd z = y)"
    and "(z = (x, y)) \<longleftrightarrow> (fst z = x \<and> snd z = y)"
by auto

lemma eq_split_pair:
  shows "(=) (x, y) = (\<lambda>p. fst p = x \<and> snd p = y)"
by fastforce

lemma map_prod_conv:
  shows "(x, y) = map_prod f g z \<longleftrightarrow> (\<exists>a b. z = (a, b) \<and> x = f a \<and> y = g b)"
    and "map_prod f g z = (x, y) \<longleftrightarrow> (\<exists>a b. z = (a, b) \<and> x = f a \<and> y = g b)"
by (case_tac [!] z) auto

lemma map_prod_image_Times:
  shows "map_prod f g ` (F \<times> G) = f ` F \<times> g ` G"
by blast

lemma map_prod_vimage_Times:
  shows "map_prod f g -` (F \<times> G) = f -` F \<times> g -` G"
by fastforce

lemma vimage_range:
  shows "f -` range f = UNIV"
by blast

lemma Pair_image:
  shows "Pair x ` F = {x} \<times> F"
by fast

lemma fst_image_map_prod:
  shows "fst ` map_prod f g ` X = f ` fst ` X"
unfolding image_def by force

lemma snd_image_map_prod:
  shows "snd ` map_prod f g ` X = g ` snd ` X"
unfolding image_def by force

lemma Times_Un_distrib2:
  shows "A \<times> (B \<union> C) = A \<times> B \<union> A \<times> C"
by fast

lemma Times_insert_distrib1:
  shows "insert x X \<times> Y = {x} \<times> Y \<union> X \<times> Y"
by fast

lemma map_prod_apfst[simp]:
  shows "map_prod f g (apfst h x) = map_prod (f \<circ> h) g x"
    and "apfst f (map_prod h g x) = map_prod (f \<circ> h) g x"
by (simp_all add: apfst_def)

lemma map_prod_apsnd[simp]:
  shows "map_prod f g (apsnd h x) = map_prod f (g \<circ> h) x"
    and "apsnd g (map_prod f h x) = map_prod f (g \<circ> h) x"
by (simp_all add: apsnd_def)

lemma map_prod_const_image:
  shows "map_prod (\<lambda>x. c) g ` X = {c} \<times> g ` snd ` X"
    and "map_prod f (\<lambda>x. c) ` X = f ` fst ` X \<times> {c}"
by force+

(* Relation *)

type_synonym 'a relp = "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition Diag :: "('a \<Rightarrow> bool) \<Rightarrow> 'a rel" where
  "Diag P = Restr Id (Collect P)"

abbreviation Pre :: "('s \<Rightarrow> bool) \<Rightarrow> 's rel" where
  "Pre P \<equiv> Collect P \<times> UNIV"

abbreviation Post :: "('v \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> 's rel" where
  "Post Q v \<equiv> UNIV \<times> Collect (Q v)"

lemma member_Diag[simp]:
  shows "(x, y) \<in> Diag P \<longleftrightarrow> x = y \<and> P x"
by (fastforce simp: Diag_def)

lemma Diag_Id_le[iff]:
  shows "Diag P \<subseteq> Id"
by (fastforce simp: Diag_def)

lemma mono_Diag:
  shows "mono Diag"
by (fastforce simp: Diag_def intro: monoI)

lemmas strengthen_Diag[strg] = st_monotone[OF mono_Diag]

lemma Diag_bot[iff]:
  shows "Diag \<bottom> = {}"
    and "Diag (\<lambda>_. False) = {}"
by (simp_all add: Diag_def)

lemma Diag_top[iff]:
  shows "Diag \<top> = Id"
    and "Diag (\<lambda>_. True) = Id"
by (auto simp: Diag_def)

lemma Diag_Sup:
  shows "Diag (\<Squnion>X) = \<Squnion>(Diag ` X)"
unfolding Diag_def by blast

declare refl_Id[iff]

lemma Id_not_empty[iff]:
  shows "Id \<noteq> {}"
by fast

lemma refl_alt_def:
  shows "refl r \<longleftrightarrow> Id \<subseteq> r"
unfolding refl_on_def by auto

lemma mono_Image:
  shows "mono (Image r)"
by (rule monoI) auto

lemma Image_comp:
  shows "(``) R \<circ> (``) S = (``) (S O R)"
by fastforce

lemmas refl_INTER = refl_on_INTER[where A="\<lambda>x. UNIV" and S=UNIV, simplified, rule_format]

lemma refl_UnionI:
  assumes "r \<in> R"
  assumes "refl r"
  shows "refl (\<Union>R)"
using assms unfolding refl_on_def by fast

lemma refl_UNIV[iff]:
  shows "refl UNIV"
unfolding refl_on_def by simp

lemma trans_UNIV[iff]:
  shows "trans UNIV"
unfolding trans_def by simp

lemma refl_on_intI:
  assumes "refl_on A r"
  assumes "refl_on A s"
  shows "refl_on A (r \<inter> s)"
using assms unfolding refl_on_def by blast

lemma refl_inter_conv:
  shows "refl (r \<inter> s) \<longleftrightarrow> refl r \<and> refl s"
unfolding refl_on_def by auto

lemma map_prod_image_Image:
  fixes X :: "('a \<times> 'b) set"
  fixes Y :: "'c set"
  fixes f :: "'a \<Rightarrow> 'c"
  fixes g :: "'b \<Rightarrow> 'd"
  shows "(map_prod f g ` X) `` Y = g ` X `` f -` Y"
by (force simp add: Image_iff image_iff)

lemma equiv_closed:
  assumes "equiv A r"
  assumes "B \<subseteq> A"
  shows "r `` r `` B = r `` B"
using assms unfolding equiv_def by (auto elim: transE dest: refl_onD)

lemma sym_trans_refl_on:
  assumes "sym r"
  assumes "trans r"
  shows "refl_on (Domain r) r"
using assms by (force intro: refl_onI elim: symE transE)

declare bot_unique[simp]

declare subset_refl[iff]

declare trans_rtrancl[iff]
declare refl_rtrancl[iff]

declare le_bool_def[simp del] \<comment>\<open> turns \<open>(\<le>)\<close> into \<open>(\<longrightarrow>)\<close> \<close>

declare transp_le[intro!]

(* List *)

declare List.null_def[simp]

lemma split_list_Ex:
  shows "(\<exists>xxs. P xxs) \<longleftrightarrow> (P [] \<or> (\<exists>x xs. P (x # xs)))"
by (metis neq_Nil_conv)

lemma append_Nil[simp]:
  shows "(@) [] = id"
by fastforce

lemma case_list_cancel:
  shows "(case xs of [] \<Rightarrow> f | _ \<Rightarrow> f) = f"
by (simp split: list.splits)

lemma rev_induct2[consumes 1, case_names Nil snoc]:
  assumes "length xs = length ys"
  assumes "P [] []"
  assumes "\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
proof -
  have "P (rev (rev xs)) (rev (rev ys))"
    by (rule list_induct2[of "rev xs" "rev ys"]) (simp_all add: assms)
  then show ?thesis by simp
qed

lemma Image_set_map_filter:
  shows "set xs `` X = set (map snd (filter (\<lambda>x. fst x \<in> X) xs))"
by (induct xs) auto

lemma case_list_snoc:
  shows "case_list n c (xs @ [x]) = c (hd (xs @ [x])) (tl (xs @ [x]))"
by (simp split: list.splits)

lemma sorted_wrt_set_last:
  assumes "x \<in> set xs"
  assumes "sorted_wrt r xs"
  assumes "reflp r"
  assumes "transp r"
  shows "r x (last xs)"
using assms by (induct xs) (auto elim: reflpE)

lemma append_eq_conv_conj:
  shows "(zs = xs @ ys) = (xs = take (length xs) zs \<and> ys = drop (length xs) zs)"
    and "(xs @ ys = zs) = (xs = take (length xs) zs \<and> ys = drop (length xs) zs)"
by (rule eq_commute_conv) (simp_all add: append_eq_conv_conj)

lemma drop_eq_Cons_length_conv:
  shows "(\<exists>y ys. drop i xs = y # ys) \<longleftrightarrow> i < length xs"
using neq_Nil_conv by fastforce

lemma drop_eq_Cons_lengthD:
  assumes "drop i xs = y # ys"
  shows "i < length xs"
by (meson assms drop_eq_Cons_length_conv)

lemma filter_weaken_cong:
  assumes "filter P xs = filter P ys"
  assumes "\<forall>x. Q x \<longrightarrow> P x"
  shows "filter Q xs = filter Q ys"
using assms(1)
proof(induct xs arbitrary: ys)
  case Nil with assms(2) show ?case by (auto simp: empty_filter_conv)
next
  case (Cons x xs) from assms(2) Cons.prems show ?case
    by (auto 4 3 simp: Cons_eq_filter_iff filter_empty_conv dest!: Cons.hyps split: if_splits)
qed

lemma filter_eq_ConsE:
  assumes "filter P xs = y # ys"
  obtains us vs where "xs = us @ y # vs" and "\<forall>u\<in>set us. \<not> P u" and "P y" and "ys = filter P vs"
using iffD1[OF filter_eq_Cons_iff assms] by blast

lemma Cons_eq_filterE:
  assumes "y # ys = filter P xs"
  obtains us vs where "xs = us @ y # vs" and "\<forall>u\<in>set us. \<not> P u" and "P y" and "ys = filter P vs"
using filter_eq_ConsE[OF sym[OF assms]] .

lemma filter_eq_appendE:
  assumes "filter P xs = ys @ zs"
  obtains us vs where "xs = us @ vs" and "filter P us = ys" and "filter P vs = zs"
apply atomize_elim
using assms
proof(induct xs arbitrary: ys)
  case (Cons x xs ys) then show ?case
    by (clarsimp simp: Cons_eq_append_conv split: if_split_asm; metis filter.simps)
qed simp

lemma append_eq_filterE:
  assumes "ys @ zs = filter P xs"
  obtains us vs where "xs = us @ vs" and "filter P us = ys" and "filter P vs = zs"
using assms by (metis filter_eq_appendE)

lemma filter_eq_append_conv:
  shows "filter P xs = ys @ zs \<longleftrightarrow> (\<exists>us vs. xs = us @ vs \<and> filter P us = ys \<and> filter P vs = zs)" (is ?thesis1)
    and "ys @ zs = filter P xs \<longleftrightarrow> (\<exists>us vs. xs = us @ vs \<and> filter P us = ys \<and> filter P vs = zs)" (is ?thesis2)
proof -
  show ?thesis1 by (meson filter_append filter_eq_appendE)
  then show ?thesis2 by (rule eq_commute_conv)
qed

lemma fold_fun:
  shows "fold (\<lambda>x. (\<circ>) (f x)) xs g s = fold f xs (g s)"
by (induct xs arbitrary: s g) simp_all

lemma last_Pair_const:
  shows "last ((a, b) # map (\<lambda>x. (a, snd x)) xs) = (a, last (b # map snd xs))"
by (induct xs) auto

lemma mono_nth_Suc_aux:
  fixes xs :: "_::linorder list"
  assumes "\<forall>i < length xs - Suc 0. xs ! i \<le> xs ! Suc i"
  assumes "j < length xs"
  assumes "i \<le> j"
  shows "xs ! i \<le> xs ! j"
using assms
proof(induct j)
  case (Suc j) then show ?case
    by (fastforce dest: iffD1[OF le_eq_less_or_eq] spec[where x="j"])
qed simp

lemma mono_nth_Suc:
  fixes xs :: "_::linorder list"
  shows "(\<forall>j < length xs. \<forall>i \<le> j. xs ! i \<le> xs ! j) \<longleftrightarrow> (\<forall>i < length xs - 1. xs!i \<le> xs ! Suc i)"
by (auto intro: mono_nth_Suc_aux)

lemma sorted_nth_monoI2:
  assumes "\<And>i. i < length xs - 1 \<Longrightarrow> xs ! i \<le> xs ! Suc i"
  shows "sorted xs"
by (meson assms mono_nth_Suc sorted_iff_nth_mono)

lemma bij_map_prod:
  shows "bij (map_prod f g) \<longleftrightarrow> bij f \<and> bij g"
unfolding bij_def surj_def inj_def by auto

lemma bij_inv_map_prod:
  assumes "bij f"
  assumes "bij g"
  shows "inv (map_prod f g) = map_prod (inv f) (inv g)"
by (simp add: assms fun_eq_iff bij_inv_eq_iff bij_map_prod bij_inv)

lemma surj_map_conv:
  shows "surj (map f) \<longleftrightarrow> surj f"
by (auto simp flip: lists_UNIV lists_image) (metis Cons_in_lists_iff UNIV_I lists_UNIV)

lemma bij_map_conv:
  shows "bij (map f) \<longleftrightarrow> bij f"
by (simp add: bij_betw_def surj_map_conv)

lemma inv_map:
  assumes "bij f"
  shows "inv (map f) xs = map (inv f) xs"
by (simp add: assms bij_inv_eq_iff(2)[OF iffD2[OF bij_map_conv]] bij_inv)

lemma set_singleton_conv:
  shows "set xs = {x} \<longleftrightarrow> (\<exists>i. xs = replicate (Suc i) x)" (is ?thesis1)
    and "{x} = set xs \<longleftrightarrow> (\<exists>i. xs = replicate (Suc i) x)" (is ?thesis2)
proof -
  show ?thesis1
    by (metis length_Cons neq_Nil_conv replicate_length_same set_empty2 set_replicate_Suc singletonD)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma nths_singleton_le:
  assumes "i < length xs"
  shows "nths xs {i} = [xs ! i]"
using assms
by (induct xs rule: rev_induct)
   (auto simp: nths_def nth_append not_less filter_empty_conv elim: in_set_zipE)

lemma nths_empty_conv:
  shows "nths xs A = [] \<longleftrightarrow> xs = [] \<or> (\<forall>i\<in>A. length xs \<le> i)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  have "length xs \<le> i" if "\<forall>j<length xs. j \<notin> A" and "xs \<noteq> []" and "i \<in> A" for i
    using that leI by blast
  then show "?lhs \<Longrightarrow> ?rhs"
    by (fastforce dest: arg_cong[where f=set] simp: set_nths)
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp: nths_def filter_empty_conv elim!: in_set_zipE)
qed

lemma nths_singleton_eq_conv:
  shows "nths xs {i} = (if i < length xs then [xs ! i] else [])"
by (simp add: nths_empty_conv nths_singleton_le)

(* Sublist *)

\<comment>\<open> same proof as for @{thm [source] "prefix_append"} \<close>
lemma prefix_append_strict_prefix:
  shows "prefix xs (ys @ zs) \<longleftrightarrow> strict_prefix xs ys \<or> (\<exists>us. xs = ys @ us \<and> prefix us zs)"
using prefix_append prefix_code(1) prefix_order.le_less by blast

lemma prefix_append_not_Nil:
  shows "prefix xs (ys @ zs) \<longleftrightarrow> prefix xs ys \<or> (\<exists>us. xs = ys @ us \<and> us \<noteq> [] \<and> prefix us zs)"
by (fastforce simp: prefix_append)

lemma prefix_append_not_NilE[consumes 1, case_names incomplete continue]:
  assumes "prefix xs (ys @ zs)"
  assumes "prefix xs ys \<Longrightarrow> R"
  assumes "\<And>us. \<lbrakk>xs = ys @ us; us \<noteq> []; prefix us zs\<rbrakk> \<Longrightarrow> R"
  shows R
using assms prefix_append_not_Nil by blast

lemma subseq_Cons_right:
  shows "subseq xs (y # ys)
     \<longleftrightarrow> (case xs of [] \<Rightarrow> True | x' # xs' \<Rightarrow> (x' = y \<and> subseq xs' ys) \<or> subseq xs ys)"
by (auto elim: subseq_Cons' split: list.splits)

lemma take_is_strict_prefix[intro!]:
  assumes "n < length xs"
  shows "strict_prefix (take n xs) xs"
by (meson assms leD prefix_order.le_neq_trans take_all_iff take_is_prefix)

lemma wfP_strict_prefix:
  shows "wfP (strict_prefix :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool)"
proof -
  have "\<exists>z\<in>Q. \<forall>y. strict_prefix y z \<longrightarrow> y \<notin> Q" if "x \<in> Q" for x :: "'a list" and Q
    using that by (induct x rule: length_induct) (blast dest: prefix_length_less)
  then show ?thesis
    unfolding wfp_def by (auto intro!: wfI_min)
qed

lemma set_subseq:
  assumes "subseq xs ys"
  shows "set xs \<subseteq> set ys"
using assms by (metis notin_set_nthsI subseq_conv_nths subsetI)

lemma subseq_filter_alt:
  assumes "subseq xs ys"
  assumes "\<forall>x\<in>set xs. P x \<longrightarrow> Q x"
  shows "subseq (filter P xs) (filter Q ys)"
using assms by induct auto

lemma lists_not_eq:
  assumes "xs \<noteq> ys"
  assumes "length xs = length ys"
  obtains ps x y xs' ys'
    where "x \<noteq> y" and "xs = ps @ x # xs'" and "ys = ps @ y # ys'"
using same_length_different[OF assms] by clarsimp

lemmas prefix_map_rightD = prefix_map_rightE

lemma prefix_map_rightE:
  assumes "prefix xs (map f ys)"
  obtains xs' where "prefix xs' ys" and "xs = map f xs'"
by (meson assms prefix_map_rightD)

lemma prefix_filter_rightE:
  assumes "prefix xs (filter P ys)"
  obtains xs' where "prefix xs' ys" and "xs = filter P xs'"
by (metis assms filter_eq_appendE prefix_def)

lemma prefix_induct[case_names Nil snoc]:
  assumes "P []"
  assumes "\<And>xs' x. \<lbrakk>prefix (xs' @ [x]) xs; P xs'\<rbrakk> \<Longrightarrow> P (xs' @ [x])"
  shows "P xs"
proof -
  have "P xs'" if "prefix xs' xs" for xs'
    using that by (induct xs' rule: rev_induct) (auto simp: prefix_def assms)
  then show ?thesis by simp
qed

(* Option *)

declare map_option.id[simp]
declare map_option.id[unfolded id_def, simp]
declare map_option.compositionality[simp]

lemma not_None_eq2[simp]:
  shows "(None \<noteq> x) = (\<exists>y. x = Some y)"
by (metis not_Some_eq)

lemmas map_option_eq_Some[simp] =
  Option.map_option_eq_Some
  eq_commute_conv[OF Option.map_option_eq_Some]

lemma inj_map_option:
  shows "inj (map_option f) \<longleftrightarrow> inj f"
by (simp add: inj_def split_option_all)

lemma surj_map_option:
  shows "surj (map_option f) \<longleftrightarrow> surj f"
by (simp add: surj_def split_option_ex split_option_all)

lemma bij_map_option:
  shows "bij (map_option f) \<longleftrightarrow> bij f"
by (simp add: bij_def inj_map_option surj_map_option)

lemma inv_map_option:
  assumes "bij f"
  shows "inv (map_option f) x = map_option (inv f) x"
by (simp add: assms bij_inv_eq_iff bij_map_option bij_inv)

lemma case_option_cancel:
  shows "case_option f (\<lambda>_. f) opt = f"
by (simp split: option.splits)

lemma option_bind_alt_def:
  shows "Option.bind = (\<lambda>opt f. case_option None f opt)"
by (simp add: fun_eq_iff split: option.split)

lemma option_bind_eq_None_conv:
  shows "Option.bind a f = None \<longleftrightarrow>  a = None \<or> f (the a) = None"
    and "None = Option.bind a f \<longleftrightarrow>  a = None \<or> f (the a) = None"
by (intro Option.bind_eq_None_conv eq_commute_conv)+

overloading
  pfunpow \<equiv> "compow :: nat \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> 'a option)"
begin

primrec pfunpow :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<rightharpoonup> 'a" where
  "pfunpow 0 f = Some"
| "pfunpow (Suc n) f = (\<lambda>x. Option.bind (f x) (pfunpow n f))"

end

lemma pfunpow_0[simp]:
  shows "(f ^^ 0) x = Some x"
by simp

lemma pfunpow_Suc_right:
  shows "f ^^ Suc n = (\<lambda>x. Option.bind ((f ^^ n) x) f)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) show ?case by (simp flip: Suc)
qed

lemmas pfunpow_simps_right = pfunpow.simps(1) pfunpow_Suc_right

text \<open>For code generation.\<close>

context
begin

qualified definition pfunpow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a option" where
  pfunpow_code_def[code_abbrev]: "pfunpow = compow"

lemma pfunpow_code[code]:
  shows "pfunpow (Suc n) f = (\<lambda>x. (Option.bind (f x)) (pfunpow n f))"
    and "pfunpow 0 f = Some"
by (simp_all add: pfunpow_code_def fun_eq_iff)

end

lemma pfunpow_add:
  shows "f ^^ (m + n) = (\<lambda>x. Option.bind ((f ^^ m) x) (f ^^ n))"
by (induct m) simp_all

lemma pfunpow_mult:
  fixes f :: "'a \<Rightarrow> 'a option"
  shows "(f ^^ m) ^^ n = f ^^ (m * n)"
by (induct n) (simp_all add: pfunpow_add)

lemma pfunpow_swap1:
  fixes f :: "'a \<Rightarrow> 'a option"
  shows "((f ^^ n) x) \<bind> f = f x \<bind> (f ^^ n)"
by (rule fun_cong[OF trans[OF pfunpow.simps(2)[symmetric] pfunpow_Suc_right], symmetric])

lemma Some_pfunpow[simp]:
  shows "Some ^^ n = Some"
by (induct n) simp_all


(* Lattices *)

lemma (in linorder) split_asm_min:
  shows "P (min i j) \<longleftrightarrow> \<not> (i \<le> j \<and> \<not> P i \<or> \<not> i \<le> j \<and> \<not> P j)"
by (simp add: min_def)

lemma (in linorder) split_asm_max:
  shows "P (max i j) \<longleftrightarrow> \<not> (i \<le> j \<and> \<not> P j \<or> \<not> i \<le> j \<and> \<not> P i)"
by (simp add: max_def)

(* Sum *)

lemmas case_sum_cancel = case_sum_KK

lemma sum_In_conv:
  shows Inl_conv: "Inl a \<in> A <+> B \<longleftrightarrow> a \<in> A"
    and Inr_conv: "Inr b \<in> A <+> B \<longleftrightarrow> b \<in> B"
by blast+

(* Map *)

lemma restrict_map_UNIV[simp]:
  shows "m |` UNIV = m"
by fastforce

(* Finite_Set *)

lemma finite_distinct_conv:
  shows "finite X \<longleftrightarrow> finite {xs . set xs \<subseteq> X \<and> distinct xs}" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs show ?rhs
    by (rule rev_finite_subset[OF finite_lists_length_le[OF \<open>?lhs\<close>, where n="card X"]])
       (fastforce dest: card_mono[OF \<open>?lhs\<close>] distinct_card)
next
  have *: "X \<subseteq> \<Union>(set ` {xs. set xs \<subseteq> X \<and> distinct xs})" by (clarsimp simp: exI[where x="[x]" for x])
  show "?rhs \<Longrightarrow> ?lhs"
    by (blast intro: rev_finite_subset[OF finite_UN_I *])
qed

lemma Min_plus:
  fixes X :: "nat set"
  assumes "finite X"
  assumes "finite Y"
  assumes "X \<noteq> {}"
  assumes "Y \<noteq> {}"
  shows "Min X + Min Y = Min {x + y |x y. x \<in> X \<and> y \<in> Y}"
using assms by (force simp: finite_image_set2 add_mono intro: Min_in sym[OF Min_eqI])

(* Nat *)

lemma always_eventually_pigeonhole:
  "(\<forall>i. \<exists>n\<ge>i. \<exists>m\<le>k. P m n) \<longleftrightarrow> (\<exists>m\<le>k::nat. \<forall>i::nat. \<exists>n\<ge>i. P m n)"
proof(induct k)
  case (Suc k) then show ?case
    by (auto 8 0 dest: le_SucI) (metis order.trans le_SucE linorder_linear)
qed simp

(* Transitive_Closure *)

lemma refl_trans_rtrancl:
  assumes "refl r"
  assumes "trans r"
  shows "r\<^sup>* = r"
using assms by (simp add: refl_alt_def rtrancl_trancl_reflcl subset_antisym)

lemma refl_trans_rtrancl_conv:
  shows "r\<^sup>* = r \<longleftrightarrow> refl r \<and> trans r"
by (metis refl_rtrancl refl_trans_rtrancl trans_rtrancl)

lemma order_rtrancl: "{(x::_::order, y). x \<le> y}\<^sup>* = {(x, y). x \<le> y}"
by (auto intro!: refl_trans_rtrancl reflI transI)


subsection\<open> Inverse image under a function \<close>

lemma inv_image_alt_def:
  shows "inv_image r f = map_prod f f -` r"
unfolding inv_image_def by fastforce

lemma inv_image_id[simp]:
  shows "inv_image r id = r"
unfolding inv_image_def by simp

lemma inv_image_union:
  shows "inv_image (X \<union> Y) f = inv_image X f \<union> inv_image Y f"
unfolding inv_image_def by fast

lemma inv_image_inter:
  shows "inv_image (X \<inter> Y) f = inv_image X f \<inter> inv_image Y f"
unfolding inv_image_def by fast


subsection\<open> Identity relation under a projection\label{sec:id_on_proj} \<close>

definition Id_on_proj :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a rel" (\<open>Id\<^bsub>_\<^esub>\<close>) where
  "Id\<^bsub>f\<^esub> = {(s, s'). f s = f s'}"

lemma member_Id_on_proj[simp]:
  shows "(x, y) \<in> Id\<^bsub>f\<^esub> \<longleftrightarrow> f x = f y"
unfolding Id_on_proj_def by simp

lemma Id_on_proj_const:
  shows "Id\<^bsub>\<lambda>_. c\<^esub> = UNIV"
by (simp add: Id_on_proj_def)

lemma Id_on_proj_id:
  shows "Id\<^bsub>id\<^esub> = Id"
by (auto simp: Id_on_proj_def Id_def)

lemma Id_weaken[iff]:
  shows "Id\<^bsub>f\<^esub> \<subseteq> Id\<^bsub>\<lambda>s. g (f s)\<^esub>"
    and "(\<lambda>x y. (x, y) \<in> Id\<^bsub>f\<^esub>) \<le> (\<lambda>x y. (x, y) \<in> Id\<^bsub>\<lambda>s. g (f s)\<^esub>)"
by (auto simp: Id_on_proj_def)

lemma refl_Id_on_proj[iff]:
  shows "refl Id\<^bsub>f\<^esub>"
by (simp add: Id_on_proj_def refl_on_def)

lemma sym_Id_on_proj[iff]:
  shows "sym Id\<^bsub>f\<^esub>"
by (simp add: Id_on_proj_def sym_def)

lemma trans_Id_on_proj[iff]:
  shows "trans Id\<^bsub>f\<^esub>"
by (simp add: Id_on_proj_def trans_def)

lemma equiv_Id_on_proj[iff]:
  shows "equiv UNIV Id\<^bsub>f\<^esub>"
by (simp add: equiv_def)

lemma Id_on_proj_pred_pair:
  shows "Id\<^bsub>\<lambda>x. (f x, g x)\<^esub> = Id\<^bsub>f\<^esub> \<inter> Id\<^bsub>g\<^esub>"
by (auto simp: Id_on_proj_def)

lemma Id_on_proj_Inf:
  shows "(\<Inter>x\<in>X. Id\<^bsub>f x\<^esub>) = Id\<^bsub>\<lambda>s. (\<lambda>x. (x, f x s)) ` X\<^esub>"
by (fastforce simp: Id_on_proj_def)


subsection\<open> Ordering under a projection \<close>

definition less_eq_on_proj :: "('s \<Rightarrow> 'a::ord) \<Rightarrow> 's rel" (\<open>\<^bold>\<le>\<^bsub>_\<^esub>\<close>) where
  "\<^bold>\<le>\<^bsub>f\<^esub> = {(s, s'). f s' \<le> f s}"

lemma less_eq_on_proj[simp]:
  shows "(x, y) \<in> \<^bold>\<le>\<^bsub>f\<^esub> \<longleftrightarrow> f y \<le> f x"
unfolding less_eq_on_proj_def by simp

lemma refl_less_eq_on_proj[iff]:
  fixes f :: "_ \<Rightarrow> _::preorder"
  shows "refl (\<^bold>\<le>\<^bsub>f\<^esub>)"
by (auto intro: refl_onI)

lemma trans_less_eq_on_proj[iff]:
  fixes f :: "_ \<Rightarrow> _::preorder"
  shows "trans (\<^bold>\<le>\<^bsub>f\<^esub>)"
unfolding trans_def by (fastforce elim: order_trans)


subsection\<open> Monotonicity \<close>

lemma mono_inf:
  assumes "mono (f::_\<Rightarrow>_::semilattice_inf)"
  assumes "mono g"
  shows "mono (\<lambda>x. f x \<sqinter> g x)"
using assms by (simp add: monotone_def le_infI1 le_infI2)

declare mono2mono_inf[partial_function_mono]
declare mono2mono_sup[cont_intro, partial_function_mono]
lemmas mono2mono_conj[cont_intro, partial_function_mono] = mono2mono_inf[where 'a=bool, simplified inf_bool_def]

lemma monotone_const:
  assumes "ordb c c"
  shows "monotone orda ordb (\<lambda>_. c)"
using assms by (simp add: monotone_def reflpD)

lemma monotone_domain_empty[cont_intro]:
  shows "monotone (\<lambda>x y. False) ordb f"
unfolding monotone_def by blast

lemma monotone_domain_Id:
  assumes "reflp ordb"
  shows "monotone (\<lambda>x y. (x, y) \<in> Id) ordb f"
using assms by (simp add: monotone_def reflpD)

lemma monotone_domain_UNIV:
  assumes "reflp ordb"
  assumes "antisymp ordb"
  shows "monotone (\<lambda>x y. True) ordb f \<longleftrightarrow> (\<exists>c. f = (\<lambda>_. c))"
using assms by (auto 7 0 simp: monotone_def reflp_def antisymp_def)

lemma antimono_monotone_domain:
  shows "antimono monotone"
unfolding monotone_def by blast

lemma monotone_monotone:
  assumes "monotone orda ordb f"
  assumes "orda' \<le> orda"
  assumes "ordb \<le> ordb'"
  shows "monotone orda' ordb' f"
using assms unfolding monotone_def by blast

lemma monotone_domain_infI:
  assumes "monotone r ordb f"
  shows "monotone (r \<sqinter> s) ordb f"
    and "monotone (s \<sqinter> r) ordb f"
using assms unfolding monotone_def by blast+

lemma monotone_domain_supD:
  assumes "monotone (r \<squnion> s) ordb f"
  shows "monotone r ordb f"
    and "monotone s ordb f"
using assms unfolding monotone_def by blast+

lemma monotone_Id_on_proj:
  assumes "\<And>v. monotone (\<lambda>x y. (x, y) \<in> Id\<^bsub>f\<^esub>) ordb (P v)"
  shows "monotone (\<lambda>x y. (x, y) \<in> Id\<^bsub>f\<^esub>) ordb (\<lambda>s. P (f s) s)"
using assms unfolding monotone_def Id_on_proj_def by simp

lemma monotone_Id_on_proj':
  assumes "reflp ordb"
  shows "monotone (\<lambda>x y. (x, y) \<in> Id\<^bsub>f\<^esub>) ordb (\<lambda>s. P (f s))"
unfolding monotone_def Id_on_proj_def using assms by (simp add: reflpD)

lemma monotone_Inf[cont_intro, partial_function_mono]:
  fixes orda :: "'c relp"
  fixes F :: "'b \<Rightarrow> 'c \<Rightarrow> 'a::complete_lattice"
  assumes "\<And>x. monotone orda (\<le>) (\<lambda>y. F x y)"
  shows "monotone orda (\<le>) (\<lambda>y. \<Sqinter>x\<in>X. F x y)"
using assms by (simp add: INF_mono' monotone_def)

lemma monotone_comp:
  fixes f :: "'b \<Rightarrow> 'c"
  fixes g :: "'a \<Rightarrow> 'b"
  assumes "monotone ordb ordc f"
  assumes "monotone orda ordb g"
  shows "monotone orda ordc (f \<circ> g)"
using assms unfolding monotone_def by simp

lemma monotone_case_sum:
  fixes v :: "'a + 'b"
  fixes left :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
  fixes right :: "'s \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "\<And>v. monotone orda ordb (\<lambda>x. left x v)"
  assumes "\<And>v. monotone orda ordb (\<lambda>x. right x v)"
  shows "monotone orda ordb (\<lambda>x. case_sum (left x) (right x) v)"
using assms unfolding monotone_def by (simp split: sum.splits)

lemma monotone_case_option:
  fixes v :: "'a option"
  fixes none :: "'s \<Rightarrow> bool"
  fixes some :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "monotone orda ordb (\<lambda>s. none s)"
  assumes "\<And>v. monotone orda ordb (\<lambda>s. some s v)"
  shows "monotone orda ordb (\<lambda>s. case_option (none s) (some s) v)"
using assms unfolding monotone_def by (simp split: option.splits)


subsection\<open> Cartesian product of relations \<close>

text\<open>

A set version of \<^const>\<open>rel_prod\<close> and corresponding projections.

\<close>

definition relprod :: "('a \<times> 'b) set \<Rightarrow> ('c \<times> 'd) set \<Rightarrow> (('a \<times> 'c) \<times> ('b \<times> 'd)) set" (infixr \<open>\<times>\<^sub>R\<close> 75) where
  "relprod P Q = {((a, c), (b, d)) |a b c d. (a, b) \<in> P \<and> (c, d) \<in> Q}"

definition relfst :: "(('a \<times> 'c) \<times> ('b \<times> 'd)) set \<Rightarrow> ('a \<times> 'b) set" where
  "relfst R = map_prod fst fst ` R"

definition relsnd :: "(('a \<times> 'c) \<times> ('b \<times> 'd)) set \<Rightarrow> ('c \<times> 'd) set" where
  "relsnd R = map_prod snd snd ` R"

lemma member_relprod[simp]:
  shows "(x, y) \<in> P \<times>\<^sub>R Q \<longleftrightarrow> (fst x, fst y) \<in> P \<and> (snd x, snd y) \<in> Q"
unfolding relprod_def by force

lemma map_prod_image_relprod:
  fixes P :: "('a \<times> 'b) set"
  fixes Q :: "('c \<times> 'd) set"
  fixes f :: "'a \<times> 'c \<Rightarrow> 'e"
  fixes g :: "'b \<times> 'd \<Rightarrow> 'f"
  shows "map_prod f g ` (P \<times>\<^sub>R Q) = {(f (a, c), g (b, d)) |a b c d. (a, b) \<in> P \<and> (c, d) \<in> Q}"
unfolding map_prod_def relprod_def image_def by auto

lemma map_prod_vimage_relprod:
  fixes P :: "('a \<times> 'b) set"
  fixes Q :: "('c \<times> 'd) set"
  fixes f :: "'e \<Rightarrow> 'a \<times> 'c"
  fixes g :: "'f \<Rightarrow> 'b \<times> 'd"
  shows "map_prod f g -` (P \<times>\<^sub>R Q) = {(x, y). (fst (f x), fst (g y)) \<in> P \<and> (snd (f x), snd (g y)) \<in> Q}"
by fastforce

lemma relprod_mono:
  assumes "P \<subseteq> P'"
  assumes "Q \<subseteq> Q'"
  shows "P \<times>\<^sub>R Q \<subseteq> P' \<times>\<^sub>R Q'"
unfolding relprod_def using assms by blast

lemma strengthen_relprod[strg]:
  assumes "st_ord F P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (P \<times>\<^sub>R Q) (P' \<times>\<^sub>R Q')"
using assms by (cases F) auto

lemma mono_relprod:
  shows "mono (\<lambda>x. relprod x Q)"
    and "mono (\<lambda>x. relprod P x)"
unfolding relprod_def by (rule monoI; blast)+

lemma mono_relfst:
  shows "mono relfst"
unfolding relfst_def by (rule monoI) blast

lemma mono_relsnd:
  shows "mono relsnd"
unfolding relsnd_def by (rule monoI) blast

lemma relfst_subseteq_conv[simp]:
  shows "relfst X \<subseteq> Y \<longleftrightarrow> X \<subseteq> Y \<times>\<^sub>R UNIV"
unfolding relfst_def by fastforce

lemma relsnd_subseteq_conv[simp]:
  shows "relsnd X \<subseteq> Y \<longleftrightarrow> X \<subseteq> UNIV \<times>\<^sub>R Y"
unfolding relsnd_def by fastforce

lemma relprod_Id[simp]:
  shows "Id \<times>\<^sub>R Id = Id"
unfolding relprod_def by auto

lemma relprod_UNIV[simp]:
  shows "UNIV \<times>\<^sub>R UNIV = UNIV"
unfolding relprod_def by auto

lemma relprod_inter_Id:
  shows "Id \<inter> UNIV \<times>\<^sub>R Id = Id"
    and "UNIV \<times>\<^sub>R Id \<sqinter> Id = Id"
by auto

lemma reflcl_relprod:
  shows "(r \<times>\<^sub>R s)\<^sup>= \<subseteq> r\<^sup>= \<times>\<^sub>R s\<^sup>="
unfolding relprod_def by auto

lemma inv_image_fst:
  shows "inv_image r fst = r \<times>\<^sub>R UNIV"
unfolding relprod_def inv_image_def by fastforce

lemma inv_image_snd:
  shows "inv_image r snd = UNIV \<times>\<^sub>R r"
unfolding relprod_def inv_image_def by fastforce

lemma relprod_inter:
  shows "r \<times>\<^sub>R s \<inter> r' \<times>\<^sub>R s' = (r \<inter> r') \<times>\<^sub>R (s \<inter> s')"
unfolding relprod_def by blast

lemma relprod_union_subseteq:
  shows "r \<times>\<^sub>R s \<union> r' \<times>\<^sub>R s' \<subseteq> (r \<union> r') \<times>\<^sub>R (s \<union> s')"
unfolding relprod_def by blast

lemma relprod_empty[simp]:
  shows "r \<times>\<^sub>R {} = {}"
    and "{} \<times>\<^sub>R r = {}"
unfolding relprod_def by simp_all

lemma relprod_empty_conv:
  shows "r \<times>\<^sub>R s = {} \<longleftrightarrow> r = {} \<or> s = {}"
unfolding relprod_def by fast

lemma relfst_empty[simp]:
  shows "relfst {} = {}"
unfolding relfst_def by simp

lemma relsnd_empty[simp]:
  shows "relsnd {} = {}"
unfolding relsnd_def by simp

lemma relprod_relfst_relsnd_subseteq:
  shows "P \<subseteq> relfst P \<times>\<^sub>R relsnd P"
unfolding relfst_def relsnd_def relprod_def by force

lemma relfst_relprod:
  assumes "Q \<noteq> {}"
  shows "relfst (P \<times>\<^sub>R Q) = P"
unfolding relfst_def relprod_def using assms by force

lemma relsnd_relprod:
  assumes "P \<noteq> {}"
  shows "relsnd (P \<times>\<^sub>R Q) = Q"
unfolding relsnd_def relprod_def using assms by force

lemma relfst_Id[simp]:
  shows "relfst Id = Id"
unfolding relfst_def by force

lemma relsnd_Id[simp]:
  shows "relsnd Id = Id"
unfolding relsnd_def by force

lemma relfst_UNIV[simp]:
  shows "relfst UNIV = UNIV"
unfolding relfst_def by (rule map_prod_surj[OF range_fst range_fst])

lemma relsnd_UNIV[simp]:
  shows "relsnd UNIV = UNIV"
unfolding relsnd_def by (rule map_prod_surj[OF range_snd range_snd])

lemma relfst_union:
  shows "relfst (R \<union> S) = relfst R \<union> relfst S"
unfolding relfst_def by blast

lemma relsnd_union:
  shows "relsnd (R \<union> S) = relsnd R \<union> relsnd S"
unfolding relsnd_def by blast

lemma relprod_unionL:
  shows "(P \<union> R) \<times>\<^sub>R S = P \<times>\<^sub>R S \<union> R \<times>\<^sub>R S"
unfolding relprod_def by blast

lemma relprod_unionR:
  shows "P \<times>\<^sub>R (R \<union> S) = P \<times>\<^sub>R R \<union> P \<times>\<^sub>R S"
unfolding relprod_def by blast

lemma Id_on_proj_fst:
  shows "Id\<^bsub>fst\<^esub> = Id \<times>\<^sub>R UNIV"
unfolding Id_on_proj_def by force

lemma Id_on_proj_snd:
  shows "Id\<^bsub>snd\<^esub> = UNIV \<times>\<^sub>R Id"
unfolding Id_on_proj_def by force

lemma refl_on_relprodI:
  assumes "refl_on A r"
  assumes "refl_on B s"
  shows "refl_on (A \<times> B) (r \<times>\<^sub>R s)"
using assms unfolding relprod_def refl_on_def by auto

lemma refl_relprod_conv:
  shows "refl (r \<times>\<^sub>R s) \<longleftrightarrow> refl r \<and> refl s"
unfolding relprod_def refl_on_def by simp

lemma trans_relprod[intro]:
  assumes "trans r"
  assumes "trans s"
  shows "trans (r \<times>\<^sub>R s)"
using assms unfolding relprod_def trans_def by fast

lemma map_prod_snd_snd_image_Id:
  shows "map_prod snd snd ` Id = Id"
by (metis relsnd_Id relsnd_def)

lemma map_prod_fst_fst_vimage:
  shows "map_prod fst fst -` X = X \<times>\<^sub>R UNIV"
by fastforce

lemma map_prod_snd_snd_vimage:
  shows "map_prod snd snd -` X = UNIV \<times>\<^sub>R X"
by fastforce

lemma map_prod_map_prod_vimage_Id:
  shows "map_prod (map_prod f g) (map_prod f g) -` Id = map_prod f f -` Id \<times>\<^sub>R map_prod g g -` Id"
by fastforce

lemma Id_le_relprod_conv:
  shows "Id \<subseteq> r \<times>\<^sub>R s \<longleftrightarrow> Id \<subseteq> r \<and> Id \<subseteq> s"
by fastforce


subsection\<open> More transfer \<close>

context
  includes lifting_syntax
begin

lemma antimono_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  assumes [transfer_rule]: "(A ===> A ===> (=)) (\<le>) (\<le>)"
  assumes [transfer_rule]: "(B ===> B ===> (=)) (\<le>) (\<le>)"
  shows "((A ===> B) ===> (=)) antimono antimono"
unfolding antimono_def by transfer_prover

end


paragraph\<open> More \<^theory>\<open>Coinductive.Coinductive_List\<close> and \<^theory>\<open>Coinductive.TLList\<close> \<close>

lemmas tset_tmap = TLList.tllist.set_map

lemma not_is_TNil:
  shows "\<not> is_TNil y \<longleftrightarrow> (\<exists>x xs. y = TCons x xs)"
by (cases y) simp_all

lemma lmap_repeat:
  shows "lmap f (repeat x) = repeat (f x)"
by coinduction simp

lemma tlength_0_conv:
  shows "tlength xs = 0 \<longleftrightarrow> (\<exists>b. xs = TNil b)"
by (cases xs) simp_all

lemma tfinite_tlength_conv:
  shows "tfinite xs \<longleftrightarrow> (\<exists>n. tlength xs = enat n)"
by (simp add: lfinite_conv_llength_enat)

lemma tdropn_eq_TNil_conv:
  shows "tdropn i xs = TNil b \<longleftrightarrow> b = terminal xs \<and> tlength xs \<le> enat i" (is ?thesis1)
    and "TNil b = tdropn i xs \<longleftrightarrow> b = terminal xs \<and> tlength xs \<le> enat i" (is ?thesis2)
proof -
  show ?thesis1
  proof(induct i arbitrary: xs)
    case (0 xs) show ?case
      by (cases xs) (auto simp: enat_0)
  next
    case (Suc i xs) then show ?case
      by (cases xs) (auto simp flip: eSuc_enat)
  qed
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma tdropn_eq_TCons_tlength_conv:
  shows "(\<exists>y ys. tdropn i xs = TCons y ys) \<longleftrightarrow> (enat i < tlength xs)"
by (metis leI tdropn_Suc_conv_tdropn tdropn_eq_TNil_conv(1) tllist.distinct(1))

lemma tdropn_eq_TCons_tlengthD:
  assumes "tdropn i xs = TCons y ys"
  shows "enat i < tlength xs"
using assms by (simp flip: tdropn_eq_TCons_tlength_conv)

lemma tdropn_tlength:
  assumes "tlength xs \<le> enat i"
  shows "tdropn i xs = TNil (terminal xs)"
by (simp add: assms tdropn_eq_TNil_conv)

lemma terminal_tdropn[simp]:
  shows "terminal (tdropn i xs) = terminal xs"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case by (cases xs) simp_all
qed simp

lemma in_tset_tdropnD:
  assumes "x \<in> tset (tdropn i xs)"
  shows "x \<in> tset xs"
using assms
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case by (cases xs) simp_all
qed simp


paragraph\<open> New constants \<close>

definition trepeat :: "'a \<Rightarrow> ('a, 'b) tllist" where
  "trepeat x = tllist_of_llist undefined (Coinductive_List.repeat x)"

primrec treplicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) tllist" where
  "treplicate 0 x v = TNil v"
| "treplicate (Suc i) x v = TCons x (treplicate i x v)"

primrec tshift :: "'a list \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist" where
  "tshift [] ys = ys"
| "tshift (x # xs) ys = TCons x (tshift xs ys)"

primrec ttake :: "nat \<Rightarrow> ('a, 'b) tllist \<Rightarrow> 'a list \<times> 'b option" where \<comment>\<open> finite taking only in contrast to \<^const>\<open>ltake\<close> \<close>
  "ttake 0 xs = ([], None)"
| "ttake (Suc i) xs = (case xs of TNil b \<Rightarrow> ([], Some b) | TCons x xs \<Rightarrow> apfst ((#) x) (ttake i xs))"

definition tshift2 :: "'a list \<times> 'b option \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist" where \<comment>\<open> the corresponding concatenation operation for \<^const>\<open>ttake\<close> \<close>
  "tshift2 xsv ys = tshift (fst xsv) (case_option ys TNil (snd xsv))"

lemma trepeat_unfold:
  shows "trepeat x = TCons x (trepeat x)"
using iterates by (fastforce simp add: trepeat_def simp flip: tllist_of_llist_LCons)

lemma not_finite_trepeat[iff]:
  shows "\<not>tfinite (trepeat x)"
by (simp add: trepeat_def)

lemma trepeat_simps[simp]:
  shows "thd (trepeat x) = x"
    and "ttl (trepeat x) = trepeat x"
    and "tset (trepeat x) = {x}"
    and "trepeat x \<noteq> TNil b"
    and "TNil b \<noteq> trepeat x"
by (simp_all add: trepeat_def lnull_iterates[unfolded lnull_def])

lemma case_tllist_trepeat:
  shows "case_tllist tnil tcons (trepeat x) = tcons x (trepeat x)"
by (subst trepeat_unfold) simp

lemma trepeat_eq_TCons_conv:
  shows "trepeat x = TCons y ys \<longleftrightarrow> x = y \<and> ys = trepeat x"
    and "TCons y ys = trepeat x \<longleftrightarrow> x = y \<and> ys = trepeat x"
by (subst trepeat_unfold; fast)+

lemma tmap_trepeat:
  shows "tmap sf vf (trepeat s) = trepeat (sf s)"
by (simp add: trepeat_def lmap_repeat tmap_tllist_of_llist)

lemma tdropn_trepeat:
  shows "tdropn i (trepeat x) = trepeat x"
proof(induct i)
  case (Suc i) then show ?case by (subst trepeat_unfold) simp
qed simp

lemma ttake_trepeat:
  shows "ttake i (trepeat x) = (List.replicate i x, None)"
by (induct i) (simp_all add: trepeat_eq_TCons_conv split: tllist.split)

lemma terminal_treplicate:
  shows "terminal (treplicate i x v) = v"
by (induct i) simp_all

lemma finite_treplicate[iff]:
  shows "tfinite (treplicate i x v)"
by (induct i) simp_all

lemma tset_treplicate:
  shows "tset (treplicate i x v) = (case i of 0 \<Rightarrow> {} | Suc _ \<Rightarrow> {x})"
by (induct i) (simp_all split: nat.split)

lemma tlength_treplicate:
  shows "tlength (treplicate i x v) = enat i"
by (induct i) (simp_all add: enat_0 eSuc_enat)

lemma tmap_treplicate:
  shows "tmap f g (treplicate i x v) = treplicate i (f x) (g v)"
by (induct i) simp_all

lemma tdropn_treplicate:
  shows "tdropn i (treplicate j x v) = treplicate (j - i) x v"
proof(induct j arbitrary: i)
  case (Suc j i) then show ?case by (cases i) simp_all
qed simp

lemma ttake_treplicate:
  shows "ttake i (treplicate j x v) = (replicate (min i j) x, if i \<le> j then None else Some v)"
proof(induct j arbitrary: i)
  case (0 i) then show ?case by (cases i) simp_all
next
  case (Suc j i) then show ?case by (cases i) simp_all
qed

lemmas treplicate_simps[simp] =
  terminal_treplicate
  tset_treplicate
  tlength_treplicate
  tmap_treplicate
  tdropn_treplicate
  ttake_treplicate

lemma tshift_sel[simp]:
  shows "thd (tshift xs ys) = (if List.null xs then thd ys else hd xs)"
    and "ttl (tshift xs ys) = (if List.null xs then ttl ys else tshift (tl xs) ys)"
by (case_tac [!] xs) simp_all

lemma tfinite_tshift[simp]:
  shows "tfinite (tshift xs ys) \<longleftrightarrow> tfinite ys"
by (induct xs) simp_all

lemma tlength_tshift:
  shows "tlength (tshift xs ys) = enat (length xs) + tlength ys"
by (induct xs) (simp_all add: enat_0 eSuc_plus flip: eSuc_enat)

lemma tmap_tshift:
  shows "tmap f g (tshift xs ys) = tshift (map f xs) (tmap f g ys)"
by (induct xs) simp_all

lemma tshift_append:
  shows "tshift (xs @ ys) zs = tshift xs (tshift ys zs)"
by (induct xs) simp_all

lemma tshift_same_conv[simp]:
  shows "tshift xs ys = tshift xs zs \<longleftrightarrow> ys = zs"
by (induct xs) simp_all

lemma tset_tshift:
  shows "tset (tshift xs ys) = set xs \<union> tset ys"
by (induct xs) simp_all

lemma terminal_tshift:
  shows "terminal (tshift xs ys) = terminal ys"
by (induct xs) simp_all

lemma tdropn_tshift:
  shows "tdropn i (tshift xs ys) = tshift (drop i xs) (tdropn (i - length xs) ys)"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs) simp_all
qed simp

lemma tshift_drop:
  shows "tshift (drop i xs) ys = tdropn (min i (length xs)) (tshift xs ys)"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs) simp_all
qed simp

lemma tshift_fst_ttake_tdropn_id[simp]:
  shows "tshift (fst (ttake i xs)) (tdropn i xs) = xs"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs) simp_all
qed simp

lemma tshift_eq_TNil_conv:
  shows "tshift ys zs = TNil v \<longleftrightarrow> ys = [] \<and> zs = TNil v" (is ?thesis1)
    and "TNil v = tshift ys zs \<longleftrightarrow> ys = [] \<and> zs = TNil v" (is ?thesis2)
proof -
  show ?thesis1 by (cases ys) simp_all
  then show ?thesis2 by (rule eq_commute_conv)
qed

lemma tshift_eq_TCons_conv:
  shows "tshift ys zs = TCons x xs \<longleftrightarrow> (ys = [] \<and> zs = TCons x xs \<or> (\<exists>ys'. ys = x # ys' \<and> tshift ys' zs = xs))" (is ?thesis1)
    and "TCons x xs = tshift ys zs \<longleftrightarrow> (ys = [] \<and> zs = TCons x xs \<or> (\<exists>ys'. ys = x # ys' \<and> tshift ys' zs = xs))" (is ?thesis2)
proof -
   show ?thesis1 by (cases ys) simp_all
  then show ?thesis2 by (rule eq_commute_conv)
qed

lemma tmap_eq_tshift_conv:
  shows "tmap f g xs = tshift ys zs \<longleftrightarrow> (\<exists>us vs. xs = tshift us vs \<and> ys = map f us \<and> zs = tmap f g vs)" (is ?thesis1)
    and "tshift ys zs = tmap f g xs \<longleftrightarrow> (\<exists>us vs. xs = tshift us vs \<and> ys = map f us \<and> zs = tmap f g vs)" (is ?thesis2)
proof -
  show ?thesis1
  proof(induct ys arbitrary: xs zs)
    case (Cons y ys xs zs) then show ?case
      by (cases xs) (auto simp: Cons_eq_map_conv tshift_eq_TNil_conv tshift_eq_TCons_conv)
  qed auto
  then show ?thesis2 by (rule eq_commute_conv)
qed

lemma ttake_tshift:
  shows "ttake i (tshift xs ys)
      = (if i \<le> length xs then (take i xs, None) else apfst ((@) xs) (ttake (i - length xs) ys))"
proof(induct i arbitrary: xs)
  case (Suc i) then show ?case
    by (cases xs; cases ys) (simp_all add: apfst_compose)
qed simp

lemma tshift_eq_trepeat_conv:
  shows "tshift xs ys = trepeat x \<longleftrightarrow> set xs \<subseteq> {x} \<and> ys = trepeat x" (is ?thesis1)
    and "trepeat x = tshift xs ys \<longleftrightarrow> set xs \<subseteq> {x} \<and> ys = trepeat x" (is ?thesis2)
proof -
  show ?thesis1 by (induct xs arbitrary: ys) (auto simp: trepeat_eq_TCons_conv)
  then show ?thesis2 by (rule eq_commute_conv)
qed

lemma tshift_eq_tshift_conv2:
  shows "tshift xs ys = tshift zs ts
     \<longleftrightarrow> (\<exists>us. xs = zs @ us \<and> tshift us ys = ts \<or> xs @ us = zs \<and> ys = tshift us ts)"
proof(induct xs arbitrary: ys zs ts)
  case (Cons x xs) show ?case
    by (auto simp: tshift_append tshift_eq_TCons_conv Cons_eq_append_conv eq_commute_conv[OF Cons])
qed auto

lemma tshift2_simps[simp]:
  shows "tshift2 (xs, Some v) ys = tshift xs (TNil v)"
    and "tshift2 (xs, None) ys = tshift xs ys"
    and "tshift2 (x # xs, w) ys = TCons x (tshift2 (xs, w) ys)"
    and "tshift2 (apfst ((#) x) zs) ys = TCons x (tshift2 zs ys)"
by (simp_all add: tshift2_def)

lemma tlength_tshift2:
  shows "tlength (tshift2 xsv ys)
       = enat (length (fst xsv)) + (case_option (tlength ys) (\<lambda>_. 0) (snd xsv))"
by (simp add: tshift2_def tlength_tshift split: option.split)

lemma tfinite_tshift2[simp]:
  shows "tfinite (tshift2 xsv ys) \<longleftrightarrow> (snd xsv = None \<longrightarrow> tfinite ys)"
by (simp add: tshift2_def split: option.split)

lemma tdropn_tshift2:
  shows "tdropn i (tshift2 xsv ys) = tshift2 (apfst (drop i) xsv) (tdropn (i - length (fst xsv)) ys)"
by (simp add: tshift2_def tdropn_tshift split: option.split)

lemma ttake_TNil:
  shows "ttake i (TNil b) = ([], case i of 0 \<Rightarrow> None | Suc _ \<Rightarrow> Some b)"
by (cases i) simp_all

lemma ttake_tmap:
  shows "ttake i (tmap f g xs) = map_prod (map f) (map_option g) (ttake i xs)"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs) (simp_all add: comp_def)
qed simp

lemma in_set_ttakeD:
  assumes "x \<in> set (fst (ttake i xs))"
  shows "x \<in> tset xs"
using assms
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs) auto
qed simp

lemma length_ttake:
  shows "length (fst (ttake i xs)) = min i (case tlength xs of \<infinity> \<Rightarrow> i | enat j \<Rightarrow> j)"
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs; clarsimp split: enat.split simp: eSuc_enat)
qed (simp split: enat.split)

lemma ttake_eq_None_conv:
  shows "snd (ttake i xs) = None \<longleftrightarrow> enat i \<le> tlength xs" (is ?thesis1)
    and "None = snd (ttake i xs) \<longleftrightarrow> enat i \<le> tlength xs" (is ?thesis2)
proof -
  show ?thesis1
  proof(induct i arbitrary: xs)
    case (Suc i xs) then show ?case
      by (cases xs) (simp_all add: Suc_ile_eq enat_0_iff)
  qed (simp add: enat_0)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma ttake_eq_Some_conv:
  shows "snd (ttake i xs) = Some b \<longleftrightarrow> b = terminal xs \<and> tlength xs < enat i" (is ?thesis1)
    and "Some b = snd (ttake i xs) \<longleftrightarrow> b = terminal xs \<and> tlength xs < enat i" (is ?thesis2)
proof -
  show ?thesis1
  proof(induct i arbitrary: xs)
    case (Suc i xs) then show ?case
      by (cases xs) (auto simp flip: eSuc_enat)
  qed (simp add: enat_0)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma ttake_eq_Nil_conv:
  shows "fst (ttake i xs) = [] \<longleftrightarrow> i = 0 \<or> is_TNil xs" (is ?thesis1)
    and "[] = fst (ttake i xs) \<longleftrightarrow> i = 0 \<or> is_TNil xs" (is ?thesis2)
proof -
  show ?thesis1
  proof(induct i arbitrary: xs)
    case (Suc i xs) then show ?case
      by (cases xs) simp_all
  qed simp
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma take_fst_ttake:
  shows "take i (fst (ttake j xs)) = fst (ttake (min i j) xs)"
proof(induct j arbitrary: xs i)
  case (Suc j xs i) then show ?case
    by (cases xs; cases i) simp_all
qed simp

lemma tshift2_ttake_shorter:
  assumes "tlength xs < enat i"
  shows "tshift2 (ttake i xs) ys = xs"
using assms
proof(induct i arbitrary: xs)
  case (Suc i xs) then show ?case
    by (cases xs) (simp_all flip: eSuc_enat)
qed (simp add: enat_0)

lemma tshift2_ttake_tdropn_id:
  shows "tshift2 (ttake i xs) (tdropn i xs) = xs"
by (simp add: tshift2_def ttake_eq_Some_conv flip: tdropn_tlength[where i=i] split: option.split)

lemma ttake_tshift2:
  shows "ttake i (tshift2 xsv ys)
      = (if i \<le> length (fst xsv) then (take i (fst xsv), None) else apfst ((@) (fst xsv)) (ttake (i - length (fst xsv)) (case_option ys TNil (snd xsv))))"
by (simp add: tshift2_def ttake_tshift)

lemma tfinite_ttake_all:
  assumes "tfinite xs"
  obtains j where "tshift2 (ttake j xs) ys = xs"
apply atomize_elim
using assms
proof(induct rule: tfinite_induct)
  case (TCons x xs)
  from TCons(2) obtain j where "tshift2 (ttake j xs) ys = xs" ..
  then show ?case by (simp add: tshift2_def exI[where x="Suc j"])
qed (simp add: exI[where x=1])

lemma fst_ttake_flat:
  assumes "tlength xs \<le> enat i"
  assumes "i \<le> j"
  shows "fst (ttake i xs) = fst (ttake j xs)"
by (metis assms enat.simps(4) enat_ile enat_ord_simps(1) length_ttake min.absorb1 min.absorb2 take_all_iff take_fst_ttake)

lemma snd_ttake_flat:
  assumes "tlength xs < enat i"
  assumes "i \<le> j"
  shows "snd (ttake i xs) = snd (ttake j xs)"
by (metis assms order.trans enat_ord_simps(1) option.collapse ttake_eq_None_conv(2) ttake_eq_Some_conv(2))

lemma ttake_flat:
  assumes "tlength xs < enat i"
  assumes "i \<le> j"
  shows "ttake i xs = ttake j xs"
by (simp add: assms fst_ttake_flat snd_ttake_flat order_less_imp_le prod.expand)

lemma ttake_add:
  shows "ttake (i + j) xs
      = (let xsv = ttake i xs in
         case snd xsv of None \<Rightarrow> apfst ((@) (fst xsv)) (ttake j (tdropn i xs)) | Some _ \<Rightarrow> xsv)"
by (induct i arbitrary: xs) (auto simp: Let_def prod.expand split: option.splits tllist.splits)

lemma nth_ttake:
  assumes "i <j"
  assumes "enat i < tlength xs"
  shows "fst (ttake j xs) ! i = tnth xs i"
using assms
proof(induct j arbitrary: xs i)
  case (Suc j xs i) then show ?case
    by (cases i) (auto simp: Suc_ile_eq split: tllist.split)
qed simp

lemma ttake_eq_imp_eq:
  assumes "\<And>i. ttake i xs = ttake i ys"
  shows "xs = ys"
using assms
proof(coinduction arbitrary: xs ys)
  case (Eq_tllist xs ys) show ?case
  proof(intro conjI impI allI exI)
    from spec[OF Eq_tllist, where x=1] show "is_TNil xs \<longleftrightarrow> is_TNil ys"
      by (simp split: tllist.split_asm)
    from spec[OF Eq_tllist, where x=1] show "terminal xs = terminal ys" if "is_TNil xs" and "is_TNil ys"
      using that by (simp split: tllist.split_asm)
    from spec[OF Eq_tllist, where x=1] show "thd xs = thd ys" if "\<not>is_TNil xs" and "\<not>is_TNil ys"
      using that by (simp split: tllist.split_asm)
    show "ttake i (ttl xs) = ttake i (ttl ys)" if "\<not>is_TNil xs" and "\<not>is_TNil ys" for i
      using spec[OF Eq_tllist, where x="Suc i"] that
      by (simp add: apfst_def map_prod_def split_def prod.expand split: tllist.split_asm)
  qed simp_all
qed

end
