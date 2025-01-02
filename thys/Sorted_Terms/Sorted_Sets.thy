theory Sorted_Sets
  imports 
    Main 
    "HOL-Library.FuncSet" 
    "HOL-Library.Monad_Syntax"
    Complete_Non_Orders.Binary_Relations
begin

section \<open>Auxiliary Lemmas\<close>

(* corr. all_set_conv_all_nth *)
lemma ex_set_conv_ex_nth:
  "(\<exists>x \<in> set xs. P x) = (\<exists>i. i < length xs \<and> P (xs ! i))"
  by (auto simp add: set_conv_nth)

lemma Ball_Pair_conv: "(\<forall>(x,y)\<in>R. P x y) \<longleftrightarrow> (\<forall>x y. (x,y) \<in> R \<longrightarrow> P x y)" by auto

lemma Some_eq_bind_conv: "(Some x = f \<bind> g) = (\<exists>y. f = Some y \<and> g y = Some x)"
  by (fold bind_eq_Some_conv, auto)

lemma length_le_nth_append: "length xs \<le> n \<Longrightarrow> (xs@ys)!n = ys!(n-length xs)"
  by (simp add: nth_append)

lemma list_all2_same_left:
 "\<forall>a' \<in> set as. a' = a \<Longrightarrow> list_all2 r as bs \<longleftrightarrow> length as = length bs \<and> (\<forall>b \<in> set bs. r a b)"
  by (auto simp: list_all2_conv_all_nth all_set_conv_all_nth)

lemma list_all2_same_leftI:
 "\<forall>a' \<in> set as. a' = a \<Longrightarrow> length as = length bs \<Longrightarrow> \<forall>b \<in> set bs. r a b \<Longrightarrow> list_all2 r as bs"
  by (auto simp: list_all2_same_left)

lemma list_all2_same_right:
 "\<forall>b' \<in> set bs. b' = b \<Longrightarrow> list_all2 r as bs \<longleftrightarrow> length as = length bs \<and> (\<forall>a \<in> set as. r a b)"
  by (auto simp: list_all2_conv_all_nth all_set_conv_all_nth)

lemma list_all2_same_rightI:
 "\<forall>b' \<in> set bs. b' = b \<Longrightarrow> length as = length bs \<Longrightarrow> \<forall>a \<in> set as. r a b \<Longrightarrow> list_all2 r as bs"
  by (auto simp: list_all2_same_right)

lemma list_all2_all_all:
 "\<forall>a \<in> set as. \<forall>b \<in> set bs. r a b \<Longrightarrow> list_all2 r as bs \<longleftrightarrow> length as = length bs"
  by (auto simp: list_all2_conv_all_nth all_set_conv_all_nth)

lemma list_all2_indep1:
  "list_all2 (\<lambda>a b. P b) as bs \<longleftrightarrow> length as = length bs \<and> (\<forall>b \<in> set bs. P b)"
  by (auto simp: list_all2_conv_all_nth all_set_conv_all_nth)

lemma list_all2_indep2:
  "list_all2 (\<lambda>a b. P a) as bs \<longleftrightarrow> length as = length bs \<and> (\<forall>a \<in> set as. P a)"
  by (auto simp: list_all2_conv_all_nth all_set_conv_all_nth)

lemma list_all2_replicate[simp]:
  "list_all2 r (replicate n x) ys \<longleftrightarrow> length ys = n \<and> (\<forall>y \<in> set ys. r x y)"
  "list_all2 r xs (replicate n y) \<longleftrightarrow> length xs = n \<and> (\<forall>x \<in> set xs. r x y)"
  by (auto simp: list_all2_conv_all_nth all_set_conv_all_nth)

lemma list_all2_choice_nth: assumes "\<forall>i < length xs. \<exists>y. r (xs!i) y" shows "\<exists>ys. list_all2 r xs ys"
proof-
  from assms have "\<forall>i \<in> {0..<length xs}. \<exists>y. r (xs!i) y" by auto
  from finite_set_choice[OF _ this]
  obtain f where "\<forall>i < length xs. r (xs ! i) (f i)" by (auto simp: Ball_def)
  then have "list_all2 r xs (map f [0..<length xs])" by (auto simp: list_all2_conv_all_nth)
  then show ?thesis by auto
qed

lemma list_all2_choice: "\<forall>x \<in> set xs. \<exists>y. r x y \<Longrightarrow> \<exists>ys. list_all2 r xs ys"
  using list_all2_choice_nth by (auto simp: all_set_conv_all_nth)

lemma list_all2_concat:
  "list_all2 (list_all2 r) ass bss \<Longrightarrow> list_all2 r (concat ass) (concat bss)"
  by (induct rule:list_all2_induct, auto intro!: list_all2_appendI)

lemma those_eq_None[simp]: "those as = None \<longleftrightarrow> None \<in> set as" by (induct as, auto split:option.split)

lemma those_eq_Some[simp]: "those xos = Some xs \<longleftrightarrow> xos = map Some xs"
  by (induct xos arbitrary:xs, auto split:option.split_asm)

lemma those_map_Some[simp]: "those (map Some xs) = Some xs" by simp

lemma those_append:
  "those (as @ bs) = do {xs \<leftarrow> those as; ys \<leftarrow> those bs; Some (xs@ys)}"
  by (auto simp: those_eq_None split: bind_split)

lemma those_Cons:
  "those (a#as) = do {x \<leftarrow> a; xs \<leftarrow> those as; Some (x # xs)}"
  by (auto split: option.split bind_split)

lemma map_singleton_o[simp]: "(\<lambda>x. [x]) \<circ> f = (\<lambda>x. [f x])" by auto

lemmas list_3_cases = remdups_adj.cases

lemma in_set_updateD: "x \<in> set (xs[n := y]) \<Longrightarrow> x \<in> set xs \<or> x = y"
  by (auto dest: subsetD[OF set_update_subset_insert])

lemma map_nth': "length xs = n \<Longrightarrow> map (nth xs) [0..<n] = xs"
  using map_nth by auto

lemma product_lists_map_map: "product_lists (map (map f) xss) = map (map f) (product_lists xss)"
  by (induct xss, auto simp: Cons o_def map_concat)

lemma (in monoid_add) sum_list_concat: "sum_list (concat xs) = sum_list (map sum_list xs)" 
  by (induct xs, auto)

context semiring_1 begin

lemma prod_list_map_sum_list_distrib:
  shows "prod_list (map sum_list xss) = sum_list (map prod_list (product_lists xss))"
  by (induct xss, simp_all add: map_concat o_def sum_list_concat sum_list_const_mult sum_list_mult_const)

lemma prod_list_sum_list_distrib:
  "(\<Prod>xs \<leftarrow> xss. \<Sum>x \<leftarrow> xs. f x) = (\<Sum>xs \<leftarrow> product_lists xss. \<Prod>x\<leftarrow>xs. f x)"
  using prod_list_map_sum_list_distrib[of "map (map f) xss"]
  by (simp add: o_def product_lists_map_map)

end

lemma ball_set_bex_set_distrib:
  "(\<forall>xs\<in>set xss. \<exists>x\<in>set xs. f x) \<longleftrightarrow> (\<exists>xs\<in>set (product_lists xss). \<forall>x\<in>set xs. f x)"
  by (induct xss, auto)

lemma bex_set_ball_set_distrib:
  "(\<exists>xs\<in>set xss. \<forall>x\<in>set xs. f x) \<longleftrightarrow> (\<forall>xs\<in>set (product_lists xss). \<exists>x\<in>set xs. f x)"
  by (induct xss, auto)

declare upt_Suc[simp del]

lemma map_nth_Cons: "map (nth (x#xs)) [0..<n] = (case n of 0 \<Rightarrow> [] | Suc n \<Rightarrow> x # map (nth xs) [0..<n])"
  by (auto simp:map_upt_Suc split: nat.split)

lemma upt_0_Suc_Cons: "[0..<Suc i] = 0 # map Suc [0..<i]"
  using map_upt_Suc[of id] by simp

lemma upt_map_add: "i \<le> j \<Longrightarrow> [i..<j] = map (\<lambda>k. k + i) [0..<j-i]"
  by (simp add: map_add_upt)

lemma map_nth_append:
  "map (nth (xs @ ys)) [0..<n] =
  (if n < length xs then map (nth xs) [0..<n] else xs @ map (nth ys) [0..<n-length xs])"
  by (induct xs arbitrary: n, auto simp: map_nth_Cons split: nat.split)

lemma all_dom: "(\<forall>x \<in> dom f. P x) \<longleftrightarrow> (\<forall>x y. f x = Some y \<longrightarrow> P x)" by auto

lemma trancl_Collect: "{(x,y). r x y}\<^sup>+ = {(x,y). tranclp r x y}"
  by (simp add: tranclp_unfold)

lemma restrict_submap[intro!]: "A |` S \<subseteq>\<^sub>m A"
  by (auto simp: restrict_map_def map_le_def domIff)

lemma restrict_map_mono_left: "A \<subseteq>\<^sub>m A' \<Longrightarrow> A |` S \<subseteq>\<^sub>m A' |` S"
  and restrict_map_mono_right: "S \<subseteq> S' \<Longrightarrow> A |` S \<subseteq>\<^sub>m A |` S'"
  by (auto simp: map_le_def)


section \<open>Sorted Sets and Maps\<close>

declare domIff[iff del]

text \<open>We view sorted sets just as partial maps from elements to their sorts.
We just introduce the following notation:\<close>

definition hastype (\<open>((_) :/ (_) in/ (_))\<close> [50,61,51]50)
  where "a : \<sigma> in A \<equiv> A a = Some \<sigma>"

abbreviation "all_hastype \<sigma> A P \<equiv> \<forall>a. a : \<sigma> in A \<longrightarrow> P a"
abbreviation "ex_hastype \<sigma> A P \<equiv> \<exists>a. a : \<sigma> in A \<and> P a"

syntax
  all_hastype :: "'pttrn \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (\<open>\<forall>_ :/ _ in/ _./ _\<close> [50,51,51,10]10)
  ex_hastype :: "'pttrn \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (\<open>\<exists>_ :/ _ in/ _./ _\<close> [50,51,51,10]10)

syntax_consts
  all_hastype \<rightleftharpoons> all_hastype and
  ex_hastype \<rightleftharpoons> ex_hastype

translations
  "\<forall>a : \<sigma> in A. e" \<rightleftharpoons> "CONST all_hastype \<sigma> A (\<lambda>a. e)"
  "\<exists>a : \<sigma> in A. e" \<rightleftharpoons> "CONST ex_hastype \<sigma> A (\<lambda>a. e)"

lemmas hastypeI = hastype_def[unfolded atomize_eq, THEN iffD2]
lemmas hastypeD[dest] = hastype_def[unfolded atomize_eq, THEN iffD1]
lemmas eq_Some_iff_hastype = hastype_def[symmetric]

lemma has_same_type: assumes "a : \<sigma> in A" shows "a : \<sigma>' in A \<longleftrightarrow> \<sigma>' = \<sigma>"
  using assms by (unfold hastype_def, auto)

lemma sset_eqI: assumes "(\<And>a \<sigma>. a : \<sigma> in A \<longleftrightarrow> a : \<sigma> in B)" shows "A = B"
proof (intro ext)
  fix a show "A a = B a" using assms apply (cases "A a", auto simp: hastype_def)
    by (metis option.exhaust)
qed

lemma in_dom_iff_ex_type: "a \<in> dom A \<longleftrightarrow> (\<exists>\<sigma>. a : \<sigma> in A)" by (auto simp: hastype_def domIff)

lemma in_dom_hastypeE: "a \<in> dom A \<Longrightarrow> (\<And>\<sigma>. a : \<sigma> in A \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: hastype_def domIff)

lemma hastype_imp_dom[simp]: "a : \<sigma> in A \<Longrightarrow> a \<in> dom A" by (auto simp: domIff)

lemma untyped_imp_not_hastype: "A a = None \<Longrightarrow> \<not> a : \<sigma> in A" by auto

lemma nex_hastype_iff: "(\<nexists>\<sigma>. a : \<sigma> in A) \<longleftrightarrow> A a = None" by (auto simp: hastype_def)

lemma all_dom_iff_all_hastype: "(\<forall>x \<in> dom A. P x) \<longleftrightarrow> (\<forall>x \<sigma>. x : \<sigma> in A \<longrightarrow> P x)"
  by (simp add: all_dom hastype_def)

abbreviation hastype_list (\<open>((_) :\<^sub>l/ (_) in/ (_))\<close> [50,61,51]50)
  where "as :\<^sub>l \<sigma>s in A \<equiv> list_all2 (\<lambda>a \<sigma>. a : \<sigma> in A) as \<sigma>s" 

lemma has_same_type_list:
  "as :\<^sub>l \<sigma>s in A \<Longrightarrow> as :\<^sub>l \<sigma>s' in A \<longleftrightarrow> \<sigma>s' = \<sigma>s"
proof (induct as arbitrary: \<sigma>s \<sigma>s')
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then show ?case by (auto simp: has_same_type list_all2_Cons1)
qed

lemma hastype_list_iff_those: "as :\<^sub>l \<sigma>s in A \<longleftrightarrow> those (map A as) = Some \<sigma>s"
proof (induct as arbitrary:\<sigma>s)
  case Nil
  then show ?case by auto
next
  case IH: (Cons a as \<sigma>\<sigma>s)
  show ?case
  proof (cases \<sigma>\<sigma>s)
    case [simp]: Nil
    show ?thesis by (auto split:option.split)
  next
    case [simp]: (Cons \<sigma> \<sigma>s)
    from IH show ?thesis by (auto intro!:hastypeI split: option.split)
  qed
qed

lemmas hastype_list_imp_those[simp] = hastype_list_iff_those[THEN iffD1]

lemma hastype_list_imp_lists_dom: "xs :\<^sub>l \<sigma>s in A \<Longrightarrow> xs \<in> lists (dom A)"
  by (auto simp: list_all2_conv_all_nth in_set_conv_nth hastype_def)

lemma subsset: "A \<subseteq>\<^sub>m A' \<longleftrightarrow> (\<forall>a \<sigma>. a : \<sigma> in A \<longrightarrow> a : \<sigma> in A')"
  by(auto simp: Ball_def map_le_def hastype_def domIff)

lemmas subssetI = subsset[THEN iffD2, rule_format]
lemmas subssetD = subsset[THEN iffD1, rule_format]

lemma subsset_hastype_listD: "A \<subseteq>\<^sub>m A' \<Longrightarrow> as :\<^sub>l \<sigma>s in A \<Longrightarrow> as :\<^sub>l \<sigma>s in A'"
  by (auto simp: list_all2_conv_all_nth subssetD)

lemma has_same_type_in_subsset:
  "a : \<sigma> in A' \<Longrightarrow> A \<subseteq>\<^sub>m A' \<Longrightarrow> a : \<sigma>' in A \<Longrightarrow> \<sigma>' = \<sigma>"
  by (auto dest!: subssetD simp: has_same_type)

lemma has_same_type_in_dom_subsset:
  "a : \<sigma> in A' \<Longrightarrow> A \<subseteq>\<^sub>m A' \<Longrightarrow> a \<in> dom A \<longleftrightarrow> a : \<sigma> in A"
  by (auto simp: in_dom_iff_ex_type dest: has_same_type_in_subsset)

lemma hastype_restrict: "a : \<sigma> in A |` S \<longleftrightarrow> a \<in> S \<and> a : \<sigma> in A"
  by (auto simp: restrict_map_def hastype_def)

lemma hastype_the_simp[simp]: "a : \<sigma> in A \<Longrightarrow> the (A a) = \<sigma>"
  by (auto)

lemma hastype_in_Some[simp]: "x : \<sigma> in Some \<longleftrightarrow> x = \<sigma>" by (auto simp: hastype_def)

lemma hastype_in_upd[simp]: "x : \<sigma> in A(y \<mapsto> \<tau>) \<longleftrightarrow> (if x = y then \<sigma> = \<tau> else x : \<sigma> in A)"
  by (auto simp: hastype_def)

lemma all_set_hastype_iff_those: "\<forall>a \<in> set as. a : \<sigma> in A \<Longrightarrow>
  those (map A as) = Some (replicate (length as) \<sigma>)"
  by (induct as, auto)

text \<open>The partial version of list nth:\<close>
primrec safe_nth where
    "safe_nth [] _ = None"
  | "safe_nth (a#as) n = (case n of 0 \<Rightarrow> Some a | Suc n \<Rightarrow> safe_nth as n)"

lemma safe_nth_simp[simp]: "i < length as \<Longrightarrow> safe_nth as i = Some (as ! i)"
  by (induct as arbitrary:i, auto split:nat.split)

lemma safe_nth_None[simp]:
  "length as \<le> i \<Longrightarrow> safe_nth as i = None"
  by (induct as arbitrary:i, auto split:nat.split)

lemma safe_nth: "safe_nth as i = (if i < length as then Some (as ! i) else None)"
  by auto

lemma safe_nth_eq_SomeE:
 "safe_nth as i = Some a \<Longrightarrow> (i < length as \<Longrightarrow> as ! i = a \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (cases "i < length as", auto)

lemma dom_safe_nth[simp]: "dom (safe_nth as) = {0..<length as}"
  by (auto simp: domIff elim!: safe_nth_eq_SomeE)

lemma safe_nth_replicate[simp]:
  "safe_nth (replicate n a) i = (if i < n then Some a else None)"
  by auto

lemma safe_nth_append:
  "safe_nth (ls@rs) i = (if i < length ls then Some (ls!i) else safe_nth rs (i - length ls))"
  by (cases "i < length (ls@rs)", auto simp: nth_append)

lemma hastype_in_safe_nth[simp]: "i : \<sigma> in safe_nth \<sigma>s \<longleftrightarrow> i < length \<sigma>s \<and> \<sigma> = \<sigma>s!i"
  by (auto simp: hastype_def safe_nth)

lemmas hastype_in_safe_nthE = safe_nth_eq_SomeE[folded hastype_def]

lemma hastype_in_o[simp]: "a : \<sigma> in A \<circ> f \<longleftrightarrow> f a : \<sigma> in A" by (simp add: hastype_def)

definition o_sset (infix \<open>\<circ>s\<close> 55) where
  "f \<circ>s A \<equiv> map_option f \<circ> A"

lemma hastype_in_o_sset: "a : \<sigma>' in f \<circ>s A \<longleftrightarrow> (\<exists>\<sigma>. a : \<sigma> in A \<and> \<sigma>' = f \<sigma>)"
  by (auto simp: o_sset_def hastype_def)

lemma hastype_in_o_ssetI: "a : \<sigma> in A \<Longrightarrow> f \<sigma> = \<sigma>' \<Longrightarrow> a : \<sigma>' in f \<circ>s A"
  by (auto simp: o_sset_def hastype_def)

lemma hastype_in_o_ssetD: "a : \<tau> in f \<circ>s A \<Longrightarrow> \<exists>\<sigma>. a : \<sigma> in A \<and> \<tau> = f \<sigma>"
  by (auto simp: o_sset_def hastype_def)

lemma hastype_in_o_ssetE: "a : \<tau> in f \<circ>s A \<Longrightarrow> (\<And>\<sigma>. a : \<sigma> in A \<Longrightarrow> \<tau> = f \<sigma> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: o_sset_def hastype_def)

lemma o_sset_restrict_sset_assoc[simp]: "f \<circ>s (A |` X) = (f \<circ>s A) |` X"
  by (auto simp: o_sset_def restrict_map_def)

lemma id_o_sset[simp]: "id \<circ>s A = A"
  and identity_o_sset[simp]: "(\<lambda>x. x) \<circ>s A = A"
  by (auto simp: o_sset_def map_option.id map_option.identity)

lemma o_ssetI: "A x = Some y \<Longrightarrow> z = f y \<Longrightarrow> (f \<circ>s A) x = Some z" by (auto simp: o_sset_def)

lemma o_ssetE: "(f \<circ>s A) x = Some z \<Longrightarrow> (\<And>y. A x = Some y \<Longrightarrow> z = f y \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: o_sset_def)

lemma dom_o_sset[simp]: "dom (f \<circ>s A) = dom A"
  by (auto intro!: o_ssetI elim!: o_ssetE simp: domIff)

lemma safe_nth_map: "safe_nth (map f as) = f \<circ>s safe_nth as"
  by (auto simp: safe_nth o_sset_def)

notation Map.empty (\<open>\<emptyset>\<close>)
lemma safe_nth_Nil[simp]: "safe_nth [] = \<emptyset>" by auto

lemma o_sset_empty[simp]: "f \<circ>s \<emptyset> = \<emptyset>" by (auto simp: o_sset_def)

lemma hastype_in_empty[simp]: "\<not>x : \<sigma> in \<emptyset>" by (auto simp: hastype_def)

subsection \<open>Maps between Sorted Sets\<close>

locale sort_preserving = fixes f :: "'a \<Rightarrow> 'b" and A :: "'a \<rightharpoonup> 's"
  assumes same_value_imp_same_type: "a : \<sigma> in A \<Longrightarrow> b : \<tau> in A \<Longrightarrow> f a = f b \<Longrightarrow> \<sigma> = \<tau>"
begin

lemma same_value_imp_in_dom_iff:
  assumes fafa': "f a = f a'" and a: "a : \<sigma> in A" shows a': "a' \<in> dom A \<longleftrightarrow> a' : \<sigma> in A"
  using same_value_imp_same_type[OF a _ fafa'] by (auto elim!: in_dom_hastypeE)

end

lemma sort_preserving_cong:
  "A = A' \<Longrightarrow> (\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> f a = f' a) \<Longrightarrow> sort_preserving f A \<longleftrightarrow> sort_preserving f' A'"
  by (auto simp: sort_preserving_def)

lemma inj_on_dom_imp_sort_preserving:
  assumes "inj_on f (dom A)" shows "sort_preserving f A"
proof unfold_locales
  fix a b \<sigma> \<tau>
  assume a: "a : \<sigma> in A" and b: "b : \<tau> in A" and eq: "f a = f b"
  with inj_onD[OF assms] have "a = b" by auto
  with a b show "\<sigma> = \<tau>" by (auto simp: has_same_type)
qed

lemma inj_imp_sort_preserving:
  assumes "inj f" shows "sort_preserving f A"
  using assms by (auto intro!: inj_on_dom_imp_sort_preserving simp: inj_on_def)

locale sorted_map =
  fixes f :: "'a \<Rightarrow> 'b" and A :: "'a \<rightharpoonup> 's" and B :: "'b \<rightharpoonup> 's"
  assumes sorted_map: "\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> f a : \<sigma> in B"
begin

lemma target_has_same_type: "a : \<sigma> in A \<Longrightarrow> f a : \<tau> in B \<longleftrightarrow> \<sigma> = \<tau>"
  by (auto simp:has_same_type dest!: sorted_map)

lemma target_dom_iff_hastype:
  "a : \<sigma> in A \<Longrightarrow> f a \<in> dom B \<longleftrightarrow> f a : \<sigma> in B"
  by (auto simp: in_dom_iff_ex_type target_has_same_type)

lemma source_dom_iff_hastype:
  "f a : \<sigma> in B \<Longrightarrow> a \<in> dom A \<longleftrightarrow> a : \<sigma> in A"
  by (auto simp: in_dom_iff_ex_type target_has_same_type)

lemma elim:
  assumes a: "(\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> f a : \<sigma> in B) \<Longrightarrow> P"
  shows P
  using a by (auto simp: sorted_map)

sublocale sort_preserving
  apply unfold_locales
  by (auto simp add: sorted_map dest!: target_has_same_type)

lemma funcset_dom: "f : dom A \<rightarrow> dom B"
  using sorted_map[unfolded hastype_def] by (auto simp: domIff)

lemma sorted_map_list: "as :\<^sub>l \<sigma>s in A \<Longrightarrow> map f as :\<^sub>l \<sigma>s in B"
  by (auto simp: list_all2_conv_all_nth sorted_map)

lemma in_dom: "a \<in> dom A \<Longrightarrow> f a \<in> dom B" by (auto elim!: in_dom_hastypeE dest!:sorted_map)

end

notation sorted_map (\<open>_ :\<^sub>s(/ _ \<rightarrow>/ _)\<close> [50,51,51]50)

abbreviation "all_sorted_map A B P \<equiv> \<forall>f. f :\<^sub>s A \<rightarrow> B \<longrightarrow> P f"
abbreviation "ex_sorted_map A B P \<equiv> \<exists>f. f :\<^sub>s A \<rightarrow> B \<and> P f"

syntax
  all_sorted_map :: "'pttrn \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (\<open>\<forall>_ :\<^sub>s(/ _ \<rightarrow>/ _)./ _\<close> [50,51,51,10]10)
  ex_sorted_map :: "'pttrn \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (\<open>\<exists>_ :\<^sub>s(/ _ \<rightarrow>/ _)./ _\<close> [50,51,51,10]10)

translations
  "\<forall>f :\<^sub>s A \<rightarrow> B. e" \<rightleftharpoons> "CONST all_sorted_map A B (\<lambda>f. e)"
  "\<exists>f :\<^sub>s A \<rightarrow> B. e" \<rightleftharpoons> "CONST ex_sorted_map A B (\<lambda>f. e)"

lemmas sorted_mapI = sorted_map.intro

lemma sorted_mapD: "f :\<^sub>s A \<rightarrow> B \<Longrightarrow> a : \<sigma> in A \<Longrightarrow> f a : \<sigma> in B"
  using sorted_map.sorted_map.

lemmas sorted_mapE = sorted_map.elim

lemma assumes "f :\<^sub>s A \<rightarrow> B"
  shows sorted_map_o: "g :\<^sub>s B \<rightarrow> C \<Longrightarrow> g \<circ> f :\<^sub>s A \<rightarrow> C"
    and sorted_map_cmono: "A' \<subseteq>\<^sub>m A \<Longrightarrow> f :\<^sub>s A' \<rightarrow> B"
    and sorted_map_mono: "B \<subseteq>\<^sub>m B' \<Longrightarrow> f :\<^sub>s A \<rightarrow> B'"
  using assms by (auto intro!:sorted_mapI dest!:subssetD sorted_mapD)

lemma sorted_map_cong:
  "(\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> f a = f' a) \<Longrightarrow>
   A = A' \<Longrightarrow>
   (\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> f a : \<sigma> in B \<longleftrightarrow> f a : \<sigma> in B') \<Longrightarrow>
  f :\<^sub>s A \<rightarrow> B \<longleftrightarrow> f' :\<^sub>s A' \<rightarrow> B'"
  by (auto simp: sorted_map_def)

lemma sorted_choice:
  assumes "\<forall>a \<sigma>. a : \<sigma> in A \<longrightarrow> (\<exists>b : \<sigma> in B. P a b)"
  shows "\<exists>f :\<^sub>s A \<rightarrow> B. (\<forall>a \<in> dom A. P a (f a))"
proof-
  have "\<forall>a \<in> dom A. \<exists>b. A a = B b \<and> P a b"
  proof
    fix a assume "a \<in> dom A"
    then obtain \<sigma> where a: "a : \<sigma> in A" by (auto elim!: in_dom_hastypeE)
    with assms obtain b where b: "b : \<sigma> in B" and P: "P a b" by auto
    with a have "A a = B b" by (auto simp: hastype_def)
    with P show "\<exists>b. A a = B b \<and> P a b" by auto
  qed
  from bchoice[OF this] obtain f where f: "\<forall>x\<in>dom A. A x = B (f x) \<and> P x (f x)" by auto
  have "f :\<^sub>s A \<rightarrow> B"
  proof
    fix a \<sigma> assume a: "a : \<sigma> in A"
    then have "a \<in> dom A" by auto
    with f have "A a = B (f a)" by auto
    with a show "f a : \<sigma> in B" by (auto simp: hastype_def)
  qed
  with f show ?thesis by auto
qed

lemma sorted_map_empty[simp]: "f :\<^sub>s \<emptyset> \<rightarrow> A"
  by (auto simp: sorted_map_def)

lemma sorted_map_comp_nth:
  "\<alpha> :\<^sub>s (f \<circ>s safe_nth (a#as)) \<rightarrow> A \<longleftrightarrow> \<alpha> 0 : f a in A \<and> (\<alpha> \<circ> Suc :\<^sub>s (f \<circ>s safe_nth as) \<rightarrow> A)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  from sorted_mapD(1)[OF this, of 0] sorted_mapD(1)[OF this, of "Suc _"]
  show ?r
    apply (intro conjI sorted_map.intro, unfold hastype_in_o_sset)
    by (auto simp: hastype_def)
next
  assume r: ?r
  then have 0: "\<alpha> 0 : f a in A" and "\<alpha> \<circ> Suc :\<^sub>s f \<circ>s safe_nth as \<rightarrow> A" by auto
  then
  have *: "i' < length as \<Longrightarrow> \<alpha> (Suc i') : f (as!i') in A" for i'
    apply (elim sorted_mapE)
    apply (unfold hastype_in_o_sset)
    apply (auto simp:sorted_map_def hastype_def).
  with 0 show ?l
    by (intro sorted_map.intro, unfold hastype_in_o_sset, unfold hastype_def,auto split:nat.split_asm elim:safe_nth_eq_SomeE)
qed

locale inhabited = fixes A
  assumes inhabited: "\<And>\<sigma>. \<exists>a. a : \<sigma> in A"
begin

lemma ex_sorted_map: "\<exists>\<alpha>. \<alpha> :\<^sub>s V \<rightarrow> A"
proof (unfold sorted_map_def, intro choice allI)
  fix v
  from inhabited
  obtain a where "\<forall>\<sigma>. v : \<sigma> in V \<longrightarrow> a : \<sigma> in A"
    apply (cases "V v")
    apply (auto dest: untyped_imp_not_hastype)[1]
    apply force.
  then show "\<exists>y. \<forall>\<sigma>. v : \<sigma> in V \<longrightarrow> y : \<sigma> in A"
    by (intro exI[of _ a], auto)
qed

end

subsection \<open>Sorted Images\<close>

text \<open>The partial version of @{term The} operator.\<close>

definition "safe_The P \<equiv> if \<exists>!x. P x then Some (The P) else None"

lemma safe_The_cong[cong]:
  assumes eq: "\<And>x. P x \<longleftrightarrow> Q x"
  shows "safe_The P = safe_The Q"
  using ext[of P Q, OF eq] by simp

lemma safe_The_eq_Some: "safe_The P = Some x \<longleftrightarrow> P x \<and> (\<forall>x'. P x' \<longrightarrow> x' = x)"
  apply (unfold safe_The_def)
  apply (cases "\<exists>!x. P x")
   apply (metis option.sel the_equality)
  by auto

lemma safe_The_eq_None: "safe_The P = None \<longleftrightarrow> \<not>(\<exists>!x. P x)"
  by (auto simp: safe_The_def)

lemma safe_The_False[simp]: "safe_The (\<lambda>x. False) = None"
  by (auto simp: safe_The_def)

definition sorted_image :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 's) \<Rightarrow> 'b \<rightharpoonup> 's" (infixr \<open>`\<^sup>s\<close> 90) where
  "(f `\<^sup>s A) b \<equiv> safe_The (\<lambda>\<sigma>. \<exists>a : \<sigma> in A. f a = b)"

lemma hastype_in_imageE:
  assumes "fx : \<sigma> in f `\<^sup>s X"
    and "\<And>x. x : \<sigma> in X \<Longrightarrow> fx = f x \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: hastype_def sorted_image_def safe_The_eq_Some)

lemma in_dom_imageE:
  "b \<in> dom (f `\<^sup>s A) \<Longrightarrow> (\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> b = f a \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (elim in_dom_hastypeE hastype_in_imageE)

context sort_preserving begin

lemma hastype_in_imageI: "a : \<sigma> in A \<Longrightarrow> b = f a \<Longrightarrow> b : \<sigma> in f `\<^sup>s A"
  by (auto simp: hastype_def sorted_image_def safe_The_eq_Some)
    (meson eq_Some_iff_hastype same_value_imp_same_type)

lemma hastype_in_imageI2: "a : \<sigma> in A \<Longrightarrow> f a : \<sigma> in f `\<^sup>s A"
  using hastype_in_imageI by simp

lemma hastype_in_image: "b : \<sigma> in f `\<^sup>s A \<longleftrightarrow> (\<exists>a : \<sigma> in A. f a = b)"
  by (auto elim!: hastype_in_imageE intro!: hastype_in_imageI)

lemma in_dom_imageI: "a \<in> dom A \<Longrightarrow> b = f a \<Longrightarrow> b \<in> dom (f `\<^sup>s A)"
  by (auto intro!: hastype_imp_dom hastype_in_imageI elim!: in_dom_hastypeE)

lemma in_dom_imageI2: "a \<in> dom A \<Longrightarrow> f a \<in> dom (f `\<^sup>s A)"
  by (auto intro!: in_dom_imageI)

lemma hastype_list_in_image: "bs :\<^sub>l \<sigma>s in f `\<^sup>s A \<longleftrightarrow> (\<exists>as. as :\<^sub>l \<sigma>s in A \<and> map f as = bs)"
  by (auto simp: list_all2_conv_all_nth hastype_in_image Skolem_list_nth intro!:nth_equalityI)

lemma dom_image[simp]: "dom (f `\<^sup>s A) = f ` dom A"
  by (auto intro!: map_le_implies_dom_le in_dom_imageI elim!: in_dom_imageE)

sublocale to_image: sorted_map f A "f `\<^sup>s A"
  apply unfold_locales by (auto intro!: hastype_in_imageI)

lemma sorted_map_iff_image_subset:
  "f :\<^sub>s A \<rightarrow> B \<longleftrightarrow> f `\<^sup>s A \<subseteq>\<^sub>m B"
  by (auto intro!: subssetI sorted_mapI hastype_in_imageI elim!: hastype_in_imageE sorted_mapE dest!:subssetD)

end

lemma sort_preserving_o:
  assumes f: "sort_preserving f A" and g: "sort_preserving g (f `\<^sup>s A)"
  shows "sort_preserving (g \<circ> f) A"
proof (intro sort_preserving.intro, unfold o_def)
  interpret f: sort_preserving using f.
  interpret g: sort_preserving g "f `\<^sup>s A" using g.
  fix a b \<sigma> \<tau>
  assume a: "a : \<sigma> in A" and b: "b : \<tau> in A" and eq: "g (f a) = g (f b)"
  from a b have "g (f a) : \<sigma> in g `\<^sup>s f `\<^sup>s A" "g (f b) : \<tau> in g `\<^sup>s f `\<^sup>s A"
    by (auto intro!: g.hastype_in_imageI f.hastype_in_imageI)
  with eq show "\<sigma> = \<tau>" by (auto simp: has_same_type)
qed

lemma sorted_image_image:
  assumes f: "sort_preserving f A" and g: "sort_preserving g (f `\<^sup>s A)"
  shows "g `\<^sup>s f `\<^sup>s A = (g \<circ> f) `\<^sup>s A"
proof-
  interpret f: sort_preserving using f.
  interpret g: sort_preserving g "f `\<^sup>s A" using g.
  interpret gf: sort_preserving \<open>g \<circ> f\<close> A using sort_preserving_o[OF f g].
  show ?thesis
    by (auto elim!: hastype_in_imageE
        intro!: sset_eqI gf.hastype_in_imageI g.hastype_in_imageI f.hastype_in_imageI)
qed

context sorted_map begin

lemma image_subsset[intro!]: "f `\<^sup>s A \<subseteq>\<^sub>m B"
  by (auto intro!: subssetI sorted_map elim!: hastype_in_imageE)

lemma dom_image_subset[intro!]: "f ` dom A \<subseteq> dom B"
  using map_le_implies_dom_le[OF image_subsset] by simp

end

lemma sorted_image_cong: "(\<And>a \<sigma>. a : \<sigma> in A \<Longrightarrow> f a = f' a) \<Longrightarrow> f `\<^sup>s A = f' `\<^sup>s A"
  by (auto 0 3 intro!: ext arg_cong[of _ _ safe_The] simp: sorted_image_def)

lemma inj_on_dom_imp_sort_preserving_inv_into:
  assumes inj: "inj_on f (dom A)" shows "sort_preserving (inv_into (dom A) f) (f `\<^sup>s A)"
  by (unfold_locales, auto elim!: hastype_in_imageE simp: inv_into_f_f[OF inj] has_same_type)

lemma inj_imp_sort_preserving_inv:
  assumes inj: "inj f" shows "sort_preserving (inv f) (f `\<^sup>s A)"
  by (unfold_locales, auto elim!: hastype_in_imageE simp: inv_into_f_f[OF inj] has_same_type)

lemma inj_on_dom_imp_inv_into_image_cancel:
  assumes inj: "inj_on f (dom A)"
  shows "inv_into (dom A) f `\<^sup>s f `\<^sup>s A = A"
proof-
  interpret f: sort_preserving f A using inj_on_dom_imp_sort_preserving[OF inj].
  interpret f': sort_preserving \<open>inv_into (dom A) f\<close> \<open>f `\<^sup>s A\<close>
    using inj_on_dom_imp_sort_preserving_inv_into[OF inj].
  show ?thesis
    by (auto intro!: sset_eqI f'.hastype_in_imageI f.hastype_in_imageI elim!: hastype_in_imageE simp: inj)
qed

lemma inj_imp_inv_image_cancel:
  assumes inj: "inj f"
  shows "inv f `\<^sup>s f `\<^sup>s A = A"
proof-
  interpret f: sort_preserving f A using inj_imp_sort_preserving[OF inj].
  interpret f': sort_preserving \<open>inv f\<close> \<open>f `\<^sup>s A\<close> using inj_imp_sort_preserving_inv[OF inj].
  show ?thesis
    by (auto intro!: sset_eqI f'.hastype_in_imageI f.hastype_in_imageI elim!: hastype_in_imageE simp: inj)
qed

definition sorted_Imagep (infixr \<open>``\<^sup>s\<close> 90)
  where "((\<sqsubseteq>) ``\<^sup>s A) b \<equiv> safe_The (\<lambda>\<sigma>. \<exists>a : \<sigma> in A. a \<sqsubseteq> b)" for r (infix \<open>\<sqsubseteq>\<close> 50)

lemma untyped_hastypeE: "A a = None \<Longrightarrow> a : \<sigma> in A \<Longrightarrow> thesis"
  by (auto simp: hastype_def)

end