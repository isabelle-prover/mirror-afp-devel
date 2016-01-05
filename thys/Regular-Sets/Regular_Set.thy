(*  Author: Tobias Nipkow, Alex Krauss, Christian Urban  *)

section "Regular sets"

theory Regular_Set
imports Main
begin

type_synonym 'a lang = "'a list set"

definition conc :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a lang" (infixr "@@" 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

text {* checks the code preprocessor for set comprehensions *}
export_code conc checking SML

overloading lang_pow == "compow :: nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
begin
  primrec lang_pow :: "nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
  "lang_pow 0 A = {[]}" |
  "lang_pow (Suc n) A = A @@ (lang_pow n A)"
end

text {* for code generation *}

definition lang_pow :: "nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
  lang_pow_code_def [code_abbrev]: "lang_pow = compow"

lemma [code]:
  "lang_pow (Suc n) A = A @@ (lang_pow n A)"
  "lang_pow 0 A = {[]}"
  by (simp_all add: lang_pow_code_def)

hide_const (open) lang_pow

definition star :: "'a lang \<Rightarrow> 'a lang" where
"star A = (\<Union>n. A ^^ n)"


subsection{* @{term "op @@"} *}

lemma concI[simp,intro]: "u : A \<Longrightarrow> v : B \<Longrightarrow> u@v : A @@ B"
by (auto simp add: conc_def)

lemma concE[elim]: 
assumes "w \<in> A @@ B"
obtains u v where "u \<in> A" "v \<in> B" "w = u@v"
using assms by (auto simp: conc_def)

lemma conc_mono: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A @@ B \<subseteq> C @@ D"
by (auto simp: conc_def) 

lemma conc_empty[simp]: shows "{} @@ A = {}" and "A @@ {} = {}"
by auto

lemma conc_epsilon[simp]: shows "{[]} @@ A = A" and "A @@ {[]} = A"
by (simp_all add:conc_def)

lemma conc_assoc: "(A @@ B) @@ C = A @@ (B @@ C)"
by (auto elim!: concE) (simp only: append_assoc[symmetric] concI)

lemma conc_Un_distrib:
shows "A @@ (B \<union> C) = A @@ B \<union> A @@ C"
and   "(A \<union> B) @@ C = A @@ C \<union> B @@ C"
by auto

lemma conc_UNION_distrib:
shows "A @@ UNION I M = UNION I (%i. A @@ M i)"
and   "UNION I M @@ A = UNION I (%i. M i @@ A)"
by auto

lemma conc_subset_lists: "A \<subseteq> lists S \<Longrightarrow> B \<subseteq> lists S \<Longrightarrow> A @@ B \<subseteq> lists S"
by(fastforce simp: conc_def in_lists_conv_set)

lemma Nil_in_conc[simp]: "[] \<in> A @@ B \<longleftrightarrow> [] \<in> A \<and> [] \<in> B"
by (metis append_is_Nil_conv concE concI)

lemma concI_if_Nil1: "[] \<in> A \<Longrightarrow> xs : B \<Longrightarrow> xs \<in> A @@ B"
by (metis append_Nil concI)

lemma conc_Diff_if_Nil1: "[] \<in> A \<Longrightarrow> A @@ B = (A - {[]}) @@ B \<union> B"
by (fastforce elim: concI_if_Nil1)

lemma concI_if_Nil2: "[] \<in> B \<Longrightarrow> xs : A \<Longrightarrow> xs \<in> A @@ B"
by (metis append_Nil2 concI)

lemma conc_Diff_if_Nil2: "[] \<in> B \<Longrightarrow> A @@ B = A @@ (B - {[]}) \<union> A"
by (fastforce elim: concI_if_Nil2)

lemma singleton_in_conc:
  "[x] : A @@ B \<longleftrightarrow> [x] : A \<and> [] : B \<or> [] : A \<and> [x] : B"
by (fastforce simp: Cons_eq_append_conv append_eq_Cons_conv
       conc_Diff_if_Nil1 conc_Diff_if_Nil2)


subsection{* @{term "A ^^ n"} *}

lemma lang_pow_add: "A ^^ (n + m) = A ^^ n @@ A ^^ m"
by (induct n) (auto simp: conc_assoc)

lemma lang_pow_empty: "{} ^^ n = (if n = 0 then {[]} else {})"
by (induct n) auto

lemma lang_pow_empty_Suc[simp]: "({}::'a lang) ^^ Suc n = {}"
by (simp add: lang_pow_empty)

lemma conc_pow_comm:
  shows "A @@ (A ^^ n) = (A ^^ n) @@ A"
by (induct n) (simp_all add: conc_assoc[symmetric])

lemma length_lang_pow_ub:
  "ALL w : A. length w \<le> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<le> k*n"
by(induct n arbitrary: w) (fastforce simp: conc_def)+

lemma length_lang_pow_lb:
  "ALL w : A. length w \<ge> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<ge> k*n"
by(induct n arbitrary: w) (fastforce simp: conc_def)+

lemma lang_pow_subset_lists: "A \<subseteq> lists S \<Longrightarrow> A ^^ n \<subseteq> lists S"
by(induction n)(auto simp: conc_subset_lists[OF assms])


subsection{* @{const star} *}

lemma star_subset_lists: "A \<subseteq> lists S \<Longrightarrow> star A \<subseteq> lists S"
unfolding star_def by(blast dest: lang_pow_subset_lists)

lemma star_if_lang_pow[simp]: "w : A ^^ n \<Longrightarrow> w : star A"
by (auto simp: star_def)

lemma Nil_in_star[iff]: "[] : star A"
proof (rule star_if_lang_pow)
  show "[] : A ^^ 0" by simp
qed

lemma star_if_lang[simp]: assumes "w : A" shows "w : star A"
proof (rule star_if_lang_pow)
  show "w : A ^^ 1" using `w : A` by simp
qed

lemma append_in_starI[simp]:
assumes "u : star A" and "v : star A" shows "u@v : star A"
proof -
  from `u : star A` obtain m where "u : A ^^ m" by (auto simp: star_def)
  moreover
  from `v : star A` obtain n where "v : A ^^ n" by (auto simp: star_def)
  ultimately have "u@v : A ^^ (m+n)" by (simp add: lang_pow_add)
  thus ?thesis by simp
qed

lemma conc_star_star: "star A @@ star A = star A"
by (auto simp: conc_def)

lemma conc_star_comm:
  shows "A @@ star A = star A @@ A"
unfolding star_def conc_pow_comm conc_UNION_distrib
by simp

lemma star_induct[consumes 1, case_names Nil append, induct set: star]:
assumes "w : star A"
  and "P []"
  and step: "!!u v. u : A \<Longrightarrow> v : star A \<Longrightarrow> P v \<Longrightarrow> P (u@v)"
shows "P w"
proof -
  { fix n have "w : A ^^ n \<Longrightarrow> P w"
    by (induct n arbitrary: w) (auto intro: `P []` step star_if_lang_pow) }
  with `w : star A` show "P w" by (auto simp: star_def)
qed

lemma star_empty[simp]: "star {} = {[]}"
by (auto elim: star_induct)

lemma star_epsilon[simp]: "star {[]} = {[]}"
by (auto elim: star_induct)

lemma star_idemp[simp]: "star (star A) = star A"
by (auto elim: star_induct)

lemma star_unfold_left: "star A = A @@ star A \<union> {[]}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" by (rule, erule star_induct) auto
qed auto

lemma concat_in_star: "set ws \<subseteq> A \<Longrightarrow> concat ws : star A"
by (induct ws) simp_all

lemma in_star_iff_concat:
  "w : star A = (EX ws. set ws \<subseteq> A & w = concat ws)"
  (is "_ = (EX ws. ?R w ws)")
proof
  assume "w : star A" thus "EX ws. ?R w ws"
  proof induct
    case Nil have "?R [] []" by simp
    thus ?case ..
  next
    case (append u v)
    moreover
    then obtain ws where "set ws \<subseteq> A \<and> v = concat ws" by blast
    ultimately have "?R (u@v) (u#ws)" by auto
    thus ?case ..
  qed
next
  assume "EX us. ?R w us" thus "w : star A"
  by (auto simp: concat_in_star)
qed

lemma star_conv_concat: "star A = {concat ws|ws. set ws \<subseteq> A}"
by (fastforce simp: in_star_iff_concat)

lemma star_insert_eps[simp]: "star (insert [] A) = star(A)"
proof-
  { fix us
    have "set us \<subseteq> insert [] A \<Longrightarrow> EX vs. concat us = concat vs \<and> set vs \<subseteq> A"
      (is "?P \<Longrightarrow> EX vs. ?Q vs")
    proof
      let ?vs = "filter (%u. u \<noteq> []) us"
      show "?P \<Longrightarrow> ?Q ?vs" by (induct us) auto
    qed
  } thus ?thesis by (auto simp: star_conv_concat)
qed

lemma star_unfold_left_Nil: "star A = (A - {[]}) @@ (star A) \<union> {[]}"
by (metis insert_Diff_single star_insert_eps star_unfold_left)

lemma star_Diff_Nil_fold: "(A - {[]}) @@ star A = star A - {[]}"
proof -
  have "[] \<notin> (A - {[]}) @@ star A" by simp
  thus ?thesis using star_unfold_left_Nil by blast
qed

lemma star_decom: 
  assumes a: "x \<in> star A" "x \<noteq> []"
  shows "\<exists>a b. x = a @ b \<and> a \<noteq> [] \<and> a \<in> A \<and> b \<in> star A"
using a by (induct rule: star_induct) (blast)+


subsection {* Left-Quotients of languages *}

definition Deriv :: "'a \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "Deriv x A = { xs. x#xs \<in> A }"

definition Derivs :: "'a list \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "Derivs xs A = { ys. xs @ ys \<in> A }"

abbreviation 
  Derivss :: "'a list \<Rightarrow> 'a lang set \<Rightarrow> 'a lang"
where
  "Derivss s As \<equiv> \<Union> (Derivs s ` As)"


lemma Deriv_empty[simp]:   "Deriv a {} = {}"
  and Deriv_epsilon[simp]: "Deriv a {[]} = {}"
  and Deriv_char[simp]:    "Deriv a {[b]} = (if a = b then {[]} else {})"
  and Deriv_union[simp]:   "Deriv a (A \<union> B) = Deriv a A \<union> Deriv a B"
  and Deriv_inter[simp]:   "Deriv a (A \<inter> B) = Deriv a A \<inter> Deriv a B"
  and Deriv_compl[simp]:   "Deriv a (-A) = - Deriv a A"
  and Deriv_Union[simp]:   "Deriv a (Union M) = Union(Deriv a ` M)"
  and Deriv_UN[simp]:      "Deriv a (UN x:I. S x) = (UN x:I. Deriv a (S x))"
by (auto simp: Deriv_def)

lemma Der_conc [simp]: 
  shows "Deriv c (A @@ B) = (Deriv c A) @@ B \<union> (if [] \<in> A then Deriv c B else {})"
unfolding Deriv_def conc_def
by (auto simp add: Cons_eq_append_conv)

lemma Deriv_star [simp]: 
  shows "Deriv c (star A) = (Deriv c A) @@ star A"
proof -
  have "Deriv c (star A) = Deriv c ({[]} \<union> A @@ star A)"
    by (metis star_unfold_left sup.commute)
  also have "... = Deriv c (A @@ star A)"
    unfolding Deriv_union by (simp)
  also have "... = (Deriv c A) @@ (star A) \<union> (if [] \<in> A then Deriv c (star A) else {})"
    by simp
  also have "... =  (Deriv c A) @@ star A"
    unfolding conc_def Deriv_def
    using star_decom by (force simp add: Cons_eq_append_conv)
  finally show "Deriv c (star A) = (Deriv c A) @@ star A" .
qed

lemma Deriv_diff[simp]:   
  shows "Deriv c (A - B) = Deriv c A - Deriv c B"
by(auto simp add: Deriv_def)

lemma Deriv_lists[simp]: "c : S \<Longrightarrow> Deriv c (lists S) = lists S"
by(auto simp add: Deriv_def)

lemma Derivs_simps [simp]:
  shows "Derivs [] A = A"
  and   "Derivs (c # s) A = Derivs s (Deriv c A)"
  and   "Derivs (s1 @ s2) A = Derivs s2 (Derivs s1 A)"
unfolding Derivs_def Deriv_def by auto

lemma in_fold_Deriv: "v \<in> fold Deriv w L \<longleftrightarrow> w @ v \<in> L"
  by (induct w arbitrary: L) (simp_all add: Deriv_def)

lemma Derivs_alt_def: "Derivs w L = fold Deriv w L"
  by (induct w arbitrary: L) simp_all


subsection {* Shuffle product *}

fun shuffle where
  "shuffle [] ys = {ys}"
| "shuffle xs [] = {xs}"
| "shuffle (x # xs) (y # ys) =
    {x # w | w . w \<in> shuffle xs (y # ys)} \<union>
    {y # w | w . w \<in> shuffle (x # xs) ys}"

lemma shuffle_empty2[simp]: "shuffle xs [] = {xs}"
  by (cases xs) auto

lemma Nil_in_shuffle[simp]: "[] \<in> shuffle xs ys \<longleftrightarrow> xs = [] \<and> ys = []"
  by (induct xs ys rule: shuffle.induct) auto

definition Shuffle (infixr "\<parallel>" 80) where
  "Shuffle A B = \<Union>{shuffle xs ys | xs ys. xs \<in> A \<and> ys \<in> B}"

lemma shuffleE:
  "zs \<in> shuffle xs ys \<Longrightarrow>
    (zs = xs \<Longrightarrow> ys = [] \<Longrightarrow> P) \<Longrightarrow>
    (zs = ys \<Longrightarrow> xs = [] \<Longrightarrow> P) \<Longrightarrow>
    (\<And>x xs' z zs'. xs = x # xs' \<Longrightarrow> zs = z # zs' \<Longrightarrow> x = z \<Longrightarrow> zs' \<in> shuffle xs' ys \<Longrightarrow> P) \<Longrightarrow>
    (\<And>y ys' z zs'. ys = y # ys' \<Longrightarrow> zs = z # zs' \<Longrightarrow> y = z \<Longrightarrow> zs' \<in> shuffle xs ys' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct xs ys rule: shuffle.induct) auto

lemma Cons_in_shuffle_iff:
  "z # zs \<in> shuffle xs ys \<longleftrightarrow>
    (xs \<noteq> [] \<and> hd xs = z \<and> zs \<in> shuffle (tl xs) ys \<or>
     ys \<noteq> [] \<and> hd ys = z \<and> zs \<in> shuffle xs (tl ys))"
  by (induct xs ys rule: shuffle.induct) auto

lemma Deriv_Shuffle[simp]:
  "Deriv a (A \<parallel> B) = Deriv a A \<parallel> B \<union> A \<parallel> Deriv a B"
  unfolding Shuffle_def Deriv_def by (fastforce simp: Cons_in_shuffle_iff neq_Nil_conv)

lemma shuffle_subset_lists:
  assumes "A \<subseteq> lists S" "B \<subseteq> lists S"
  shows "A \<parallel> B \<subseteq> lists S"
unfolding Shuffle_def proof safe
  fix x and zs xs ys :: "'a list"
  assume zs: "zs \<in> shuffle xs ys" "x \<in> set zs" and "xs \<in> A" "ys \<in> B"
  with assms have "xs \<in> lists S" "ys \<in> lists S" by auto
  with zs show "x \<in> S" by (induct xs ys arbitrary: zs rule: shuffle.induct) auto
qed

lemma Nil_in_Shuffle[simp]: "[] \<in> A \<parallel> B \<longleftrightarrow> [] \<in> A \<and> [] \<in> B"
  unfolding Shuffle_def by force

lemma shuffle_Un_distrib:
shows "A \<parallel> (B \<union> C) = A \<parallel> B \<union> A \<parallel> C"
and   "A \<parallel> (B \<union> C) = A \<parallel> B \<union> A \<parallel> C"
unfolding Shuffle_def by fast+

lemma shuffle_UNION_distrib:
shows "A \<parallel> UNION I M = UNION I (%i. A \<parallel> M i)"
and   "UNION I M \<parallel> A = UNION I (%i. M i \<parallel> A)"
unfolding Shuffle_def by fast+

lemma Shuffle_empty[simp]:
  "A \<parallel> {} = {}"
  "{} \<parallel> B = {}"
  unfolding Shuffle_def by auto

lemma Shuffle_eps[simp]:
  "A \<parallel> {[]} = A"
  "{[]} \<parallel> B = B"
  unfolding Shuffle_def by auto


subsection {* Arden's Lemma *}

lemma arden_helper:
  assumes eq: "X = A @@ X \<union> B"
  shows "X = (A ^^ Suc n) @@ X \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)"
proof (induct n)
  case 0 
  show "X = (A ^^ Suc 0) @@ X \<union> (\<Union>m\<le>0. (A ^^ m) @@ B)"
    using eq by simp
next
  case (Suc n)
  have ih: "X = (A ^^ Suc n) @@ X \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)" by fact
  also have "\<dots> = (A ^^ Suc n) @@ (A @@ X \<union> B) \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)" using eq by simp
  also have "\<dots> = (A ^^ Suc (Suc n)) @@ X \<union> ((A ^^ Suc n) @@ B) \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)"
    by (simp add: conc_Un_distrib conc_assoc[symmetric] conc_pow_comm)
  also have "\<dots> = (A ^^ Suc (Suc n)) @@ X \<union> (\<Union>m\<le>Suc n. (A ^^ m) @@ B)"
    by (auto simp add: le_Suc_eq)
  finally show "X = (A ^^ Suc (Suc n)) @@ X \<union> (\<Union>m\<le>Suc n. (A ^^ m) @@ B)" .
qed

lemma Arden:
  assumes "[] \<notin> A" 
  shows "X = A @@ X \<union> B \<longleftrightarrow> X = star A @@ B"
proof
  assume eq: "X = A @@ X \<union> B"
  { fix w assume "w : X"
    let ?n = "size w"
    from `[] \<notin> A` have "ALL u : A. length u \<ge> 1"
      by (metis Suc_eq_plus1 add_leD2 le_0_eq length_0_conv not_less_eq_eq)
    hence "ALL u : A^^(?n+1). length u \<ge> ?n+1"
      by (metis length_lang_pow_lb nat_mult_1)
    hence "ALL u : A^^(?n+1)@@X. length u \<ge> ?n+1"
      by(auto simp only: conc_def length_append)
    hence "w \<notin> A^^(?n+1)@@X" by auto
    hence "w : star A @@ B" using `w : X` using arden_helper[OF eq, where n="?n"]
      by (auto simp add: star_def conc_UNION_distrib)
  } moreover
  { fix w assume "w : star A @@ B"
    hence "EX n. w : A^^n @@ B" by(auto simp: conc_def star_def)
    hence "w : X" using arden_helper[OF eq] by blast
  } ultimately show "X = star A @@ B" by blast 
next
  assume eq: "X = star A @@ B"
  have "star A = A @@ star A \<union> {[]}"
    by (rule star_unfold_left)
  then have "star A @@ B = (A @@ star A \<union> {[]}) @@ B"
    by metis
  also have "\<dots> = (A @@ star A) @@ B \<union> B"
    unfolding conc_Un_distrib by simp
  also have "\<dots> = A @@ (star A @@ B) \<union> B" 
    by (simp only: conc_assoc)
  finally show "X = A @@ X \<union> B" 
    using eq by blast 
qed


lemma reversed_arden_helper:
  assumes eq: "X = X @@ A \<union> B"
  shows "X = X @@ (A ^^ Suc n) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))"
proof (induct n)
  case 0 
  show "X = X @@ (A ^^ Suc 0) \<union> (\<Union>m\<le>0. B @@ (A ^^ m))"
    using eq by simp
next
  case (Suc n)
  have ih: "X = X @@ (A ^^ Suc n) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))" by fact
  also have "\<dots> = (X @@ A \<union> B) @@ (A ^^ Suc n) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))" using eq by simp
  also have "\<dots> = X @@ (A ^^ Suc (Suc n)) \<union> (B @@ (A ^^ Suc n)) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))"
    by (simp add: conc_Un_distrib conc_assoc)
  also have "\<dots> = X @@ (A ^^ Suc (Suc n)) \<union> (\<Union>m\<le>Suc n. B @@ (A ^^ m))"
    by (auto simp add: le_Suc_eq)
  finally show "X = X @@ (A ^^ Suc (Suc n)) \<union> (\<Union>m\<le>Suc n. B @@ (A ^^ m))" .
qed

theorem reversed_Arden:
  assumes nemp: "[] \<notin> A"
  shows "X = X @@ A \<union> B \<longleftrightarrow> X = B @@ star A"
proof
 assume eq: "X = X @@ A \<union> B"
  { fix w assume "w : X"
    let ?n = "size w"
    from `[] \<notin> A` have "ALL u : A. length u \<ge> 1"
      by (metis Suc_eq_plus1 add_leD2 le_0_eq length_0_conv not_less_eq_eq)
    hence "ALL u : A^^(?n+1). length u \<ge> ?n+1"
      by (metis length_lang_pow_lb nat_mult_1)
    hence "ALL u : X @@ A^^(?n+1). length u \<ge> ?n+1"
      by(auto simp only: conc_def length_append)
    hence "w \<notin> X @@ A^^(?n+1)" by auto
    hence "w : B @@ star A" using `w : X` using reversed_arden_helper[OF eq, where n="?n"]
      by (auto simp add: star_def conc_UNION_distrib)
  } moreover
  { fix w assume "w : B @@ star A"
    hence "EX n. w : B @@ A^^n" by (auto simp: conc_def star_def)
    hence "w : X" using reversed_arden_helper[OF eq] by blast
  } ultimately show "X = B @@ star A" by blast 
next 
  assume eq: "X = B @@ star A"
  have "star A = {[]} \<union> star A @@ A" 
    unfolding conc_star_comm[symmetric]
    by(metis Un_commute star_unfold_left)
  then have "B @@ star A = B @@ ({[]} \<union> star A @@ A)"
    by metis
  also have "\<dots> = B \<union> B @@ (star A @@ A)"
    unfolding conc_Un_distrib by simp
  also have "\<dots> = B \<union> (B @@ star A) @@ A" 
    by (simp only: conc_assoc)
  finally show "X = X @@ A \<union> B" 
    using eq by blast 
qed

end
