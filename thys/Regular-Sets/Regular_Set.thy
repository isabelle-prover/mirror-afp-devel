(*  Author: Tobias Nipkow, Alex Krauss  *)

header "Regular sets"

theory Regular_Set
imports Main
begin

types 'a lang = "'a list set"

definition conc :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a lang" (infixr "@@" 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

overloading lang_pow == "compow :: nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
begin
  primrec lang_pow :: "nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
  "lang_pow 0 A = {[]}" |
  "lang_pow (Suc n) A = A @@ (lang_pow n A)"
end

definition star :: "'a lang \<Rightarrow> 'a lang" where
"star A = (\<Union>n. A ^^ n)"

definition deriv :: "'a \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "deriv x L = { xs. x#xs \<in> L }"


coinductive bisimilar :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> bool" where
"([] \<in> K \<longleftrightarrow> [] \<in> L) 
 \<Longrightarrow> (\<And>x. bisimilar (deriv x K) (deriv x L))
 \<Longrightarrow> bisimilar K L"


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


subsection{* @{term "A ^^ n"} *}

lemma lang_pow_add: "A ^^ (n + m) = A ^^ n @@ A ^^ m"
by (induct n) (auto simp: conc_assoc)

lemma lang_pow_empty: "{} ^^ n = (if n = 0 then {[]} else {})"
by (induct n) auto

lemma lang_pow_empty_Suc[simp]: "({}::'a lang) ^^ Suc n = {}"
by (simp add: lang_pow_empty)


lemma length_lang_pow_ub:
  "ALL w : A. length w \<le> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<le> k*n"
by(induct n arbitrary: w) (fastsimp simp: conc_def)+

lemma length_lang_pow_lb:
  "ALL w : A. length w \<ge> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<ge> k*n"
by(induct n arbitrary: w) (fastsimp simp: conc_def)+


subsection{* @{const star} *}

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
by (fastsimp simp: in_star_iff_concat)

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

lemma Arden:
assumes "[] \<notin> A" and "X = A @@ X \<union> B"
shows "X = star A @@ B"
proof -
  { fix n have "X = A^^(n+1)@@X \<union> (\<Union>i\<le>n. A^^i@@B)"
    proof(induct n)
      case 0 show ?case using `X = A @@ X \<union> B` by simp
    next
      case (Suc n)
      have "X = A@@X Un B" by(rule assms(2))
      also have "\<dots> = A@@(A^^(n+1)@@X \<union> (\<Union>i\<le>n. A^^i@@B)) Un B"
        by(subst Suc)(rule refl)
      also have "\<dots> =  A^^(n+2)@@X \<union> (\<Union>i\<le>n. A^^(i+1)@@B) Un B"
        by(simp add:conc_UNION_distrib conc_assoc conc_Un_distrib)
      also have "\<dots> =  A^^(n+2)@@X \<union> (UN i : {1..n+1}. A^^i@@B) \<union> B"
        by(subst UN_le_add_shift)(rule refl)
      also have "\<dots> =  A^^(n+2)@@X \<union> (UN i : {1..n+1}. A^^i@@B) \<union> A^^0@@B"
        by(simp)
      also have "\<dots> =  A^^(n+2)@@X \<union> (\<Union>i\<le>n+1. A^^i@@B)"
        by(auto simp: UN_le_eq_Un0)
      finally show ?case by simp
    qed
  } note 1 = this
  { fix w assume "w : X"
    let ?n = "size w"
    from `[] \<notin> A` have "ALL u : A. length u \<ge> 1"
      by (metis Suc_eq_plus1 add_leD2 le_0_eq length_0_conv not_less_eq_eq)
    hence "ALL u : A^^(?n+1). length u \<ge> ?n+1"
      by (metis length_lang_pow_lb nat_mult_1)
    hence "ALL u : A^^(?n+1)@@X. length u \<ge> ?n+1"
      by(auto simp only: conc_def length_append)
    hence "w \<notin> A^^(?n+1)@@X" by auto
    hence "w : star A @@ B" using `w : X` 1[of ?n]
      by(auto simp add: star_def conc_UNION_distrib)
  } moreover
  { fix w assume "w : star A @@ B"
    hence "EX n. w : A^^n @@ B" by(auto simp: conc_def star_def)
    hence "w : X" using 1 by blast
  } ultimately show ?thesis by blast
qed

subsection{* @{const deriv} *}

lemma deriv_empty[simp]: "deriv a {} = {}"
and deriv_epsilon[simp]: "deriv a {[]} = {}"
and deriv_char[simp]: "deriv a {[b]} = (if a = b then {[]} else {})"
and deriv_union[simp]: "deriv a (A \<union> B) = deriv a A \<union> deriv a B"
by (auto simp: deriv_def)

lemma deriv_conc_subset:
"deriv a A @@ B \<subseteq> deriv a (A @@ B)" (is "?L \<subseteq> ?R")
proof 
  fix w assume "w \<in> ?L"
  then obtain u v where "w = u @ v" "a # u \<in> A" "v \<in> B"
    by (auto simp: deriv_def)
  then have "a # w \<in> A @@ B"
    by (auto intro: concI[of "a # u", simplified])
  thus "w \<in> ?R" by (auto simp: deriv_def)
qed

lemma deriv_conc1:
assumes "[] \<notin> A"
shows "deriv a (A @@ B) = deriv a A @@ B" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix w assume "w \<in> ?L"
    then have "a # w \<in> A @@ B" by (simp add: deriv_def)
    then obtain x y 
      where aw: "a # w = x @ y" "x \<in> A" "y \<in> B" by auto
    with `[] \<notin> A` obtain x' where "x = a # x'"
      by (cases x) auto
    with aw have "w = x' @ y" "x' \<in> deriv a A"
      by (auto simp: deriv_def)
    with `y \<in> B` show "w \<in> ?R" by simp
  qed
  show "?R \<subseteq> ?L" by (fact deriv_conc_subset)
qed

lemma deriv_conc2:
assumes "[] \<in> A"
shows "deriv a (A @@ B) = deriv a A @@ B \<union> deriv a B"
(is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix w assume "w \<in> ?L"
    then have "a # w \<in> A @@ B" by (simp add: deriv_def)
    then obtain x y 
      where aw: "a # w = x @ y" "x \<in> A" "y \<in> B" by auto
    show "w \<in> ?R"
    proof (cases x)
      case Nil
      with aw have "w \<in> deriv a B" by (auto simp: deriv_def)
      thus ?thesis ..
    next
      case (Cons b x')
      with aw have "w = x' @ y" "x' \<in> deriv a A"
        by (auto simp: deriv_def)
      with `y \<in> B` show "w \<in> ?R" by simp
    qed
  qed

  from concI[OF `[] \<in> A`, simplified]
  have "B \<subseteq> A @@ B" ..
  then have "deriv a B \<subseteq> deriv a (A @@ B)" by (auto simp: deriv_def)
  with deriv_conc_subset[of a A B]
  show "?R \<subseteq> ?L" by auto
qed

lemma wlog_no_eps: 
assumes PB: "\<And>B. [] \<notin> B \<Longrightarrow> P B"
assumes preserved: "\<And>A. P A \<Longrightarrow> P (insert [] A)"
shows "P A"
proof -
  let ?B = "A - {[]}"
  have "P ?B" by (rule PB) auto
  thus "P A"
  proof cases
    assume "[] \<in> A"
    then have "(insert [] ?B) = A" by auto
    with preserved[OF `P ?B`]
    show ?thesis by simp
  qed auto
qed

lemma deriv_insert_eps[simp]: 
"deriv a (insert [] A) = deriv a A"
by (auto simp: deriv_def)

lemma deriv_star[simp]: "deriv a (star A) = deriv a A @@ star A"
proof (induct A rule: wlog_no_eps)
  fix B :: "'a list set" assume "[] \<notin> B"
  thus "deriv a (star B) = deriv a B @@ star B" 
    by (subst star_unfold_left) (simp add: deriv_conc1)
qed auto


subsection{* @{const bisimilar} *}

lemma equal_if_bisimilar:
assumes "bisimilar K L" shows "K = L"
proof (rule set_eqI)
  fix w
  from `bisimilar K L` show "w \<in> K \<longleftrightarrow> w \<in> L"
  proof (induct w arbitrary: K L)
    case Nil thus ?case by (auto elim: bisimilar.cases)
  next
    case (Cons a w K L)
    from `bisimilar K L` have "bisimilar (deriv a K) (deriv a L)"
      by (auto elim: bisimilar.cases)
    then have "w \<in> deriv a K \<longleftrightarrow> w \<in> deriv a L" by (rule Cons(1))
    thus ?case by (auto simp: deriv_def)
  qed
qed

lemma language_coinduct:
fixes R (infixl "\<sim>" 50)
assumes "K \<sim> L"
assumes "\<And>K L. K \<sim> L \<Longrightarrow> ([] \<in> K \<longleftrightarrow> [] \<in> L)"
assumes "\<And>K L x. K \<sim> L \<Longrightarrow> deriv x K \<sim> deriv x L"
shows "K = L"
apply (rule equal_if_bisimilar)
apply (rule bisimilar.coinduct[of R, OF `K \<sim> L`])
apply (auto simp: assms)
done

end
