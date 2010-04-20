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


subsection{* @{term "op @@"} *}

lemma concI[simp,intro]: "u : A \<Longrightarrow> v : B \<Longrightarrow> u@v : A @@ B"
by (auto simp add: conc_def)

lemma concE[elim]: 
assumes "w \<in> A @@ B"
obtains u v where "u \<in> A" "v \<in> B" "w = u@v"
using assms by (auto simp: conc_def)

lemma conc_empty[simp]: shows "{} @@ A = {}" and "A @@ {} = {}"
by auto

lemma conc_epsilon[simp]: shows "{[]} @@ A = A" and "A @@ {[]} = A"
by (simp_all add:conc_def)

lemma conc_assoc: "(A @@ B) @@ C = A @@ (B @@ C)"
by (auto elim!: concE) (simp only: append_assoc[symmetric] concI)

lemma conc_Un_distrib:
shows "(A \<union> B) @@ C = A @@ C \<union> B @@ C"
and   "A @@ (B \<union> C) = A @@ B \<union> A @@ C"
by (auto simp: conc_def)


subsection{* @{term "A ^^ n"} *}

lemma lang_pow_add: "A ^^ (n + m) = A ^^ n @@ A ^^ m"
by (induct n) (auto simp: conc_assoc)

lemma lang_pow_empty: "{} ^^ n = (if n = 0 then {[]} else {})"
by (induct n) auto

lemma lang_pow_empty_Suc[simp]: "({}::'a lang) ^^ Suc n = {}"
by (simp add: lang_pow_empty)

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


end
