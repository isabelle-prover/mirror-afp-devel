section {* Word Problem for Context-Free Grammars  *}
(*<*)
theory Context_Free_Grammar
imports Coinductive_Language "~~/src/HOL/Library/FSet"
begin
(*>*)

section {* Context Free Languages *}

text {*
A context-free grammar consists of a list of productions for every nonterminal
and an initial nonterminal. The productions are required to be in weak Greibach
normal form, i.e. each right hand side of a production must either be empty or
start with a terminal.
*}

locale cfg =
fixes init :: "'n::enum"
and   prod :: "'n \<Rightarrow> ('t + 'n) list fset"
assumes weakGreibach:
  "\<forall>N. \<forall>rhs. rhs |\<in>| prod N \<longrightarrow> (case rhs of (Inr N # _) \<Rightarrow> False | _ \<Rightarrow> True)"

context
fixes init :: "'n::enum"
and   prod :: "'n \<Rightarrow> ('t + 'n) list fset"
begin

private fun \<oo>\<^sub>P where
  "\<oo>\<^sub>P [] = True"
| "\<oo>\<^sub>P (Inl _ # _) = False"
| "\<oo>\<^sub>P (Inr N # rhs) = ([] |\<in>| prod N \<and> \<oo>\<^sub>P rhs)"

private fun \<dd>\<^sub>P where
  "\<dd>\<^sub>P [] a = {||}"
| "\<dd>\<^sub>P (Inl b # rhs) a = (if a = b then {|rhs|} else {||})"
| "\<dd>\<^sub>P (Inr N # rhs) a =
    (\<lambda>xs. tl xs @ rhs) |`| ffilter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = Inl a) (prod N) |\<union>|
    (if [] |\<in>| prod N then \<dd>\<^sub>P rhs a else {||})"

primcorec subst :: "('t + 'n) list fset \<Rightarrow> 't language" where
  "subst P = Lang (fBex P \<oo>\<^sub>P) (\<lambda>a. subst (ffUnion ((\<lambda>r. \<dd>\<^sub>P r a) |`| P)))"

end

abbreviation (in cfg) lang where
  "lang \<equiv> subst prod (prod init)"

text {*
The function @{term in_language} decides the word problem for a given language.
Since we can construct the language of a CFG using @{const cfg.lang} we obtain an
executable (but not very efficient) decision procedure for CFGs for free.
*}

abbreviation "\<aa> \<equiv> Inl True"
abbreviation "\<bb> \<equiv> Inl False"
abbreviation "S \<equiv> Inr ()"

interpretation palindromes: cfg "()" "\<lambda>_. {|[], [\<aa>], [\<bb>], [\<aa>, S, \<aa>], [\<bb>, S, \<bb>]|}"
  by unfold_locales auto

lemma "in_language palindromes.lang []" by normalization
lemma "in_language palindromes.lang [True]" by normalization
lemma "in_language palindromes.lang [False]" by normalization
lemma "in_language palindromes.lang [True, True]" by normalization
lemma "in_language palindromes.lang [True, False, True]" by normalization
lemma "\<not> in_language palindromes.lang [True, False]" by normalization
lemma "\<not> in_language palindromes.lang [True, False, True, False]" by normalization
lemma "in_language palindromes.lang [True, False, True, True, False, True]" by normalization
lemma "\<not> in_language palindromes.lang [True, False, True, False, False, True]" by normalization

interpretation Dyck: cfg "()" "\<lambda>_. {|[], [\<aa>, S, \<bb>, S]|}"
  by unfold_locales auto
lemma "in_language Dyck.lang []" by normalization
lemma "\<not> in_language Dyck.lang [True]" by normalization
lemma "\<not> in_language Dyck.lang [False]" by normalization
lemma "in_language Dyck.lang [True, False, True, False]" by normalization
lemma "in_language Dyck.lang [True, True, False, False]" by normalization
lemma "in_language Dyck.lang [True, False, True, False]" by normalization
lemma "in_language Dyck.lang [True, False, True, False, True, True, False, False]" by normalization
lemma "\<not> in_language Dyck.lang [True, False, True, True, False]" by normalization
lemma "\<not> in_language Dyck.lang [True, True, False, False, False, True]" by normalization

interpretation abSSa: cfg "()" "\<lambda>_. {|[], [\<aa>, \<bb>, S, S, \<aa>]|}"
  by unfold_locales auto
lemma "in_language abSSa.lang []" by normalization
lemma "\<not> in_language abSSa.lang [True]" by normalization
lemma "\<not> in_language abSSa.lang [False]" by normalization
lemma "in_language abSSa.lang [True, False, True]" by normalization
lemma "in_language abSSa.lang [True, False, True, False, True, True, False, True, True]" by normalization
lemma "in_language abSSa.lang [True, False, True, False, True, True]" by normalization
lemma "\<not> in_language abSSa.lang [True, False, True, True, False]" by normalization
lemma "\<not> in_language abSSa.lang [True, True, False, False, False, True]" by normalization

end
