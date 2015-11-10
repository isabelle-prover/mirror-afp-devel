section {* Word Problem for Context-Free Grammars  *}
(*<*)
theory CFG_Examples
imports Coinductive_Language
begin
(*>*)

text {*
The function @{term in_language} decides the word problem for a given language.
Since we can construct the language of a CFG using @{const cfg.lang} we obtain an
executable (but not very efficient) decision procedure for CFGs for free.
*}

abbreviation "\<aa> \<equiv> Inl True"
abbreviation "\<bb> \<equiv> Inl False"
abbreviation "S \<equiv> Inr ()"

interpretation palindromes: cfg "()" "\<lambda>_. [[], [\<aa>], [\<bb>], [\<aa>, S, \<aa>], [\<bb>, S, \<bb>]]"
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

interpretation Dyck: cfg "()" "\<lambda>_. [[], [\<aa>, S, \<bb>, S]]"
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

interpretation abSSa: cfg "()" "\<lambda>_. [[], [\<aa>, \<bb>, S, S, \<aa>]]"
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
