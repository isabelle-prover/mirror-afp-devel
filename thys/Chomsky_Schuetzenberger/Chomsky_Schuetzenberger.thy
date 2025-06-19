(* Author: Moritz Roos; Tobias Nipkow *)

theory Chomsky_Schuetzenberger
imports
  Context_Free_Grammar.Parse_Tree
  Context_Free_Grammar.Chomsky_Normal_Form
  Finite_Automata_Not_HF
  Dyck_Language_Syms
begin

text \<open>This theory proves the Chomsky-Schützenberger representation theorem \<^cite>\<open>ChomskyS\<close>.
We closely follow Kozen \<^cite>\<open>Kozen\<close> for the proof.
The theorem states that every context-free language \<open>L\<close> 
can be written as \<^term>\<open>h(R \<inter> Dyck_lang(\<Gamma>))\<close>, for a suitable alphabet \<open>\<Gamma>\<close>, 
a regular language \<open>R\<close> and a word-homomorphism \<open>h\<close>.

The Dyck language over a set \<open>\<Gamma>\<close> (also called it's bracket language) is defined as follows:
The symbols of  \<open>\<Gamma>\<close> are paired with \<open>[\<close> and \<open>]\<close>, as in \<open>[\<^sub>g\<close> and \<open>]\<^sub>g\<close> for \<open>g \<in> \<Gamma>\<close>.
The Dyck language over \<open>\<Gamma>\<close> is the language of correctly bracketed words.
The construction of the Dyck language is found in theory \<^theory>\<open>Chomsky_Schuetzenberger.Dyck_Language_Syms\<close>.
\<close>

section\<open>Overview of the Proof\<close>

text\<open>
A rough proof of Chomsky-Schützenberger is as follows:
Take some context-free grammar for \<open>L\<close> with productions \<open>P\<close>.
Wlog assume it is in Chomsky Normal Form. 
Now define a new language \<open>L'\<close> with productions \<open>P'\<close> in the following way from \<open>P\<close>:

If \<open>\<pi> = A \<rightarrow> BC\<close> let \<open>\<pi>' = A \<rightarrow> [\<^sup>1\<^sub>\<pi> B ]\<^sup>1\<^sub>p [\<^sup>2\<^sub>\<pi> C ]\<^sup>2\<^sub>p\<close>,
if \<open>\<pi> = A \<rightarrow> a\<close> let \<open>\<pi>' = A \<rightarrow> [\<^sup>1\<^sub>\<pi> ]\<^sup>1\<^sub>p [\<^sup>2\<^sub>\<pi> ]\<^sup>2\<^sub>p\<close>,
where the brackets are viewed as terminals and the old variables 
\<open>A\<close>, \<open>B\<close>, \<open>C\<close> are again viewed as nonterminals.
This transformation is implemented by the function \<open>transform_prod\<close> below.
Note brackets are now adorned with superscripts
1 and 2 to distinguish the first and second occurrences easily. That is, we work with symbols
that are triples of type \<open>{[,]} \<times> old_prod_type \<times> {1,2}\<close>.

This bracketing encodes the parse tree of any old word.
The old word is easily recovered by the homomorphism which sends 
\<open>[\<^sup>1\<^sub>\<pi>\<close> to \<open>a\<close> if \<open>\<pi> = A \<rightarrow> a\<close>, and sends every other bracket to \<open>\<epsilon>\<close>.
Thus we have \<open>h(L') = L\<close> by essentially exchanging \<open>\<pi>\<close> for \<open>\<pi>'\<close> and the other way round in the derivation.
The direction \<open>\<supseteq>\<close> is done in \<open>transfer_parse_tree\<close>,
the direction \<open>\<subseteq>\<close> is done directly in the proof of the main theorem.

Then all that remains to show is, that \<open>L'\<close> is of the form \<open>R \<inter> Dyck_lang \<Gamma>\<close> 
(for \<open>\<Gamma>:= P \<times> {1, 2}\<close>) and the regularity of \<open>R\<close>.

For this, \<open>R := R\<^sub>S\<close> is defined via an intersection of 5 following regular languages. 
Each of these is defined via a property on words \<open>x\<close>:

  \<^descr> \<open>P1 x\<close>: after a \<open>]\<^sup>1\<^sub>p\<close> there always immediately follows a \<open>[\<^sup>2\<^sub>p\<close> in \<open>x\<close>.
      This especially means, that \<open>]\<^sup>1\<^sub>p\<close> cannot be the end of the string.

  \<^descr> \<open>successively P2 x\<close>: a \<open>]\<^sup>2\<^sub>\<pi>\<close> is never directly followed by some \<open>[\<close> in \<open>x\<close>.

  \<^descr> \<open>successively P3 x\<close>: each \<open>[\<^sup>1\<^bsub>A\<rightarrow>BC\<^esub>\<close> is directly followed by \<open>[\<^sup>1\<^bsub>B\<rightarrow>_\<^esub>\<close> in \<open>x\<close>
      (last letter isn't checked).

  \<^descr> \<open>successively P4 x\<close>: each \<open>[\<^sup>1\<^bsub>A\<rightarrow>a\<^esub>\<close> is directly followed by \<open>]\<^sup>1\<^bsub>A\<rightarrow>a\<^esub>\<close> in \<open>x\<close>
and each \<open>[\<^sup>2\<^bsub>A\<rightarrow>a\<^esub>\<close> is directly followed by \<open>]\<^sup>2\<^bsub>A\<rightarrow>a\<^esub>\<close> in \<open>x\<close> (last letter isn't checked).

  \<^descr> \<open>P5 A x\<close>: there exists some \<open>y\<close> such that the word begins with \<open>[\<^sup>1\<^bsub>A\<rightarrow>y\<^esub>\<close>.


One then shows the key theorem \<open>P' \<turnstile> A \<rightarrow>\<^sup>* w  \<longleftrightarrow>  w \<in> R\<^sub>A \<inter> Dyck_lang \<Gamma>\<close>:

The \<open>\<rightarrow>\<close>-direction (see lemma \<open>P'_imp_Reg\<close>) is easily checked, by checking that every condition holds
during all derivation steps already. For this one needs a version of R (and all the conditions)
which ignores any Terminals that might still exist in such a derivation step. Since this version
operates on symbols (a different type) it needs a fully new definition. Since these new versions 
allow more flexibility on the words, it turns out that the original 5 conditions aren't enough anymore 
to fully constrain to the target language. Thus we add two additional 
constraints \<open>successively P7\<close> and \<open>successively P8\<close> on the symbol-version of \<open>R\<^sub>A\<close> that vanish when 
we ultimately restricts back to words consisting only of terminal symbols. With these the induction goes through:

  \<^descr> \<open>(successively P7_sym) x\<close>: each \<open>Nt Y\<close> is directly preceded by some \<open>Tm [\<^sup>1\<^bsub>A\<rightarrow>YC\<^esub>\<close> or some \<open>Tm [\<^sup>2\<^bsub>A\<rightarrow>BY\<^esub>\<close> in \<open>x\<close>;
  \<^descr> \<open>(successively P8_sym) x\<close>: each \<open>Nt Y\<close> is directly followed by some \<open>]\<^sup>1\<^bsub>A\<rightarrow>YC\<^esub>\<close> or some \<open>]\<^sup>2\<^bsub>A\<rightarrow>BY\<^esub>\<close> in \<open>x\<close>.

The \<open>\<leftarrow>\<close>-direction (see lemma \<open>Reg_and_dyck_imp_P'\<close>) is more work. 
This time we stick with fully terminal words, so we work with the standard version of \<open>R\<^sub>A\<close>:
Proceed by induction on the length of \<open>w\<close> generalized over \<open>A\<close>. 
For this, let \<open>x \<in> R\<^sub>A \<inter> Dyck_lang \<Gamma>\<close>, thus we have the properties 
\<open>P1 x\<close>, \<open>successively Pi x\<close> for \<open>i \<in> {2,3,4,7,8}\<close> and \<open>P5 A x\<close> available.
From \<open>P5 A x\<close> we have that there exists \<open>\<pi> \<in> P\<close> s.t. \<open>fst \<pi> = A\<close> and \<open>x\<close> begins
with \<open>[\<^sup>1\<^sub>\<pi>\<close>. Since \<open>x \<in> Dyck_lang \<Gamma>\<close> it is balanced, so it must be of the form
  \<open>x = [\<^sup>1\<^sub>\<pi>  y  ]\<^sup>1\<^sub>\<pi>  r1\<close> 
for some balanced \<open>y\<close>.  From \<open>P1 x\<close> it must then be of the form 
  \<open>x = [\<^sup>1\<^sub>\<pi>  y  ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi>  r1'.\<close>
Since \<open>x\<close> is balanced it must then be of the form
  \<open>x = [\<^sup>1\<^sub>\<pi>  y  ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi> z ]\<^sup>2\<^sub>\<pi> r2\<close> 
for some balanced \<open>z\<close>. Then \<open>r2\<close> must also be balanced. If \<open>r2\<close> was not empty 
it would begin with an opening bracket, but \<open>P2 x\<close> makes this impossible - so 
\<open>r2 = []\<close> and as such
  \<open>x = [\<^sup>1\<^sub>\<pi>  y  ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi> z ]\<^sup>2\<^sub>\<pi>.\<close>
Since our grammar is in CNF, we can consider the following case distinction on \<open>\<pi>\<close>:
  \<^descr> Case 1: \<open>\<pi> = A \<rightarrow> BC\<close>. 
  Since \<open>y,z\<close> are balanced substrings of \<open>x\<close> one easily checks
  \<open>Pi y\<close> and \<open>Pi z\<close> for \<open>i \<in> {1,2,3,4}\<close>. From \<open>P3 x\<close> (and \<open>\<pi> = A \<rightarrow> BC\<close>) we further obtain \<open>P5 B y\<close> and \<open>P5 C z\<close>.
  So \<open>y \<in> R\<^sub>B \<inter> Dyck_lang \<Gamma>\<close> and \<open>z \<in> R\<^sub>C \<inter> Dyck_lang \<Gamma>\<close>.
  From the induction hypothesis we thus obtain 
    \<open>P' \<turnstile> B \<rightarrow>\<^sup>* y\<close> and \<open>P' \<turnstile> C \<rightarrow>\<^sup>* z.\<close>
  Since \<open>\<pi> = A \<rightarrow> BC\<close> we then have
    \<open>A  \<rightarrow>\<^sup>1\<^bsub>\<pi>'\<^esub>  [\<^sup>1\<^sub>\<pi>  B  ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi> C ]\<^sup>2\<^sub>\<pi>  \<rightarrow>\<^sup>* [\<^sup>1\<^sub>\<pi>  y  ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi> z ]\<^sup>2\<^sub>\<pi> = x\<close>
  as required.
  \<^descr> Case 2: \<open>\<pi> = A \<rightarrow> a\<close>. 
  Suppose we didn't have \<open>y = []\<close>. Then from \<open>P4 x\<close> (and \<open>\<pi> = A \<rightarrow> a\<close>) we would have \<open>y = ]\<^sup>1\<^sub>\<pi>\<close>. 
  But since \<open>y\<close> is balanced it needs to begin with an opening bracket, contradiction.
  So it must be that \<open>y = []\<close>.
  By the same argument we also have that \<open>z = []\<close>.
  So really \<open>x = [\<^sup>1\<^sub>\<pi>   ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi>  ]\<^sup>2\<^sub>\<pi>\<close> and of course from \<open>\<pi> = A \<rightarrow> a\<close> it holds
  \<open>A  \<rightarrow>\<^sup>1\<^bsub>\<pi>'\<^esub>  [\<^sup>1\<^sub>\<pi>  ]\<^sup>1\<^sub>\<pi>  [\<^sup>2\<^sub>\<pi>  ]\<^sup>2\<^sub>\<pi>  = x\<close> as required.

From the key theorem we obtain (by setting \<open>A := S\<close>) that 
  \<open>L' = R\<^sub>S \<inter> Dyck_lang \<Gamma>\<close> as wanted.

Only regularity remains to be shown. 
For this we use that 
\<open>R\<^sub>S \<inter> Dyck_lang \<Gamma> = (R\<^sub>S \<inter> brackets \<Gamma>) \<inter> Dyck_lang \<Gamma>\<close>, 
where \<open>brackets \<Gamma> (\<supseteq> Dyck_lang \<Gamma>)\<close> is the set of words which only 
consist of brackets over \<open>\<Gamma>\<close>.
Actually, what we defined as \<open>R\<^sub>S\<close>, isn't regular, only \<open>(R\<^sub>S \<inter> brackets \<Gamma>)\<close> is.
The intersection restricts to a finite amount of possible brackets, 
that are used in states for finite automatons for the 5 languages that \<open>R\<^sub>S\<close> is
the intersection of.

Throughout most of the proof below, we implicitly or explicitly assume that the grammar is in CNF.
This is lifted only at the very end.
\<close>



section\<open>Production Transformation and Homomorphisms\<close>

text \<open>A fixed finite set of productions \<open>P\<close>, used later on:\<close>

locale locale_P =
fixes P :: "('n,'t) Prods"
assumes finiteP: \<open>finite P\<close>


subsection\<open>Brackets\<close>

text\<open>A type with 2 elements, for creating 2 copies as needed in the proof:\<close>
datatype version = One | Two

type_synonym ('n,'t) bracket3 = "(('n, 't) prod \<times> version) bracket"

abbreviation open_bracket1 :: "('n, 't) prod \<Rightarrow> ('n,'t) bracket3" ("[\<^sup>1\<^sub>_ " [1000]) where
  "[\<^sup>1\<^sub>p  \<equiv> (Open (p, One))"

abbreviation close_bracket1 :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("]\<^sup>1\<^sub>_" [1000]) where
  "]\<^sup>1\<^sub>p \<equiv> (Close (p, One))"

abbreviation open_bracket2 :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("[\<^sup>2\<^sub>_" [1000]) where
  "[\<^sup>2\<^sub>p \<equiv> (Open (p, Two))"

abbreviation close_bracket2 :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("]\<^sup>2\<^sub>_" [1000]) where
  "]\<^sup>2\<^sub>p \<equiv> (Close (p, Two))"


text\<open>Version for p = (A, w) (multiple letters) with bsub and esub:\<close>
abbreviation open_bracket1' :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("[\<^sup>1\<^bsub>_\<^esub> ") where
  "[\<^sup>1\<^bsub>p\<^esub>  \<equiv> (Open (p, One))"

abbreviation close_bracket1' :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("]\<^sup>1\<^bsub>_\<^esub>") where
  "]\<^sup>1\<^bsub>p\<^esub> \<equiv> (Close (p, One))"

abbreviation open_bracket2' :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("[\<^sup>2\<^bsub>_\<^esub>") where
  "[\<^sup>2\<^bsub>p\<^esub> \<equiv> (Open (p, Two))"

abbreviation close_bracket2' :: "('n,'t) prod \<Rightarrow> ('n,'t) bracket3" ("]\<^sup>2\<^bsub>_\<^esub> ") where
  "]\<^sup>2\<^bsub>p\<^esub> \<equiv> (Close (p, Two))"

text \<open>Nice LaTeX rendering:\<close>

notation (latex output) open_bracket1 ("\<^latex>\<open>$[^1_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) open_bracket1' ("\<^latex>\<open>$[^1_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) open_bracket2 ("\<^latex>\<open>$[^2_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) open_bracket2' ("\<^latex>\<open>$[^2_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) close_bracket1 ("\<^latex>\<open>$]^1_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) close_bracket1' ("\<^latex>\<open>$]^1_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) close_bracket2 ("\<^latex>\<open>$]^2_{\<close>_\<^latex>\<open>}$\<close>")
notation (latex output) close_bracket2' ("\<^latex>\<open>$]^2_{\<close>_\<^latex>\<open>}$\<close>")


subsection \<open>Transformation\<close>

abbreviation wrap1 :: \<open>'n \<Rightarrow> 't \<Rightarrow> ('n, ('n,'t) bracket3) syms\<close> where
  \<open>wrap1 A a \<equiv> 
       [ Tm [\<^sup>1\<^bsub>(A, [Tm a])\<^esub>,       
         Tm ]\<^sup>1\<^bsub>(A, [Tm a])\<^esub>, 
         Tm [\<^sup>2\<^bsub>(A, [Tm a])\<^esub>,       
         Tm ]\<^sup>2\<^bsub>(A, [Tm a])\<^esub>  ]\<close>

abbreviation wrap2 :: \<open>'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n, ('n,'t) bracket3) syms\<close> where
  \<open>wrap2 A B C \<equiv> 
       [ Tm [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>, 
         Nt B, 
         Tm ]\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>, 

         Tm [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub>, 
         Nt C, 
         Tm ]\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub>  ]\<close>

text\<open>The transformation of old productions to new productions used in the proof:\<close>

fun transform_rhs :: "'n \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, ('n,'t) bracket3) syms" where
  \<open>transform_rhs A [Tm a] = wrap1 A a\<close> | 
  \<open>transform_rhs A [Nt B, Nt C] = wrap2 A B C\<close>

text \<open>The last equation is only added to permit us to state lemmas about \<close>

fun transform_prod :: "('n, 't) prod \<Rightarrow> ('n, ('n,'t) bracket3) prod" where
  \<open>transform_prod (A, \<alpha>) = (A, transform_rhs A \<alpha>)\<close>


subsection\<open>Homomorphisms\<close>

text\<open>Definition of a monoid-homomorphism where multiplication is \<open>(@)\<close>:\<close>
definition hom_list :: \<open>('a list \<Rightarrow> 'b list) \<Rightarrow> bool\<close> where
\<open>hom_list h = (\<forall>a b. h (a @ b) = h a @ h b)\<close>

lemma hom_list_Nil: "hom_list h \<Longrightarrow> h [] = []"
  unfolding hom_list_def by (metis self_append_conv)

text\<open>The homomorphism on single brackets:\<close>
fun the_hom1 :: \<open>('n,'t) bracket3 \<Rightarrow> 't list\<close> where
  \<open>the_hom1 [\<^sup>1\<^bsub>(A, [Tm a])\<^esub> = [a]\<close> | 
  \<open>the_hom1 _ = []\<close> 

text\<open>The homomorphism on single bracket symbols:\<close>
fun the_hom_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n,'t) sym list\<close> where
  \<open>the_hom_sym (Tm [\<^sup>1\<^bsub>(A, [Tm a])\<^esub>) = [Tm a]\<close> | 
  \<open>the_hom_sym (Nt A) = [Nt A]\<close> | 
  \<open>the_hom_sym _ = []\<close>

text\<open>The homomorphism on bracket words:\<close>
fun the_hom :: \<open>('n,'t) bracket3 list \<Rightarrow> 't list \<close> ("\<h>") where
  \<open>the_hom l = concat (map the_hom1 l)\<close>

text\<open>The homomorphism extended to symbols:\<close>
fun the_hom_syms :: \<open>('n, ('n,'t) bracket3) syms \<Rightarrow> ('n,'t) syms\<close> where
  \<open>the_hom_syms l = concat (map the_hom_sym l)\<close>

notation the_hom ("\<h>")
notation the_hom_syms ("\<h>\<s>")

lemma the_hom_syms_hom: \<open>\<h>\<s> (l1 @ l2) = \<h>\<s> l1 @ \<h>\<s> l2\<close>
  by simp

lemma the_hom_syms_keep_var: \<open>\<h>\<s> [(Nt A)] = [Nt A]\<close> 
  by simp 

lemma the_hom_syms_tms_inj: \<open>\<h>\<s> w = map Tm m \<Longrightarrow> \<exists>w'. w = map Tm w'\<close> 
proof(induction w arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then obtain w' where \<open>w = map Tm w'\<close> 
    by (metis (no_types, opaque_lifting) append_Cons append_Nil map_eq_append_conv the_hom_syms_hom)
  then obtain a' where \<open>a = Tm a'\<close> 
  proof -
    assume a1: "\<And>a'. a = Tm a' \<Longrightarrow> thesis"
    have f2: "\<forall>ss s. [s::('a, ('a,'b) bracket3) sym] @ ss = s # ss" 
      by auto
    have "\<forall>ss s. (s::('a, 'b) sym) # ss = [s] @ ss" 
      by simp
    then show ?thesis using f2 a1 by (metis sym.exhaust sym.simps(4) Cons.prems map_eq_Cons_D the_hom_syms_hom the_hom_syms_keep_var)
  qed
  then show \<open>\<exists>w'. a # w = map Tm w'\<close> 
    by (metis List.list.simps(9) \<open>w = map Tm w'\<close>)
qed

text\<open>Helper for showing the upcoming lemma:\<close>
lemma helper: \<open>the_hom_sym (Tm x) = map Tm (the_hom1 x)\<close>
  by(induction x rule: the_hom1.induct)(auto split: list.splits sym.splits)

text\<open>Show that the extension really is an extension in some sense:\<close>
lemma h_eq_h_ext: \<open>\<h>\<s> (map Tm x) = map Tm (\<h> x)\<close>
proof(induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case using helper[of a] by simp
qed

lemma the_hom1_strip: \<open>(the_hom_sym x') = map Tm w \<Longrightarrow> the_hom1 (destTm x') = w\<close>
  by(induction x' rule: the_hom_sym.induct; auto)

lemma the_hom1_strip2: \<open>concat (map the_hom_sym w') = map Tm w  \<Longrightarrow> concat (map (the_hom1 \<circ> destTm) w') = w\<close>
proof(induction w' arbitrary: w)
  case Nil
  then show ?case by simp
next
  case (Cons a w')
  then show ?case
    by(auto simp: the_hom1_strip map_eq_append_conv append_eq_map_conv)
qed

lemma h_eq_h_ext2:
  assumes \<open>\<h>\<s> w' = (map Tm w)\<close> 
  shows \<open>\<h> (map destTm w') = w\<close>
using assms by (simp add: the_hom1_strip2)



section\<open>The Regular Language\<close>

text\<open>The regular Language @{term \<open>Reg\<close>} will be an intersection of 5 Languages.
The languages \<open>2, 3 ,4\<close> are defined each via a relation \<open>P2, P3, P4\<close> on neighbouring letters and 
lifted to a language via @{term \<open>successively\<close>}. 
Language \<open>1\<close> is an intersection of another such lifted relation \<open>P1'\<close> and a 
condition on the last letter (if existent).
Language \<open>5\<close> is a condition on the first letter (and requires it to exist). 
It takes a term of type \<open>'n\<close> (the original variable type) as parameter.

Additionally a version of each language (taking symbols as input) is defined 
which allows arbitrary interspersion of nonterminals.

As this interspersion weakens the description, the symbol version of the regular language (@{term \<open>Reg_sym\<close>})
is defined using two additional languages lifted from \<open>P7\<close> and \<open>P8\<close>. These vanish when restricted to
words only containing terminals.

As stated in the introductory text, these languages will only be regular, when constrained to a finite bracket set.
The theorems about this, are in the later section \<open>Showing Regularity\<close>.
\<close>


subsection\<open>\<open>P1\<close>\<close>

text\<open>\<open>P1\<close> will define a predicate on string elements. 
It will be true iff each \<open>]\<^sup>1\<^sub>p\<close> is directly followed by \<open>[\<^sup>2\<^sub>p\<close>.
 That also means \<open>]\<^sup>1\<^sub>p\<close> cannot be the end of the string.\<close>

text\<open>But first we define a helper function, that only captures the neighbouring condition for two strings:\<close>
fun P1' :: \<open>('n,'t) bracket3 \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool\<close> where
  \<open>P1' ]\<^sup>1\<^sub>p [\<^sup>2\<^sub>p' = (p = p')\<close> | 
  \<open>P1' ]\<^sup>1\<^sub>p y  = False\<close> | 
  \<open>P1' x y = True\<close>

text\<open>A version of @{term \<open>P1'\<close>} for symbols, i.e. strings that may still contain Nt's:\<close>
fun P1'_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n, ('n,'t) bracket3) sym \<Rightarrow> bool\<close> where
  \<open>P1'_sym (Tm ]\<^sup>1\<^sub>p) (Tm [\<^sup>2\<^sub>p')  = (p = p')\<close> | 
  \<open>P1'_sym (Tm ]\<^sup>1\<^sub>p) y  = False\<close> | 
  \<open>P1'_sym x y = True\<close>

lemma P1'D[simp]:
  \<open>P1' ]\<^sup>1\<^sub>p r \<longleftrightarrow> r = [\<^sup>2\<^sub>p\<close> 
by(induction \<open>]\<^sup>1\<^sub>p\<close> \<open>r\<close> rule: P1'.induct) auto

text\<open>Asserts that \<open>P1'\<close> holds for every pair in xs, and that xs doesnt end in \<open>]\<^sup>1\<^sub>p\<close>:\<close>
fun P1 :: "('n, 't) bracket3 list \<Rightarrow> bool" where
  \<open>P1 xs = ((successively P1' xs) \<and> (if xs \<noteq> [] then (\<nexists>p. last xs = ]\<^sup>1\<^sub>p) else True))\<close>

text\<open>Asserts that \<open>P1'\<close> holds for every pair in xs, and that xs doesnt end in \<open>Tm ]\<^sup>1\<^sub>p\<close>:\<close>
fun P1_sym where
  \<open>P1_sym xs = ((successively P1'_sym xs) \<and> (if xs \<noteq> [] then (\<nexists>p. last xs = Tm ]\<^sup>1\<^sub>p) else True))\<close>

lemma P1_for_tm_if_P1_sym[dest!]: \<open>P1_sym (map Tm x) \<Longrightarrow> P1 x\<close>
proof(induction x rule: induct_list012)
  case (3 x y zs)
  then show ?case
    by(cases \<open>(Tm x :: ('a, ('a,'b)bracket3) sym, Tm y :: ('a, ('a,'b)bracket3) sym)\<close> rule: P1'_sym.cases) auto  
qed simp_all

lemma P1I[intro]: 
  assumes \<open>successively P1' xs\<close>
    and \<open>\<nexists>p. last xs = ]\<^sup>1\<^sub>p\<close>
  shows \<open>P1 xs\<close>
proof(cases xs)
  case Nil
  then show ?thesis using assms by force
next
  case (Cons a list)
  then show ?thesis using assms by (auto split: version.splits sym.splits prod.splits)
qed

lemma P1_symI[intro]: 
  assumes \<open>successively P1'_sym xs\<close>
    and \<open>\<nexists>p. last xs = Tm ]\<^sup>1\<^sub>p\<close>
  shows \<open>P1_sym xs\<close> 
proof(cases xs rule: rev_cases)
  case Nil
  then show ?thesis by auto
next
  case (snoc ys y)
  then show ?thesis 
    using assms by (cases y) auto
qed

lemma P1_symD[dest]: \<open>P1_sym xs \<Longrightarrow> successively P1'_sym xs\<close> by simp

lemma P1D_not_empty[intro]:
  assumes \<open>xs \<noteq> []\<close>
    and \<open>P1 xs\<close>
  shows \<open>last xs \<noteq> ]\<^sup>1\<^sub>p\<close>
proof-
  from assms have \<open>successively P1' xs \<and> (\<nexists>p. last xs = ]\<^sup>1\<^sub>p)\<close> 
    by simp
  then show ?thesis by blast
qed

lemma P1_symD_not_empty'[intro]:
  assumes \<open>xs \<noteq> []\<close>
    and \<open>P1_sym xs\<close>
  shows \<open>last xs \<noteq> Tm ]\<^sup>1\<^sub>p\<close>
proof-
  from assms have \<open>successively P1'_sym xs \<and> (\<nexists>p. last xs = Tm ]\<^sup>1\<^sub>p)\<close> 
    by simp
  then show ?thesis by blast
qed

lemma P1_symD_not_empty:
  assumes \<open>xs \<noteq> []\<close>
    and \<open>P1_sym xs\<close>
  shows \<open>\<nexists>p. last xs = Tm ]\<^sup>1\<^sub>p\<close> 
  using P1_symD_not_empty'[OF assms] by simp


subsection\<open>\<open>P2\<close>\<close>

text\<open>A \<open>]\<^sup>2\<^sub>\<pi>\<close> is never directly followed by some \<open>[\<close>:\<close>
fun P2 :: \<open>('n,'t) bracket3 \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool\<close> where
  \<open>P2 (Close (p, Two)) (Open (p', v))  = False\<close> | 
  \<open>P2 (Close (p, Two)) y  = True\<close> | 
  \<open>P2 x y = True\<close>

fun P2_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n, ('n,'t) bracket3) sym \<Rightarrow> bool\<close> where
  \<open>P2_sym (Tm (Close (p, Two))) (Tm (Open (p', v)))  = False\<close> | 
  \<open>P2_sym (Tm (Close (p, Two))) y  = True\<close> | 
  \<open>P2_sym x y = True\<close>

lemma P2_for_tm_if_P2_sym[dest]: \<open>successively P2_sym (map Tm x) \<Longrightarrow> successively P2 x\<close>
  apply(induction x rule: induct_list012) 
    apply simp 
   apply simp
  using P2.elims(3) by fastforce 


subsection\<open>\<open>P3\<close>\<close>

text\<open>Each \<open>[\<^sup>1\<^bsub>A\<rightarrow>BC\<^esub>\<close> is directly followed by \<open>[\<^sup>1\<^bsub>B\<rightarrow>_\<^esub>\<close>,
and each \<open>[\<^sup>2\<^bsub>A\<rightarrow>BC\<^esub>\<close> is directly followed by \<open>[\<^sup>1\<^bsub>C\<rightarrow>_\<^esub>\<close>:\<close>
fun P3 :: \<open>('n,'t) bracket3 \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool\<close> where
  \<open>P3 [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub> (p, ((X,y), t)) = (p = True \<and> t = One \<and> X = B)\<close> |
  \<open>P3 [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub> (p, ((X,y), t)) = (p = True \<and> t = One \<and> X = C)\<close> |
  \<open>P3 x y = True\<close>

text\<open>Each \<open>[\<^sup>1\<^bsub>A\<rightarrow>BC\<^esub>\<close> is directly followed \<open>[\<^sup>1\<^bsub>B\<rightarrow>_\<^esub>\<close> or \<open>Nt B\<close>,
and each \<open>[\<^sup>2\<^bsub>A\<rightarrow>BC\<^esub>\<close> is directly followed by \<open>[\<^sup>1\<^bsub>C\<rightarrow>_\<^esub>\<close> or \<open>Nt C\<close>:\<close>
fun P3_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n, ('n,'t) bracket3) sym \<Rightarrow> bool\<close> where
  \<open>P3_sym (Tm [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>) (Tm (p, ((X,y), t))) = (p = True \<and> t = One \<and> X = B)\<close> |
  \<comment> \<open>Not obvious: the case \<open>(Tm [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>) Nt X\<close> is set to True with the catch all\<close>
  \<open>P3_sym (Tm [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>) (Nt X) = (X = B)\<close> | 

\<open>P3_sym (Tm [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub>) (Tm (p, ((X,y), t))) = (p = True \<and> t = One \<and> X = C)\<close> | 
\<open>P3_sym (Tm [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub>) (Nt X) = (X = C)\<close> | 
\<open>P3_sym x y = True\<close>

lemma P3D1[dest]:
  fixes r::\<open>('n,'t) bracket3\<close>
  assumes \<open>P3 [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub> r\<close>
  shows \<open>\<exists>l. r = [\<^sup>1\<^bsub>(B, l)\<^esub>\<close>
  using assms by(induction \<open>[\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>:: ('n,'t) bracket3\<close> r rule: P3.induct) auto 

lemma P3D2[dest]:
  fixes r::\<open>('n,'t) bracket3\<close>
  assumes \<open>P3 [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub> r\<close>
  shows \<open>\<exists>l. r = [\<^sup>1\<^bsub>(C, l)\<^esub>\<close>
  using assms by(induction \<open>[\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>:: ('n,'t) bracket3\<close> r rule: P3.induct) auto 

lemma P3_for_tm_if_P3_sym[dest]: \<open>successively P3_sym (map Tm x) \<Longrightarrow> successively P3 x\<close>
proof(induction x rule: induct_list012)
  case (3 x y zs)
  then show ?case
    by(cases \<open>(Tm x :: ('a, ('a,'b) bracket3) sym, Tm y :: ('a, ('a,'b) bracket3) sym)\<close> rule: P3_sym.cases) auto
qed simp_all


subsection\<open>\<open>P4\<close>\<close>

text\<open>Each \<open>[\<^sup>1\<^bsub>A\<rightarrow>a\<^esub>\<close> is directly followed by \<open>]\<^sup>1\<^bsub>A\<rightarrow>a\<^esub>\<close>
and each \<open>[\<^sup>2\<^bsub>A\<rightarrow>a\<^esub>\<close> is directly followed by \<open>]\<^sup>2\<^bsub>A\<rightarrow>a\<^esub>\<close>:\<close>
fun P4 :: \<open>('n,'t) bracket3 \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool\<close> where
  \<open>P4 (Open ((A, [Tm a]), s)) (p, ((X, y), t)) = (p = False \<and> X = A \<and> y = [Tm a] \<and> s = t)\<close> |
  \<open>P4 x y = True\<close>

text\<open>Each \<open>[\<^sup>1\<^bsub>A\<rightarrow>a\<^esub>\<close> is directly followed by \<open>]\<^sup>1\<^bsub>A\<rightarrow>a\<^esub>\<close>
and each \<open>[\<^sup>2\<^bsub>A\<rightarrow>a\<^esub>\<close> is directly followed by \<open>]\<^sup>2\<^bsub>A\<rightarrow>a\<^esub>\<close>:\<close>
fun P4_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n, ('n,'t) bracket3) sym \<Rightarrow> bool\<close> where
  \<open>P4_sym (Tm (Open ((A, [Tm a]), s))) (Tm (p, ((X, y), t))) = (p = False \<and> X = A \<and> y = [Tm a] \<and> s = t)\<close> | 
  \<open>P4_sym (Tm (Open ((A, [Tm a]), s))) (Nt X) = False\<close> | 
  \<open>P4_sym x y = True\<close>

lemma P4D[dest]:
  fixes r::\<open>('n,'t) bracket3\<close>
  assumes \<open>P4 (Open ((A, [Tm a]), v)) r\<close>
  shows \<open>r = Close ((A, [Tm a]), v)\<close> 
  using assms by(induction \<open>(Open ((A, [Tm a]), v))::('n,'t) bracket3\<close> r rule: P4.induct) auto

lemma P4_for_tm_if_P4_sym[dest]: \<open>successively P4_sym (map Tm x) \<Longrightarrow> successively P4 x\<close>
proof(induction x rule: induct_list012)
  case (3 x y zs)
  then show ?case
    by(cases \<open>(Tm x :: ('a, ('a,'b) bracket3) sym, Tm y :: ('a, ('a,'b) bracket3) sym)\<close> rule: P4_sym.cases) auto
qed simp_all


subsection\<open>\<open>P5\<close>\<close>

text\<open>\<open>P5 A x\<close> holds, iff there exists some \<open>y\<close> such that \<open>x\<close> begins with \<open>[\<^sup>1\<^bsub>A\<rightarrow>y\<^esub>\<close>:\<close>
fun P5 :: \<open>'n \<Rightarrow> ('n,'t) bracket3 list \<Rightarrow> bool\<close> where
  \<open>P5 A [] = False\<close> | 
  \<open>P5 A ([\<^sup>1\<^bsub>(X,x)\<^esub> # xs) = (X = A)\<close> | 
  \<open>P5 A (x # xs) = False\<close>

text\<open>\<open>P5_sym A x\<close> holds, iff either there exists some \<open>y\<close> such that \<open>x\<close> begins with \<open>[\<^sup>1\<^bsub>A\<rightarrow>y\<^esub>\<close>, or if it begins with \<open>Nt A\<close>:\<close>
fun P5_sym :: \<open>'n \<Rightarrow> ('n, ('n,'t) bracket3) syms \<Rightarrow> bool\<close> where
  \<open>P5_sym A [] = False\<close> | 
  \<open>P5_sym A (Tm [\<^sup>1\<^bsub>(X,x)\<^esub> # xs) = (X = A)\<close> | 
  \<open>P5_sym A ((Nt X) # xs) = (X = A)\<close> | 
  \<open>P5_sym A (x # xs) = False\<close>

lemma P5D[dest]: 
  assumes \<open>P5 A x\<close>
  shows \<open>\<exists>y. hd x = [\<^sup>1\<^bsub>(A,y)\<^esub>\<close>
  using assms by(induction A x rule: P5.induct) auto

lemma P5_symD[dest]: 
  assumes \<open>P5_sym A x\<close>
  shows \<open>(\<exists>y. hd x = Tm [\<^sup>1\<^bsub>(A,y)\<^esub>) \<or> hd x = Nt A\<close>
  using assms by(induction A x rule: P5_sym.induct) auto

lemma P5_for_tm_if_P5_sym[dest]: \<open>P5_sym A (map Tm x) \<Longrightarrow> P5 A x\<close>
  by(induction x) auto


subsection\<open>\<open>P7\<close> and \<open>P8\<close>\<close>

text\<open>\<open>(successively P7_sym) w\<close> iff \<open>Nt Y\<close> is directly preceded by some \<open>Tm [\<^sup>1\<^bsub>A\<rightarrow>YC\<^esub>\<close> or \<open>Tm [\<^sup>2\<^bsub>A\<rightarrow>BY\<^esub>\<close> in w:\<close>
fun P7_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n, ('n,'t) bracket3) sym \<Rightarrow> bool\<close> where
  \<open>P7_sym (Tm (b,(A, [Nt B, Nt C]), v )) (Nt Y) = (b = True \<and> ((Y = B \<and> v = One) \<or> (Y=C \<and> v = Two)) )\<close> | 
  \<open>P7_sym x (Nt Y) = False\<close> | 
  \<open>P7_sym x y = True\<close>

lemma P7_symD[dest]: 
  fixes x:: \<open>('n, ('n,'t) bracket3) sym\<close>
  assumes \<open>P7_sym x (Nt Y)\<close>
  shows \<open>(\<exists>A C. x = Tm [\<^sup>1\<^bsub>(A,[Nt Y, Nt C])\<^esub>) \<or> (\<exists>A B. x = Tm [\<^sup>2\<^bsub>(A,[Nt B, Nt Y])\<^esub>)\<close>
  using assms by(induction x \<open>Nt Y::('n, ('n,'t) bracket3) sym\<close> rule: P7_sym.induct) auto

text\<open>\<open>(successively P8_sym) w\<close> iff \<open>Nt Y\<close> is directly followed by some \<open>]\<^sup>1\<^bsub>A\<rightarrow>YC\<^esub>\<close> or \<open>]\<^sup>2\<^bsub>A\<rightarrow>BY\<^esub>\<close> in w:\<close>
fun P8_sym :: \<open>('n, ('n,'t) bracket3) sym \<Rightarrow> ('n, ('n,'t) bracket3) sym \<Rightarrow> bool\<close> where
  \<open>P8_sym (Nt Y) (Tm (b,(A, [Nt B, Nt C]), v ))  = (b = False \<and> ( (Y = B \<and> v = One) \<or> (Y=C \<and> v = Two)) )\<close> | 
  \<open>P8_sym (Nt Y) x = False\<close> | 
  \<open>P8_sym x y = True\<close>

lemma P8_symD[dest]: 
  fixes x:: \<open>('n, ('n,'t) bracket3) sym\<close>
  assumes \<open>P8_sym (Nt Y) x\<close>
  shows \<open>(\<exists>A C. x = Tm ]\<^sup>1\<^bsub>(A,[Nt Y, Nt C])\<^esub>) \<or> (\<exists>A B. x = Tm ]\<^sup>2\<^bsub>(A,[Nt B, Nt Y])\<^esub>)\<close>
  using assms by(induction \<open>Nt Y::('n, ('n,'t) bracket3) sym\<close> x rule: P8_sym.induct) auto


subsection\<open>\<open>Reg\<close> and \<open>Reg_sym\<close>\<close>

text\<open>This is the regular language, where one takes the Start symbol as a parameter, and then has the searched for \<open>R := R\<^sub>A\<close>:\<close>
definition Reg :: \<open>'n \<Rightarrow> ('n,'t) bracket3 list set\<close> where
  \<open>Reg A = {x. (P1 x) \<and> 
    (successively P2 x) \<and> 
    (successively P3 x) \<and> 
    (successively P4 x) \<and> 
    (P5 A x)}\<close>

lemma RegI[intro]:
  assumes \<open>(P1 x)\<close> 
    and \<open>(successively P2 x)\<close> 
    and \<open>(successively P3 x)\<close> 
    and \<open>(successively P4 x)\<close> 
    and \<open>(P5 A x)\<close>
  shows \<open>x \<in> Reg A\<close>
  using assms unfolding Reg_def by blast

lemma RegD[dest]:
  assumes \<open>x \<in> Reg A\<close>
  shows \<open>(P1 x)\<close> 
    and \<open>(successively P2 x)\<close> 
    and \<open>(successively P3 x)\<close> 
    and \<open>(successively P4 x)\<close> 
    and \<open>(P5 A x)\<close>
  using assms unfolding Reg_def by blast+

text\<open>A version of \<open>Reg\<close> for symbols, i.e. strings that may still contain Nt's. 
It has 2 more Properties \<open>P7\<close> and \<open>P8\<close> that vanish for pure terminal strings:\<close>
definition Reg_sym :: \<open>'n \<Rightarrow> ('n, ('n,'t) bracket3) syms set\<close> where
  \<open>Reg_sym A = {x. (P1_sym x) \<and> 
     (successively P2_sym x) \<and> 
     (successively P3_sym x) \<and> 
     (successively P4_sym x) \<and> 
     (P5_sym A x) \<and> 
     (successively P7_sym x) \<and> 
     (successively P8_sym x)}\<close>

lemma Reg_symI[intro]:
  assumes \<open>P1_sym x\<close> 
    and \<open>successively P2_sym x\<close> 
    and \<open>successively P3_sym x\<close> 
    and \<open>successively P4_sym x\<close> 
    and \<open>P5_sym A x\<close> 
    and \<open>(successively P7_sym x)\<close> 
    and \<open>(successively P8_sym x)\<close>
  shows \<open>x \<in> Reg_sym A\<close>
  using assms unfolding Reg_sym_def by blast

lemma Reg_symD[dest]:
  assumes \<open>x \<in> Reg_sym A\<close>
  shows \<open>P1_sym x\<close> 
    and \<open>successively P2_sym x\<close> 
    and \<open>successively P3_sym x\<close> 
    and \<open>successively P4_sym x\<close> 
    and \<open>P5_sym A x\<close> 
    and \<open>(successively P7_sym x)\<close> 
    and \<open>(successively P8_sym x)\<close>
  using assms unfolding Reg_sym_def by blast+

lemma Reg_for_tm_if_Reg_sym[dest]: \<open>(map Tm x) \<in> Reg_sym A \<Longrightarrow> x \<in> Reg A\<close> 
by(rule RegI) auto



section\<open>Showing Regularity\<close>

context locale_P
begin

abbreviation brackets::\<open>('n,'t) bracket3 list set\<close> where
  \<open>brackets \<equiv> {bs. \<forall>(_,p,_) \<in> set bs. p \<in> P}\<close>

text\<open>This is needed for the construction that shows P2,P3,P4 regular.\<close>
datatype 'a state = start | garbage |  letter 'a

definition allStates :: \<open>('n,'t) bracket3 state set \<close>where
  \<open>allStates = { letter (br,(p,v)) | br p v. p \<in> P } \<union> {start, garbage}\<close>

lemma allStatesI: \<open>p \<in> P \<Longrightarrow> letter (br,(p,v)) \<in> allStates\<close> 
  unfolding allStates_def by blast

lemma start_in_allStates[simp]: \<open>start \<in> allStates\<close> 
  unfolding allStates_def by blast

lemma garbage_in_allStates[simp]: \<open>garbage \<in> allStates\<close> 
  unfolding allStates_def by blast

lemma finite_allStates_if: 
  shows \<open>finite( allStates)\<close>
proof -
  define S::\<open>('n,'t) bracket3 state set\<close> where  "S = {letter (br, (p, v)) | br p v. p \<in> P}"
  have 1:"S = (\<lambda>(br, p, v). letter (br, (p, v))) ` ({True, False} \<times> P \<times> {One, Two})" 
    unfolding S_def by (auto simp: image_iff intro: version.exhaust)
  have "finite ({True, False} \<times> P \<times> {One, Two})" 
    using finiteP by simp
  then have \<open>finite ((\<lambda>(br, p, v). letter (br, (p, v))) ` ({True, False} \<times> P \<times> {One, Two}))\<close> 
    by blast
  then have \<open>finite S\<close> 
    unfolding 1 by blast
  then have "finite (S \<union> {start, garbage})" 
    by simp
  then show \<open>finite (allStates)\<close> 
    unfolding allStates_def S_def by blast
qed

end (* P *)


subsection\<open>An automaton for \<open>{xs. successively Q xs \<and> xs \<in> brackets P}\<close>\<close>

locale successivelyConstruction = locale_P where P = P for P :: "('n,'t) Prods" +
fixes Q :: "('n,'t) bracket3 \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool" \<comment> \<open>e.g. P2\<close>
begin

fun succNext :: \<open>('n,'t) bracket3 state \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> ('n,'t) bracket3 state\<close> where 
  \<open>succNext garbage _ = garbage\<close> | 
  \<open>succNext start (br', p', v') = (if p' \<in> P then letter (br', p',v') else garbage )\<close> | 
  \<open>succNext (letter (br, p, v)) (br', p', v') =  (if Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P then letter (br',p',v') else garbage)\<close>

theorem succNext_induct[case_names garbage startp startnp letterQ letternQ]:
  fixes R :: "('n,'t) bracket3 state \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool"
  fixes a0 :: "('n,'t) bracket3 state"
    and a1 :: "('n,'t) bracket3"
  assumes "\<And>u. R garbage u"
    and "\<And>br' p' v'. p' \<in> P \<Longrightarrow> R state.start (br', p', v')"
    and "\<And>br' p' v'. p' \<notin> P \<Longrightarrow> R state.start (br', p', v')"
    and "\<And>br p v br' p' v'. Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P \<Longrightarrow> R (letter (br, p, v)) (br', p', v')"
    and "\<And>br p v br' p' v'. \<not>(Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P) \<Longrightarrow> R (letter (br, p, v)) (br', p', v')"
  shows "R a0 a1"
by (metis assms prod_cases3 state.exhaust)

abbreviation aut where \<open>aut \<equiv> \<lparr>dfa'.states = allStates,
                     init  = start,
                     final = (allStates - {garbage}),
                     nxt   = succNext \<rparr>\<close>

interpretation aut : dfa' aut
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by simp 
next
  case 2
  then show ?case by simp
next
  case (3 q x)
  then show ?case 
    by(induction rule: succNext_induct[of _ q x]) (auto simp: allStatesI)
next
  case 4
  then show ?case 
    using finiteP by (simp add: finite_allStates_if)
qed

lemma nextl_in_allStates[intro,simp]: \<open>q \<in> allStates \<Longrightarrow> aut.nextl q ys \<in> allStates\<close>
  using aut.nxt by(induction ys arbitrary: q) auto

lemma nextl_garbage[simp]: \<open>aut.nextl garbage xs = garbage\<close> 
by(induction xs) auto

lemma drop_right: \<open>xs@ys \<in> aut.language \<Longrightarrow> xs \<in> aut.language\<close>
proof(induction ys)
  case (Cons a ys)
  then have \<open>xs @ [a] \<in> aut.language\<close> 
    using aut.language_def aut.nextl_app by fastforce
  then have \<open>xs \<in> aut.language\<close> 
    using aut.language_def by force
  then show ?case by blast
qed auto

lemma state_after1[iff]: \<open>(succNext q a \<noteq> garbage) = (succNext q a = letter a)\<close>
by(induction q a rule: succNext.induct) (auto split: if_splits)

lemma state_after_in_P[intro]: \<open>succNext q (br, p, v) \<noteq> garbage \<Longrightarrow> p \<in> P\<close>
by(induction q \<open>(br, p, v)\<close> rule: succNext_induct) auto 

lemma drop_left_general: \<open>aut.nextl start ys = garbage \<Longrightarrow> aut.nextl q ys = garbage\<close>
proof(induction ys)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  show ?case
    by(rule succNext.elims[of q a])(use Cons.prems in auto)
qed

lemma drop_left: \<open>xs@ys \<in> aut.language \<Longrightarrow> ys \<in> aut.language\<close>
  unfolding aut.language_def
  by(induction xs arbitrary: ys) (auto dest: drop_left_general)

lemma empty_in_aut: \<open>[] \<in> aut.language\<close> 
  unfolding aut.language_def by simp  

lemma singleton_in_aut_iff: \<open>[(br, p, v)] \<in> aut.language \<longleftrightarrow> p \<in> P\<close> 
  unfolding aut.language_def by simp

lemma duo_in_aut_iff: \<open>[(br, p, v), (br', p', v')] \<in> aut.language \<longleftrightarrow> Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P\<close> 
  unfolding aut.language_def by auto 

lemma trio_in_aut_iff: \<open>(br, p, v) # (br', p', v') # zs \<in> aut.language \<longleftrightarrow>   Q (br,p,v) (br',p',v')  \<and>   p \<in> P \<and>   p' \<in> P \<and>   (br',p',v') # zs \<in> aut.language\<close> 
proof(standard, goal_cases)
  case 1
  with drop_left have *:\<open>(br', p', v') # zs \<in> aut.language\<close> 
    by (metis append_Cons append_Nil)
  from drop_right 1 have \<open>[(br, p, v), (br', p', v')] \<in> aut.language\<close> 
    by simp
  with duo_in_aut_iff have **:\<open>Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P\<close> 
    by blast
  from * ** show ?case by simp
next
  case 2
  then show ?case unfolding aut.language_def by auto
qed

lemma aut_lang_iff_succ_Q: \<open>(successively Q xs \<and>  xs \<in> brackets) \<longleftrightarrow> (xs \<in> aut.language)\<close>
proof(induction xs rule: induct_list012)
  case 1
  then show ?case using empty_in_aut by auto
next
  case (2 x)
  then show ?case
    using singleton_in_aut_iff by auto
next
  case (3 x y zs)
  show ?case
  proof(cases x)
    case (fields br p v)
    then have x_eq: \<open>x = (br, p, v)\<close> 
      by simp
    then show ?thesis
    proof(cases y)
      case (fields br' p' v')
      then have y_eq: \<open>y = (br', p', v')\<close> 
        by simp
      have \<open>(x # y # zs \<in> aut.language) \<longleftrightarrow> Q (br,p,v) (br',p',v')  \<and>   p \<in> P \<and>   p' \<in> P \<and>   (br',p',v') # zs \<in> aut.language\<close> 
        unfolding x_eq y_eq using trio_in_aut_iff by blast
      also have \<open>...     \<longleftrightarrow> Q (br,p,v) (br',p',v')  \<and>   p \<in> P \<and>   p' \<in> P \<and>  (successively Q ((br',p',v') # zs)  \<and> (br',p',v') # zs \<in> brackets)\<close> 
        using 3 unfolding x_eq y_eq by blast
      also have \<open>...     \<longleftrightarrow> successively Q ((br,p,v) # (br',p',v') #zs) \<and> (br,p,v) # (br',p',v') # zs \<in> brackets\<close> 
        by force
      also have \<open>...     \<longleftrightarrow> successively Q (x # y #zs) \<and> x # y # zs \<in> brackets\<close> 
        unfolding x_eq y_eq by blast
      finally show ?thesis by blast
    qed
  qed
qed

lemma aut_language_reg: \<open>regular aut.language\<close>
by (meson aut.regular)

corollary regular_successively_inter_brackets: \<open>regular {xs. successively Q xs \<and>  xs \<in> brackets}\<close> 
  using aut_language_reg aut_lang_iff_succ_Q by auto

end (* successivelyConstruction *)


subsection\<open>Regularity of \<open>P2\<close>, \<open>P3\<close> and \<open>P4\<close>\<close>

context locale_P
begin

lemma P2_regular:
  shows \<open>regular {xs. successively P2 xs \<and>  xs \<in> brackets} \<close>
proof-
  interpret successivelyConstruction P P2
    by(unfold_locales)
  show ?thesis using regular_successively_inter_brackets by blast
qed

lemma P3_regular:
  \<open>regular {xs. successively P3 xs \<and>  xs \<in> brackets} \<close>
proof-
  interpret successivelyConstruction P P3 
    by(unfold_locales) 
  show ?thesis using regular_successively_inter_brackets by blast
qed

lemma P4_regular:
  \<open>regular {xs. successively P4 xs \<and>  xs \<in> brackets }\<close>
proof-
  interpret successivelyConstruction P P4
    by(unfold_locales) 
  show ?thesis using regular_successively_inter_brackets by blast
qed


subsection\<open>An automaton for \<open>P1\<close>\<close>

text\<open>More Precisely, for the \<open>if not empty, then doesnt end in (Close_,1)\<close> part. 
Then intersect with the other construction for \<open>P1'\<close> to get \<open>P1\<close> regular.\<close>

datatype P1_State = last_ok | last_bad | garbage 

text\<open>The good ending letters, are those that are not of the form \<open>(Close _ , 1)\<close>.\<close>
fun good where
  \<open>good ]\<^sup>1\<^sub>p  = False\<close> | 
  \<open>good (br, p, v) = True\<close>

fun nxt1 :: \<open>P1_State \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> P1_State\<close> where 
  \<open>nxt1 garbage _ = garbage\<close> | 
  \<open>nxt1 last_ok  (br, p, v) = (if p \<notin> P then garbage else (if good (br, p, v) then last_ok else last_bad))\<close> | 
  \<open>nxt1 last_bad (br, p, v) = (if p \<notin> P then garbage else (if good (br, p, v) then last_ok else last_bad))\<close>

theorem nxt1_induct[case_names garbage startp startnp letterQ letternQ]:
  fixes R :: "P1_State \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool"
  fixes a0 :: "P1_State"
    and a1 :: "('n,'t) bracket3"
  assumes "\<And>u. R garbage u"
    and "\<And>br p v. p \<notin> P \<Longrightarrow> R last_ok (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> good (br, p, v) \<Longrightarrow> R last_ok (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> \<not>(good (br, p, v)) \<Longrightarrow> R last_ok (br, p, v)"
    and "\<And>br p v. p \<notin> P \<Longrightarrow> R last_bad (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> good (br, p, v) \<Longrightarrow> R last_bad (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> \<not>(good (br, p, v)) \<Longrightarrow> R last_bad (br, p, v)"
  shows "R a0 a1"
by (metis (full_types) P1_State.exhaust assms prod_induct3)

abbreviation p1_aut  where \<open>p1_aut \<equiv> \<lparr>dfa'.states = {last_ok, last_bad, garbage},
                     init  = last_ok,
                     final = {last_ok},
                     nxt   = nxt1\<rparr>\<close>

interpretation p1_aut : dfa' p1_aut
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by simp 
next
  case 2
  then show ?case by simp
next
  case (3 q x)
  then show ?case 
    by(induction rule: nxt1_induct[of _ q x]) auto
next
  case 4
  then show ?case by simp
qed

lemma nextl_garbage_iff[simp]: \<open>p1_aut.nextl last_ok xs = garbage \<longleftrightarrow> xs \<notin> brackets\<close>
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by simp 
next
  case (snoc x xs)
  then have \<open>xs @ [x] \<notin> brackets \<longleftrightarrow> (xs \<notin> brackets \<or> [x] \<notin> brackets)\<close> 
    by auto
  moreover have \<open>(p1_aut.nextl last_ok (xs@[x]) = garbage) \<longleftrightarrow> 
    (p1_aut.nextl last_ok xs = garbage) \<or> ((p1_aut.nextl last_ok (xs @ [x]) = garbage) \<and> (p1_aut.nextl last_ok (xs) \<noteq> garbage))\<close> 
    by auto
  ultimately show ?case using snoc
    apply (cases x)
     apply (simp)
    by (smt (z3) P1_State.exhaust P1_State.simps(3,5) nxt1.simps(2,3))
qed

lemma lang_descr_full: 
  \<open>(p1_aut.nextl last_ok xs = last_ok \<longleftrightarrow> (xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets))) \<and> 
 (p1_aut.nextl last_ok xs = last_bad \<longleftrightarrow> ((xs \<noteq> [] \<and> \<not>good (last xs) \<and> xs \<in> brackets)))\<close>
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
  proof(cases \<open>p1_aut.nextl last_ok (xs@[x]) = garbage\<close>)
    case True
    then show ?thesis using nextl_garbage_iff by fastforce
  next
    case False
    then have br: \<open>xs \<in> brackets\<close> \<open>[x] \<in> brackets\<close>
      using nextl_garbage_iff by fastforce+
    with snoc consider \<open>(p1_aut.nextl last_ok xs = last_ok)\<close> | \<open>(p1_aut.nextl last_ok xs = last_bad)\<close> 
      using nextl_garbage_iff by blast
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using br by(cases \<open>good x\<close>) auto 
    next
      case 2
      then show ?thesis using br by(cases \<open>good x\<close>) auto 
    qed
  qed
qed

lemma lang_descr: \<open>xs \<in> p1_aut.language \<longleftrightarrow> (xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets))\<close>
  unfolding p1_aut.language_def using lang_descr_full by auto

lemma good_iff[simp]:\<open>(\<forall>a b. last xs \<noteq> ]\<^sup>1\<^bsub>(a, b)\<^esub>) = good (last xs)\<close> 
  by (metis good.simps(1) good.elims(3) split_pairs)

lemma in_P1_iff: \<open>(P1 xs \<and> xs \<in> brackets) \<longleftrightarrow>  (xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets)) \<and> successively P1' xs \<and>  xs \<in> brackets\<close> 
  using good_iff by auto

corollary P1_eq: \<open>{xs. P1 xs \<and> xs \<in> brackets}  =   
  {xs. successively P1' xs \<and>  xs \<in> brackets}   \<inter>   {xs. xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets)}\<close> 
  using in_P1_iff by blast

lemma P1'_regular:
  shows \<open>regular {xs. successively P1' xs \<and>  xs \<in> brackets} \<close>
proof-
  interpret successivelyConstruction P P1' 
    by(unfold_locales)
  show ?thesis using regular_successively_inter_brackets by blast
qed

lemma aut_language_reg: \<open>regular p1_aut.language\<close>
  using p1_aut.regular by blast 

corollary aux_regular: \<open>regular {xs. xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets)}\<close> 
  using lang_descr aut_language_reg p1_aut.language_def by simp

corollary regular_P1: \<open>regular {xs. P1 xs \<and> xs \<in> brackets}\<close> 
  unfolding P1_eq using P1'_regular aux_regular using regular_Int by blast

end (* P *)


subsection\<open>An automaton for \<open>P5\<close>\<close>

locale P5Construction = locale_P where P=P for P :: "('n,'t)Prods" +
fixes A :: 'n
begin

datatype P5_State = start | first_ok | garbage 

text\<open>The good/ok ending letters, are those that are not of the form \<open>(Close _ , 1)\<close>.\<close>
fun ok where
  \<open>ok (Open ((X, _), One)) = (X = A)\<close> | 
  \<open>ok _ = False\<close>

fun nxt2 :: \<open>P5_State \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> P5_State\<close> where 
  \<open>nxt2 garbage _ = garbage\<close> | 
  \<open>nxt2 start  (br, (X, r), v) = (if (X,r) \<notin> P then garbage else (if ok (br, (X, r), v) then first_ok else garbage))\<close> | 
  \<open>nxt2 first_ok (br, p, v) = (if p \<notin> P then garbage else first_ok)\<close>

theorem nxt2_induct[case_names garbage startnp start_p_ok start_p_nok first_ok_np first_ok_p]:
  fixes R :: "P5_State \<Rightarrow> ('n,'t) bracket3 \<Rightarrow> bool"
  fixes a0 :: "P5_State"
    and a1 :: "('n,'t) bracket3"
  assumes "\<And>u. R garbage u"
    and "\<And>br p v. p \<notin> P \<Longrightarrow> R start (br, p, v)"
    and "\<And>br X r v. (X, r) \<in> P \<and> ok (br, (X, r), v) \<Longrightarrow> R start (br, (X, r), v)"
    and "\<And>br X r v. (X, r) \<in> P \<and> \<not>ok (br, (X, r), v) \<Longrightarrow> R start (br, (X, r), v)"
    and "\<And>br X r v. (X, r) \<notin> P  \<Longrightarrow> R first_ok (br, (X, r), v)"
    and "\<And>br X r v. (X, r) \<in> P  \<Longrightarrow> R first_ok (br, (X, r), v)"
  shows "R a0 a1"
by (metis (full_types, opaque_lifting) P5_State.exhaust assms surj_pair)

abbreviation p5_aut  where \<open>p5_aut \<equiv> \<lparr>dfa'.states = {start, first_ok, garbage},
                     init  = start,
                     final = {first_ok},
                     nxt   = nxt2\<rparr>\<close>

interpretation p5_aut : dfa' p5_aut
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by simp 
next
  case 2
  then show ?case by simp
next
  case (3 q x)
  then show ?case by(induction rule: nxt2_induct[of _ q x]) auto
next
  case 4
  then show ?case by simp
qed

corollary nxt2_start_ok_iff: \<open>ok x \<and> fst(snd x) \<in> P \<longleftrightarrow> nxt2 start x = first_ok\<close>
by(auto elim!: nxt2.elims ok.elims split: if_splits)

lemma empty_not_in_lang[simp]:\<open>[] \<notin> p5_aut.language\<close> 
  unfolding p5_aut.language_def by auto 

lemma singleton_in_lang_iff: \<open>[x] \<in> p5_aut.language \<longleftrightarrow> ok (hd [x]) \<and> [x] \<in> brackets\<close> 
  unfolding p5_aut.language_def using nxt2_start_ok_iff by (cases x) fastforce

lemma singleton_first_ok_iff: \<open>p5_aut.nextl start ([x]) = first_ok \<or> p5_aut.nextl start ([x]) = garbage\<close> 
by(cases x) (auto split: if_splits)

lemma first_ok_iff: \<open>xs\<noteq> [] \<Longrightarrow> p5_aut.nextl start xs = first_ok \<or> p5_aut.nextl start xs = garbage\<close>
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by blast
next
  case (snoc x xs)
  then show ?case
  proof(cases \<open>xs = []\<close>)
    case True
    then show ?thesis unfolding True using singleton_first_ok_iff by auto
  next
    case False
    with snoc have \<open>p5_aut.nextl start xs = first_ok \<or> p5_aut.nextl start xs = garbage\<close> 
      by blast
    then show ?thesis
      by(cases x) (auto split: if_splits)
  qed
qed

lemma lang_descr: \<open>xs \<in> p5_aut.language \<longleftrightarrow> (xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets)\<close>
proof(induction xs rule: rev_induct)
  case (snoc x xs)
  then have IH: \<open>(xs \<in> p5_aut.language) = (xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets)\<close> 
    by blast
  then show ?case
  proof(cases xs)
    case Nil
    then show ?thesis using singleton_in_lang_iff by auto
  next
    case (Cons y ys)
    then have xs_eq: \<open>xs = y # ys\<close> 
      by blast
    then show ?thesis
    proof(cases \<open>xs \<in> p5_aut.language\<close>)
      case True
      then have \<open>(xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets)\<close> 
        using IH by blast
      then show ?thesis 
        using p5_aut.language_def snoc by(cases x) auto
    next
      case False
      then have \<open>p5_aut.nextl start xs = garbage\<close> 
        unfolding p5_aut.language_def using first_ok_iff[of xs] Cons by auto
      then have \<open>p5_aut.nextl start (xs@[x]) = garbage\<close> 
        by simp
      then show ?thesis using IH unfolding xs_eq p5_aut.language_def by auto
    qed
  qed
qed simp

lemma in_P5_iff: \<open>P5 A xs \<and> xs \<in> brackets \<longleftrightarrow> (xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets)\<close>
  using P5.elims(3) by fastforce 

lemma aut_language_reg: \<open>regular p5_aut.language\<close>
  using p5_aut.regular by blast 

corollary aux_regular: \<open>regular {xs. xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets}\<close> 
  using lang_descr aut_language_reg p5_aut.language_def by simp

lemma regular_P5:\<open>regular {xs. P5 A xs \<and> xs \<in> brackets}\<close> 
  using in_P5_iff aux_regular by presburger

end (* P5Construction *)


context locale_P
begin

corollary regular_Reg_inter: \<open>regular (brackets \<inter> Reg A)\<close>
proof-
  interpret P5Construction P A ..
  from finiteP have regs: \<open>regular {xs. P1 xs \<and> xs \<in> brackets}\<close>  
    \<open>regular {xs. successively P2 xs \<and>  xs \<in> brackets}\<close> 
    \<open>regular {xs. successively P3 xs \<and>  xs \<in> brackets}\<close> 
    \<open>regular {xs. successively P4 xs \<and>  xs \<in> brackets}\<close> 
    \<open>regular {xs. P5 A xs \<and> xs \<in> brackets}\<close>
    using regular_P1 P2_regular P3_regular P4_regular regular_P5
    by blast+ 

  hence \<open>regular ({xs. P1 xs \<and> xs \<in> brackets} \<inter>
    {xs. successively P2 xs \<and>  xs \<in> brackets} \<inter>
    {xs. successively P3 xs \<and>  xs \<in> brackets} \<inter>
    {xs. successively P4 xs \<and>  xs \<in> brackets} \<inter>
    {xs. P5 A xs \<and> xs \<in> brackets})\<close> 
    by (meson regular_Int)

  moreover have set_eq: \<open>{xs. P1 xs \<and> xs \<in> brackets} \<inter>
           {xs. successively P2 xs \<and>  xs \<in> brackets} \<inter>
           {xs. successively P3 xs \<and>  xs \<in> brackets} \<inter>
           {xs. successively P4 xs \<and>  xs \<in> brackets} \<inter>
           {xs. P5 A xs \<and> xs \<in> brackets} 
  = brackets \<inter> Reg A\<close> by auto 

  ultimately show ?thesis by argo
qed

text\<open>A lemma saying that all \<open>Dyck_lang\<close> words really only consist of brackets (trivial definition wrangling):\<close>

lemma Dyck_lang_subset_brackets: \<open>Dyck_lang (P \<times> {One, Two}) \<subseteq> brackets\<close>
  unfolding Dyck_lang_def using Ball_set by auto


end (* P *)



section\<open>Definitions of \<open>L\<close>, \<open>\<Gamma>\<close>, \<open>P'\<close>, \<open>L'\<close>\<close>

locale Chomsky_Schuetzenberger_locale = locale_P where P = P for P :: "('n,'t)Prods" +
fixes S :: "'n"
assumes CNF_P: \<open>CNF P\<close>

begin

lemma P_CNFE[dest]:
  assumes \<open>\<pi> \<in> P\<close>
  shows \<open>\<exists>A a B C. \<pi> = (A, [Nt B, Nt C]) \<or> \<pi> = (A, [Tm a])\<close>  
  using assms CNF_P unfolding CNF_def by fastforce

definition L where 
  \<open>L = Lang P S\<close>

definition \<Gamma> where 
  \<open>\<Gamma> = P \<times> {One, Two}\<close>

definition P' where 
  \<open>P' = transform_prod ` P\<close>

definition L' where 
  \<open>L' = Lang P' S\<close>



section\<open>Lemmas for \<open>P' \<turnstile> A \<Rightarrow>\<^sup>* x  \<longleftrightarrow>  x \<in> R\<^sub>A \<inter> Dyck_lang \<Gamma>\<close>\<close>

lemma prod1_snds_in_tm [intro, simp]: \<open>(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> snds_in_tm \<Gamma> (wrap2 A B C)\<close> 
  unfolding snds_in_tm_def using \<Gamma>_def by auto

lemma prod2_snds_in_tm [intro, simp]: \<open>(A, [Tm a]) \<in> P \<Longrightarrow> snds_in_tm \<Gamma> (wrap1 A a)\<close> 
  unfolding snds_in_tm_def using \<Gamma>_def by auto

lemma bal_tm_wrap1[iff]: \<open>bal_tm (wrap1 A a)\<close>
unfolding bal_tm_def by (simp add: bal_iff_bal_stk)

lemma bal_tm_wrap2[iff]: \<open>bal_tm (wrap2 A B C)\<close> 
unfolding bal_tm_def by (simp add: bal_iff_bal_stk)

text\<open>This essentially says, that the right sides of productions are in the Dyck language of \<open>\<Gamma>\<close>, 
if one ignores any occuring nonterminals. This will be needed for \<open>\<rightarrow>\<close>.\<close>
lemma bal_tm_transform_rhs[intro!]:
  \<open>(A,\<alpha>) \<in> P \<Longrightarrow> bal_tm (transform_rhs A \<alpha>)\<close>
by auto

lemma snds_in_tm_transform_rhs[intro!]:
  \<open>(A,\<alpha>) \<in> P \<Longrightarrow> snds_in_tm \<Gamma> (transform_rhs A \<alpha>)\<close>
  using P_CNFE by (fastforce)

text\<open>The lemma for \<open>\<rightarrow>\<close>\<close>
lemma P'_imp_bal:
  assumes \<open>P' \<turnstile> [Nt A] \<Rightarrow>* x\<close>
  shows \<open>bal_tm x \<and> snds_in_tm \<Gamma> x\<close>
  using assms proof(induction rule: derives_induct)
  case base
  then show ?case unfolding snds_in_tm_def by auto
next
  case (step u A v w)
  have \<open>bal_tm (u @ [Nt A] @ v)\<close> and \<open>snds_in_tm \<Gamma> (u @ [Nt A] @ v)\<close> 
    using step.IH step.prems by auto
  obtain w' where w'_def: \<open>w = transform_rhs A w'\<close> and A_w'_in_P: \<open>(A,w') \<in> P\<close>
    using P'_def step.hyps(2) by force
  have bal_tm_w: \<open>bal_tm w\<close>
    using bal_tm_transform_rhs[OF \<open>(A,w') \<in> P\<close>] w'_def by auto
  then have \<open>bal_tm (u @ w @ v)\<close> 
    using \<open>bal_tm (u @ [Nt A] @ v)\<close> by (metis bal_tm_empty bal_tm_inside bal_tm_prepend_Nt)
  moreover have \<open>snds_in_tm \<Gamma> (u @ w @ v)\<close> 
    using snds_in_tm_transform_rhs[OF \<open>(A,w') \<in> P\<close>] \<open>snds_in_tm \<Gamma> (u @ [Nt A] @ v)\<close> w'_def by (simp)
  ultimately show ?case using \<open>bal_tm (u @ w @ v)\<close> by blast
qed

text\<open>Another lemma for \<open>\<rightarrow>\<close>\<close>
lemma P'_imp_Reg:
  assumes \<open>P' \<turnstile> [Nt T] \<Rightarrow>* x\<close>
  shows \<open>x \<in> Reg_sym T\<close>
  using assms proof(induction rule: derives_induct)
  case base
  show ?case by(rule Reg_symI) simp_all
next
  case (step u A v w)
  have uAv: \<open>u @ [Nt A] @ v \<in> Reg_sym T\<close> 
    using step by blast
  have \<open>(A, w) \<in> P'\<close> 
    using step by blast
  then obtain w' where w'_def: \<open>transform_prod (A, w') = (A, w)\<close> and \<open>(A,w') \<in> P\<close> 
    by (smt (verit, best) transform_prod.simps P'_def P_CNFE fst_conv image_iff)
  then obtain B C a where w_eq: \<open>w = wrap1 A a \<or> w = wrap2 A B C\<close> (is \<open>w = ?w1 \<or> w = ?w2\<close>) 
    by fastforce
  then have w_resym: \<open>w \<in> Reg_sym A\<close> 
    by auto 
  have P5_uAv: \<open>P5_sym T (u @ [Nt A] @ v)\<close> 
    using Reg_symD[OF uAv] by blast
  have P1_uAv: \<open>P1_sym (u @ [Nt A] @ v)\<close> 
    using Reg_symD[OF uAv] by blast
  have left: \<open>successively P1'_sym (u@w) \<and> 
              successively P2_sym (u@w) \<and> 
              successively P3_sym (u@w) \<and> 
              successively P4_sym (u@w) \<and> 
              successively P7_sym (u@w) \<and> 
              successively P8_sym (u@w)\<close>
  proof(cases u rule: rev_cases)
    case Nil
    then show ?thesis using w_eq by auto
  next
    case (snoc ys y)

    then have \<open>successively P7_sym (ys @ [y] @ [Nt A] @ v)\<close> 
      using Reg_symD[OF uAv] snoc by auto
    then have \<open>P7_sym y (Nt A)\<close> 
      by (simp add: successively_append_iff)

    then obtain R X Y v' where y_eq: \<open>y = (Tm (Open((R, [Nt X, Nt Y]), v')))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> 
      by blast
    then have \<open>P3_sym y (hd w)\<close> 
      using w_eq \<open>P7_sym y (Nt A)\<close> by force
    hence \<open>P1'_sym (last (ys@[y])) (hd w) \<and> 
          P2_sym (last (ys@[y])) (hd w) \<and> 
          P3_sym (last (ys@[y])) (hd w) \<and> 
          P4_sym (last (ys@[y])) (hd w) \<and> 
          P7_sym (last (ys@[y])) (hd w) \<and> 
          P8_sym (last (ys@[y])) (hd w)\<close> 
      unfolding y_eq using w_eq by auto
    with Reg_symD[OF uAv] moreover have 
      \<open>successively P1'_sym (ys @ [y]) \<and> 
     successively P2_sym (ys @ [y]) \<and> 
     successively P3_sym (ys @ [y]) \<and> 
     successively P4_sym (ys @ [y]) \<and> 
     successively P7_sym (ys @ [y]) \<and> 
     successively P8_sym (ys @ [y])\<close> 
      unfolding snoc using successively_append_iff by blast
    ultimately show 
      \<open>successively P1'_sym (u@w) \<and> 
     successively P2_sym (u@w) \<and> 
     successively P3_sym (u@w) \<and> 
     successively P4_sym (u@w) \<and> 
     successively P7_sym (u@w) \<and> 
     successively P8_sym (u@w)\<close> 
      unfolding snoc using Reg_symD[OF w_resym] using successively_append_iff by blast
  qed
  have right: \<open>successively P1'_sym (w@v) \<and> 
               successively P2_sym (w@v) \<and> 
               successively P3_sym (w@v) \<and> 
               successively P4_sym (w@v) \<and> 
               successively P7_sym (w@v) \<and> 
               successively P8_sym (w@v)\<close>
  proof(cases v)
    case Nil
    then show ?thesis using w_eq by auto
  next
    case (Cons y ys)
    then have \<open>successively P8_sym ([Nt A] @ y # ys)\<close> 
      using Reg_symD[OF uAv] Cons using successively_append_iff by blast
    then have \<open>P8_sym (Nt A) y\<close> 
      by fastforce
    then obtain R X Y v' where y_eq: \<open>y = (Tm (Close((R, [Nt X, Nt Y]), v')))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> 
      by blast
    have \<open>P1'_sym (last w) (hd (y#ys)) \<and> 
         P2_sym (last w) (hd (y#ys)) \<and> 
         P3_sym (last w) (hd (y#ys)) \<and> 
         P4_sym (last w) (hd (y#ys)) \<and> 
         P7_sym (last w) (hd (y#ys)) \<and> 
         P8_sym (last w) (hd (y#ys))\<close> 
      unfolding y_eq using w_eq by auto
    with Reg_symD[OF uAv] moreover have 
      \<open>successively P1'_sym (y # ys) \<and> 
     successively P2_sym (y # ys) \<and> 
     successively P3_sym (y # ys) \<and> 
     successively P4_sym (y # ys) \<and> 
     successively P7_sym (y # ys) \<and> 
     successively P8_sym (y # ys)\<close> 
      unfolding Cons by (metis P1_symD successively_append_iff)
    ultimately show \<open>successively P1'_sym (w@v) \<and> 
                     successively P2_sym (w@v) \<and> 
                     successively P3_sym (w@v) \<and> 
                     successively P4_sym (w@v) \<and> 
                     successively P7_sym (w@v) \<and> 
                     successively P8_sym (w@v)\<close> 
      unfolding Cons using Reg_symD[OF w_resym] successively_append_iff by blast
  qed
  from left right have P1_uwv: \<open>successively P1'_sym (u@w@v)\<close> 
    using w_eq by (metis (no_types, lifting) List.list.discI hd_append2 successively_append_iff)
  from left right have ch: 
    \<open>successively P2_sym (u@w@v) \<and> 
   successively P3_sym (u@w@v) \<and> 
   successively P4_sym (u@w@v) \<and> 
   successively P7_sym (u@w@v) \<and> 
   successively P8_sym (u@w@v)\<close> 
    using w_eq by (metis (no_types, lifting) List.list.discI hd_append2 successively_append_iff)

  moreover have \<open>P5_sym T (u@w@v)\<close> 
    using w_eq P5_uAv by (cases u) auto

  moreover have \<open>P1_sym (u@w@v)\<close> 
  proof(cases v rule: rev_cases)
    case Nil
    then have \<open>\<nexists>p. last (u@w@v) = Tm (Close(p, One))\<close> 
      using w_eq by auto
    with P1_uwv show \<open>P1_sym (u @ w @ v)\<close> 
      by blast
  next
    case (snoc vs v')
    then have \<open>\<nexists>p. last v = Tm (Close(p, One))\<close> 
      using P1_symD_not_empty[OF _ P1_uAv] by (metis Nil_is_append_conv last_appendR not_Cons_self2)
    then have \<open>\<nexists>p. last (u@w@v) = Tm (Close(p, One))\<close> 
      by (simp add: snoc)
    with P1_uwv show \<open>P1_sym (u @ w @ v)\<close> 
      by blast
  qed
  ultimately show \<open>(u@w@v) \<in> Reg_sym T\<close> 
    by blast 
qed

text\<open>This will be needed for the direction \<open>\<leftarrow>\<close>.\<close>
lemma transform_prod_one_step:
  assumes \<open>\<pi> \<in> P\<close>
  shows \<open>P' \<turnstile> [Nt (fst \<pi>)] \<Rightarrow> snd (transform_prod \<pi>)\<close>
proof-
  obtain w' where w'_def: \<open>transform_prod \<pi> = (fst \<pi>, w')\<close> 
    by (metis fst_eqD transform_prod.simps surj_pair)
  then have \<open>(fst \<pi>, w') \<in> P'\<close> 
    using assms by (simp add: P'_def rev_image_eqI)
  then show ?thesis 
    by (simp add: w'_def derive_singleton)
qed

text\<open>The lemma for \<open>\<leftarrow>\<close>\<close>
lemma Reg_and_dyck_imp_P':
  assumes \<open>x \<in> (Reg A \<inter> Dyck_lang \<Gamma>)\<close>
  shows \<open>P' \<turnstile> [Nt A] \<Rightarrow>* map Tm x\<close> using assms 
proof(induction \<open>length (map Tm x)\<close> arbitrary: A x rule: less_induct)
  case less
  then have IH: \<open>\<And>w H. \<lbrakk>length (map Tm w) < length (map Tm x);  w \<in> Reg H \<inter> Dyck_lang (\<Gamma>)\<rbrakk> \<Longrightarrow> 
                  P' \<turnstile> [Nt H] \<Rightarrow>* map Tm w\<close> 
    using less by simp
  have xReg: \<open>x \<in> Reg A\<close> and xDL: \<open>x \<in> Dyck_lang (\<Gamma>)\<close> 
    using less by blast+

  have p1x: \<open>P1 x\<close> 
    and p2x: \<open>successively P2 x\<close> 
    and p3x: \<open>successively P3 x\<close> 
    and p4x: \<open>successively P4 x\<close> 
    and p5x: \<open>P5 A x\<close> 
    using RegD[OF xReg] by blast+

  from p5x obtain \<pi> t where hd_x: \<open>hd x = [\<^sup>1\<^sub>\<pi>\<close> and pi_def: \<open>\<pi> = (A, t)\<close> 
    by (metis List.list.sel(1) P5.elims(2))
  with xReg have \<open>[\<^sup>1\<^sub>\<pi> \<in> set x\<close> 
    by (metis List.list.sel(1) List.list.set_intros(1) RegD(5) P5.elims(2))
  then have pi_in_P: \<open>\<pi> \<in> P\<close> 
    using xDL unfolding Dyck_lang_def \<Gamma>_def by fastforce
  have bal_x: \<open>bal x\<close> 
    using xDL by blast
  then have \<open>\<exists>y r. bal y \<and> bal r \<and> [\<^sup>1\<^bsub>\<pi>\<^esub>  # tl x = [\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub> # r\<close> 
    using hd_x bal_x bal_Open_split[of \<open>[\<^sup>1\<^bsub>\<pi>\<^esub> \<close>, where ?xs = \<open>tl x\<close>] 
    by (metis (no_types, lifting) List.list.exhaust_sel List.list.inject Product_Type.prod.inject P5.simps(1) p5x)
  then obtain y r1 where \<open>[\<^sup>1\<^bsub>\<pi>\<^esub>  # tl x   =   [\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub> # r1\<close> and bal_y: \<open>bal y\<close> and bal_r1: \<open>bal r1\<close> 
    by blast
  then have split1: \<open>x = [\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub> # r1\<close> 
    using hd_x by (metis List.list.exhaust_sel List.list.set(1) \<open>[\<^sup>1\<^bsub>\<pi>\<^esub> \<in> set x\<close> empty_iff)
  have \<open>r1 \<noteq> []\<close> 
  proof(rule ccontr)
    assume \<open>\<not> r1 \<noteq> []\<close>
    then have \<open>last x = ]\<^sup>1\<^bsub>\<pi>\<^esub> \<close> 
      using split1 by(auto)
    then show \<open>False\<close> 
      using p1x using P1D_not_empty split1 by blast
  qed
  from p1x have hd_r1: \<open>hd r1 = [\<^sup>2\<^bsub>\<pi>\<^esub>\<close> 
    using split1 \<open>r1 \<noteq> []\<close> by (metis (no_types, lifting) List.list.discI List.successively.elims(1) P1'D P1.simps successively_Cons successively_append_iff)
  from bal_r1 have \<open>\<exists>z r2. bal z \<and> bal r2 \<and> [\<^sup>2\<^bsub>\<pi>\<^esub> # tl r1 = [\<^sup>2\<^bsub>\<pi>\<^esub> # z @ ]\<^sup>2\<^bsub>\<pi>\<^esub>  # r2\<close> 
    using bal_Open_split[of \<open>[\<^sup>2\<^bsub>\<pi>\<^esub>\<close> \<open>tl r1\<close>] by (metis List.list.exhaust_sel List.list.sel(1) Product_Type.prod.inject hd_r1 \<open>r1 \<noteq> []\<close>) 
  then obtain z r2 where split2': \<open>[\<^sup>2\<^bsub>\<pi>\<^esub> # tl r1   =   [\<^sup>2\<^bsub>\<pi>\<^esub> # z @ ]\<^sup>2\<^bsub>\<pi>\<^esub>  # r2\<close> and bal_z: \<open>bal z\<close> and bal_r2: \<open>bal r2\<close> 
    by blast+
  then have split2: \<open>x  =   [\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub>  # [\<^sup>2\<^bsub>\<pi>\<^esub> # z @ ]\<^sup>2\<^bsub>\<pi>\<^esub>  # r2\<close>
    by (metis \<open>r1 \<noteq> []\<close> hd_r1 list.exhaust_sel split1)
  have r2_empty: \<open>r2 = []\<close>  \<comment> \<open>prove that if r2 was not empty, it would need to start with an open bracket, else it cant be balanced. But this cant be with P2.\<close>
  proof(cases r2)
    case (Cons r2' r2's)
    with bal_r2 obtain g where r2_begin_op: \<open>r2' = (Open g)\<close> 
      using bal_start_Open[of r2' r2's] using Cons by blast
    have \<open>successively P2 ( ]\<^sup>2\<^bsub>\<pi>\<^esub>  # r2' # r2's)\<close> 
      using p2x unfolding split2 Cons successively_append_iff by (metis append_Cons successively_append_iff)
    then have \<open>P2 ]\<^sup>2\<^bsub>\<pi>\<^esub> (r2')\<close> 
      by fastforce
    with r2_begin_op have \<open>False\<close> 
      by (metis P2.simps(1) split_pairs)
    then show ?thesis by blast
  qed blast
  then have split3: \<open>x  =   [\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub>  # [\<^sup>2\<^bsub>\<pi>\<^esub> # z @[   ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]\<close> 
    using split2 by blast
  consider (BC) \<open>\<exists>B C. \<pi> = (A, [Nt B, Nt C])\<close> | (a) \<open>\<exists>a. \<pi> = (A, [Tm a])\<close> 
    using assms pi_in_P local.pi_def by fastforce
  then show \<open>P' \<turnstile> [Nt A] \<Rightarrow>* map Tm x\<close>
  proof(cases)
    case BC
    then obtain B C where pi_eq: \<open>\<pi> = (A, [Nt B, Nt C])\<close> 
      by blast
    from split3 have y_successivelys: 
      \<open>successively P1' y \<and> 
       successively P2 y \<and> 
       successively P3 y \<and> 
       successively P4 y\<close> 
      using P1.simps p1x p2x p3x p4x by (metis List.list.simps(3) Nil_is_append_conv successively_Cons successively_append_iff)

    have y_not_empty: \<open>y \<noteq> []\<close> 
      using p3x pi_eq split1 by fastforce
    have \<open>\<nexists>p. last y = ]\<^sup>1\<^sub>p\<close>
    proof(rule ccontr)
      assume \<open>\<not> (\<nexists>p. last y = ]\<^sup>1\<^bsub>p\<^esub>)\<close>
      then obtain p where last_y: \<open>last y = ]\<^sup>1\<^bsub>p\<^esub> \<close> 
        by blast
      obtain butl where butl_def: \<open>y = butl @ [last y]\<close> 
        by (metis append_butlast_last_id y_not_empty)

      have  \<open>successively P1' ([\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub>  # [\<^sup>2\<^bsub>\<pi>\<^esub> # z @[   ]\<^sup>2\<^bsub>\<pi>\<^esub>   ])\<close> 
        using p1x split3 by auto 
      then have \<open>successively P1' ([\<^sup>1\<^bsub>\<pi>\<^esub>  # (butl@[last y]) @ ]\<^sup>1\<^bsub>\<pi>\<^esub>  # [\<^sup>2\<^bsub>\<pi>\<^esub> # z @[   ]\<^sup>2\<^bsub>\<pi>\<^esub>   ])\<close> 
        using butl_def by simp
      then have \<open>successively P1' (([\<^sup>1\<^bsub>\<pi>\<^esub>  # butl) @ last y # [ ]\<^sup>1\<^bsub>\<pi>\<^esub>] @ [\<^sup>2\<^bsub>\<pi>\<^esub> # z @ [ ]\<^sup>2\<^bsub>\<pi>\<^esub> ])\<close> 
        by (metis (no_types, opaque_lifting) Cons_eq_appendI append_assoc append_self_conv2) 
      then have \<open>P1' ]\<^sup>1\<^bsub>p\<^esub>  ]\<^sup>1\<^bsub>\<pi>\<^esub> \<close> 
        using last_y by (metis (no_types, lifting) List.successively.simps(3) append_Cons successively_append_iff)
      then show \<open>False\<close> 
        by simp
    qed
    with y_successivelys have P1y: \<open>P1 y\<close> 
      by blast
    with p3x pi_eq have \<open>\<exists>g. hd y = [\<^sup>1\<^bsub>(B,g)\<^esub>\<close> 
      using y_not_empty split3 by (metis (no_types, lifting) P3D1 append_is_Nil_conv hd_append2 successively_Cons)
    then have \<open>P5 B y\<close> 
      by (metis \<open>y \<noteq> []\<close> P5.simps(2) hd_Cons_tl)
    with y_successivelys P1y have \<open>y \<in> Reg B\<close> 
      by blast
    moreover have \<open>y \<in> Dyck_lang (\<Gamma>)\<close> 
      using split3 bal_y Dyck_lang_substring by (metis append_Cons append_Nil hd_x split1 xDL)
    ultimately have \<open>y \<in> Reg B \<inter> Dyck_lang (\<Gamma>)\<close> 
      by force
    moreover have \<open>length (map Tm y) < length (map Tm x)\<close> 
      using length_append length_map lessI split3 by fastforce
    ultimately have der_y: \<open>P' \<turnstile> [Nt B] \<Rightarrow>* map Tm y\<close> 
      using IH[of y B] split3  by blast
    from split3 have z_successivelys: 
      \<open>successively P1' z \<and> 
     successively P2 z \<and> 
     successively P3 z \<and> 
     successively P4 z\<close> 
      using P1.simps p1x p2x p3x p4x by (metis List.list.simps(3) Nil_is_append_conv successively_Cons successively_append_iff)
    then have successively_P3: \<open>successively P3 (([\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ [ ]\<^sup>1\<^bsub>\<pi>\<^esub>]) @ [\<^sup>2\<^bsub>\<pi>\<^esub> # z @ [ ]\<^sup>2\<^bsub>\<pi>\<^esub> ])\<close> 
      using split3 p3x by (metis List.append.assoc append_Cons append_Nil)
    have z_not_empty: \<open>z \<noteq> []\<close> 
      using p3x pi_eq split1 successively_P3 by (metis List.list.distinct(1) List.list.sel(1) append_Nil P3.simps(2) successively_Cons successively_append_iff)
    then have \<open>P3 [\<^sup>2\<^bsub>\<pi>\<^esub> (hd z)\<close> 
      by (metis append_is_Nil_conv hd_append2 successively_Cons successively_P3 successively_append_iff)
    with p3x pi_eq have \<open>\<exists>g. hd z = [\<^sup>1\<^bsub>(C,g)\<^esub>\<close> 
      using split_pairs by blast
    then have \<open>P5 C z\<close> 
      by (metis List.list.exhaust_sel \<open>z \<noteq> []\<close> P5.simps(2)) 
    moreover have \<open>P1 z\<close>
    proof-
      have \<open>\<nexists>p. last z = ]\<^sup>1\<^bsub>p\<^esub>\<close> 
      proof(rule ccontr)
        assume \<open>\<not> (\<nexists>p. last z = ]\<^sup>1\<^bsub>p\<^esub>)\<close>
        then obtain p where last_y: \<open>last z = ]\<^sup>1\<^bsub>p\<^esub> \<close> 
          by blast
        obtain butl where butl_def: \<open>z = butl @ [last z]\<close> 
          by (metis append_butlast_last_id z_not_empty)
        have  \<open>successively P1' ([\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub>  # [\<^sup>2\<^bsub>\<pi>\<^esub> # z @[   ]\<^sup>2\<^bsub>\<pi>\<^esub>   ])\<close> 
          using p1x split3 by auto 
        then have \<open>successively P1' ([\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub>  # [\<^sup>2\<^bsub>\<pi>\<^esub> # butl @ [last z] @[   ]\<^sup>2\<^bsub>\<pi>\<^esub>   ])\<close> 
          using butl_def by (metis append_assoc)
        then have \<open>successively P1' (([\<^sup>1\<^bsub>\<pi>\<^esub>  # y @ ]\<^sup>1\<^bsub>\<pi>\<^esub> # [\<^sup>2\<^bsub>\<pi>\<^esub> # butl) @ last z # [ ]\<^sup>2\<^bsub>\<pi>\<^esub> ] @ [])\<close> 
          by (metis (no_types, opaque_lifting) Cons_eq_appendI append_assoc append_self_conv2) 
        then have \<open>P1' ]\<^sup>1\<^bsub>p\<^esub>  ]\<^sup>2\<^bsub>\<pi>\<^esub> \<close> 
          using last_y by (metis List.append.right_neutral List.successively.simps(3) successively_append_iff)
        then show \<open>False\<close> 
          by simp
      qed
      then show \<open>P1 z\<close> 
        using z_successivelys by blast
    qed

    ultimately have \<open>z \<in> Reg C\<close> 
      using z_successivelys by blast
    moreover have \<open>z \<in> Dyck_lang (\<Gamma>)\<close> 
      using xDL[simplified split3] bal_z Dyck_lang_substring[of z "[\<^sup>1\<^sub>\<pi> # y @ ]\<^sup>1\<^sub>\<pi> # [\<^sup>2\<^sub>\<pi> # []" "[ ]\<^sup>2\<^sub>\<pi> ]"]
      by auto
    ultimately have \<open>z \<in> Reg C \<inter> Dyck_lang (\<Gamma>)\<close> 
      by force
    moreover have \<open>length (map Tm z) < length (map Tm x)\<close> 
      using length_append length_map lessI split3 by fastforce
    ultimately have der_z: \<open>P' \<turnstile> [Nt C] \<Rightarrow>* map Tm z\<close> 
      using IH[of z C] split3  by blast
    have \<open>P' \<turnstile> [Nt A] \<Rightarrow>* [ Tm [\<^sup>1\<^bsub>\<pi>\<^esub> ] @ [(Nt B)] @ [Tm ]\<^sup>1\<^bsub>\<pi>\<^esub>  , Tm [\<^sup>2\<^bsub>\<pi>\<^esub> ] @  [(Nt C)] @ [   Tm ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]\<close> 
      using transform_prod_one_step[OF pi_in_P] using pi_eq by auto 
    also have \<open>P' \<turnstile> [ Tm [\<^sup>1\<^bsub>\<pi>\<^esub> ] @ [(Nt B)] @ [Tm ]\<^sup>1\<^bsub>\<pi>\<^esub>  , Tm [\<^sup>2\<^bsub>\<pi>\<^esub> ] @  [(Nt C)] @ [   Tm ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]    \<Rightarrow>*    [ Tm [\<^sup>1\<^bsub>\<pi>\<^esub> ] @ map Tm y @ [Tm ]\<^sup>1\<^bsub>\<pi>\<^esub>  , Tm [\<^sup>2\<^bsub>\<pi>\<^esub> ] @  [(Nt C)] @ [   Tm ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]\<close> 
      using der_y using derives_append derives_prepend by blast
    also have \<open>P' \<turnstile> [ Tm [\<^sup>1\<^bsub>\<pi>\<^esub> ] @ map Tm y @ [Tm ]\<^sup>1\<^bsub>\<pi>\<^esub>  , Tm [\<^sup>2\<^bsub>\<pi>\<^esub> ] @  [(Nt C)] @ [   Tm ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]    \<Rightarrow>*    [ Tm [\<^sup>1\<^bsub>\<pi>\<^esub> ] @ map Tm y @ [Tm ]\<^sup>1\<^bsub>\<pi>\<^esub>  , Tm [\<^sup>2\<^bsub>\<pi>\<^esub> ] @  (map Tm z) @ [   Tm ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]\<close> 
      using der_z by (meson derives_append derives_prepend)
    finally have \<open>P' \<turnstile> [Nt A] \<Rightarrow>* [ Tm [\<^sup>1\<^bsub>\<pi>\<^esub> ] @ map Tm y @ [Tm ]\<^sup>1\<^bsub>\<pi>\<^esub>  , Tm [\<^sup>2\<^bsub>\<pi>\<^esub> ] @  (map Tm z) @ [   Tm ]\<^sup>2\<^bsub>\<pi>\<^esub>   ]\<close> 
      .
    then show ?thesis using split3 by simp
  next
    case a
    then obtain a where pi_eq: \<open>\<pi> = (A, [Tm a])\<close> 
      by blast
    have \<open>y = []\<close>
    proof(cases y)
      case (Cons y' ys')
      have \<open>P4 [\<^sup>1\<^bsub>\<pi>\<^esub> y'\<close> 
        using Cons append_Cons p4x split3 by (metis List.successively.simps(3)) 
      then have \<open>y' = Close (\<pi>, One)\<close> 
        using pi_eq P4D by auto
      moreover obtain g where \<open>y' = (Open g)\<close> 
        using Cons bal_start_Open bal_y by blast
      ultimately have \<open>False\<close> 
        by blast
      then show ?thesis by blast
    qed blast
    have \<open>z = []\<close>
    proof(cases z)
      case (Cons z' zs')
      have \<open>P4 [\<^sup>2\<^bsub>\<pi>\<^esub> z'\<close> 
        using p4x split3 by (simp add: Cons \<open>y = []\<close>)
      then have \<open>z' = Close (\<pi>, One)\<close> 
        using pi_eq bal_start_Open bal_z local.Cons by blast
      moreover obtain g where \<open>z' = (Open g)\<close> 
        using Cons bal_start_Open bal_z by blast
      ultimately have \<open>False\<close> 
        by blast
      then show ?thesis by blast
    qed blast
    have \<open>P' \<turnstile> [Nt A] \<Rightarrow>* [ Tm [\<^sup>1\<^sub>\<pi>,       Tm ]\<^sup>1\<^sub>\<pi> , Tm [\<^sup>2\<^sub>\<pi> ,       Tm ]\<^sup>2\<^sub>\<pi>   ]\<close> 
      using transform_prod_one_step[OF pi_in_P] pi_eq by auto
    then show ?thesis using \<open>y = []\<close> \<open>z = []\<close> by (simp add: split3)
  qed
qed



section\<open>Showing \<open>h(L') = L\<close>\<close>

text\<open>Particularly \<open>\<supseteq>\<close> is formally hard. 
To create the witness in \<open>L'\<close> we need to use the corresponding production in \<open>P'\<close> in each step. 
We do this by defining the transformation on the parse tree, instead of only the word. 
Simple induction on the derivation wouldn't (in the induction step) get us enough information on 
where the corresponding production needs to be applied in the transformed version.\<close>

abbreviation \<open>roots ts \<equiv> map root ts\<close>

fun wrap1_Sym :: \<open>'n \<Rightarrow> ('n,'t) sym \<Rightarrow> version \<Rightarrow> ('n,('n,'t) bracket3) tree list\<close> where
  "wrap1_Sym A (Tm a) v = [ Sym (Tm (Open ((A, [Tm a]),v))),  Sym (Tm (Close ((A, [Tm a]), v)))]" | 
  \<open>wrap1_Sym _ _ _ = []\<close>

fun wrap2_Sym :: \<open>'n \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) sym \<Rightarrow> version \<Rightarrow> ('n,('n,'t) bracket3) tree \<Rightarrow> ('n,('n,'t) bracket3) tree list\<close>  where
  "wrap2_Sym A (Nt B) (Nt C) v t = [Sym (Tm (Open ((A, [Nt B, Nt C]), v))), t , Sym (Tm (Close ((A, [Nt B, Nt C]), v)))]" | 
  \<open>wrap2_Sym _ _ _ _ _ = []\<close>

fun transform_tree :: "('n,'t) tree \<Rightarrow> ('n,('n,'t) bracket3) tree" where
  \<open>transform_tree (Sym (Nt A)) = (Sym (Nt A))\<close> | 
  \<open>transform_tree (Sym (Tm a)) = (Sym (Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub>))\<close> |
  \<open>transform_tree (Rule A [Sym (Tm a)]) = Rule A ((wrap1_Sym A (Tm a) One)@(wrap1_Sym A (Tm a) Two))\<close> | 
  \<open>transform_tree (Rule A [t1, t2]) = Rule A ((wrap2_Sym A (root t1) (root t2) One (transform_tree t1)) @ (wrap2_Sym A (root t1) (root t2) Two (transform_tree t2)))\<close> | 
  \<open>transform_tree (Rule A y) = (Rule A [])\<close>

lemma root_of_transform_tree[intro, simp]: \<open>root t = Nt X \<Longrightarrow> root (transform_tree t) = Nt X\<close>
  by(induction t rule: transform_tree.induct) auto

lemma transform_tree_correct:
  assumes \<open>parse_tree P t \<and> fringe t = w\<close>
  shows \<open>parse_tree P' (transform_tree t)  \<and>  \<h>\<s> (fringe (transform_tree t)) = w\<close>
  using assms proof(induction t arbitrary: w)
  case (Sym x)
  from Sym have pt: \<open>parse_tree P (Sym x)\<close> and \<open>fringe (Sym x) = w\<close> 
    by blast+
  then show ?case 
  proof(cases x)
    case (Nt x1)
    then have \<open>transform_tree (Sym x) = (Sym (Nt x1))\<close> 
      by simp 
    then show ?thesis using Sym by (metis Nt Parse_Tree.fringe.simps(1) Parse_Tree.parse_tree.simps(1) the_hom_syms_keep_var)
  next
    case (Tm x2)
    then obtain a where \<open>transform_tree (Sym x) = (Sym (Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub>))\<close> 
      by simp
    then have \<open>fringe ... = [Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub>]\<close> 
      by simp
    then have \<open>\<h>\<s> ... = [Tm a]\<close> 
      by simp
    then have \<open>... = w\<close> using Sym using Tm \<open>transform_tree (Sym x) = Sym (Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub> )\<close> 
      by force
    then show ?thesis using Sym by (metis Parse_Tree.parse_tree.simps(1) \<open>fringe (Sym (Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub> )) = [Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub> ]\<close> \<open>\<h>\<s> [Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub> ] = [Tm a]\<close> \<open>transform_tree (Sym x) = Sym (Tm [\<^sup>1\<^bsub>(SOME A. True, [Tm a])\<^esub> )\<close>)
  qed
next
  case (Rule A ts)
  from Rule have pt: \<open>parse_tree P (Rule A ts)\<close> and fr: \<open>fringe (Rule A ts) = w\<close> 
    by blast+
  from Rule have IH: \<open>\<And>x2a w'. \<lbrakk>x2a \<in> set ts; parse_tree P x2a \<and> fringe x2a = w'\<rbrakk> \<Longrightarrow> parse_tree P' (transform_tree x2a) \<and> \<h>\<s> (fringe (transform_tree x2a)) = w'\<close> 
    using P'_def by blast
  from pt have \<open>(A, roots ts) \<in> P\<close> 
    by simp
  then obtain B C a where 
    def: \<open>(A, roots ts) = (A, [Nt B, Nt C]) \<and> transform_prod (A, roots ts) = (A, [Tm [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub> , Nt B, Tm ]\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>, Tm [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub>, Nt C, Tm ]\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub> ]) 
\<or>
       (A, roots ts) = (A, [Tm a]) \<and> transform_prod (A, roots ts) = (A, [Tm [\<^sup>1\<^bsub>(A, [Tm a])\<^esub> , Tm ]\<^sup>1\<^bsub>(A, [Tm a])\<^esub>, Tm [\<^sup>2\<^bsub>(A, [Tm a])\<^esub>, Tm ]\<^sup>2\<^bsub>(A, [Tm a])\<^esub> ])\<close> 
    by fastforce
  then obtain t1 t2 e1 where ei_def: \<open>ts = [e1] \<or> ts = [t1, t2]\<close> 
    by blast
  then consider (Tm) \<open>roots ts = [Tm a]       \<and> ts = [Sym (Tm a)]\<close> | 
    (Nt_Nt) \<open>roots ts = [Nt B, Nt C] \<and> ts = [t1, t2]\<close> 
    by (smt (verit, best) def list.inject list.simps(8,9) not_Cons_self2 prod.inject root.elims sym.distinct(1))
  then show ?case
  proof(cases)
    case Tm
    then have ts_eq: \<open>ts = [Sym (Tm a)]\<close> and roots: \<open>roots ts = [Tm a]\<close> 
      by blast+
    then have \<open>transform_tree (Rule A ts) = Rule A [ Sym (Tm [\<^sup>1\<^bsub>(A,[Tm a])\<^esub>),  Sym(Tm ]\<^sup>1\<^bsub>(A,[Tm a])\<^esub>),  Sym (Tm [\<^sup>2\<^bsub>(A,[Tm a])\<^esub>),  Sym(Tm ]\<^sup>2\<^bsub>(A, [Tm a])\<^esub>)  ]\<close> 
      by simp
    then have \<open>\<h>\<s> (fringe (transform_tree (Rule A ts))) = [Tm a]\<close> 
      by simp
    also have \<open>... = w\<close> 
      using fr unfolding ts_eq by auto
    finally have \<open>\<h>\<s> (fringe (transform_tree (Rule A ts))) = w\<close> .
    moreover have \<open>parse_tree (P') (transform_tree (Rule A [Sym (Tm a)]))\<close> 
      using pt roots unfolding P'_def by force
    ultimately show ?thesis unfolding ts_eq P'_def by blast
  next
    case Nt_Nt
    then have ts_eq: \<open>ts = [t1, t2]\<close>  and roots: \<open>roots ts = [Nt B, Nt C]\<close> 
      by blast+
    then have root_t1_eq_B: \<open>root t1 = Nt B\<close> and root_t2_eq_C: \<open>root t2 = Nt C\<close>
      by blast+
    then have \<open>transform_tree (Rule A ts) = Rule A ((wrap2_Sym A (Nt B) (Nt C) One (transform_tree t1)) @ (wrap2_Sym A (Nt B) (Nt C) Two (transform_tree t2)))\<close>                
      by (simp add: ts_eq)  
    then have \<open>\<h>\<s> (fringe (transform_tree (Rule A ts))) = \<h>\<s> (fringe (transform_tree t1)) @  \<h>\<s> (fringe (transform_tree t2))\<close> 
      by auto
    also have \<open>... = fringe t1 @ fringe t2\<close> 
      using IH pt ts_eq by force
    also have \<open>... = fringe (Rule A ts)\<close> 
      using ts_eq by simp
    also have \<open>... = w\<close> 
      using fr by blast
    ultimately have \<open>\<h>\<s> (fringe (transform_tree (Rule A ts))) = w\<close> 
      by blast

    have \<open>parse_tree P t1\<close> and \<open>parse_tree P t2\<close> 
      using pt ts_eq by auto
    then have \<open>parse_tree P' (transform_tree t1)\<close> and \<open>parse_tree P' (transform_tree t2)\<close>
      by (simp add: IH ts_eq)+
    have root1: \<open>map Parse_Tree.root (wrap2_Sym A (Nt B) (Nt C) version.One (transform_tree t1)) = [Tm [\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub> , Nt B, Tm ]\<^sup>1\<^bsub>(A, [Nt B, Nt C])\<^esub>]\<close> 
      using root_t1_eq_B by auto
    moreover have root2: \<open>map Parse_Tree.root (wrap2_Sym A (Nt B) (Nt C) Two (transform_tree t2)) = [Tm [\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub>, Nt C, Tm ]\<^sup>2\<^bsub>(A, [Nt B, Nt C])\<^esub> ] \<close> 
      using root_t2_eq_C by auto
    ultimately have \<open>parse_tree P' (transform_tree (Rule A ts))\<close> 
      using \<open>parse_tree P' (transform_tree t1)\<close>  \<open>parse_tree P' (transform_tree t2)\<close>
        \<open>(A, map Parse_Tree.root ts) \<in> P\<close> roots
      by (force simp: ts_eq P'_def)
    then show ?thesis 
      using \<open>\<h>\<s> (fringe (transform_tree (Rule A ts))) = w\<close> by auto
  qed  
qed

lemma 
  transfer_parse_tree:
  assumes \<open>w \<in> Ders P S\<close>
  shows \<open>\<exists>w' \<in> Ders P' S. w = \<h>\<s> w'\<close>
proof-
  from assms obtain t where t_def: \<open>parse_tree P t \<and> fringe t = w \<and> root t = Nt S\<close> 
    using parse_tree_if_derives DersD by meson
  then have root_tr: \<open>root (transform_tree t) = Nt S\<close> 
    by blast
  from t_def have \<open>parse_tree P' (transform_tree t)  \<and>  \<h>\<s> (fringe (transform_tree t)) = w\<close> 
    using transform_tree_correct assms by blast
  with root_tr have \<open>fringe (transform_tree t) \<in> Ders P' S \<and> w = \<h>\<s> (fringe (transform_tree t))\<close> 
    using fringe_steps_if_parse_tree by (metis DersI)
  then show ?thesis by blast
qed

text\<open>This is essentially \<open>h(L') \<supseteq> L\<close>:\<close>
lemma P_imp_h_L':
  assumes \<open>w  \<in> Lang P S\<close>
  shows \<open>\<exists>w' \<in> L'. w = \<h> w'\<close>
proof-
  have ex: \<open>\<exists>w' \<in> Ders P' S. (map Tm w) = \<h>\<s> w'\<close> 
    using transfer_parse_tree by (meson Lang_Ders assms imageI subsetD)
  then obtain w' where w'_def: \<open>w' \<in> Ders P' S\<close> \<open>(map Tm w) = \<h>\<s> w'\<close> 
    using ex by blast 
  moreover obtain w'' where \<open>w' = map Tm w''\<close> 
    using w'_def the_hom_syms_tms_inj by metis
  then have \<open>w = \<h> w''\<close> 
    using h_eq_h_ext2 by (metis h_eq_h_ext w'_def(2))
  moreover have \<open>w'' \<in> L'\<close> 
    using DersD L'_def Lang_def \<open>w' = map Tm w''\<close> w'_def(1) by fastforce
  ultimately show ?thesis
    by blast
qed

text\<open>This lemma is used in the proof of the other direction \<open>(h(L') \<subseteq> L)\<close>:\<close>
lemma hom_ext_inv[simp]: 
  assumes \<open>\<pi> \<in> P\<close>
  shows \<open>\<h>\<s> (snd (transform_prod \<pi>)) = snd \<pi>\<close> 
proof-
  obtain A a B C where pi_def: \<open>\<pi> = (A, [Nt B, Nt C]) \<or> \<pi> = (A, [Tm a])\<close> 
    using assms by fastforce
  then show ?thesis 
    by auto
qed

text\<open>This lemma is essentially the other direction \<open>(h(L') \<subseteq> L)\<close>:\<close>
lemma L'_imp_h_P:
  assumes \<open>w'  \<in> L'\<close>
  shows \<open>\<h> w' \<in> Lang P S\<close>
proof-
  from assms L'_def have \<open>w' \<in> Lang P' S\<close> 
    by simp
  then have \<open>P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w'\<close> 
    by (simp add: Lang_def)
  then obtain n where \<open>P' \<turnstile> [Nt S] \<Rightarrow>(n) map Tm w'\<close> 
    by (metis rtranclp_power)
  then have \<open>P \<turnstile> [Nt S] \<Rightarrow>* \<h>\<s> (map Tm w')\<close> 
  proof(induction rule: deriven_induct)
    case 0
    then show ?case by auto
  next
    case (Suc n u A v x')
    from \<open>(A, x') \<in> P'\<close> obtain \<pi> where \<open>\<pi> \<in> P\<close> and transf_\<pi>_def: \<open>(transform_prod \<pi>) = (A, x')\<close> 
      using P'_def by auto
    then obtain x where \<pi>_def: \<open>\<pi> = (A, x)\<close> 
      by auto
    have \<open>\<h>\<s> (u @ [Nt A] @ v) = \<h>\<s> u @ \<h>\<s> [Nt A] @ \<h>\<s> v\<close> 
      by simp
    then have \<open> P \<turnstile> [Nt S] \<Rightarrow>* \<h>\<s> u @ \<h>\<s> [Nt A] @ \<h>\<s> v\<close> 
      using Suc.IH by auto
    then have \<open> P \<turnstile> [Nt S] \<Rightarrow>* \<h>\<s> u @ [Nt A] @ \<h>\<s> v\<close> 
      by simp
    then have \<open> P \<turnstile> [Nt S] \<Rightarrow>* \<h>\<s> u @ x @ \<h>\<s> v\<close> 
      using \<pi>_def \<open>\<pi> \<in> P\<close> derive.intros by (metis Transitive_Closure.rtranclp.rtrancl_into_rtrancl)
    have \<open>\<h>\<s> x' = \<h>\<s> (snd (transform_prod \<pi>))\<close> 
      by (simp add: transf_\<pi>_def)
    also have \<open>... = snd \<pi>\<close> 
      using hom_ext_inv \<open>\<pi> \<in> P\<close> by blast
    also have \<open>... = x\<close> 
      by (simp add: \<pi>_def)
    finally have \<open>\<h>\<s> x' = x\<close> 
      by simp
    with \<open> P \<turnstile> [Nt S] \<Rightarrow>* \<h>\<s> u @ x @ \<h>\<s> v\<close> have \<open> P \<turnstile> [Nt S] \<Rightarrow>* \<h>\<s> u @ \<h>\<s> x' @ \<h>\<s> v\<close> 
      by simp
    then show ?case by auto
  qed
  then show \<open>\<h> w' \<in> Lang P S\<close> 
    by (metis Lang_def h_eq_h_ext mem_Collect_eq)
qed



section\<open>The Theorem\<close>

text\<open>The constructive version of the Theorem, for a grammar already in CNF:\<close>
lemma Chomsky_Schuetzenberger_CNF:
  \<open>regular (brackets \<inter> Reg S)
   \<and> L = \<h> ` ((brackets \<inter> Reg S) \<inter> Dyck_lang \<Gamma>)
   \<and> hom_list (\<h> :: ('n,'t) bracket3 list \<Rightarrow> 't list)\<close>
proof -
  have \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> Dyck_lang \<Gamma> \<inter> Reg A\<close> (* This is the hard part of the proof - the local lemma in the textbook *)
  proof-
    have \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longrightarrow> x \<in> Dyck_lang \<Gamma> \<inter> Reg A\<close>
      using P'_imp_Reg P'_imp_bal Dyck_langI_tm by blast
    moreover have \<open>\<forall>A. \<forall>x. x \<in> Dyck_lang \<Gamma> \<inter> Reg A \<longrightarrow> P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<close> 
      using Reg_and_dyck_imp_P' by blast
    ultimately show ?thesis by blast
  qed
  then have \<open>L' = Dyck_lang \<Gamma> \<inter> (Reg S)\<close> 
    by (auto simp add: Lang_def L'_def)
  then have \<open>\<h> ` (Dyck_lang \<Gamma> \<inter> Reg S) = \<h> ` L'\<close> 
    by simp
  also have \<open>... = Lang P S\<close>
  proof(standard)
    show \<open>\<h> ` L' \<subseteq> Lang P S\<close> 
      using L'_imp_h_P by blast
  next
    show \<open>Lang P S \<subseteq> \<h> ` L'\<close> 
      using P_imp_h_L' by blast
  qed
  also have \<open>... = L\<close> 
    by (simp add: L_def)
  finally have \<open>\<h> ` (Dyck_lang \<Gamma> \<inter> Reg S) = L\<close> 
    by auto
  moreover have \<open>Dyck_lang \<Gamma> \<inter> (brackets \<inter> Reg S) = Dyck_lang \<Gamma> \<inter> Reg S\<close>
    using Dyck_lang_subset_brackets unfolding \<Gamma>_def by fastforce
  moreover have hom: \<open>hom_list \<h>\<close> 
    by (simp add: hom_list_def)
  moreover from finiteP have \<open>regular (brackets \<inter> Reg S)\<close> 
    using regular_Reg_inter by fast
  ultimately have \<open>regular (brackets \<inter> Reg S) \<and> L = \<h> ` ((brackets \<inter> Reg S) \<inter> Dyck_lang \<Gamma>) \<and> hom_list \<h>\<close> 
    by (simp add: inf_commute)
  then show ?thesis unfolding \<Gamma>_def by blast
qed

end (* Chomsky_Schuetzenberger_locale *)


text \<open>Now we want to prove the theorem without assuming that \<open>P\<close> is in CNF.
Of course any grammar can be converted into CNF, but this requires an infinite type of nonterminals
(because the conversion to CNF may need to invent new nonterminals).
Therefore we cannot just re-enter \<open>locale_P\<close>. Now we make all the assumption explicit.\<close>

text\<open>The theorem for any grammar, but only for languages not containing \<open>\<epsilon>\<close>:\<close>
lemma Chomsky_Schuetzenberger_not_empty:
  fixes P :: \<open>('n :: infinite, 't) Prods\<close> and S::"'n"
  defines \<open>L \<equiv> Lang P S - {[]}\<close>
  assumes finiteP: \<open>finite P\<close>
  shows \<open>\<exists>(R::('n,'t) bracket3 list set) h \<Gamma>. regular R \<and> L = h ` (R \<inter> Dyck_lang \<Gamma>) \<and> hom_list h\<close>
proof -
  define h where \<open>h = (the_hom:: ('n,'t) bracket3 list \<Rightarrow> 't list)\<close>
  obtain ps where ps_def: \<open>set ps = P\<close> 
    using \<open>finite P\<close> finite_list by auto
  from cnf_exists obtain ps' where
    \<open>CNF(set ps')\<close> and lang_ps_eq_lang_ps': \<open>Lang (set ps') S = Lang (set ps) S - {[]}\<close> 
    by blast
  then have \<open>finite (set ps')\<close>
    by auto
  interpret Chomsky_Schuetzenberger_locale \<open>(set ps')\<close> S
    apply unfold_locales
    using \<open>finite (set ps')\<close> \<open>CNF (set ps')\<close> by auto
  have \<open>regular (brackets \<inter> Reg S) \<and> Lang (set ps') S = h ` (brackets \<inter> Reg S \<inter> Dyck_lang \<Gamma>) \<and> hom_list h\<close> 
    using Chomsky_Schuetzenberger_CNF L_def h_def by argo
  moreover have  \<open>Lang (set ps') S = L - {[]}\<close> 
    unfolding lang_ps_eq_lang_ps' using L_def ps_def by (simp add: assms(1))
  ultimately have \<open>regular (brackets \<inter> Reg S) \<and> L - {[]} = h ` (brackets \<inter> Reg S \<inter> Dyck_lang \<Gamma>) \<and> hom_list h\<close> 
    by presburger
  then show ?thesis 
    using assms(1) by auto
qed

text\<open>The Chomsky-Schützenberger theorem that we really want to prove:\<close>
theorem Chomsky_Schuetzenberger:
  fixes P :: \<open>('n :: infinite, 't) Prods\<close> and S :: "'n"
  defines \<open>L \<equiv> Lang P S\<close>
  assumes finite: \<open>finite P\<close>
  shows \<open>\<exists>(R::('n,'t) bracket3 list set) h \<Gamma>. regular R \<and> L = h ` (R \<inter> Dyck_lang \<Gamma>) \<and> hom_list h\<close>
proof(cases \<open>[] \<in> L\<close>)
  case False
  then show ?thesis
    using Chomsky_Schuetzenberger_not_empty[OF finite, of S] unfolding L_def by auto
next
  case True
  obtain R::"('n,'t) bracket3 list set" and h and \<Gamma> where
    reg_R: \<open>(regular R)\<close> and L_minus_eq: \<open>L-{[]} = h ` (R \<inter> Dyck_lang \<Gamma>)\<close> and hom_h: \<open>hom_list h\<close> 
    by (metis L_def Chomsky_Schuetzenberger_not_empty finite)
  then have reg_R_union: \<open>regular(R \<union> {[]})\<close>
    by (meson regular_Un regular_nullstr)
  have \<open>[] = h([])\<close>
    by (simp add: hom_h hom_list_Nil)
  moreover have \<open>[] \<in> Dyck_lang \<Gamma>\<close> 
    by auto
  ultimately have \<open>[] \<in> h ` ((R \<union> {[]}) \<inter> Dyck_lang \<Gamma>)\<close> 
    by blast
  with True L_minus_eq have \<open>L = h ` ((R \<union> {[]}) \<inter> Dyck_lang \<Gamma>)\<close> 
    using \<open>[] \<in> Dyck_lang \<Gamma>\<close> \<open>[] = h []\<close> by auto
  then show ?thesis using reg_R_union hom_h by blast
qed

no_notation the_hom ("\<h>")
no_notation the_hom_syms ("\<h>\<s>")

end
