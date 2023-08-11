theory boolean_algebra
  imports Main
begin

(*-----------------------------------*)
text\<open>Technical configuration\<close>
declare[[smt_timeout=30]]
declare[[show_types]]
(* declare[[syntax_ambiguity_warning=false]] *)
sledgehammer_params[isar_proof=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3, atoms=a b c d] (*default Nitpick settings*)
text\<open>We hide some Isabelle/HOL notation from the libraries (which we don't use) to avoid overloading\<close>
hide_const(open) List.list.Nil no_notation List.list.Nil ("[]")  (*We have no use for lists... *)
hide_const(open) Relation.converse no_notation Relation.converse ("(_\<inverse>)" [1000] 999) (*..nor for relations in this work*)
hide_const(open) Fun.comp no_notation Fun.comp (infixl "\<circ>" 55) (*we redefine function composition below*)
hide_const(open) Groups.plus_class.plus no_notation Groups.plus_class.plus (infixl "+" 65) (*we don't use this*)
hide_const(open) Groups.times_class.times no_notation Groups.times_class.times (infixl "*" 70) (*we don't use this*)
hide_const(open) Groups.minus_class.minus no_notation Groups.minus_class.minus (infixl "-" 65) (*we don't use this*)
hide_const(open) Groups.uminus_class.uminus no_notation Groups.uminus_class.uminus ("- _" [81] 80) (*we don't use this*)
(*-----------------------------------*)

section \<open>Shallow semantical embedding of (a logic of) Boolean algebras\<close>

text\<open>We encode Boolean algebras via their (Stone) representation as algebras of sets ('fields of sets').
This means that each element of (the carrier of) the algebra will be a set of 'points'.
Inspired by the 'propositions as sets of worlds' paradigm from modal logic, we may think of points 
as being 'worlds', and thus of the elements of our Boolean algebras as 'propositions'.
Of course, this is just one among many possible interpretations, and nothing stops us from thinking 
of points as any other kind of object (e.g., they can be sets, functions, sets of functions, etc.).
\<close>

text\<open>We utilize a particular naming convention: The type parameter 'w is employed for the
domain/universe of 'points'. We conveniently introduce the (parametric) type-alias @{text "('w)\<sigma>"} 
as shorthand for @{text "'w\<Rightarrow>bool"}. Hence, the elements of our algebra are objects of type @{text "('w)\<sigma>"},
and thus correspond to (characteristic functions of) sets of 'points'.
Set-valued (resp. set-domain) functions are thus functions that have sets as their codomain (resp. domain),
they are basically anything with a (parametric) type @{text "'a\<Rightarrow>('w)\<sigma>"} (resp. @{text "('w)\<sigma>\<Rightarrow>'a)"}.\<close>

text\<open>Type for (characteristic functions of) sets (of 'points')\<close>
type_synonym 'w \<sigma> = \<open>'w \<Rightarrow> bool\<close>

text\<open>In the sequel, we will (try to) enforce the following naming convention:\<close>

text\<open>(i) Upper-case latin letters (A, B, D, M, P, S, X, etc.) denote arbitrary sets (type @{text "('w)\<sigma>"}).
We will employ lower-case letters (p, q, x, w, etc.) to denote variables playing the role of 'points'.
In some contexts, the letters S and D will be employed to denote sets/domains of sets (of 'points').\<close>

text\<open>(ii) Greek letters denote arbitrary set-valued functions (type @{text "'a\<Rightarrow>('w)\<sigma>"}).
We employ the letters @{text "\<phi>, \<psi> and \<eta>"} to denote arbitrary unary operations
(with type @{text "('w)\<sigma>\<Rightarrow>('w)\<sigma>)"}.\<close>

text\<open>(iii) Upper-case calligraphic letters @{text "(\<B>, \<I>, \<C>, \<F>, etc.)"} are reserved for unary operations that are
intended to act as 'topological operators' in the given context.\<close>

subsection \<open>Encoding Boolean operations\<close>

text\<open>Standard inclusion-based order structure on sets.\<close>
definition subset::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" (infixr "\<^bold>\<le>" 45) 
  where "A \<^bold>\<le> B \<equiv> \<forall>p. A p \<longrightarrow> B p"
definition setequ::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool" (infixr "\<^bold>=" 45) 
  where "A \<^bold>= B \<equiv> \<forall>p. A p \<longleftrightarrow> B p"

named_theorems order (*to group together order-related definitions*)
declare setequ_def[order] subset_def[order]

lemma subset_char1: "(A \<^bold>\<le> B) = (\<forall>C. B \<^bold>\<le> C \<longrightarrow> A \<^bold>\<le> C)" by (metis subset_def)
lemma subset_char2: "(A \<^bold>\<le> B) = (\<forall>C. C \<^bold>\<le> A \<longrightarrow> C \<^bold>\<le> B)" by (metis subset_def)

text\<open>These (trivial) lemmas are intended to help automated tools.\<close>
lemma setequ_char: "(A \<^bold>= B) = (A \<^bold>\<le> B \<and> B \<^bold>\<le> A)" unfolding order by blast
lemma setequ_ext: "(A \<^bold>= B) = (A = B)" unfolding order by blast

text\<open>We now encode connectives for (distributive and complemented) bounded lattices, mostly 
by reusing their counterpart meta-logical HOL connectives.\<close>
definition meet::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>p. (A p) \<and> (B p)" \<comment>\<open> intersection \<close>
definition join::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>p. (A p) \<or> (B p)" \<comment>\<open> union \<close>
definition top::"'w \<sigma>" ("\<^bold>\<top>")    
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"   \<comment>\<open> universe \<close>
definition bottom::"'w \<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"  \<comment>\<open> empty-set \<close>

text\<open>And introduce further operations to obtain a Boolean algebra (of sets).\<close>
definition compl::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>\<midarrow>_" [57]58)
  where "\<^bold>\<midarrow>A  \<equiv> \<lambda>p. \<not>(A p)" \<comment>\<open>  (set-)complement \<close>
definition impl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>p. (A p) \<longrightarrow> (B p)" \<comment>\<open>  (set-)implication \<close>
definition diff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) 
  where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>p. (A p) \<and> \<not>(B p)" \<comment>\<open>  (set-)difference \<close>
definition dimpl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51)
  where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>p. (A p) = (B p)" \<comment>\<open>  double implication \<close>
definition sdiff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<triangle>" 51)
  where "A \<^bold>\<triangle> B \<equiv> \<lambda>p. (A p) \<noteq> (B p)" \<comment>\<open>  symmetric difference (aka. xor)  \<close>

named_theorems conn (*to group together definitions for algebraic connectives*)
declare meet_def[conn] join_def[conn] top_def[conn] bottom_def[conn]
        impl_def[conn] dimpl_def[conn] diff_def[conn] sdiff_def[conn] compl_def[conn]

text\<open>Verify characterization for some connectives.\<close>
lemma compl_char: "\<^bold>\<midarrow>A = A \<^bold>\<rightarrow> \<^bold>\<bottom>" unfolding conn by simp
lemma impl_char: "A \<^bold>\<rightarrow> B = \<^bold>\<midarrow>A \<^bold>\<or> B" unfolding conn by simp
lemma dimpl_char: "A \<^bold>\<leftrightarrow> B = (A \<^bold>\<rightarrow> B) \<^bold>\<and> (B \<^bold>\<rightarrow> A)" unfolding conn by blast
lemma diff_char1: "A \<^bold>\<leftharpoonup> B = A \<^bold>\<and> \<^bold>\<midarrow>B" unfolding conn by simp
lemma diff_char2: "A \<^bold>\<leftharpoonup> B = \<^bold>\<midarrow>(A \<^bold>\<rightarrow> B)" unfolding conn by simp
lemma sdiff_char1: "A \<^bold>\<triangle> B = (A \<^bold>\<leftharpoonup> B) \<^bold>\<or> (B \<^bold>\<leftharpoonup> A)" unfolding conn by blast
lemma sdiff_char2: "A \<^bold>\<triangle> B = \<^bold>\<midarrow>(A \<^bold>\<leftrightarrow> B)" unfolding conn by simp

text\<open>We can verify that (quite trivially) this algebra satisfies some properties of lattices.\<close>
lemma L1: "A \<^bold>= A \<^bold>\<or> A" unfolding conn order by simp
lemma L2: "A \<^bold>= A \<^bold>\<and> A" unfolding conn order by simp
lemma L3: "A \<^bold>\<le> A \<^bold>\<or> B" unfolding conn order by simp
lemma L4: "A \<^bold>\<and> B \<^bold>\<le> A" unfolding conn order by simp
lemma L5: "(A \<^bold>\<and> B) \<^bold>\<or> B \<^bold>= B" unfolding setequ_char conn order by simp 
lemma L6: "A \<^bold>\<and> (A \<^bold>\<or> B) \<^bold>= A" unfolding setequ_char conn order by simp
lemma L7: "A \<^bold>\<le> C \<and> B \<^bold>\<le> C \<longrightarrow> A \<^bold>\<or> B \<^bold>\<le> C" unfolding conn order by simp 
lemma L8: "C \<^bold>\<le> A \<and> C \<^bold>\<le> B \<longrightarrow> C \<^bold>\<le> A \<^bold>\<and> B" unfolding conn order by simp
lemma L9:  "A \<^bold>\<le> B \<longleftrightarrow> (A \<^bold>\<or> B) \<^bold>= B" unfolding setequ_char conn order by simp
lemma L10: "B \<^bold>\<le> A \<longleftrightarrow> (A \<^bold>\<and> B) \<^bold>= B" unfolding setequ_char conn order by simp
lemma L11: "A \<^bold>\<le> B \<and> C \<^bold>\<le> D \<longrightarrow> A \<^bold>\<or> C \<^bold>\<le> B \<^bold>\<or> D" unfolding conn order by simp
lemma L12: "A \<^bold>\<le> B \<and> C \<^bold>\<le> D \<longrightarrow> A \<^bold>\<and> C \<^bold>\<le> B \<^bold>\<and> D" unfolding conn order by simp
lemma L13: "A \<^bold>\<and> \<^bold>\<top> \<^bold>= A" unfolding conn order by simp
lemma L14: "A \<^bold>\<or> \<^bold>\<bottom> \<^bold>= A" unfolding conn order by simp
lemma L15: "A \<^bold>\<le> B \<longleftrightarrow> (\<forall>C. C \<^bold>\<and> A \<^bold>\<le> C \<^bold>\<and> B)" by (metis L3 L4 L5 L8 setequ_char subset_char1)
lemma L16: "A \<^bold>\<le> B \<longleftrightarrow> (\<forall>C. C \<^bold>\<or> A \<^bold>\<le> C \<^bold>\<or> B)" by (metis L11 L4 L5 setequ_char setequ_ext)

text\<open>These properties below hold in particular also for Boolean algebras.\<close>
lemma BA_impl: "A \<^bold>\<le> B \<longleftrightarrow> A \<^bold>\<rightarrow> B \<^bold>= \<^bold>\<top>" unfolding conn order by simp
lemma BA_distr1: "(A \<^bold>\<and> (B \<^bold>\<or> C)) \<^bold>= ((A \<^bold>\<and> B) \<^bold>\<or> (A \<^bold>\<and> C))" unfolding setequ_char conn order by simp
lemma BA_distr2: "(A \<^bold>\<or> (B \<^bold>\<and> C)) \<^bold>= ((A \<^bold>\<or> B) \<^bold>\<and> (A \<^bold>\<or> C))" unfolding conn order by blast
lemma BA_cp: "A \<^bold>\<le> B \<longleftrightarrow> \<^bold>\<midarrow>B \<^bold>\<le> \<^bold>\<midarrow>A" unfolding conn order by blast 
lemma BA_deMorgan1: "\<^bold>\<midarrow>(A \<^bold>\<or> B) \<^bold>= (\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B)" unfolding conn order by simp
lemma BA_deMorgan2: "\<^bold>\<midarrow>(A \<^bold>\<and> B) \<^bold>= (\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" unfolding conn order by simp
lemma BA_dn: "\<^bold>\<midarrow>\<^bold>\<midarrow>A \<^bold>= A" unfolding conn order by simp
lemma BA_cmpl_equ: "(\<^bold>\<midarrow>A \<^bold>= B) = (A \<^bold>= \<^bold>\<midarrow>B)" unfolding conn order by blast


text\<open>We conveniently introduce these properties of sets of sets (of points).\<close>
definition meet_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool"
  where "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
definition join_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool"
  where "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

definition upwards_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool"
  where "upwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<le> Y \<longrightarrow> S Y"
definition downwards_closed::"('w \<sigma>)\<sigma> \<Rightarrow> bool" 
  where "downwards_closed S \<equiv> \<forall>X Y. S X \<and> Y \<^bold>\<le> X \<longrightarrow> S Y"


subsection \<open>Atomicity and primitive equality\<close>

text\<open>We can verify indeed that the algebra is atomic (in three different ways) by relying on the
presence of primitive equality in HOL.\<close>

lemma atomic1: "\<forall>w. \<exists>Q. Q w \<and> (\<forall>P. P w \<longrightarrow> Q \<^bold>\<le> P)" unfolding order using the_sym_eq_trivial by metis

definition "atom A \<equiv> \<not>(A \<^bold>= \<^bold>\<bottom>) \<and> (\<forall>P. A \<^bold>\<le> P \<or> A \<^bold>\<le> \<^bold>\<midarrow>P)"

lemma atomic2: "\<forall>w. \<exists>Q. Q w \<and> atom Q" unfolding atom_def order conn using the_sym_eq_trivial by metis
lemma atomic3: "\<forall>P. \<not>(P \<^bold>= \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<^bold>\<le> P)" unfolding atom_def order conn by fastforce

text\<open>Now with interactive proof:\<close>
lemma "\<forall>P. \<not>(P \<^bold>= \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<^bold>\<le> P)"
proof -
  { fix P::"'w \<sigma>"
    { assume "\<not>(P \<^bold>= \<^bold>\<bottom>)"
      hence "\<exists>v. P v" unfolding conn order by simp
      then obtain w where 1:"P w" by (rule exE)
      let ?Q="\<lambda>v. v = w" \<comment>\<open> using HOL primitive equality \<close>
      have 2: "atom ?Q" unfolding atom_def unfolding conn order by simp
      have "\<forall>v. ?Q v \<longrightarrow> P v" using 1 by simp
      hence 3: "?Q \<^bold>\<le> P" unfolding order by simp
      from 2 3 have "\<exists>Q. atom Q \<and> Q \<^bold>\<le> P" by blast
    } hence "\<not>(P \<^bold>= \<^bold>\<bottom>) \<longrightarrow> (\<exists>Q. atom Q \<and> Q \<^bold>\<le> P)" by (rule impI)
  } thus ?thesis by (rule allI)
qed

subsection \<open>Miscellaneous notions\<close>

text\<open>We add some miscellaneous notions that will be useful later.\<close>

abbreviation "isEmpty S \<equiv> \<forall>x. \<not>S x"
abbreviation "nonEmpty S \<equiv> \<exists>x. S x"

text\<open>Function composition.\<close>
definition fun_comp :: "('b \<Rightarrow> 'c) \<Rightarrow> ( 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<circ>" 75) 
  where "\<phi> \<circ> \<psi> \<equiv> \<lambda>x. \<phi> (\<psi> x)"

text\<open>Inverse projection maps a unary function to a 'projected' binary function wrt. its 1st argument.\<close>
abbreviation inv_proj::\<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)\<close> ("(_)\<upharpoonleft>")
  where "D\<upharpoonleft> \<equiv> \<lambda>A B. D A"

text\<open>Image of a mapping @{text "\<phi>"}, with range as an special case.\<close>
definition image::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" ("\<lbrakk>_ _\<rbrakk>") 
  where "\<lbrakk>\<phi> S\<rbrakk> \<equiv> \<lambda>y. \<exists>x. (S x) \<and> (\<phi> x) = y"
definition range::"('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> bool)" ("\<lbrakk>_'_\<rbrakk>") 
  where "\<lbrakk>\<phi> _\<rbrakk> \<equiv> \<lambda>Y. \<exists>x. (\<phi> x) = Y"
lemma range_char1: "\<lbrakk>\<phi> _\<rbrakk> = \<lbrakk>\<phi> (\<lambda>x. True)\<rbrakk>" by (simp add: image_def range_def)
lemma range_char2: "\<lbrakk>\<phi> _\<rbrakk> = (\<lambda>X. \<exists>S. \<lbrakk>\<phi> S\<rbrakk> X)" unfolding range_def image_def by blast

lemma image_comp: "\<lbrakk>(f \<circ> g) S\<rbrakk> = \<lbrakk>f \<lbrakk>g S\<rbrakk>\<rbrakk>" unfolding fun_comp_def image_def by metis

end
