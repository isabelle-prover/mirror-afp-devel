(*<*)
theory Lifted_Predicates
imports
  HOL_Basis
begin

(*>*)
section\<open> Point-free notation \label{sec:lifted_predicates} \<close>

text\<open>

Typically we define predicates as functions of a state. The following
provide a somewhat comfortable point-free imitation of Isabelle/HOL's
operators.

\<close>

type_synonym 's pred = "'s \<Rightarrow> bool"

abbreviation (input)
  pred_K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>") where
  "\<langle>f\<rangle> \<equiv> \<lambda>s. f"

abbreviation (input)
  pred_not :: "'a pred \<Rightarrow> 'a pred" ("\<^bold>\<not> _" [40] 40) where
  "\<^bold>\<not>a \<equiv> \<lambda>s. \<not>a s"

abbreviation (input)
  pred_conj :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixr "\<^bold>\<and>" 35) where
  "a \<^bold>\<and> b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation (input)
  pred_disj :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixr "\<^bold>\<or>" 30) where
  "a \<^bold>\<or> b \<equiv> \<lambda>s. a s \<or> b s"

abbreviation (input)
  pred_implies :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixr "\<^bold>\<longrightarrow>" 25) where
  "a \<^bold>\<longrightarrow> b \<equiv> \<lambda>s. a s \<longrightarrow> b s"

abbreviation (input)
  pred_iff :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixr "\<^bold>\<longleftrightarrow>" 25) where
  "a \<^bold>\<longleftrightarrow> b \<equiv> \<lambda>s. a s \<longleftrightarrow> b s"

abbreviation (input)
  pred_eq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<^bold>=" 40) where
  "a \<^bold>= b \<equiv> \<lambda>s. a s = b s"

abbreviation (input)
  pred_neq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<^bold>\<noteq>" 40) where
  "a \<^bold>\<noteq> b \<equiv> \<lambda>s. a s \<noteq> b s"

abbreviation (input)
  pred_If :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("(If (_)/ Then (_)/ Else (_))" [0, 0, 10] 10)
  where "If P Then x Else y \<equiv> \<lambda>s. if P s then x s else y s"

abbreviation (input)
  pred_less :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<^bold><" 40) where
  "a \<^bold>< b \<equiv> \<lambda>s. a s < b s"

abbreviation (input)
  pred_less_eq :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<^bold>\<le>" 40) where
  "a \<^bold>\<le> b \<equiv> \<lambda>s. a s \<le> b s"

abbreviation (input)
  pred_greater :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<^bold>>" 40) where
  "a \<^bold>> b \<equiv> \<lambda>s. a s > b s"

abbreviation (input)
  pred_greater_eq :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<^bold>\<ge>" 40) where
  "a \<^bold>\<ge> b \<equiv> \<lambda>s. a s \<ge> b s"

abbreviation (input)
  pred_plus :: "('a \<Rightarrow> 'b::plus) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>+" 65) where
  "a \<^bold>+ b \<equiv> \<lambda>s. a s + b s"

abbreviation (input)
  pred_minus :: "('a \<Rightarrow> 'b::minus) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>-" 65) where
  "a \<^bold>- b \<equiv> \<lambda>s. a s - b s"

abbreviation (input)
  pred_times :: "('a \<Rightarrow> 'b::times) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>*" 65) where
  "a \<^bold>* b \<equiv> \<lambda>s. a s * b s"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a pred) \<Rightarrow> 'a pred" (binder "\<^bold>\<forall>" 10) where
  "\<^bold>\<forall>x. P x \<equiv> \<lambda>s. \<forall>x. P x s"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a pred) \<Rightarrow> 'a pred" (binder "\<^bold>\<exists>" 10) where
  "\<^bold>\<exists>x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

(* this one is applicative-functor ish *)
abbreviation (input)
  pred_app :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<^bold>$" 100) where
  "f \<^bold>$ g \<equiv> \<lambda>s. f s (g s)"

(* this one is monadic postcondition ish *)
abbreviation (input)
  pred_app' :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<^bold>$\<^bold>$" 100) where
  "f \<^bold>$\<^bold>$ g \<equiv> \<lambda>s. f (g s) s"

abbreviation (input)
  pred_member :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a pred" (infix "\<^bold>\<in>" 40) where
  "a \<^bold>\<in> b \<equiv> \<lambda>s. a s \<in> b s"

abbreviation (input)
  pred_subseteq :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a pred" (infix "\<^bold>\<subseteq>" 50) where
  "A \<^bold>\<subseteq> B \<equiv> \<lambda>s. A s \<subseteq> B s"

abbreviation (input)
  pred_union :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixl "\<^bold>\<union>" 65) where
  "a \<^bold>\<union> b \<equiv> \<lambda>s. a s \<union> b s"

abbreviation (input)
  pred_inter :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixl "\<^bold>\<inter>" 65) where
  "a \<^bold>\<inter> b \<equiv> \<lambda>s. a s \<inter> b s"

abbreviation (input)
  pred_conjoin :: "'a pred list \<Rightarrow> 'a pred" where
  "pred_conjoin xs \<equiv> foldr (\<^bold>\<and>) xs \<langle>True\<rangle>"

abbreviation (input)
  pred_disjoin :: "'a pred list \<Rightarrow> 'a pred" where
  "pred_disjoin xs \<equiv> foldr (\<^bold>\<or>) xs \<langle>False\<rangle>"

abbreviation (input)
  pred_min :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "pred_min x y \<equiv> \<lambda>s. min (x s) (y s)"

abbreviation (input)
  pred_max :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "pred_max x y \<equiv> \<lambda>s. max (x s) (y s)"

abbreviation (input)
  NULL :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a pred" where
  "NULL a \<equiv> \<lambda>s. a s = None"

abbreviation (input)
  EMPTY :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a pred" where
  "EMPTY a \<equiv> \<lambda>s. a s = {}"

abbreviation (input)
  LIST_NULL :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a pred" where
  "LIST_NULL a \<equiv> \<lambda>s. a s = []"

abbreviation (input)
  SIZE :: "('a \<Rightarrow> 'b::size) \<Rightarrow> 'a \<Rightarrow> nat" where
  "SIZE a \<equiv> \<lambda>s. size (a s)"

abbreviation (input)
  SET :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "SET a \<equiv> \<lambda>s. set (a s)"

abbreviation (input)
  pred_singleton :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "pred_singleton x \<equiv> \<lambda>s. {x s}"

abbreviation (input)
  pred_list_nth :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>!" 150) where
  "xs \<^bold>! i \<equiv> \<lambda>s. xs s ! i s"

abbreviation (input)
  pred_list_append :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b list" (infixr "\<^bold>@" 65) where
  "xs \<^bold>@ ys \<equiv> \<lambda>s. xs s @ ys s"

abbreviation (input)
  FST :: "'a pred \<Rightarrow> ('a \<times> 'b) pred" where
  "FST P \<equiv> \<lambda>s. P (fst s)"

abbreviation (input)
  SND :: "'b pred \<Rightarrow> ('a \<times> 'b) pred" where
  "SND P \<equiv> \<lambda>s. P (snd s)"

abbreviation (input)
  pred_pair :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" (infixr "\<^bold>\<otimes>" 60) where
  "a \<^bold>\<otimes> b \<equiv> \<lambda>s. (a s, b s)"
(*<*)

end
(*>*)
