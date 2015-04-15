(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_pred
imports
  Main
begin

(*>*)
section{* Lifted predicates *}

text{*

\label{sec:cimp-lifted-predicates}

Typically we define predicates as functions of a state. The following
provide a somewhat comfortable imitatation of Isabelle/HOL's
operators.

*}

(*
FIXME precedences probably need tweaking. @{text "pred_diff"}
FIXME consider bounded quantifiers. See Set.thy. Don't care about printing so maybe not too hard.
*)

abbreviation (input)
  pred_pair :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" (infixr "\<otimes>" 60) where
  "a \<otimes> b \<equiv> \<lambda>s. (a s, b s)"

abbreviation (input)
  pred_in :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" (infix "in" 50) where
  "a in A \<equiv> \<lambda>s. a s \<in> A s"

abbreviation (input)
  pred_subseteq :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" (infix "subseteq" 50) where
  "A subseteq B \<equiv> \<lambda>s. A s \<subseteq> B s"

abbreviation (input)
  pred_union :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixl "union" 65) where
  "a union b \<equiv> \<lambda>s. a s \<union> b s"

abbreviation (input)
  pred_diff :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixr "diff" 65) where
  "a diff b \<equiv> \<lambda>s. a s - b s"

abbreviation (input)
  pred_comp :: "(('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'd" (infixl "\<bigcirc>" 55) where
  "f \<bigcirc> g \<equiv> \<lambda>s. f (\<lambda>b. g b s) s"

abbreviation (input)
  pred_app :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<triangleright>" 100) where
  "f \<triangleright> g \<equiv> \<lambda>s. f (g s) s"

abbreviation (input)
  pred_eq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "eq" 40) where
  "a eq b \<equiv> \<lambda>s. a s = b s"

abbreviation (input)
  pred_neq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "neq" 40) where
  "a neq b \<equiv> \<lambda>s. a s \<noteq> b s"

abbreviation (input)
  pred_lt :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "lt" 40) where
  "a lt b \<equiv> \<lambda>s. a s < b s"

abbreviation (input)
  pred_and :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "and" 35) where
  "a and b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation (input)
  pred_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "or" 30) where
  "a or b \<equiv> \<lambda>s. a s \<or> b s"

abbreviation (input)
  pred_not :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("not _" [40] 40) where
  "not a \<equiv> \<lambda>s. \<not>a s"

abbreviation (input)
  pred_imp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "imp" 25) where
  "a imp b \<equiv> \<lambda>s. a s \<longrightarrow> b s"

abbreviation (input)
  pred_iff :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "iff" 25) where
  "a iff b \<equiv> \<lambda>s. a s \<longleftrightarrow> b s"

abbreviation (input)
  pred_K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>") where
  "\<langle>f\<rangle> \<equiv> \<lambda>s. f"

abbreviation (input)
  pred_conjoin :: "('a \<Rightarrow> bool) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "pred_conjoin xs \<equiv> foldr (op and) xs \<langle>True\<rangle>"

abbreviation (input)
  pred_singleton :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "pred_singleton x \<equiv> \<lambda>s. {x s}"

abbreviation (input)
  pred_empty :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" ("empty _" [40] 40) where
  "empty a \<equiv> \<lambda>s. a s = {}"

abbreviation (input)
  pred_map_empty :: "('a \<Rightarrow> ('b \<Rightarrow> 'c option)) \<Rightarrow> 'a \<Rightarrow> bool" ("map'_empty _" [40] 40) where
  "map_empty a \<equiv> \<lambda>s. a s = Map.empty"

abbreviation (input)
  pred_list_null :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> bool" ("list'_null _" [40] 40) where
  "list_null a \<equiv> \<lambda>s. a s = []"

abbreviation (input)
  pred_null :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> bool" ("null _" [40] 40) where
  "null a \<equiv> \<lambda>s. a s = None"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "EXS " 10) where
  "EXS x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "ALLS " 10) where
  "ALLS x. P x \<equiv> \<lambda>s. \<forall>x. P x s"

abbreviation (input)
  pred_If :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("(If (_)/ Then (_)/ Else (_))" [0, 0, 10] 10)
  where "If P Then x Else y \<equiv> \<lambda>s. if P s then x s else y s"
(*<*)

end
(*>*)
