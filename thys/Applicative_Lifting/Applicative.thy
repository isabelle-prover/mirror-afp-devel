(* Author: Joshua Schneider *)

section \<open>Lifting with applicative functors\<close>

theory Applicative
imports Main
keywords "applicative" :: thy_goal and "print_applicative" :: diag
begin

ML_file "applicative.ML"

method_setup applicative_unfold = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.unfold_wrapper_tac ctxt opt_af)) *}
  "unfold to applicative expression"

method_setup applicative_fold = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.fold_wrapper_tac ctxt opt_af)) *}
  "folding of applicative expression"

method_setup applicative_nf = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.normalize_wrapper_tac ctxt opt_af)) *}
  "reduce equation using applicative normal form"

method_setup applicative_lifting = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.lifting_wrapper_tac ctxt opt_af)) *}
  "reduce equation lifted with applicative functor"

ML {* Outer_Syntax.local_theory_to_proof @{command_keyword "applicative"}
  "register applicative functors"
  (Parse.binding --
    Scan.optional (@{keyword "("} |-- Parse.list Parse.short_ident --| @{keyword ")"}) [] --|
    @{keyword "for"} --| Parse.reserved "pure" --| @{keyword ":"} -- Parse.term --|
    Parse.reserved "ap" --| @{keyword ":"} -- Parse.term >>
    (fn (((name, combs), pure), ap) => Applicative.applicative_cmd name pure ap combs)) *}

ML {* Outer_Syntax.command @{command_keyword "print_applicative"}
  "print registered applicative functors"
  (Scan.succeed (Toplevel.keep (Applicative.print_afuns o Toplevel.context_of))) *}

attribute_setup applicative_unfold =
  {* Scan.lift (Scan.option Parse.xname >> Applicative.add_unfold_attrib) *}
  "register rules for unfolding to applicative expressions"

attribute_setup applicative_lifted =
  {* Scan.lift (Parse.xname >> Applicative.forward_lift_attrib) *}
  "lift an equation to an applicative functor"

subsection \<open>Overloaded applicative operators\<close>

consts pure :: "'a \<Rightarrow> 'b"

consts ap :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
locale applicative_syntax begin
  notation ap (infixl "\<diamondop>" 70)
end
hide_const (open) ap

end
