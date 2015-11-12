section {* Syntactic Matching in the Simplifier *}
theory Syntax_Match
imports Main
begin

subsection {* Non-Matching *}

text {*
  We define the predicates @{text "syntax_nomatch"} 
  and @{text "syntax_fo_nomatch"}. The expression 
  @{text "syntax_nomatch pattern object"} is simplified to true only if 
  the term @{text "pattern"} syntactically matches the term @{text "object"}. 
  Note that, semantically, @{text "syntax_nomatch pattern object"} is always
  true. While @{text "syntax_nomatch"} does higher-order matching, 
  @{text "syntax_fo_nomatch"} does first-order matching.

  The intended application of these predicates are as guards for simplification
  rules, enforcing additional syntactic restrictions on the applicability of
  the simplification rule.
*}
definition syntax_nomatch :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  where syntax_nomatch_def: "syntax_nomatch pat obj \<equiv> True"
definition syntax_fo_nomatch :: "'a \<Rightarrow> 'b \<Rightarrow> bool" 
  where syntax_fo_nomatch_def: "syntax_fo_nomatch pat obj \<equiv> True"

(* Prevent simplifier to simplify inside syntax_xx predicates *)
lemma [cong]: "syntax_fo_nomatch x y = syntax_fo_nomatch x y" by simp
lemma [cong]: "syntax_nomatch x y = syntax_nomatch x y" by simp

ML {*
structure Syntax_Match = struct
  val nomatch_thm = @{thm syntax_nomatch_def};
  val fo_nomatch_thm = @{thm syntax_fo_nomatch_def};

  fun fo_nomatch_simproc ctxt credex = let
    (*val ctxt = Simplifier.the_context ss;*)
    val thy = Proof_Context.theory_of ctxt;

    val redex = Thm.term_of credex;
    val (_,[pat,obj]) = strip_comb redex;

    fun fo_matches po = (Pattern.first_order_match 
      thy po (Vartab.empty, Vartab.empty); true) handle Pattern.MATCH => false;
  in
    if fo_matches (pat,obj) then NONE else SOME fo_nomatch_thm
  end

  fun nomatch_simproc ctxt credex = let
    (*val ctxt = Simplifier.the_context ss;*)
    val thy = Proof_Context.theory_of ctxt;

    val redex = Thm.term_of credex;
    val (_,[pat,obj]) = strip_comb redex;
  in
    if Pattern.matches thy (pat,obj) then NONE else SOME nomatch_thm
  end
end
*}
simproc_setup nomatch ("syntax_nomatch pat obj") 
  = {* K Syntax_Match.nomatch_simproc *}
simproc_setup fo_nomatch ("syntax_fo_nomatch pat obj") 
  = {* K Syntax_Match.fo_nomatch_simproc *}


subsection {* Examples *}
subsubsection {* Ordering AC-structures *}
text {*
  Currently, the simplifier rules for ac-rewriting only work when
  associativity groups to the right. Here, we define rules that work for
  associativity grouping to the left. They are useful for operators where 
  syntax is parsed (and pretty-printed) left-associative.
*}

locale ac_operator =
  fixes f
  assumes right_assoc: "f (f a b) c = f a (f b c)"
  assumes commute: "f a b = f b a"
begin
  lemmas left_assoc = right_assoc[symmetric]
  lemma left_commute: "f a (f b c) = f b (f a c)"
    apply (simp add: left_assoc)
    apply (simp add: commute)
    done

  lemmas right_ac = right_assoc left_commute commute

  lemma right_commute: "f (f a b) c = f (f a c) b"
    by (simp add: right_ac)

  lemma safe_commute: "syntax_fo_nomatch (f x y) a \<Longrightarrow> f a b = f b a"
    by (simp add: right_ac)

  lemmas left_ac = left_assoc right_commute safe_commute
end

interpretation mult: ac_operator "op *::'a::ab_semigroup_mult \<Rightarrow> _ \<Rightarrow> _"
  apply unfold_locales
  apply (simp_all add: ac_simps)
  done

interpretation add: ac_operator "op +::'a::ab_semigroup_add \<Rightarrow> _ \<Rightarrow> _"
  apply unfold_locales
  apply (simp_all add: ac_simps)
  done

text {* Attention: @{text "conj_assoc"} is in standard simpset, it has to be 
  removed when using @{text "conj.left_ac"} ! *}
interpretation conj: ac_operator "op \<and>"
  by unfold_locales auto
interpretation disj: ac_operator "op \<or>"
  by unfold_locales auto

end
