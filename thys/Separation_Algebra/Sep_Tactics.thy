(* Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

section "Separation Logic Tactics"

theory Sep_Tactics
imports Separation_Algebra
begin

ML_file "sep_tactics.ML"

text {* A number of proof methods to assist with reasoning about separation logic. *}


section {* Selection (move-to-front) tactics *}

method_setup sep_select = {*
  Scan.lift Parse.int >> (fn n => fn ctxt => SIMPLE_METHOD' (sep_select_tac ctxt n))
*} "Select nth separation conjunct in conclusion"

method_setup sep_select_asm = {*
  Scan.lift Parse.int >> (fn n => fn ctxt => SIMPLE_METHOD' (sep_select_asm_tac ctxt n))
*} "Select nth separation conjunct in assumptions"


section {* Substitution *}

method_setup "sep_subst" = {*
  Scan.lift (Args.mode "asm" -- Scan.optional (Args.parens (Scan.repeat Parse.nat)) [0]) --
    Attrib.thms >> (fn ((asm, occs), thms) => fn ctxt =>
      SIMPLE_METHOD' ((if asm then sep_subst_asm_tac else sep_subst_tac) ctxt occs thms))
*}
"single-step substitution after solving one separation logic assumption"


section {* Forward Reasoning *}

method_setup "sep_drule" = {*
  Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (sep_dtac ctxt thms))
*} "drule after separating conjunction reordering"

method_setup "sep_frule" = {*
  Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (sep_ftac ctxt thms))
*} "frule after separating conjunction reordering"


section {* Backward Reasoning *}

method_setup "sep_rule" = {*
  Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (sep_rtac ctxt thms))
*} "applies rule after separating conjunction reordering"


section {* Cancellation of Common Conjuncts via Elimination Rules *}

named_theorems sep_cancel

text {*
  The basic @{text sep_cancel_tac} is minimal. It only eliminates
  erule-derivable conjuncts between an assumption and the conclusion.

  To have a more useful tactic, we augment it with more logic, to proceed as
  follows:
  \begin{itemize}
  \item try discharge the goal first using @{text tac}
  \item if that fails, invoke @{text sep_cancel_tac}
  \item if @{text sep_cancel_tac} succeeds
    \begin{itemize}
    \item try to finish off with tac (but ok if that fails)
    \item try to finish off with @{term sep_true} (but ok if that fails)
    \end{itemize}
  \end{itemize}
  *}

ML {*
  fun sep_cancel_smart_tac ctxt tac =
    let fun TRY' tac = tac ORELSE' (K all_tac)
    in
      tac
      ORELSE' (sep_cancel_tac ctxt tac
               THEN' TRY' tac
               THEN' TRY' (resolve_tac ctxt @{thms TrueI}))
      ORELSE' (eresolve_tac ctxt @{thms sep_conj_sep_emptyE}
               THEN' sep_cancel_tac ctxt tac
               THEN' TRY' tac
               THEN' TRY' (resolve_tac ctxt @{thms TrueI}))
    end;

  fun sep_cancel_smart_tac_rules ctxt etacs =
      sep_cancel_smart_tac ctxt (FIRST' ([assume_tac ctxt] @ etacs));

  val sep_cancel_syntax = Method.sections [
    Args.add -- Args.colon >>
      K (Method.modifier (Named_Theorems.add @{named_theorems sep_cancel}) @{here})];
*}

method_setup sep_cancel = {*
  sep_cancel_syntax >> (fn _ => fn ctxt =>
    let
      val etacs = map (eresolve_tac ctxt o single)
        (rev (Named_Theorems.get ctxt @{named_theorems sep_cancel}));
    in
      SIMPLE_METHOD' (sep_cancel_smart_tac_rules ctxt etacs)
    end)
*} "Separating conjunction conjunct cancellation"

text {*
  As above, but use blast with a depth limit to figure out where cancellation
  can be done. *}

method_setup sep_cancel_blast = {*
  sep_cancel_syntax >> (fn _ => fn ctxt =>
    let
      val rules = rev (Named_Theorems.get ctxt @{named_theorems sep_cancel});
      val tac = Blast.depth_tac (ctxt addIs rules) 10;
    in
      SIMPLE_METHOD' (sep_cancel_smart_tac ctxt tac)
    end)
*} "Separating conjunction conjunct cancellation using blast"

end
