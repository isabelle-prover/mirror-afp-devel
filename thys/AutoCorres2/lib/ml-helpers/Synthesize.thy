(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Tools for intro-rule based term synthesis \<open>synthesize_rules\<close>\<close>

theory Synthesize
  imports 
  "Tuple_Tools"
  "AutoCorres_Utils"
  "MkTermAntiquote" 
keywords
  "synthesize_rules"::thy_decl and
  "add_synthesize_pattern"::thy_decl % "ML" and
  "print_synthesize_rules"::diag
begin



ML_file \<open>synthesize_rules.ML\<close> 


subsection \<open>Commands\<close>

ML \<open>
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize_rules\<close>
    "declare named collection of synthesize rules (pattern indexed intro rules)"
    (Parse.and_list1 Parse.binding >> 
        (fold (fn b => (snd o Synthesize_Rules.declare b))))
\<close>

ML \<open>
val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>add_synthesize_pattern\<close>
    "add pattern schemes via ML or declarations"
    (Parse.and_list1 Parse.binding :|-- (fn rules_names => 
        (\<^keyword>\<open>where\<close> |-- Synthesize_Rules.pattern_decls >> (fn decls => 
           fold (fn rules_name => Synthesize_Rules.add_pattern_decls rules_name decls) rules_names))  
     || 
        (\<^keyword>\<open>=\<close> |-- Parse.ML_source >> (fn src => 
           fold (fn rules_name => Synthesize_Rules.add_pattern_ml rules_name src) rules_names))))
\<close>

ML \<open>
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>print_synthesize_rules\<close>
    "print named collection of synthesize rules (optionally matching a given term)"
    (Parse.name_position -- Scan.option Parse.term >> 
        (fn (name, term_opt)  => Synthesize_Rules.print_rules_cmd name term_opt))
\<close>


subsection \<open>ML Antiquotations\<close>


ML \<open> Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>synthesize_rules_name\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => ML_Syntax.print_string (Synthesize_Rules.check (Context.Proof ctxt) name |> fst))))
\<close>

ML \<open> Theory.setup
 (ML_Antiquotation.value_embedded \<^binding>\<open>synthesize_rules\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => "Synthesize_Rules.get_rules ML_context " ^ 
         ML_Syntax.print_string (Synthesize_Rules.check (Context.Proof ctxt) name |> fst))))
\<close>

ML \<open>
Theory.setup
   (ML_Antiquotation.inline @{binding "mk_synthesize_pattern"}
      ((Args.context -- Scan.lift Parse.embedded_inner_syntax -- 
         (Scan.optional (Scan.lift ((Synthesize_Rules.comma_list Args.name))) []))
         >> (fn ((ctxt, pattern_str), synth_args) => Synthesize_Rules.gen_pattern_fun "" ctxt (pattern_str, synth_args) )))
\<close>


subsection \<open>Attributes\<close>


attribute_setup synthesize_rule = \<open>
let
  val priority = Args.$$$ "priority" |-- Args.colon |-- Parse.int
  val opt_priority = Scan.optional (Scan.lift (priority)) 10
  val only_schematic_goal = Args.$$$ "only_schematic_goal" >> (fn _ => true)
  val opt_only_schematic_goal = Scan.optional (Scan.lift only_schematic_goal) false
  val del = Args.del >> (fn _ => true)
  val opt_del = Scan.optional (Scan.lift del) false
  val split = Args.$$$ "split" |-- Args.colon |-- Parse.and_list Parse.short_ident
  val opt_split = Scan.optional (Scan.lift (split)) []
in
  Scan.lift (Parse.and_list1 Parse.name_position) 
  -- opt_priority -- opt_split -- opt_only_schematic_goal -- opt_del >> (fn ((((rules_names, prio), splits), only_schematic_goal), del) => 
  let
  in
    Thm.declaration_attribute (fn thm => fn context => 
      let
         val ctxt = Context.proof_of context
         val thm_binding1 = Utils.guess_binding_of_thm ctxt thm
         val thm_binding2 = if Binding.is_empty thm_binding1 then Binding.make ("??", (snd (hd rules_names))) else thm_binding1
         val rules_names = map (Synthesize_Rules.check context #> fst) rules_names
         fun add_rule rules_name = 
           if null splits 
           then Synthesize_Rules.add_rule rules_name {only_schematic_goal = only_schematic_goal} thm_binding2 prio thm
           else Synthesize_Rules.add_split_rule rules_name {only_schematic_goal = only_schematic_goal} thm_binding2 prio splits thm #> snd
         fun del_rule rules_name = 
           if null splits 
           then Synthesize_Rules.del_rule rules_name {only_schematic_goal = only_schematic_goal} thm_binding2 prio thm
           else Synthesize_Rules.del_split_rule rules_name {only_schematic_goal = only_schematic_goal} thm_binding2 prio splits thm
      in 
         context |> fold (if del then del_rule else add_rule) rules_names
      end)
  end)
end
\<close>







end
