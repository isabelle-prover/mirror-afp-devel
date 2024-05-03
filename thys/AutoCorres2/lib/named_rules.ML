(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
Variant of Named_Theorems exposing net operations.
*)

signature NAMED_RULES =
sig
  val member: Proof.context -> string -> thm -> bool
  val get: Proof.context -> string -> thm list
  val retrieve: Proof.context -> string -> term -> thm list
  val retrieve_matching: Proof.context -> string -> term -> thm list
  val clear: string -> Context.generic -> Context.generic
  val add_thm: string -> thm -> Context.generic -> Context.generic
  val del_thm: string -> thm -> Context.generic -> Context.generic
  val add: string -> attribute
  val del: string -> attribute
  val check: Proof.context -> string * Position.T -> string
  val declare: {intro:bool} -> binding -> string -> local_theory -> string * local_theory

  val with_rules: string -> (Proof.context -> thm list -> int -> tactic) -> 
         Proof.context -> int -> tactic 
  val with_matching_rules: string -> (Proof.context -> thm list -> int -> tactic) -> 
         Proof.context -> int -> tactic 
end;

structure Named_Rules: NAMED_RULES =
struct

(* context data *)

structure Data = Generic_Data
(
  type T = thm Item_Net.T Symtab.table;
  val empty: T = Symtab.empty;
  val merge : T * T -> T = Symtab.join (K Item_Net.merge);
);

fun new_entry intro name =
  Data.map (fn data =>
    if Symtab.defined data name
    then error ("Duplicate declaration of named theorems: " ^ quote name)
    else Symtab.update (name, if intro then Thm.item_net_intro else Thm.item_net) data);

fun undeclared name = "Undeclared named theorems " ^ quote name;

val defined_entry = Symtab.defined o Data.get;

fun the_entry context name =
  (case Symtab.lookup (Data.get context) name of
    NONE => error (undeclared name)
  | SOME entry => entry);

fun map_entry name f context =
  (the_entry context name; Data.map (Symtab.map_entry name f) context);


(* maintain content *)

fun member ctxt = Item_Net.member o the_entry (Context.Proof ctxt);

fun content context =
  rev o map (Thm.transfer'' context) o Item_Net.content o the_entry context;

val get = content o Context.Proof;

fun retrieve ctxt name t = 
  let 
    val net = the_entry (Context.Proof ctxt) name
  in
    Item_Net.retrieve net t
  end 

fun retrieve_matching ctxt name t = 
  let 
    val net = the_entry (Context.Proof ctxt) name
  in
    Item_Net.retrieve_matching net t
  end 


fun clear name = map_entry name (K Thm.item_net);

fun add_thm name = map_entry name o Item_Net.update o Thm.trim_context;
fun del_thm name = map_entry name o Item_Net.remove;

val add = Thm.declaration_attribute o add_thm;
val del = Thm.declaration_attribute o del_thm;


(* check *)

fun check ctxt (xname, pos) =
  let
    val context = Context.Proof ctxt;
    val fact_ref = Facts.Named ((xname, Position.none), NONE);
    fun err () =
      let
        val space = Facts.space_of (Proof_Context.facts_of ctxt);
        val completion = Name_Space.completion context space (defined_entry context) (xname, pos);
      in error (undeclared xname ^ Position.here pos ^ Completion.markup_report [completion]) end;
  in
    (case try (Proof_Context.get_fact_generic context) fact_ref of
      SOME (SOME name, _) => if defined_entry context name then name else err ()
    | _ => err ())
  end;


(* declaration *)

fun declare {intro} binding descr lthy =
  let
    val name = Local_Theory.full_name lthy binding;
    val description =
      "declaration of " ^ (if descr = "" then Binding.name_of binding ^ " rules" else descr);
    val lthy' = lthy
      |> Local_Theory.background_theory (Context.theory_map (new_entry intro name))
      |> Local_Theory.map_contexts (K (Context.proof_map (new_entry intro name)))
      |> Local_Theory.add_thms_dynamic (binding, fn context => content context name)
      |> Attrib.local_setup binding (Attrib.add_del (add name) (del name)) description
  in (name, lthy') end;

(* tactic *)

fun gen_with_rules match name tac ctxt = SUBGOAL (fn (t, i) => 
  let
    val concl = Logic.strip_assums_concl t
    val rules = if match then retrieve_matching ctxt name concl else retrieve ctxt name concl
      |> map (Thm.transfer' ctxt)
  in
    tac ctxt rules i 
  end)

val with_rules = gen_with_rules false
val with_matching_rules = gen_with_rules true


(* ML antiquotation *)

val _ = Theory.setup
  (ML_Antiquotation.inline_embedded \<^binding>\<open>named_rules\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => ML_Syntax.print_string (check ctxt name))));


(* command *)
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>named_rules\<close>
    "declare named collection of theorems"
     ((Args.mode "intro") -- (Parse.and_list1 (Parse.binding -- Scan.optional Parse.embedded "")) >>
      (fn (intro, decls) => fold (fn (b, descr) => snd o declare {intro=intro} b descr) decls));

end;
