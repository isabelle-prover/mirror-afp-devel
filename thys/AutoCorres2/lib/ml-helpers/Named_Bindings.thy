(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Named_Bindings
  imports Main
  keywords "named_bindings"::thy_decl
begin

text \<open>
Command \<open>named_bindings\<close> as theorem collection as alternative to @{command named_theorems}:
Instead of theorems we only store theorem bindings in data, and fetch the theorems from the
context with the names in these bindings. The intended use case is to note theorems without
any attributes but with a proper binding, and then adding this binding to the named bindings.
The hypothesis is that this is less ressource consuming in the locale infrastructure as we
make use of the lazy-facts optimization and only transform bindings instead of theorems with
the locale morphisms.
\<close>
ML \<open>

signature NAMED_BINDINGS =
sig
  val member: Proof.context -> string -> binding -> bool
  val get: Proof.context -> string -> binding list
  val get_thms: Proof.context -> string -> thm list
  val clear: string -> Context.generic -> Context.generic
  val add_binding: string -> binding -> Context.generic -> Context.generic
  val del_binding: string -> binding -> Context.generic -> Context.generic
  val add_thm: string -> thm -> Context.generic -> Context.generic
  val del_thm: string -> thm -> Context.generic -> Context.generic
  val add: string -> attribute
  val del: string -> attribute
  val check: Proof.context -> string * Position.T -> string
  val declare: binding -> string -> local_theory -> string * local_theory

  val binding_declaration: binding * string list -> local_theory -> local_theory
  val binding_declarations: binding list * string list -> local_theory -> local_theory
  val note : ((binding * string list) * thm list) -> local_theory ->
        (string * thm list) * Proof.context
end;

structure Named_Bindings : NAMED_BINDINGS =
struct

structure Data = Generic_Data
(
  type T = binding list Symtab.table;
  val empty: T = Symtab.empty;
  val merge : T * T -> T = Symtab.join (K (merge (op =)))
)

fun new_entry name =
  Data.map (fn data =>
    if Symtab.defined data name
    then error ("Duplicate declaration of named binbings: " ^ quote name)
    else Symtab.update (name, []) data);

fun undeclared name = "Undeclared named bindings " ^ quote name;

val defined_entry = Symtab.defined o Data.get;

fun the_entry context name =
  (case Symtab.lookup (Data.get context) name of
    NONE => error (undeclared name)
  | SOME entry => entry);

fun map_entry name f context =
  (the_entry context name; Data.map (Symtab.map_entry name f) context);

(* maintain content *)

val list_member = member
fun member ctxt = list_member (op =) o the_entry (Context.Proof ctxt);


fun content context =
  rev o the_entry context;

fun thm_content context =
  content context #> maps (Proof_Context.get_thms (Context.proof_of context) o Binding.long_name_of)

val get = content o Context.Proof;
fun get_thms ctxt = get ctxt #> maps (Proof_Context.get_thms ctxt o Binding.long_name_of)

fun clear name = map_entry name (K []);


fun add_binding name binding = not (Binding.is_empty binding) ? (map_entry name o insert (op =)) binding
fun del_binding name binding = not (Binding.is_empty binding) ? (map_entry name o remove (op =)) binding;

fun binding_of [] = Binding.empty
  | binding_of [n] = Binding.name n
  | binding_of (base::ns) = Binding.name base |> fold (Binding.qualify false) ns
 
fun mk_binding long_name =
  case Long_Name.dest_local long_name of
    SOME n => Binding.name n
  | _ =>  Long_Name.explode long_name |> rev |> binding_of 

fun binding_of_thm_name (n as (name, i)) =
  if Thm_Name.is_empty n then
    Binding.empty
  else if i > 0 then
    error ("Named_Bindings: expecting singleton theorem: " ^ @{make_string} n)
  else let val b = mk_binding name; val _ = tracing ("b: " ^ @{make_string} b) in b end

fun thm_binding thm = 
  let
    val n = Thm.derivation_name thm

  in 
    if Thm_Name.is_empty n then
      Binding.empty (* Considering Thm.get_name_hint instead, is almost always 
       misleading in case of theorems within a locale. So we ignore those cases. *)
    else
      binding_of_thm_name n
  end
  
fun add_thm name thm context = 
  let 
    val context' = add_binding name (thm_binding thm) context
  in
    context'
  end

fun del_thm name thm context = del_binding name (thm_binding thm) context

(* Caution: using add / del attributes only has a meaningful effect on theory level thms.
 *  For local facts it is ignored.
 *)

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

fun declare binding descr lthy =
  let
    val name = Local_Theory.full_name lthy binding;
    val description =
      "declaration of " ^ (if descr = "" then Binding.name_of binding ^ " rules" else descr);
    val lthy' = lthy
      |> Local_Theory.background_theory (Context.theory_map (new_entry name))
      |> Local_Theory.map_contexts (K (Context.proof_map (new_entry name)))
      |> Local_Theory.add_thms_dynamic (binding, fn context => thm_content context name)
      |> Attrib.local_setup binding (Attrib.add_del (add name) (del name)) description
  in (name, lthy') end;

(* ML antiquotation *)

val _ = Theory.setup
  (ML_Antiquotation.inline_embedded \<^binding>\<open>named_bindings\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => ML_Syntax.print_string (check ctxt name))));
(* Local Theory operations *)


fun binding_declarations (bindings, named_bindings) =
  Local_Theory.declaration {pervasive = false, pos = \<^here>, syntax = false} (fn phi =>
    fold (fn binding => 
      (fold (fn nb => add_binding nb (Morphism.binding phi binding)) named_bindings)) bindings)

fun binding_declaration (binding, named_bindings) = binding_declarations ([binding], named_bindings)

fun note ((binding, named_bindings), thms) = 
  Local_Theory.note ((binding, []), thms)
  ##> binding_declaration (binding, named_bindings)

end
\<close>

ML \<open>
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>named_bindings\<close>
    "declare named collection of theorems"
    (Parse.and_list1 (Parse.binding -- Scan.optional Parse.embedded "") >>
      fold (fn (b, descr) => snd o Named_Bindings.declare b descr));
\<close>

end