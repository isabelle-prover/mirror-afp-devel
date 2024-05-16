(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature LAZY_NAMED_THEOREMS =
sig
  val member: Proof.context -> string -> thm -> bool
  val get: Proof.context -> string -> (thm list * Proof.context)
  val clear: string -> Context.generic -> Context.generic
  val add_lazy_thm: string -> thm -> Token.src list -> morphism ->
        Context.generic -> Context.generic
  val add_lazy_thm_declaration: string -> thm -> Token.src list -> local_theory -> local_theory
  val add_thm: string -> thm -> Context.generic -> Context.generic
  val del_thm: string -> thm -> Context.generic -> Context.generic
  val add: string -> attribute
  val del: string -> attribute
  val check: Proof.context -> string * Position.T -> string
  val declare: binding -> string -> local_theory -> string * local_theory
end;

structure Lazy_Named_Theorems: LAZY_NAMED_THEOREMS =
struct

(* context data *)

type item_data = {index: term, thm : thm Lazy.lazy, attribs: Token.src list}

fun item_of thm attribs = 
  {index = Thm.full_prop_of thm, thm = Lazy.value thm, attribs = attribs}:item_data

structure Data = Generic_Data
(
  type T = item_data Item_Net.T Symtab.table;
  val empty: T = Symtab.empty;
  val merge : T * T -> T = Symtab.join (K Item_Net.merge);
);


val item_net = 
  Item_Net.init 
     (fn (i1:item_data, i2:item_data) => (#index i1) aconv (#index i2))  
    (single o #index)

fun new_entry name =
  Data.map (fn data =>
    if Symtab.defined data name
    then error ("Duplicate declaration of named theorems: " ^ quote name)
    else Symtab.update (name, item_net) data);

fun undeclared name = "Undeclared named theorems " ^ quote name;

val defined_entry = Symtab.defined o Data.get;

val _ = Thm.typ_of
fun the_entry context name =
  (case Symtab.lookup (Data.get context) name of
    NONE => error (undeclared name)
  | SOME entry => entry);

fun map_entry name f context =
  (the_entry context name; Data.map (Symtab.map_entry name f) context);


(* maintain content *)

fun member ctxt name thm = Item_Net.member (the_entry (Context.Proof ctxt) name) (item_of thm []);

fun get_raw context = the_entry context 
  #> Item_Net.content 
  #> map (fn {thm, attribs, ...} => (Thm.transfer'' context (Lazy.force thm), attribs))
  #> rev

val attribute = Context.cases Attrib.attribute_global Attrib.attribute 
 
fun apply_attributes context [] = ([], context)
  | apply_attributes context ((thm, attrs)::xs) = 
     let 
       val (thm', context') = (thm, context) 
         |> fold (fn attr => fn (thm, context) => 
              Thm.apply_attribute (attribute context attr) thm context) attrs
       val (thms, context'') = apply_attributes context' xs 
     in (thm'::thms, context'') end

fun content context name =
  get_raw context name |> apply_attributes context

fun get ctxt name = 
  content (Context.Proof ctxt) name |> apsnd Context.the_proof

fun add_lazy_thm name thm attribs phi =
 let
   val thm = Thm.trim_context thm
   val index = Thm.full_prop_of thm
   val lazy_thm = Lazy.lazy (fn () => Morphism.thm phi thm)
   val item = {index = index, thm = lazy_thm, attribs = attribs}: item_data
 in
   map_entry name (Item_Net.update item)
 end

fun add_lazy_thm_declaration name thm attribs = 
  Local_Theory.declaration {pervasive = true, syntax = false, pos = \<^here>} (add_lazy_thm name thm attribs)

fun add_thm name thm  =
 let
   val thm = Thm.trim_context thm
   val item = item_of thm []
 in
   map_entry name (Item_Net.update item)
 end

fun del_thm name thm =
 let
   val item = item_of thm []
 in
  map_entry name (Item_Net.remove item)
 end

val add = Thm.declaration_attribute o add_thm;
val del = Thm.declaration_attribute o del_thm;

fun clear name = map_entry name (K item_net);

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
      |> Local_Theory.add_thms_dynamic (binding, fn context => fst (content context name)) 
      |> Attrib.local_setup binding (Attrib.add_del (add name) (del name)) description
  in (name, lthy') end;


(* ML antiquotation *)

val _ = Theory.setup
  (ML_Antiquotation.inline_embedded \<^binding>\<open>lazy_named_theorems\<close>
    (Args.context -- Scan.lift Parse.embedded_position >>
      (fn (ctxt, name) => ML_Syntax.print_string (check ctxt name))));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>lazy_named_theorems\<close>
    "declare named collection of theorems"
    (Parse.and_list1 (Parse.binding -- Scan.optional Parse.embedded "") >>
      fold (fn (b, descr) => snd o declare b descr));

end