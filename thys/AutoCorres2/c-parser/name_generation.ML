(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature NAME_GENERATION =
sig

  val globalsN : string
  val locals_stackN: string
  val bytesN : string

  val initialisation_function : string
  val return_var_name : MString.t
  val tmp_var_name : string * int -> MString.t
  val dest_tmp : MString.t -> (string * int) option
  val is_return_or_tmp: MString.t -> bool
  val fun_ptr_name: string -> string
  val C_global_var : MString.t -> MString.t
  val global_var : string -> string
  val global_addr : string -> string
  val fake_param : string -> int -> string
  val stack_addrs : string
  val global_addrs : string
  val known_function: string

  datatype var_kind = In of int | Out | Loc
  val var_kind_ord : (var_kind * var_kind) -> order
  type var_sort = {kind: var_kind, addressable: bool}

  datatype local_ref = Positional of (int * typ) | Named of string  
  val map_local_ref : ((int * typ) -> (int * typ)) -> (string -> string) -> local_ref -> local_ref
  val map_positional:  ((int * typ) -> (int * typ)) -> local_ref -> local_ref
  val map_named     :  (string -> string)           -> local_ref -> local_ref
  val the_named: local_ref -> string
  val the_positional: local_ref -> (int * typ)

  val positional_name : bool -> string -> int -> int CTypeDatatype.ctype -> string
  val dest_positional_name : string -> (var_kind * string) option
  val ensure_varname : string -> string 
  val un_varname : string -> string
  val canonical_name : (string *  (var_kind * typ * int CTypeDatatype.ctype)) -> string

  val tag_name_with_type : {name: string, typname:string} -> string
  val adglob_rcd_tyname : string
  val adglob_struct_var : string

  val naming_scheme_name : string

  val exitN : string
  val exit_status_parN : string

  val enum_const_name : string -> string
  val enum_const_summary_lemma_sfx : string
  val untouched_global_name : MString.t -> MString.t
  val global_initializer_name : MString.t -> MString.t
  val global_data_name : string -> string

  val state_rcd_name  : string
  val global_rcd_name : string
  val global_ext_type : string
  val global_exn_var_name : string
  val global_exn_var : string
  val global_heap : string
  val global_heap_var : string

  val C_struct_name : string -> string
  val unC_struct_name : string -> string
  val ensure_C_struct_name : string -> string
  val C_field_name : string -> string
  val unC_field_name : string -> string
  val ensure_C_field_name : string -> string

  val internalAnonStructPfx : string
  val mkAnonStructName : {union:bool} -> int -> string

  val mkIdentUScoreSafe : string -> string
  val rmUScoreSafety : string -> string

  val apt_string : string -> string

  val numCopyN : string

  val phantom_state_name : string
  val ghost_state_name : string
  val owned_by_fn_name : string

  val mk_localstatic : {fname : string, vname : string } -> MString.t

  val globals_locale_name: string -> string
  val variables_bundle_name: string -> string               (* parameters + local variables of function*)
  val impl_clique_locale_name: string list -> string        (* body locales and defining equation of clique (closed under callees) *)
  val impl_locale_name: string -> string                    (* alias to impl_clique for a single function of clique *)
  val simpl_locale_name: string -> string                   (* all impl locales together *)
  val intern_locale: theory -> xstring -> string
  val maybe_intern_locale: theory -> xstring -> string
  val intern_bundle: theory -> xstring -> string
  val intern_globals_locale_name: theory -> string -> string
  val intern_variables_bundle_name: theory -> string -> string
  val intern_impl_clique_locale_name: theory -> string list -> string
  val intern_impl_locale_name: theory -> string -> string
  val intern_simpl_locale_name: theory -> string -> string
end;

(*

  [initialisation_function] is the name of the implicit initialisation
  function responsible for initialising global variables.

  [return_var_name ty] is the 'name' of the variable that stands for a
  function's return value, given the type of the value returned by the
  function.

  [tag_name_with_type {name,typname}] combines the two strings to create
  a new variable name.  Used when two local variables are requested and
  have different types. (The Hoare environment can't cope with this, so
  one or both variables need to pick up new names.)

  [embret_var_name(f,i)] is the name of the variable that stands for
  the ith return value from a function f that is called while embedded
  in some expression.

  [dest_embret s] returns SOME(f,i) if embret_var_name(f,i) = s, NONE
  if there is no such f and i.

  [global_var s] translates a global variable to an Isabelle variable
  name.  Note that the only variables so treated are special Hoare
  environments like the heap, and the well-typedness environment -
  there aren't any C global variables treated this way.

  [C_global_var s] translates a C global variable name.

  [global_addr s] translates a global C variable name into the name of an
  Isabelle constant that will hold that variable's address in the heap.

  [fake_param s i] gives a name for a parameter based on the name of the
  function and the number of the parameter in the list.

  [adglob_rcd_tyname] is the name of the C struct type that
  contains the global variables that are addressed.

  [adglob_rcd_addr] is the name of the Isabelle variable (it will be a
  locale parameter) containing the address of the addressed globals
  struct in the heap.

  [enum_const_name s] gives back the Isabelle name of the constant
  that will correspond to the enumeration constant s.

  [enum_const_summary_lemma_sfx] is the suffix appended to the name of
  an enumeration type to generate the name of the lemma that lists all
  of the definitions for that type's constants.

  [global_heap_var] is the name of the global variable corresponding to
  the program's heap, which will be of type (addr -> byte x heap_typ_desc).
  This includes both components in the same variable to provide serialisation
  of updates.

  [global_rcd_name] is the name of the record type that stores the
  program's global variables.  May need to be turned into a fully-qualified
  name through the use of Sign.intern_tycon

  [global_ext_type] is similar, but gives the type name suitable for
  axiomatic type class instantiation.

  [global_exn_var_name] is the name of the local variable that contains the
  current type of exception (Break|Return|Continue).

  [global_exn_var] is the name of the local variable accessor that gets the
  current type of exception (Break|Return|Continue).

  [C_struct_name s] "munges" the name s of a C struct type into a form
  that is acceptable for the Isabelle verification.

  [C_field_name s] "munges" the name s of a field in a C struct type
  into a form that is acceptable for the Isabelle verification.

  [apt_string] translates a term representing a term to one that will have
  the _quote parse translation applied to it in read_cterm.

*)

structure NameGeneration :> NAME_GENERATION =
struct

datatype local_ref = Positional of (int * typ) | Named of string

fun map_local_ref f g l = 
  case l of
    Positional p => Positional (f p)
  | Named n => Named (g n)

fun map_positional f = map_local_ref f I 
fun map_named      g = map_local_ref I g
fun the_named (Named s) = s
fun the_positional (Positional p) = p


 
val globalsN = "_global_addresses"
val locals_stackN = "locals_stack"
                              
val exitN = "exit"
val exit_status_parN = "status"

val initialisation_function = "___special___init"

val bytesN = "bytes'"

(*      
Notes on naming scheme for local variables.
The prime ' cannot occur in C variable names, so we can safely use it without colliding
with user input from the C sources. 

Like in Simpl variable names are suffixed with _'. So a C local variable
c results in a constant c_'. This ensures that e.g. bound variables like c or c' can still 
be used without being renamed to ca or c'a. Note that renaming of bound variables is based on the
base names of constants appearing in terms, regardless if the constant has to be qualified
or not. So even a mandatory qualified constant foo.c would make a bound variable c be renamed to ca, 
e.g:
  input "\<forall>c. foo.c = x"
  is printed as "\<forall>ca. foo.c = x"

The auxiliary variable for return values is named ret' (resulting in a constant ret'_') to
avoid a naming conflict with a potential local C variable ret.

Temporary variables for intermediate results of expression evaluation follow the scheme:
  
   tmp'<type>'<number> 
*)

val return_var_name = MString.mk "ret'";

fun tmp_var_name (f,i) =
  MString.mk ("ret'" ^ f ^ "'" ^ Int.toString i)

fun dest_tmp s0 =
  let
    val s = MString.dest s0
    open Substring
    val (pfx, digsfx) = splitr Char.isDigit (full s)
  in
    if isEmpty digsfx then NONE             
    else if isSuffix "'" pfx andalso isPrefix "ret'" pfx then
      SOME (string (triml 4 (trimr 1 pfx)), the (Int.fromString (string digsfx)))
    else
      NONE
  end

fun is_return_or_tmp s =
 MString.dest s = MString.dest return_var_name orelse is_some (dest_tmp s)

datatype var_kind = In of int | Out | Loc

fun var_kind_ord (In i1, In i2) = int_ord (i1, i2)
  | var_kind_ord (In _ , Out  ) = LESS
  | var_kind_ord (In _ , Loc  ) = LESS
  | var_kind_ord (Out  , In _ ) = GREATER
  | var_kind_ord (Out  , Out  ) = EQUAL
  | var_kind_ord (Out  , Loc  ) = LESS
  | var_kind_ord (Loc  , In _ ) = GREATER
  | var_kind_ord (Loc  , Out  ) = GREATER
  | var_kind_ord (Loc  , Loc  ) = EQUAL

type var_sort = {kind: var_kind, addressable: bool}

fun un_varname name =
  perhaps (try (unsuffix HoarePackage.deco)) name 

fun ensure_varname name = 
  case try (unsuffix HoarePackage.deco) name of
    SOME _ => name
  | _ => suffix HoarePackage.deco name

fun gen_positional_name sfx kind i cty = suffix sfx (space_implode "'" [kind, string_of_int i, Absyn.tyname cty])
fun positional_name deco = gen_positional_name (if deco then HoarePackage.deco else "")
fun dest_positional_name n = 
  case space_explode "'" (un_varname n) of
    ("in":: pos::(tynames as _::_)) => SOME (In (fst (read_int (Symbol.explode pos))), space_implode "'" tynames)
   | _ => NONE

fun canonical_name (name, (kind, ty, cty)) =
  (case kind of
     In i => positional_name false "in" i cty
   | _ => name)

fun tag_name_with_type {name: string, typname:string} = name ^ "'" ^ typname

fun fake_param f i = f ^ "_param_" ^ Int.toString i
fun ext_type t = t ^ "_ext"

fun enum_const_name s = s
val enum_const_summary_lemma_sfx = "_defs"

fun fix_underscore s = if String.isPrefix "_" s
  then "underscore" ^ s else s

fun untouched_global_name s =
  s |> MString.dest |> fix_underscore |> MString.mk

fun global_initializer_name s =
  fix_underscore (MString.dest s) ^ "_global_initializer" |> MString.mk
fun global_data_name s = fix_underscore s ^ "_global_data"

val state_rcd_name = "state"
val global_rcd_name = "globals"
val global_ext_type = ext_type global_rcd_name
val global_exn_var_name = "global_exn_var'"
val global_exn_var = global_exn_var_name ^ "_'"


fun C_global_var s = s
fun global_var s = Hoare.varname s
fun global_addr s = s ^"_addr"
fun global_upd s = global_var s ^ "_upd"

val global_heap = "t_hrs"
val global_heap_var = global_var global_heap

val stack_addrs = "\<S>"
val global_addrs = "\<G>"
val known_function = "known_function"

fun apt_string s = "[.[" ^ s ^ "].]"

val numCopyN = "tyCopy"

fun C_struct_name s = s ^ "_C"
fun unC_struct_name s =
    if String.isSuffix "_C" s then
      String.extract(s,0,SOME(size s - 2))
    else s

val C_field_name = CType.C_field_name
val unC_field_name = CType.unC_field_name

fun ensure make dest s = make (dest s)
val ensure_C_struct_name = ensure C_struct_name unC_struct_name
val ensure_C_field_name = ensure C_field_name unC_field_name 

val adglob_rcd_tyname = "adglobs_struct"
val adglob_struct_var = "adglobs"

val phantom_state_name = "phantom_machine_state"
val ghost_state_name = "ghost'state"

val naming_scheme_name = "\\" ^ "<Gamma>_naming"
val owned_by_fn_name = "owner'ship"

val internalAnonStructPfx = "ISA_anon_struct_"
fun mkAnonStructName {union=false} i = "AnonStruct" ^ Int.toString i ^ "'"
  | mkAnonStructName {union=true}  i = "AnonUnion" ^ Int.toString i ^ "'"

(* mkIdentUScoreSafe is injective on identifiers that can be
   generated by the lexer *)
val ussafe_pfx = "StrictC'"
fun mkIdentUScoreSafe s =
    if String.sub(s, 0) = #"_" then ussafe_pfx^s
    else s

fun rmUScoreSafety s =
    if String.isPrefix ussafe_pfx s then
      String.extract(s, String.size ussafe_pfx, NONE)
    else s

fun mk_localstatic {fname, vname} =
  MString.mk (fname ^ "'" ^ vname)

fun fun_ptr_name fname =
 if Name.is_internal fname then suffix Hoare.proc_deco fname else fname
 
fun intern_locale thy name = 
  let 
    val loc = Locale.intern thy name |> perhaps Long_Name.dest_hidden
  in
    if Locale.defined thy loc then loc else error ("intern_locale: undefined locale: " ^ name)
  end

fun maybe_intern_locale thy name = 
 case try (intern_locale thy) name of SOME n => n | NONE => name
 
fun intern_bundle thy name = 
  let 
    val ctxt = Proof_Context.init_global thy
    val loc = Bundle.check ctxt (name, Position.none)
  in
    loc
  end


fun globals_locale_name filename = suffix globalsN filename
fun intern_globals_locale_name thy filename = 
  intern_locale thy (globals_locale_name filename);

fun variables_bundle_name fname = suffix "_variables" fname;
fun intern_variables_bundle_name thy fname =
  intern_bundle thy (variables_bundle_name fname);

fun impl_clique_locale_name clique = suffix "_impl" (space_implode "_" (sort_strings clique));
fun impl_locale_name fname = impl_clique_locale_name [fname]
fun intern_impl_clique_locale_name thy clique =
  intern_locale thy (impl_clique_locale_name clique);
fun intern_impl_locale_name thy fname = intern_impl_clique_locale_name thy [fname]


fun simpl_locale_name prog_name = suffix "_simpl" prog_name;
fun intern_simpl_locale_name thy prog_name = intern_locale thy prog_name


end;
