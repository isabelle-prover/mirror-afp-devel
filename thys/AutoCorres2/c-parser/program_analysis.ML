(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature PROGRAM_ANALYSIS =
sig

  type 'ce ctype = 'ce Absyn.ctype
  type expr = Absyn.expr
  type ecenv = Absyn.ecenv
  type s2s_config = {anon_vars : bool, owners : string list,
                     allow_underscore_idents : bool,
                     munge_info_fname : Path.T option}

  type 'a rcd_env = (string * (CType.rcd_kind * (string * 'a) list * Region.t * CType.attribute list)) list
  type senv = (int ctype * CType.attribute list) rcd_env

  type union_variants = (string * ((string * senv) list)) list

  (* Information necessary for name and definition generation.
     - `src_name` is the name as it appears in the original source file, or a
       synthetic name for return variables.
     - `isa_name` is the munged name without the trailing `_'` suffixes (e.g.
       `x___int` for a source variable called `x`).
  *)
  type nm_info = {src_name : string, isa_name : MString.t}

  type var_info
  val is_global : var_info -> bool
  val srcname : var_info -> string
  val fullname : var_info -> string
  val get_mname : var_info -> MString.t
  val get_fname : var_info -> string option
  val get_vtype : var_info -> int ctype
  val get_struct_env : var_info -> senv
  val get_attrs : var_info -> StmtDecl.gcc_attribute list
  val declpos : var_info -> Region.t
  val vi_compare : var_info * var_info -> order

  datatype modify_var = M of var_info | TheHeap | PhantomState
    | GhostState | AllGlobals
  val mvar_compare : modify_var * modify_var -> order
  val string_of_mvar : modify_var -> string
  structure MVar_Table : TABLE where type key = modify_var

  datatype fncall_type = DirectCall of string
                       | FnPtrCall of (int ctype * int ctype list) *
                                      (string * ExprDatatype.var_info) list * (* potentially called functions *)
                                      bool (* true if C-style object method *)

  val fncall_ord : fncall_type * fncall_type -> order

  datatype selector = Field of string | Array_Index
  val selector_ord: selector * selector -> order
  val selectors_ord: selector list * selector list -> order

  type callgraph =
    {callees: string Binaryset.set Symtab.table, callers: string Binaryset.set Symtab.table}

  type csenv
  val cse2ecenv : Proof.context -> csenv -> ecenv
  val get_array_mentions : csenv -> (int ctype * int) Binaryset.set
  val get_senv : csenv -> senv
  val get_pruned_senv : csenv -> senv
  val get_union_variants : csenv -> union_variants
  val get_rettype : string -> csenv -> int ctype option
  val get_heaptypes : csenv -> int ctype Binaryset.set
  val get_usedtypes : csenv -> int ctype Binaryset.set
  val compute_callgraphs : Proof.context -> csenv -> callgraph
  val compute_callgraphs_with_exit : Proof.context -> csenv -> callgraph
  val get_addressed : csenv -> (expr * selector list) list XMSymTab.table
  val is_addressed  : csenv -> (MString.t * string option) -> bool
  val get_addressed_types: csenv -> selector list Ord_List.T Absyn.CTypeTab.table
  val get_callgraph : csenv -> fncall_type Binaryset.set Symtab.table
  val get_direct_callees: csenv -> Symtab.key -> string list
  val get_fun_ptr_callees: csenv -> Symtab.key -> string list
  val get_other_fun_ptr_dependencies: csenv -> Symtab.key -> string list
  val get_all_other_fun_ptr_dependencies: csenv -> string list
  val get_all_addressed_funs : csenv -> string list
  val get_indirect_fun_ptr_dependencies: csenv -> Symtab.key -> string list
  val get_callers   : csenv -> string Binaryset.set Symtab.table
  val get_vars      : csenv -> var_info list Symtab.table
  val get_locals    : csenv -> string -> var_info list
  val get_return_vars: csenv -> string -> var_info list
  val get_variables : csenv -> string option -> var_info list
  val get_globals   : csenv -> var_info list
  val get_globinits : csenv -> Absyn.expr MSymTab.table
  val get_mangled_vars : csenv -> var_info list Symtab.table
  val get_params : string -> csenv -> var_info list option
  val get_embedded_fncalls : csenv -> fncall_type Binaryset.set
  val get_referenced_funs: csenv -> string list Symtab.table
  val get_all_referenced_funs: csenv -> Symtab.key list
  val get_referenced_funs_global: csenv -> string list
  val get_referenced_funs_via_const_globals: csenv -> Symtab.key -> string list
  val get_functions_used_as_fun_ptr_params: csenv -> string list
  val get_functions_used_via_fun_ptr: csenv -> string list
  val get_addressed_vis : string option -> csenv -> var_info list
  val get_addressed_globals : csenv -> string -> string list
  val get_local_info: csenv -> MString.t * string option -> {kind:NameGeneration.var_kind, addressed:bool,info:var_info} option
  val has_addressable_variables: csenv -> string -> bool
  val callers_with_addressable_variables: csenv -> string -> string list
  val get_global_addressed : csenv -> (MString.t * (Absyn.expr * selector list) list) list
  val get_vi_nm_info : csenv -> var_info -> nm_info
  val get_fun_modifies : csenv -> string -> modify_var Binaryset.set option
  val get_functions : csenv -> string list
  val get_non_proto_functions : csenv -> string list
  val has_body_spec : csenv -> Symtab.key -> bool
  val get_non_proto_and_body_spec_functions : csenv -> string list
  val get_fninfo : csenv -> (int ctype * bool * var_info list) Symtab.table
  val get_hpfninfo : csenv -> Absyn.ext_decl Symtab.table
  val get_constant_global_fun_ptrs : csenv -> (string * string list) list
  val map_constant_global_fun_ptrs : ((string * string list) list ->  (string * string list) list)
         -> csenv -> csenv
  val get_cliques : csenv -> string list list
  val map_cliques : (string list list -> string list list ) -> csenv -> csenv
  val get_final_callgraph : csenv -> callgraph
  val get_final_callers : csenv -> string -> string list
  val map_final_callgraph: (callgraph -> callgraph) -> csenv -> csenv
  val get_final_callgraph_with_exit : csenv -> callgraph
  val map_final_callgraph_with_exit: (callgraph -> callgraph) -> csenv -> csenv
  val get_clique : csenv -> string -> string list option
  val get_fun_ptr_parameters: csenv -> Symtab.key -> var_info option list
  val has_fun_ptr_parameters: csenv -> Symtab.key -> bool
  val all_fun_ptr_parameter_types: csenv -> int CTypeDatatype.ctype list
  val all_method_fun_ptr_types: csenv -> int CTypeDatatype.ctype list
  val is_exit_reachable: csenv -> string -> bool
  val update_hpfninfo0 : Absyn.ext_decl -> Absyn.ext_decl Symtab.table ->
                         Absyn.ext_decl Symtab.table
  val get_defined_functions : csenv -> Region.Wrap.region Symtab.table
  val get_read_globals : csenv -> modify_var Binaryset.set Symtab.table
  val is_recursivefn : csenv -> string -> bool
  val mvar_traverse : Proof.context -> csenv -> csenv
  val get_modified_global_locns : csenv -> string Binaryset.set MVar_Table.table
  val calc_all_globals : csenv -> int ctype MSymTab.table
  val calc_untouched_globals : csenv -> int ctype MSymTab.table
  val fndes_callinfo : Proof.context -> csenv -> expr -> fncall_type * (int ctype * int ctype list)

  val fns_by_type : csenv -> int ctype * int ctype list -> string list

  val cse_typing : Proof.context -> csenv -> expr -> int ctype

  val used_fun_types_of_fun : csenv -> string -> int ctype list
  val uses_globals : csenv -> string -> bool

  val process_decls : Proof.context -> s2s_config -> Absyn.ext_decl list ->
                      ((Absyn.ext_decl list * Absyn.statement list) * csenv)
  val function_specs : csenv -> Absyn.fnspec list Symtab.table
  val sizeof : csenv -> int ctype -> int
  val sizeof_padding : csenv -> int ctype -> int * bool
  val sizeof_struct_or_union: csenv -> string -> int
  val alignof: csenv -> int ctype -> int
  val alignof_struct_or_union: csenv -> string -> int
  val offsetof: csenv -> string -> string -> int
  val offsetof': csenv -> string -> string list -> int

  val eq_string_assoc: (string * string list) list * (string * string list) list -> bool

  type asm_stmt_elements = (string * bool * expr option * expr list)
  val split_asm_stmt : Absyn.statement_node -> asm_stmt_elements
  val merge_asm_stmt : asm_stmt_elements -> Absyn.statement_node

  val get_globals_rcd : csenv -> senv

  val dest_method_fun_ptr: Proof.context -> csenv -> Expr.expr ->
        (int CTypeDatatype.ctype * string) option

  val method_callers: csenv -> string list
  val method_types: csenv -> (int ctype * int ctype list)  list

  type mungedb = {fun_name: string option, nm_info: nm_info} list

  (* Returns the variable name munging information for all variables. *)
  val get_mungedb : csenv -> mungedb

  (* Writes the contents of the mungedb to a string list.
     The list has one human-readable string per C declaration, sorted
     alphabetically, with the following format per line:

     C variable '{c_source_name}' \
     declared {decl_info} -> Isabelle state field '{isabelle_name}' \
     and {abbreviation_info}

     Where:
       - {c_source_name} is the name of the variable in the C source.
       - {decl_info} indicates whether the variable was declared globally,
         and if not then which function it was declared in.
       - {isabelle_name} is the type-mangled name that we use in Isabelle
         (e.g. "foo___int").
       - {abbreviation_info} indicates whether an Isabelle abbreviation
         was created between the short C name and the long Isabelle name.

     For an example, see `./.testfiles/jiraver1241.thy`.
  *)
  val render_mungedb : mungedb -> string list

  (* Writes the mungedb to the file specified in `munge_info_fname` (see
     type s2s_config). *)
  val export_mungedb : csenv -> unit
end

structure ProgramAnalysis : PROGRAM_ANALYSIS =
struct

fun maybe f opt = fold f (the_list opt)

open Absyn NameGeneration

type program = ext_decl list
type s2s_config = {anon_vars : bool, owners : string list,
                   allow_underscore_idents : bool, munge_info_fname : Path.T option}

fun fname_str NONE = NameGeneration.initialisation_function
  | fname_str (SOME f) = f

(* ----------------------------------------------------------------------
    Collect all of a program's variables

    The variables collected will be analysed to generate an appropriate
    VCG environment state-space
   ---------------------------------------------------------------------- *)
(* name will be NameGeneration.return_var_name if the variable is a
   "return" variable. There will be at least one such per function,
   unless the function returns "void".

   fname is NONE if the variable is global, "return" variables are not
   global.

   The struct_env is the structure type environment that is in force at the
   point of the variable's declaration.  This allows the consumer of this
   data to figure out what is meant by a Struct s type.

   return_var is true if the variable is a return variable.

   proto_param is true if the variable has been created from a
   prototype function declaration; such names can be overridden if a
   function definition later occurs.

*)


type 'a rcd_env = (string * (rcd_kind * (string * 'a) list * Region.t * CType.attribute list)) list
type senv = (int ctype * CType.attribute list) rcd_env

type union_variants = (string * ((string * senv) list)) list

@{record \<open>datatype var_info = Var_info of
                {name : string,
                return_var : bool,
                vtype : int ctype,
                struct_env : senv,

                (* Name of the function in which this variable was declared (if
                   any). *)
                fname : string option,
                proto_param : bool,
                method_call_tmp_var : bool,
                munged_name : MString.t,
                declared_at : Region.t,
                attrs : gcc_attribute list}
\<close>
};


type nm_info = {src_name : string, isa_name : MString.t}

fun viToString (Var_info {name, fname,...}) =
    case fname of
      NONE => "global "^name
    | SOME f => name ^ " (in " ^ f ^")"
val fullname = viToString
fun srcname (Var_info {name,...}) = name

val get_mname = get_munged_name

val declpos = get_declared_at

fun vi_compare(Var_info vi1, Var_info vi2) = let
  val ocmp = option_ord and pcmp = prod_ord and scmp = string_ord
  val mscmp = MString.ord
in
  pcmp (ocmp scmp) (pcmp scmp mscmp)
       ((#fname vi1, (#name vi1, #munged_name vi1)),
        (#fname vi2, (#name vi2, #munged_name vi2)))
end

fun is_global (Var_info r) = case #fname r of NONE => true | _ => false

fun fnToString NONE = "at global level"
  | fnToString (SOME s) = "in function "^s

fun types_compatible global ty1 ty2 =
    (* All locals need to be fully specified, but global arrays are special. *)
    if not global then ty1 = ty2
    else
      case (ty1, ty2) of
        (Array(ty1', sz1), Array(ty2', sz2)) =>
          (ty1' = ty2') andalso (sz1 = sz2 orelse sz1 = NONE orelse sz2 = NONE)
      | _ => ty1 = ty2

fun max_type ty1 ty2 =
    (* assumes types are compatible *)
    case (ty1, ty2) of
      (Array(_, NONE), _) => ty2
    | (_, Array(_, NONE)) => ty1
    | _ => ty1

fun vars_compatible vi1 vi2 =
    get_mname vi1 <> get_mname vi2 orelse
    is_global vi1 <> is_global vi2 orelse
    types_compatible (is_global vi1) (get_vtype vi1) (get_vtype vi2)

(* ----------------------------------------------------------------------

    vars field contains list of all variables of a given original name
    that are encountered.

    scope contains a stack of varinfo information, where top element
    of the stack is the current scope (innermost block).

    variables in these tables are indexed by their original names.

   ---------------------------------------------------------------------- *)

datatype modify_var = M of var_info | TheHeap | PhantomState
  | GhostState | AllGlobals
(* the AllGlobals summary is used in initial analysis of function bodies.
Underspecified operations modify AllGlobals rather than listing all the
actual globals, so that globals which are never *explicitly* modified can
still be candidates for const promotion. AllGlobals is expanded out once that
is done. *)

fun mvar_compare (mv1, mv2) = let
    fun mvid (M _) = 1
      | mvid TheHeap = 2
      | mvid PhantomState = 3
      | mvid GhostState = 4
      | mvid AllGlobals = 5
    fun mvc2 (M vi1, M vi2) = vi_compare (vi1, vi2)
      | mvc2 _ = EQUAL
    val id1 = mvid mv1
    val id2 = mvid mv2
  in if id1 < id2 then LESS else (if id1 > id2
    then GREATER
    else mvc2 (mv1, mv2)) end

fun string_of_mvar TheHeap = "<the heap>"
  | string_of_mvar (M vi) = MString.dest (get_mname vi)
  | string_of_mvar PhantomState = "<phantom state>"
  | string_of_mvar GhostState = "<ghost state>"
  | string_of_mvar AllGlobals = "<*>"

structure MVar_Table = Table(struct type key = modify_var
                                    val ord = mvar_compare
                             end)



datatype fncall_type = DirectCall of string
                     | FnPtrCall of (int ctype * int ctype list) *
                                    (string * ExprDatatype.var_info) list * (* potentially called functions *)
                                    bool (* true if C-style object method *)

val ty_ord = ctype_ord int_ord
val funty_ord = prod_ord ty_ord (list_ord ty_ord)
fun fncall_ord (f1,f2) =
    case (f1, f2) of
      (DirectCall s1, DirectCall s2) => string_ord(s1, s2)
    | (DirectCall _, _) => LESS
    | (_, DirectCall _) => GREATER
    | (FnPtrCall (x1, x2, x3), FnPtrCall (y1, y2, y3)) =>
        prod_ord funty_ord (prod_ord (list_ord (prod_ord (string_ord) (ExprDatatype.var_info_ord))) bool_ord) 
         ((x1, (x2, x3)), (y1, (y2, y3)))

datatype selector = Field of string | Array_Index

fun selector_ord (Field s1, Field s2) = fast_string_ord (s1, s2)
  | selector_ord (Field _ , Array_Index) = LESS
  | selector_ord (Array_Index, Field _)  = GREATER
  | selector_ord (Array_Index, Array_Index) = EQUAL

val selectors_ord = list_ord selector_ord
type callgraph =
  {callees: string Binaryset.set Symtab.table, callers: string Binaryset.set Symtab.table}

@{record \<open>
datatype csenv (* CalculateSatate environment *) = Csenv of
                 {senv : senv, union_variants: union_variants,  allow_underscore_idents : bool,
                 anon_vars : bool,
                 fninfo : (int ctype (* return *) * bool (* proto *) *
                           var_info list (* params *)) Symtab.table,
                 hpfninfo : Absyn.ext_decl Symtab.table,
                 vars : var_info list Symtab.table,

                 (* A mapping from mangled variable names to the matching variable
                    declarations. `demangle_table[long_name][5]` is a variable which
                    received the mangled name `long_name`.

                    Excludes global vars, anonymous local vars, and return vars. *)
                 mangled_vars : var_info list Symtab.table,

                 scope : var_info Symtab.table list,
                 array_mentions : (int ctype * int) Binaryset.set,
                 enumenv : string wrap list *
                           (IntInf.int * string option) Symtab.table,
                 globinits : Absyn.expr MSymTab.table,
                 heaptypes : int ctype Binaryset.set,
                 usedtypes : int ctype Binaryset.set, (* subset of types that are actually used by variables *)
                 call_info : fncall_type Binaryset.set Symtab.table,
                 caller_info : string Binaryset.set Symtab.table,
                 referenced_funs : string list Symtab.table, (* calls and addressed funs *)
                 addressed : (expr * selector list) list XMSymTab.table,
                 addressed_types: selector list Ord_List.T Absyn.CTypeTab.table,
                 embedded_fncalls : fncall_type Binaryset.set,
                 recursive_functions : string Binaryset.set,
                 defined_functions : Region.Wrap.region Symtab.table,
                 modifies : modify_var Binaryset.set Symtab.table,
                 modify_locs : string Binaryset.set MVar_Table.table,
                 read_globals : modify_var Binaryset.set Symtab.table,
                 fnspecs : fnspec list Symtab.table,
                 owners : string list,
                 munge_info_fname : Path.T option,
                 constant_global_fun_ptrs: (string * string list) list,
                 fun_ptr_params: ((string * ExprDatatype.var_info) list) option list Symtab.table, (* variables with which function pointer parameters are called*)
                 cliques : string list list,
                 final_callgraph : callgraph, 
                 final_callgraph_with_exit: callgraph}
\<close>}





val get_fulleenv = get_enumenv
fun get_enumenv cse = #2 (get_fulleenv cse)

fun get_rettype fnname (Csenv {fninfo,...}) =
    Option.map #1 (Symtab.lookup fninfo fnname)
fun get_params fname (Csenv {fninfo,...}) =
    Option.map #3 (Symtab.lookup fninfo fname)
fun get_callgraph cse = get_call_info cse |> Symtab.delete_safe NameGeneration.exitN

fun get_direct_callees cse fname =
  case Symtab.lookup (get_callgraph cse) fname of
    SOME set => Binaryset.listItems set
      |> map_filter (fn DirectCall s => SOME s | _ => NONE)
      |> filter_out (fn n => n = fname orelse n = NameGeneration.exitN)
  |  NONE => []

fun get_fun_ptr_calls cse fname =
  case Symtab.lookup (get_call_info cse) fname of
    SOME callees => Binaryset.listItems callees |> map_filter (fn FnPtrCall x => SOME x | _ => NONE)
  | NONE => []

fun has_fun_ptr_calls cse fname =
  not (null (get_fun_ptr_calls cse fname))

fun get_fun_ptr_callees cse fname =
 get_fun_ptr_calls cse fname |> map #2 |> flat
 |> map_filter (fn (n, r) => case !r of SOME (_, FunctionName) => SOME n | _ => NONE)


fun get_fun_ptr_parameters cse fname =
  case Symtab.lookup (get_fninfo cse) fname of
    SOME (_,_, args) => args |> map (fn a => case get_vtype a of Ptr (Function fty) => SOME a | _ => NONE)
  | _ => []

fun has_fun_ptr_parameters cse fname =
  exists is_some (get_fun_ptr_parameters cse fname)

fun all_fun_ptr_parameters cse =
  Symtab.dest (get_fninfo cse)
  |> map (fn (_, (_,_, args)) =>
      args |> map_filter (fn a => case get_vtype a of Ptr (Function _) => SOME a | _ => NONE))
  |> flat

fun all_fun_ptr_parameter_types cse =
  all_fun_ptr_parameters cse |> map ((fn (Ptr fty) => fty) o get_vtype) |> distinct (op =)

fun all_method_fun_ptr_types cse =
  let
    fun method_type (FnPtrCall ((retT, argTs), _, True)) = SOME (CType.Function (retT, argTs))
      | method_type _ = NONE
    val Ts = get_callgraph cse |> Symtab.dest |> maps (Binaryset.listItems o snd) 
      |> map_filter method_type |> sort_distinct (CType.ctype_ord int_ord)
  in
    Ts
  end

fun add_function_ptr (senv: senv) ty fts =
  case ty of
    Ptr (f as (Function _)) => f::fts
  | Array (ty', _) => add_function_ptr senv ty' fts
  | StructTy s => fts |> fold (add_function_ptr senv) ((map (#1 o #2) o #2) (the (AList.lookup (op =) senv s)))
  | UnionTy s => fts |> fold (add_function_ptr senv) ((map (#1 o #2) o #2) (the (AList.lookup (op =) senv s)))
  | _ => fts

fun contains_function_ptr senv ty =
  not (null (add_function_ptr senv ty []))

val get_callers = get_caller_info
fun get_fun_modifies (Csenv {modifies,...}) fname = Symtab.lookup modifies fname

fun get_fun_modifies_globals cse fname =
  get_fun_modifies cse fname |> Option.map (Binaryset.listItems) |> these

val get_allow_underscores = get_allow_underscore_idents

fun get_extended_senv cse = get_senv cse @ (maps snd o maps snd) (get_union_variants cse)

fun get_record_info cse s = 
    the (AList.lookup (op =) (get_extended_senv cse) s)    
     handle Option => raise Fail ("get_record_info: no record_info for "^s)

fun get_fields cse s = #2 (the (AList.lookup (op =) (get_extended_senv cse) s))
                       handle Option =>
                              raise Fail ("get_fields: no fields for "^s)

fun get_struct_attrs cse s = #4 (the (AList.lookup (op =) (get_extended_senv cse) s))
                       handle Option =>
                              raise Fail ("get_struct_attrs: no attributes for "^s)

fun get_globals (Csenv {vars,...}) = let
  fun innerfold vi acc =
      if is_global vi andalso not (function_type (get_vtype vi)) then
        vi::acc
      else acc
  fun foldthis (_, vilist) acc = acc |> fold innerfold vilist
in
  List.rev (Symtab.fold foldthis vars [])
end

fun get_fninfo (Csenv {fninfo,...}) = Symtab.delete_safe NameGeneration.exitN fninfo

fun get_functions cse = get_fninfo cse |> Symtab.keys

fun function_specs (Csenv {fnspecs,...}) = fnspecs

fun has_body_spec cse fname = exists (fn StmtDeclDatatype.gcc_attribs _ => false | _ => true)
               (these (Symtab.lookup (function_specs cse) fname))

fun get_non_proto_functions cse = get_fninfo cse |> Symtab.dest
  |> map_filter (fn (n, (_,is_proto,_)) => if is_proto then NONE else SOME n)

fun get_non_proto_and_body_spec_functions cse = get_fninfo cse |> Symtab.dest
  |> map_filter (fn (n, (_,is_proto,_)) => if is_proto andalso not (has_body_spec cse n) then NONE else SOME n)

fun is_recursivefn (Csenv {recursive_functions,...}) s =
    Binaryset.member(recursive_functions, s)

fun get_modified_global_locns (Csenv {modify_locs,...}) = modify_locs

fun get_locals (Csenv {fninfo, vars,...}) fname =
  let
    val all_vars = Symtab.dest vars;
    val (ret_var, params) = case Symtab.lookup fninfo fname of
                   SOME (ret_ty, _ , params) => (MString.dest NameGeneration.return_var_name, params)
                 | _ => error ("get_locals: function " ^ fname ^ " not defined.")
  in
    all_vars
    |> map snd
    |> flat
    |> filter (fn vi => get_fname vi = SOME fname)
    |> filter_out (fn vi_all => get_name vi_all = ret_var orelse
                    member (fn (n,vi) => n = get_name vi) params (get_name vi_all))
  end

fun get_return_vars (Csenv {fninfo, vars,...}) fname =
  let
    val all_vars = Symtab.dest vars;
    val (ret_var, params) = case Symtab.lookup fninfo fname of
                   SOME (ret_ty, _ , params) => (MString.dest NameGeneration.return_var_name, params)
                 | _ => error ("get_return_vars: function " ^ fname ^ " not defined.")
  in
    all_vars
    |> map snd
    |> flat
    |> filter (fn vi => get_fname vi = SOME fname)
    |> filter (fn vi_all => get_name vi_all = ret_var)
    |> distinct ((op =) o apply2 get_name)
  end

fun get_variables (Csenv {fninfo, vars,...}) opt_fname =
  let
    val all_vars = Symtab.dest vars;
  in
    all_vars
    |> map snd
    |> flat
    |> filter (fn vi => get_fname vi = opt_fname)
  end


fun emptycse ({anon_vars,owners,allow_underscore_idents = aui,munge_info_fname,...} : s2s_config)=
    Csenv {
         senv = [], union_variants = [], anon_vars = anon_vars, allow_underscore_idents = aui,
         vars = Symtab.empty, mangled_vars = Symtab.empty,
         scope = [Symtab.empty],
         fninfo = Symtab.empty, hpfninfo = Symtab.empty,
         enumenv = ([],Symtab.empty),
         heaptypes = Binaryset.empty (ctype_ord int_ord),
         usedtypes = Binaryset.empty (ctype_ord int_ord),
         array_mentions = Binaryset.empty (prod_ord (ctype_ord int_ord) int_ord),
         call_info = Symtab.empty,
         caller_info = Symtab.empty,
         referenced_funs = Symtab.empty,
         addressed = XMSymTab.empty,
         addressed_types = Absyn.CTypeTab.empty,
         defined_functions = Symtab.empty,
         embedded_fncalls = Binaryset.empty fncall_ord,
         recursive_functions = Binaryset.empty string_ord,
         modifies = Symtab.empty, modify_locs = MVar_Table.empty,
         fnspecs = Symtab.empty, read_globals = Symtab.empty,
         globinits = MSymTab.empty, owners = owners, munge_info_fname = munge_info_fname, 
         constant_global_fun_ptrs = [], cliques = [], fun_ptr_params = Symtab.empty, 
         final_callgraph = {callees = Symtab.empty, callers = Symtab.empty},
         final_callgraph_with_exit = {callees = Symtab.empty, callers = Symtab.empty}}

fun add_exit cse =
 let
   val exitN = NameGeneration.exitN
   (* fixme: we should not need the variable name exit_status_parN at all, as we never go inside the scope of the exit function*)
   val status_var_info = Var_info {name = exit_status_parN, vtype = Signed Int,
     munged_name = MString.mk (tag_name_with_type {name = exit_status_parN, typname = tyname (Signed Int)}),
     proto_param = true, struct_env = [], fname = SOME exitN, return_var = false, attrs = [],
     declared_at = Region.bogus, method_call_tmp_var = false}
   val exit_var_info = Var_info {name = exitN, vtype = Function (Void, [Signed Int]),
     munged_name = MString.mk (exitN),
     proto_param = false, struct_env = [], fname = NONE, return_var = false, attrs = [],
     declared_at = Region.bogus, method_call_tmp_var = false}
 in
   cse

   |> map_fninfo (Symtab.update (exitN, (Void, true, [status_var_info])))
   |> map_scope (fn [s] => [(Symtab.update (exitN, exit_var_info) s)])


 end


fun get_addressed_vis fname (Csenv {vars, addressed, ...}) = let
  fun innerfold vi acc =
      if XMSymTab.defined addressed (get_mname vi, fname) then
        vi::acc
      else acc
  fun foldthis (_, vis) acc = acc |> fold innerfold vis
in
  Symtab.fold foldthis vars []
end


fun get_pruned_senv cse =
  let
    val senv = get_senv cse
    val used_types = get_usedtypes cse
  in
    senv |> filter (fn item => Binaryset.member (used_types, type_of_rcd item))
  end

fun upd_mname mname  = map_munged_name (K mname)

fun vi_upd_type ty  = map_vtype (K ty)


fun fns_by_type cse (retty, ptyps) = let
  val fninfo = get_fninfo cse
  fun listcmp x =
      case x of
        ([], []) => true
      | (ctyp::ctyps, vi::vis) => ctyp = get_vtype vi andalso
                                  listcmp (ctyps, vis)
      | _ => false
  fun foldthis (nm, (nm_retty, _, ps)) acc =
      if nm_retty = retty andalso listcmp (ptyps, ps) then nm::acc
      else acc
in
  Symtab.fold foldthis fninfo []
end


fun mk_recursive f =
    map_recursive_functions (fn s => Binaryset.add(s,f))

fun new_embedded_fncall s cse =
    map_embedded_fncalls (fn set => Binaryset.add(set,s)) cse

fun add_addressed_type ty selectors =
  map_addressed_types
   (Absyn.CTypeTab.map_default
     (ty, Ord_List.make selectors_ord [selectors])
     (Ord_List.insert selectors_ord selectors))

fun new_addressed vi expr (selectors: selector list) =
  map_addressed (XMSymTab.map_default ((get_mname vi, get_fname vi), []) (cons (expr, selectors)))
  #> add_addressed_type (get_vtype vi) selectors

fun new_array tysz =
    map_array_mentions (fn s => Binaryset.add(s,tysz))

fun add_heaptype ty env = let
  val htypes = get_heaptypes env
in
  if Binaryset.member(htypes, ty) then env
  else
    let
      val env' = map_heaptypes (fn s => Binaryset.add(s, ty)) env
      fun struct_or_union s =
        case AList.lookup (op =) (get_senv env') s of
            NONE => (* do nothing for the moment, thus env, not env' *) env
          | SOME (_, flds, _, _) =>
            env' |> fold (fn (_, (fldty,_)) => add_heaptype fldty) flds
    in
      case ty of
        Ptr ty0 => add_heaptype ty0 env'
      | Array(ty0, _) => add_heaptype ty0 env'
      | StructTy s => struct_or_union s
      | UnionTy s => struct_or_union s
      | _ => env'
    end
end


fun update_hpfninfo0 d tab =
    case d of
        FnDefn((_, fname), _, _, _) => Symtab.update(node fname,d) tab
      | Decl d0 => let
        in
          case node d0 of
            ExtFnDecl(ed0 as {name = name_w,...}) => let
              val name = node name_w
            in
              case Symtab.lookup tab name of
                NONE => Symtab.update(name, d) tab
              | SOME (FnDefn _) => tab
              | SOME (Decl d1) => let
                in
                  case node d1 of
                    ExtFnDecl {specs,name,rettype,params} => let
                      val newd0 = {rettype=rettype,name=name,params=params,
                                   specs=merge_specs (#specs ed0) specs}
                      val newd = wrap(ExtFnDecl newd0, left d0, right d0)
                    in
                      Symtab.update (node name, Decl newd) tab
                    end
                  | _ => tab
                end
            end
          | _ => tab
        end

fun update_hpfninfo d = map_hpfninfo (update_hpfninfo0 d)

fun insert_fnretty ctxt (s, ty, env) = let
  open Feedback
  fun upd tab =
      case Symtab.lookup tab (node s) of
        NONE => (informStr ctxt (6, "Recording return type of "^ tyname ty^
                               " for function "^ node s);
                 Symtab.update(node s,(ty,true,[])) tab)
                (* insert dummy values for parameters *)
      | SOME (ty',_,_) => if ty = ty' then tab
                          else
                            (Feedback.errorStr' ctxt (left s, right s,
                                                "Incompatible return type");
                             tab)
in
  map_fninfo upd env
end

fun new_defined_fn s =
    map_defined_functions (Symtab.update(node s, Region.Wrap.region s))

fun set_proto_params fname ps env = let
  fun upd tab =
      case Symtab.lookup tab fname of
        NONE => raise Fail "set_proto_params: This should never happen"
      | SOME(retty,protop,_) => if not protop then tab
                                else Symtab.update(fname,(retty,true,ps)) tab
in
  map_fninfo upd env
end

fun set_defn_params fname ps env = let
  fun upd tab =
      case Symtab.lookup tab fname of
        NONE => raise Fail "set_defn_params: This should never happen"
      | SOME (retty,_,_) => Symtab.update(fname, (retty,false,ps)) tab
in
  map_fninfo upd env
end

fun add_modification fname vi env = let
  val dflt = Binaryset.empty mvar_compare
  val dflt_locs = Binaryset.empty string_ord
  fun add e set = Binaryset.add(set,e)
in
  (map_modifies (Symtab.map_default (fname, dflt) (add vi)) o
   map_modify_locs (MVar_Table.map_default (vi,dflt_locs) (add fname)))
  env
end

fun add_read fname mvi env = let
  val dflt = Binaryset.empty mvar_compare
  fun add e set = Binaryset.add(set, e)
in
  map_read_globals (Symtab.map_default (fname,dflt) (add mvi)) env
end

fun calc_all_globals cse = let
  open MSymTab
  val all_globals = let
    fun foldthis (vi as Var_info vr) tab =
        if #return_var vr then tab
        else
          update (get_mname vi, get_vtype vi) tab
  in
    empty |> Basics.fold foldthis (get_globals cse)
  end
in
  all_globals
end

fun calc_untouched_globals cse = let
  open MSymTab
  fun mydelete (t,e) = delete_safe e t
  val all_globals = calc_all_globals cse
  val remove_modified = let
    fun foldthis (mvar, _) set =
        case mvar of
          M vi => mydelete(set, get_mname vi)
        | _ => set
  in
    MVar_Table.fold foldthis (get_modified_global_locns cse)
  end
  val remove_addressed = let
    fun foldthis ((k, NONE), _) set = mydelete(set, k)
      | foldthis _ set = set
  in
    XMSymTab.fold foldthis (get_addressed cse)
  end
in
  all_globals
      |> remove_modified
      |> remove_addressed
end



fun get_vi_nm_info (Csenv cse) (Var_info {name, munged_name, ...}) : nm_info =
    let
    in
      {src_name = name, isa_name = munged_name}
    end

(* ML computation of alignment and type sizes *)
val ti  = IntInf.toInt
fun ialignof ity = let
  open ImplementationNumbers
in
  case ity of
    Char => ti 1
  | Short => ti (shortWidth div CHAR_BIT)
  | Int => ti (intWidth div CHAR_BIT)
  | Long => ti (longWidth div CHAR_BIT)
  | LongLong => ti (llongWidth div CHAR_BIT)
  | Int128 => ti (int128Width div CHAR_BIT)
end

fun roundup base n = if n mod base = 0 then (n, false) else ((n div base + 1) * base, true)
fun maxl [] = 0
  | maxl (h::t) = let val m = maxl t in if h > m then h else m end

fun alignof_attrs [] = NONE
  | alignof_attrs (AlignedExponent i::_) = SOME (IntInf.pow(2, i))

fun alignof_attr_of_struct_or_union cse s =
  case alignof_attrs (get_struct_attrs cse s) of
    SOME a => a
  | NONE => 1

fun gen_alignof cse (ty, attrs) : Int.int =
  case alignof_attrs attrs of SOME i => Int.max (i, (gen_alignof cse (ty, [])))
  | NONE =>
    let
      open ImplementationNumbers
    in
      case ty of
        Signed i => ialignof i
      | Unsigned i => ialignof i
      | PlainChar => 1
      | Bool => 1
      | Ptr _ => IntInf.toInt (ptrWidth div CHAR_BIT)
      | StructTy s => maxl (alignof_attr_of_struct_or_union cse s :: map (gen_alignof cse o #2) (get_fields cse s))
      | UnionTy s => maxl (alignof_attr_of_struct_or_union cse s :: map (gen_alignof cse o #2) (get_fields cse s))
      | Array(base, _) => gen_alignof cse (base, [])
      | EnumTy _ => gen_alignof cse (Signed Int, [])
      | Ident _ => raise Fail "ProgramAnalysis.alignof: typedefs need to be \
                              \compiled out"
      | Function _ => raise Fail "ProgramAnalysis.alignof: functions have no \
                                 \alignment"
      | Bitfield _ => ialignof Int
      | Void => raise Fail "ProgramAnalysis.alignof: void has no alignment"
      | _ => raise Fail ("ProgramAnalysis.alignof: no alignment for "^tyname ty)
    end


fun join_bitfields tylist =
  let
    fun join (b1 as (Bitfield (ty1, i),[])) (b2 as (Bitfield (ty2, j),[])) =
      if #2 (dest_int_type ty1) = #2 (dest_int_type ty2)
      then [(Bitfield (ty1, i + j), [])]
      else [b1, b2]
      | join ty1 ty2 = [ty1, ty2]
    fun joins [] = []
      | joins [ty] = [ty]
      | joins (ty1::ty2::tys) = (join ty1 ty2 @ tys)

  in
    fold_rev (fn ty => fn tys => joins (ty::tys)) tylist []
  end

fun gen_offset strict cse tylist n =
  let
    val offset = gen_offset strict cse
  in
    if n = 0 then (0, false)
    else if length tylist <= n then (0, false)
    else
      let
        val (offn', padding0) = offset tylist (n - 1)
        val tyn' = #1 (List.nth(tylist, n - 1))
        val tyn = List.nth(tylist, n)
        val (sz', padding') = gen_sizeof strict cse tyn'
        val b = offn' + sz'
        val (res, padding1) = roundup (gen_alignof cse tyn) b
      in
        (res, padding0 orelse padding' orelse padding1)
      end
  end
and gen_strsize strict cse s : (Int.int * bool) =
  let
    val (kind, flds, _, attrs) = get_record_info cse s
    val algn = the_default 1 (alignof_attrs attrs)
    val tys = map #2 flds
  in
    case kind of
      Struct =>
        let
          val tys' = join_bitfields tys
          val lastn = length tys' - 1
          val lastty = #1 (List.last tys')
          val (off, padding1) = gen_offset strict cse tys' lastn
          val a = maxl (algn :: (map (gen_alignof cse) tys'))
          val (sz', padding2) = gen_sizeof strict cse lastty
          val (res, padding3) = roundup a (off + sz')
        in
          (res, padding1 orelse padding2 orelse padding3)
        end
    | Union active =>
        let
          fun error_msg sizes flds = Pretty.block (
                [Pretty.str  ("different variants of union " ^ quote s ^ " don't have same size: ")] @
                [Pretty.list "" ""  (map (fn ((n, _), size) => Pretty.str (n ^ ": " ^ string_of_int size)) (flds ~~ sizes))])
            |> Pretty.string_of
          val fld_sizes_paddings = map (fn (s, (t, _)) => (s, gen_sizeof strict cse t)) flds
          val fld_sizes = map (apsnd fst) fld_sizes_paddings
          val paddings = map (#2 o #2) fld_sizes_paddings
          val variant_padding = exists I paddings
          val sizes = (map (#2) fld_sizes)
          val size = case distinct (op =) sizes of
                  [size] => size
                | _ =>
                  if strict then error (error_msg sizes flds)
                  else
                    (case filter (fn (n, _) => member (op =) active n) fld_sizes |> sort (rev_order o int_ord o apply2 snd) of
                       [] =>
                        let
                          val _ = warning (error_msg sizes flds ^ "\n" ^
                                  "Picking size 0 as there is no active variant at all")
                        in 0 end
                     | [(f, s)] =>
                        let
                          val _ = warning (error_msg sizes flds ^ "\n" ^
                                  "Picking size " ^ string_of_int s  ^ " of active variant " ^ quote f)
                        in s end
                     | (f, s)::_ =>
                        let
                          val _ = warning (error_msg sizes flds ^ "\n" ^
                                  "Picking size " ^ string_of_int s  ^ " of largest active variant " ^ quote f)
                        in s end)

          val a = maxl (algn :: (map (gen_alignof cse) tys))
          val (res, padding) = roundup a size
        in
          (res, variant_padding orelse padding)
        end
  end

and gen_sizeof strict cse ty = Absyn.sizeof (gen_strsize strict cse) ty
val sizeof_padding = gen_sizeof false
val sizeof = fst oo sizeof_padding
val offset_padding = gen_offset false
val offset = fst ooo offset_padding
val strsize = gen_strsize false
fun alignof cse ty = gen_alignof cse (ty,[])

fun offsetof cse s fld =
  let
    val (kind, fields, _, _) = get_record_info cse s
    val idx = find_index (fn (n, _) => n = fld) fields
  in
    if idx >= 0
    then (case kind of
            Struct => offset cse (map snd fields) idx
          | Union  _ => 0)
    else (case kind of Struct => ~1
           | Union _ => if fld = NameGeneration.bytesN then 0 else ~1)
  end

fun offsetof' cse s flds =
  case flds of
    [] => error ("offsetof': empty field list")
  | [fld] => offsetof cse s fld
  | (fld::flds') =>
      let
        val (kind, fields, _, _) = get_record_info cse s
      in
        case find_first (fn (n, _) => n = fld) fields of
          SOME (_, (cty, _)) =>
            let
              val s' = case cty of CType.StructTy s' => s' | CType.UnionTy s' => s'
                | _ => error ("offsetof': expecting structure or union got: " ^ @{make_string} cty)
            in
              offsetof cse s fld + offsetof' cse s' flds'
            end
        | NONE => ~1
      end


fun type_of_struct_or_union cse s =
 CType.type_of_rcd (s, (get_record_info cse s))

fun sizeof_struct_or_union cse s = sizeof cse (type_of_struct_or_union cse s)
fun alignof_struct_or_union cse s = alignof cse (type_of_struct_or_union cse s)

fun cse2ecenv ctxt cse = CE {enumenv = get_enumenv cse,
                        typing = cse_typing ctxt cse,
                        structsize = strsize cse,
                        offset_of = offsetof' cse}
and cse_typing ctxt cse e = let
  val scopes = get_scope cse
  fun var_typing [] _ = NONE
    | var_typing (tab::rest) s =
      case Symtab.lookup tab s of
        NONE => var_typing rest s
      | SOME vi => SOME (get_vtype vi)
                    handle Empty => raise Fail "Empty vi-list in cse_typing"
in
  ExpressionTyping.expr_type ctxt (cse2ecenv ctxt cse)
                              (get_senv cse)
                              (var_typing scopes)
                              e
end

local
open ExprDatatype
datatype access = Field of string | Index of int option

fun dest_access ctxt ecenv (Var (s, info)) = ((s, info), [])
  | dest_access ctxt ecenv (StructDot (E e, fld)) =
     let
       val (var, accs) = dest_access ctxt ecenv (node e)
     in (var, accs @ [Field fld]) end
  | dest_access ctxt ecenv (ArrayDeref (E a, i)) =
     let
       val (var, accs) = dest_access ctxt ecenv (node a)
       val idx = try (consteval false ctxt ecenv) i
     in (var, accs @ [Index idx]) end
  | dest_access _ _ _ = raise Match

fun dest_node_var x = case node x of Var x => [x] | _ => []

fun dest_init_var (InitE (E x)) = dest_node_var x
  | dest_init_var _ = []

fun dest_init_array (InitList xs) = map snd xs
  | dest_init_array _ = []

fun dest_init_field fld (InitList xs) =
  AList.lookup (fn (fld, [DesignFld x]) => x = fld | _ => false) xs fld |> the_list
  | dest_init_field _ _ = []

fun approx_literal_access [] is = map dest_init_var is |> flat
  | approx_literal_access (Index NONE::accs) is =
      is |> map dest_init_array |> flat |> approx_literal_access accs
  | approx_literal_access (Index (SOME i)::accs) is =
      is |> map dest_init_array |> map (fn xs => nth xs i) |> approx_literal_access accs
  | approx_literal_access (Field fld::accs) is =
      is |> map (dest_init_field fld) |> flat |> approx_literal_access accs

fun dest_init_expr (E x) =
  case node x of
    (Var _) => [InitE (E x)]
  | (CompLiteral (_, xs)) => [InitList xs]
  | _ => []

fun add_accesses (senv:senv) cty accss =
  let
    fun struct_or_union s accs =
      let
        val fld_tys = (map (apsnd #1)) (#2 (the (AList.lookup (op =) senv s)))
        val accss = fld_tys |> map (fn (fld, ty) => map (cons (Field fld)) accss) |> flat
      in accss end
  in
    case cty of
      Array (ty, _) => add_accesses senv ty (map (cons (Index NONE)) accss)
    | StructTy s => struct_or_union s accss
    | UnionTy s => struct_or_union s accss
    | _ => accss
    end

fun all_accesses senv cty = add_accesses senv cty [[]] |> map rev

in

fun approx_expr ctxt cse e =
  let
    val ecenv = cse2ecenv ctxt cse
  in
    try (dest_access ctxt ecenv) e
    |> Option.map (fn ((v, info), accs) =>
         (case MSymTab.lookup (get_globinits cse) (MString.mk v) of
           SOME e => dest_init_expr e |> approx_literal_access accs
          | NONE => if null accs then [(v,info)] else []))
    |> these
  end


fun approx_globals cse =
  let
    val senv = get_senv cse
    val vars = get_variables cse NONE
    fun lookup g = find_first (fn vi => get_munged_name vi = g) vars
    fun typ_of g = lookup g |> the |> get_vtype
    fun approx (g, e) =
      let
        val inits = dest_init_expr e
        val accss = all_accesses senv (typ_of g)
      in ( MString.dest g, accss |> map (fn accs => approx_literal_access accs inits) |> flat) end
  in
    MSymTab.dest (get_globinits cse)
    |> map approx
  end

fun eq_string_assoc (xs, ys) =
  let
    val xs = sort (fast_string_ord o apply2 fst) xs
    val ys = sort (fast_string_ord o apply2 fst) ys
  in
    map fst xs = map fst ys andalso
    map (sort fast_string_ord o snd) xs = map (sort fast_string_ord o snd) ys
  end

fun type_of_var_info v = !v |> Option.map fst

fun approx_global_fun_ptrs cse =
  approx_globals cse
  |> map (apsnd (map_filter
       (fn (n, vi) =>
          let val T = the (type_of_var_info vi)
          in if CType.fun_ptr_type T orelse CType.function_type T then SOME n else NONE end)))

end

fun merge_params [] [] = []
  | merge_params (NONE::xs) (NONE::ys) = NONE::merge_params xs ys
  | merge_params (SOME vs::xs) (SOME ws::ys) = SOME (vs @ ws)::merge_params xs ys
  | merge_params xs ys = error ("merge_params unexpected input: " ^ @{make_string} (xs, ys))

fun add_fun_ptr_params fname params =
 if exists is_some params
 then Symtab.map_default (fname, params) (merge_params params)
 else I


fun new_call ctxt (x as {caller, callee, args}) cse =
  let
    val cse' = map_call_info
                   (Symtab.map_default (caller, Binaryset.empty fncall_ord)
                                       (fn s => Binaryset.add(s,callee)))
                   cse
  in
    case callee of
      DirectCall somefn =>
      let
        val fun_ptr_params = get_fun_ptr_parameters cse somefn
        val fun_ptr_args = (args ~~ fun_ptr_params) |> map (fn (e, SOME _) => SOME (enode e) | _ => NONE)
        val addressed_funs = fun_ptr_args |> map (Option.map (approx_expr ctxt cse))
      in
        cse'
        |> map_caller_info
            (Symtab.map_default (somefn, Binaryset.empty string_ord)
                                (fn s => Binaryset.add(s,caller)))
        |> map_fun_ptr_params (add_fun_ptr_params somefn addressed_funs)
      end
    | _ => cse'
  end

fun raw_fndes_callinfo ctxt cse e =
    case (cse_typing ctxt cse e, enode e) of
      (Function x, Var(s, _)) =>
        let
        in
          (DirectCall s, x)
        end
    | (ty, e') => let
      in
        case ty of
          Function x => (FnPtrCall (x, approx_expr ctxt cse e' , false), x)
        | Ptr (Function x) =>
            (FnPtrCall (x, approx_expr ctxt cse e', false ), x)
        | _ => eFail ctxt (e, "Function designator has bad type ("^
                               tyname ty ^ ")")
      end

fun get_local_info cse (n, NONE) = NONE
  | get_local_info cse (loc as (n, SOME fname)) =
  let
    val addressed = XMSymTab.defined (get_addressed cse) loc
    val vars = get_variables cse (SOME fname)
    fun match vi = MString.eq (get_mname vi, n)
    val params = get_params fname cse |> these
    val i = find_index match params

  in
    if 0 <= i then SOME {kind = NameGeneration.In i, addressed = addressed, info = nth params i}
    else find_first match vars |> Option.map (fn info => {kind=NameGeneration.Loc, addressed= addressed, info= info})
  end

fun dest_method_fun_ptr ctxt cse fn_e =
  (case raw_fndes_callinfo ctxt cse fn_e of
    (FnPtrCall ((retT, argTs), funs, _), _) => 
      (case Expr.vars_expr {typ = false, addr = false} fn_e of
        [(p, var_info)] => 
           (case !var_info of
              SOME (pT, MungedVar {munge, fname = SOME fname, ...}) => 
                (case get_local_info cse (munge, SOME fname) of 
                  SOME {info, ...} =>
                    if CType.fun_ptr_type (get_vtype info) andalso not (get_method_call_tmp_var info) then   
                       NONE
                    else (* no plain function pointer, e.g. reference to a structure containing function pointers*)
                      SOME (Ptr (Function (retT, argTs)), fname)
                  | _ => NONE )
                
             | _ => NONE)
       | _ => NONE)
  | _ => NONE)

fun fndes_callinfo ctxt cse fn_e =
  case raw_fndes_callinfo ctxt cse fn_e of
    (FnPtrCall (ty, fs, false), x) => (FnPtrCall (ty, fs, is_some (dest_method_fun_ptr ctxt cse fn_e)), x)
  | res => res
 

fun process_enumdecl ctxt (enameopt_w,econsts) env = let
  fun mk_ecenv (set, enum_tab) = CE {enumenv = enum_tab,
          typing = cse_typing ctxt env, structsize = strsize env, offset_of = offsetof' env}
  fun foldthis (ecn_w, eopt) (i, set, enum_tab) =
      case List.find (fn sw => node sw = node ecn_w) set of
        SOME first => (Feedback.errorStr' ctxt (left ecn_w, right ecn_w,
                                          "Re-using enum const (" ^ node ecn_w ^
                                          ") from "^
                                          Region.toString
                                              (Region.Wrap.region first));
                       (i, set, enum_tab))
      | NONE => let
          val e_val = case eopt of
                        NONE => i
                      | SOME e => consteval true ctxt (mk_ecenv (set, enum_tab)) e
          val tab' = Symtab.update(node ecn_w, (e_val, node enameopt_w)) enum_tab
        in
          (e_val + 1, ecn_w::set, tab')
        end
  val (set0, enum_tab0) = get_fulleenv env
  val (_, set', enum_tab') = (0, set0, enum_tab0) |> fold foldthis econsts
in
  map_enumenv (K (set', enum_tab')) env
end

fun process_type process_exp ctxt (posrange as (l,r)) ty env =
    case ty of
      Array(elty, sz_opt) => let
        val env' = process_type process_exp ctxt posrange elty env
        val ecenv = cse2ecenv ctxt env
        val ti = IntInf.toInt
      in
        case sz_opt of
          NONE => env'
        | SOME sz_e => let
            val sz_i = ti (consteval true ctxt ecenv sz_e)
          in
            if sz_i < 1 then let
                val region = Region.make{left=l,right=r}
              in
                raise Fail ("Array in area "^Region.toString region^
                            " has non-positive size "^Int.toString sz_i)
              end
            else
              new_array (constify_abtype true ctxt ecenv elty, sz_i) env'
          end
      end
    | Ptr ty' => let
        val ty'' = constify_abtype true ctxt (cse2ecenv ctxt env) ty'
      in
        process_type process_exp ctxt posrange ty' (add_heaptype ty'' env)
      end
    | Bitfield (ty, n) =>
      let
        val _ = if can dest_int_type ty then () else
                   Feedback.errorStr' ctxt (l, r, "expecting integer type for bitfield")
      in
        env
      end
    | TypeOf e => process_exp e env
    | _ => env


fun check_uscore_ok s = let
  val s = NameGeneration.rmUScoreSafety s
in
  s <> "" andalso String.sub(s,0) <> #"_"
end

fun report_error ctxt l r f x =
  let
    val res = f x
  in
    ()
  end handle ERROR s => Feedback.errorStr' ctxt (l, r, s)


fun newstr_decl process_expr ctxt (kind: rcd_kind) (nm, flds0 : (expr ctype * string wrap * gcc_attribute list) list, sattrs0) cse = let
  open NameGeneration
  fun foldthis (cty,fldnm,attrs) acc =
      process_type process_expr ctxt (left fldnm, right fldnm) cty acc
  val cse = cse |> fold foldthis flds0
  val ecenv = cse2ecenv ctxt cse
  fun uscore_check i nmty s =
      if get_allow_underscores cse orelse check_uscore_ok (node s) then ()
      else
        Feedback.error_range ctxt (left s) (right s)
                           (rmUScoreSafety (i (node s)) ^
                           " is an illegal name for a structure " ^nmty)

  fun add_aligned' l r (GCC_AttribFn ("aligned", [e])) (attrs:CType.attribute list) =
        let
          val i = consteval true ctxt ecenv e
          val exp = IntInf.log2 i
          val _ = if IntInf.pow (2, exp) = i then () else
                Feedback.error_range ctxt l r ("aligned attribute may only contain powers of 2: " ^ string_of_int i)
        in
          (AlignedExponent exp)::attrs
        end
    | add_aligned' _ _ _ attrs = attrs

  fun check_align attrs = length (filter (fn AlignedExponent _ => true) attrs) <= 1
  fun add_aligned l r gcc_attr (attrs:CType.attribute list) =
    let
      val res = add_aligned' l r gcc_attr attrs
      val _ = if check_align res then () else
           Feedback.error_range ctxt l r ("at most one aligned attribute is allowed")
     in res end

  val sattrs = [] |> fold (add_aligned (left sattrs0) (right sattrs0)) (node sattrs0)
  val flds =
      map (fn (ty,s,attrs) =>
              ((uscore_check unC_field_name "field" s; node s),
               (remove_enums (constify_abtype true ctxt ecenv ty), [] |> fold (add_aligned (left nm) (right nm)) attrs)
               ))
          flds0
  val _ = uscore_check unC_struct_name "tag" nm
  val r = Region.make {left=left nm, right=right nm}
  val cse' = map_senv (fn rest => (node nm, (kind, flds, r, sattrs)) :: rest) cse
in
  cse'
end

fun add_variant variant union = map_senv (AList.map_entry (op =) union (fn (Union active, flds, r, attrs) =>
  (Union (distinct (op =) (variant::active)), flds, r, attrs)))


fun find_scoped_vdecl ctxt name scope = let
  fun recurse i scope =
    case scope of
      [] => NONE
    | (db::rest) => let
      in
        case Symtab.lookup db name of
          NONE => recurse (i + 1) rest
        | SOME vi => let
            val fnm = case get_fname vi of NONE => "<global>" | SOME s => s
          in
            Feedback.informStr ctxt (10, "find_scoped_vdecl: Found "^fnm^":"^name^
                                   " at depth "^Int.toString i);
            SOME (i,vi)
          end
      end
in
  recurse 0 scope
end

val new_scope = map_scope (fn l => Symtab.empty :: l)
val pop_scope = map_scope tl
fun fupd_hd _ [] = raise Fail "fupd_hd: empty list"
  | fupd_hd f (h :: t) = f h :: t
fun fupd_last _ [] = raise Fail "fupd_last: empty list"
  | fupd_last f [h] = [f h]
  | fupd_last f (h1::t) = h1::fupd_last f t

fun pluck _ [] = NONE
  | pluck P (h::t) = if P h then SOME(h,t)
                     else case pluck P t of
                            NONE => NONE
                          | SOME (e,rest) => SOME (e, h::rest)

(* `munge_insert` adds a newly declared variable to the map of all seen variables,
   and to the current scope. If a global of the same name and incompatible type
   is encountered, we show an error.
*)
fun munge_insert ctxt (v as Var_info vrec) cse = let
  val v_table = get_vars cse
  fun prepend_insert (n,vi) = Symtab.map_default (n,[]) (fn t => vi::t)
  val name = #name vrec
  fun merge_global_vis v1 v2 = let
    val ty1 = get_vtype v1
    val ty2 = get_vtype v2
  in
    vi_upd_type (max_type ty1 ty2) v1
  end
  fun same_global v' =
      is_global v' andalso srcname v' = name andalso get_mname v' = get_mname v
  fun vars_add v1 vlist =
      if not (is_global v1) then prepend_insert(name,v1)
      else
        case pluck same_global vlist of
          NONE => Symtab.update(name, v::vlist)
        | SOME (v2, rest) => Symtab.update(name, merge_global_vis v1 v2::rest)
  fun scope_add v1 tab =
      if not (is_global v1) then Symtab.update(name, v1) tab
      else
        case Symtab.lookup tab name of
          NONE => Symtab.update(name, v1) tab
        | SOME v2 => Symtab.update(name, merge_global_vis v1 v2) tab
  val scope = fupd_hd

  val mname = #munged_name vrec |> MString.dest
  val full_name = the_default mname (get_fname v |> Option.map (fn f =>
    let
      val locs = get_locals cse f
      val conflicts = filter (equal name o get_name) locs
        |> filter_out (equal (get_vtype v) o get_vtype)
    in
      if null conflicts then
         name
      else
         tag_name_with_type {
              name = name, typname = tyname (get_vtype v)
           }
    end))


  val v = upd_mname (MString.mk full_name) v
  val update_mangled_vars = map_mangled_vars (prepend_insert (full_name, v))
  val update_names = update_mangled_vars
in
  if not (get_anon_vars cse) orelse is_global v orelse #return_var vrec then
    case Symtab.lookup v_table name of
      NONE => (v, (update_names o map_vars (Symtab.update(name, [v])) o
                      map_scope (scope (Symtab.update(name, v)))) cse)
    | SOME vlist => let
        val _ = Feedback.informStr ctxt (10,  "Found vlist for "^name^" of length "^
                                        Int.toString (length vlist))
      in
        case List.find (fn v' => not (vars_compatible v v')) vlist of
          NONE => (v, (update_names o map_vars (vars_add v vlist) o
                            map_scope (scope (scope_add v))) cse)
        | SOME badv => let
            open Feedback
            val _ = if is_global v andalso is_global badv then
                      errorStr ctxt (declpos v,
                               "Global variable "^viToString v^
                               " not compatible with previous declaration at "^
                               Region.toString (declpos badv))
                    else
                      ()
          in
            (* In this case:
               - There are previously added variables with the source name
                 `name`.
               - At least one of them is a non-global variable with a different
                 type (which we know from `not vars_compatible`).
               - So we don't bother adding an alias for the new variable.

               fixme: should this *error* if there isn't an existing alias for
               `name`? *)
            (v, (update_names o map_vars (prepend_insert(name, v)) o
                      map_scope (scope (Symtab.update(name, v)))) cse)
          end
      end
  else (* "anonymous" local variables *) let
      val allvars_in_scope = List.concat (map (map #2 o Symtab.dest) (get_scope cse))
      val varprefix = tyname (get_vtype v) ^ "'local"
      fun foldthis vi c =
          if String.isPrefix varprefix (MString.dest (get_mname vi)) then c + 1 else c
      val numdups = 0 |> fold foldthis allvars_in_scope
      val new_vi = upd_mname (MString.mk (varprefix ^ Int.toString numdups)) v
    in
      (new_vi, (map_vars (prepend_insert(name, new_vi)) o
                map_scope (fupd_hd (Symtab.update(name, new_vi)))) cse)
    end
end


fun insert_var ctxt (v as Var_info {name, vtype, fname, ...}, e as Csenv cse) = let
  open Symtab
  val scopes = #scope cse
  val _ = Feedback.informStr ctxt (10,
                             "insert_var: Inserting "^name^"("^tyname vtype^
                             ") at scope depth "^
                             Int.toString (length scopes))
in
  case find_scoped_vdecl ctxt name scopes of
    NONE => munge_insert ctxt v e
  | SOME (i,_) => let
    in
      if is_return_or_tmp (get_mname v) then
        (v, e)
      else if i = length scopes - 1 (* i.e., a global *) then
         munge_insert ctxt v e
      else
         raise Fail ("Variable "^name^ " " ^ fnToString fname ^
                     " declared twice (no scope-masking allowed)")

    end
end

fun inits_to_elist f (InitE e) acc = List.rev (f e :: acc)
  | inits_to_elist f (InitList dis) acc =
       acc |> fold (fn (_, i) => fn a => inits_to_elist f i a) dis

fun tmp_fun_ptr_var_info senv fname count T =
 let
   val nm = tmp_var_name (tyname T, count)
   val retvar = Var_info {name = MString.dest nm, munged_name = nm, vtype = T,
         struct_env = senv, proto_param = false,
         fname = SOME fname, return_var = true, attrs = [],
         declared_at = Region.bogus, method_call_tmp_var = true}
 in
   retvar
 end

fun tmp_method_fun_ptr ctxt fn_e env =
  let
        val env' = the_default env (dest_method_fun_ptr ctxt env fn_e |> Option.map (fn (fun_ptrT, fname) =>
              let 
                val tmpvar = tmp_fun_ptr_var_info (get_senv env) fname 1 fun_ptrT
              in #2 (insert_var ctxt (tmpvar, env)) end))
  in env' end


structure TypeTab = Table(type key = int ctype
                          val ord = ctype_ord int_ord);

datatype lvstate = LV | RV

(* fname is a string option; NONE corresponds to an expression appearing at
   the global level, as can happen in the initialisation of a global *)
fun process_expr ctxt lvstate fname (env as Csenv {senv, ...}) e = let
  fun inc ((fm,greads), k) = (TypeTab.map_default (k,0) (fn i => i + 1) fm, greads)
  (* count_fncalls not only counts function calls in the accompanying fmap,
     but is also a general traversal of the expression, where other stuff
     can be done too *)
  datatype addr_status = Rvalue | BrackLeft | UnderAddr of selector list | BL_Addr of selector list | Lvalue
                       | BrackLeftLV | SzOf
  fun extend_selector sel (UnderAddr sels) = UnderAddr (sel :: sels)
    | extend_selector sel (BL_Addr sels) = BL_Addr (sel :: sels)
    | extend_selector _ adstat = adstat
  fun get_selector (UnderAddr sels) = sels
    | get_selector (BL_Addr sels) = sels
    | get_selector _ = []

  fun lvadstat BrackLeftLV = true | lvadstat Lvalue = true | lvadstat _ = false
  fun pex e env = fst (process_expr ctxt lvstate fname env e)
  datatype eact = E of expr | RAS of addr_status (* Restore Address Status *)
  fun rval (env,fmap,_) = (env,fmap,Rvalue)
  fun count_fncalls (ef as (env,fmap,_)) elist =
      case elist of
        [] => (env,fmap)
      | E e :: es => count_fncall ef e es
      | RAS b :: es => count_fncalls (env,fmap,b) es
  and count_fncall (ef as (env,fmap,adstat)) e es =
      case enode e of
        BinOp(bop, e1, e2) => let
          val scp = bop = LogAnd orelse bop = LogOr
          val acc = if scp andalso eneeds_sc_protection e2 andalso
                       adstat <> SzOf
                    then
                      (env,inc(fmap,Signed Int),adstat)
                    else rval ef
        in
          count_fncalls acc (E e1::E e2::es)
        end
      | UnOp(uop, e1) => let
        in
          case uop of
            Addr => count_fncalls (env,fmap,UnderAddr []) (E e1::RAS adstat :: es)
          | _ => count_fncalls (rval ef) (E e1::es)
        end
      | CondExp(e1,e2,e3) => let
          val acc =
              if adstat <> SzOf andalso
                 (eneeds_sc_protection e2 orelse eneeds_sc_protection e3)
              then let
                  val ty1 = cse_typing ctxt env e2
                  val ty2 = cse_typing ctxt env e3
                  val common = unify_types (ty1, ty2)
                      handle Fail _ =>
                             (Feedback.errorStr' ctxt (eleft e2,
                                                 eright e3,
                                                 "Types of conditional exp \
                                                 \branches (" ^ tyname ty1 ^
                                                 ", " ^ tyname ty2 ^
                                                 ") not compatible");
                              ty1)
                in
                  (env,inc(fmap,common),adstat)
                end
              else rval ef
        in
          count_fncalls acc (E e1::E e2::E e3::es)
        end
      | Constant _ => count_fncalls ef es
      | Var(s,vinfo_ref) => let
        in
          case find_scoped_vdecl ctxt s (get_scope env) of
            NONE => let
            in
              case Symtab.lookup (get_enumenv env) s of
                NONE => let
                in
                  case get_rettype s env of
                    NONE => (Feedback.errorStr' ctxt (eleft e, eright e,
                                                "Undeclared variable: "^s);
                             count_fncalls ef es)
                  | SOME retty => let
                      val ptys = map get_vtype (the (get_params s env))
                    in
                      vinfo_ref := SOME (Function(retty, ptys), FunctionName);
                      count_fncalls ef es
                    end
                end
              | SOME _ => (vinfo_ref := SOME (Signed Int, EnumC);
                           count_fncalls ef es)
            end
          | SOME (_, vi) => let
              val ty = get_vtype vi
              fun addifglob env (fm as (fmap, greads)) =
                  if is_global vi andalso adstat <> SzOf
                  then
                    if is_some fname
                    then (add_read (the fname) (M vi) env,
                          (fmap, Binaryset.add(greads, e)))
                    else (add_read "" (M vi) env, fm)
                  else (env, fm)
              val (env,fmap) =
                  case adstat of
                    Rvalue => if array_type ty then
                                (new_addressed vi e [] env, fmap)
                              else addifglob env fmap
                  | BL_Addr sels => if aggregate_type ty then (new_addressed vi e sels env, fmap)
                               else (env, fmap)
                  | UnderAddr sels => if function_type ty then (env, fmap)
                                 else (new_addressed vi e sels env, fmap)
                  | BrackLeft => if ptr_type ty andalso is_some fname then
                                   let
                                     val (env, fmap) = addifglob env fmap
                                   in
                                     (add_read (the fname) TheHeap env, fmap)
                                   end
                                 else addifglob env fmap
                  | BrackLeftLV => (env, fmap)
                  | Lvalue => (env, fmap)
                  | SzOf => (env, fmap)
              val (env, info) =
                  if function_type ty then (env, FunctionName)
                  else
                    (env,
                     MungedVar
                       { munge = get_mname vi,
                         owned_by = StmtDecl.get_owned_by (get_attrs vi),
                         fname = fname, init = the_default false (Option.mapPartial (get_init o snd) (!vinfo_ref))
                       })
            in
              vinfo_ref := SOME (ty, info);
              count_fncalls (env,fmap,adstat) es
            end
        end
      | StructDot(e1, field) =>
        let
          val ty = cse_typing ctxt env e
          val ty1 = cse_typing ctxt env e1
          val env = env |> maybe (add_variant field) (dest_union_type ty1)
        in
          if adstat = Rvalue andalso array_type ty then
            count_fncalls (env,fmap,UnderAddr []) (E e1::RAS adstat::es)
          else let
              val env =
                  if adstat = BrackLeft andalso ptr_type ty andalso
                     is_some fname
                  then add_read (the fname) TheHeap env
                  else env
            in
              count_fncalls (env, fmap, extend_selector (Field field) adstat) (E e1::es)
            end
        end
      | ArrayDeref(e1,e2) => let
          val ty = cse_typing ctxt env e
          val ty1 = cse_typing ctxt env e1
          val env = if ptr_type ty1 andalso is_some fname andalso
                       not (lvadstat adstat) andalso adstat <> SzOf
                    then
                      add_read (the fname) TheHeap env
                    else env
        in
          case adstat of
            UnderAddr sels => count_fncalls (env,fmap,extend_selector Array_Index (BL_Addr sels))
                                       (E e1::RAS Rvalue::E e2::RAS adstat::es)
          | Rvalue => let
            in
              if array_type ty then
                count_fncalls (env,fmap,BL_Addr [])
                              (E e1::RAS Rvalue::E e2::RAS adstat::es)
              else
                count_fncalls (env,fmap,BrackLeft) (E e1::RAS Rvalue::E e2::es)
            end
          | BrackLeft => count_fncalls (env,fmap,BrackLeft)
                                       (E e1::RAS Rvalue::E e2::es)
          | BL_Addr sels => count_fncalls (env,fmap,extend_selector Array_Index (BL_Addr sels))
                                     (E e1::RAS Rvalue::E e2::RAS adstat::es)
          | Lvalue => count_fncalls (env,fmap,BrackLeftLV)
                                    (E e1::RAS Rvalue::E e2::RAS Lvalue::es)
          | BrackLeftLV =>
            count_fncalls (env,fmap,BrackLeftLV)
                          (E e1::RAS Rvalue::E e2::RAS BrackLeftLV::es)
          | SzOf => count_fncalls (env,fmap,SzOf) (E e1::E e2::es)
        end
      | Deref e1 => let
          val env = if is_some fname andalso adstat <> Lvalue andalso
                       adstat <> SzOf
                    then
                      add_read (the fname) TheHeap env
                    else env
          val stat' = if adstat = SzOf then SzOf else Rvalue
          val ty = case cse_typing ctxt env e1 of
                       Ptr ty => ty
                     | ty as Array _ => ty
                     | ty => error ("unexpected type for Deref: " ^ @{make_string} ty)
          val env = add_addressed_type ty (get_selector adstat) env
        in
          count_fncalls (env,fmap,stat') (E e1::RAS adstat:: es)
        end
      | TypeCast(ty, e1) =>
          count_fncalls (process_type pex ctxt (left ty, right ty)
                                      (node ty) env,
                         fmap, Rvalue)
                        (E e1::es)
      | Sizeof e1 => count_fncalls (env,fmap,SzOf) (E e1::RAS adstat::es)
          (* sizeof expressions aren't evaluated - so ignore e1 *)
      | SizeofTy ty => count_fncalls (process_type pex ctxt (left ty, right ty)
                                                   (node ty) env, fmap,
                                      Rvalue) es
      | EFnCall(fn_e, args) => let
          val env = pex fn_e env
          
          val (callee, (rettyp, _)) = fndes_callinfo ctxt env fn_e
          val fmap = the_default fmap (dest_method_fun_ptr ctxt env fn_e |> Option.map (fn (fun_ptrT, fname) =>
                       inc(fmap, fun_ptrT)))
          val env = if adstat <> SzOf then
                      new_call ctxt {caller = fname_str fname, callee = callee, args = args} env
                    else env
          val env = if adstat <> SzOf then new_embedded_fncall callee env
                    else env
          val stat' = if adstat <> SzOf then Rvalue else SzOf
        in
          count_fncalls (env,inc(fmap,rettyp),stat')
                        (map E args @ es)
        end
      | CompLiteral (ty, dis) =>
          count_fncalls (process_type pex ctxt (eleft e, eright e) ty env,
                         fmap, adstat)
                        (inits_to_elist E (InitList dis) es)
      | Arbitrary ty =>
          count_fncalls (process_type pex ctxt (eleft e, eright e) ty env,
                         fmap, adstat)
                        es
      | OffsetOf (ty, _) => count_fncalls (process_type pex ctxt (left ty, right ty) (node ty) env, fmap, Rvalue) es
      | _ => eFail ctxt (e, "count_fncall: Can't handle expr type: "^
                             expr_string e)

  val (env', (counts, globalreads)) =
      count_fncalls (env, (TypeTab.empty, Binaryset.empty expr_ord),
                     if lvstate = LV then Lvalue else Rvalue)
                    [E e]
  fun foldthis (rettype,count) (acc : csenv) =
      if count <= 0 then acc
      else let
          val nm = tmp_var_name (tyname rettype, count)
          val retvar =
              Var_info {name = MString.dest nm, munged_name = nm, vtype = rettype,
                  struct_env = senv, proto_param = false,
                  fname = if is_some fname then fname else SOME "", return_var = true, attrs = [],
                  declared_at = Region.bogus, method_call_tmp_var = false}
        in
          foldthis (rettype, count - 1) (#2 (insert_var ctxt (retvar, acc)))
        end
in
  (TypeTab.fold foldthis counts env', globalreads)
end

fun get_modified ctxt env e = let
  (* e is an lvalue expression on the left of an assignment.  Return the
     base modified var_info for e if something in the global memory might be
     changing *)
  datatype s = BrackLeft | Normal
  fun recurse state e =
      case enode e of
        Var (s, Unsynchronized.ref (SOME (ty, MungedVar {munge = mnm, ...}))) => let
          fun check vi = srcname vi = s andalso get_mname vi = mnm
        in
          case find_scoped_vdecl ctxt s (get_scope env) of
            NONE => raise Fail ("Munged Variable "^s^", "^MString.dest mnm^
                                " not in environment")
          | SOME (_, vi) => let
              val isptr = case ty of Ptr _ => true | _ => false
            in
              if check vi then
                case (is_global vi, state = BrackLeft, isptr) of
                  (_, true, true) => SOME TheHeap
                | (true, _, _) => SOME (M vi)
                | _ => NONE
              else raise Fail ("Munged Variable "^s^", "^MString.dest mnm^
                               " not in environment")
            end
        end
      | Var (s, Unsynchronized.ref NONE) => let
          open Region
          val msg = toString (make {left = eleft e, right = eright e}) ^
                    "no info attached for variable " ^ s
        in
          raise Fail msg
        end
      | Var _ => NONE
      | StructDot (e', _) => let
        in
          case cse_typing ctxt env e of
            Ptr _ => if state = BrackLeft then SOME TheHeap
                     else recurse state e'
          | _ => recurse state e'
        end
      | ArrayDeref (e', _) => recurse BrackLeft e'
      | Deref _ => SOME TheHeap
      | TypeCast (_, e') => recurse state e'
      | _ => NONE
in
  recurse Normal e
end


fun fcall_retty_disagrees ctxt env fn_e args lvtyp = let
    val (_, (retty, _)) = fndes_callinfo ctxt env fn_e
  in lvtyp <> retty end

(* treat some problematic function calls as embedded. this detects whether the
   lvar is compound or type promotion would be required. either case would
   result in a nonstandard CALL element once translated. tweaking the function
   call into an embedded EFnCall causes it to be separated into an additional
   standard CALL statement later. *)
fun treat_as_emb_fcall ctxt env (NONE,fn_e,args) = false
  | treat_as_emb_fcall ctxt env (SOME lv,fn_e,args) = let
    val lvtyp = cse_typing ctxt env lv
    val lv_plain = case enode lv of Var _ => true | _ => false
  in not lv_plain orelse fcall_retty_disagrees ctxt env fn_e args lvtyp end

fun treat_ret_as_emb_fcall ctxt env (NONE,fn_e,args) = false
  | treat_ret_as_emb_fcall ctxt env (SOME retty,fn_e,args)
    = fcall_retty_disagrees ctxt env fn_e args retty

fun fold_pipe (f : 'env -> 'a -> 'b * 'env) (env0 : 'env) (items : 'a list) =
    let
      fun foldthis i (acc, env) = let
        val (i', env') = f env i
      in
        (i'::acc, env')
      end
      val (items0, env') = ([], env0) |> fold foldthis items
    in
      (List.rev items0, env')
    end


(* fname is a string option : NONE corresponds to a declaration at the global
   level *)
fun process_decl ctxt fname (d:declaration wrap) (e as Csenv {senv,...}) = let
  val ecenv = cse2ecenv ctxt e
  fun puredecl d = {decl = d, localinits = [], globalinits = []}
  fun pex e env = fst (process_expr ctxt RV fname env e)
in
  case node d of
    VarDecl (ty,s,storage_specs,iopt,attrs) => let
      val s = if node s = phantom_state_name then
                (Feedback.errorStr' ctxt
                     (left s, right s,
                      "Not allowed to use this as a variable name");
                 wrap(node s ^ "'", left s, right s))
              else s
      val str = node s
      val str = let
        val err =
            "You may not use \"" ^ str ^ "\" as a variable name; \
            \you might try turning on the \"allow_underscore_idents\"\n\
            \config variable to get around this error."
      in
        if get_allow_underscores e orelse check_uscore_ok str then str
        else (Feedback.errorStr' ctxt (left s, right s, err); str)
      end
      val is_extern = is_extern storage_specs
      val is_static = is_static storage_specs

      val _ = if is_static andalso is_extern then
                Feedback.errorStr' ctxt (left s, right s,
                                   "Var can't be declared static *and* extern")
              else ()
      val _ = if is_extern andalso is_some fname andalso is_some iopt then
                Feedback.errorStr' ctxt (left s, right s,
                                   "Can't initialise block-local extern")
              else ()
      val fname = if is_extern then NONE else fname

      val ty = fparam_norm ty
      val ty =
          (* calculate the size of an initialised incomplete array *)
          case ty of
            Array(elty, NONE) => let
            in
              case iopt of
                NONE => let
                in
                  case fname of
                    SOME fnm => if not is_extern then
                                  raise Fail ("Array "^str^" in function "^fnm^
                                              " must be given a size or an \
                                              \initialiser")
                                else ty
                  | NONE => ty
                end
              | SOME (InitE _) =>
                  raise Fail ("Array "^str^" initialised with non-constant "^
                              "expression")
              | SOME (InitList ilist) => let
                  val sz = complit.find_ilist_size ctxt ecenv ilist
                  val _ = if sz = 0 then
                            raise Fail "Array given empty initializer"
                          else ()
                in
                  Array(elty, SOME (expr_int (IntInf.fromInt sz)))
                end
            end
          | _ => ty
      val e = process_type pex ctxt (left d, right d) ty e
      val vty = constify_abtype true ctxt ecenv ty

      val (fname, munged_name) =
          if is_static andalso is_some fname then
            (NONE, mk_localstatic {fname = the fname, vname = str})
          else (fname, MString.mk str)
      val vi = Var_info {name = str, vtype = vty, attrs = attrs,
                   munged_name = munged_name, struct_env = senv,
                   proto_param = false,
                   fname = fname, return_var = false,
                   declared_at = Region.make{left = left s, right = right s},
                   method_call_tmp_var = false}
      val (vi, e) = insert_var ctxt (vi, e)
      (* inserting vi may force further munging if the name is already being
         used at a different type *)
      val munged_name = get_mname vi
      val bogus = SourcePos.bogus
      val mvinfo = MungedVar {munge = munged_name,
                              owned_by = StmtDecl.get_owned_by attrs, fname=fname, init=true}
      val var_e = ewrap(Var (str, Unsynchronized.ref (SOME (vty, mvinfo))), left s, right s)
      val (inits, proc_expr_opt, e) =
          case iopt of
            NONE => let
            in
              case fname of
                NONE => ([], NONE, e)
              | SOME _ => ([swrap(LocalInit var_e, left s, right s)],
                           NONE,
                           e)
            end
          | SOME (InitE exp) => let
              fun w s0 = swrap (s0, left s, eright exp)
            in
              case enode exp of
                EFnCall(e_fn,args) => let
                  val called =
                      case (enode e_fn, cse_typing ctxt e e_fn) of
                        (Var(s, _), Function _) => DirectCall s
                      | (_, ty) => let
                          val fty = case ty of
                                      Ptr (Function x) => x
                                    | Function x => x
                                    | _ => eFail ctxt (e_fn,
                                                        "Function designator\
                                                        \has bad type ("^
                                                        tyname ty^")")
                        in
                          FnPtrCall (fty, approx_expr ctxt e (enode e_fn), is_some (dest_method_fun_ptr ctxt e e_fn))
                        end
                  val e = new_call ctxt {caller = fname_str fname, callee = called, args=args} e
                  val () = case fname of
                            NONE =>
                              eFail ctxt (exp, "Can't initialise a global with a \
                                                \function call")
                          | SOME _ => ()
                in
                  ([w (AssignFnCall(SOME var_e, e_fn, args))],
                   let
                     fun foldthis e acc = ebogwrap(BinOp(Plus,e,acc))
                   in
                     SOME (e_fn |> fold foldthis args)
                   end,
                   e)
                end
              | _ => let
                  val e = case fname of
                            NONE => map_globinits (MSymTab.update (munged_name, exp)) e
                          | _ => e
                in
                  ([w (Assign(var_e, exp))], SOME exp, pex exp e)
                end
            end
          | SOME (InitList ilist) => let
              fun w s0 = swrap (s0, left s, bogus)
              val exp = ewrap(CompLiteral(ty, ilist), bogus, bogus)
              val e =
                  case fname of
                    NONE => map_globinits (MSymTab.update (munged_name, exp)) e
                  | _ => e
            in
              ([w (Assign(var_e, exp))], SOME exp, e)
            end
      val d' = wrap(VarDecl(ty,s,storage_specs,NONE,attrs), left d, right d)
      val e =
          case proc_expr_opt of
              NONE => e
            | SOME exp => #1 (process_expr ctxt RV fname e exp)
                          (* ignore global reads done by initialiser *)
      val (globalinits, localinits) =
          case fname of
              NONE => (inits, [])
            | SOME _ => ([], inits)
    in
      ({decl = d', localinits = localinits, globalinits = globalinits}, e)
    end
  | StructDecl s => (puredecl d, newstr_decl pex ctxt Struct s e)
  | UnionDecl u => (puredecl d, newstr_decl pex ctxt (Union []) u e)
  | TypeDecl _ => raise Fail "collect_vars: TypeDecl unexpected, \
                             \translate these out!"
  | ExtFnDecl {rettype = rettype0,name = fname0,params,specs,...} => let
      val _ = if get_allow_underscores e orelse check_uscore_ok (node fname0)
              then ()
              else Feedback.errorStr' ctxt (left fname0, right fname0,
                                      rmUScoreSafety (node fname0) ^
                                      " is an illegal name for a function")
      val e = e |> fold (process_type pex ctxt (left d, right d))
                     (rettype0 :: map #1 params)
      val rettype = fparam_norm (constify_abtype true ctxt ecenv rettype0)
      val fname = node fname0
      val e = insert_fnretty ctxt (fname0, rettype, e)
      val ret_vname = return_var_name
      fun do_ret e =
          if rettype = Void then e
          else let
              val retvar = Var_info {name = MString.dest ret_vname,
                               munged_name = ret_vname,
                               vtype = rettype, proto_param = false,
                               struct_env = senv,
                               fname = SOME fname, return_var = true,
                               attrs = [], declared_at = Region.bogus, method_call_tmp_var = false}
            in
              #2 (insert_var ctxt (retvar, e))
            end
      fun to_vi (i, (ty,pnameopt)) (acc, e) = let
        val name = case pnameopt of
                     NONE => fake_param fname i
                   | SOME s => s
        val var =
            Var_info {name = name, vtype = param_norm (constify_abtype true ctxt ecenv ty),
                munged_name = MString.mk name, attrs = [],
                struct_env = senv, proto_param = true,
                fname = SOME fname, return_var = false,
                declared_at = Region.bogus, method_call_tmp_var = false}
        val (var',e') = insert_var ctxt (var, e)
      in
        (var'::acc, e')
      end
      val paramtypes = map (param_norm o constify_abtype true ctxt ecenv o #1) params
      val ftype = Function(rettype, paramtypes)
      val fvi = Var_info {name = fname, vtype = ftype, munged_name = MString.mk fname,
                    proto_param = false, struct_env = senv,
                    fname = NONE, return_var = false, attrs = [],
                    declared_at = Region.Wrap.region d, method_call_tmp_var = false}
      val (_, e) = insert_var ctxt (fvi, e)
      val e = do_ret (new_scope e)
      val (pm_vis0, e) = fold_index to_vi params ([], e)
      val e = (* check for modifies assertions *)
          case List.find (fn fn_modifies _ => true | _ => false) specs of
            NONE => e
          | SOME (fn_modifies slist) => let
              fun doit varname e =
                  case Symtab.lookup (get_vars e) varname of
                    NONE => let
                    in
                      if varname = phantom_state_name then
                        add_modification fname PhantomState e
                      else if varname = ghost_state_name then
                        add_modification fname GhostState e
                      else if varname = global_heap then
                        add_modification fname TheHeap e
                      else
                        (Feedback.errorStr' ctxt (left fname0, right fname0,
                                            "MODIFIES spec for function "^fname^
                                            " mentions non-existent variable "^
                                            varname);
                         e)
                    end
                  | SOME vis => let
                    in
                      case List.find is_global vis of
                        NONE =>
                        (Feedback.errorStr' ctxt (left fname0, right fname0,
                                            "MODIFIES spec for function "^fname^
                                            " mentions non-global variable "^
                                            varname); e)
                      | SOME vi => add_modification fname (M vi) e
                    end
            in
              if null slist then
                map_modifies
                    (Symtab.update (fname, Binaryset.empty mvar_compare))
                    e
              else e |> fold doit slist
            end
          | SOME _ => e (* can't happen, but here to squish compiler warning *)
      val e = (* add fnspecs *) let
        fun U s1 s2 = merge_specs s1 s2
      in
        map_fnspecs (Symtab.map_default (fname, []) (U specs)) e
      end
      val e = update_hpfninfo (Decl d) e
    in
      (puredecl d, pop_scope (set_proto_params fname (List.rev pm_vis0) e))
    end
  | EnumDecl eninfo => (puredecl d, process_enumdecl ctxt eninfo e)
end

type asm_stmt_elements = (string * bool * expr option * expr list)

fun split_asm_stmt (AsmStmt dets) = let
  open Feedback
  val rets = #mod1 (#asmblock dets)
  fun str_so NONE = "NONE" | str_so (SOME s) = "SOME (" ^ s ^ ")"
  fun str_trio (so, s, _) = "(" ^ str_so so ^ ", " ^ s ^ ")"
  val _ = List.app (K () o (fn (so, s, ex) =>
    (s = "=r" orelse s = "=&r")
    orelse raise Fail ("Can not handle asm lval specifier: "
            ^ str_trio (so, s, ex)))) rets
  fun str_trios [] = ""
    | str_trios [tr] = str_trio tr
    | str_trios (tr :: trs) = str_trio tr ^ ", " ^ str_trios trs
  val _ = K () (length rets <= 1
    orelse raise Fail ("Can not handle multiple asm lval specifiers: ["
            ^ str_trios rets ^ "]"))
  val ret = case rets of [] => NONE | [(_, _, r)] => SOME r
    | _ => NONE
  val args = #mod2 (#asmblock dets)
  val _ = List.app (K () o (fn (so, s, ex) =>
    (* fixme: have different asm specifier whitelists per arch. *)
    (s = "r" orelse s = "i" orelse s = "rK")
    orelse raise Fail ("Can not handle asm rval specifier: "
            ^ str_trio (so, s, ex)))) args
  val args = map #3 args
in
  (#head (#asmblock dets), #volatilep dets, ret, args)
end
  | split_asm_stmt st = raise Fail
    ("split_asm_stmt: " ^ stmt_type (sbogwrap st))

fun merge_asm_stmt (nm, vol, ret, args) = let
in
  AsmStmt {volatilep = vol, asmblock = {head = nm,
    mod1 = (case ret of NONE => [] | SOME expr => [(NONE, "=r", expr)]),
    mod2 = map (fn expr => (NONE, "r", expr)) args,
    mod3 = []}}
end

fun process_blockitem ctxt fname e bi = let
in
  case bi of
    BI_Stmt s => apfst (map BI_Stmt) (process_stmt ctxt fname e s)
  | BI_Decl d =>
    let
      val ({decl,localinits,globalinits}, e') = process_decl ctxt (SOME fname) d e
      (* process the new local inits in the process_stmt sense.
         process_decl already did most of the work, but this is the best
         opportunity to treat problematic function calls as embedded
         (see treat_as_emb_fcall) *)
      val (stmts, e'') = fold_pipe (process_stmt ctxt fname) e' localinits
    in
      (* throw away globalinits for the moment *)
      (BI_Decl decl :: map BI_Stmt (List.concat stmts), e'')
    end
end
and process_stmt ctxt fname e (stmt : statement) = let
  fun pex e exp = process_expr ctxt RV (SOME fname) e exp
  fun pexlv e exp = process_expr ctxt LV (SOME fname) e exp
  fun pst e st = process_stmt ctxt fname e st
  fun pbil e blist = process_blockitems ctxt fname e blist
  fun w s0 = swrap(s0, sleft stmt, sright stmt)
  val retty = get_rettype fname e
  fun lift_stmts stmts =
      case stmts of
          [] => w EmptyStmt
        | [s] => s
        | _ => w(Block (map BI_Stmt stmts))
  val owners = get_owners e
  val mk_chaos_stmts =
      if null owners then fn _ => []
      else
        fn grs =>
           let
             fun foldthis (e, acc) =
                 case enode e of
                     Var(nm, Unsynchronized.ref (SOME (_, MungedVar {owned_by = NONE,...}))) =>
                     (Feedback.informStr' ctxt (5, sleft stmt, sright stmt,
                                          "Found that "^nm^" is not owned.");
                      w (Chaos e) :: acc)
                   | _ => acc
           in
             Binaryset.foldl foldthis [] grs
           end
  fun prechaos grs stmts = mk_chaos_stmts grs @ stmts
in
  case snode stmt of
    While(g, i, s) => let
      val (e,grs) = pex e g
      val cstmts = mk_chaos_stmts grs
      val (s', e) = pst e s
    in
      (cstmts @ [w (While(g,i,lift_stmts (s' @ cstmts)))], e)
    end
  | Trap(traptype, s) => let
      val (s',e) = pst e s
    in
      ([w (Trap(traptype, lift_stmts s'))], e)
    end
  | LabeledStmt(l, s) => let
      val (s',e) = pst e s
    in
      ([w (LabeledStmt(l, lift_stmts s'))], e)
    end
  | IfStmt(g,s1,s2) => let
      val (e, grs) = pex e g
      val (s1',e) = pst e s1
      val (s2',e) = pst e s2
    in
      (prechaos grs [w (IfStmt(g,lift_stmts s1',lift_stmts s2'))], e)
    end
  | Block b =>
      apfst (single o w o Block) (apsnd pop_scope (pbil (new_scope e) b))
  | Chaos lv_expr =>
    let
      val (e,grs) = pexlv e lv_expr
      val modified = get_modified ctxt e lv_expr
      val e =
          case modified of
              NONE => e
            | SOME m => add_modification fname m e
    in
      (prechaos grs [stmt], e)
    end
  | Switch(g,cases) => let
      (* deal with guard *)
      val (e, grs) = apfst new_scope (pex e g)
      fun label_fold NONE env = env
        | label_fold (SOME exp) env = #1 (pex env exp)
            (* should be no global reads in a case label *)
      fun one_case e (eoptlist, bis) = let
        val e = e |> fold label_fold eoptlist
      in
        apfst (fn y => (eoptlist,y)) (pbil e bis)
      end
    in
      apfst (fn cs => prechaos grs [w (Switch(g,cs))])
            (apsnd pop_scope (fold_pipe one_case e cases))
    end
  | Assign(e1,e2) =>
    let
      val _ = if CType.fun_ptr_type (cse_typing ctxt e e1)
        then Feedback.errorStr' ctxt (sleft stmt, sright stmt, "assignment to function pointer not supported")
        else ();

      val (e, grs1) = pexlv e e1
      val (e, grs2) = pex e e2
      val grs = Binaryset.union(grs1,grs2)
      val modified = get_modified ctxt e e1
      val e =
          case modified of
            NONE => e
          | SOME m => add_modification fname m e
    in
      (prechaos grs [stmt], e)
    end
  | AssignFnCall(eopt,fn_e,args) => let in
      if treat_as_emb_fcall ctxt e (eopt,fn_e,args)
      then let
        val lv = case eopt of SOME lv => lv
          | NONE => raise Fail "Trying to embed fcall without lval."
      in pst e (w (Assign(lv,ebogwrap (EFnCall(fn_e,args))))) end
      else let
       (* val _ (* for the side effect to fill reference to var_info for fndes_callinfo *) = pex e fn_e *)

        val (e,grs1) =
            case eopt of
                NONE => (e,Binaryset.empty expr_ord)
              | SOME exp => let
                    val (e,grs) = pexlv e exp
                  in
                    case get_modified ctxt e exp of
                      NONE => (e,grs)
                    | SOME m => (add_modification fname m e, grs)
                  end
        val (e,grs2) = pex e
          (fn_e |> fold (fn a => fn exp => ebogwrap (BinOp(Plus,a,exp))) args)
        val grs = Binaryset.union(grs1,grs2)
        val (callee, _) = fndes_callinfo ctxt e fn_e
        (* the arguments need to be considered as being part of one big
           expression (rather than independently) in order for the
           embedded function call analysis to work, so we create one fake
           expression embodying them all to be analysed by pex *)
        val e = new_call ctxt {caller = fname, callee = callee, args = args} e
        val e = tmp_method_fun_ptr ctxt fn_e e
      in
        (prechaos grs [stmt], e)
      end
    end
  | Return NONE => let
    in
      case retty of
        NONE => ([stmt], e) (* probably really an error *)
      | SOME Void => ([stmt], e)
      | _ => raise stmt_fail (stmt, "Null-return in function with return-type")
    end
  | Return (SOME ex) => let
    in
      case retty of
        NONE => raise stmt_fail (stmt, "Returning a value in a void function")
      | SOME ty => let
          val etyp = cse_typing ctxt e ex
        in
          if ExpressionTyping.assignment_compatible (ty, etyp, ex) then
            let
              val (e,grs) = pex e ex
            in
              (prechaos grs [stmt], e)
            end
          else
            raise stmt_fail (stmt,
                             "Type of returned expression ("^tyname etyp^
                             ") incompatible with that of containing function ("^
                             tyname ty^")")
        end
    end
  | ReturnFnCall(fn_e, args) => let in
      if treat_ret_as_emb_fcall ctxt e (retty,fn_e,args)
      then pst e (w (Return (SOME (ebogwrap (EFnCall(fn_e,args))))))
      else let
        val (e, grs) = pex e (fn_e |> fold (fn e => fn acc => ebogwrap(BinOp(Plus,e,acc))) args)
        val (callee, _) = fndes_callinfo ctxt e fn_e
        val e = new_call ctxt {caller = fname, callee = callee, args = args} e
        val e = tmp_method_fun_ptr ctxt fn_e e
      in
        (prechaos grs [stmt], e)
      end
    end
  | AsmStmt {asmblock = {mod1,mod2,...}, ...} =>
    let
      fun handle_mod ((_,_,exp) : namedstringexp) (e0, grs0) =
        let
          val (e,newgrs) = pex e0 exp
        in
          (e,Binaryset.union(newgrs,grs0))
        end
      val (e,grs) = (e, Binaryset.empty expr_ord) |> fold handle_mod mod1
      val (e,grs) = (e, grs) |> fold handle_mod mod2
    in
      (prechaos grs [stmt],
       fold (add_modification fname) [TheHeap, PhantomState, AllGlobals] e)
    end
  | Ghostupd _ => ([stmt], add_modification fname GhostState e)
  | Auxupd _ => ([stmt], add_modification fname TheHeap e)
  | _ => ([stmt], e)
end
and process_blockitems ctxt (fname : string) (env : csenv) bis =
    apfst List.concat (fold_pipe (process_blockitem ctxt fname) env bis)

fun delete_earlier_fvars fname env = let
  fun vitest (Var_info vinfo) =
      #fname vinfo <> SOME fname orelse
      #return_var vinfo
  fun allvars_upd (vname,vlist) newtab =
      case List.filter vitest vlist of
        [] => newtab
      | x => Symtab.update (vname, x) newtab
  fun scope_upd (vname, vi) newtab =
      if vitest vi then Symtab.update (vname, vi) newtab
      else newtab
  fun allvarupd tab = Symtab.fold allvars_upd tab Symtab.empty
  val scopes_upd = map (fn tab => Symtab.fold scope_upd tab Symtab.empty)
in
  (map_scope scopes_upd o map_vars allvarupd) env
end

fun split_decls (ds, is) bis =
    case bis of
      [] => (List.rev ds, List.rev is)
    | BI_Stmt s :: rest => split_decls (ds, s :: is) rest
    | BI_Decl d :: rest => split_decls (Decl d :: ds, is) rest


fun process_one_extdecl ctxt (env0 : csenv) edec =
    case edec of
      Decl d => let
        val ({decl, localinits, globalinits}, e) = process_decl ctxt NONE d env0
      in
        (([Decl decl], globalinits), e)
      end
    | FnDefn((rettype0, s), params, specs, body) => let
        val _ =
            if get_allow_underscores env0 orelse check_uscore_ok (node s) then ()
                else Feedback.errorStr' ctxt (left s, right s,
                                        rmUScoreSafety (node s) ^
                                        " is an illegal name for a function")
        val _ =
            case get_fun_modifies env0 (node s) of
              NONE => ()
            | SOME _ => Feedback.warnStr' ctxt
                            (left s, right s,
                             "Ignoring previous MODIFIES spec for function "^
                             node s)
        val ecenv = cse2ecenv ctxt env0
        val rettype = fparam_norm (constify_abtype true ctxt ecenv rettype0)
        val fname = SOME (node s)
        val senv = get_senv env0
        val env = delete_earlier_fvars (node s)
                                       (insert_fnretty ctxt (s,rettype, env0))
        val env = new_defined_fn s env
        val rv_nm = return_var_name
        val retvar =
            Var_info {name = MString.dest rv_nm, munged_name = rv_nm, attrs = [],
                vtype = rettype, proto_param = false,
                struct_env = senv,
                fname = SOME (node s), return_var = true,
                declared_at = Region.bogus, 
                method_call_tmp_var = false}
        val paramtypes = map (param_norm o constify_abtype true ctxt ecenv o #1) params
        val ftype = Function(rettype, paramtypes)
        val fvi = Var_info {name = node s, vtype = ftype,
                      munged_name = MString.mk (node s),
                      proto_param = false, struct_env = senv,
                      fname = NONE, return_var = false, attrs = [],
                      declared_at = Region.Wrap.region s, 
                      method_call_tmp_var = false}
        val (_, env) = insert_var ctxt (fvi,env)
        fun to_vi (ty,pname) =
            Var_info{name = node pname,
               munged_name = MString.mk (node pname),
               attrs = [],
               vtype = param_norm (constify_abtype true ctxt ecenv ty),
               struct_env = senv, proto_param = false,
               fname = fname, return_var = false,
               declared_at =
                 Region.make{left = left pname, right = right pname}, 
               method_call_tmp_var = false}
        val env = new_scope env (* new scope for parameters and body *)
        val (params0,env) = let
          fun foldthis p (accps, env) = let
            val (vi,env) = insert_var ctxt (to_vi p, env)
          in
            (vi::accps, env)
          end
        in
          ([], env) |> fold foldthis params
        end
        val env = set_defn_params (node s) (List.rev params0) env
        val env = if rettype <> Void then #2 (insert_var ctxt (retvar, env))
                  else env
        val (body0, env) = process_blockitems ctxt (node s) env (node body)
        val body' = wrap (body0, left body, right body)
        val env = (* add fnspecs *) let
          val U = merge_specs
        in
          map_fnspecs (Symtab.map_default (node s, []) (U specs)) env
        end
        val env = pop_scope env
      in
        (([FnDefn((rettype0, s), params, specs, body')], []), env)
      end

fun gen_compute_callgraphs excludes ctxt env = let
  fun add fname s = if member (op =) excludes fname then s else Binaryset.add(s, fname)

  val (callgraph, converse) = let
    fun setfoldthis caller (fncall, acc) =
        case fncall of
          DirectCall nm => add nm acc
        | FnPtrCall (fty, potential_callees,_) =>
           let
             val callees_via_global_consts = potential_callees
               |> map_filter (fn (n, r) => case !r of SOME (_, FunctionName) => SOME n | _ => NONE)
           in
             Binaryset.addList(acc, callees_via_global_consts)
           end
    fun foldthis (fname, called) (callgraph,converse) = let
      val called' = Binaryset.foldl (setfoldthis fname)
                                    (Binaryset.empty string_ord)
                                    called
      val cg' = Symtab.update (fname, called') callgraph
      fun setfold (callee, acc) =
          Symtab.map_default (callee, Binaryset.empty string_ord)
                             (add fname)
                             acc
      val conv' = Binaryset.foldl setfold converse called'
    in
      (cg',conv')
    end

   val initial_callgraph = get_callgraph env

  in
    Symtab.fold foldthis initial_callgraph (Symtab.empty, Symtab.empty)
  end
in
  {callees = callgraph, callers = converse}
end

val compute_callgraphs = gen_compute_callgraphs [NameGeneration.exitN]
val compute_callgraphs_with_exit = gen_compute_callgraphs []

fun has_addressable_variables cse fname =
  let
    fun key vi = (get_mname vi, SOME fname)
    val addressed = get_addressed cse
  in
    get_variables cse (SOME fname) |> exists (XMSymTab.defined addressed o key)
  end

fun mvar_traverse ctxt env = let
  val fnames = get_functions env
  val defined_fns = Symtab.keys (get_defined_functions env)
  val empty_sset = Binaryset.empty string_ord
  val empty_mvset = Binaryset.empty mvar_compare
  (* first set all modifies entries for defined functions to be the empty set
     (if they don't already have a value) *)
  val env = let
    fun foldthis f tab = Symtab.map_default (f, empty_mvset) I tab
    fun updtab tab = tab |> fold foldthis defined_fns
  in
    (map_modifies updtab o map_read_globals updtab) env
  end
  val env = env |> map_modifies (Symtab.map (fn fname => fn mods => 
     if has_addressable_variables env fname then Binaryset.add (mods, TheHeap) else mods))
  fun mv_munge mvi =
      case mvi of
        M vi => let
        in
          case XMSymTab.lookup (get_addressed env) (get_mname vi, NONE) of
            NONE => mvi
          | SOME _ => TheHeap
        end
      | _ => mvi

  fun map_mungeset _ set = let
    fun foldthis (mvi, set) = Binaryset.add(set, mv_munge mvi)
  in
    Binaryset.foldl foldthis empty_mvset set
  end
  val env = (map_modifies (Symtab.map map_mungeset) o
             map_read_globals (Symtab.map map_mungeset)) env

  fun lift f fnm = case Symtab.lookup f fnm of
                     NONE => []
                   | SOME s => Binaryset.listItems s
  val {callees,callers} = compute_callgraphs ctxt env

  val sorted = Topo_Sort.topo_sort {cmp = string_ord,
                                    graph = lift callees,
                                    converse = lift callers}
                                   fnames
  fun remove x env = env
    |> map_modifies (Symtab.delete_safe x)
    |> map_read_globals (Symtab.delete_safe x)
  nonfix union
  fun process fnlist env =
      case fnlist of
        [] => raise Fail "topological sort produced empty component??"
      | [x] => let
          val callees = lift callees x
          val env = if member (op =) callees x then mk_recursive x env else env
          fun do_callees (callees, acc) =
              case callees of
                [] => acc
              | c::cs => let
                  fun union s1 s2 = Binaryset.union (s1, s2)
                in
                  case get_fun_modifies acc c of
                    NONE => remove x acc
                  | SOME modset => let
                      fun upd set = Symtab.map_entry x (union set)
                      val acc = map_modifies (upd modset) acc
                      val reads_db = get_read_globals acc
                    in
                      case Symtab.lookup reads_db c of
                        NONE => let
                          val fspecs =
                              the (Symtab.lookup (function_specs env) c)
                              handle Option => []
                          val acc =
                              if is_some
                                 (Absyn.has_IDattribute (fn s => s = "noreturn")
                                                        fspecs)
                              then acc
                              else
                                map_read_globals (Symtab.delete_safe x) acc
                        in
                          do_callees (cs, acc)
                        end
                      | SOME rset => let
                          val acc = map_read_globals (upd rset) acc
                        in
                          do_callees (cs, acc)
                        end
                    end
                end
        in
          case get_fun_modifies env x of
            NONE => env
          | SOME _ => if has_fun_ptr_calls env x then remove x env else do_callees (callees, env)
        end
      | _ => let
          (* we know that these functions form a strongly connected component
             in the call graph, so each will have modifies data. *)
          open Binaryset
          val all_callees = let  (* will include elements of fnlist *)
            fun foldthis nm acc =
                case Symtab.lookup callees nm of
                  NONE => acc
                | SOME set => union (acc, set)
          in
            empty_sset |> fold foldthis fnlist
          end
          val read_db = get_read_globals env
          fun do_callees (callees, acc as (mods,reads)) =
              case callees of
                [] => acc
              | c::cs => let
                  fun updmods ms =
                      case get_fun_modifies env c of
                        NONE => NONE
                      | SOME modset => SOME (union (ms, modset))
                  fun updreads rs =
                      case Symtab.lookup read_db c of
                        NONE => let
                          val fspecs =
                              the (Symtab.lookup (function_specs env) c)
                              handle Option => []
                        in
                          if is_some
                                 (Absyn.has_IDattribute (fn s => s = "noreturn")
                                                        fspecs)
                          then
                            SOME rs
                          else NONE
                        end
                      | SOME rset => SOME (union (rs, rset))
                  fun omj _ NONE = NONE
                    | omj f (SOME x) = (case f x of NONE => NONE | y => y)
                  val acc = (omj updmods mods, omj updreads reads)
                in
                  do_callees (cs, acc)
                end
          val (ms,rs) = if exists (has_fun_ptr_calls env) fnlist then (NONE, NONE)
                        else do_callees (listItems all_callees,
                                    (SOME empty_mvset, SOME empty_mvset))
          fun del f csemod = csemod (Symtab.delete f)
          fun ins f csemod s = csemod (Symtab.update (f,s))
          fun update_at f cmod setopt =
              case setopt of
                NONE => del f cmod
              | SOME s => ins f cmod s
          fun foldthis f env =
              env |> mk_recursive f
                  |> update_at f map_modifies ms
                  |> update_at f map_read_globals rs
        in
          env |> fold foldthis fnlist
        end
in
  env |> fold process sorted
end

fun used_types filter cse =
  let
    fun mk_set ts = Binaryset.addList (Binaryset.empty (ctype_ord int_ord), ts)
    val var_types =
      get_vars cse |> Symtab.dest |> filter |> map snd |> flat |> map get_vtype |> mk_set
    fun step_type senv ty =
      case ty of
        StructTy s =>
        (case AList.lookup (op =) senv s of
          SOME (Struct, flds, _, _) => map (#1 o #2) flds
         | _ => error ("step_type: structure '" ^ s ^ "' not found"))
      | UnionTy s  =>
        (case AList.lookup (op =) senv s of
          SOME (Union active, flds, _, _) => map (#1 o #2) (CType.active_variants s active flds) (* (CType.single_variant s active flds) *) (* FIXME: remove *)
         | _ => error ("step_type: union '" ^ s ^ "' not found"))
      | Ptr ty => [ty]
      | Function (ret, pars) => ret::pars
      | Array (ty, _) => [ty]
      | _ => []
    val structs_and_unions = get_senv cse
    val used_types = Binaryset.closure (mk_set o step_type structs_and_unions) var_types
  in
    used_types
  end

fun used_types_of_fun cse n =
  let
     val read_globals = case Symtab.lookup (get_read_globals cse) n of NONE => []
       | SOME s => Binaryset.listItems s |> map string_of_mvar
     fun relevant_vars (x, infos) =
       let
         val relevant_infos = filter (fn info => case get_fname info of
             SOME m => n = m andalso get_name info <> n
           | NONE => member (op =) read_globals x) infos
      in
        if null relevant_infos then NONE else SOME (x, relevant_infos)
      end
  in
    used_types (map_filter relevant_vars) cse
  end

fun used_fun_types_of_fun cse n =
  used_types_of_fun cse n |> Binaryset.listItems |> filter (function_type)

fun get_functions_used_as_fun_ptr_params cse =
  let
    fun is_fun (n, r) = case !r of SOME (_, FunctionName) => SOME n | _ => NONE
  in
    get_fun_ptr_params cse |> Symtab.dest
    |> map (map_filter (is_fun) o flat o map_filter I o snd)
    |> flat |> distinct (op =)
  end


local

fun is_non_proto cse name =
  case (Symtab.lookup (get_fninfo cse) name |> Option.map #2) of
    NONE => false
  | SOME is_proto => not is_proto
in
fun get_referenced_funs_global cse =
   these (Symtab.lookup (get_referenced_funs cse) "") |> filter (is_non_proto cse)

fun get_all_referenced_funs cse =
   (Symtab.dest (get_referenced_funs cse) ) |> map snd |> flat |> distinct (op =) |> filter (is_non_proto cse)

fun get_referenced_funs_via_const_globals cse fname  =
  let
    val infos = get_constant_global_fun_ptrs cse;
    val globs = map fst infos;
    val relevant_globs = Symtab.lookup (get_read_globals cse) fname |> the_list
      |> map Binaryset.listItems |> flat |> map string_of_mvar |> filter (member (op =) globs);
    val fun_ptrs = map (AList.lookup (op =) infos #> these) relevant_globs |> flat |> distinct (op =);
  in
    fun_ptrs |> filter (is_non_proto cse)
  end

fun get_functions_used_via_fun_ptr cse =
  let
    val glob_fun_ptr = get_constant_global_fun_ptrs cse
      |> map snd |> flat |> filter (is_non_proto cse)
  in
    get_functions_used_as_fun_ptr_params cse @ glob_fun_ptr |> distinct (op =)
  end
end

fun get_clique cse fname =
  let
    val cliques = get_cliques cse
  in
    find_first (fn clique => member (op =) clique fname) cliques
  end

fun get_other_fun_ptr_dependencies cse fname =
 let
   val fun_ptr_callees = get_fun_ptr_callees cse fname
   val referenced_funs = Symtab.lookup (get_referenced_funs cse) fname |> these
   val direct_callees = get_direct_callees cse fname
   val clique = get_clique cse fname |> these
 in
   fun_ptr_callees @ referenced_funs
   |> filter_out (member (op =) (direct_callees @ clique)) |> sort_distinct fast_string_ord
 end

fun get_all_other_fun_ptr_dependencies cse =
  map (get_other_fun_ptr_dependencies cse) (get_functions cse) |> flat |> sort_distinct fast_string_ord

fun get_all_addressed_funs cse =
  get_referenced_funs_global cse @ get_all_other_fun_ptr_dependencies cse |> sort_distinct fast_string_ord

fun get_indirect_fun_ptr_dependencies cse fname =
 let
   val fun_ptr_callees = get_fun_ptr_callees cse fname
   val referenced_funs = Symtab.lookup (get_referenced_funs cse) fname |> these
   val direct_callees = get_direct_callees cse fname
 in
   fun_ptr_callees @ referenced_funs
   |> filter_out (member (op =) (direct_callees)) |> distinct (op =)
 end

fun get_global_addressed cse = get_addressed cse |> XMSymTab.dest
  |> map_filter (fn ((n, NONE), x) => SOME (n, x) | _ => NONE)

fun get_addressed_globals cse fname =
 let
   fun relevant_var ((n, NONE), infos) =
    let
     val fns = infos |> map (Expr.fun_of_var_expr o fst)
    in if exists (fn SOME fname' => fname' = fname | _ => false) fns then SOME (MString.dest n) else NONE end
     | relevant_var _ = NONE
 in
   get_addressed cse |> XMSymTab.dest |> map_filter relevant_var
 end

fun uses_globals cse fname =
  let
    val reads_globals = (SOME false = (Option.map (Binaryset.isEmpty) (Symtab.lookup (get_read_globals cse) fname)))
    val writes_globals = (not (null (get_fun_modifies_globals cse fname)))
    val addresses_globals = not (null (get_addressed_globals cse fname))
  in
    reads_globals orelse writes_globals orelse addresses_globals
  end

fun get_globals_rcd cse =
let
  val advis = get_addressed_vis NONE cse
in
  if null advis then []
  else
    [(adglob_rcd_tyname, (Struct, map (fn vi => (srcname vi, (get_vtype vi, []))) advis, Region.bogus, []))]
end

val is_addressed = XMSymTab.defined o get_addressed

fun get_final_callers cse fname =
  let
    val emp =  Binaryset.empty string_ord
    val init = Binaryset.singleton string_ord fname
    val callers = #callers (get_final_callgraph cse)
    fun step f = the_default emp (Symtab.lookup callers f)
    val all = Binaryset.closure step init
  in
    Binaryset.listItems all
  end


fun callers_with_addressable_variables cse fname =
  let
    val callers = get_final_callers cse fname
  in
    callers |> filter (has_addressable_variables cse)
  end

val compress_fun_ptr_params =
  Symtab.map (fn _ => fn params => map (Option.map (distinct (op =))) params)

fun mvar_finalise env = let
    open Binaryset
    val (Csenv {modifies, ...}) = env
    val un = Binaryset.union

    fun mk xs = addList (empty mvar_compare, xs)

    val addressed = get_addressed_vis NONE env
        |> map M |> mk

    val all_modified = get_modified_global_locns env
        |> MVar_Table.dest
        |> List.filter (fn (_, mset) => not (isEmpty mset))
        |> map (fn (m, _) => m)
        |> List.filter (fn M v => true | _ => false)
        |> mk

    val mod_not_addr = difference (all_modified, addressed)

    fun upd modif = if member (modif, AllGlobals)
      then delete (un (mod_not_addr, modif), AllGlobals)
      else modif
  in
    env
    |> map_modifies (Symtab.map (K upd))
    |> map_usedtypes (K (used_types I env))
  end


exception Check of string

fun check_packed cse align size ty =
 let
   val (sz, padding_ty) = sizeof_padding cse ty
   val res = sz mod align = 0
   val _ = if res then
             if padding_ty then
               raise Check ("type " ^ @{make_string} ty ^ " is not packed")
             else if sz <> size then
               raise Check ("all variants of union must have same size: " ^ @{make_string} size ^  
                 "\n Type " ^ @{make_string} ty ^ " has size " ^ @{make_string} sz ^ " not " ^ @{make_string} size)
             else ()
           else 
             raise Check ("size of type " ^ @{make_string} ty ^ " is " ^ @{make_string} sz ^ 
             ", which is not a multiple of alignment " ^  @{make_string} align)

 in
   ()
 end

fun used_union_variants ctxt cse (usedtypes: int ctype Binaryset.set) (senv: senv) = 
  let
    fun expand (entry as (nm, (Struct, flds, reg, attrs))) = []
      | expand (entry as (nm, (Union active, variants, reg, attrs))) = 
         let 
            val union_align = alignof cse (UnionTy nm)
            val union_size = sizeof cse (UnionTy nm)
            val align_attr = AlignedExponent (IntInf.log2 union_align)
            fun check fld_name ty = 
              let 
              in
                check_packed cse union_align union_size ty 
                handle Check str =>
                   Feedback.error_region ctxt reg ("union " ^ quote nm ^ " has a non-packed variant: " ^ quote fld_name ^ 
                     ":\n " ^ str)
              end
         in
         (if length active > 1 andalso Binaryset.member (usedtypes, UnionTy nm) then
            (* First active variant is considered to be the canonical type representing the union;
             * It gets the same name as the union and thus "overrides" the entry for the union when preparing
             * all records for the 'recursive record package' definitions, cf. Calculate_State.get_sorted_structs *)
            [(nm, map_index (fn (i, (variant_name, fld as (ty, _))) => 
                            let val _ = check variant_name ty
                            in (variant_name, [(nm ^ (if i = 0 then "" else  "'" ^ variant_name), (Struct, [(variant_name, fld)], reg, align_attr::attrs))]) end) 
                   (CType.active_variants nm active variants))] 
          else [])
         end
  in
    maps expand senv
  end

fun expand_unions (senv:senv) = 
  let
    fun expand (entry as (nm, (Struct, flds, reg, attrs))) = [entry]
      | expand (entry as (nm, (Union active, flds, reg, attrs))) = 
         (if length active > 1 then 
            map (fn (fld_name, fld) => (nm ^ "'" ^ fld_name, (Struct, [(fld_name, fld)], reg, attrs))) flds 
          else []) @ 
         [entry]
    val senv' = maps expand senv
  in
    senv'
  end
fun process_decls ctxt cfg (p : program) = let
  fun recurse (ds, is) (env, edecs) =
      case edecs of
        [] => ((List.rev ds, List.rev is), env)
      | e :: es => let
          val ((ds0, is0), env') = process_one_extdecl ctxt env e
        in
          recurse (List.revAppend(ds0,ds), List.revAppend(is0, is)) (env', es)
        end
  val init_cse = emptycse cfg |> add_exit
  val (i, env) = recurse ([], []) (init_cse, p)

  fun check (rcd as (name, (kind, flds, r, attrs))) =
    let
       val _ = gen_sizeof false env (type_of_rcd rcd)
    in
      ()
    end handle ERROR str => Feedback.errorStr ctxt (r, str)
  val _ = app check (get_pruned_senv env)

  fun get_referenced_fname (M (Var_info {munged_name, vtype = Function _, ...})) =
       let
         val name = MString.dest munged_name
       in if name <> exitN then SOME name else NONE end
    | get_referenced_fname _ = NONE

  val referenced_funs = get_read_globals env |> Symtab.dest
   |> map (apsnd (map_filter get_referenced_fname o Binaryset.listItems))
   |> Symtab.make


  val env = map_referenced_funs (K referenced_funs) env
  val orig_read_globals = get_read_globals env
       (* mvar_traverse uses read_globals as intermediate value and restricts the domain to
        * globals that are modified at some point. So global constants will disappear.
        * We restore the original values in the end.
        *)
  val env = mvar_finalise (mvar_traverse ctxt env)
  val env = map_read_globals (K orig_read_globals) env
  val env = map_fun_ptr_params (compress_fun_ptr_params) env
  val env = map_constant_global_fun_ptrs (K (approx_global_fun_ptrs env)) env


  val all_addressed_funs = get_all_addressed_funs env
  val all_referenced_funs = get_all_referenced_funs env
  val constant_global_fun_ptrs = get_constant_global_fun_ptrs env |> map snd |> flat |> sort_distinct fast_string_ord
  val functions_used_as_fun_ptr_params = get_functions_used_as_fun_ptr_params env
  val functions_used_via_fun_ptr = get_functions_used_via_fun_ptr env
  val all_other_fun_ptr_dependencies = get_all_other_fun_ptr_dependencies env

  val _ = @{assert} (subset (op =) (all_addressed_funs, all_referenced_funs))

  val _ = if (subset (op =) (constant_global_fun_ptrs, all_addressed_funs)) then ()
    else error ("More constant global function pointers than addressed functions, the following are "
      ^ "missing: " ^ @{make_string} (subtract (op =) all_addressed_funs constant_global_fun_ptrs))
   val _ = @{assert} (subset (op =) (functions_used_as_fun_ptr_params, all_addressed_funs))
  val _ = @{assert} (subset (op =) (all_other_fun_ptr_dependencies, all_addressed_funs))

  val _ = @{assert} (subset (op =) (constant_global_fun_ptrs, functions_used_via_fun_ptr))

  val _ = @{assert} (subset (op =) (all_addressed_funs,
                       union (op =) all_other_fun_ptr_dependencies functions_used_via_fun_ptr))


  val env = env |> map_union_variants (K (used_union_variants ctxt env (get_usedtypes env) (get_senv env)))
in
  (i, env)
end




(* Iterate over each element of each list value in a table. No good guarantees
   about traversal order. *)
fun fold_list_values
      (f: 'v -> 'acc -> 'acc)
      (acc0: 'acc)
      (tab: 'v list Symtab.table) =
    let
      fun f_list (_, values) acc = List.foldl (uncurry f) acc values
    in Symtab.fold f_list tab acc0 end

type mungedb = {fun_name: string option, nm_info: nm_info} list

fun get_mungedb c =
    let
      fun get_info vinfo acc = {
            fun_name = get_fname vinfo,
            nm_info = get_vi_nm_info c vinfo} :: acc
    in fold_list_values get_info [] (get_vars c) end

fun render_mungedb_line {fun_name: string option, nm_info: nm_info} =
    let
      val decl =
          case fun_name of
            NONE => "globally"
          | SOME f => "in function '" ^ f ^ "'"
      val c = #src_name nm_info
      val isa = #isa_name nm_info |> MString.dest
    in
      "C variable '" ^ c ^ "' " ^
      "declared " ^ decl ^ " " ^
      "-> Isabelle state field '" ^ isa ^ "'"
    end

fun render_mungedb (info: mungedb): string list =
    List.map render_mungedb_line info
    |> Library.sort string_ord

fun export_mungedb (c as Csenv cse) =
  case #munge_info_fname cse of
    NONE => ()
  | SOME fname => fname |> File_Stream.open_output (fn outstrm =>
    let
      fun tab_foldthis vinfo acc =
        let
          val srcnm = srcname vinfo
          val mnm = get_mname vinfo
          val fopt = get_fname vinfo
        in
          ((case fopt of NONE => "" | SOME f => f) ^ "::" ^ srcnm ^ " -> " ^
           MString.dest mnm ^ "\n") :: acc
        end
      fun foldthis (_, vinfos) acc = acc |> fold tab_foldthis vinfos
      fun recurse tab = Symtab.fold foldthis tab []
      val data0 = recurse (get_vars c)
      val data = Library.sort string_ord data0
    in List.app (fn s => File_Stream.output outstrm (s ^ "\n")) data end)

fun is_reachable (callee_graph: string Binaryset.set Symtab.table) caller callee =
  let
    fun immediate_callees caller = 
      case Symtab.lookup callee_graph caller of 
       SOME X => X
      | NONE => Binaryset.empty (fast_string_ord)

    fun reach searched caller =
      let 
        val immediate = immediate_callees caller
      in
        if Binaryset.member (immediate, callee) then 
          true 
        else 
          let
            val remaining = Binaryset.difference (immediate, searched)
          in 
            if Binaryset.isEmpty remaining then 
              false
             else
              exists (reach (Binaryset.union (searched, remaining))) (Binaryset.listItems remaining)
          end
          
      end
  in
    reach (Binaryset.empty fast_string_ord) caller
  end

fun is_exit_reachable cse caller =
  let
    val {callees, ...} = get_final_callgraph_with_exit cse
  in
    is_reachable callees caller exitN
  end


fun method_call_types fncall_types =
  fncall_types |> Binaryset.listItems |> map_filter (fn FnPtrCall (ty, _, true) => SOME ty | _ => NONE)

fun method_callers cse =
 let
   val cs = [] 
     |> Symtab.fold (fn (name, calltypes) => fn xs => 
          if null (method_call_types calltypes) then xs else name::xs) (get_callgraph cse)
     |> sort_distinct fast_string_ord
 in
   cs
 end

fun method_types cse =
 let
   val ts = [] 
     |> Symtab.fold (fn (name, calltypes) => fn xs => 
          method_call_types calltypes @  xs) (get_callgraph cse)
     |> sort_distinct funty_ord
 in
   ts
 end

end (* struct *)

(* Local variables: *)
(* mode: sml *)
(* End: *)
